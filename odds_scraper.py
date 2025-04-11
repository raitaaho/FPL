import requests
import pandas as pd
import json
from bs4 import BeautifulSoup

from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.common.exceptions import NoSuchElementException
from selenium.common.exceptions import TimeoutException
from selenium.common.exceptions import ElementClickInterceptedException
from selenium.webdriver.common.action_chains import ActionChains
import undetected_chromedriver as uc
import time
from fractions import Fraction
from collections import defaultdict
from unicodedata import normalize
from itertools import zip_longest
import os
from datetime import datetime

TEAM_NAMES_ODDSCHECKER = {
    "Nott'm Forest": "Nottingham Forest",
    "Wolves": "Wolverhampton",
    "Spurs": "Tottenham",
    }

odd_types = ['Win Market', 'Player Assists', 'To Score A Hat-Trick', 'Anytime Goalscorer', 'To Score 2 Or More Goals', 'Goalkeeper Saves',  'Total Home Goals', 'Total Away Goals']

def get_all_fixtures():
    url = "https://fantasy.premierleague.com/api/fixtures/"
    response = requests.get(url)
    if response.status_code != 200:
        raise Exception(f"Failed to fetch fixtures: {response.status_code}")
    # Get all fixtures from FPL API
    return response.json()

def get_next_gw(fixtures):
    '''
    return the next gameweek
    '''
    game_weeks = defaultdict(list)
    for fixture in fixtures:
        game_weeks[fixture["event"]].append(fixture)
    for event in sorted(game_weeks.keys()):
        if all(not fixture['finished'] for fixture in game_weeks[event]):
            next_gameweek =  event
            break
        else:
            next_gameweek = None
    
    return [next_gameweek]
    
def fetch_fpl_data():
    url = "https://fantasy.premierleague.com/api/bootstrap-static/"
    response = requests.get(url)
    if response.status_code != 200:
        raise Exception(f"Failed to fetch teams: {response.status_code}")
    data = response.json()
    # Get team and player data from FPL API
    teams_data = data['teams']
    players_data = data['elements']
    # A dictionary containing the team name corresponding to each team id
    team_id_to_name = {team['id']: team['name'] for team in data['teams']}

    return teams_data, players_data, team_id_to_name

def get_next_fixtures(fixtures, next_gw, team_id_to_name):
    
    gw_fixtures = [fixture for fixture in fixtures if (fixture['event'] in next_gw) and (fixture['started'] == False)]
    print("Odds are fetched for the following fixtures:")
    print('')
    for fixture in gw_fixtures:
        print(f"GW{fixture['event']} {team_id_to_name[fixture['team_h']]} v. {team_id_to_name[fixture['team_a']]}")
    print('')
    return gw_fixtures

def teams_league_positions_mapping(teams):
    '''
    Returns a dictionary containing the league position corresponding to each team id
    '''
    return {team['id']: team['position'] for team in teams}

def fetch_all_match_links(next_fixtures, team_id_to_name, teams_positions_map, driver):
    '''
    Returns a dictionary containing details for every game of the next gameweek
    '''
    driver.get("https://www.oddschecker.com/football/english/premier-league/")
    wait = WebDriverWait(driver, 10)
    try:
        span_element = wait.until(EC.element_to_be_clickable((By.XPATH, '/html/body/div[1]/div/section/h2/span[2]')))
        # Click on the <span> element (Accessing outside UK pop-up)
        span_element.click()
    except TimeoutException:
        print("Prompt for accessing outside UK did not pop up")
    wait = WebDriverWait(driver, 3)
    try:
        cookiebutton = wait.until(EC.element_to_be_clickable((By.CLASS_NAME, 'CookieBannerAcceptButton_c1mxe743')))
        # Click on the accept cookies button
        cookiebutton.click()
    except TimeoutException:
        print("Prompt for accepting Cookies did not pop up")
    except ElementClickInterceptedException:
        try:
            wait = WebDriverWait(driver, 3)
            cookiebutton = wait.until(EC.element_to_be_clickable((By.CLASS_NAME, 'CookieBannerAcceptButton_c1mxe743')))
            cookiebutton.click()
        except ElementClickInterceptedException:
            print("Prompt for accepting Cookies did not pop up")
    wait = WebDriverWait(driver, 5)
    try:
        close_ad = wait.until(EC.element_to_be_clickable((By.CLASS_NAME, 'webpush-swal2-close')))
        # Click close ad button
        close_ad.click()
    except TimeoutException:
        print('Ad did not pop up')
    try:
        wait = WebDriverWait(driver, 3)
        matches_button = wait.until(EC.element_to_be_clickable((By.XPATH, "//button[contains(text(), 'Matches')]")))
        matches_button.click()
    except Exception as e:
        print("Couldn't click Matches tab ", e)

    matches_details = defaultdict(lambda: defaultdict(list))
    for fixture in next_fixtures:
        home_team_id = fixture['team_h']
        away_team_id = fixture['team_a']
        home_team_name = team_id_to_name.get(home_team_id, "Unknown Team")
        away_team_name = team_id_to_name.get(away_team_id, "Unknown Team")
        home_position = teams_positions_map.get(home_team_id, "Unknown Position")
        away_position = teams_positions_map.get(away_team_id, "Unknown Position")
        if abs(int(home_position) - int(away_position)) >= 5:
            if home_position > away_position:
                Underdog_Bonus = 'Home'
            else:
                Underdog_Bonus = 'Away'
        else:
            Underdog_Bonus = 'None'

        home_team = TEAM_NAMES_ODDSCHECKER.get(home_team_name, home_team_name)
        away_team = TEAM_NAMES_ODDSCHECKER.get(away_team_name, away_team_name)
        match_title = home_team + " v " + away_team

        # Find match link
        match_link = driver.find_element(By.XPATH, f"//a[@title='{match_title}'][@href]")
        href = match_link.get_attribute("href")

        matches_details[match_title]['Gameweek'] = fixture['event']
        matches_details[match_title]['Home Team'] = home_team
        matches_details[match_title]['Away Team'] = away_team
        matches_details[match_title]['Underdog Bonus'] = Underdog_Bonus
        matches_details[match_title]['Link'] = href

    return matches_details

def fetch_all_odds(match, driver):
    '''
    Fetches the odds for odd_type and returns an array containing the odds
    '''
    link = match.get('Link', 'Link not found')
    home_team = match.get('Home Team', 'Home Team not found')
    away_team = match.get('Away Team', 'Away Team not found')
    odds_dict = {}
    i = 0

    try:
        driver.get(link)
    except Exception as e:
        print("Couldn't open link ", link, " ", e)
    wait = WebDriverWait(driver, 5)
    try:
        close_ad = wait.until(EC.element_to_be_clickable((By.CLASS_NAME, 'webpush-swal2-close')))
        # Click close ad button
        close_ad.click()
        time.sleep(2)
    except TimeoutException:
        print('Ad did not pop up')
    try:
        # Find the section
        headers = driver.find_elements(By.XPATH, "//h2")
        # Expand the section if it's collapsed
        for header in headers:
            header_text = header.get_attribute("innerText")
            if header_text not in odd_types:
                continue
            else:
                if header.get_attribute("aria-expanded") == "false":
                    header.click()
                    time.sleep(3)
                try:
                    compare_odds = header.find_element(By.XPATH, "./following-sibling::*[1]/*[1]/button[text()='Compare All Odds']")
                    # Expand the section if it's collapsed
                    if compare_odds.get_attribute("aria-expanded") == "false":
                        compare_odds.click()
                        time.sleep(3)  # Wait for the section to expand
                    odds_dict = {}
                    try:
                        time.sleep(3)
                        if header_text == 'Win Market':
                            outcomes = header.find_elements(By.XPATH, "./following::h4[text()='Win Market']/following::a[position()<4]")
                            odds_columns = header.find_elements(By.XPATH, f"./following::h4[text()='{header_text}']/following::div[@class='oddsAreaWrapper_o17xb9rs RowLayout_refg9ta'][position()<4]")  
                            for outcome in outcomes:
                                outcome_string = outcome.get_attribute("innerText")
                                if outcome_string == home_team:
                                    odds_dict["Home Win Odds"] = []
                                elif outcome_string == away_team:
                                    odds_dict["Away Win Odds"] = []
                                else:
                                    odds_dict["Draw Odds"] = []
                        else:
                            outcomes = header.find_elements(By.XPATH, f"./following::h4[text()='{header_text}']/following::span[@class='BetRowLeftBetName_b1m53rgx']")
                            odds_columns = header.find_elements(By.XPATH, f"./following::h4[text()='{header_text}']/following::div[@class='oddsAreaWrapper_o17xb9rs RowLayout_refg9ta']")
                            for outcome in outcomes:
                                outcome_string = outcome.get_attribute("innerText")
                                odds_dict[f"{header_text} {outcome_string} Odds"] = []
                        try:
                            for column in odds_columns:
                                odd_buttons = column.find_elements(By.XPATH, "./child::button")
                                odds_list = []
                                for odd_button in odd_buttons:
                                    odd_text = odd_button.get_attribute("innerText")
<<<<<<< HEAD
                                    if odd_text.find(' ') != -1:
                                        odd_text = odd_text.replace(' ', '')
=======
<<<<<<< HEAD
                                    if odd_text.find(' ') != -1:
                                        odd_text = odd_text.replace(' ', '')
                                    odd_fraction = Fraction(odd_text)
                                    odds_list.append(float(odd_fraction + 1))
=======
>>>>>>> 5da2cf13816b1561ab89d8b3b7adb7211ae924a1
                                    odds_list.append(odd_text)

>>>>>>> 9b73ef7a722e9ecc15dc0d308464d222e9544e53
                                odds_dict[list(odds_dict)[i]] = odds_list
                                i += 1
                            print(f"Found odds for {header_text}")
                        except Exception as e:
                            print("Couldn't find odds for ", list(odds_dict)[i])              
                    except Exception as e:
                        print(f"Couldn't find {header_text} odds", e)
                except Exception as e:
                    print(f"Couldn't click Compare All Odds on {header_text}")
                header.click()
                time.sleep(3)
    except Exception as e:
        print(f"Couldn't find or expand section: {header_text}")
    return odds_dict
        

def scrape_all_matches(match_dict, driver, data_dir, counter=0):
    for match, details in match_dict.items():
        home_team = details.get('Home Team', 'Unknown')
        away_team = details.get('Away Team', 'Unknown')
        underdog_bonus = details.get('Underdog Bonus', 'Unknown')
        gw = details.get('Gameweek', 'Unknown')
        link = details.get('Link', 'Unknown')
        match_odds_dict = {}
        match_odds_dict = {'Home Team': home_team, 'Away Team': away_team, 'Underdog Bonus': underdog_bonus, 'Gameweek': gw, 'Link': link}
        counter += 1
        match_string_for_filename = "_".join(str(word) for word in match.split())

        print('')
        print(f"{counter}/{len(match_dict)} Fetching odds for {match}")

<<<<<<< HEAD
        fixtures_odds_dict = fetch_all_odds(details, driver)
        for odd_type, odd_list in fixtures_odds_dict.items():
            updated_match_dict[match].update({odd_type: odd_list})

    return updated_match_dict
    
=======
        match_odds = fetch_all_odds(details, driver)
>>>>>>> 9b73ef7a722e9ecc15dc0d308464d222e9544e53

        for odd_type, odd_list in match_odds.items():
            match_odds_dict.update({odd_type: odd_list})
        match_odds_json = json.dumps(match_odds_dict, indent=4)
        current_time = datetime.now()
        new_filename = f"{data_dir}\\GW{gw}_{match_string_for_filename}_odds_{current_time.strftime('%d')}_{current_time.strftime('%b')}_{current_time.strftime('%H')}_{current_time.strftime('%M')}_{current_time.strftime('%S')}.json"
        try:
            with open(new_filename, "w") as outfile:
                outfile.write(match_odds_json)
                print(f"Match {match} odds successfully written to {new_filename}")
            file_prefix = f"GW{gw}_{match_string_for_filename}_odds_"
            for filename in os.listdir(data_dir):
                if filename.startswith(file_prefix) and filename != os.path.basename(new_filename):
                    os.remove(os.path.join(data_dir, filename))
        except Exception as e:
            print(f"Couldn't create or delete previous fixture {match} odds file ", e)
def main():
    teams_data, players_data, team_id_to_name = fetch_fpl_data()
    fixtures = get_all_fixtures()
    teams_data_json = json.dumps(teams_data, indent=4)
    players_data_json = json.dumps(players_data, indent=4)
    fixtures_json = json.dumps(fixtures, indent=4)
    current_time = datetime.now()
    cur_dir = os.getcwd()
    api_data_dir = os.path.join(cur_dir, "data", "api_data")
    fixture_data_dir = os.path.join(cur_dir, "data", "fixture_data")
    file_suffix = f"{current_time.strftime('%d')}_{current_time.strftime('%b')}_{current_time.strftime('%H')}_{current_time.strftime('%M')}_{current_time.strftime('%S')}.json"
    filename1 = f"{api_data_dir}\\fixtures_data_{file_suffix}"
    filename2 = f"{api_data_dir}\\players_data_{file_suffix}"
    filename3 = f"{api_data_dir}\\teams_data_{file_suffix}"
    try:
        with open(filename3, "w") as outfile:
            outfile.write(teams_data_json)
            print(f"Teams data fetched from FPL API successfully written to {filename3}")
        file_prefix = f"teams_data_"
        for filename in os.listdir(api_data_dir):
            if filename.startswith(file_prefix) and filename != os.path.basename(filename3):
                os.remove(os.path.join(api_data_dir, filename))
    except Exception as e:
        print(f"Couldn't create or delete previous teams data file", e)
    try:
        with open(filename2, "w") as outfile:
            outfile.write(players_data_json)
            print(f"Players data fetched from FPL API successfully written to {filename2}")
        file_prefix = f"players_data_"
        for filename in os.listdir(api_data_dir):
            if filename.startswith(file_prefix) and filename != os.path.basename(filename2):
                os.remove(os.path.join(api_data_dir, filename))
    except Exception as e:
        print(f"Couldn't create or delete previous players data file", e)
    try:
        with open(filename1, "w") as outfile:
            outfile.write(fixtures_json)
            print(f"Fixtures data fetched from FPL API successfully written to {filename1}")
        file_prefix = f"fixtures_data_"
        for filename in os.listdir(api_data_dir):
            if filename.startswith(file_prefix) and filename != os.path.basename(filename1):
                os.remove(os.path.join(api_data_dir, filename))
    except Exception as e:
        print(f"Couldn't create or delete previous fixtures data file", e)

    next_gw = get_next_gw(fixtures)
    next_fixtures = get_next_fixtures(fixtures, next_gw, team_id_to_name)
    teams_positions_map = teams_league_positions_mapping(teams_data)
    driver = uc.Chrome() # Replace with the path to your WebDriver if needed

    match_dict = fetch_all_match_links(next_fixtures, team_id_to_name, teams_positions_map, driver)
    scrape_all_matches(match_dict, driver, fixture_data_dir)
    
if __name__=="__main__":
    main()