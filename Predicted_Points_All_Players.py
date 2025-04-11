# pip install - r requirements.txt

import requests
import pandas as pd
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

def get_all_fixtures():
    url = "https://fantasy.premierleague.com/api/fixtures/"
    response = requests.get(url)
    if response.status_code != 200:
        raise Exception(f"Failed to fetch fixtures: {response.status_code}")
    # Get all fixtures from FPL API
    return response.json()

def get_next_gws(fixtures, extra_gw='False'):
    '''
    return the next gameweek, or next two gameweeks if extra_gw = 'True'
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
    if extra_gw == 'True':
        return [next_gameweek, next_gameweek + 1]
    else:
        return [next_gameweek]

def fetch_fpl_data():
    url = "https://fantasy.premierleague.com/api/bootstrap-static/"
    response = requests.get(url)
    if response.status_code != 200:
        raise Exception(f"Failed to fetch teams: {response.status_code}")
    data = response.json()
    # Get team data from FPL API
    teams_data = data['teams']
    # Get player data from FPL API
    players_data = data['elements']
    # A dictionary containing the team name corresponding to each team id
    team_id_to_name = {team['id']: team['name'] for team in teams_data}
    player_id_to_name = {player['id']: player["first_name"] + " " + player['second_name'] for player in players_data}

    return data, teams_data, players_data, team_id_to_name, player_id_to_name

# Dictionary to match teams from Oddschecker to correct team fetched from FPL API
TEAM_NAMES_ODDSCHECKER = {
    "Nott'm Forest": "Nottingham Forest",
    "Wolves": "Wolverhampton",
    "Spurs": "Tottenham",
    }

def get_next_fixtures(fixtures, next_gws):
    # Dictionary storing the fixtures for next full gameweek
    return [fixture for fixture in fixtures if (fixture['event'] in next_gws) and (fixture['started'] == False)]

# Function to construct the dictionary with team names, goals, assists and amount of games played
def construct_team_data(fpl_data, team_id_to_name, player_id_to_name, fixtures):
    """
    Constructs and returns two dictionaries: (1) a dictionary that contains total goals scored, total assists, assists per goal, amount of games played,
    goalkeeper saves and goalkeeper saves per game for every team. (2) a dictionary that contains games played for current team, goals scored for current team, 
    assists assisted for current team and goalkeeper saves for current team for every player.
    """
    teams = fpl_data['teams']
    elements = fpl_data['elements']
    
    team_data = {}
    player_data = {}

    # Initialize team data with goals and assists set to 0
    for team in teams:
        team_data[team['name']] = {
            'Goals': 0,
            'Assists': 0,
            'Assists per Goal': 0,
            'Games Played': 0,
            'Goalkeeper Saves': 0,
            'Goalkeeper Saves per Game': 0
        }

    for player in elements:
        player_data[player_id_to_name[player['id']]] = {
            'Games Played for Current Team': 0,
            'Goals for Current Team': 0,
            'Assists for Current Team': 0,
            'Goalkeeper Saves for Current Team': 0
        }

    # Count the number of completed fixtures for each team
    for fixture in fixtures:
        if fixture['finished']:  # Check if the fixture is completed
            home_team_id = fixture['team_h']
            away_team_id = fixture['team_a']
            home_team_name = team_id_to_name[home_team_id]
            away_team_name = team_id_to_name[away_team_id]

            # Increment games played for both teams
            team_data[home_team_name]['Games Played'] += 1
            team_data[away_team_name]['Games Played'] += 1

            # Add values to both dictionaries by fixture. Adding values by fixture instead of player data takes into account only fixtures where a player has played for his current team
            # instead of using the value from player data (which includes also goals, assists and saves from previous teams)
            for stat in fixture['stats']:
                if stat['identifier'] == 'bps':
                    for pair in stat['a']:
                        for player in elements:
                            if player["team"] == away_team_id and player["id"] == pair['element']:
                                player_data[player_id_to_name[pair['element']]]['Games Played for Current Team'] += 1
                    for pair in stat['h']:
                        for player in elements:
                            if player["team"] == home_team_id and player["id"] == pair['element']:
                                player_data[player_id_to_name[pair['element']]]['Games Played for Current Team'] += 1
                if stat['identifier'] == 'goals_scored':
                    for pair in stat['a']:
                        team_data[away_team_name]['Goals'] += int(pair['value'])
                        for player in elements:
                            if player["team"] == away_team_id and player["id"] == pair['element']:
                                player_data[player_id_to_name[pair['element']]]['Goals for Current Team'] += int(pair['value'])
                    for pair in stat['h']:
                        team_data[home_team_name]['Goals'] += int(pair['value'])
                        for player in elements:
                            if player["team"] == home_team_id and player["id"] == pair['element']:
                                player_data[player_id_to_name[pair['element']]]['Goals for Current Team'] += int(pair['value'])
                if stat['identifier'] == 'assists':
                    for pair in stat['a']:
                        team_data[away_team_name]['Assists'] += int(pair['value'])
                        for player in elements:
                            if player["team"] == away_team_id and player["id"] == pair['element']: 
                                player_data[player_id_to_name[pair['element']]]['Assists for Current Team'] += int(pair['value'])
                    for pair in stat['h']:
                        team_data[home_team_name]['Assists'] += int(pair['value'])
                        for player in elements:
                            if player["team"] == home_team_id and player["id"] == pair['element']:
                                player_data[player_id_to_name[pair['element']]]['Assists for Current Team'] += int(pair['value'])
                if stat['identifier'] == 'saves':
                    for pair in stat['a']:
                        team_data[away_team_name]['Goalkeeper Saves'] += int(pair['value'])
                        for player in elements:
                            if player["team"] == away_team_id and player["id"] == pair['element']:
                                player_data[player_id_to_name[pair['element']]]['Goalkeeper Saves for Current Team'] += int(pair['value'])
                    for pair in stat['h']:
                        team_data[home_team_name]['Goalkeeper Saves'] += int(pair['value'])
                        for player in elements:
                            if player["team"] == home_team_id and player["id"] == pair['element']:
                                player_data[player_id_to_name[pair['element']]]['Goalkeeper Saves for Current Team'] += int(pair['value'])

    for team in team_data:
        team_data[team]['Goalkeeper Saves per Game'] = float(team_data[team]['Goalkeeper Saves']/team_data[team]['Games Played'])
        team_data[team]['Assists per Goal'] = float(team_data[team]['Assists']/team_data[team]['Goals'])
    
    
    return team_data, player_data

def print_and_store_next_fixtures(next_fixtures, team_id_to_name):
    print("Predicted Points Will Be Calculated for The Following Fixtures:")
    print('')
    teams_playing = defaultdict(int)
    for fixture in next_fixtures:
        teams_playing[TEAM_NAMES_ODDSCHECKER.get(team_id_to_name[fixture['team_h']], team_id_to_name[fixture['team_h']])] += 1
        teams_playing[TEAM_NAMES_ODDSCHECKER.get(team_id_to_name[fixture['team_a']], team_id_to_name[fixture['team_a']])] += 1
        print(f"GW{fixture['event']} {team_id_to_name[fixture['team_h']]} v. {team_id_to_name[fixture['team_a']]}")
    print('')
    return teams_playing

# Function to normalize and prepare names for comparison
def prepare_name(name):
    """
    Normalizes a name by converting to lowercase, removing accents, and splitting into tokens.
    """
    # Replace foreign letters with their ASCII equivalents
    foreign_replacements = {
        'ø': 'o',
        'å': 'a',
        'æ': 'ae',
        'ä': 'a',
        'ö': 'o',
        'ú': 'u',
        'ü': 'u',
        'é': 'e',
        'ñ': 'n',
        'ï': 'i',
        'í': 'i',
        'ã': 'a',
        'á': 'a',
        'č': 'c',
        'ć': 'c',
        'š': 's'
    }
    for foreign_char, ascii_char in foreign_replacements.items():
        name = name.lower().replace(foreign_char, ascii_char)

    # Normalize the name to handle accents and foreign characters
    normalized_name = normalize('NFKD', name).encode('ascii', 'ignore').decode('ascii')
    
    cleaned_name = normalized_name.replace('-', ' ')
    cleaned_name2 = cleaned_name.replace("'", '')
    # Split into tokens
    return cleaned_name2.split()

def teams_league_positions_mapping(teams):
    '''
    Returns a dictionary containing the league position corresponding to each team id
    '''
    return {team['id']: team['position'] for team in teams}

def position_mapping(data):
    '''
    Returns a dictionary containing the player position ('MNG', 'GKP', 'DEF', 'MID', 'FWD') corresponding to each element_type
    '''
    return {et["id"]: et["singular_name_short"] for et in data["element_types"]}

def prepare_nickname(nickname):
    '''
    Returns two different cleaned nicknames
    '''
    nickname1 = nickname.replace("'", '')
    nickname2 = nickname.replace("'", '')
    index = nickname1.find(".")
    while (index != -1):
        if index != len(nickname1) - 1:
            nickname1 = nickname1[:index] + ' ' + nickname1[index+1:].strip()
            if nickname1.find(".") != -1:
                nickname1 = nickname1[index+1:]
            index = nickname1.find(".")
        else:
            nickname1 = nickname1[:index]
            index = nickname1.find(".")

    index2 = nickname2.find(".")
    while (index2 != -1):
        if index2 != len(nickname2) - 1:
            nickname2 = nickname2[index2+1:]
            index2 = nickname2.find(".")
        else:
            nickname2 = nickname2[:index2]
            index2 = nickname2.find(".")

    nickname1 = nickname1.replace("-", " ").replace("'", '')
    nickname2 = nickname2.replace("-", " ").replace("'", '')
    return nickname1, nickname2

def player_dict_constructor(players_data, team_stats_dict, player_stats_dict, element_types, team_id_to_name):
    '''
    Constructs and returns a dictionary containing details for every player fetched from FPL API
    '''
    # Initialize player_dict to store lists of values for each key
    player_dict = defaultdict(lambda: defaultdict(list))

    for player in players_data:
        player_name = player["first_name"] + " " + player["second_name"]
        nickname = player['web_name']
        nickname1, nickname2 = prepare_nickname(nickname)

        player_dict[player_name]['Nickname'] = nickname1.strip() if nickname1 != None else "Unknown"
        player_dict[player_name]['Nickname2'] = nickname2.strip() if nickname2 != None else "Unknown"
        player_dict[player_name]['Position'] = element_types[player["element_type"]]
        player_dict[player_name]['Team'] = TEAM_NAMES_ODDSCHECKER.get(team_id_to_name[player["team"]], team_id_to_name[player["team"]])
        player_dict[player_name]['Chance of Playing'] = player['chance_of_playing_next_round'] / 100 if player['chance_of_playing_next_round'] else 1 if player['status'] in ('a', 'd') else 0
        games_played_of_total_games_ratio = float((team_stats_dict[team_id_to_name[player["team"]]]['Games Played'])/player_stats_dict[player_name]['Games Played for Current Team']) if player_stats_dict[player_name]['Games Played for Current Team'] > 0 else 1
        player_dict[player_name]['Games Played for Current Team'] = player_stats_dict[player_name]['Games Played for Current Team']

        # How many goals has the player scored out of the total goals scored by his team 
        player_dict[player_name]['Share of Goals by The Team'] = float(player_stats_dict[player_name]["Goals for Current Team"]/team_stats_dict[team_id_to_name[player["team"]]]['Goals'] * games_played_of_total_games_ratio) if games_played_of_total_games_ratio < 5 else float(player_stats_dict[player_name]["Goals for Current Team"]/team_stats_dict[team_id_to_name[player["team"]]]['Goals'])
        # How many assists has the player assisted out of the total assists assisted by his team 
        player_dict[player_name]['Share of Assists by The Team'] = float(player_stats_dict[player_name]["Assists for Current Team"]/team_stats_dict[team_id_to_name[player["team"]]]['Assists'] * games_played_of_total_games_ratio) if games_played_of_total_games_ratio < 5 else float(player_stats_dict[player_name]["Assists for Current Team"]/team_stats_dict[team_id_to_name[player["team"]]]['Assists'])
        # On average, how many assists does the team get per goal scored
        player_dict[player_name]['Team Assists per Goal'] = team_stats_dict[team_id_to_name[player["team"]]]['Assists per Goal']
        if element_types[player["element_type"]] == 'GKP':
            player_dict[player_name]['Team Goalkeeper Saves per Game'] = team_stats_dict[team_id_to_name[player["team"]]]['Goalkeeper Saves per Game']
            player_dict[player_name]['Share of Goalkeeper Saves by The Team'] = float(player_stats_dict[player_name]["Goalkeeper Saves for Current Team"]/team_stats_dict[team_id_to_name[player["team"]]]['Goalkeeper Saves'] * games_played_of_total_games_ratio) if games_played_of_total_games_ratio < 5 else float(player_stats_dict[player_name]["Goalkeeper Saves for Current Team"]/team_stats_dict[team_id_to_name[player["team"]]]['Goalkeeper Saves'])
    
    return player_dict

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

    matches_details = {}
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

        matches_details[match_title] = {}
        matches_details[match_title]['home_team'] = home_team
        matches_details[match_title]['away_team'] = away_team
        matches_details[match_title]['Underdog Bonus'] = Underdog_Bonus
        matches_details[match_title]['Link'] = href

    return matches_details

def fetch_win_market_odds(match_dict, driver, player_dict):
    '''
    Fetches the odds for home win, away win and draw outcomes, calculates the probabilities for the outcomes and appends the probabilities for players with 'MNG' as position to player_dict
    '''
    home_team = match_dict.get('home_team', 'Unknown')
    away_team = match_dict.get('away_team', 'Unknown')
    Underdog_Bonus = match_dict.get('Underdog Bonus', 'None')
    link = match_dict.get('Link', 'Link not found')

    try:
        driver.get(link)
        wait = WebDriverWait(driver, 3)
        try:
            close_ad = wait.until(EC.element_to_be_clickable((By.CLASS_NAME, 'webpush-swal2-close')))
            # Click close ad button
            close_ad.click()
        except TimeoutException:
            print('Ad did not pop up')
    except Exception as e:
        print("Couldn't open link ", link, " ", e)
    
    try:
        win_market_header = driver.find_element(By.XPATH, "//h2[contains(text(), 'Win Market')]")
        # Expand the section if it's collapsed
        if win_market_header.get_attribute("aria-expanded") == "false":
            win_market_header.click()
            time.sleep(3)
        wait = WebDriverWait(driver, 3)
        try:
            compare_odds = wait.until(EC.element_to_be_clickable((By.XPATH, f"//h2[contains(text(), 'Win Market')]/following-sibling::*[1]/*[1]/button[contains(text(), 'Compare All Odds')]")))
            # Expand the section if it's collapsed
            if compare_odds.get_attribute("aria-expanded") == "false":
                compare_odds.click()
                time.sleep(3)  # Wait for the section to expand
            try:
                odds_dict = {}
                outcomes = driver.find_elements(By.XPATH, "//h4[contains(text(), 'Win Market')]/following::a[position()<4]")
                odds_columns = driver.find_elements(By.XPATH, "//h4[contains(text(), 'Win Market')]/following::div[@class='oddsAreaWrapper_o17xb9rs RowLayout_refg9ta']")
                for outcome in outcomes:
                    outcome_string = outcome.get_attribute("innerText")
                    odds_dict[outcome_string] = []
                i = 0
                try:
                    for column in odds_columns:
                        odd_buttons = column.find_elements(By.XPATH, "./child::button")
                        odds_list = []
                        for odd_button in odd_buttons:
                            odd_text = odd_button.get_attribute("innerText")
                            if odd_text.find(' ') != -1:
                                odd_text = odd_text.replace(' ', '')
                            odd_fraction = Fraction(odd_text)
                            odds_list.append(odd_fraction)
                        if len(odds_list) > 4:
                            # Include only odds that do not deviate from the mean more than the mean
                            odds_list = [i for i in odds_list if abs(i - (sum(odds_list)/len(odds_list))) < sum(odds_list)/len(odds_list)]
                        if len(odds_list) > 5:
                            # Include only odds that do not deviate from the mean more than half of the mean
                            odds_list = [i for i in odds_list if abs(i - (sum(odds_list)/len(odds_list))) < (sum(odds_list)/len(odds_list))/2]
                        odds_dict[list(odds_dict)[i]] = odds_list
                        i += 1
                    print("Found odds for Win Market")

                    try:
                        home_win_odd = sum(odds_dict[home_team])/len(odds_dict[home_team])
                        away_win_odd = sum(odds_dict[away_team])/len(odds_dict[away_team])
                        draw_odd = sum(odds_dict['Draw'])/len(odds_dict['Draw'])

                        home_win_prob = 1/float(home_win_odd + 1) if home_win_odd else 0
                        away_win_prob = 1/float(away_win_odd + 1) if away_win_odd else 0
                        draw_prob = 1/float(draw_odd + 1) if draw_odd else 0

                    except Exception as e:
                        print("Could not get average odds for Home Win, Away Win and/or Draw", e)
                        home_win_prob = 0
                        away_win_prob = 0
                        draw_prob = 0
                except Exception as e:
                    print("Couldn't get odds for Win Market", e)
                    home_win_prob = 0
                    away_win_prob = 0
                    draw_prob = 0

            except Exception as e:
                print("Couldn't find Win Market All Odds Section")
                home_win_prob = 0
                away_win_prob = 0
                draw_prob = 0

        except Exception as e:
            print("Could not open Compare All Odds on Win Market, e")
            home_win_prob = 0
            away_win_prob = 0
            draw_prob = 0

    except Exception as e:
        print("Could not find Win Market header, e")
        home_win_prob = 0
        away_win_prob = 0
        draw_prob = 0

    for player in player_dict:
        if player_dict[player]['Position'] == 'MNG':
            if player_dict[player]['Team'] == home_team:
                player_dict[player]['Win Probability'].append(home_win_prob)
                player_dict[player]['Draw Probability'].append(draw_prob)
                if Underdog_Bonus == 'Home':
                    player_dict[player]['Manager Bonus'].append('True')
                else: 
                    player_dict[player]['Manager Bonus'].append('False')
                    
            if player_dict[player]['Team'] == away_team:
                player_dict[player]['Win Probability'].append(away_win_prob)
                player_dict[player]['Draw Probability'].append(draw_prob)
                if Underdog_Bonus == 'Away':
                    player_dict[player]['Manager Bonus'].append('True')
                else:
                    player_dict[player]['Manager Bonus'].append('False')

def fetch_odds(odd_type, driver):
    '''
    Fetches the odds for odd_type and returns an array containing the odds
    '''
    wait = WebDriverWait(driver, 2)
    try:
        # Find the section
        header = wait.until(EC.element_to_be_clickable((By.XPATH, "//h2[text() ='" + odd_type + "']")))
        # Expand the section if it's collapsed
        if header.get_attribute("aria-expanded") == "false":
            header.click()
            time.sleep(3)
        wait = WebDriverWait(driver, 5)
        try:
            compare_odds = wait.until(EC.element_to_be_clickable((By.XPATH, "//h2[(text() ='" + odd_type + "')]/following-sibling::*[1]/*[1]/button[contains(text(), 'Compare All Odds')]")))
            # Expand the section if it's collapsed
            if compare_odds.get_attribute("aria-expanded") == "false":
                compare_odds.click()
                time.sleep(3)  # Wait for the section to expand
            try:
                odds_dict = {}
                outcomes = driver.find_elements(By.XPATH, "//h4[(text() ='" + odd_type + "')]/following::span[@class='BetRowLeftBetName_b1m53rgx']")
                odds_columns = driver.find_elements(By.XPATH, "//h4[(text() ='" + odd_type + "')]/following::div[@class='oddsAreaWrapper_o17xb9rs RowLayout_refg9ta']")
                try:
                    for outcome in outcomes:
                        outcome_string = outcome.get_attribute("innerText")
                        odds_dict[outcome_string] = []
                    try:
                        i = 0
                        for column in odds_columns:
                            odd_buttons = column.find_elements(By.XPATH, "./child::button")
                            odds_list = []
                            for odd_button in odd_buttons:
                                odd_text = odd_button.get_attribute("innerText")
                                if odd_text.find(' ') != -1:
                                    odd_text = odd_text.replace(' ', '')
                                odd_fraction = Fraction(odd_text)
                                odds_list.append(odd_fraction)
                            if len(odds_list) > 4:
                                # Include only odds that do not deviate from the mean more than the mean 
                                odds_list = [i for i in odds_list if abs(i - (sum(odds_list)/len(odds_list))) < sum(odds_list)/len(odds_list)]
                            if len(odds_list) > 7:
                                # Include only odds that do not deviate from the mean more than half of the mean mean
                                odds_list = [i for i in odds_list if abs(i - (sum(odds_list)/len(odds_list))) < (sum(odds_list)/len(odds_list))/2]
                            odds_dict[list(odds_dict)[i]] = odds_list
                            i += 1
                        header.click()
                        time.sleep(1)
                        print(f"Found odds for {odd_type}")
                        return odds_dict
                    except Exception as e:
                        print("Couldn't get odds for ", list(odds_dict)[i])
                except Exception as e:
                    print("Couldn't get odds for ", outcome, " ", e)                  
            except Exception as e:
                print(f"Couldn't find {odd_type} All Odds Section", e)
        except Exception as e:
            print(f"Couldn't click Compare All Odds on {odd_type}")
        header.click()
        time.sleep(1)
    except Exception as e:
        print(f"Couldn't find or expand section: {odd_type}")
    
def get_player_over_probs(odd_type, odds_dict, player_dict, home_team, away_team):
    '''
    Calculates player Over x probabilities according to odds_dict for odd_type and appends the probabilities to player_dict
    '''
    if odd_type == "Player Assists":
        odds_for = ['Over 0.5', 'Over 1.5', 'Over 2.5']
    if odd_type == "Goalkeeper Saves":
        odds_for = ['Over 0.5 Saves', 'Over 1.5 Saves', 'Over 2.5 Saves', 'Over 3.5 Saves', 'Over 4.5 Saves', 'Over 5.5 Saves', 'Over 6.5 Saves', 'Over 7.5 Saves', 'Over 8.5 Saves', 'Over 9.5 Saves']
    try:
        for player_odd, odds_list in odds_dict.items():
            index = player_odd.find("Over")
            odd_for = player_odd[index:].strip()
            if odd_for in odds_for:
                odd = sum(odds_list)/len(odds_list)
                if odd_type == "Goalkeeper Saves":
                    name = player_odd[:index].replace("Saves", '').strip()
                    odd_for = odd_for.replace("Saves", '').strip()
                else:
                    name = player_odd[:index].strip()
                probability = (1/(float(Fraction(odd)) + 1)) if odd else 0
            else:
                continue
            try:
                for p in player_dict:
                    # Prepare the player name for comparison
                    player_tokens = prepare_name(p)
                    webname_tokens = prepare_name(name)
                    matched_name = None

                    # Check if all tokens in one name exist in the other
                    if all(token in webname_tokens for token in player_tokens) or all(token in player_tokens for token in webname_tokens):
                        matched_name = p
                        break

                # Add the odds to the player's dictionary
                if matched_name:
                    player_dict[matched_name][f"{odd_for} {odd_type} Probability"].append(probability)
                    
                    
                else:
                    for p in player_dict:
                        # Prepare the player name for comparison
                        webname_tokens = prepare_name(name)
                        matched_name = None
                        nickname1 = player_dict[p]['Nickname']
                        nickname2 = player_dict[p]['Nickname2']
                        nickname1_tokens = prepare_name(nickname1)
                        nickname2_tokens = prepare_name(nickname2)

                        if (" ".join(nickname1_tokens) in name.lower() and (all(token in nickname2_tokens for token in webname_tokens) or all(token in webname_tokens for token in nickname2_tokens))) and (player_dict[p]['Team'] in [home_team, away_team]):
                            matched_name = p
                            break

                    if matched_name:
                        player_dict[matched_name][f"{odd_for} {odd_type} Probability"].append(probability)

                    else:
                        player_dict[name]['Nickname'] = 'Unknown'
                        player_dict[name]['Nickname2'] = 'Unknown'
                        player_dict[name]['Position'] = 'Unknown'
                        player_dict[name]['Team'] = "Unknown"
                        player_dict[name][f"{odd_for} {odd_type} Probability"].append(probability)
            except Exception as e:
                print("Couldn't update player_dict", e)
    except Exception as e:
        print("Couldn't calculate probabilities for ", odd_type, " ", e)

def get_total_goals_over_probs(odds_dict, team):
    '''
    Calculates probabilities for Total Goals according to Over x Goals Odds in odds_dict and returns a dictionary containing the probabilities
    '''
    try:
        for team_odd, odds_list in odds_dict.items():
            if team_odd == "Over 0.5":
                team_over_05_odd = sum(odds_list)/len(odds_list)
            if team_odd == "Over 1.5":
                team_over_15_odd = sum(odds_list)/len(odds_list)
            if team_odd == "Over 2.5":
                team_over_25_odd = sum(odds_list)/len(odds_list)
            if team_odd == "Over 3.5":
                team_over_35_odd = sum(odds_list)/len(odds_list)
            if team_odd == "Over 4.5":
                team_over_45_odd = sum(odds_list)/len(odds_list)

            if team_odd == "Under 0.5":
                team_under_05_odd = sum(odds_list)/len(odds_list)
            if team_odd == "Under 1.5":
                team_under_15_odd = sum(odds_list)/len(odds_list)
            if team_odd == "Under 2.5":
                team_under_25_odd = sum(odds_list)/len(odds_list)
            if team_odd == "Under 3.5":
                team_under_35_odd = sum(odds_list)/len(odds_list)
            if team_odd == "Under 4.5":
                team_under_45_odd = sum(odds_list)/len(odds_list)
            if team_odd == "Under 5.5":
                team_under_55_odd = sum(odds_list)/len(odds_list)
        try:
            team_over_05_prob = (1/(float(Fraction(team_over_05_odd + 1)))) if team_over_05_odd else 0
            team_over_15_prob = (1/(float(Fraction(team_over_15_odd + 1)))) if team_over_15_odd else 0
            team_over_25_prob = (1/(float(Fraction(team_over_25_odd + 1)))) if team_over_25_odd else 0
            team_over_35_prob = (1/(float(Fraction(team_over_35_odd + 1)))) if team_over_35_odd else 0
            team_over_45_prob = (1/(float(Fraction(team_over_45_odd + 1)))) if team_over_45_odd else 0

            team_under_05_prob = (1/(float(Fraction(team_under_05_odd + 1)))) if team_under_05_odd else 0
            team_under_15_prob = (1/(float(Fraction(team_under_15_odd + 1)))) if team_under_15_odd else 0
            team_under_25_prob = (1/(float(Fraction(team_under_25_odd + 1)))) if team_under_25_odd else 0
            team_under_35_prob = (1/(float(Fraction(team_under_35_odd + 1)))) if team_under_35_odd else 0
            team_under_45_prob = (1/(float(Fraction(team_under_45_odd + 1)))) if team_under_45_odd else 0
            team_under_55_prob = (1/(float(Fraction(team_under_55_odd + 1)))) if team_under_55_odd else 0
            try:
                team_0_goal_over_prob = 1 - team_over_05_prob if team_over_05_prob != 0 else 0
                team_0_goal_under_prob = team_under_05_prob if team_under_05_prob != 0 else 0
                team_0_goal_ave_prob = (team_0_goal_over_prob + team_0_goal_under_prob) / 2 if team_0_goal_over_prob != 0 and team_0_goal_under_prob != 0 else max(team_0_goal_over_prob, team_0_goal_under_prob)

                team_5_goal_over_prob = team_over_45_prob
                team_5_goal_under_prob = team_under_55_prob - team_under_45_prob if team_under_45_prob !=0 and team_under_55_prob != 0 else 0
                team_5_goal_ave_prob = (team_5_goal_over_prob + team_5_goal_under_prob) / 2 if team_5_goal_over_prob != 0 and team_5_goal_under_prob != 0 else max(team_5_goal_over_prob, team_5_goal_under_prob)

                team_1_goal_over_prob = team_over_05_prob - team_over_15_prob if team_over_05_prob != 0 and team_over_15_prob != 0 else team_over_05_prob
                team_1_goal_under_prob = team_under_15_prob - team_under_05_prob if team_under_05_prob != 0 and team_under_15_prob != 0 else 0
                team_1_goal_ave_prob = (team_1_goal_over_prob + team_1_goal_under_prob) / 2 if team_1_goal_over_prob != 0 and team_1_goal_under_prob != 0 else max(team_1_goal_over_prob, team_1_goal_under_prob)
                
                team_2_goal_over_prob = team_over_15_prob - team_over_25_prob if team_over_15_prob != 0 and team_over_25_prob != 0 else team_over_15_prob
                team_2_goal_under_prob = team_under_25_prob - team_under_15_prob if team_under_15_prob != 0 and team_under_25_prob != 0 else 0
                team_2_goal_ave_prob = (team_2_goal_over_prob + team_2_goal_under_prob) / 2 if team_2_goal_over_prob != 0 and team_2_goal_under_prob != 0 else max(team_2_goal_over_prob, team_2_goal_under_prob)
                
                team_3_goal_over_prob = team_over_25_prob - team_over_35_prob if team_over_25_prob != 0 and team_over_35_prob != 0 else team_over_25_prob
                team_3_goal_under_prob = team_under_45_prob - team_under_35_prob if team_under_35_prob != 0 and team_under_35_prob != 0 else 0
                team_3_goal_ave_prob = (team_3_goal_over_prob + team_3_goal_under_prob) / 2 if team_3_goal_over_prob != 0 and team_3_goal_under_prob != 0 else max(team_3_goal_over_prob, team_3_goal_under_prob)
                
                team_4_goal_over_prob = team_over_35_prob - team_over_45_prob if team_over_35_prob != 0 and team_over_45_prob != 0 else team_over_35_prob
                team_4_goal_under_prob = team_under_45_prob - team_under_35_prob if team_under_35_prob != 0 and team_under_45_prob != 0 else 0
                team_4_goal_ave_prob = (team_4_goal_over_prob + team_4_goal_under_prob) / 2 if team_4_goal_over_prob != 0 and team_4_goal_under_prob != 0 else max(team_4_goal_over_prob, team_4_goal_under_prob)

            except Exception as e:
                print(f"Couldnt calculate probabilities for Total {team.capitalize()} Goals", e)  
        except Exception as e:
            print(f"Couldnt calculate probabilities for Total {team.capitalize()} Over Goals", e)  
        return {team + '_0_goal_prob': team_0_goal_ave_prob, team + '_1_goal_prob': team_1_goal_ave_prob, team + '_2_goals_prob': team_2_goal_ave_prob, team + '_3_goals_prob': team_3_goal_ave_prob, team + '_4_goals_prob': team_4_goal_ave_prob, team + '_5_goals_prob': team_5_goal_ave_prob}      
    except Exception as e:
        print(f"Couldnt find probabilities from odds_dict for Total {team.capitalize()} Over Goals", e)

def add_total_goals_probs_to_dict(probs_dict, home_team, away_team, player_dict):
    '''
    Calculates home and away goals scored probabilities according to probs_dict and appends the probabilities to player_dict
    '''
    for player in player_dict:
        if player_dict[player]['Team'] == home_team:
            if player_dict[player]['Position'] in ['MNG', 'GKP', 'DEF', 'MID']:
                player_dict[player]['Clean Sheet Probability'].append(probs_dict["away_0_goal_prob"])
                if player_dict[player]['Position'] in ['GKP', 'DEF']:
                    home_goals_conceded_average = probs_dict["away_1_goal_prob"] + 2 * probs_dict["away_2_goals_prob"] + 3 * probs_dict["away_3_goals_prob"] + 4 * probs_dict["away_4_goals_prob"] + 5 * probs_dict["away_5_goals_prob"]
                    player_dict[player]['Goals Conceded by Team on Average'].append(home_goals_conceded_average)
                    player_dict[player]['0 Goals Conceded by Team Probability'].append(probs_dict["away_0_goal_prob"])
                    player_dict[player]['1 Goals Conceded by Team Probability'].append(probs_dict["away_1_goal_prob"])
                    player_dict[player]['2 Goals Conceded by Team Probability'].append(probs_dict["away_2_goals_prob"])
                    player_dict[player]['3 Goals Conceded by Team Probability'].append(probs_dict["away_3_goals_prob"])
                    player_dict[player]['4 Goals Conceded by Team Probability'].append(probs_dict["away_4_goals_prob"])
                    player_dict[player]['5 Goals Conceded by Team Probability'].append(probs_dict["away_5_goals_prob"])
            if player_dict[player]['Position'] in ['MNG', 'DEF', 'MID', 'FWD']:
                home_goals_average = probs_dict["home_1_goal_prob"] + 2 * probs_dict["home_2_goals_prob"] + 3 * probs_dict["home_3_goals_prob"] + 4 * probs_dict["home_4_goals_prob"] + 5 * probs_dict["home_5_goals_prob"]
                player_dict[player]['Goals Scored by Team on Average'].append(home_goals_average)
                player_dict[player]['0 Goals Scored by Team Probability'].append(probs_dict["home_0_goal_prob"])
                player_dict[player]['1 Goals Scored by Team Probability'].append(probs_dict["home_1_goal_prob"])
                player_dict[player]['2 Goals Scored by Team Probability'].append(probs_dict["home_2_goals_prob"])
                player_dict[player]['3 Goals Scored by Team Probability'].append(probs_dict["home_3_goals_prob"])
                player_dict[player]['4 Goals Scored by Team Probability'].append(probs_dict["home_4_goals_prob"])
                player_dict[player]['5 Goals Scored by Team Probability'].append(probs_dict["home_5_goals_prob"])

        if player_dict[player]['Team'] == away_team:
            if player_dict[player]['Position'] in ['MNG', 'GKP', 'DEF', 'MID']:
                player_dict[player]['Clean Sheet Probability'].append(probs_dict["home_0_goal_prob"])
                if player_dict[player]['Position'] in ['GKP', 'DEF']:
                    away_goals_conceded_average = probs_dict["home_1_goal_prob"] + 2 * probs_dict["home_2_goals_prob"] + 3 * probs_dict["home_3_goals_prob"] + 4 * probs_dict["home_4_goals_prob"] + 5 * probs_dict["home_5_goals_prob"]
                    player_dict[player]['Goals Conceded by Team on Average'].append(away_goals_conceded_average)
                    player_dict[player]['0 Goals Conceded by Team Probability'].append(probs_dict["home_0_goal_prob"])
                    player_dict[player]['1 Goals Conceded by Team Probability'].append(probs_dict["home_1_goal_prob"])
                    player_dict[player]['2 Goals Conceded by Team Probability'].append(probs_dict["home_2_goals_prob"])
                    player_dict[player]['3 Goals Conceded by Team Probability'].append(probs_dict["home_3_goals_prob"])
                    player_dict[player]['4 Goals Conceded by Team Probability'].append(probs_dict["home_4_goals_prob"])
                    player_dict[player]['5 Goals Conceded by Team Probability'].append(probs_dict["home_5_goals_prob"])
            if player_dict[player]['Position'] in ['MNG', 'DEF', 'MID', 'FWD']:
                away_goals_average = probs_dict["away_1_goal_prob"] + 2 * probs_dict["away_2_goals_prob"] + 3 * probs_dict["away_3_goals_prob"] + 4 * probs_dict["away_4_goals_prob"] + 5 * probs_dict["away_5_goals_prob"]
                player_dict[player]['Goals Scored by Team on Average'].append(away_goals_average)
                player_dict[player]['0 Goals Scored by Team Probability'].append(probs_dict["away_0_goal_prob"])
                player_dict[player]['1 Goals Scored by Team Probability'].append(probs_dict["away_1_goal_prob"])
                player_dict[player]['2 Goals Scored by Team Probability'].append(probs_dict["away_2_goals_prob"])
                player_dict[player]['3 Goals Scored by Team Probability'].append(probs_dict["away_3_goals_prob"])
                player_dict[player]['4 Goals Scored by Team Probability'].append(probs_dict["away_4_goals_prob"])
                player_dict[player]['5 Goals Scored by Team Probability'].append(probs_dict["away_5_goals_prob"])

def add_probs_to_dict(odd_type, odds_dict, player_dict, home_team, away_team):
    '''
    Calculates probabilities according to probs_dict for odd_type and appends the probabilities to player_dict
    '''
    try:
        for player_odd, odds_list in odds_dict.items():
            name = player_odd.strip()
            odd = sum(odds_list)/len(odds_list)

            for p in player_dict:
                # Prepare the player name for comparison
                player_tokens = prepare_name(p)
                webname_tokens = prepare_name(name)
                matched_name = None

                # Check if all tokens in one name exist in the other
                if all(token in webname_tokens for token in player_tokens) or all(token in player_tokens for token in webname_tokens):
                    matched_name = p
                    break

            # Add the odds to the player's dictionary
            if matched_name:

                # Calculate and add the probability
                probability = 1/float(odd + 1)
                if probability is not None:
                    player_dict[matched_name][f"{odd_type} Probability"].append(probability)
                else:
                    player_dict[matched_name][f"{odd_type} Probability"].append(0)
                    
            else:
                for p in player_dict:
                    # Prepare the player name for comparison
                    webname_tokens = prepare_name(name)
                    matched_name = None
                    nickname1 = player_dict[p]['Nickname']
                    nickname2 = player_dict[p]['Nickname2']
                    nickname1_tokens = prepare_name(nickname1)
                    nickname2_tokens = prepare_name(nickname2)

                    if (" ".join(nickname1_tokens) in name.lower() and (all(token in nickname2_tokens for token in webname_tokens) or all(token in webname_tokens for token in nickname2_tokens))) and (player_dict[p]['Team'] in [home_team, away_team]):
                        matched_name = p
                        break

                if matched_name:
                    # Calculate and add the probability
                    probability = 1/float(odd + 1)
                    if probability is not None:
                        player_dict[matched_name][f"{odd_type} Probability"].append(probability)
                    else:
                        player_dict[matched_name][f"{odd_type} Probability"].append(0)

                else:
                    player_dict[name]['Nickname'] = 'Unknown'
                    player_dict[name]['Nickname2'] = 'Unknown'
                    player_dict[name]['Position'] = 'Unknown'
                    player_dict[name]['Team'] = "Unknown"
                    probability = 1/float(odd + 1)
                    if probability is not None:
                        player_dict[name][f"{odd_type} Probability"].append(probability)
                    else:
                        player_dict[name][f"{odd_type} Probability"].append(0)
    except Exception as e:
        print("Couldn't get probability for ", odd_type, " ", e)

def scrape_all_matches(match_dict, player_dict, driver, counter=0):
    for match, details in match_dict.items():
        counter += 1
        print('')
        print(f"{counter}/{len(match_dict)} Fetching odds for {match}")
        home_team_name = details.get('home_team', 'Unknown')
        away_team_name = details.get('away_team', 'Unknown')
        home_team = TEAM_NAMES_ODDSCHECKER.get(home_team_name, home_team_name)
        away_team = TEAM_NAMES_ODDSCHECKER.get(away_team_name, away_team_name)

        fetch_win_market_odds(details, driver, player_dict)

        odd_type = 'Player Assists'
        ass_odds_dict = fetch_odds(odd_type, driver)
        if ass_odds_dict:
            get_player_over_probs(odd_type, ass_odds_dict, player_dict, home_team, away_team)

        odd_type = 'Goalkeeper Saves'
        saves_odds_dict = fetch_odds(odd_type, driver)
        if saves_odds_dict:
            get_player_over_probs(odd_type, saves_odds_dict, player_dict, home_team, away_team)

        odd_type = 'To Score A Hat-Trick'
        hattrick_odds_dict = fetch_odds(odd_type, driver)
        if hattrick_odds_dict:
            add_probs_to_dict(odd_type, hattrick_odds_dict, player_dict, home_team, away_team)

        odd_type = 'Total Home Goals'
        total_home_goals_dict = fetch_odds(odd_type, driver)
        if total_home_goals_dict:
            total_home_goals_probs = get_total_goals_over_probs(total_home_goals_dict, "home")
        odd_type = 'Total Away Goals'
        total_away_goals_dict = fetch_odds(odd_type, driver)
        if total_away_goals_dict:
            total_away_goals_probs = get_total_goals_over_probs(total_away_goals_dict, "away")
        total_combined_goals_dict = total_home_goals_probs | total_away_goals_probs
        if total_combined_goals_dict:
            add_total_goals_probs_to_dict(total_combined_goals_dict, home_team, away_team, player_dict)

        odd_type = 'Anytime Goalscorer'
        anytime_scorer_odds_dict = fetch_odds(odd_type, driver)
        if anytime_scorer_odds_dict:
            add_probs_to_dict(odd_type, anytime_scorer_odds_dict, player_dict, home_team, away_team)

        odd_type = 'To Score 2 Or More Goals'
        to_score_2_or_more_dict = fetch_odds(odd_type, driver)
        if to_score_2_or_more_dict:
            add_probs_to_dict(odd_type, to_score_2_or_more_dict, player_dict, home_team, away_team)

def calc_specific_odds(player_dict):
    '''
    Calculates assists on average, goals on average and saves on average for players according to probabilities and averages stored in player_dict and appends the calculated probabilities to player_dict
    '''
    for player, odds in player_dict.items():
        if odds.get("Position") in ['DEF', 'MID', 'FWD', 'Unknown']:
            anytime_prob = odds.get("Anytime Goalscorer Probability", [])
            two_or_more_prob = odds.get("To Score 2 Or More Goals Probability", [])
            hattrick_prob = odds.get("To Score A Hat-Trick Probability", [])
            assisting_over_05_prob = odds.get("Over 0.5 Player Assists Probability", [])
            assisting_over_15_prob = odds.get("Over 1.5 Player Assists Probability", [])
            assisting_over_25_prob = odds.get("Over 2.5 Player Assists Probability", [])
            ass_share = odds.get("Share of Assists by The Team", 0)
            ass_per_goal = odds.get("Team Assists per Goal", 0)
            goal_share = odds.get("Share of Goals by The Team", 0)
            goals_scored_average = odds.get("Goals Scored by Team on Average", [])
            ass_average = 0
            goal_average = 0

            for p25, p15, p05, gs_a in zip_longest(assisting_over_25_prob, assisting_over_15_prob, assisting_over_05_prob, goals_scored_average, fillvalue=0):
                zero_ass_prob = 1 - p05 if p05 != 0 else 1
                three_ass_prob = p25
                one_ass_prob = p05 - p15 if p05 and p15 else max((1 - p15 - zero_ass_prob), 0)
                two_ass_prob = p15 - p25 if p15 and p25 else max((1 - three_ass_prob - one_ass_prob - zero_ass_prob), 0) 
                ass_average = three_ass_prob * 3 + two_ass_prob * 2 + one_ass_prob
                if ass_average > 0:
                    player_dict[player]["Assist Odds Available"].append('True')
                # If odds for Player Assists were not available, calculate average assists according to FPL API data and average goals by team
                else:
                    player_dict[player]["Assist Odds Available"].append('False')
                    ass_average = ass_per_goal * ass_share * gs_a
                player_dict[player]["Assists On Average"].append(ass_average)

            for p3, p2, p1, gs_a in zip_longest(hattrick_prob, two_or_more_prob, anytime_prob, goals_scored_average, fillvalue=0):
                zero_goal_prob = 1 - p1 if p1 != 0 else 1
                three_goals_prob = p3
                one_goal_prob = p1 - p2 if p1 and p2 else max((1 - p2 - zero_goal_prob), 0)
                two_goals_prob = p2 - p3 if p2 and p3 else max((1 - three_goals_prob - one_goal_prob - zero_goal_prob), 0)
                goal_average = three_goals_prob * 3 + two_goals_prob * 2 + one_goal_prob
                if goal_average > 0:
                    player_dict[player]["Goal Odds Available"].append('True')
                # If odds for Player Goals were not available, calculate average goals according to FPL API data and average goals by team
                else:
                    player_dict[player]["Goal Odds Available"].append('False')
                    goal_average = goal_share * gs_a
                player_dict[player]["Goals On Average"].append(goal_average)
                
        if odds.get("Position") == 'GKP':
            saves_share = odds.get("Share of Goalkeeper Saves by The Team", 0)
            team_saves_per_game = odds.get("Team Goalkeeper Saves per Game", 0)
            saves_average = 0
            cs_probs = odds.get("Clean Sheet Probability", [])  
            over_05_saves = odds.get("Over 0.5 Goalkeeper Saves Probability", [])
            over_15_saves = odds.get("Over 1.5 Goalkeeper Saves Probability", [])
            over_25_saves = odds.get("Over 2.5 Goalkeeper Saves Probability", [])
            over_35_saves = odds.get("Over 3.5 Goalkeeper Saves Probability", [])
            over_45_saves = odds.get("Over 4.5 Goalkeeper Saves Probability", [])
            over_55_saves = odds.get("Over 5.5 Goalkeeper Saves Probability", [])
            over_65_saves = odds.get("Over 6.5 Goalkeeper Saves Probability", [])
            over_75_saves = odds.get("Over 7.5 Goalkeeper Saves Probability", [])
            over_85_saves = odds.get("Over 8.5 Goalkeeper Saves Probability", [])
            over_95_saves = odds.get("Over 9.5 Goalkeeper Saves Probability", [])

            for s95, s85, s75, s65, s55, s45, s35, s25, s15, s05, cs_prob in zip_longest(over_95_saves, over_85_saves, over_75_saves, over_65_saves, over_55_saves, over_45_saves, over_35_saves, over_25_saves, over_15_saves, over_05_saves, cs_probs, fillvalue=0):
                zero_saves_prob = 1 - s05 if s05 else 1
                ten_saves_prob = s95 if s95 else 0
                one_saves_prob = s05 - s15 if s05 and s15 else max((1 - s15 - zero_saves_prob), 0)
                two_saves_prob = s15 - s25 if s15 and s25 else max((1 - one_saves_prob - zero_saves_prob), 0)
                three_saves_prob = s25 - s35 if s25 and s35 else max((1 - two_saves_prob - one_saves_prob - zero_saves_prob), 0) 
                four_saves_prob = s35 - s45 if s35 and s45 else max((1 - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
                five_saves_prob = s45 - s55 if s45 and s55 else max((1 - four_saves_prob - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
                six_saves_prob = s55 - s65 if s55 and s65 else max((1 - five_saves_prob - four_saves_prob - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
                seven_saves_prob = s65 - s75 if s65 and s75 else max((1 - six_saves_prob - five_saves_prob - four_saves_prob - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
                eight_saves_prob = s75 - s85 if s75 and s85 else max((1 - seven_saves_prob - six_saves_prob - five_saves_prob - four_saves_prob - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
                nine_saves_prob = s85 - s95 if s85 and s95 else max((1 - eight_saves_prob - seven_saves_prob - six_saves_prob - five_saves_prob - four_saves_prob - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
            
                saves_average = one_saves_prob + two_saves_prob * 2 + three_saves_prob * 3 + four_saves_prob * 4 + five_saves_prob * 5 + six_saves_prob * 6 + seven_saves_prob * 7 + eight_saves_prob * 8 + nine_saves_prob * 9 + ten_saves_prob * 10
                if saves_average > 0:
                    player_dict[player]["Goalkeeper Saves Odds Available"].append('True')
                # If odds for Goalkeeper Saves were not available, calculate average goalkeeper saves according to team and player saves from FPL API data
                else:
                    player_dict[player]["Goalkeeper Saves Odds Available"].append('False')
                    saves_average = saves_share * team_saves_per_game
                player_dict[player]["Saves On Average"].append(saves_average)

def calc_points(player_dict, teams_playing):
    '''
    Calculates predicted points for players according to probabilities and averages stored in player_dict and appends the predicted points to player_dict
    '''
    for player, odds in player_dict.items():
        try:
            # Get probabilities
            team = odds.get("Team", "Unknown")
            number_of_games = teams_playing[team] if team != 'Unknown' else 1
            goals_average = odds.get("Goals On Average", [])
            ass_average = odds.get("Assists On Average", [])      
            cs_odd = odds.get("Clean Sheet Probability", [])
            position = odds.get("Position", "Unknown")
            saves_average = odds.get("Saves On Average", [])
            goals_scored_average = odds.get("Goals Scored by Team on Average", [])
            goals_conceded_average = odds.get("Goals Conceded by Team on Average", [])

            win_probability =  odds.get('Win Probability', [])
            draw_probability =  odds.get('Draw Probability', [])
            MGR_Bonus = odds.get('Manager Bonus', [])
            chance_of_playing = odds.get("Chance of Playing", 1)

            # If there are more probability/average entries than number of games in the gameweek for a player, skip the player
            if len(goals_average) > number_of_games or len(ass_average) > number_of_games or len(saves_average) > number_of_games:
                print(f"{player} skipped due to data entries being higher than number of games the player is playing")
                continue
                
            # Calculate points
            if position in ('MID'):
                points = chance_of_playing * (
                number_of_games * 
                2 + sum(goals_average) * 5 +
                sum(ass_average) * 3 +
                sum(cs_odd))
            if position in ('DEF'):
                points = chance_of_playing * (
                number_of_games * 
                2 + sum(goals_average) * 6 +
                sum(ass_average) * 3 +
                sum(cs_odd) * 4 - (sum(goals_conceded_average)/2))
            if position in ('GKP'):
                points = chance_of_playing * (
                number_of_games * 2 +
                sum(saves_average)/3 +
                sum(cs_odd) * 4 - (sum(goals_conceded_average)/2))
            if position in ('FWD'):
                points = chance_of_playing * (
                number_of_games * 
                2 + sum(goals_average) * 4 +
                sum(ass_average) * 3)
            if position in ('Unknown'):
                points = chance_of_playing * (
                number_of_games * 
                2 + sum(goals_average) * 4 +
                sum(ass_average) * 3)
            if position in ('MNG'):
                points = 0
                if len(win_probability) > 0:
                    for w, d, b in zip_longest(win_probability, draw_probability, MGR_Bonus, fillvalue=0):
                        points += w * 6 + d * 3
                        # If Manager Bonus is True
                        if b == 'True':
                            points += w * 10 + d * 5
                    points += sum(cs_odd) * 2 + sum(goals_scored_average)

            player_dict[player]['Points'] = round(points, 3)
        except Exception as e:
            print(f"Could not calculate points for {player}: {e}")

def main():
    data, teams_data, players_data, team_id_to_name, player_id_to_name = fetch_fpl_data()
    fixtures = get_all_fixtures()
    next_gws = get_next_gws(fixtures, extra_gw = 'False')
    next_fixtures = get_next_fixtures(fixtures, next_gws)
    teams_playing = print_and_store_next_fixtures(next_fixtures, team_id_to_name)
    element_types = position_mapping(data)
    teams_positions_map = teams_league_positions_mapping(teams_data)
    team_stats_dict, player_stats_dict = construct_team_data(data, team_id_to_name, player_id_to_name, fixtures)
    player_dict = player_dict_constructor(players_data, team_stats_dict, player_stats_dict, element_types, team_id_to_name)
    driver = uc.Chrome() # Replace with the path to your WebDriver if needed
    match_dict = fetch_all_match_links(next_fixtures, team_id_to_name, teams_positions_map, driver)

    scrape_all_matches(match_dict, player_dict, driver)

    driver.quit()

    calc_specific_odds(player_dict)

    calc_points(player_dict, teams_playing)

    # Construct a DataFrame containing the player details
    player_data_df = pd.DataFrame.from_dict(player_dict, orient='index')
    player_data_df.index.name = 'Player'

    # Sort the Dataframe according to predicted points and games player for current team (in case of exact same predicted points between players)
    sorted_player_points_df = player_data_df.sort_values(by=['Points', 'Games Played for Current Team'], ascending=[False, False])

    # Construct an additional DataFrame containing only player position, team and predicted points in order to create a simpler Excel sheet for comparing players according to their predicted points
    player_points_df = sorted_player_points_df[['Position', 'Team', 'Points']]

    # Convert the array containing gameweeks that predicted points were calculated for to single string for the file name the Excel file is written under
    gws_for_filename = "_".join(str(gw) for gw in next_gws)
    # Create an Excel with the DataFrames as sheets
    with pd.ExcelWriter(f"gw_{gws_for_filename}_output.xlsx") as writer:
        player_data_df.to_excel(writer, sheet_name='Data')
        sorted_player_points_df.to_excel(writer, sheet_name='Points')

    # Select the player with most predicted points for every position
    best_mng = sorted_player_points_df[sorted_player_points_df['Position'] == 'MNG'].head(1)
    best_gkp = sorted_player_points_df[sorted_player_points_df['Position'] == 'GKP'].head(1)
    best_def = sorted_player_points_df[sorted_player_points_df['Position'] == 'DEF'].head(1)
    best_mid = sorted_player_points_df[sorted_player_points_df['Position'] == 'MID'].head(1)
    best_fwd = sorted_player_points_df[sorted_player_points_df['Position'] == 'FWD'].head(1)
    # Print the player with most predicted points for every position
    print("Player Predicted to Score Highest Points by Position:")
    print()
    print(f"Manager:          {best_mng.axes[0].tolist()[0]:35s} {best_mng.iloc[0]['Team']:15s} {best_mng.iloc[0]['Points']:5f} Points")
    print(f"Goalkeeper:       {best_gkp.axes[0].tolist()[0]:35s} {best_gkp.iloc[0]['Team']:15s} {best_gkp.iloc[0]['Points']:5f} Points")
    print(f"Defender:         {best_def.axes[0].tolist()[0]:35s} {best_def.iloc[0]['Team']:15s} {best_def.iloc[0]['Points']:5f} Points")
    print(f"Midfielder:       {best_mid.axes[0].tolist()[0]:35s} {best_mid.iloc[0]['Team']:15s} {best_mid.iloc[0]['Points']:5f} Points")
    print(f"Forward:          {best_fwd.axes[0].tolist()[0]:35s} {best_fwd.iloc[0]['Team']:15s} {best_fwd.iloc[0]['Points']:5f} Points")

if __name__=="__main__":
    main()