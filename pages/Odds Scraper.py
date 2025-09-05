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
import time
from fractions import Fraction
from collections import defaultdict
import os
import typing
import statistics
import json
import random
from datetime import datetime
from scipy.stats import norm
import glob
import streamlit as st
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
import shutil
import re
import subprocess

# Mapping of team names from Oddschecker to FPL API team names for consistency.
TEAM_NAMES_ODDSCHECKER = {
    "Nott'm Forest": "Nottingham Forest",
    "Wolves": "Wolverhampton",
    "Spurs": "Tottenham",
    }

# Mapping of player names from Oddschecker to FPL API player names for consistency.
PLAYER_NAMES_ODDSCHECKER = {
    "Diogo Jota": "Diogo Teixeira Da Silva",
    "Yegor Yarmolyuk": "Yehor Yarmoliuk"
    }

def fetch_fpl_data() -> tuple:
    """
    Fetch all FPL data from the API, including teams and players.

    Returns:
        tuple: (data, teams_data, players_data, team_id_to_name, player_id_to_name)
            - data: Full API response as a dictionary.
            - teams_data: List of team dictionaries.
            - players_data: List of player dictionaries.
            - team_id_to_name: Mapping from team ID to team name (with Oddschecker mapping).
            - player_id_to_name: Mapping from player ID to full player name.
    """
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
    team_id_to_name = {int(team['id']): TEAM_NAMES_ODDSCHECKER.get(team['name'], team['name']) for team in teams_data}
    player_id_to_name = {int(player['id']): player["first_name"] + " " + player['second_name'] for player in players_data}

    return data, teams_data, players_data, team_id_to_name, player_id_to_name

def get_all_fixtures() -> list:
    """
    Fetch all Premier League fixtures from the FPL API.

    Returns:
        list: A list of fixture dictionaries, each containing details about a scheduled or completed match.

    Raises:
        Exception: If the API request fails.
    """
    url = "https://fantasy.premierleague.com/api/fixtures/"
    response = requests.get(url)
    if response.status_code != 200:
        raise Exception(f"Failed to fetch fixtures: {response.status_code}")
    # Get all fixtures from FPL API
    return response.json()

def get_next_gws(fixtures: list) -> list:
    """
    Find the next gameweek(s) that have not yet started.

    Args:
        fixtures (list): List of fixture dictionaries from the FPL API.

    Returns:
        next_gameweek (int): The next gameweek as integer.
    """
    game_weeks = defaultdict(list)
    for fixture in fixtures:
        game_weeks[fixture["event"]].append(fixture)
    next_gameweek = None
    for event in sorted(game_weeks.keys()):
        if all(not fixture['finished_provisional'] for fixture in game_weeks[event]):
            next_gameweek = event
            break
    if next_gameweek is None:
        raise Exception("No upcoming gameweek found.")
    
    return next_gameweek
    
def get_next_fixtures(fixtures: list, next_gw: int) -> list:
    # Return fixtures for the next full gameweek(s) that have not started yet.
    return [fixture for fixture in fixtures if (fixture['event'] == next_gw) and (fixture['started'] == False)]

def teams_league_positions_mapping(teams: list) -> dict:
    """
    Return a mapping from team ID to league position.

    Args:
        teams (list): List of team dictionaries.

    Returns:
        dict: Mapping from team ID to league position.
    """
    return {team['id']: team['position'] for team in teams}

def fetch_all_match_links(
    next_fixtures: list,
    team_id_to_name: dict,
    teams_positions_map: dict,
    driver: "webdriver.Chrome"
) -> dict:
    """
    Scrape Oddschecker for links to all matches in the next gameweek(s).

    Args:
        next_fixtures (list): List of fixture dictionaries for the next gameweek(s).
        team_id_to_name (dict): Mapping from team ID to team name.
        teams_positions_map (dict): Mapping from team ID to league position.
        driver (webdriver.Chrome): Selenium WebDriver instance.

    Returns:
        dict: Details for each match, including Oddschecker link and team info.
    """
    driver.get("https://www.oddschecker.com/football/english/premier-league/")
    wait = WebDriverWait(driver, 20)
    try:
        cookiebutton = wait.until(EC.element_to_be_clickable((By.XPATH, "//button[contains(text(), 'Accept') or contains(text(), 'Hyväksy')]")))
        # Click on the accept cookies button
        cookiebutton.click()
        time.sleep(random.uniform(1, 2))
    except TimeoutException:
        print("Prompt for accepting Cookies did not pop up")

    try:
        wait = WebDriverWait(driver, 3)
        matches_button = wait.until(EC.element_to_be_clickable((By.XPATH, "//button[contains(text(), 'Matches')]")))
        matches_button.click()
        time.sleep(random.uniform(1, 2))
    except Exception as e:
        wait = WebDriverWait(driver, 3)
        try:
            close_ad = wait.until(EC.element_to_be_clickable((By.CLASS_NAME, 'webpush-swal2-close')))
            # Click close ad button
            close_ad.click()
            time.sleep(random.uniform(1, 2))
        except TimeoutException:
            print('Ad did not pop up')
            wait = WebDriverWait(driver, 3)
            try:
                span_element = wait.until(EC.element_to_be_clickable((By.XPATH, "//span[starts-with(@class, 'PopupCloseIcon')]")))
                # Click on the <span> element (Accessing outside UK pop-up)
                span_element.click()
                time.sleep(random.uniform(1, 2))
            except TimeoutException:
                print("Prompt for accessing outside UK did not pop up")
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

        home_team = TEAM_NAMES_ODDSCHECKER.get(home_team_name, home_team_name)
        away_team = TEAM_NAMES_ODDSCHECKER.get(away_team_name, away_team_name)
        if home_team == None:
            home_team = home_team_name
        if away_team == None:
            away_team = away_team_name
        match_title = home_team + " v " + away_team

        try:
            # Find match link
            match_link = driver.find_element(By.XPATH, f"//a[@title='{match_title}'][@href]")
            href = match_link.get_attribute("href")
        except NoSuchElementException:
            print(f"Match link for {match_title} not found.")
            href = "Link not found"
        matches_details[match_title] = {}
        matches_details[match_title]['home_team'] = home_team
        matches_details[match_title]['away_team'] = away_team
        matches_details[match_title]['home_position'] = home_position
        matches_details[match_title]['away_position'] = away_position
        matches_details[match_title]['Link'] = href

    return matches_details

def fetch_odds(match_name: str, odd_type: str, driver: "webdriver.Chrome") -> typing.Optional[dict]:
    """
    Fetch odds for a specific market (e.g., Player Assists, Goalkeeper Saves) from Oddschecker.

    Args:
        odd_type (str): The odds market to fetch.
        driver (webdriver.Chrome): Selenium WebDriver instance.

    Returns:
        dict: Mapping from outcome to list of odds, or None if not found.
    """

    odds_dict = {}
    wait = WebDriverWait(driver, 4)
    try:
        # Find the section
        header = wait.until(EC.element_to_be_clickable((By.XPATH, "//h2[text() ='" + odd_type + "']")))
        # Expand the section if it's collapsed
        if header.get_attribute("aria-expanded") == "false":
            try:
                driver.execute_script('arguments[0].click()', header)
            except Exception as e:
                try:
                    header.send_keys(Keys.PAGE_DOWN)
                    time.sleep(random.uniform(1, 2))
                    header.click()
                    print("Successfully expanded section after scrolling down")
                except Exception as e:
                    try:
                        header = driver.find_element(By.XPATH, "//h2[text() ='" + odd_type + "']")
                        driver.execute_script("arguments[0].scrollIntoView()", header)
                        time.sleep(random.uniform(1, 2))
                        header.click()
                        print("Successfully expanded section after scrolling into view")
                    except Exception as e:
                        try:
                            driver.execute_script("window.scrollBy(0,-100)")
                            time.sleep(random.uniform(1, 2))
                            header.click()
                            print("Successfully expanded section after scrolling into view and 100 pixels up")
                        except Exception as e:
                            print("Header not clickable")

                    
        wait = WebDriverWait(driver, 5)
        try:
            compare_odds = wait.until(EC.element_to_be_clickable((By.XPATH, "//h2[(text() ='" + odd_type + "')]/following-sibling::*[1]/*[1]/button[contains(text(), 'Compare All Odds')]")))
            # Expand the section if it's collapsed
            if compare_odds.get_attribute("aria-expanded") == "false":
                try:
                    driver.execute_script('arguments[0].click()', compare_odds)
                    time.sleep(random.uniform(1, 2))  # Wait for the section to expand
                except Exception as e:
                    try:
                        compare_odds.send_keys(Keys.PAGE_DOWN)
                        time.sleep(random.uniform(1, 2))
                        compare_odds.click()
                        print("Successfully expanded compare all after scrolling down")
                        time.sleep(random.uniform(2, 3))
                    except Exception as e:
                        try:
                            compare_odds = driver.find_element(By.XPATH, "//h2[(text() ='" + odd_type + "')]/following-sibling::*[1]/*[1]/button[contains(text(), 'Compare All Odds')]")
                            driver.execute_script("arguments[0].scrollIntoView()", compare_odds)
                            time.sleep(random.uniform(1, 2))
                            compare_odds.click()
                            print("Successfully expanded compare all after scrolling into view")
                            time.sleep(random.uniform(2, 3))
                        except Exception as e:
                            driver.execute_script("window.scrollBy(0,-100)")
                            time.sleep(random.uniform(1, 2))
                            compare_odds.click()
                            print("Successfully expanded compare all after scrolling into view and 100 pixels up")
                            time.sleep(random.uniform(2, 3))
            try:
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
                                if odd_text and odd_text.find(' ') != -1:
                                    odd_text = odd_text.replace(' ', '')
                                if odd_text and odd_text.find('/') != -1:
                                    odd_fraction = Fraction(odd_text)
                                    # Convert fractional odds to decimal odds
                                    odd_decimal = float(odd_fraction + 1) if odd_fraction else 0
                                    odds_list.append(odd_decimal)
                            if len(odds_list) > 2:
                                mean = sum(odds_list) / len(odds_list)
                                std = statistics.stdev(odds_list)
                                # Filter out odds that are more than 2 standard deviations away from the mean
                                old_len = len(odds_list)
                                odds_list = [odd for odd in odds_list if abs(odd - mean) <= 3 * std]
                                new_len = len(odds_list)
                                if old_len > new_len:
                                    print(f"Deleted {old_len - new_len} {list(odds_dict)[i]} {odd_type} odd(s) from total of {old_len} odds due to differing over 3 standard deviations from the mean")
                                odds_dict[list(odds_dict)[i]] = odds_list
                            else:
                                print(f"Skipped {list(odds_dict)[i]} {odd_type} since less than 3 odds available")
                            i += 1
                        print("Found odds for", odd_type)
                    except Exception as e:
                        print("Couldn't get odds for", odd_type, e)
                except Exception as e:
                    print("Couldn't get innerText-attribute for", odd_type, "outcome", e)                  
            except Exception as e:
                print("Couldn't find", odd_type, " All Odds Section", e)
        except Exception as e:
            print("Couldn't click Compare All Odds on", odd_type, e)
        try:
            if header.get_attribute("aria-expanded") == "true":
                driver.execute_script('arguments[0].click()', header)
                time.sleep(random.uniform(1, 2))
        except Exception as e:
            print("Couldn't collapse", header)
    except Exception as e:
        print("Couldn't find or expand section:", odd_type)
        #driver.save_screenshot('screenshot.png')
        #st.image("screenshot.png", caption="Screen")

    return odds_dict

def scrape_all_matches(match_dict, driver):
    start0 = time.perf_counter()
    elapsed_time_text = st.empty()
    match_progress_text = st.empty()
    match_progress_bar = st.progress(0)
    match_text = st.empty()

    # Loop through each match, fetch odds, calculate probabilities, and update player_dict.
    match_counter = 0
    total_matches = len(match_dict)

    odd_types = ['Player Assists', 'Goalkeeper Saves', 'To Score A Hat-Trick', 'Anytime Goalscorer', 'Total Home Goals', 'Total Away Goals', 'To Score 2 Or More Goals']
    total_odds= len(odd_types)

    elapsed = time.perf_counter() - start0
    for match, details in match_dict.items():
        odd_counter = 0
        match_counter += 1

        match_progress_text.markdown(f"## Scraping match {match_counter} of {total_matches}")

        match_text = st.empty()
        match_text.markdown(f"### Scraping odds for {match}")
       
        odd_progress_text = st.empty()
        odd_progress_bar = st.progress(0)

        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")

        home_team_name = details.get('home_team', 'Unknown')
        away_team_name = details.get('away_team', 'Unknown')
        home_team = TEAM_NAMES_ODDSCHECKER.get(home_team_name, home_team_name)
        away_team = TEAM_NAMES_ODDSCHECKER.get(away_team_name, away_team_name)
        link = details.get('Link', 'Link not found')

        if link == 'Link not found':
            print(f"Link not found for {match}. Skipping.")
            match_progress_bar.progress(int((match_counter / total_matches) * 100))
            continue
        try:
            driver.get(link)
            time.sleep(random.uniform(4, 6))
            if match_counter == 1:
                wait = WebDriverWait(driver, 5)
                try:
                    span_element = wait.until(EC.element_to_be_clickable((By.XPATH, "//span[starts-with(@class, 'UK')]")))
                    # Click on the <span> element (Accessing outside UK pop-up)
                    span_element.click()
                    time.sleep(random.uniform(1, 2))
                except TimeoutException:
                    print("Prompt for accessing outside UK did not pop up")
            
            wait = WebDriverWait(driver, 3)
            try:
                close_ad = wait.until(EC.element_to_be_clickable((By.CLASS_NAME, 'webpush-swal2-close')))
                # Click close ad button
                close_ad.click()
                time.sleep(random.uniform(1, 2))
            except TimeoutException:
                print('Ad did not pop up')
        except Exception as e:
            print("Couldn't open link ", link, " ", e)
            match_progress_bar.progress(int((match_counter / total_matches) * 100))
            continue

        #driver.execute_script("document.body.style.zoom='60%'")
        time.sleep(random.uniform(1, 2))

        headers = driver.find_elements(By.XPATH, "//h2")
        for header in headers:
            if header.get_attribute("aria-expanded") == "true":
                try:
                    driver.execute_script('arguments[0].click()', header)
                    time.sleep(random.uniform(1, 2))  # Wait for the section to expand
                except Exception as e:
                    try:
                        header.send_keys(Keys.PAGE_DOWN)
                        time.sleep(random.uniform(1, 2))
                        header.click()
                        time.sleep(random.uniform(1, 2))
                    except Exception as e:
                        st.write("Couldn't collapse", header)
        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")

        for odd_type in odd_types:
            odd_counter += 1
            odd_progress_text.text(f"Scraping odd type {odd_counter} of {total_odds} - {odd_type}")
            odds_dict = fetch_odds(match, odd_type, driver)
            if odds_dict:
                st.success(f'Scraped odds for {odd_type}', icon="✅")
                match_dict[match][odd_type] = odds_dict
            else:
                st.warning(f'Could not scrape odds for {odd_type}', icon="⚠️")
            
            odd_progress_bar.progress(int((odd_counter / total_odds) * 100))

            elapsed = time.perf_counter() - start0
            elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")

        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")
        match_progress_bar.progress(int((match_counter / total_matches) * 100))
        odd_progress_text.text(f"Scraped all of {total_odds} odd types in match {match}")

    elapsed = time.perf_counter() - start0
    match_progress_text.markdown(f"## Scraped all of {total_matches} matches in {round(elapsed/60, 2)} minutes") 
    driver.quit()
    
    st.session_state.scrape_time = round(elapsed / 60, 2)
    st.session_state.scraping_done = True
    st.session_state.scraped_data = match_dict

    return st.session_state.scraped_data, st.session_state.scraping_done, st.session_state.scrape_time

def get_logpath() -> str:
    return os.path.join(os.getcwd(), 'selenium.log')

def get_chromedriver_path() -> str:
    return shutil.which('chromedriver')

def get_webdriver_service(logpath) -> Service:
    service = Service(
    executable_path=get_chromedriver_path(),
    log_output=logpath,
    )
    return service

if "scraped_data" not in st.session_state:
    st.session_state.scraped_data = None
if "scrape_time" not in st.session_state:
    st.session_state.scrape_time = None
if "scraping_done" not in st.session_state:
    st.session_state.scraping_done = False

st.set_page_config(page_title="Oddschecker.com Odds Scraper", page_icon="📈")

st.markdown("# Oddschecker.com Odds Scraper")
st.write(
    """This is a web scraper that scrapes odds from Oddschecker.com for Player Assists, Goalkeeper Saves, Anytime Goalscorer, To Score 2 Or More Goals, To Score A Hat-Trick, Total Home Goals and Total Away Goals markets for the next gameweek of the Premier League.
    The odds are saved to a JSON file containing odds for every match of the next gameweek. These odds can be used to calculate probabilities for each player and team based on the odds provided by Oddschecker.com and these probabilities can be used to make predictions about the outcomes of matches."""
)

fixtures = get_all_fixtures()
next_gw = get_next_gws(fixtures)

cur_dir = os.getcwd()
fixtures_dir = os.path.join(cur_dir, "data", "fixture_data")

old_filename = os.path.join(fixtures_dir, f"gw{next_gw}_all_odds_")
json_files = glob.glob(f"{old_filename}*.json")

if json_files:
    latest_file_path = max(json_files)
    latest_file = latest_file_path.replace(fixtures_dir, '')
    parts = latest_file.replace(".json", '').split('_')
    st.info(f"Github repository's latest scraped odds file for next gameweek (GW{next_gw}) has a timestamp of {parts[3][2:]}.{parts[3][:2]} {parts[4][:2]}:{parts[4][2:]}")
else:
    st.info(f"Latest scraped odds file for next gameweek (GW{next_gw}) not found in Github repository")

if st.button("Start scraping"):
    data, teams_data, players_data, team_id_to_name, player_id_to_name = fetch_fpl_data()
    next_fixtures = get_next_fixtures(fixtures, next_gw)
    teams_positions_map = teams_league_positions_mapping(teams_data)

    try: 
        logpath=get_logpath()

        options = Options()
        options.binary_location = "/usr/bin/chromium"

        user_agents = [
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Safari/605.1.15",
        "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/123.0.0.0 Safari/537.36",
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:125.0) Gecko/20100101 Firefox/125.0",
        "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1",
        "Mozilla/5.0 (Linux; Android 14; SM-G991B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Mobile Safari/537.36",
        "Mozilla/5.0 (iPad; CPU OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1",
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Edge/124.0.2478.80",
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 13_5) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
        "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
        "Mozilla/5.0 (Linux; Android 13; Pixel 6) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Mobile Safari/537.36",
        "Mozilla/5.0 (Linux; Android 14; Samsung Galaxy S22) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Mobile Safari/537.36",
        "Mozilla/5.0 (Windows NT 11.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 14_1) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
        "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.0.0 Safari/537.36",
        "Mozilla/5.0 (Linux; Android 13; Xiaomi Mi 11) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.0.0 Mobile Safari/537.36",
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.0.0 Safari/537.36"
        ]

        user_agent = random.choice(user_agents)

        options.add_argument("--headless=new") 
        options.add_argument("--no-sandbox")
        options.add_argument("--disable-dev-shm-usage")
        options.add_argument("--disable-gpu")
        options.add_argument("--remote-debugging-port=9222")
        options.add_argument("--start-maximized")

        service = get_webdriver_service(logpath=logpath)

        driver = webdriver.Chrome(options=options, service=service)
        time.sleep(random.uniform(10, 12))
    except Exception as e: 
        st.write("Couldn't open Chrome")
        quit()

    match_dict = fetch_all_match_links(next_fixtures, team_id_to_name, teams_positions_map, driver)
    st.session_state.scraped_data, st.session_state.scraping_done, st.session_state.scrape_time = scrape_all_matches(match_dict, driver)

# Show download button if scraping is done
if st.session_state.scraping_done and st.session_state.scraped_data and st.session_state.scrape_time:
    json_data = json.dumps(st.session_state.scraped_data, indent=4)
    current_time = datetime.now()
    filename = f"gw{next_gw}_all_odds_{current_time.strftime('%m')}{current_time.strftime('%d')}_{current_time.strftime('%H')}{current_time.strftime('%M')}.json"

    st.success(f"✅ Scraping completed in {st.session_state.scrape_time} minutes.")
    st.download_button(
        label="Download odds as JSON file",
        data=json_data,
        file_name=filename,
        mime="text/json",
        icon=":material/download:",
    )

