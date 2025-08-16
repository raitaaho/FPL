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
import math
import csv
import ast
import chardet
import typing
import statistics
import json
import random
import sys
from datetime import datetime
from datetime import date
import scipy.stats as stats
from scipy.stats import norm
import glob
import streamlit as st

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

def get_next_gws(fixtures: list, extra_gw: str = 'False') -> list:
    """
    Find the next gameweek(s) that have not yet started.

    Args:
        fixtures (list): List of fixture dictionaries from the FPL API.
        extra_gw (str): If 'True', return the next two gameweeks; otherwise, return only the next gameweek.

    Returns:
        list: A list containing the next gameweek(s) as integers.
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
    if extra_gw == 'True':
        return [next_gameweek, next_gameweek + 1]
    else:
        return [next_gameweek]
    
def get_next_fixtures(fixtures: list, next_gws: list) -> list:
    # Return fixtures for the next full gameweek(s) that have not started yet.
    return [fixture for fixture in fixtures if (fixture['event'] in next_gws) and (fixture['started'] == False)]

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
    except TimeoutException:
        print("Prompt for accepting Cookies did not pop up")

    wait = WebDriverWait(driver, 3)
    try:
        span_element = wait.until(EC.element_to_be_clickable((By.XPATH, '/html/body/div[1]/div/section/h2/span[2]')))
        # Click on the <span> element (Accessing outside UK pop-up)
        span_element.click()

    except TimeoutException:
        print("Prompt for accessing outside UK did not pop up")

    wait = WebDriverWait(driver, 3)
    try:
        close_ad = wait.until(EC.element_to_be_clickable((By.CLASS_NAME, 'webpush-swal2-close')))
        # Click close ad button
        close_ad.click()
    except TimeoutException:
        print('Ad did not pop up')
        
    driver.execute_script("document.body.style.zoom='65%'")
    time.sleep(random.uniform(1, 2))

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

    wait = WebDriverWait(driver, 2)
    try:
        # Find the section
        header = wait.until(EC.element_to_be_clickable((By.XPATH, "//h2[text() ='" + odd_type + "']")))
        # Expand the section if it's collapsed
        if header.get_attribute("aria-expanded") == "false":
            try:
                header.click()
                time.sleep(random.uniform(2, 3))  # Wait for the section to expand
            except Exception as e:
                try:
                    header.send_keys(Keys.PAGE_DOWN)
                    time.sleep(random.uniform(1, 2))
                    header.click()
                    print("Successfully expanded section after scrolling down")
                    time.sleep(random.uniform(2, 3))
                except Exception as e:
                    try:
                        header = driver.find_element(By.XPATH, "//h2[text() ='" + odd_type + "']")
                        driver.execute_script("arguments[0].scrollIntoView()", header)
                        time.sleep(random.uniform(1, 2))
                        header.click()
                        print("Successfully expanded section after scrolling into view")
                        time.sleep(random.uniform(2, 3))
                    except Exception as e:
                        driver.execute_script("window.scrollBy(0,-100)")
                        time.sleep(random.uniform(1, 2))
                        header.click()
                        print("Successfully expanded section after scrolling into view and 100 pixels up")
                        time.sleep(random.uniform(2, 3))
                    
        wait = WebDriverWait(driver, 5)
        try:
            compare_odds = wait.until(EC.element_to_be_clickable((By.XPATH, "//h2[(text() ='" + odd_type + "')]/following-sibling::*[1]/*[1]/button[contains(text(), 'Compare All Odds')]")))
            # Expand the section if it's collapsed
            if compare_odds.get_attribute("aria-expanded") == "false":
                try:
                    compare_odds.click()
                    time.sleep(random.uniform(2, 3))  # Wait for the section to expand
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
                                    print(f"Deleted {old_len - new_len} {list(odds_dict)[i]} odd(s) from total of {old_len} odds due to differing over 3 standard deviations from the mean")
                            odds_dict[list(odds_dict)[i]] = odds_list
                            i += 1
                        print("Found odds for", odd_type)
                    except Exception as e:
                        print("Couldn't get odds for", odd_type, e)
                except Exception as e:
                    print("Couldn't get odds for", odd_type, e)                  
            except Exception as e:
                print("Couldn't find", odd_type, " All Odds Section", e)

            try:
                if compare_odds.get_attribute("aria-expanded") == "true":
                    compare_odds.click()
                    time.sleep(random.uniform(1, 2))
            except Exception as e:
                print("Couldn't collapse Compare All Odds on", header)
        except Exception as e:
            print("Couldn't click Compare All Odds on", odd_type, e)

        try:
            if header.get_attribute("aria-expanded") == "true":
                header.click()
                time.sleep(random.uniform(1, 2))
        except Exception as e:
            print("Couldn't collapse", header)

    except Exception as e:
        print("Couldn't find or expand section:", odd_type)

    return odds_dict

def scrape_all_matches(match_dict, driver):
    start0 = time.perf_counter()
    elapsed_time_text = st.empty()
    match_progress_text = st.empty()
    match_progress_bar = st.progress(0)
    odd_progress_text = st.empty()
    odd_progress_bar = st.progress(0)
    # Loop through each match, fetch odds, calculate probabilities, and update player_dict.
    match_counter = 0
    total_matches = len(match_dict)
    total_odds = 7

    wait = WebDriverWait(driver, 5)
    try:
        span_element = wait.until(EC.element_to_be_clickable((By.XPATH, '/html/body/div[1]/div/section/h2/span[2]')))
        # Click on the <span> element (Accessing outside UK pop-up)
        span_element.click()
        time.sleep(random.uniform(1, 2))
    except TimeoutException:
        print("Prompt for accessing outside UK did not pop up")
    for match, details in match_dict.items():
        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")

        odd_counter = 0
        match_counter += 1
        match_progress_text.text(f"Scraping match {match_counter} of {total_matches} - {match}")
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
            time.sleep(random.uniform(2, 4))
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
        driver.execute_script("document.body.style.zoom='65%'")
        time.sleep(random.uniform(1, 2))

        headers = driver.find_elements(By.XPATH, "//h2")
        for header in headers:
            if header.get_attribute("aria-expanded") == "true":
                try:
                    header.click()
                    time.sleep(random.uniform(1, 2))  # Wait for the section to expand
                except Exception as e:
                    try:
                        header.send_keys(Keys.PAGE_DOWN)
                        time.sleep(random.uniform(1, 2))
                        header.click()
                        time.sleep(random.uniform(1, 2))
                    except Exception as e:
                        print("Couldn't collapse", header)
        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")

        odd_type = 'Player Assists'
        odd_counter += 1
        odd_progress_text.text(f"Scraping odd type {odd_counter} of {total_odds} - {odd_type}")
        ass_odds_dict = fetch_odds(match, odd_type, driver)
        if ass_odds_dict:
            match_dict[match][odd_type] = ass_odds_dict
        odd_progress_bar.progress(int((odd_counter / total_odds) * 100))

        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")

        odd_type = 'Goalkeeper Saves'
        odd_counter += 1
        odd_progress_text.text(f"Scraping odd type {odd_counter} of {total_odds} - {odd_type}")
        saves_odds_dict = fetch_odds(match, odd_type, driver)
        if saves_odds_dict:
            match_dict[match][odd_type] = saves_odds_dict
        odd_progress_bar.progress(int((odd_counter / total_odds) * 100))

        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")

        odd_type = 'To Score A Hat-Trick'
        odd_counter += 1
        odd_progress_text.text(f"Scraping odd type {odd_counter} of {total_odds} - {odd_type}")
        hattrick_odds_dict = fetch_odds(match, odd_type, driver)
        if hattrick_odds_dict:
            match_dict[match][odd_type] = hattrick_odds_dict
        odd_progress_bar.progress(int((odd_counter / total_odds) * 100))

        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")

        odd_type = 'Total Home Goals'
        odd_counter += 1
        odd_progress_text.text(f"Scraping odd type {odd_counter} of {total_odds} - {odd_type}")
        total_home_goals_dict = fetch_odds(match, odd_type, driver)
        if total_home_goals_dict:
            match_dict[match][odd_type] = total_home_goals_dict
        odd_progress_bar.progress(int((odd_counter / total_odds) * 100)) 

        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")

        odd_type = 'Total Away Goals'
        odd_counter += 1
        odd_progress_text.text(f"Scraping odd type {odd_counter} of {total_odds} - {odd_type}")
        total_away_goals_dict = fetch_odds(match, odd_type, driver)
        if total_away_goals_dict:
            match_dict[match][odd_type] = total_away_goals_dict
        odd_progress_bar.progress(int((odd_counter / total_odds) * 100)) 

        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")

        odd_type = 'Anytime Goalscorer'
        odd_counter += 1
        odd_progress_text.text(f"Scraping odd type {odd_counter} of {total_odds} - {odd_type}")
        anytime_scorer_odds_dict = fetch_odds(match, odd_type, driver)
        if anytime_scorer_odds_dict:
            match_dict[match][odd_type] = anytime_scorer_odds_dict
        odd_progress_bar.progress(int((odd_counter / total_odds) * 100)) 

        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")

        odd_type = 'To Score 2 Or More Goals'
        odd_counter += 1
        odd_progress_text.text(f"Scraping odd type {odd_counter} of {total_odds} - {odd_type}")
        to_score_2_or_more_dict = fetch_odds(match, odd_type, driver)
        if to_score_2_or_more_dict:
            match_dict[match][odd_type] = to_score_2_or_more_dict
        odd_progress_bar.progress(int((odd_counter / total_odds) * 100)) 

        elapsed = time.perf_counter() - start0
        elapsed_time_text.text(f"Total time elapsed: {round(elapsed/60, 2)} minutes")
        match_progress_bar.progress(int((match_counter / total_matches) * 100))
        odd_progress_text.text(f"Scraped all of {total_odds} odd types")

    match_progress_text.text(f"Scraped all of {total_matches} matches")    
    driver.quit()

st.set_page_config(page_title="Oddschecker.com Odds Scraper", page_icon="📈")

st.markdown("# Oddschecker.com Odds Scraper")
st.write(
    """This is a web scraper that scrapes odds from Oddschecker.com for Total Home and Away Goals, Player Assists, Goalkeeper Saves and Player Goals for Premier League matches.
    The odds are saved to a match specific JSON files and a single JSON file containing odds for every match."""
)

if st.button("Start scraping"):

    data, teams_data, players_data, team_id_to_name, player_id_to_name = fetch_fpl_data()
    fixtures = get_all_fixtures()
    next_gws = get_next_gws(fixtures, extra_gw = 'False')
    next_fixtures = get_next_fixtures(fixtures, next_gws)
    teams_positions_map = teams_league_positions_mapping(teams_data)

    driver = uc.Chrome() # Replace with the path to your WebDriver if needed
    match_dict = fetch_all_match_links(next_fixtures, team_id_to_name, teams_positions_map, driver)
    scrape_all_matches(match_dict, driver)

    gws_for_filename = "-".join(str(gw) for gw in next_gws)
    cur_dir = os.getcwd()
    fixtures_dir = os.path.join(cur_dir, "data", "fixture_data")
    current_time = datetime.now()
    filename = os.path.join(fixtures_dir, f"gw{gws_for_filename}_all_odds_{current_time.strftime('%d')}-{current_time.strftime('%m')}_{current_time.strftime('%H')}-{current_time.strftime('%M')}.json")
    json_data = json.dumps(match_dict, indent=4)
    with open(filename, 'w') as f:
        f.write(json_data)
        print("Saved odds for GW(s)", gws_for_filename, "fixtures to", filename)