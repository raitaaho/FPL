# Import all required libraries for data fetching, processing, and web scraping.
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
import numpy as np

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
        #if all(not fixture['finished'] for fixture in game_weeks[event]):
            #next_gameweek = event
            #break
        if any(fixture['finished'] == False for fixture in game_weeks[event]):
            next_gameweek = event
            break
    if next_gameweek is None:
        raise Exception("No upcoming gameweek found.")
    if extra_gw == 'True':
        return [next_gameweek, next_gameweek + 1]
    else:
        return [next_gameweek]

def prepare_name(name: str) -> list:
    """
    Normalize a name for robust comparison by converting to lowercase, removing accents, and splitting into tokens.

    Args:
        name (str): The name to normalize.

    Returns:
        list: List of capitalized tokens from the cleaned name.
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
    cleaned_name = cleaned_name.replace("'", '')
    # Split into tokens
    name_tokens = cleaned_name.split()
    cap_tokens = [token.capitalize() for token in name_tokens]
    return cap_tokens

def prepare_nickname(nickname: str) -> tuple:
    """
    Clean and generate two versions of a player's nickname for matching purposes.

    Args:
        nickname (str): The player's nickname.

    Returns:
        tuple: Two cleaned nickname strings.
    """
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

def position_mapping(data: dict) -> dict:
    """
    Return a mapping from element_type ID to player position short name (e.g., 'GKP', 'DEF').

    Args:
        data (dict): FPL API data.

    Returns:
        dict: Mapping from element_type ID to position short name.
    """
    return {et["id"]: et["singular_name_short"] for et in data["element_types"]}

def player_dict_constructor(
    players_data: list,
    element_types: dict,
    team_id_to_name: dict
) -> dict:
    """
    Build a dictionary with detailed stats for every player from the FPL API.

    Args:
        players_data (list): List of player dictionaries.
        team_stats_dict (dict): Team statistics.
        player_stats_dict (dict): Player statistics.
        element_types (dict): Mapping from element_type ID to position.
        team_id_to_name (dict): Mapping from team ID to team name.

    Returns:
        dict: Player details dictionary.
    """
    # Initialize player_dict to store lists of values for each key
    player_dict = defaultdict(lambda: defaultdict(list))

    for player in players_data:
        first_name = " ".join(prepare_name(player["first_name"]))
        second_name = " ".join(prepare_name(player["second_name"]))
        player_name = first_name + " " + second_name
        nickname = player['web_name']
        nickname1, nickname2 = prepare_nickname(nickname)
        team = TEAM_NAMES_ODDSCHECKER.get(team_id_to_name[player["team"]], team_id_to_name[player["team"]])

        response = requests.get(f"https://fantasy.premierleague.com/api/element-summary/{player['id']}/")
        history_data = response.json()
        prev_seasons_data = history_data.get('history_past', [])
        prev_fixtures_data = history_data.get('history', [])
        games = 0
        for fixture in prev_fixtures_data:
            if fixture.get('minutes', 0) > 0:
                games += 1

        minutes_24_25 = 0
        def_contributions_24_25 = 0
        saves_24_25 = 0
        bps_24_25 = 0
        for season in prev_seasons_data:
            if season['season_name'] != '2024/25':
                continue
            else:
                minutes_24_25 = season.get('minutes', 0)
                def_contributions_24_25 = season.get('defensive_contribution', 0) if minutes_24_25 > 900 else 0
                saves_24_25 = season.get('saves', 0) if minutes_24_25 > 450 else 0
                bps_24_25 = season.get('bps', 0) if minutes_24_25 > 450 else 0
                xg_24_25 = season.get('expected_goals', 0) if minutes_24_25 > 450 else 0
                xa_24_25 = season.get('expected_assists', 0) if minutes_24_25 > 450 else 0
                break

        player_dict[player_name]['Nickname'] = [nickname1.strip()] if nickname1 != None else ["Unknown"] 
        player_dict[player_name]['Nickname2'] = [nickname2.strip()] if nickname2 != None else ["Unknown"]
        player_dict[player_name]['Position'] = [element_types[player["element_type"]]]
        player_dict[player_name]['Team'] = [team]
        player_dict[player_name]['Price'] = [player['now_cost'] / 10]
        player_dict[player_name]['Minutes'] = [player['minutes']]
        player_dict[player_name]['Games'] = [games]
        player_dict[player_name]['Minutes per Game'] = [player['minutes'] / games] if games > 0 else [0]
        player_dict[player_name]['Chance of Playing'] = [player['chance_of_playing_next_round'] / 100] if player['chance_of_playing_next_round'] else [1] if player['status'] in ('a', 'd') else [0]
        player_dict[player_name]['Defensive Contributions per Game'] = [player["defensive_contribution"] / games] if games > 0 else [0]
        player_dict[player_name]['CBI per Game'] = [player["clearances_blocks_interceptions"] / games] if games > 0 else [0]
        player_dict[player_name]['Recoveries per Game'] = [player["recoveries"] / games] if games > 0 else [0]
        player_dict[player_name]['Tackles per Game'] = [player["tackles"] / games] if games > 0 else [0]
        player_dict[player_name]['BPS per Game'] = [player['bps'] / games] if games > 0 else [0]

        player_dict[player_name]['24/25 Defensive Contributions P90'] = [def_contributions_24_25 / (minutes_24_25 / 90)] if minutes_24_25 > 0 else [0]
        player_dict[player_name]['24/25 BPS P90'] = [bps_24_25 / (minutes_24_25 / 90)] if minutes_24_25 > 0 else [0]

        if element_types[player["element_type"]] == 'GKP':
            player_dict[player_name]['Saves per Game'] = [player["saves"] / games] if games > 0 else [0]
            player_dict[player_name]['24/25 Saves P90'] = [saves_24_25 / (minutes_24_25 / 90)] if minutes_24_25 > 0 else [0]

        player_dict[player_name]['Estimated BPS'] = []
        player_dict[player_name]['Estimated Bonus Points'] = []
        
    return player_dict

def get_pos_range(position: int) -> str:
    """
    Return the league position range string for a given position (1-4, 5-8, etc.).

    Args:
        position (int): League position.

    Returns:
        str: Position range as string.
    """
    if position <= 4:
        return '1-4'
    elif position <= 8:
        return '5-8'
    elif position <= 12:
        return '9-12'   
    elif position <= 16:
        return '13-16'
    elif position <= 20:
        return '17-20'
    else:
        return 'Unknown'
    
def get_team_template(pos_24_25: int, pos: int) -> dict:
    """
    Create a template dictionary for storing team statistics, initialized to default values.

    Args:
        pos_24_25 (int): Team's position in 2024/25 season.
        pos (int): Current league position.

    Returns:
        dict: Team statistics template.
    """
    team_template = {'League Position': pos,
        '24/25 League Position': pos_24_25,                                                          
        'ELO': 1000,
        'Home ELO': 1000,
        'Away ELO': 1000,
        'Home Goals': 0,
        'Away Goals': 0,
        'Home Assists': 0,
        'Away Assists': 0,
        'Goals Conceded Home': 0,
        'Goals Conceded Away': 0,
        'Home Games Played': 0,
        'Away Games Played': 0,
        'Home Goalkeeper Saves': 0,
        'Away Goalkeeper Saves': 0,
        '24/25 Home Goals': 0,
        '24/25 Away Goals': 0,
        '24/25 Home Assists': 0,
        '24/25 Away Assists': 0,
        '24/25 Goals Conceded Home': 0,
        '24/25 Goals Conceded Away': 0,
        '24/25 Home Goalkeeper Saves': 0,
        '24/25 Away Goalkeeper Saves': 0,
        'Home Games Against 1-4': 0,
        'Home Goals Against 1-4': 0,
        'Home Goals Conceded Against 1-4': 0,
        'Home Games Against 5-8': 0,
        'Home Goals Against 5-8': 0,
        'Home Goals Conceded Against 5-8': 0,
        'Home Games Against 9-12': 0,
        'Home Goals Against 9-12': 0,
        'Home Goals Conceded Against 9-12': 0,
        'Home Games Against 13-16': 0,
        'Home Goals Against 13-16': 0,
        'Home Goals Conceded Against 13-16': 0,
        'Home Games Against 17-20': 0,
        'Home Goals Against 17-20': 0,
        'Home Goals Conceded Against 17-20': 0,
        'Away Games Against 1-4': 0,
        'Away Goals Against 1-4': 0,
        'Away Goals Conceded Against 1-4': 0,
        'Away Games Against 5-8': 0,
        'Away Goals Against 5-8': 0,
        'Away Goals Conceded Against 5-8': 0,
        'Away Games Against 9-12': 0,
        'Away Goals Against 9-12': 0,
        'Away Goals Conceded Against 9-12': 0,
        'Away Games Against 13-16': 0,
        'Away Goals Against 13-16': 0,
        'Away Goals Conceded Against 13-16': 0,
        'Away Games Against 17-20': 0,
        'Away Goals Against 17-20': 0,
        'Away Goals Conceded Against 17-20': 0,
        '24/25 Home Games Against 1-4': 0,
        '24/25 Home Goals Against 1-4': 0,
        '24/25 Home Goals Conceded Against 1-4': 0,
        '24/25 Home Games Against 5-8': 0,
        '24/25 Home Goals Against 5-8': 0,
        '24/25 Home Goals Conceded Against 5-8': 0,
        '24/25 Home Games Against 9-12': 0,
        '24/25 Home Goals Against 9-12': 0,
        '24/25 Home Goals Conceded Against 9-12': 0,
        '24/25 Home Games Against 13-16': 0,
        '24/25 Home Goals Against 13-16': 0,
        '24/25 Home Goals Conceded Against 13-16': 0,
        '24/25 Home Games Against 17-20': 0,
        '24/25 Home Goals Against 17-20': 0,
        '24/25 Home Goals Conceded Against 17-20': 0,
        '24/25 Away Games Against 1-4': 0,
        '24/25 Away Goals Against 1-4': 0,
        '24/25 Away Goals Conceded Against 1-4': 0,
        '24/25 Away Games Against 5-8': 0,
        '24/25 Away Goals Against 5-8': 0,
        '24/25 Away Goals Conceded Against 5-8': 0,
        '24/25 Away Goals Against 9-12': 0,
        '24/25 Away Games Against 9-12': 0,
        '24/25 Away Goals Conceded Against 9-12': 0,
        '24/25 Away Games Against 13-16': 0,
        '24/25 Away Goals Against 13-16': 0,
        '24/25 Away Goals Conceded Against 13-16': 0,
        '24/25 Away Games Against 17-20': 0,
        '24/25 Away Goals Against 17-20': 0,
        '24/25 Away Goals Conceded Against 17-20': 0
        }
    return team_template

def get_player_template(team_name: str, minutes: int, starts: int) -> dict:
    """
    Create a template dictionary for storing player statistics, initialized to default values.

    Args:
        team_name (str): Name of the player's team.
        minutes (int): Total minutes played.
        starts (int): Number of starts.

    Returns:
        dict: Player statistics template.
    """
    player_template = {
            'Team': team_name,
            'Minutes': minutes,
            'Starts': starts,
            'Home Games Played for Current Team': 0,
            'Away Games Played for Current Team': 0,
            'Home Goals for Current Team': 0,
            'Away Goals for Current Team': 0,
            'Home Assists for Current Team': 0,
            'Away Assists for Current Team': 0,
            'Goalkeeper Saves for Current Team': 0,
            '24/25 Home Games Played for Current Team': 0,
            '24/25 Away Games Played for Current Team': 0,
            '24/25 Home Goals for Current Team': 0,
            '24/25 Away Goals for Current Team': 0,
            '24/25 Home Assists for Current Team': 0,
            '24/25 Away Assists for Current Team': 0,
            '24/25 Goalkeeper Saves for Current Team': 0,
            'Home Games Against 1-4': 0,
            'Home Goals Against 1-4': 0,
            'Home Assists Against 1-4': 0,
            'Home Games Against 5-8': 0,
            'Home Goals Against 5-8': 0,
            'Home Assists Against 5-8': 0,
            'Home Games Against 9-12': 0,
            'Home Goals Against 9-12': 0,
            'Home Assists Against 9-12': 0,
            'Home Games Against 13-16': 0,
            'Home Goals Against 13-16': 0,
            'Home Assists Against 13-16': 0,
            'Home Games Against 17-20': 0,
            'Home Goals Against 17-20': 0,
            'Home Assists Against 17-20': 0,
            'Away Games Against 1-4': 0,
            'Away Goals Against 1-4': 0,
            'Away Assists Against 1-4': 0,
            'Away Games Against 5-8': 0,
            'Away Goals Against 5-8': 0,
            'Away Assists Against 5-8': 0,
            'Away Games Against 9-12': 0,
            'Away Goals Against 9-12': 0,
            'Away Assists Against 9-12': 0,
            'Away Games Against 13-16': 0,
            'Away Goals Against 13-16': 0,
            'Away Assists Against 13-16': 0,
            'Away Games Against 17-20': 0,
            'Away Goals Against 17-20': 0,
            'Away Assists Against 17-20': 0,
            '24/25 Home Games Against 1-4': 0,
            '24/25 Home Goals Against 1-4': 0,
            '24/25 Home Assists Against 1-4': 0,
            '24/25 Home Games Against 5-8': 0,
            '24/25 Home Goals Against 5-8': 0,
            '24/25 Home Assists Against 5-8': 0,
            '24/25 Home Games Against 9-12': 0,
            '24/25 Home Goals Against 9-12': 0,
            '24/25 Home Assists Against 9-12': 0,
            '24/25 Home Games Against 13-16': 0,
            '24/25 Home Goals Against 13-16': 0,
            '24/25 Home Assists Against 13-16': 0,
            '24/25 Home Games Against 17-20': 0,
            '24/25 Home Goals Against 17-20': 0,
            '24/25 Home Assists Against 17-20': 0,
            '24/25 Away Games Against 1-4': 0,
            '24/25 Away Goals Against 1-4': 0,
            '24/25 Away Assists Against 1-4': 0,
            '24/25 Away Games Against 5-8': 0,
            '24/25 Away Goals Against 5-8': 0,
            '24/25 Away Assists Against 5-8': 0,
            '24/25 Away Games Against 9-12': 0,
            '24/25 Away Goals Against 9-12': 0,
            '24/25 Away Assists Against 9-12': 0,
            '24/25 Away Games Against 13-16': 0,
            '24/25 Away Goals Against 13-16': 0,
            '24/25 Away Assists Against 13-16': 0,
            '24/25 Away Games Against 17-20': 0,
            '24/25 Away Goals Against 17-20': 0,
            '24/25 Away Assists Against 17-20': 0
            }
    return player_template

def construct_team_and_player_data(
    fpl_data: dict,
    team_id_to_name: dict,
    player_id_to_name: dict,
    fixtures: list
) -> tuple:
    """
    Build and return two dictionaries:
      1. Team statistics (goals, assists, games played, saves, etc.)
      2. Player statistics (games/goals/assists/saves for current team, etc.)

    Args:
        fpl_data (dict): FPL API data.
        team_id_to_name (dict): Mapping from team ID to team name.
        player_id_to_name (dict): Mapping from player ID to player name.
        fixtures (list): List of fixture dictionaries.

    Returns:
        tuple: (team_data, player_data)
    """
    teams = fpl_data['teams']
    elements = fpl_data['elements']
    
    team_data = {}
    player_data = defaultdict(lambda: defaultdict(float))

    fixtures = [fixture for fixture in fixtures if (fixture['finished'] == True)]

    # --- Error handling for CSV loading ---
    try:
        fixtures_24_25_df = pd.read_csv("https://raw.githubusercontent.com/vaastav/Fantasy-Premier-League/master/data/2024-25/fixtures.csv")
        teams_24_25_df = pd.read_csv("https://raw.githubusercontent.com/vaastav/Fantasy-Premier-League/master/data/2024-25/teams.csv")
        player_idlist_24_25_df = pd.read_csv("https://raw.githubusercontent.com/vaastav/Fantasy-Premier-League/master/data/2024-25/player_idlist.csv")

        # Convert DataFrames to lists of dictionaries
        fixtures_24_25 = fixtures_24_25_df.to_dict(orient='records')
        teams_24_25 = teams_24_25_df.to_dict(orient='records')
        player_idlist_24_25 = player_idlist_24_25_df.to_dict(orient='records')

    except Exception as e:
        print(f"Error loading CSV data: {e}", file=sys.stderr)
        fixtures_24_25 = []
        teams_24_25 = []
        player_idlist_24_25 = []

    for row in fixtures_24_25:
        # Convert the 'stats' field from a string to a Python object (list of dictionaries)
        if 'stats' in row:
            row['stats'] = ast.literal_eval(row['stats'])
    
    team_id_to_name_24_25 = {int(team['id']): TEAM_NAMES_ODDSCHECKER.get(team['name'], team['name']) for team in teams_24_25}

    player_id_to_name_24_25 = {int(player['id']): player["first_name"] + " " + player['second_name'] for player in player_idlist_24_25}

    season_24_25_team_positions = {
        'Man City': 3,
        'Arsenal': 2,
        'Man Utd': 15,
        'Newcastle': 5,
        'Liverpool': 1,
        'Brighton': 8,
        'Aston Villa': 6,
        'Tottenham': 17,
        'Brentford': 10,
        'Fulham': 11,
        'Crystal Palace': 12,
        'Chelsea': 4,
        'Wolverhampton': 16,
        'West Ham': 14,
        'Bournemouth': 9,
        'Nottingham Forest': 7,
        'Everton': 13,
        'Leicester': 18,
        'Ipswich': 19,
        'Southampton': 20
        }

    # Initialize team data set to 0
    for team in teams:
        team_name_key = team['name'] if team['name'] is not None else ""
        team_name = TEAM_NAMES_ODDSCHECKER.get(team_name_key, team_name_key)
        pos_24_25 = season_24_25_team_positions.get(team_name, 21)
        pos_current = team.get('position', 21)
        team_data[team_name] = defaultdict(float)
        team_data[team_name].update(get_team_template(pos_24_25, pos_current))

    for player in elements:
        name = " ".join(prepare_name(player_id_to_name[player['id']]))
        team_name_key = player['team'] if player['team'] is not None else ""
        team_name_lookup = team_id_to_name.get(team_name_key, "Unknown")
        team_name = TEAM_NAMES_ODDSCHECKER.get(team_name_lookup, team_name_lookup)
        if team_name is None:
            team_name = ""
        minutes = player['minutes']
        starts = player['starts']
        player_data[name] = defaultdict(float)
        player_data[name].update(get_player_template(team_name, minutes, starts))

    k_factor = 20 # K-factor for ELO rating system

    for fixture in fixtures_24_25:
        home_team_id = int(fixture['team_h'])
        away_team_id = int(fixture['team_a'])
        if home_team_id is None or away_team_id is None:
            continue
        home_team_lookup = team_id_to_name_24_25.get(home_team_id, "Unknown")
        away_team_lookup = team_id_to_name_24_25.get(away_team_id, "Unknown")
        home_team_key = home_team_lookup if home_team_lookup is not None else ""
        away_team_key = away_team_lookup if away_team_lookup is not None else ""
        home_team_name = TEAM_NAMES_ODDSCHECKER.get(home_team_key, home_team_key)
        away_team_name = TEAM_NAMES_ODDSCHECKER.get(away_team_key, away_team_key)
        home_pos_24_25 = season_24_25_team_positions.get(home_team_name, 21)
        away_pos_24_25 = season_24_25_team_positions.get(away_team_name, 21)
        team_data[home_team_name] = team_data.get(
            home_team_name, defaultdict(float, get_team_template(home_pos_24_25, 21))
        )
        team_data[away_team_name] = team_data.get(
            away_team_name, defaultdict(float, get_team_template(away_pos_24_25, 21))
        )

        # Ensure team_data always contains defaultdict(float)
        if not isinstance(team_data.get(home_team_name), defaultdict):
            team_data[home_team_name] = defaultdict(float, team_data[home_team_name])
        if not isinstance(team_data.get(away_team_name), defaultdict):
            team_data[away_team_name] = defaultdict(float, team_data[away_team_name])

        # Update ELO rankings
        home_goals = int(fixture['team_h_score'])
        away_goals = int(fixture['team_a_score'])

        home_pos_range = get_pos_range(home_pos_24_25)
        away_pos_range = get_pos_range(away_pos_24_25)

        home_games_against_string = f"24/25 Home Games Against {away_pos_range}"
        home_goals_against_string = f"24/25 Home Goals Against {away_pos_range}"
        home_goals_conceded_against_string = f"24/25 Home Goals Conceded Against {away_pos_range}"
        home_assists_against_string = f"24/25 Home Assists Against {away_pos_range}"

        away_games_against_string = f"24/25 Away Games Against {home_pos_range}"
        away_goals_against_string = f"24/25 Away Goals Against {home_pos_range}"
        away_goals_conceded_against_string = f"24/25 Away Goals Conceded Against {home_pos_range}"
        away_assists_against_string = f"24/25 Away Assists Against {home_pos_range}"

        team_data[home_team_name]['24/25 Home Goals'] += home_goals
        team_data[away_team_name]['24/25 Away Goals'] += away_goals

        team_data[home_team_name]['24/25 Goals Conceded Home'] += away_goals
        team_data[away_team_name]['24/25 Goals Conceded Away'] += home_goals 
        
        team_data[away_team_name][away_games_against_string] += 1
        team_data[away_team_name][away_goals_against_string] += away_goals
        team_data[away_team_name][away_goals_conceded_against_string] += home_goals

        team_data[home_team_name][home_games_against_string] += 1
        team_data[home_team_name][home_goals_against_string] += home_goals
        team_data[home_team_name][home_goals_conceded_against_string] += away_goals

        home_overall_elo = team_data[home_team_name]['ELO']
        away_overall_elo = team_data[away_team_name]['ELO']

        home_elo = team_data[home_team_name]['Home ELO']
        away_elo = team_data[away_team_name]['Away ELO']

        expected_home = 1 / (10 ** (-(home_elo - away_elo) / 400) + 1)
        expected_away = 1 / (10 ** (-(away_elo - home_elo) / 400) + 1)

        expected_home_overall = 1 / (10 ** (-(home_overall_elo - away_overall_elo) / 400) + 1)
        expected_away_overall = 1 / (10 ** (-(away_overall_elo - home_overall_elo) / 400) + 1)

        if home_goals > away_goals:
            actual_home = 1
            actual_away = 0
        elif home_goals < away_goals:
            actual_home = 0
            actual_away = 1
        else:
            actual_home = 0.5
            actual_away = 0.5

        # Calculate the margin of victory
        goal_difference = abs(home_goals - away_goals)
        margin_multiplier = 1.5 if goal_difference == 2 else 1.75 if goal_difference == 3 else 1.75 + ((goal_difference - 3) / 8) if goal_difference >= 4 else 1

        home_elo_change = k_factor * (actual_home - expected_home) * margin_multiplier
        away_elo_change = k_factor * (actual_away - expected_away) * margin_multiplier

        home_overall_elo_change = k_factor * (actual_home - expected_home_overall) * margin_multiplier
        away_overall_elo_change = k_factor * (actual_away - expected_away_overall) * margin_multiplier

        team_data[home_team_name]['Home ELO'] += home_elo_change
        team_data[away_team_name]['Away ELO'] += away_elo_change

        team_data[home_team_name]['ELO'] += home_overall_elo_change
        team_data[away_team_name]['ELO'] += away_overall_elo_change

        # Add values to both dictionaries by fixture
        for stat in fixture['stats']:
            if stat['identifier'] == 'bps':
                for pair in stat['a']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name_24_25[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name_24_25[pair['element']])):
                            player_data[player]['24/25 Away Games Played for Current Team'] += 1
                            player_data[player][away_games_against_string] += 1

                for pair in stat['h']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name_24_25[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name_24_25[pair['element']])):
                            player_data[player]['24/25 Home Games Played for Current Team'] += 1
                            player_data[player][home_games_against_string] += 1

            if stat['identifier'] == 'goals_scored':
                for pair in stat['a']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name_24_25[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name_24_25[pair['element']])):
                            player_data[player]['24/25 Away Goals for Current Team'] += int(pair['value'])
                            player_data[player][away_goals_against_string] += int(pair['value'])

                for pair in stat['h']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name_24_25[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name_24_25[pair['element']])):
                            player_data[player]['24/25 Home Goals for Current Team'] += int(pair['value'])
                            player_data[player][home_goals_against_string] += int(pair['value'])

            if stat['identifier'] == 'assists':
                for pair in stat['a']:
                    team_data[away_team_name]['24/25 Away Assists'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name_24_25[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name_24_25[pair['element']])): 
                            player_data[player]['24/25 Away Assists for Current Team'] += int(pair['value'])
                            player_data[player][away_assists_against_string] += int(pair['value'])

                for pair in stat['h']:
                    team_data[home_team_name]['24/25 Home Assists'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name_24_25[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name_24_25[pair['element']])): 
                            player_data[player]['24/25 Home Assists for Current Team'] += int(pair['value'])
                            player_data[player][home_assists_against_string] += int(pair['value'])

            if stat['identifier'] == 'saves':
                for pair in stat['a']:
                    team_data[away_team_name]['24/25 Away Goalkeeper Saves'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name_24_25[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name_24_25[pair['element']])):
                            player_data[player]['24/25 Goalkeeper Saves for Current Team'] += int(pair['value'])

                for pair in stat['h']:
                    team_data[home_team_name]['24/25 Home Goalkeeper Saves'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name_24_25[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name_24_25[pair['element']])):
                            player_data[player]['24/25 Goalkeeper Saves for Current Team'] += int(pair['value'])

    # Process each gameweek
    for fixture in fixtures:
        home_team_id = int(fixture['team_h'])
        away_team_id = int(fixture['team_a'])
        home_team_name = TEAM_NAMES_ODDSCHECKER.get(team_id_to_name[home_team_id], team_id_to_name[home_team_id])
        away_team_name = TEAM_NAMES_ODDSCHECKER.get(team_id_to_name[away_team_id], team_id_to_name[away_team_id])
        home_pos = team_data[home_team_name]['League Position']
        away_pos = team_data[away_team_name]['League Position']
        # Update ELO rankings
        home_goals = fixture['team_h_score']
        away_goals = fixture['team_a_score']

        home_pos_range = get_pos_range(home_pos)
        away_pos_range = get_pos_range(away_pos)

        home_games_against_string = f"Home Games Against {away_pos_range}"
        home_goals_against_string = f"Home Goals Against {away_pos_range}"
        home_goals_conceded_against_string = f"Home Goals Conceded Against {away_pos_range}"
        home_assists_against_string = f"Home Assists Against {away_pos_range}"

        away_games_against_string = f"Away Games Against {home_pos_range}"
        away_goals_against_string = f"Away Goals Against {home_pos_range}"
        away_goals_conceded_against_string = f"Away Goals Conceded Against {home_pos_range}"
        away_assists_against_string = f"Away Assists Against {home_pos_range}"

        team_data[home_team_name]['Home Goals'] += home_goals
        team_data[away_team_name]['Away Goals'] += away_goals

        team_data[home_team_name]['Goals Conceded Home'] += away_goals
        team_data[away_team_name]['Goals Conceded Away'] += home_goals 
        
        team_data[away_team_name][away_games_against_string] += 1
        team_data[away_team_name][away_goals_against_string] += away_goals
        team_data[away_team_name][away_goals_conceded_against_string] += home_goals

        team_data[home_team_name][home_games_against_string] += 1
        team_data[home_team_name][home_goals_against_string] += home_goals
        team_data[home_team_name][home_goals_conceded_against_string] += away_goals

        # Increment games played for both teams
        team_data[home_team_name]['Home Games Played'] += 1
        team_data[away_team_name]['Away Games Played'] += 1

        home_overall_elo = team_data[home_team_name]['ELO']
        away_overall_elo = team_data[away_team_name]['ELO']

        home_elo = team_data[home_team_name]['Home ELO']
        away_elo = team_data[away_team_name]['Away ELO']

        expected_home = 1 / (10 ** (-(home_elo - away_elo) / 400) + 1)
        expected_away = 1 / (10 ** (-(away_elo - home_elo) / 400) + 1)

        expected_home_overall = 1 / (10 ** (-(home_overall_elo - away_overall_elo) / 400) + 1)
        expected_away_overall = 1 / (10 ** (-(away_overall_elo - home_overall_elo) / 400) + 1)

        if home_goals > away_goals:
            actual_home = 1
            actual_away = 0
        elif home_goals < away_goals:
            actual_home = 0
            actual_away = 1
        else:
            actual_home = 0.5
            actual_away = 0.5

        # Calculate the margin of victory
        goal_difference = abs(home_goals - away_goals)
        margin_multiplier = 1.5 if goal_difference == 2 else 1.75 if goal_difference == 3 else 1.75 + ((goal_difference - 3) / 8) if goal_difference >= 4 else 1

        home_elo_change = k_factor * (actual_home - expected_home) * margin_multiplier
        away_elo_change = k_factor * (actual_away - expected_away) * margin_multiplier

        home_overall_elo_change = k_factor * (actual_home - expected_home_overall) * margin_multiplier
        away_overall_elo_change = k_factor * (actual_away - expected_away_overall) * margin_multiplier

        team_data[home_team_name]['Home ELO'] += home_elo_change
        team_data[away_team_name]['Away ELO'] += away_elo_change

        team_data[home_team_name]['ELO'] += home_overall_elo_change
        team_data[away_team_name]['ELO'] += away_overall_elo_change

        # Add values to both dictionaries by fixture
        for stat in fixture['stats']:
            if stat['identifier'] == 'bps':
                for pair in stat['a']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['Away Games Played for Current Team'] += 1
                            player_data[player][away_games_against_string] += 1
                for pair in stat['h']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['Home Games Played for Current Team'] += 1
                            player_data[player][home_games_against_string] += 1
                            
            if stat['identifier'] == 'goals_scored':
                for pair in stat['a']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['Away Goals for Current Team'] += int(pair['value'])
                            player_data[player][away_goals_against_string] += int(pair['value'])
                for pair in stat['h']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['Home Goals for Current Team'] += int(pair['value'])
                            player_data[player][home_goals_against_string] += int(pair['value'])
            if stat['identifier'] == 'assists':
                for pair in stat['a']:
                    team_data[away_team_name]['Away Assists'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])): 
                            player_data[player]['Away Assists for Current Team'] += int(pair['value'])
                            player_data[player][away_assists_against_string] += int(pair['value'])
                for pair in stat['h']:
                    team_data[home_team_name]['Home Assists'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['Home Assists for Current Team'] += int(pair['value'])
                            player_data[player][home_assists_against_string] += int(pair['value'])
            if stat['identifier'] == 'saves':
                for pair in stat['a']:
                    team_data[away_team_name]['Away Goalkeeper Saves'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['Goalkeeper Saves for Current Team'] += int(pair['value'])
                for pair in stat['h']:
                    team_data[home_team_name]['Home Goalkeeper Saves'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['Goalkeeper Saves for Current Team'] += int(pair['value'])
    
    for team in team_data:
        team_data[team]['HFA'] = float(team_data[team]['Home ELO'] - team_data[team]['Away ELO']) if team_data[team]['Away ELO'] != 0 else 0

        team_data[team]['Goalkeeper Saves per Home Game'] = float(team_data[team]['Home Goalkeeper Saves']/team_data[team]['Home Games Played']) if team_data[team]['Home Games Played'] != 0 else 0
        team_data[team]['Goalkeeper Saves per Away Game'] = float(team_data[team]['Away Goalkeeper Saves']/team_data[team]['Away Games Played']) if team_data[team]['Away Games Played'] != 0 else 0
        team_data[team]['Goals per Game'] = float((team_data[team]['Home Goals'] + team_data[team]['Away Goals'])/(team_data[team]['Home Games Played'] + team_data[team]['Away Games Played'])) if (team_data[team]['Home Games Played'] + team_data[team]['Away Games Played']) != 0 else 0
        team_data[team]['Goals per Home Game'] = float(team_data[team]['Home Goals']/team_data[team]['Home Games Played']) if team_data[team]['Home Games Played'] != 0 else 0
        team_data[team]['Goals per Away Game'] = float(team_data[team]['Away Goals']/team_data[team]['Away Games Played']) if team_data[team]['Away Games Played'] != 0 else 0
        team_data[team]['Goals Conceded per Game'] = float((team_data[team]['Goals Conceded Home'] + team_data[team]['Goals Conceded Away'])/(team_data[team]['Home Games Played'] + team_data[team]['Away Games Played'])) if (team_data[team]['Home Games Played'] + team_data[team]['Away Games Played']) != 0 else 0
        team_data[team]['Goals Conceded per Home Game'] = float(team_data[team]['Goals Conceded Home']/team_data[team]['Home Games Played']) if team_data[team]['Home Games Played'] != 0 else 0
        team_data[team]['Goals Conceded per Away Game'] = float(team_data[team]['Goals Conceded Away']/team_data[team]['Away Games Played']) if team_data[team]['Away Games Played'] != 0 else 0

        team_data[team]['Goals per Home Game Against 1-4'] = float(team_data[team]['Home Goals Against 1-4']/team_data[team]['Home Games Against 1-4']) if team_data[team]['Home Games Against 1-4'] != 0 else 0
        team_data[team]['Goals Conceded per Home Game Against 1-4'] = float(team_data[team]['Home Goals Conceded Against 1-4']/team_data[team]['Home Games Against 1-4']) if team_data[team]['Home Games Against 1-4'] != 0 else 0
        team_data[team]['Goals per Home Game Against 5-8'] = float(team_data[team]['Home Goals Against 5-8']/team_data[team]['Home Games Against 5-8']) if team_data[team]['Home Games Against 5-8'] != 0 else 0
        team_data[team]['Goals Conceded per Home Game Against 5-8'] = float(team_data[team]['Home Goals Conceded Against 5-8']/team_data[team]['Home Games Against 5-8']) if team_data[team]['Home Games Against 5-8'] != 0 else 0
        team_data[team]['Goals per Home Game Against 9-12'] = float(team_data[team]['Home Goals Against 9-12']/team_data[team]['Home Games Against 9-12']) if team_data[team]['Home Games Against 9-12'] != 0 else 0
        team_data[team]['Goals Conceded per Home Game Against 9-12'] = float(team_data[team]['Home Goals Conceded Against 9-12']/team_data[team]['Home Games Against 9-12']) if team_data[team]['Home Games Against 9-12'] != 0 else 0
        team_data[team]['Goals per Home Game Against 13-16'] = float(team_data[team]['Home Goals Against 13-16']/team_data[team]['Home Games Against 13-16']) if team_data[team]['Home Games Against 13-16'] != 0 else 0
        team_data[team]['Goals Conceded per Home Game Against 13-16'] = float(team_data[team]['Home Goals Conceded Against 13-16']/team_data[team]['Home Games Against 13-16']) if team_data[team]['Home Games Against 13-16'] != 0 else 0
        team_data[team]['Goals per Home Game Against 17-20'] = float(team_data[team]['Home Goals Against 17-20']/team_data[team]['Home Games Against 17-20']) if team_data[team]['Home Games Against 17-20'] != 0 else 0
        team_data[team]['Goals Conceded per Home Game Against 17-20'] = float(team_data[team]['Home Goals Conceded Against 17-20']/team_data[team]['Home Games Against 17-20']) if team_data[team]['Home Games Against 17-20'] != 0 else 0

        team_data[team]['Goals per Away Game Against 1-4'] = float(team_data[team]['Away Goals Against 1-4']/team_data[team]['Away Games Against 1-4']) if team_data[team]['Away Games Against 1-4'] != 0 else 0
        team_data[team]['Goals Conceded per Away Game Against 1-4'] = float(team_data[team]['Away Goals Conceded Against 1-4']/team_data[team]['Away Games Against 1-4']) if team_data[team]['Away Games Against 1-4'] != 0 else 0
        team_data[team]['Goals per Away Game Against 5-8'] = float(team_data[team]['Away Goals Against 5-8']/team_data[team]['Away Games Against 5-8']) if team_data[team]['Away Games Against 5-8'] != 0 else 0
        team_data[team]['Goals Conceded per Away Game Against 5-8'] = float(team_data[team]['Away Goals Conceded Against 5-8']/team_data[team]['Away Games Against 5-8']) if team_data[team]['Away Games Against 5-8'] != 0 else 0
        team_data[team]['Goals per Away Game Against 9-12'] = float(team_data[team]['Away Goals Against 9-12']/team_data[team]['Away Games Against 9-12']) if team_data[team]['Away Games Against 9-12'] != 0 else 0
        team_data[team]['Goals Conceded per Away Game Against 9-12'] = float(team_data[team]['Away Goals Conceded Against 9-12']/team_data[team]['Away Games Against 9-12']) if team_data[team]['Away Games Against 9-12'] != 0 else 0
        team_data[team]['Goals per Away Game Against 13-16'] = float(team_data[team]['Away Goals Against 13-16']/team_data[team]['Away Games Against 13-16']) if team_data[team]['Away Games Against 13-16'] != 0 else 0
        team_data[team]['Goals Conceded per Away Game Against 13-16'] = float(team_data[team]['Away Goals Conceded Against 13-16']/team_data[team]['Away Games Against 13-16']) if team_data[team]['Away Games Against 13-16'] != 0 else 0
        team_data[team]['Goals per Away Game Against 17-20'] = float(team_data[team]['Away Goals Against 17-20']/team_data[team]['Away Games Against 17-20']) if team_data[team]['Away Games Against 17-20'] != 0 else 0
        team_data[team]['Goals Conceded per Away Game Against 17-20'] = float(team_data[team]['Away Goals Conceded Against 17-20']/team_data[team]['Away Games Against 17-20']) if team_data[team]['Away Games Against 17-20'] != 0 else 0

        team_data[team]['24/25 Goalkeeper Saves per Home Game'] = float(team_data[team]['24/25 Home Goalkeeper Saves']/19)
        team_data[team]['24/25 Goalkeeper Saves per Away Game'] = float(team_data[team]['24/25 Away Goalkeeper Saves']/19)
        team_data[team]['24/25 Goals per Home Game'] = float(team_data[team]['24/25 Home Goals']/19)
        team_data[team]['24/25 Goals per Away Game'] = float(team_data[team]['24/25 Away Goals']/19)
        team_data[team]['24/25 Goals Conceded per Home Game'] = float(team_data[team]['24/25 Goals Conceded Home']/19)
        team_data[team]['24/25 Goals Conceded per Away Game'] = float(team_data[team]['24/25 Goals Conceded Away']/19)

        team_data[team]['24/25 Goals per Home Game Against 1-4'] = float(team_data[team]['24/25 Home Goals Against 1-4']/team_data[team]['24/25 Home Games Against 1-4']) if team_data[team]['24/25 Home Games Against 1-4'] > 0 else 0
        team_data[team]['24/25 Goals Conceded per Home Game Against 1-4'] = float(team_data[team]['24/25 Home Goals Conceded Against 1-4']/team_data[team]['24/25 Home Games Against 1-4']) if team_data[team]['24/25 Home Games Against 1-4'] > 0 else 0
        team_data[team]['24/25 Goals per Home Game Against 5-8'] = float(team_data[team]['24/25 Home Goals Against 5-8']/team_data[team]['24/25 Home Games Against 5-8']) if team_data[team]['24/25 Home Games Against 5-8'] > 0 else 0
        team_data[team]['24/25 Goals Conceded per Home Game Against 5-8'] = float(team_data[team]['24/25 Home Goals Conceded Against 5-8']/team_data[team]['24/25 Home Games Against 5-8']) if team_data[team]['24/25 Home Games Against 5-8'] > 0 else 0
        team_data[team]['24/25 Goals per Home Game Against 9-12'] = float(team_data[team]['24/25 Home Goals Against 9-12']/team_data[team]['24/25 Home Games Against 9-12']) if team_data[team]['24/25 Home Games Against 9-12'] > 0 else 0
        team_data[team]['24/25 Goals Conceded per Home Game Against 9-12'] = float(team_data[team]['24/25 Home Goals Conceded Against 9-12']/team_data[team]['24/25 Home Games Against 9-12'])if team_data[team]['24/25 Home Games Against 9-12'] > 0 else 0
        team_data[team]['24/25 Goals per Home Game Against 13-16'] = float(team_data[team]['24/25 Home Goals Against 13-16']/team_data[team]['24/25 Home Games Against 13-16']) if team_data[team]['24/25 Home Games Against 13-16'] > 0 else 0
        team_data[team]['24/25 Goals Conceded per Home Game Against 13-16'] = float(team_data[team]['24/25 Home Goals Conceded Against 13-16']/team_data[team]['24/25 Home Games Against 13-16']) if team_data[team]['24/25 Home Games Against 13-16'] > 0 else 0
        team_data[team]['24/25 Goals per Home Game Against 17-20'] = float(team_data[team]['24/25 Home Goals Against 17-20']/team_data[team]['24/25 Home Games Against 17-20']) if team_data[team]['24/25 Home Games Against 17-20'] > 0 else 0
        team_data[team]['24/25 Goals Conceded per Home Game Against 17-20'] = float(team_data[team]['24/25 Home Goals Conceded Against 17-20']/team_data[team]['24/25 Home Games Against 17-20']) if team_data[team]['24/25 Home Games Against 17-20'] > 0 else 0
        team_data[team]['24/25 Goals per Away Game Against 1-4'] = float(team_data[team]['24/25 Away Goals Against 1-4']/team_data[team]['24/25 Away Games Against 1-4']) if team_data[team]['24/25 Away Games Against 1-4'] > 0 else 0
        team_data[team]['24/25 Goals Conceded per Away Game Against 1-4'] = float(team_data[team]['24/25 Away Goals Conceded Against 1-4']/team_data[team]['24/25 Away Games Against 1-4']) if team_data[team]['24/25 Away Games Against 1-4'] > 0 else 0
        team_data[team]['24/25 Goals per Away Game Against 5-8'] = float(team_data[team]['24/25 Away Goals Against 5-8']/team_data[team]['24/25 Away Games Against 5-8']) if team_data[team]['24/25 Away Games Against 5-8'] > 0 else 0
        team_data[team]['24/25 Goals Conceded per Away Game Against 5-8'] = float(team_data[team]['24/25 Away Goals Conceded Against 5-8']/team_data[team]['24/25 Away Games Against 5-8']) if team_data[team]['24/25 Away Games Against 5-8'] > 0 else 0
        team_data[team]['24/25 Goals per Away Game Against 9-12'] = float(team_data[team]['24/25 Away Goals Against 9-12']/team_data[team]['24/25 Away Games Against 9-12']) if team_data[team]['24/25 Away Games Against 9-12'] > 0 else 0
        team_data[team]['24/25 Goals Conceded per Away Game Against 9-12'] = float(team_data[team]['24/25 Away Goals Conceded Against 9-12']/team_data[team]['24/25 Away Games Against 9-12']) if team_data[team]['24/25 Away Games Against 9-12'] > 0 else 0
        team_data[team]['24/25 Goals per Away Game Against 13-16'] = float(team_data[team]['24/25 Away Goals Against 13-16']/team_data[team]['24/25 Away Games Against 13-16']) if team_data[team]['24/25 Away Games Against 13-16'] > 0 else 0
        team_data[team]['24/25 Goals Conceded per Away Game Against 13-16'] = float(team_data[team]['24/25 Away Goals Conceded Against 13-16']/team_data[team]['24/25 Away Games Against 13-16']) if team_data[team]['24/25 Away Games Against 13-16'] > 0 else 0
        team_data[team]['24/25 Goals per Away Game Against 17-20'] = float(team_data[team]['24/25 Away Goals Against 17-20']/team_data[team]['24/25 Away Games Against 17-20']) if team_data[team]['24/25 Away Games Against 17-20'] > 0 else 0
        team_data[team]['24/25 Goals Conceded per Away Game Against 17-20'] = float(team_data[team]['24/25 Away Goals Conceded Against 17-20']/team_data[team]['24/25 Away Games Against 17-20']) if team_data[team]['24/25 Away Games Against 17-20'] > 0 else 0
            
    for player in player_data:
        games_played = max((player_data[player]['Home Games Played for Current Team'] + player_data[player]['Away Games Played for Current Team']), player_data[player]['Starts'])
        player_data[player]['Minutes per Game'] = float(player_data[player]['Minutes']/games_played) if games_played != 0 else 0

        player_data[player]['Goals per Home Game'] = float(player_data[player]['Home Goals for Current Team']/player_data[player]['Home Games Played for Current Team']) if player_data[player]['Home Games Played for Current Team'] != 0 else 0
        player_data[player]['Goals per Home Game Against 1-4'] = float(player_data[player]['Home Goals Against 1-4']/player_data[player]['Home Games Against 1-4']) if player_data[player]['Home Games Against 1-4'] != 0 else 0
        player_data[player]['Assists per Home Game'] = float(player_data[player]['Home Assists for Current Team']/player_data[player]['Home Games Played for Current Team']) if player_data[player]['Home Games Played for Current Team'] != 0 else 0
        player_data[player]['Assists per Home Game Against 1-4'] = float(player_data[player]['Home Assists Against 1-4']/player_data[player]['Home Games Against 1-4']) if player_data[player]['Home Games Against 1-4'] != 0 else 0
        player_data[player]['Goals per Home Game Against 5-8'] = float(player_data[player]['Home Goals Against 5-8']/player_data[player]['Home Games Against 5-8']) if player_data[player]['Home Games Against 5-8'] != 0 else 0
        player_data[player]['Assists per Home Game Against 5-8'] = float(player_data[player]['Home Assists Against 5-8']/player_data[player]['Home Games Against 5-8']) if player_data[player]['Home Games Against 5-8'] != 0 else 0
        player_data[player]['Goals per Home Game Against 9-12'] = float(player_data[player]['Home Goals Against 9-12']/player_data[player]['Home Games Against 9-12']) if player_data[player]['Home Games Against 9-12'] != 0 else 0
        player_data[player]['Assists per Home Game Against 9-12'] = float(player_data[player]['Home Assists Against 9-12']/player_data[player]['Home Games Against 9-12']) if player_data[player]['Home Games Against 9-12'] != 0 else 0
        player_data[player]['Goals per Home Game Against 13-16'] = float(player_data[player]['Home Goals Against 13-16']/player_data[player]['Home Games Against 13-16']) if player_data[player]['Home Games Against 13-16'] != 0 else 0
        player_data[player]['Assists per Home Game Against 13-16'] = float(player_data[player]['Home Assists Against 13-16']/player_data[player]['Home Games Against 13-16']) if player_data[player]['Home Games Against 13-16'] != 0 else 0
        player_data[player]['Goals per Home Game Against 17-20'] = float(player_data[player]['Home Goals Against 17-20']/player_data[player]['Home Games Against 17-20']) if player_data[player]['Home Games Against 17-20'] != 0 else 0
        player_data[player]['Assists per Home Game Against 17-20'] = float(player_data[player]['Home Assists Against 17-20']/player_data[player]['Home Games Against 17-20']) if player_data[player]['Home Games Against 17-20'] != 0 else 0
        player_data[player]['Goals per Away Game'] = float(player_data[player]['Away Goals for Current Team']/player_data[player]['Away Games Played for Current Team']) if player_data[player]['Away Games Played for Current Team'] != 0 else 0
        player_data[player]['Goals per Away Game Against 1-4'] = float(player_data[player]['Away Goals Against 1-4']/player_data[player]['Away Games Against 1-4']) if player_data[player]['Away Games Against 1-4'] != 0 else 0
        player_data[player]['Assists per Away Game'] = float(player_data[player]['Away Assists for Current Team']/player_data[player]['Away Games Played for Current Team']) if player_data[player]['Away Games Played for Current Team'] != 0 else 0
        player_data[player]['Assists per Away Game Against 1-4'] = float(player_data[player]['Away Assists Against 1-4']/player_data[player]['Away Games Against 1-4']) if player_data[player]['Away Games Against 1-4'] != 0 else 0
        player_data[player]['Goals per Away Game Against 5-8'] = float(player_data[player]['Away Goals Against 5-8']/player_data[player]['Away Games Against 5-8']) if player_data[player]['Away Games Against 5-8'] != 0 else 0
        player_data[player]['Assists per Away Game Against 5-8'] = float(player_data[player]['Away Assists Against 5-8']/player_data[player]['Away Games Against 5-8']) if player_data[player]['Away Games Against 5-8'] != 0 else 0
        player_data[player]['Goals per Away Game Against 9-12'] = float(player_data[player]['Away Goals Against 9-12']/player_data[player]['Away Games Against 9-12']) if player_data[player]['Away Games Against 9-12'] != 0 else 0
        player_data[player]['Assists per Away Game Against 9-12'] = float(player_data[player]['Away Assists Against 9-12']/player_data[player]['Away Games Against 9-12']) if player_data[player]['Away Games Against 9-12'] != 0 else 0
        player_data[player]['Goals per Away Game Against 13-16'] = float(player_data[player]['Away Goals Against 13-16']/player_data[player]['Away Games Against 13-16']) if player_data[player]['Away Games Against 13-16'] != 0 else 0
        player_data[player]['Assists per Away Game Against 13-16'] = float(player_data[player]['Away Assists Against 13-16']/player_data[player]['Away Games Against 13-16']) if player_data[player]['Away Games Against 13-16'] != 0 else 0
        player_data[player]['Goals per Away Game Against 17-20'] = float(player_data[player]['Away Goals Against 17-20']/player_data[player]['Away Games Against 17-20']) if player_data[player]['Away Games Against 17-20'] != 0 else 0
        player_data[player]['Assists per Away Game Against 17-20'] = float(player_data[player]['Away Assists Against 17-20']/player_data[player]['Away Games Against 17-20']) if player_data[player]['Away Games Against 17-20'] != 0 else 0

        player_data[player]['24/25 Goals per Home Game'] = float(player_data[player]['24/25 Home Goals for Current Team']/player_data[player]['24/25 Home Games Played for Current Team']) if player_data[player]['24/25 Home Games Played for Current Team'] != 0 else 0
        player_data[player]['24/25 Goals per Home Game Against 1-4'] = float(player_data[player]['24/25 Home Goals Against 1-4']/player_data[player]['24/25 Home Games Against 1-4']) if player_data[player]['24/25 Home Games Against 1-4'] != 0 else 0
        player_data[player]['24/25 Assists per Home Game'] = float(player_data[player]['24/25 Home Assists for Current Team']/player_data[player]['24/25 Home Games Played for Current Team']) if player_data[player]['24/25 Home Games Played for Current Team'] != 0 else 0
        player_data[player]['24/25 Assists per Home Game Against 1-4'] = float(player_data[player]['24/25 Home Assists Against 1-4']/player_data[player]['24/25 Home Games Against 1-4']) if player_data[player]['24/25 Home Games Against 1-4'] != 0 else 0
        player_data[player]['24/25 Goals per Home Game Against 5-8'] = float(player_data[player]['24/25 Home Goals Against 5-8']/player_data[player]['24/25 Home Games Against 5-8']) if player_data[player]['24/25 Home Games Against 5-8'] != 0 else 0
        player_data[player]['24/25 Assists per Home Game Against 5-8'] = float(player_data[player]['24/25 Home Assists Against 5-8']/player_data[player]['24/25 Home Games Against 5-8']) if player_data[player]['24/25 Home Games Against 5-8'] != 0 else 0
        player_data[player]['24/25 Goals per Home Game Against 9-12'] = float(player_data[player]['24/25 Home Goals Against 9-12']/player_data[player]['24/25 Home Games Against 9-12']) if player_data[player]['24/25 Home Games Against 9-12'] != 0 else 0
        player_data[player]['24/25 Assists per Home Game Against 9-12'] = float(player_data[player]['24/25 Home Assists Against 9-12']/player_data[player]['24/25 Home Games Against 9-12']) if player_data[player]['24/25 Home Games Against 9-12'] != 0 else 0
        player_data[player]['24/25 Goals per Home Game Against 13-16'] = float(player_data[player]['24/25 Home Goals Against 13-16']/player_data[player]['24/25 Home Games Against 13-16']) if player_data[player]['24/25 Home Games Against 13-16'] != 0 else 0
        player_data[player]['24/25 Assists per Homer Game Against 13-16'] = float(player_data[player]['24/25 Home Assists Against 13-16']/player_data[player]['24/25 Home Games Against 13-16']) if player_data[player]['24/25 Home Games Against 13-16'] != 0 else 0
        player_data[player]['24/25 Goals per Home Game Against 17-20'] = float(player_data[player]['24/25 Home Goals Against 17-20']/player_data[player]['24/25 Home Games Against 17-20']) if player_data[player]['24/25 Home Games Against 17-20'] != 0 else 0
        player_data[player]['24/25 Assists per Home Game Against 17-20'] = float(player_data[player]['24/25 Home Assists Against 17-20']/player_data[player]['24/25 Home Games Against 17-20']) if player_data[player]['24/25 Home Games Against 17-20'] != 0 else 0
        player_data[player]['24/25 Goals per Away Game'] = float(player_data[player]['24/25 Away Goals for Current Team']/player_data[player]['24/25 Away Games Played for Current Team']) if player_data[player]['24/25 Away Games Played for Current Team'] != 0 else 0
        player_data[player]['24/25 Goals per Away Game Against 1-4'] = float(player_data[player]['24/25 Away Goals Against 1-4']/player_data[player]['24/25 Away Games Against 1-4']) if player_data[player]['24/25 Away Games Against 1-4'] != 0 else 0
        player_data[player]['24/25 Assists per Away Game'] = float(player_data[player]['24/25 Away Assists for Current Team']/player_data[player]['24/25 Away Games Played for Current Team']) if player_data[player]['24/25 Away Games Played for Current Team'] != 0 else 0
        player_data[player]['24/25 Assists per Away Game Against 1-4'] = float(player_data[player]['24/25 Away Assists Against 1-4']/player_data[player]['24/25 Away Games Against 1-4']) if player_data[player]['24/25 Away Games Against 1-4'] != 0 else 0
        player_data[player]['24/25 Goals per Away Game Against 5-8'] = float(player_data[player]['24/25 Away Goals Against 5-8']/player_data[player]['24/25 Away Games Against 5-8']) if player_data[player]['24/25 Away Games Against 5-8'] != 0 else 0
        player_data[player]['24/25 Assists per Away Game Against 5-8'] = float(player_data[player]['24/25 Away Assists Against 5-8']/player_data[player]['24/25 Away Games Against 5-8']) if player_data[player]['24/25 Away Games Against 5-8'] != 0 else 0
        player_data[player]['24/25 Goals per Away Game Against 9-12'] = float(player_data[player]['24/25 Away Goals Against 9-12']/player_data[player]['24/25 Away Games Against 9-12']) if player_data[player]['24/25 Away Games Against 9-12'] != 0 else 0
        player_data[player]['24/25 Assists per Away Game Against 9-12'] = float(player_data[player]['24/25 Away Assists Against 9-12']/player_data[player]['24/25 Away Games Against 9-12']) if player_data[player]['24/25 Away Games Against 9-12'] != 0 else 0
        player_data[player]['24/25 Goals per Away Game Against 13-16'] = float(player_data[player]['24/25 Away Goals Against 13-16']/player_data[player]['24/25 Away Games Against 13-16']) if player_data[player]['24/25 Away Games Against 13-16'] != 0 else 0
        player_data[player]['24/25 Assists per Away Game Against 13-16'] = float(player_data[player]['24/25 Away Assists Against 13-16']/player_data[player]['24/25 Away Games Against 13-16']) if player_data[player]['24/25 Away Games Against 13-16'] != 0 else 0
        player_data[player]['24/25 Goals per Away Game Against 17-20'] = float(player_data[player]['24/25 Away Goals Against 17-20']/player_data[player]['24/25 Away Games Against 17-20']) if player_data[player]['24/25 Away Games Against 17-20'] != 0 else 0
        player_data[player]['24/25 Assists per Away Game Against 17-20'] = float(player_data[player]['24/25 Away Assists Against 17-20']/player_data[player]['24/25 Away Games Against 17-20']) if player_data[player]['24/25 Away Games Against 17-20'] != 0 else 0

    team_json_data = json.dumps(team_data, indent=4)
    with open('team_data.json', 'w') as f:
        f.write(team_json_data)

    player_json_data = json.dumps(player_data, indent=4)
    with open('player_data.json', 'w') as f2:
        f2.write(player_json_data)

    team_data_df = pd.DataFrame.from_dict(team_data, orient='index')
    team_data_df.index.name = 'Team'
    player_data_df = pd.DataFrame.from_dict(player_data, orient='index')
    player_data_df.index.name = 'Player'

    with pd.ExcelWriter(f"historical_data_output.xlsx") as writer:
        team_data_df.to_excel(writer, sheet_name='Teams')
        player_data_df.to_excel(writer, sheet_name='Players')

    return team_data, player_data

def get_player_over_probs(
    odd_type: str,
    odds_dict: dict,
    player_dict: dict,
    home_team: str,
    away_team: str
) -> None:
    """
    Calculate player 'Over X' probabilities from odds and update player_dict.

    Args:
        odd_type (str): Odds market type.
        odds_dict (dict): Mapping from player/outcome to odds.
        player_dict (dict): Player details dictionary.
        home_team (str): Home team name.
        away_team (str): Away team name.
    """
    bookmaker_margin = 0.05
    if odd_type == "Player Assists":
        odds_for = ['Over 0.5', 'Over 1.5', 'Over 2.5']
    else:
        odds_for = ['Over 0.5 Saves', 'Over 1.5 Saves', 'Over 2.5 Saves', 'Over 3.5 Saves', 'Over 4.5 Saves', 'Over 5.5 Saves', 'Over 6.5 Saves', 'Over 7.5 Saves', 'Over 8.5 Saves', 'Over 9.5 Saves']
    try:
        for player_odd, odds_list in odds_dict.items():
            index = player_odd.find("Over")
            odd_for = player_odd[index:].strip()
            if odd_for in odds_for:
                if len(odds_list) > 0:
                    odd = (sum(odds_list)/len(odds_list)) / (1 - bookmaker_margin)
                else:
                    odd = 0
                if odd_type == "Goalkeeper Saves":
                    name = player_odd[:index].replace("Saves", '').strip()
                    odd_for = odd_for.replace("Saves", '').strip()
                else:
                    name = player_odd[:index].strip()
                probability = 1/float(odd) if odd != 0 else 0
            else:
                continue
            try:
                matched_name = None  # Ensure matched_name is always defined
                for p in player_dict:
                    # Prepare the player name for comparison
                    player_tokens = prepare_name(p)
                    webname_tokens = prepare_name(name)

                    # Check if all tokens in one name exist in the other
                    if all(token in webname_tokens for token in player_tokens) or all(token in player_tokens for token in webname_tokens):
                        matched_name = p
                        break

                # Add the odds to the player's dictionary
                if matched_name is not None:
                    player_dict[matched_name][f"{odd_for} {odd_type} Probability"].append(probability)
                else:
                    for p in player_dict:
                        # Prepare the player name for comparison
                        webname_tokens = prepare_name(name)
                        nickname1 = player_dict[p]['Nickname'][0]
                        nickname2 = player_dict[p]['Nickname2'][0]
                        nickname1_tokens = prepare_name(nickname1)
                        nickname2_tokens = prepare_name(nickname2)

                        if (" ".join(nickname2_tokens) in " ".join(webname_tokens) or " ".join(nickname1_tokens) in " ".join(webname_tokens)) and (player_dict[p]['Team'][0] in [home_team, away_team]):
                            matched_name = p
                            break
                        else:
                            p_name = PLAYER_NAMES_ODDSCHECKER.get(name, "Unknown")
                            if p_name != "Unknown":
                                matched_name = p_name
                                break
                        
                    if matched_name:
                        player_dict[matched_name][f"{odd_for} {odd_type} Probability"].append(probability)

                    else:
                        player_dict[name]['Nickname'] = ['Unknown']
                        player_dict[name]['Nickname2'] = ['Unknown']
                        player_dict[name]['Position'] = ['Unknown']
                        player_dict[name]['Team'] = ["Unknown"]
                        player_dict[name][f"{odd_for} {odd_type} Probability"].append(probability)
            except Exception as e:
                print("Couldn't update player_dict", e)
    except Exception as e:
        print("Couldn't calculate probabilities for ", odd_type, " ", e)

def get_total_goals_over_probs(odds_dict: dict, team: str) -> typing.Optional[dict]:
    """
    Calculate probabilities for total goals scored by a team using Over X odds.

    Args:
        odds_dict (dict): Mapping from outcome to odds.
        team (str): 'home' or 'away'.

    Returns:
        dict: Probabilities for 0-6+ goals scored by the team.
    """
    bookmaker_margin = 0.05
    try:
        team_over_05_odd, team_over_15_odd, team_over_25_odd, team_over_35_odd, team_over_45_odd, team_over_55_odd = 0,0,0,0,0,0
        for team_odd, odds_list in odds_dict.items():
            if len(odds_list) != 0:
                ave_odd = (sum(odds_list)/len(odds_list)) / (1 - bookmaker_margin)
            else:
                ave_odd = 0
            if team_odd == "Over 0.5":
                team_over_05_odd = ave_odd
            if team_odd == "Over 1.5":
                team_over_15_odd = ave_odd
            if team_odd == "Over 2.5":
                team_over_25_odd = ave_odd
            if team_odd == "Over 3.5":
                team_over_35_odd = ave_odd
            if team_odd == "Over 4.5":
                team_over_45_odd = ave_odd
            if team_odd == "Over 5.5":
                team_over_55_odd = ave_odd

        try:
            team_over_05_prob = 1/float(team_over_05_odd) if team_over_05_odd != 0 else 0
            team_over_15_prob = 1/float(team_over_15_odd) if team_over_15_odd != 0 else 0
            team_over_25_prob = 1/float(team_over_25_odd) if team_over_25_odd != 0 else 0
            team_over_35_prob = 1/float(team_over_35_odd) if team_over_35_odd != 0 else 0
            team_over_45_prob = 1/float(team_over_45_odd) if team_over_45_odd != 0 else 0
            team_over_55_prob = 1/float(team_over_55_odd) if team_over_55_odd != 0 else 0

            try:
                team_0_goal_prob = 1 - team_over_05_prob if team_over_05_prob != 0 else 0
                team_6_goal_prob = team_over_55_prob
                team_1_goal_prob = max(team_over_05_prob - team_over_15_prob, 0) if team_over_05_prob != 0 and team_over_15_prob != 0 else team_over_05_prob
                team_2_goal_prob = max(team_over_15_prob - team_over_25_prob, 0) if team_over_15_prob != 0 and team_over_25_prob != 0 else team_over_15_prob
                team_3_goal_prob = max(team_over_25_prob - team_over_35_prob, 0) if team_over_25_prob != 0 and team_over_35_prob != 0 else team_over_25_prob
                team_4_goal_prob = max(team_over_35_prob - team_over_45_prob, 0) if team_over_35_prob != 0 and team_over_45_prob != 0 else team_over_35_prob
                team_5_goal_prob = max(team_over_45_prob - team_over_55_prob, 0) if team_over_45_prob != 0 and team_over_55_prob != 0 else team_over_45_prob
                
            except Exception as e:
                print(f"Couldnt calculate probabilities for Total {team.capitalize()} Goals", e)
                return None  
        except Exception as e:
            print(f"Couldnt calculate probabilities for Total {team.capitalize()} Over Goals", e)
            return None  
        return {team + '_0_goal_prob': team_0_goal_prob, team + '_1_goal_prob': team_1_goal_prob, team + '_2_goals_prob': team_2_goal_prob, team + '_3_goals_prob': team_3_goal_prob, team + '_4_goals_prob': team_4_goal_prob, team + '_5_goals_prob': team_5_goal_prob, team + '_6_goals_prob': team_6_goal_prob}      
    except Exception as e:
        print(f"Couldnt find probabilities from odds_dict for Total {team.capitalize()} Over Goals", e)
        return None
    
def add_total_goals_probs_to_dict(
    probs_dict: dict,
    home_team: str,
    away_team: str,
    player_dict: dict
) -> None:
    """
    Add calculated home/away goals probabilities to each player's dictionary.

    Args:
        probs_dict (dict): Probabilities for goals scored/conceded.
        home_team (str): Home team name.
        away_team (str): Away team name.
        player_dict (dict): Player details dictionary.
    """
    for player in player_dict:
        if player_dict[player]['Team'][0] == home_team:
            home_goals_conceded_average = probs_dict["away_1_goal_prob"] + 2 * probs_dict["away_2_goals_prob"] + 3 * probs_dict["away_3_goals_prob"] + 4 * probs_dict["away_4_goals_prob"] + 5 * probs_dict["away_5_goals_prob"] + 6 * probs_dict["away_6_goals_prob"]
            player_dict[player]['Clean Sheet Probability by Bookmaker Odds'].append((probs_dict["away_0_goal_prob"] + math.exp(-home_goals_conceded_average)) / 2)
            player_dict[player]['Goals Conceded by Team on Average'].append(home_goals_conceded_average)
            home_goals_average = probs_dict["home_1_goal_prob"] + 2 * probs_dict["home_2_goals_prob"] + 3 * probs_dict["home_3_goals_prob"] + 4 * probs_dict["home_4_goals_prob"] + 5 * probs_dict["home_5_goals_prob"] + 6 * probs_dict["home_6_goals_prob"]
            player_dict[player]['Goals Scored by Team on Average'].append(home_goals_average)
        if player_dict[player]['Team'][0] == away_team:
            away_goals_conceded_average = probs_dict["home_1_goal_prob"] + 2 * probs_dict["home_2_goals_prob"] + 3 * probs_dict["home_3_goals_prob"] + 4 * probs_dict["home_4_goals_prob"] + 5 * probs_dict["home_5_goals_prob"] + 6 * probs_dict["home_6_goals_prob"]
            player_dict[player]['Clean Sheet Probability by Bookmaker Odds'].append((probs_dict["home_0_goal_prob"] + math.exp(-away_goals_conceded_average)) / 2)
            player_dict[player]['Goals Conceded by Team on Average'].append(away_goals_conceded_average)
            away_goals_average = probs_dict["away_1_goal_prob"] + 2 * probs_dict["away_2_goals_prob"] + 3 * probs_dict["away_3_goals_prob"] + 4 * probs_dict["away_4_goals_prob"] + 5 * probs_dict["away_5_goals_prob"] + 6 * probs_dict["away_6_goals_prob"]
            player_dict[player]['Goals Scored by Team on Average'].append(away_goals_average)

def add_probs_to_dict(
    odd_type: str,
    odds_dict: dict,
    player_dict: dict,
    home_team: str,
    away_team: str
) -> None:
    """
    Add calculated probabilities for a specific odds market to player_dict.

    Args:
        odd_type (str): Odds market type.
        odds_dict (dict): Mapping from player/outcome to odds.
        player_dict (dict): Player details dictionary.
        home_team (str): Home team name.
        away_team (str): Away team name.
    """
    try:
        for player_odd, odds_list in odds_dict.items():
            name = player_odd.strip()
            if len(odds_list) != 0:
                odd = sum(odds_list)/len(odds_list)
            else:
                odd = 0
            probability = 1/float(odd) if odd != 0 else 0
            matched_name = None  # Ensure matched_name is always defined
            for p in player_dict:
                # Prepare the player name for comparison
                player_tokens = prepare_name(p)
                webname_tokens = prepare_name(name)
                # Check if all tokens in one name exist in the other
                if all(token in webname_tokens for token in player_tokens) or all(token in player_tokens for token in webname_tokens):
                    matched_name = p
                    break
            # Add the odds to the player's dictionary
            if matched_name is not None:
                player_dict[matched_name][f"{odd_type} Probability"].append(probability)
            else:
                for p in player_dict:
                    # Prepare the player name for comparison
                    webname_tokens = prepare_name(name)
                    nickname1 = player_dict[p]['Nickname'][0]
                    nickname2 = player_dict[p]['Nickname2'][0]
                    nickname1_tokens = prepare_name(nickname1)
                    nickname2_tokens = prepare_name(nickname2)
                    if (" ".join(nickname2_tokens) in " ".join(webname_tokens) or " ".join(nickname1_tokens) in " ".join(webname_tokens)) and (player_dict[p]['Team'][0] in [home_team, away_team]):
                        matched_name = p
                        break
                    else:
                        p_name = PLAYER_NAMES_ODDSCHECKER.get(name, "Unknown")
                        if p_name != "Unknown":
                            matched_name = p_name
                            break
                    
                if matched_name:
                    player_dict[matched_name][f"{odd_type} Probability"].append(probability)
                else:
                    player_dict[name]['Nickname'] = ['Unknown']
                    player_dict[name]['Nickname2'] = ['Unknown']
                    player_dict[name]['Position'] = ['Unknown']
                    player_dict[name]['Team'] = ["Unknown"]
                    player_dict[name][f"{odd_type} Probability"].append(probability)
    except Exception as e:
        print("Couldn't get probability for ", odd_type, " ", e)

def calc_specific_probs(
    player_dict: dict
) -> None:
    """
    Calculate average assists, goals, and saves for each player using bookmaker and historical data.

    Args:
        player_dict (dict): Player details dictionary.
    """     
    for player, odds in player_dict.items():
        position = odds.get("Position", ["Unknown"])[0]
        anytime_prob = odds.get("Anytime Goalscorer Probability", [])
        two_or_more_prob = odds.get("To Score 2 Or More Goals Probability", [])
        hattrick_prob = odds.get("To Score A Hat-Trick Probability", [])
        assisting_over_05_prob = odds.get("Over 0.5 Player Assists Probability", [])
        assisting_over_15_prob = odds.get("Over 1.5 Player Assists Probability", [])
        assisting_over_25_prob = odds.get("Over 2.5 Player Assists Probability", [])

        if position in ['DEF', 'MID', 'FWD', 'Unknown']:
            for p25, p15, p05 in zip_longest(assisting_over_25_prob, assisting_over_15_prob, assisting_over_05_prob, fillvalue=0):
                three_ass_prob = p25
                one_ass_prob = p05 - p15 if p05 != 0 and p15 != 0 else p05
                two_ass_prob = p15 - p25 if p15 != 0 and p25 != 0 else p15
                expected_assists = three_ass_prob * 3 + two_ass_prob * 2 + one_ass_prob
                if expected_assists != 0:
                    ass_average = expected_assists
                    player_dict[player]["xA by Bookmaker Odds"].append(ass_average)
                
            for p3, p2, p1 in zip_longest(hattrick_prob, two_or_more_prob, anytime_prob, fillvalue=0):
                three_goals_prob = p3
                one_goal_prob = p1 - p2 if p1 != 0 and p2 != 0 else p1
                two_goals_prob = p2 - p3 if p2 != 0 and p3 != 0 else p2
                expected_goals = three_goals_prob * 3 + two_goals_prob * 2 + one_goal_prob
                if expected_goals != 0:
                    goal_average = expected_goals
                    player_dict[player]["xG by Bookmaker Odds"].append(goal_average)

        if position == 'GKP':
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

            for s95, s85, s75, s65, s55, s45, s35, s25, s15, s05 in zip_longest(over_95_saves, over_85_saves, over_75_saves, over_65_saves, over_55_saves, over_45_saves, over_35_saves, over_25_saves, over_15_saves, over_05_saves, fillvalue=0):
                zero_saves_prob = 1 - s05
                ten_saves_prob = s95 
                one_saves_prob = s05 - s15 if s05 != 0 and s15 != 0 else max((1 - s15 - zero_saves_prob), 0)
                two_saves_prob = s15 - s25 if s15 != 0 and s25 != 0 else max((1 - one_saves_prob - zero_saves_prob), 0)
                three_saves_prob = s25 - s35 if s25 != 0 and s35 != 0 else max((1 - two_saves_prob - one_saves_prob - zero_saves_prob), 0) 
                four_saves_prob = s35 - s45 if s35 != 0 and s45 != 0 else max((1 - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
                five_saves_prob = s45 - s55 if s45 != 0 and s55 != 0 else max((1 - four_saves_prob - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
                six_saves_prob = s55 - s65 if s55 != 0 and s65 != 0 else max((1 - five_saves_prob - four_saves_prob - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
                seven_saves_prob = s65 - s75 if s65 != 0 and s75 != 0 else max((1 - six_saves_prob - five_saves_prob - four_saves_prob - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
                eight_saves_prob = s75 - s85 if s75 != 0 and s85 != 0 else max((1 - seven_saves_prob - six_saves_prob - five_saves_prob - four_saves_prob - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
                nine_saves_prob = s85 - s95 if s85 != 0 and s95 != 0 else max((1 - eight_saves_prob - seven_saves_prob - six_saves_prob - five_saves_prob - four_saves_prob - three_saves_prob - two_saves_prob - one_saves_prob - zero_saves_prob), 0)
            
                saves_average = one_saves_prob + two_saves_prob * 2 + three_saves_prob * 3 + four_saves_prob * 4 + five_saves_prob * 5 + six_saves_prob * 6 + seven_saves_prob * 7 + eight_saves_prob * 8 + nine_saves_prob * 9 + ten_saves_prob * 10
                if saves_average != 0:
                    player_dict[player]["xSaves by Bookmaker Odds"].append(saves_average)

def calc_avg_bps(
    player_dict: dict,
    match_dict: dict
) -> None:
    """
    Calculate and add predicted bonus points per game for each player.

    Args:
        player_dict (dict): Player details dictionary.
        match_dict (dict): Match details dictionary.
    """
    for player, odds in player_dict.items():
        try:
            # Get probabilities
            team = odds.get("Team", ["Unknown"])[0]
            number_of_games = len(odds.get("Opponent", [])) if team != 'Unknown' else 1
            goals_average1 = odds.get("xG by Bookmaker Odds", [])
            ass_average1 = odds.get("xA by Bookmaker Odds", [])        
            cs_odds1 = odds.get("Clean Sheet Probability by Bookmaker Odds", [])
            position = odds.get("Position", ["Unknown"])[0]
            saves_average1 = odds.get("xSaves by Bookmaker Odds", [])

            goals_conceded_team_bookmaker = odds.get('Goals Conceded by Team on Average', [])

            minutes_per_game = odds.get("Minutes per Game", [0])[0]

            saves_per_game = odds.get('Saves per Game', [0])[0]
            saves_p90_24_25 = odds.get('24/25 Saves P90', [0])[0]
            combined_saves_per_game = (saves_per_game + 2 * saves_p90_24_25) / 3 if saves_p90_24_25 > 0 else saves_per_game

            cbi_per_game = odds.get("CBI per Game", [0])[0]
            recoveries_per_game = odds.get("Recoveries per Game", [0])[0]
            tackles_per_game = odds.get("Tackles per Game", [0])[0]

            # If there are more probability/average entries than number of games in the gameweek for a player, skip the player
            if len(goals_average1) > number_of_games or len(ass_average1) > number_of_games or len(saves_average1) > number_of_games:
                print(f"Calculating BPS for {player} skipped due to data entries being higher than number of games the player is playing")
                player_dict[player]['Estimated BPS'].append(0.0)
                continue

            for goals_a, ass_a, cs_odd, saves_a, g_conceded in zip_longest(goals_average1, ass_average1, cs_odds1, saves_average1, goals_conceded_team_bookmaker, fillvalue=0):
                bps = 0.0
                bps += ass_a * 9                # Assist
                bps += cbi_per_game / 2         # For every 2 clearances, blocks and interceptions (total)
                bps += recoveries_per_game / 3  # For every 3 recoveries
                bps += tackles_per_game * 2     # Successful tackle

                # Based on historical match data, roughly 25% of all goals scored in the Premier League end up being the winning goal. 
                bps += (0.25 * goals_a) * 9 # Scoring the goal that wins a match

                if minutes_per_game > 60:
                    bps += 6 # Playing over 60 minutes
                else:
                    bps += 3 # Playing 1 to 60 minutes

                if position == 'GKP':
                    if saves_a != 0:
                        # Save from a shot inside the box is 3 and Save from a shot outside the box is 2, using the average in calculations
                        bps += saves_a * 2.5                 # Save from a shot 
                    else:
                        bps += combined_saves_per_game * 2.5 # Save from a shot 
                
                if position == 'DEF' or position == 'GKP':
                    bps += cs_odd * 12    # Goalkeepers and defenders keeping a clean sheet
                    bps -= g_conceded * 4 # Goalkeepers and defenders conceding a goal
                    bps += goals_a * 12   # Goalkeepers and defenders scoring a goal

                if position == 'MID':
                    bps += goals_a * 18 # Midfielders scoring a goal

                if position == 'FWD':
                    bps += goals_a * 24 # Forwards scoring a goal

                player_dict[player]['Estimated BPS'].append(float(bps))

        except Exception as e:
            print(f"Could not calculate BPS for {player}: {e}")

def calculate_bonus_points(match_bps, player_bps, std_dev=10) -> float:
    """
    Calculate exact probabilities of receiving 0, 1, 2, or 3 bonus points based on expected BPS scores using a normal distribution model.
    Calculate expected bonus points according to these probabilities.

    Parameters:
    - match_bps: list of estimated BPS scores for 22 other players
    - player_bps: estimated BPS score of the player of interest
    - std_dev: standard deviation for uncertainty in BPS scores

    Returns:
    - Expected bonus points (float)
    """
    n = len(match_bps)
    probs = {0: 0.0, 1: 0.0, 2: 0.0, 3: 0.0}

    # Step 1: Probability player beats each other player
    beat_probs = [norm.cdf(player_bps - bps, scale=std_dev) for bps in match_bps]

    # Step 2: Distribution of number of players beaten
    beat_distribution = np.zeros(n + 1)
    beat_distribution[0] = 1.0
    for p in beat_probs:
        beat_distribution[1:] = beat_distribution[1:] * (1 - p) + beat_distribution[:-1] * p
        beat_distribution[0] *= (1 - p)

    # Step 3: Assign bonus points based on rank
    for beaten in range(n + 1):
        rank = n - beaten + 1  # rank from 1 (best) to n+1 (worst)
        if rank == 1:
            probs[3] += beat_distribution[beaten]
        elif rank == 2:
            probs[2] += beat_distribution[beaten]
        elif rank == 3:
            probs[1] += beat_distribution[beaten]
        else:
            probs[0] += beat_distribution[beaten]

    expected_bonus = sum(bp * prob for bp, prob in probs.items())
    return expected_bonus

def calc_team_xgs(
    home_team: str,
    away_team: str,
    team_stats_dict: dict,
    player_dict: dict
) -> None:
    """
    Estimate expected goals (xG) for both teams in a fixture and update each player's stats.

    Args:
        home_team (str): Name of the home team.
        away_team (str): Name of the away team.
        team_stats_dict (dict): Team statistics dictionary.
        player_dict (dict): Player details dictionary.
    """
    home_pos_range = get_pos_range(team_stats_dict[home_team]['League Position'])
    away_pos_range = get_pos_range(team_stats_dict[away_team]['League Position'])
    home_goals_p90 = team_stats_dict[home_team]['24/25 Goals per Home Game']
    away_goals_p90 = team_stats_dict[away_team]['24/25 Goals per Away Game']
    home_goals_conceded_p90 = team_stats_dict[home_team]['24/25 Goals Conceded per Home Game']
    away_goals_conceded_p90 = team_stats_dict[away_team]['24/25 Goals Conceded per Away Game']
    home_conceded_against_string = f"24/25 Goals Conceded per Home Game Against {away_pos_range}"
    away_conceded_against_string = f"24/25 Goals Conceded per Away Game Against {home_pos_range}"
    home_scored_against_string = f"24/25 Goals per Home Game Against {away_pos_range}"
    away_scored_against_string = f"24/25 Goals per Away Game Against {home_pos_range}"
    home_xg = ((home_goals_p90 + away_goals_conceded_p90 + 0.5 * team_stats_dict[home_team][home_scored_against_string] + 0.5 * team_stats_dict[away_team][away_conceded_against_string]) / 3)
    away_xg = ((away_goals_p90 + home_goals_conceded_p90 + 0.5 * team_stats_dict[away_team][away_scored_against_string] + 0.5 * team_stats_dict[home_team][home_conceded_against_string]) / 3)
    
    for player, stats in player_dict.items():
        if stats['Team'][0] == home_team:
            player_dict[player]['Team xG by Historical Data'].append(home_xg)
            player_dict[player]['Team xGC by Historical Data'].append(away_xg)
            player_dict[player]["Clean Sheet Probability by Historical Data"].append(math.exp(-away_xg))
        if stats['Team'][0] == away_team:
            player_dict[player]['Team xG by Historical Data'].append(away_xg)
            player_dict[player]['Team xGC by Historical Data'].append(home_xg)
            player_dict[player]["Clean Sheet Probability by Historical Data"].append(math.exp(-home_xg))

def calc_points(player_dict: dict, saves_button: bool) -> None:
    """
    Calculate predicted FPL points for each player using all available probabilities and averages.

    Args:
        player_dict (dict): Player details dictionary.

    Updates:
        player_dict: Adds 'xP by Bookmaker Odds' and 'xP by Historical Data' for each player.
    """
    for player, odds in player_dict.items():
        try:
            # Get probabilities
            team = odds.get("Team", ["Unknown"])[0]
            number_of_games = len(odds.get("Opponent", [])) if team != 'Unknown' else 1
            goals_average1 = odds.get("xG by Bookmaker Odds", [])
            ass_average1 = odds.get("xA by Bookmaker Odds", [])        
            cs_odds1 = odds.get("Clean Sheet Probability by Bookmaker Odds", [])
            position = odds.get("Position", ["Unknown"])[0]
            saves_average1 = odds.get("xSaves by Bookmaker Odds", [])

            goals_conceded_team_bookmaker = odds.get('Goals Conceded by Team on Average', [])

            chance_of_playing = odds.get("Chance of Playing", [1])[0] if team != 'Unknown' else 1

            def_contr_per_game = odds.get("Defensive Contributions per Game", [0])[0]
            def_contr_p90_24_25 = odds.get("24/25 Defensive Contributions P90", [0])[0]
            def_contr_avg = (2 * def_contr_p90_24_25 + def_contr_per_game) / 3 if def_contr_p90_24_25 > 0 else def_contr_per_game
            threshold = 10 if position == 'DEF' else 12
            dc_points = max(float(2 * (norm.cdf(2 * def_contr_avg, loc=def_contr_avg, scale=def_contr_avg/2) - norm.cdf(threshold, loc=def_contr_avg, scale=def_contr_avg/2)) / (norm.cdf(2 * def_contr_avg, loc=def_contr_avg, scale=def_contr_avg/2) - norm.cdf(0, loc=def_contr_avg, scale=def_contr_avg/2))), 0.0) if def_contr_avg > 0 else 0
            
            if saves_button and position == 'GKP':
                saves_per_game = odds.get('Saves per Game', [0])[0]
                saves_p90_24_25 = odds.get('24/25 Saves P90', [0])[0]
                saves_avg = (2 * saves_p90_24_25 + saves_per_game) / 3 if saves_p90_24_25 > 0 else saves_per_game
               
                saves_points = saves_avg / 3

                player_dict[player]['Average Save points'] = round(saves_points, 3)
            else:
                saves_points = 0

            bonus_points = odds.get('Estimated Bonus Points', [])
            
            # If there are more probability/average entries than number of games in the gameweek for a player, skip the player
            if len(goals_average1) > number_of_games or len(ass_average1) > number_of_games or len(saves_average1) > number_of_games:
                print(f"{player} skipped due to data entries being higher than number of games the player is playing")
                continue
            points = 0
            
            # Calculate points
            if position in ('MID'):
                points = chance_of_playing * (
                number_of_games * 2 + sum(goals_average1) * 5 +
                sum(ass_average1) * 3 + sum(cs_odds1) + 
                sum(bonus_points) + dc_points)

            if position in ('DEF'):
                points = chance_of_playing * (
                number_of_games * 2 + sum(goals_average1) * 6 +
                sum(ass_average1) * 3 + sum(cs_odds1) * 4
                - (sum(goals_conceded_team_bookmaker)/2) +
                sum(bonus_points) + dc_points)

            if position in ('GKP'):
                points = chance_of_playing * (
                number_of_games * 2 + sum(saves_average1)/3
                + sum(cs_odds1) * 4 - (sum(goals_conceded_team_bookmaker)/2) +
                sum(bonus_points) + dc_points)

                if saves_average1 == []:
                    points += number_of_games * saves_points

            if position in ('FWD'):
                points = chance_of_playing * (
                number_of_games * 2 + sum(goals_average1) * 4 +
                sum(ass_average1) * 3 + sum(bonus_points) + dc_points)

            if position in ('Unknown'):
                points = chance_of_playing * (
                number_of_games * 2 + sum(goals_average1) * 4 +
                sum(ass_average1) * 3)

            player_dict[player]['xP by Bookmaker Odds'] = round(points, 3)
            player_dict[player]['Average DC points'] = round(dc_points, 3)
        except Exception as e:
            print(f"Could not calculate points for {player}: {e}")

def initialize_predicted_points_df(saves_button: bool, bps_button: bool):

    fixtures = get_all_fixtures()
    next_gws = get_next_gws(fixtures, extra_gw = 'False')
    gws_for_filename = "-".join(str(gw) for gw in next_gws)

    cur_dir = os.getcwd()
    fixtures_dir = os.path.join(cur_dir, "data", "fixture_data")
    filename = os.path.join(fixtures_dir, f"gw{gws_for_filename}_all_odds_")

    json_files = glob.glob(f"{filename}*.json")

    if json_files:
        latest_file = max(json_files, key=os.path.getctime)
        try:
            with open(latest_file, 'r') as file:
                all_odds_dict = json.load(file)
        except IOError:
            st.write("Could not open all odds file.")
            all_odds_dict = {}
    else:
        st.write("JSON file not found")
        all_odds_dict = {}

    data, teams_data, players_data, team_id_to_name, player_id_to_name = fetch_fpl_data()
    element_types = position_mapping(data)
    player_dict = player_dict_constructor(players_data, element_types, team_id_to_name)

    team_stats_dict, player_stats_dict = construct_team_and_player_data(data, team_id_to_name, player_id_to_name, fixtures)

    for match, details in all_odds_dict.items():
        home_team_name = details.get('home_team', 'Unknown')
        away_team_name = details.get('away_team', 'Unknown')
        home_team = TEAM_NAMES_ODDSCHECKER.get(home_team_name, home_team_name)
        away_team = TEAM_NAMES_ODDSCHECKER.get(away_team_name, away_team_name)
        total_home_goals_probs = None
        total_away_goals_probs = None

        for player in player_dict:
            if player_dict[player].get('Team', ['Unknown'])[0] == home_team:
                player_dict[player]['Opponent'].append(away_team)
            if player_dict[player].get('Team', ['Unknown'])[0] == away_team:
                player_dict[player]['Opponent'].append(home_team)

        for odd_type, odds in details.items():
            if odd_type == 'Player Assists':
                if home_team is not None and away_team is not None:
                    get_player_over_probs(odd_type, odds, player_dict, home_team, away_team)
                else:
                    # Handle the case where home_team or away_team is None
                    print("Error adding Player Assists: home_team or away_team is None")

            if odd_type == 'Goalkeeper Saves':
                if home_team is not None and away_team is not None:
                    get_player_over_probs(odd_type, odds, player_dict, home_team, away_team)
                else:
                    # Handle the case where home_team or away_team is None
                    print("Error adding Goalkeeper Saves: home_team or away_team is None")

            if odd_type == 'To Score A Hat-Trick':
                if home_team is not None and away_team is not None:
                    add_probs_to_dict(odd_type, odds, player_dict, home_team, away_team)
                else:
                    # Handle the case where home_team or away_team is None
                    print("Error adding To Score A Hat-Trick: home_team or away_team is None")

            if odd_type == 'Anytime Goalscorer':
                if home_team is not None and away_team is not None:
                    add_probs_to_dict(odd_type, odds, player_dict, home_team, away_team)
                else:
                    # Handle the case where home_team or away_team is None
                    print("Error adding Anytime Goalscorer: home_team or away_team is None")

            if odd_type == 'To Score 2 Or More Goals':
                if home_team is not None and away_team is not None:
                    add_probs_to_dict(odd_type, odds, player_dict, home_team, away_team)
                else:
                    # Handle the case where home_team or away_team is None
                    print("Error adding To Score 2 Or More Goals: home_team or away_team is None") 

            if odd_type == 'Total Home Goals':      
                total_home_goals_probs = get_total_goals_over_probs(odds, "home") 

            if odd_type == 'Total Away Goals':
                total_away_goals_probs = get_total_goals_over_probs(odds, "away")

        total_combined_goals_dict = total_home_goals_probs | total_away_goals_probs if total_home_goals_probs and total_away_goals_probs else None
        if total_combined_goals_dict:
            if home_team is not None and away_team is not None:
                add_total_goals_probs_to_dict(total_combined_goals_dict, home_team, away_team, player_dict)
            else:
                # Handle the case where home_team or away_team is None
                print("Error adding Total Goals: home_team or away_team is None")
    
    calc_specific_probs(player_dict)
    if bps_button:
        with st.spinner("Calculating predicted bonus points..."):
            calc_avg_bps(player_dict, all_odds_dict)
            match_bps_dict = defaultdict(list)
            for match, details in all_odds_dict.items():
                match_bps_home = []
                match_bps_away = []
                home_team_name = details.get('home_team', 'Unknown')
                away_team_name = details.get('away_team', 'Unknown')
                home_team = TEAM_NAMES_ODDSCHECKER.get(home_team_name, home_team_name)
                away_team = TEAM_NAMES_ODDSCHECKER.get(away_team_name, away_team_name)

                for player in player_dict:
                    if player_dict[player].get('Team', ['Unknown'])[0] == home_team:
                        try:
                            opp_index = player_dict[player].get('Opponent', []).index(away_team)
                        except ValueError:
                            opp_index = -1

                        if opp_index != -1 and len(player_dict[player].get('Estimated BPS', [])) > opp_index:
                            match_bps_home.append(player_dict[player].get('Estimated BPS', [])[opp_index])

                    if player_dict[player].get('Team', ['Unknown'])[0] == away_team:
                        try:
                            opp_index = player_dict[player].get('Opponent', []).index(home_team)
                        except ValueError:
                            opp_index = -1

                        if opp_index != -1 and len(player_dict[player].get('Estimated BPS', [])) > opp_index:
                            match_bps_away.append(player_dict[player].get('Estimated BPS', [])[opp_index])

                match_bps_home = sorted(match_bps_home, reverse=True)[:11]
                match_bps_away = sorted(match_bps_away, reverse=True)[:11]
                match_bps = match_bps_home + match_bps_away
                match_bps_dict[home_team].append(sorted(match_bps, reverse=True)[:21])
                match_bps_dict[away_team].append(sorted(match_bps, reverse=True)[:21])

            for player in player_dict:
                team = player_dict[player].get('Team', ['Unknown'])[0]
                match_bps_list = match_bps_dict.get(team, [[0]])
                player_bps = player_dict[player].get('Estimated BPS', [0])
                for match_bps, p_bps in zip_longest(match_bps_list, player_bps):
                    #player_bonus_points = calculate_bonus_points(match_bps, p_bps)
                    player_bonus_points = max((p_bps / (sum(match_bps) + p_bps)) * 6, 0)
                    player_dict[player]['Estimated Bonus Points'].append(player_bonus_points)

    calc_points(player_dict, saves_button)

    # Create and save DataFrames with all player data and a summary of expected points.
    player_data_df = pd.DataFrame.from_dict(player_dict, orient='index')
    player_data_df.index.name = 'Player'
    # Convert all columns: if value is a list of length 1, replace with the value contained in the list.
    for col in player_data_df.columns:
        player_data_df[col] = player_data_df[col].apply(lambda x: x[0] if isinstance(x, list) and len(x) == 1 else x)

    return player_data_df, gws_for_filename

st.set_page_config(page_title="FPL Predicted Points", page_icon="📈")

st.markdown("# FPL Predicted Points")
st.write(
    """This is a FPL Predicted Points tool for viewing Fantasy Premier League predicted points according to the bookmaker odds scraped from Oddschecker.com"""
)

st.header("Select metrics to use in predicted points calculations")
saves_button = st.toggle("Use Saves per Game in predicted points calculation for goalkeepers if odds for Goalkeeper Saves are not available", value=True)
bps_button = st.toggle("Use Estimated Bonus Points in predicted points calculation if available", value=False)

if st.button("Calculate Predicted Points"):
    with st.spinner("Calculating predicted points..."):
        df, gws_for_filename = initialize_predicted_points_df(saves_button, bps_button)

    columns = df.columns.tolist()
    column_names = st.multiselect("Select Columns to Display", columns, default=columns)
    if column_names:
        df = df.loc[:, column_names]

    if "Position" in df.columns:
        positions = st.multiselect("Select Player Position(s)", sorted(df["Position"].dropna().unique()))
        if positions:
            df = df[df["Position"].isin(positions)]

    max_price = st.number_input(
        "Max price", value=20, placeholder="Type a price..."
    )

    df = df[df["Price"] <= max_price]

    # Display filtered data
    st.subheader("Predicted Points for Filtered Position(s)")
    st.data_editor(df)

    # Download button
    csv = df.to_csv(index=False).encode('utf-8')
    st.download_button(
        label="Download Predicted Points for filtered position(s) as CSV",
        data=csv,
        file_name=f"gw{gws_for_filename}_filtered_predicted_points.csv",
        mime="text/csv"
        )