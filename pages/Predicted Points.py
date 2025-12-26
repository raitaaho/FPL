# Import all required libraries for data fetching, processing, and web scraping.
import requests
import pandas as pd
from bs4 import BeautifulSoup

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
from scipy.stats import poisson
import glob
import streamlit as st
import numpy as np
import plotly.express as px

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

def get_next_gw(fixtures: list) -> int:
    """
    Find the next gameweek(s) that have not yet started.

    Args:
        fixtures (list): List of fixture dictionaries from the FPL API.

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
    
    return next_gameweek

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
    team_stats_dict: dict,
    player_stats_dict: dict,
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

        xg_25_26 = float(player["expected_goals"])  
        xa_25_26 = float(player["expected_assists"])
        saves_25_26 = int(player.get("saves", 0))

        games_played_for_current_team_24_25 = player_stats_dict[player_name]['24/25 Home Games Played for Current Team'] + player_stats_dict[player_name]['24/25 Away Games Played for Current Team']

        share_of_goals_scored = player_stats_dict[player_name]['Share of Goals by Current Team']
        share_of_assists = player_stats_dict[player_name]['Share of Assists by Current Team']
        share_of_team_xg = player_stats_dict[player_name]['Share of xG by Current Team']

        player_dict[player_name]['Nickname'] = [nickname1.strip()] if nickname1 != None else ["Unknown"] 
        player_dict[player_name]['Nickname2'] = [nickname2.strip()] if nickname2 != None else ["Unknown"]
        player_dict[player_name]['Position'] = [element_types[player["element_type"]]]
        player_dict[player_name]['Team'] = [team]
        player_dict[player_name]['Price'] = [player['now_cost'] / 10]
        player_dict[player_name]['Minutes'] = [player['minutes']]
        player_dict[player_name]['25/26 Games Played'] = [player_stats_dict[player_name]['25/26 Games Played']]
        player_dict[player_name]['Minutes per Game'] = [player['minutes'] / player_stats_dict[player_name]['25/26 Games Played']] if player_stats_dict[player_name]['25/26 Games Played'] > 0 else [0]
        player_dict[player_name]['Chance of Playing'] = [player['chance_of_playing_next_round'] / 100] if player['chance_of_playing_next_round'] else [1] if player['status'] in ('a', 'd') else [0]
        player_dict[player_name]['25/26 Defensive Contributions'] = [player["defensive_contribution"]] if player["defensive_contribution"] else [0]
        player_dict[player_name]['25/26 Defensive Contributions per Game'] = [player["defensive_contribution"] / player_stats_dict[player_name]['25/26 Games Played']] if player_stats_dict[player_name]['25/26 Games Played'] > 0 else [0]
        player_dict[player_name]['CBI per Game'] = [player["clearances_blocks_interceptions"] / player_stats_dict[player_name]['25/26 Games Played']] if player_stats_dict[player_name]['25/26 Games Played'] > 0 else [0]
        player_dict[player_name]['Recoveries per Game'] = [player["recoveries"] / player_stats_dict[player_name]['25/26 Games Played']] if player_stats_dict[player_name]['25/26 Games Played'] > 0 else [0]
        player_dict[player_name]['Tackles per Game'] = [player["tackles"] / player_stats_dict[player_name]['25/26 Games Played']] if player_stats_dict[player_name]['25/26 Games Played'] > 0 else [0]
        player_dict[player_name]['25/26 xG'] = [xg_25_26]
        player_dict[player_name]['25/26 xA'] = [xa_25_26]

        player_dict[player_name]['24/25 Defensive Contributions'] = [player_stats_dict[player_name]['24/25 Defensive Contributions']]
        player_dict[player_name]['24/25 Defensive Contributions per Game'] = [player_stats_dict[player_name]['24/25 Defensive Contributions'] / player_stats_dict[player_name]['24/25 Games Played']] if player_stats_dict[player_name]['24/25 Games Played'] > 0 else [0]

        if element_types[player["element_type"]] == 'GKP':
            player_dict[player_name]['24/25 Saves'] = [player_stats_dict[player_name]['24/25 Saves']]
            player_dict[player_name]['25/26 Saves'] = [saves_25_26]

            player_dict[player_name]['24/25 Saves per Home Game for Current Team'] = [player_stats_dict[player_name]['24/25 Saves per Home Game for Current Team']]
            player_dict[player_name]['24/25 Saves per Away Game for Current Team'] = [player_stats_dict[player_name]['24/25 Saves per Away Game for Current Team']]

            player_dict[player_name]['25/26 Saves per Home Game for Current Team'] = [player_stats_dict[player_name]['25/26 Saves per Home Game for Current Team']]
            player_dict[player_name]['25/26 Saves per Away Game for Current Team'] = [player_stats_dict[player_name]['25/26 Saves per Away Game for Current Team']]
        
        player_dict[player_name]['Estimated BPS'] = []
        player_dict[player_name]['Estimated Bonus Points'] = []

        player_dict[player_name]['24/25 Games Played'] = [player_stats_dict[player_name]['24/25 Games Played']]
        player_dict[player_name]['24/25 Games Played for Current Team'] = [games_played_for_current_team_24_25]
        player_dict[player_name]['24/25 xG'] = [player_stats_dict[player_name]['24/25 xG']]
        player_dict[player_name]['24/25 xA'] = [player_stats_dict[player_name]['24/25 xA']]
        player_dict[player_name]['Share of Goals by Current Team'] = [share_of_goals_scored]
        player_dict[player_name]['Share of Assists by Current Team'] = [share_of_assists]
        player_dict[player_name]['Share of xG by Current Team'] = [share_of_team_xg]
        
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
        return '17-20'
    
def get_pos_range2(position: int) -> str:
    if position <= 10:
        return '1-10'
    else:
        return '11-20'
    
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
        '24/25 Home Goals': 0,
        '24/25 Away Goals': 0,
        '24/25 Home Assists': 0,
        '24/25 Away Assists': 0,
        '24/25 Goals Conceded Home': 0,
        '24/25 Goals Conceded Away': 0,
        '24/25 Home Games Played': 0,
        '24/25 Away Games Played': 0,
        '24/25 Home Goalkeeper Saves': 0,
        '24/25 Away Goalkeeper Saves': 0,
        '24/25 Games Against 1-4': 0,
        '24/25 Goals Against 1-4': 0,
        '24/25 Goals Conceded Against 1-4': 0,
        '24/25 Games Against 5-8': 0,
        '24/25 Goals Against 5-8': 0,
        '24/25 Goals Conceded Against 5-8': 0,
        '24/25 Games Against 9-12': 0,
        '24/25 Goals Against 9-12': 0,
        '24/25 Goals Conceded Against 9-12': 0,
        '24/25 Games Against 13-16': 0,
        '24/25 Goals Against 13-16': 0,
        '24/25 Goals Conceded Against 13-16': 0,
        '24/25 Games Against 17-20': 0,
        '24/25 Goals Against 17-20': 0,
        '24/25 Goals Conceded Against 17-20': 0,
        '25/26 Home Goals': 0,
        '25/26 Away Goals': 0,
        '25/26 Home Assists': 0,
        '25/26 Away Assists': 0,
        '25/26 Goals Conceded Home': 0,
        '25/26 Goals Conceded Away': 0,
        '25/26 Home Games Played': 0,
        '25/26 Away Games Played': 0,
        '25/26 Home Goalkeeper Saves': 0,
        '25/26 Away Goalkeeper Saves': 0,
        '25/26 Games Against 1-4': 0,
        '25/26 Goals Against 1-4': 0,
        '25/26 Goals Conceded Against 1-4': 0,
        '25/26 Games Against 5-8': 0,
        '25/26 Goals Against 5-8': 0,
        '25/26 Goals Conceded Against 5-8': 0,
        '25/26 Games Against 9-12': 0,
        '25/26 Goals Against 9-12': 0,
        '25/26 Goals Conceded Against 9-12': 0,
        '25/26 Games Against 13-16': 0,
        '25/26 Goals Against 13-16': 0,
        '25/26 Goals Conceded Against 13-16': 0,
        '25/26 Games Against 17-20': 0,
        '25/26 Goals Against 17-20': 0,
        '25/26 Goals Conceded Against 17-20': 0
        }
    return team_template

def get_player_template(team_name: str, games: int) -> dict:
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
        'xg for Current Team': 0,
        '25/26 Games Played': games,
        '24/25 Home Games Played for Current Team': 0,
        '24/25 Away Games Played for Current Team': 0,
        '24/25 Home Goals for Current Team': 0,
        '24/25 Away Goals for Current Team': 0,
        '24/25 Home Assists for Current Team': 0,
        '24/25 Away Assists for Current Team': 0,
        '24/25 Goalkeeper Saves for Current Team': 0,
        '24/25 Games Against 1-4': 0,
        '24/25 Goals Against 1-4': 0,
        '24/25 Assists Against 1-4': 0,
        '24/25 Games Against 5-8': 0,
        '24/25 Goals Against 5-8': 0,
        '24/25 Assists Against 5-8': 0,
        '24/25 Games Against 9-12': 0,
        '24/25 Goals Against 9-12': 0,
        '24/25 Assists Against 9-12': 0,
        '24/25 Games Against 13-16': 0,
        '24/25 Goals Against 13-16': 0,
        '24/25 Assists Against 13-16': 0,
        '24/25 Games Against 17-20': 0,
        '24/25 Goals Against 17-20': 0,
        '24/25 Assists Against 17-20': 0,
        '25/26 Home Games Played for Current Team': 0,
        '25/26 Away Games Played for Current Team': 0,
        '25/26 Home Goals for Current Team': 0,
        '25/26 Away Goals for Current Team': 0,
        '25/26 Home Assists for Current Team': 0,
        '25/26 Away Assists for Current Team': 0,
        '25/26 Goalkeeper Saves for Current Team': 0,
        '25/26 Games Against 1-4': 0,
        '25/26 Goals Against 1-4': 0,
        '25/26 Assists Against 1-4': 0,
        '25/26 Games Against 5-8': 0,
        '25/26 Goals Against 5-8': 0,
        '25/26 Assists Against 5-8': 0,
        '25/26 Games Against 9-12': 0,
        '25/26 Goals Against 9-12': 0,
        '25/26 Assists Against 9-12': 0,
        '25/26 Games Against 13-16': 0,
        '25/26 Goals Against 13-16': 0,
        '25/26 Assists Against 13-16': 0,
        '25/26 Games Against 17-20': 0,
        '25/26 Goals Against 17-20': 0,
        '25/26 Assists Against 17-20': 0
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

    team_players = {}
    player_xgs = {}

    for team in teams:
        team_players[team['id']] = [player['id'] for player in elements if player['team'] == team['id']]

    fixtures = [fixture for fixture in fixtures if (fixture['finished_provisional'] == True)]

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
        for team_id, players in team_players.items():
            for player_id in players:
                if player_id != player['id']:
                    continue
                player_xgs[player['id']] = {}

        time.sleep(random.uniform(0, 0.2)) 
        response = requests.get(f"https://fantasy.premierleague.com/api/element-summary/{player['id']}/")
        if response.status_code != 200:
            print("Error fetching data for player ID:", player['id'])
            raise Exception(f"Failed to fetch teams: {response.status_code}")
            
        history_data = response.json()
        prev_fixtures_data = history_data.get('history', [])
        prev_seasons_data = history_data.get('history_past', [])
        
        for match in prev_fixtures_data:
            xg = float(match.get("expected_goals", 0))
            gw = match.get("round", "0")
            if gw != "0":
                player_xgs[player['id']][gw] = xg

        name = " ".join(prepare_name(player_id_to_name[player['id']]))
        team_name_key = player['team'] if player['team'] is not None else ""
        team_name_lookup = team_id_to_name.get(team_name_key, "Unknown")
        team_name = TEAM_NAMES_ODDSCHECKER.get(team_name_lookup, team_name_lookup)
        if team_name is None:
            team_name = ""

        games_25_26 = 0

        minutes_24_25 = 0
        games_24_25 = 0
        def_contributions_24_25 = 0
        goals_24_25 = 0
        assists_24_25 = 0
        xg_24_25 = 0
        xa_24_25 = 0
        saves_24_25 = 0
        for fixture in prev_fixtures_data:
            if fixture.get('minutes', 0) > 0:
                games_25_26 += 1

        for season in prev_seasons_data:
            if season['season_name'] != '2024/25':
                continue
            else:
                minutes_24_25 = int(season.get('minutes', 0))
                def_contributions_24_25 = int(season.get('defensive_contribution', 0))
                xg_24_25 = float(season.get('expected_goals', 0))
                xa_24_25 = float(season.get('expected_assists', 0))
                goals_24_25 = int(season.get('goals_scored', 0))
                assists_24_25 = int(season.get('assists', 0))
                saves_24_25 = int(season.get('saves', 0))
                break
        player_data[name] = defaultdict(float)
        player_data[name].update(get_player_template(team_name, games_25_26))
        player_data[name]['24/25 Defensive Contributions'] = def_contributions_24_25
        player_data[name]['24/25 xG'] = xg_24_25
        player_data[name]['24/25 xA'] = xa_24_25
        player_data[name]['24/25 Minutes Played'] = minutes_24_25
        player_data[name]['24/25 Goals'] = goals_24_25
        player_data[name]['24/25 Assists'] = assists_24_25
        player_data[name]['24/25 Saves'] = saves_24_25

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

        team_data[home_team_name]['24/25 Home Games Played'] += 1
        team_data[away_team_name]['24/25 Away Games Played'] += 1

        home_games_against_string = f"24/25 Games Against {away_pos_range}"
        home_goals_against_string = f"24/25 Goals Against {away_pos_range}"
        home_goals_conceded_against_string = f"24/25 Goals Conceded Against {away_pos_range}"
        home_assists_against_string = f"24/25 Assists Against {away_pos_range}"

        away_games_against_string = f"24/25 Games Against {home_pos_range}"
        away_goals_against_string = f"24/25 Goals Against {home_pos_range}"
        away_goals_conceded_against_string = f"24/25 Goals Conceded Against {home_pos_range}"
        away_assists_against_string = f"24/25 Assists Against {home_pos_range}"

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
                    old_name_tokens = prepare_name(player_id_to_name_24_25[pair['element']])
                    for player in player_data:
                        if all(token in old_name_tokens for token in prepare_name(player)) or all(token in prepare_name(player) for token in old_name_tokens):
                            if player_data[player]["Team"] == away_team_name:
                                player_data[player]['24/25 Away Games Played for Current Team'] += 1
                                player_data[player][away_games_against_string] += 1

                for pair in stat['h']:
                    old_name_tokens = prepare_name(player_id_to_name_24_25[pair['element']])
                    for player in player_data:
                        if all(token in old_name_tokens for token in prepare_name(player)) or all(token in prepare_name(player) for token in old_name_tokens):
                            if player_data[player]["Team"] == home_team_name:
                                player_data[player]['24/25 Home Games Played for Current Team'] += 1
                                player_data[player][home_games_against_string] += 1

            if stat['identifier'] == 'goals_scored':
                for pair in stat['a']:
                    old_name_tokens = prepare_name(player_id_to_name_24_25[pair['element']])
                    for player in player_data:
                        if all(token in old_name_tokens for token in prepare_name(player)) or all(token in prepare_name(player) for token in old_name_tokens):
                            if player_data[player]["Team"] == away_team_name:
                                player_data[player]['24/25 Away Goals for Current Team'] += int(pair['value'])
                                player_data[player][away_goals_against_string] += int(pair['value'])

                for pair in stat['h']:
                    old_name_tokens = prepare_name(player_id_to_name_24_25[pair['element']])
                    for player in player_data:
                        if all(token in old_name_tokens for token in prepare_name(player)) or all(token in prepare_name(player) for token in old_name_tokens):
                            if player_data[player]["Team"] == home_team_name:
                                player_data[player]['24/25 Home Goals for Current Team'] += int(pair['value'])
                                player_data[player][home_goals_against_string] += int(pair['value'])

            if stat['identifier'] == 'assists':
                for pair in stat['a']:
                    team_data[away_team_name]['24/25 Away Assists'] += int(pair['value'])
                    old_name_tokens = prepare_name(player_id_to_name_24_25[pair['element']])
                    for player in player_data:
                        if all(token in old_name_tokens for token in prepare_name(player)) or all(token in prepare_name(player) for token in old_name_tokens):
                            if player_data[player]["Team"] == away_team_name: 
                                player_data[player]['24/25 Away Assists for Current Team'] += int(pair['value'])
                                player_data[player][away_assists_against_string] += int(pair['value'])

                for pair in stat['h']:
                    team_data[home_team_name]['24/25 Home Assists'] += int(pair['value'])
                    old_name_tokens = prepare_name(player_id_to_name_24_25[pair['element']])
                    for player in player_data:
                        if all(token in old_name_tokens for token in prepare_name(player)) or all(token in prepare_name(player) for token in old_name_tokens):
                            if player_data[player]["Team"] == home_team_name: 
                                player_data[player]['24/25 Home Assists for Current Team'] += int(pair['value'])
                                player_data[player][home_assists_against_string] += int(pair['value'])

            if stat['identifier'] == 'saves':
                for pair in stat['a']:
                    team_data[away_team_name]['24/25 Away Goalkeeper Saves'] += int(pair['value'])
                    old_name_tokens = prepare_name(player_id_to_name_24_25[pair['element']])
                    for player in player_data:
                        if all(token in old_name_tokens for token in prepare_name(player)) or all(token in prepare_name(player) for token in old_name_tokens):
                            if player_data[player]["Team"] == away_team_name:
                                player_data[player]['24/25 Away Goalkeeper Saves for Current Team'] += int(pair['value'])

                for pair in stat['h']:
                    team_data[home_team_name]['24/25 Home Goalkeeper Saves'] += int(pair['value'])
                    old_name_tokens = prepare_name(player_id_to_name_24_25[pair['element']])
                    for player in player_data:
                        if all(token in old_name_tokens for token in prepare_name(player)) or all(token in prepare_name(player) for token in old_name_tokens):
                            if player_data[player]["Team"] == home_team_name:
                                player_data[player]['24/25 Home Goalkeeper Saves for Current Team'] += int(pair['value'])

    # Process each gameweek
    for fixture in fixtures:
        gw = fixture["event"]
        home_team_id = int(fixture['team_h'])
        away_team_id = int(fixture['team_a'])
        home_team_name = TEAM_NAMES_ODDSCHECKER.get(team_id_to_name[home_team_id], team_id_to_name[home_team_id])
        away_team_name = TEAM_NAMES_ODDSCHECKER.get(team_id_to_name[away_team_id], team_id_to_name[away_team_id])

        home_team_xg = 0
        away_team_xg = 0

        home_pos = team_data[home_team_name]['League Position']
        away_pos = team_data[away_team_name]['League Position']

        home_goals = fixture['team_h_score']
        away_goals = fixture['team_a_score']

        for player_id in team_players[home_team_id]:
            player_match = player_xgs.get(player_id, {})
            if player_match.get(gw, -1) != -1:
                player_match_xg = player_match.get(gw, 0)
                home_team_xg += player_match_xg

                player = " ".join(prepare_name(player_id_to_name[player_id]))
                player_data[player]['xG for Current Team'] += player_match_xg

        for player_id in team_players[away_team_id]:
            player_match = player_xgs.get(player_id, {})
            if player_match.get(gw, -1) != -1:
                player_match_xg = player_match.get(gw, 0)
                away_team_xg += player_match_xg

                player = " ".join(prepare_name(player_id_to_name[player_id]))
                player_data[player]['xG for Current Team'] += player_match_xg

        home_pos_range = get_pos_range(home_pos)
        away_pos_range = get_pos_range(away_pos)

        home_xg_against_string = f"25/26 xG Against {away_pos_range}"
        home_xgc_against_string = f"25/26 xGC Against {away_pos_range}"

        home_games_against_string = f"25/26 Games Against {away_pos_range}"
        home_goals_against_string = f"25/26 Goals Against {away_pos_range}"
        home_goals_conceded_against_string = f"25/26 Goals Conceded Against {away_pos_range}"
        home_assists_against_string = f"25/26 Assists Against {away_pos_range}"

        away_xg_against_string = f"25/26 xG Against {home_pos_range}"
        away_xgc_against_string = f"25/26 xGC Against {home_pos_range}"

        away_games_against_string = f"25/26 Games Against {home_pos_range}"
        away_goals_against_string = f"25/26 Goals Against {home_pos_range}"
        away_goals_conceded_against_string = f"25/26 Goals Conceded Against {home_pos_range}"
        away_assists_against_string = f"25/26 Assists Against {home_pos_range}"

        fixture["home_team_xg"] = home_team_xg
        fixture["away_team_xg"] = away_team_xg

        team_data[home_team_name]['25/26 Home xG'] += home_team_xg
        team_data[away_team_name]['25/26 Away xG'] += away_team_xg

        team_data[home_team_name]['25/26 Home xGC'] += away_team_xg
        team_data[away_team_name]['25/26 Away xGC'] += home_team_xg

        team_data[away_team_name][away_xg_against_string] += away_team_xg
        team_data[away_team_name][away_xgc_against_string] += home_team_xg

        team_data[away_team_name][away_games_against_string] += 1
        team_data[away_team_name][away_goals_against_string] += away_goals
        team_data[away_team_name][away_goals_conceded_against_string] += home_goals

        team_data[home_team_name][home_xg_against_string] += home_team_xg
        team_data[home_team_name][home_xgc_against_string] += away_team_xg

        team_data[home_team_name][home_games_against_string] += 1
        team_data[home_team_name][home_goals_against_string] += home_goals
        team_data[home_team_name][home_goals_conceded_against_string] += away_goals

        team_data[home_team_name]['25/26 Home Goals'] += home_goals
        team_data[away_team_name]['25/26 Away Goals'] += away_goals

        team_data[home_team_name]['25/26 Goals Conceded Home'] += away_goals
        team_data[away_team_name]['25/26 Goals Conceded Away'] += home_goals 

        # Increment games played for both teams
        team_data[home_team_name]['25/26 Home Games Played'] += 1
        team_data[away_team_name]['25/26 Away Games Played'] += 1

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

        home_players_appeared = []
        away_players_appeared = []

        for stat in fixture['stats']:
            if stat['identifier'] == 'bps':
                for pair in stat['a']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            away_players_appeared.append(player)
                for pair in stat['h']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            home_players_appeared.append(player)

            if stat['identifier'] == 'defensive_contribution':
                for pair in stat['a']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            away_players_appeared.append(player)
                for pair in stat['h']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            home_players_appeared.append(player)
                            
            if stat['identifier'] == 'goals_scored':
                for pair in stat['a']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['25/26 Away Goals for Current Team'] += int(pair['value'])
                            player_data[player][away_goals_against_string] += int(pair['value'])
                for pair in stat['h']:
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['25/26 Home Goals for Current Team'] += int(pair['value'])
                            player_data[player][home_goals_against_string] += int(pair['value'])
            if stat['identifier'] == 'assists':
                for pair in stat['a']:
                    team_data[away_team_name]['25/26 Away Assists'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])): 
                            player_data[player]['25/26 Away Assists for Current Team'] += int(pair['value'])
                            player_data[player][away_assists_against_string] += int(pair['value'])
                for pair in stat['h']:
                    team_data[home_team_name]['25/26 Home Assists'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['25/26 Home Assists for Current Team'] += int(pair['value'])
                            player_data[player][home_assists_against_string] += int(pair['value'])
            if stat['identifier'] == 'saves':
                for pair in stat['a']:
                    team_data[away_team_name]['25/26 Away Goalkeeper Saves'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == away_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['25/26 Away Goalkeeper Saves for Current Team'] += int(pair['value'])
                for pair in stat['h']:
                    team_data[home_team_name]['25/26 Home Goalkeeper Saves'] += int(pair['value'])
                    if player_data.get(" ".join(prepare_name(player_id_to_name[pair['element']]))) == None:
                        continue
                    for player in player_data:
                        if player_data[player]["Team"] == home_team_name and player == " ".join(prepare_name(player_id_to_name[pair['element']])):
                            player_data[player]['25/26 Home Goalkeeper Saves for Current Team'] += int(pair['value'])

        for player in list(set(away_players_appeared)):
            player_data[player]['25/26 Away Games Played for Current Team'] += 1
            player_data[player][away_games_against_string] += 1
        for player in list(set(home_players_appeared)):
            player_data[player]['25/26 Home Games Played for Current Team'] += 1
            player_data[player][home_games_against_string] += 1
    
    for team in team_data:
        team_data[team]['HFA'] = float(team_data[team]['Home ELO'] - team_data[team]['Away ELO']) if team_data[team]['Away ELO'] != 0 else 0

        team_data[team]['24/25 Goals per Home Game'] = float(team_data[team]['24/25 Home Goals'] / team_data[team]['24/25 Home Games Played']) if team_data[team]['24/25 Home Games Played'] > 0 else -1
        team_data[team]['24/25 Goals per Away Game'] = float(team_data[team]['24/25 Away Goals'] / team_data[team]['24/25 Away Games Played']) if team_data[team]['24/25 Away Games Played'] > 0 else -1

        team_data[team]['24/25 Goals Conceded per Home Game'] = float(team_data[team]['24/25 Goals Conceded Home']/team_data[team]['24/25 Home Games Played']) if team_data[team]['24/25 Home Games Played'] != 0 else -1
        team_data[team]['24/25 Goals Conceded per Away Game'] = float(team_data[team]['24/25 Goals Conceded Away']/team_data[team]['24/25 Away Games Played']) if team_data[team]['24/25 Away Games Played'] != 0 else -1

        team_data[team]['25/26 Goals per Home Game'] = float(team_data[team]['25/26 Home Goals'] / team_data[team]['25/26 Home Games Played']) if team_data[team]['25/26 Home Games Played'] > 0 else 0
        team_data[team]['25/26 Goals per Away Game'] = float(team_data[team]['25/26 Away Goals'] / team_data[team]['25/26 Away Games Played']) if team_data[team]['25/26 Away Games Played'] > 0 else 0

        team_data[team]['25/26 Goals Conceded per Home Game'] = float(team_data[team]['25/26 Goals Conceded Home']/team_data[team]['25/26 Home Games Played']) if team_data[team]['25/26 Home Games Played'] != 0 else 0
        team_data[team]['25/26 Goals Conceded per Away Game'] = float(team_data[team]['25/26 Goals Conceded Away']/team_data[team]['25/26 Away Games Played']) if team_data[team]['25/26 Away Games Played'] != 0 else 0

        team_data[team]['24/25 Goalkeeper Saves per Home Game'] = float(team_data[team]['24/25 Home Goalkeeper Saves'] / team_data[team]['24/25 Home Games Played']) if team_data[team]['24/25 Home Games Played'] > 0 else -1
        team_data[team]['24/25 Goalkeeper Saves per Away Game'] = float(team_data[team]['24/25 Away Goalkeeper Saves'] / team_data[team]['24/25 Away Games Played']) if team_data[team]['24/25 Away Games Played'] > 0 else -1

        team_data[team]['25/26 Goalkeeper Saves per Home Game'] = float(team_data[team]['25/26 Home Goalkeeper Saves']/team_data[team]['25/26 Home Games Played']) if team_data[team]['25/26 Home Games Played'] != 0 else 0
        team_data[team]['25/26 Goalkeeper Saves per Away Game'] = float(team_data[team]['25/26 Away Goalkeeper Saves']/team_data[team]['25/26 Away Games Played']) if team_data[team]['25/26 Away Games Played'] != 0 else 0
        
        team_data[team]['24/25 Goals per Game Against 1-4'] = float(team_data[team]['24/25 Goals Against 1-4'] / team_data[team]['24/25 Games Against 1-4']) if team_data[team]['24/25 Games Against 1-4'] != 0 else -1
        team_data[team]['24/25 Goals Conceded per Game Against 1-4'] = float(team_data[team]['24/25 Goals Conceded Against 1-4'] / team_data[team]['24/25 Games Against 1-4']) if team_data[team]['24/25 Games Against 1-4'] != 0 else -1
        team_data[team]['24/25 Goals per Game Against 5-8'] = float(team_data[team]['24/25 Goals Against 5-8']/team_data[team]['24/25 Games Against 5-8']) if team_data[team]['24/25 Games Against 5-8'] != 0 else -1
        team_data[team]['24/25 Goals Conceded per Game Against 5-8'] = float(team_data[team]['24/25 Goals Conceded Against 5-8']/team_data[team]['24/25 Games Against 5-8']) if team_data[team]['24/25 Games Against 5-8'] != 0 else -1
        team_data[team]['24/25 Goals per Game Against 9-12'] = float(team_data[team]['24/25 Goals Against 9-12']/team_data[team]['24/25 Games Against 9-12']) if team_data[team]['24/25 Games Against 9-12'] != 0 else -1
        team_data[team]['24/25 Goals Conceded per Game Against 9-12'] = float(team_data[team]['24/25 Goals Conceded Against 9-12']/team_data[team]['24/25 Games Against 9-12']) if team_data[team]['24/25 Games Against 9-12'] != 0 else -1
        team_data[team]['24/25 Goals per Game Against 13-16'] = float(team_data[team]['24/25 Goals Against 13-16']/team_data[team]['24/25 Games Against 13-16']) if team_data[team]['24/25 Games Against 13-16'] != 0 else -1
        team_data[team]['24/25 Goals Conceded per Game Against 13-16'] = float(team_data[team]['24/25 Goals Conceded Against 13-16']/team_data[team]['24/25 Games Against 13-16']) if team_data[team]['24/25 Games Against 13-16'] != 0 else -1
        team_data[team]['24/25 Goals per Game Against 17-20'] = float(team_data[team]['24/25 Goals Against 17-20']/team_data[team]['24/25 Games Against 17-20']) if team_data[team]['24/25 Games Against 17-20'] != 0 else -1
        team_data[team]['24/25 Goals Conceded per Game Against 17-20'] = float(team_data[team]['24/25 Goals Conceded Against 17-20']/team_data[team]['24/25 Games Against 17-20']) if team_data[team]['24/25 Games Against 17-20'] != 0 else -1

        team_data[team]['25/26 Goals per Game Against 1-4'] = float(team_data[team]['25/26 Goals Against 1-4']/team_data[team]['25/26 Games Against 1-4']) if team_data[team]['25/26 Games Against 1-4'] != 0 else 0
        team_data[team]['25/26 Goals Conceded per Game Against 1-4'] = float(team_data[team]['25/26 Goals Conceded Against 1-4']/team_data[team]['25/26 Games Against 1-4']) if team_data[team]['25/26 Games Against 1-4'] != 0 else 0
        team_data[team]['25/26 Goals per Game Against 5-8'] = float(team_data[team]['25/26 Goals Against 5-8']/team_data[team]['25/26 Games Against 5-8']) if team_data[team]['25/26 Games Against 5-8'] != 0 else 0
        team_data[team]['25/26 Goals Conceded per Game Against 5-8'] = float(team_data[team]['25/26 Goals Conceded Against 5-8']/team_data[team]['25/26 Games Against 5-8']) if team_data[team]['25/26 Games Against 5-8'] != 0 else 0
        team_data[team]['25/26 Goals per Game Against 9-12'] = float(team_data[team]['25/26 Goals Against 9-12']/team_data[team]['25/26 Games Against 9-12']) if team_data[team]['25/26 Games Against 9-12'] != 0 else 0
        team_data[team]['25/26 Goals Conceded per Game Against 9-12'] = float(team_data[team]['25/26 Goals Conceded Against 9-12']/team_data[team]['25/26 Games Against 9-12']) if team_data[team]['25/26 Games Against 9-12'] != 0 else 0
        team_data[team]['25/26 Goals per Game Against 13-16'] = float(team_data[team]['25/26 Goals Against 13-16']/team_data[team]['25/26 Games Against 13-16']) if team_data[team]['25/26 Games Against 13-16'] != 0 else 0
        team_data[team]['25/26 Goals Conceded per Game Against 13-16'] = float(team_data[team]['25/26 Goals Conceded Against 13-16']/team_data[team]['25/26 Games Against 13-16']) if team_data[team]['25/26 Games Against 13-16'] != 0 else 0
        team_data[team]['25/26 Goals per Game Against 17-20'] = float(team_data[team]['25/26 Goals Against 17-20']/team_data[team]['25/26 Games Against 17-20']) if team_data[team]['25/26 Games Against 17-20'] != 0 else 0
        team_data[team]['25/26 Goals Conceded per Game Against 17-20'] = float(team_data[team]['25/26 Goals Conceded Against 17-20']/team_data[team]['25/26 Games Against 17-20']) if team_data[team]['25/26 Games Against 17-20'] != 0 else 0

        team_data[team]['xG per Game Against 1-4'] = float(team_data[team]['25/26 xG Against 1-4']/team_data[team]['25/26 Games Against 1-4']) if team_data[team]['25/26 Games Against 1-4'] != 0 else 0
        team_data[team]['xGC per Game Against 1-4'] = float(team_data[team]['25/26 xGC Against 1-4']/team_data[team]['25/26 Games Against 1-4']) if team_data[team]['25/26 Games Against 1-4'] != 0 else 0
        team_data[team]['xG per Game Against 5-8'] = float(team_data[team]['25/26 xG Against 5-8']/team_data[team]['25/26 Games Against 5-8']) if team_data[team]['25/26 Games Against 5-8'] != 0 else 0
        team_data[team]['xGC per Game Against 5-8'] = float(team_data[team]['25/26 xGC Against 5-8']/team_data[team]['25/26 Games Against 5-8']) if team_data[team]['25/26 Games Against 5-8'] != 0 else 0
        team_data[team]['xG per Game Against 9-12'] = float(team_data[team]['25/26 xG Against 9-12']/team_data[team]['25/26 Games Against 9-12']) if team_data[team]['25/26 Games Against 9-12'] != 0 else 0
        team_data[team]['xGC per Game Against 9-12'] = float(team_data[team]['25/26 xGC Against 9-12']/team_data[team]['25/26 Games Against 9-12']) if team_data[team]['25/26 Games Against 9-12'] != 0 else 0
        team_data[team]['xG per Game Against 13-16'] = float(team_data[team]['25/26 xG Against 13-16']/team_data[team]['25/26 Games Against 13-16']) if team_data[team]['25/26 Games Against 13-16'] != 0 else 0
        team_data[team]['xGC per Game Against 13-16'] = float(team_data[team]['25/26 xGC Against 13-16']/team_data[team]['25/26 Games Against 13-16']) if team_data[team]['25/26 Games Against 13-16'] != 0 else 0
        team_data[team]['xG per Game Against 17-20'] = float(team_data[team]['25/26 xG Against 17-20']/team_data[team]['25/26 Games Against 17-20']) if team_data[team]['25/26 Games Against 17-20'] != 0 else 0
        team_data[team]['xGC per Game Against 17-20'] = float(team_data[team]['25/26 xGC Against 17-20']/team_data[team]['25/26 Games Against 17-20']) if team_data[team]['25/26 Games Against 17-20'] != 0 else 0

        team_data[team]['xG per Home Game'] = float(team_data[team]['25/26 Home xG'] / team_data[team]['25/26 Home Games Played']) if team_data[team]['25/26 Home Games Played'] != 0 else 0
        team_data[team]['xG per Away Game'] = float(team_data[team]['25/26 Away xG'] / team_data[team]['25/26 Away Games Played']) if team_data[team]['25/26 Away Games Played'] != 0 else 0
        team_data[team]['xGC per Home Game'] = float(team_data[team]['25/26 Home xGC'] / team_data[team]['25/26 Home Games Played']) if team_data[team]['25/26 Home Games Played'] != 0 else 0
        team_data[team]['xGC per Away Game'] = float(team_data[team]['25/26 Away xGC'] / team_data[team]['25/26 Away Games Played']) if team_data[team]['25/26 Away Games Played'] != 0 else 0

    for player in player_data:
        team = player_data[player]['Team']

        team_games_25_26 = team_data[team]['25/26 Home Games Played'] + team_data[team]['25/26 Away Games Played']
        team_goals_24_25 = team_data[team]['24/25 Home Goals'] + team_data[team]['24/25 Away Goals']
        team_goals_25_26 = team_data[team]['25/26 Home Goals'] + team_data[team]['25/26 Away Goals']

        team_assists_24_25 = team_data[team]['24/25 Home Assists'] + team_data[team]['24/25 Away Assists']
        team_assists_25_26 = team_data[team]['25/26 Home Assists'] + team_data[team]['25/26 Away Assists']

        team_xg = team_data[team]['25/26 Home xG'] + team_data[team]['25/26 Away xG']

        games_for_team_24_25 = player_data[player]['24/25 Home Games Played for Current Team'] + player_data[player]['24/25 Away Games Played for Current Team'] 
        games_for_team_25_26 = player_data[player]['25/26 Home Games Played for Current Team'] + player_data[player]['25/26 Away Games Played for Current Team']

        full_90s_played_24_25 = math.floor(player_data[player].get('24/25 Minutes Played', 0) / 90)
        player_data[player]['24/25 Games Played'] = max(full_90s_played_24_25, games_for_team_24_25)

        player_data[player]['24/25 Defensive Contributions per Game'] = player_data[player]['24/25 Defensive Contributions'] / max(full_90s_played_24_25, games_for_team_24_25) if max(full_90s_played_24_25, games_for_team_24_25) > 0 else 0

        goals_for_team_24_25 = player_data[player]['24/25 Home Goals for Current Team'] + player_data[player]['24/25 Away Goals for Current Team']
        goals_for_team_25_26 = player_data[player]['25/26 Home Goals for Current Team'] + player_data[player]['25/26 Away Goals for Current Team']

        assists_for_team_24_25 = player_data[player]['24/25 Home Assists for Current Team'] + player_data[player]['24/25 Away Assists for Current Team']
        assists_for_team_25_26 = player_data[player]['25/26 Home Assists for Current Team'] + player_data[player]['25/26 Away Assists for Current Team']

        if games_for_team_24_25 == 0:
            share_of_team_goals = (goals_for_team_25_26 * (1 + ((team_games_25_26 - games_for_team_25_26) / team_games_25_26))) / team_goals_25_26 if team_games_25_26 != 0 and team_goals_25_26 != 0 else 0
            share_of_team_assists = (assists_for_team_25_26 * (1 + ((team_games_25_26 - games_for_team_25_26) / team_games_25_26))) / team_assists_25_26 if team_games_25_26 != 0 and team_assists_25_26 != 0 else 0
        else:
            share_of_team_goals = ((goals_for_team_24_25 + goals_for_team_25_26) * (1 + (((38 + team_games_25_26) - (games_for_team_24_25 + games_for_team_25_26)) / (38 + team_games_25_26)))) / (team_goals_24_25 + team_goals_25_26) if team_games_25_26 != 0 and team_goals_24_25 + team_goals_25_26 != 0 else 0
            share_of_team_assists = ((assists_for_team_24_25 + assists_for_team_25_26) * (1 + (((38 + team_games_25_26) - (games_for_team_24_25 + games_for_team_25_26)) / (38 + team_games_25_26)))) / (team_assists_24_25 + team_assists_25_26) if team_games_25_26 != 0 and team_assists_24_25 + team_assists_25_26 != 0 else 0
            
        player_data[player]['Share of Goals by Current Team'] = float(share_of_team_goals)
        player_data[player]['Share of Assists by Current Team'] = float(share_of_team_assists)

        share_of_team_xg = (player_data[player]['xG for Current Team'] * (1 + ((team_games_25_26 - games_for_team_25_26) / team_games_25_26))) / team_xg if team_games_25_26 != 0 and team_xg != 0 else 0
        player_data[player]['Share of xG by Current Team'] = float(share_of_team_xg)

        player_data[player]['Goals per Home Game'] = float(player_data[player]['Home Goals for Current Team']/player_data[player]['Home Games Played for Current Team']) if player_data[player]['Home Games Played for Current Team'] != 0 else 0
        player_data[player]['Assists per Home Game'] = float(player_data[player]['Home Assists for Current Team']/player_data[player]['Home Games Played for Current Team']) if player_data[player]['Home Games Played for Current Team'] != 0 else 0
        player_data[player]['Goals per Away Game'] = float(player_data[player]['Away Goals for Current Team']/player_data[player]['Away Games Played for Current Team']) if player_data[player]['Away Games Played for Current Team'] != 0 else 0
        player_data[player]['Assists per Away Game'] = float(player_data[player]['Away Assists for Current Team']/player_data[player]['Away Games Played for Current Team']) if player_data[player]['Away Games Played for Current Team'] != 0 else 0
        
        player_data[player]['24/25 Saves per Home Game for Current Team'] = float(player_data[player]['24/25 Home Goalkeeper Saves for Current Team'] / player_data[player]['24/25 Home Games Played for Current Team']) if player_data[player]['24/25 Home Games Played for Current Team'] > 0 else -1
        player_data[player]['24/25 Saves per Away Game for Current Team'] = float(player_data[player]['24/25 Away Goalkeeper Saves for Current Team'] / player_data[player]['24/25 Away Games Played for Current Team']) if player_data[player]['24/25 Away Games Played for Current Team'] > 0 else -1

        player_data[player]['25/26 Saves per Home Game for Current Team'] = float(player_data[player]['25/26 Home Goalkeeper Saves for Current Team'] / player_data[player]['25/26 Home Games Played for Current Team']) if player_data[player]['25/26 Home Games Played for Current Team'] > 0 else 0
        player_data[player]['25/26 Saves per Away Game for Current Team'] = float(player_data[player]['25/26 Away Goalkeeper Saves for Current Team'] / player_data[player]['25/26 Away Games Played for Current Team']) if player_data[player]['25/26 Away Games Played for Current Team'] > 0 else 0

        player_data[player]['Goals per Game Against 1-4'] = float((player_data[player]['24/25 Goals Against 1-4'] + player_data[player]['25/26 Goals Against 1-4'])/(player_data[player]['24/25 Games Against 1-4'] + player_data[player]['25/26 Games Against 1-4'])) if player_data[player]['24/25 Games Against 1-4'] + player_data[player]['25/26 Games Against 1-4'] != 0 else 0 
        player_data[player]['Goals Conceded per Game Against 1-4'] = float((player_data[player]['24/25 Goals Conceded Against 1-4'] + player_data[player]['25/26 Goals Conceded Against 1-4'])/(player_data[player]['24/25 Games Against 1-4'] + player_data[player]['25/26 Games Against 1-4'])) if player_data[player]['24/25 Games Against 1-4'] + player_data[player]['25/26 Games Against 1-4'] != 0 else 0 
        player_data[player]['Goals per Game Against 5-8'] = float((player_data[player]['24/25 Goals Against 5-8'] + player_data[player]['25/26 Goals Against 5-8'])/(player_data[player]['24/25 Games Against 5-8'] + player_data[player]['25/26 Games Against 5-8'])) if player_data[player]['24/25 Games Against 5-8'] + player_data[player]['25/26 Games Against 5-8'] != 0 else 0 
        player_data[player]['Goals Conceded per Game Against 5-8'] = float((player_data[player]['24/25 Goals Conceded Against 5-8'] + player_data[player]['25/26 Goals Conceded Against 5-8'])/(player_data[player]['24/25 Games Against 5-8'] + player_data[player]['25/26 Games Against 5-8'])) if player_data[player]['24/25 Games Against 5-8'] + player_data[player]['25/26 Games Against 5-8'] != 0 else 0 
        player_data[player]['Goals per Game Against 9-12'] = float((player_data[player]['24/25 Goals Against 9-12'] + player_data[player]['25/26 Goals Against 9-12'])/(player_data[player]['24/25 Games Against 9-12'] + player_data[player]['25/26 Games Against 9-12'])) if player_data[player]['24/25 Games Against 9-12'] + player_data[player]['25/26 Games Against 9-12'] != 0 else 0
        player_data[player]['Goals Conceded per Game Against 9-12'] = float((player_data[player]['24/25 Goals Conceded Against 9-12'] + player_data[player]['25/26 Goals Conceded Against 9-12'])/(player_data[player]['24/25 Games Against 9-12'] + player_data[player]['25/26 Games Against 9-12'])) if player_data[player]['24/25 Games Against 9-12'] + player_data[player]['25/26 Games Against 9-12'] != 0 else 0
        player_data[player]['Goals per Game Against 13-16'] = float((player_data[player]['24/25 Goals Against 13-16'] + player_data[player]['25/26 Goals Against 13-16'])/(player_data[player]['24/25 Games Against 13-16'] + player_data[player]['25/26 Games Against 13-16'])) if player_data[player]['24/25 Games Against 13-16'] + player_data[player]['25/26 Games Against 13-16'] != 0 else 0
        player_data[player]['Goals Conceded per Game Against 13-16'] = float((player_data[player]['24/25 Goals Conceded Against 13-16'] + player_data[player]['25/26 Goals Conceded Against 13-16'])/(player_data[player]['24/25 Games Against 13-16'] + player_data[player]['25/26 Games Against 13-16'])) if player_data[player]['24/25 Games Against 13-16'] + player_data[player]['25/26 Games Against 13-16'] != 0 else 0
        player_data[player]['Goals per Game Against 17-20'] = float((player_data[player]['24/25 Goals Against 17-20'] + player_data[player]['25/26 Goals Against 17-20'])/(player_data[player]['24/25 Games Against 17-20'] + player_data[player]['25/26 Games Against 17-20'])) if player_data[player]['24/25 Games Against 17-20'] + player_data[player]['25/26 Games Against 17-20'] != 0 else 0
        player_data[player]['Goals Conceded per Game Against 17-20'] = float((player_data[player]['24/25 Goals Conceded Against 17-20'] + player_data[player]['25/26 Goals Conceded Against 17-20'])/(player_data[player]['24/25 Games Against 17-20'] + player_data[player]['25/26 Games Against 17-20'])) if player_data[player]['24/25 Games Against 17-20'] + player_data[player]['25/26 Games Against 17-20'] != 0 else 0

    return team_data, player_data

def get_player_over_probs(
    odd_type: str,
    odds_dict: dict,
    player_dict: dict,
    home_team: str,
    away_team: str,
    bookmaker_margin: float
) -> None:
    """
    Calculate player 'Over X' probabilities from odds and update player_dict.

    Args:
        odd_type (str): Odds market type.
        odds_dict (dict): Mapping from player/outcome to odds.
        player_dict (dict): Player details dictionary.
        home_team (str): Home team name.
        away_team (str): Away team name.
        bookmaker_margin (float): Bookmaker margin to adjust odds.
    """
    if odd_type == "Player Assists":
        odds_for = ['Over 0.5', 'Over 1.5', 'Over 2.5']
    else:
        odds_for = ['Over 0.5', 'Over 1.5', 'Over 2.5', 'Over 3.5', 'Over 4.5', 'Over 5.5', 'Over 6.5', 'Over 7.5', 'Over 8.5', 'Over 9.5']
    try:
        for player_odd, odds_list in odds_dict.items():
            index = player_odd.find("Over")
            odd_for = player_odd[index:].strip()
            name = player_odd[:index].strip()
            if odd_for in odds_for:
                if len(odds_list) > 0:
                    odd = (sum(odds_list)/len(odds_list)) / (1 - bookmaker_margin)
                else:
                    odd = 0
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
                        player_dict[name]['Nickname'] = [name]
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
        float: Bookmaker margin.
    """
    bookmaker_margin = 0.05
    try:
        team_under_05_odd, team_over_05_odd, team_over_15_odd, team_over_25_odd, team_over_35_odd, team_over_45_odd, team_over_55_odd = 0,0,0,0,0,0,0
        for team_odd, odds_list in odds_dict.items():
            if len(odds_list) != 0:
                ave_odd = sum(odds_list)/len(odds_list)
            else:
                ave_odd = 0
            if team_odd == "Under 0.5":
                team_under_05_odd = ave_odd
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
            team_under_05_prob = 1/float(team_under_05_odd) if team_under_05_odd != 0 else 1 - team_over_05_prob
            team_over_15_prob = 1/float(team_over_15_odd) if team_over_15_odd != 0 else 0
            team_over_25_prob = 1/float(team_over_25_odd) if team_over_25_odd != 0 else 0
            team_over_35_prob = 1/float(team_over_35_odd) if team_over_35_odd != 0 else 0
            team_over_45_prob = 1/float(team_over_45_odd) if team_over_45_odd != 0 else 0
            team_over_55_prob = 1/float(team_over_55_odd) if team_over_55_odd != 0 else 0

            try:
                team_0_goal_prob = team_under_05_prob
                team_6_goal_prob = team_over_55_prob
                team_1_goal_prob = max(team_over_05_prob - team_over_15_prob, 0) if team_over_05_prob != 0 and team_over_15_prob != 0 else team_over_05_prob
                team_2_goal_prob = max(team_over_15_prob - team_over_25_prob, 0) if team_over_15_prob != 0 and team_over_25_prob != 0 else team_over_15_prob
                team_3_goal_prob = max(team_over_25_prob - team_over_35_prob, 0) if team_over_25_prob != 0 and team_over_35_prob != 0 else team_over_25_prob
                team_4_goal_prob = max(team_over_35_prob - team_over_45_prob, 0) if team_over_35_prob != 0 and team_over_45_prob != 0 else team_over_35_prob
                team_5_goal_prob = max(team_over_45_prob - team_over_55_prob, 0) if team_over_45_prob != 0 and team_over_55_prob != 0 else team_over_45_prob
                team_6_goal_prob = team_over_55_prob

                bookmaker_margin = (team_0_goal_prob + team_1_goal_prob + team_2_goal_prob + team_3_goal_prob + team_4_goal_prob + team_5_goal_prob + team_6_goal_prob) - 1
                
            except Exception as e:
                print(f"Couldnt calculate probabilities for Total {team.capitalize()} Goals", e)
                return None, bookmaker_margin
        except Exception as e:
            print(f"Couldnt calculate probabilities for Total {team.capitalize()} Over Goals", e)
            return None, bookmaker_margin 
        return {team + '_0_goal_prob': team_0_goal_prob/(1 + bookmaker_margin), team + '_1_goal_prob': team_1_goal_prob/(1 + bookmaker_margin), team + '_2_goals_prob': team_2_goal_prob/(1 + bookmaker_margin), team + '_3_goals_prob': team_3_goal_prob/(1 + bookmaker_margin), team + '_4_goals_prob': team_4_goal_prob/(1 + bookmaker_margin), team + '_5_goals_prob': team_5_goal_prob/(1 + bookmaker_margin), team + '_6_goals_prob': team_6_goal_prob/(1 + bookmaker_margin)}, bookmaker_margin     
    except Exception as e:
        print(f"Couldnt find probabilities from odds_dict for Total {team.capitalize()} Over Goals", e)
        return None, bookmaker_margin
    
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
    away_team: str,
    bookmaker_margin: float
) -> None:
    """
    Add calculated probabilities for a specific odds market to player_dict.

    Args:
        odd_type (str): Odds market type.
        odds_dict (dict): Mapping from player/outcome to odds.
        player_dict (dict): Player details dictionary.
        home_team (str): Home team name.
        away_team (str): Away team name.
        bookmaker_margin (float): Bookmaker margin to adjust odds.
    """
    try:
        for player_odd, odds_list in odds_dict.items():
            name = player_odd.strip()
            if len(odds_list) != 0:
                odd = sum(odds_list)/len(odds_list)
            else:
                odd = 0
            probability = (1/float(odd)) / (1 + bookmaker_margin) if odd != 0 else 0
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
                    player_dict[name]['Nickname'] = [name]
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
        opponents = odds.get("Opponent", [])
        anytime_prob = odds.get("Anytime Goalscorer Probability", [])
        two_or_more_prob = odds.get("To Score 2 Or More Goals Probability", [])
        hattrick_prob = odds.get("To Score A Hat-Trick Probability", [])
        assisting_over_05_prob = odds.get("Over 0.5 Player Assists Probability", [])
        assisting_over_15_prob = odds.get("Over 1.5 Player Assists Probability", [])
        assisting_over_25_prob = odds.get("Over 2.5 Player Assists Probability", [])

        ass_share = odds.get("Share of Assists by Current Team", [0])[0]
        goal_share = odds.get("Share of Goals by Current Team", [0])[0]
        xg_share = odds.get("Share of xG by Current Team", [0])[0]
        total_goals_historical = odds.get('Team xG by Historical Data', [])

        xa_per_game_24_25 = odds.get("24/25 xA", [0])[0] / odds.get("24/25 Games Played", [0])[0] if odds.get("24/25 Games Played", [0])[0] > 0 else 0
        xa_per_game_25_26 =  odds.get("25/26 xA", [0])[0] / odds.get("25/26 Games Played", [0])[0] if odds.get("25/26 Games Played", [0])[0] > 0 else 0
        xa_per_game = (2 * xa_per_game_25_26 + xa_per_game_24_25) / 3 if odds.get("24/25 Games Played", [0])[0] > 0 and odds.get("25/26 Games Played", [0])[0] > 0 else xa_per_game_25_26 if odds.get("25/26 Games Played", [0])[0] > 0 else xa_per_game_24_25
        xg_per_game_24_25 = odds.get("24/25 xG", [0])[0] / odds.get("24/25 Games Played", [0])[0] if odds.get("24/25 Games Played", [0])[0] > 0 else 0
        xg_per_game_25_26 =  odds.get("25/26 xG", [0])[0] / odds.get("25/26 Games Played", [0])[0] if odds.get("25/26 Games Played", [0])[0] > 0 else 0
        xg_per_game = (2 * xg_per_game_25_26 + xg_per_game_24_25) / 3 if odds.get("24/25 Games Played", [0])[0] > 0 and odds.get("25/26 Games Played", [0])[0] > 0 else xg_per_game_25_26 if odds.get("25/26 Games Played", [0])[0] > 0 else xg_per_game_24_25

        if position in ['DEF', 'MID', 'FWD', 'Unknown']:
            for p25, p15, p05 in zip_longest(assisting_over_25_prob, assisting_over_15_prob, assisting_over_05_prob, fillvalue=0):
                three_ass_prob = p25
                one_ass_prob = p05 - p15 if p05 != 0 and p15 != 0 else p05
                two_ass_prob = p15 - p25 if p15 != 0 and p25 != 0 else p15
                expected_assists = three_ass_prob * 3 + two_ass_prob * 2 + one_ass_prob
                player_dict[player]["xA by Bookmaker Odds"].append(expected_assists)
                
            for p3, p2, p1 in zip_longest(hattrick_prob, two_or_more_prob, anytime_prob, fillvalue=0):
                three_goals_prob = p3
                one_goal_prob = p1 - p2 if p1 != 0 and p2 != 0 else p1
                two_goals_prob = p2 - p3 if p2 != 0 and p3 != 0 else p2
                expected_goals = three_goals_prob * 3 + two_goals_prob * 2 + one_goal_prob
                player_dict[player]["xG by Bookmaker Odds"].append(expected_goals)

            for t_gsa, opp in zip_longest(total_goals_historical, opponents, fillvalue=0):
                # On average, the assists per goal scored ratio is rougly 0.70 in the Premier League 
                ave_ass = ((ass_share * 0.70 * t_gsa) + xa_per_game) / 2 if t_gsa != 0 else xa_per_game
                ave_g = ((((goal_share + xg_share) / 2) * t_gsa) + xg_per_game) / 2 if t_gsa != 0 and goal_share != 0 else (xg_share * t_gsa + xg_per_game) / 2 if t_gsa != 0 else xg_per_game
                player_dict[player]["xA by Historical Data"].append(ave_ass)
                player_dict[player]["xG by Historical Data"].append(ave_g)

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
                ten_saves_prob = s95 
                one_saves_prob = s05 - s15 if s05 != 0 and s15 != 0 else s05
                two_saves_prob = s15 - s25 if s15 != 0 and s25 != 0 else s15
                three_saves_prob = s25 - s35 if s25 != 0 and s35 != 0 else s25 
                four_saves_prob = s35 - s45 if s35 != 0 and s45 != 0 else s35
                five_saves_prob = s45 - s55 if s45 != 0 and s55 != 0 else s45
                six_saves_prob = s55 - s65 if s55 != 0 and s65 != 0 else s55
                seven_saves_prob = s65 - s75 if s65 != 0 and s75 != 0 else s65
                eight_saves_prob = s75 - s85 if s75 != 0 and s85 != 0 else s75
                nine_saves_prob = s85 - s95 if s85 != 0 and s95 != 0 else s85
            
                saves_average = one_saves_prob + two_saves_prob * 2 + three_saves_prob * 3 + four_saves_prob * 4 + five_saves_prob * 5 + six_saves_prob * 6 + seven_saves_prob * 7 + eight_saves_prob * 8 + nine_saves_prob * 9 + ten_saves_prob * 10
                player_dict[player]["xSaves by Bookmaker Odds"].append(saves_average)

def calc_avg_bps(
    player_dict: dict,
    saves_button: bool
) -> None:
    """
    Calculate and add predicted bonus points per game for each player.

    Args:
        player_dict (dict): Player details dictionary.
    """     
    for player, odds in player_dict.items():
        try:
            # Get probabilities
            team = odds.get("Team", ["Unknown"])[0]
    
            opponents = odds.get("Opponent", [])
            number_of_games = len(odds.get("Opponent", [])) if team != 'Unknown' else 1
            goals_average_bookmaker = odds.get("xG by Bookmaker Odds", [])
            goals_average_historical = odds.get("xG by Historical Data", [])
            ass_average_bookmaker = odds.get("xA by Bookmaker Odds", [])
            ass_average_historical = odds.get("xA by Historical Data", [])       
            cs_odds_bookmaker = odds.get("Clean Sheet Probability by Bookmaker Odds", [])
            cs_odds_statsbetting = odds.get("Clean Sheet Probability by Stats Betting Market", [])
            cs_odds_historical = odds.get("Clean Sheet Probability by Historical Data", [])
            position = odds.get("Position", ["Unknown"])[0]
            saves_average_bookmaker = odds.get("xSaves by Bookmaker Odds", [])
            saves_average_historical = odds.get("Saves by Historical Data", [])
            team_saves_average = odds.get("Team Saves by Historical Data", [])

            goals_conceded_team_bookmaker = odds.get('Goals Conceded by Team on Average', [])
            goals_conceded_team_historical = odds.get('Team xGC by Historical Data', [])

            minutes_per_game = odds.get("Minutes per Game", [0])[0]

            cbi_per_game = odds.get("CBI per Game", [0])[0]
            recoveries_per_game = odds.get("Recoveries per Game", [0])[0]
            tackles_per_game = odds.get("Tackles per Game", [0])[0]

            # If there are more probability/average entries than number of games in the gameweek for a player, skip the player
            if len(goals_average_bookmaker) > number_of_games or len(ass_average_bookmaker) > number_of_games or len(saves_average_bookmaker) > number_of_games:
                print(f"Calculating BPS for {player} skipped due to data entries being higher than number of games the player is playing")
                continue

            for g1, g2, a1, a2, cs1, cs2, cs3, ga1, ga2, s1, s2, s3, opp in zip_longest(goals_average_bookmaker, goals_average_historical, ass_average_bookmaker, ass_average_historical, cs_odds_bookmaker, cs_odds_statsbetting, cs_odds_historical, goals_conceded_team_bookmaker, goals_conceded_team_historical, saves_average_bookmaker, saves_average_historical, team_saves_average, opponents, fillvalue=-1):
                xg = g1 if g1 != -1 else max(g2, 0)
                xa = a1 if a1 != -1 else max(a2, 0)
                xcs = cs1 if cs1 != -1 else cs2 if cs1 != -1 else max(cs3, 0)
                xgc = ga1 if ga1 != -1 else max(ga2, 0)

                if saves_button:
                    saves_avg = (2 * s2 + s3) / 3 if s2 != -1 and s3 != -1 else 0
                else:
                    saves_avg = 0
                xsav = s1 if s1 != -1 else saves_avg

                bps = 0.0
                bps += xa * 9                   # Assist
                bps += cbi_per_game / 2         # For every 2 clearances, blocks and interceptions (total)
                bps += recoveries_per_game / 3  # For every 3 recoveries
                bps += tackles_per_game * 2     # Successful tackle

                # Based on historical match data, roughly 25% of all goals scored in the Premier League end up being the winning goal. 
                bps += (0.25 * xg) * 3 # Scoring the goal that wins a match

                if minutes_per_game > 60:
                    bps += 6 # Playing over 60 minutes
                elif minutes_per_game > 0:
                    bps += 3 # Playing 1 to 60 minutes
                else:
                    bps += 0 # Playing under 60 minutes

                if position == 'GKP':
                    # Save from a shot inside the box is 3 and Save from a shot outside the box is 2, using the average in calculations
                    bps += xsav * 2.5   # Save from a shot 
                    
                
                if position == 'DEF' or position == 'GKP':
                    bps += xcs * 12     # Goalkeepers and defenders keeping a clean sheet
                    bps -= xgc * 4      # Goalkeepers and defenders conceding a goal
                    bps += xg * 12      # Goalkeepers and defenders scoring a goal

                if position == 'MID':
                    bps += xg * 18      # Midfielders scoring a goal

                if position == 'FWD':
                    bps += xg * 24      # Forwards scoring a goal

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

    promoted_g_h_average = 1.00
    promoted_g_a_average = 0.90

    promoted_gc_h_average = 2.00
    promoted_gc_a_average = 2.20

    home_pos_range = get_pos_range(team_stats_dict[home_team]['League Position'])
    away_pos_range = get_pos_range(team_stats_dict[away_team]['League Position'])

    home_goals_p90_24_25 = team_stats_dict[home_team]['24/25 Goals per Home Game']
    away_goals_p90_24_25 = team_stats_dict[away_team]['24/25 Goals per Away Game']
    home_goals_conceded_p90_24_25 = team_stats_dict[home_team]['24/25 Goals Conceded per Home Game']
    away_goals_conceded_p90_24_25 = team_stats_dict[away_team]['24/25 Goals Conceded per Away Game']

    home_goals_p90_25_26 = team_stats_dict[home_team]['25/26 Goals per Home Game']
    away_goals_p90_25_26 = team_stats_dict[away_team]['25/26 Goals per Away Game']
    home_goals_conceded_p90_25_26 = team_stats_dict[home_team]['25/26 Goals Conceded per Home Game']
    away_goals_conceded_p90_25_26 = team_stats_dict[away_team]['25/26 Goals Conceded per Away Game']

    home_weighted_goals_p90 = (home_goals_p90_24_25 + 2 * home_goals_p90_25_26) / 3 if home_goals_p90_24_25 >= 0 else home_goals_p90_25_26
    away_weighted_goals_p90 = (away_goals_p90_24_25 + 2 * away_goals_p90_25_26) / 3 if away_goals_p90_24_25 >= 0 else away_goals_p90_25_26
    home_weighted_goals_conceded_p90 = (home_goals_conceded_p90_24_25 + 2 * home_goals_conceded_p90_25_26) / 3 if home_goals_conceded_p90_24_25 >= 0 else home_goals_conceded_p90_25_26
    away_weighted_goals_conceded_p90 = (away_goals_conceded_p90_24_25 + 2 * away_goals_conceded_p90_25_26) / 3 if away_goals_conceded_p90_24_25 >= 0 else away_goals_conceded_p90_25_26

    home_conceded_against_string = f"Goals Conceded per Game Against {away_pos_range}"
    away_conceded_against_string = f"Goals Conceded per Game Against {home_pos_range}"
    home_scored_against_string = f"Goals per Game Against {away_pos_range}"
    away_scored_against_string = f"Goals per Game Against {home_pos_range}"

    home_conceded_against_24_25 = team_stats_dict[home_team][f"24/25 {home_conceded_against_string}"]
    away_conceded_against_24_25 = team_stats_dict[away_team][f"24/25 {away_conceded_against_string}"]
    home_scored_against_24_25 = team_stats_dict[home_team][f"24/25 {home_scored_against_string}"]
    away_scored_against_24_25 = team_stats_dict[away_team][f"24/25 {away_scored_against_string}"]

    home_conceded_against_25_26 = team_stats_dict[home_team][f"25/26 {home_conceded_against_string}"]
    away_conceded_against_25_26 = team_stats_dict[away_team][f"25/26 {away_conceded_against_string}"]
    home_scored_against_25_26 = team_stats_dict[home_team][f"25/26 {home_scored_against_string}"]
    away_scored_against_25_26 = team_stats_dict[away_team][f"25/26 {away_scored_against_string}"]

    home_weighted_conceded_against = (home_conceded_against_24_25 + 3 * home_conceded_against_25_26) / 4 if home_conceded_against_24_25 >= 0 else home_conceded_against_25_26
    away_weighted_conceded_against = (away_conceded_against_24_25 + 3 * away_conceded_against_25_26) / 4 if away_conceded_against_24_25 >= 0 else away_conceded_against_25_26
    home_weighted_scored_against = (home_scored_against_24_25 + 3 * home_scored_against_25_26) / 4 if home_scored_against_24_25 >= 0 else home_scored_against_25_26
    away_weighted_scored_against = (away_scored_against_24_25 + 3 * away_scored_against_25_26) / 4 if away_scored_against_24_25 >= 0 else away_scored_against_25_26

    home_xgc_against_string = f"xGC per Game Against {away_pos_range}"
    away_xgc_against_string = f"xGC per Game Against {home_pos_range}"
    home_xg_against_string = f"xG per Game Against {away_pos_range}"
    away_xg_against_string = f"xG per Game Against {home_pos_range}"

    home_goals = (home_weighted_goals_p90 + 1.5 * home_weighted_scored_against + 1.5 * team_stats_dict[home_team][home_xg_against_string] + team_stats_dict[home_team]['xG per Home Game']) / 5
    away_goals = (away_weighted_goals_p90 + 1.5 * away_weighted_scored_against + 1.5 * team_stats_dict[away_team][away_xg_against_string] + team_stats_dict[away_team]['xG per Away Game']) / 5
    home_goals_conceded = (home_weighted_goals_conceded_p90 + 1.5 * home_weighted_conceded_against + 1.5 * team_stats_dict[home_team][home_xgc_against_string] + team_stats_dict[home_team]['xGC per Home Game']) / 5
    away_goals_conceded = (away_weighted_goals_conceded_p90 + 1.5 * away_weighted_conceded_against + 1.5 * team_stats_dict[away_team][away_xgc_against_string] + team_stats_dict[away_team]['xGC per Away Game']) / 5

    home_xg = (home_goals + away_goals_conceded) / 2
    away_xg = (away_goals + home_goals_conceded) / 2

    home_team_saves_24_25 = team_stats_dict[home_team]['24/25 Goalkeeper Saves per Home Game']
    away_team_saves_24_25 = team_stats_dict[away_team]['24/25 Goalkeeper Saves per Away Game']

    home_team_saves_25_26 = team_stats_dict[home_team]['25/26 Goalkeeper Saves per Home Game']
    away_team_saves_25_26 = team_stats_dict[away_team]['25/26 Goalkeeper Saves per Away Game']

    home_team_saves = (2 * home_team_saves_25_26 + home_team_saves_24_25) / 3 if home_team_saves_24_25 >= 0 else home_team_saves_25_26
    away_team_saves = (2 * away_team_saves_25_26 + away_team_saves_24_25)/ 3 if away_team_saves_24_25 >= 0 else away_team_saves_25_26 

    for player, stats in player_dict.items():
        if stats['Team'][0] == home_team:
            player_dict[player]['Team xG by Historical Data'].append(home_xg)
            player_dict[player]['Team xGC by Historical Data'].append(away_xg)
            player_dict[player]["Clean Sheet Probability by Historical Data"].append(math.exp(-away_xg))

            if player_dict[player]['Position'][0] == 'GKP':
                gkp_saves_24_25 = player_dict[player].get('24/25 Saves per Home Game for Current Team', [0])[0]
                gkp_saves_25_26 = player_dict[player].get('25/26 Saves per Home Game for Current Team', [0])[0]
                gkp_saves = (2 * gkp_saves_25_26 + gkp_saves_24_25) / 3 if gkp_saves_24_25 >= 0 else gkp_saves_25_26

                player_dict[player]['Saves by Historical Data'].append(gkp_saves)
                player_dict[player]['Team Saves by Historical Data'].append(home_team_saves)

        if stats['Team'][0] == away_team:
            player_dict[player]['Team xG by Historical Data'].append(away_xg)
            player_dict[player]['Team xGC by Historical Data'].append(home_xg)
            player_dict[player]["Clean Sheet Probability by Historical Data"].append(math.exp(-home_xg))

            if player_dict[player]['Position'][0] == 'GKP':
                gkp_saves_24_25 = player_dict[player].get('24/25 Saves per Away Game for Current Team', [0])[0]
                gkp_saves_25_26 = player_dict[player].get('25/26 Saves per Away Game for Current Team', [0])[0]
                gkp_saves = (2 * gkp_saves_25_26 + gkp_saves_24_25) / 3 if gkp_saves_24_25 >= 0 else gkp_saves_25_26

                player_dict[player]['Saves by Historical Data'].append(gkp_saves)
                player_dict[player]['Team Saves by Historical Data'].append(away_team_saves)

def expected_save_points(m: float, max_k: int = 12) -> float:
    """
    Estimate expected FPL save points using Poisson(m).
    
    Parameters:
    - m: average saves per match
    - max_k: maximum number of saves to consider in summation
    
    Returns:
    - Expected save points (fractional expectation)
    """
    k_values = np.arange(0, max_k + 1)
    pmf_values = poisson.pmf(k_values, mu=m)
    expected_points = np.sum((k_values // 3) * pmf_values)
    return expected_points

def expected_conceded_deductions(m: float, max_k: int = 8) -> float:
    """
    Estimate expected lost points for goalkeepers and defenders due to goals conceded using Poisson(m).
    
    Parameters:
    - m: Expected goals conceded
    - max_k: maximum number of goals conceded to consider in summation
    
    Returns:
    - Expected lost points due to goals conceded (fractional expectation)
    """
    k_values = np.arange(0, max_k + 1)
    pmf_values = poisson.pmf(k_values, mu=m)
    expected_points_deducted = np.sum((k_values // 2) * pmf_values)
    return expected_points_deducted

def expected_defensive_contributions_probability(m, threshold) -> float:
    """
    Estimate probability that a player gets >= threshold defensive contributions in a match.
    
    Parameters:
    - m (float): average defensive contributions per game
    - threshold (int): threshold number of defensive contributions to calculate probability for (10 for defenders, 12 for other positions)
    
    Returns:
    float: probability of >= threshold contributions
    """
    # P(X >= threshold) = 1 - P(X <= threshold - 1)
    prob_thresh_or_more = 1 - poisson.cdf(threshold-1, mu=m)
    return prob_thresh_or_more


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
    
            opponents = odds.get("Opponent", [])
            number_of_games = len(odds.get("Opponent", [])) if team != 'Unknown' else 1
            mins_per_game = odds.get("Minutes per Game", [90])[0]
            mins_played_points = 1 + min(mins_per_game/70, 1) if mins_per_game >= 45 else 1 if mins_per_game > 0 else 0
            goals_average_bookmaker = odds.get("xG by Bookmaker Odds", [])
            goals_average_historical = odds.get("xG by Historical Data", [])
            goals_average = []
            ass_average_bookmaker = odds.get("xA by Bookmaker Odds", []) 
            ass_average_historical = odds.get("xA by Historical Data", []) 
            ass_average = []        
            cs_odds_bookmaker = odds.get("Clean Sheet Probability by Bookmaker Odds", [])
            cs_odds_statsbetting = odds.get("Clean Sheet Probability by Stats Betting Market", [])
            cs_odds_historical = odds.get("Clean Sheet Probability by Historical Data", [])
            cs_odds = []
            position = odds.get("Position", ["Unknown"])[0]
            saves_average_bookmaker = odds.get("xSaves by Bookmaker Odds", [])
            saves_average_historical = odds.get("Saves by Historical Data", [])
            saves_points = []
            team_saves_average = odds.get("Team Saves by Historical Data", [])

            goals_conceded_team_bookmaker = odds.get('Goals Conceded by Team on Average', [])
            goals_conceded_team_historical = odds.get('Team xGC by Historical Data', [])
            goals_conceded_team = []

            chance_of_playing = odds.get("Chance of Playing", [1])[0] if team != 'Unknown' else 1

            def_contr_avg = (2 * odds.get("25/26 Defensive Contributions per Game", [0])[0] + odds.get("24/25 Defensive Contributions per Game", [0])[0]) / 3 if odds.get("24/25 Games Played", [0])[0] > 0 and odds.get("25/26 Games Played", [0])[0] > 0 else odds.get("25/26 Defensive Contributions per Game", [0])[0] if odds.get("25/26 Games Played", [0])[0] > 0 else odds.get("24/25 Defensive Contributions per Game", [0])[0]
            def_contr_threshold = 10 if position == 'DEF' else 12
            dc_points = expected_defensive_contributions_probability(def_contr_avg, def_contr_threshold) * 2
            player_dict[player]['Estimated DC points per Game'] = round(dc_points, 3)

            bonus_points = odds.get('Estimated Bonus Points', [])

            points_all_gws = []
            for g1, g2, a1, a2, cs1, cs2, cs3, ga1, ga2, s1, s2, s3, bp1, opp in zip_longest(goals_average_bookmaker, goals_average_historical, ass_average_bookmaker, ass_average_historical, cs_odds_bookmaker, cs_odds_statsbetting, cs_odds_historical, goals_conceded_team_bookmaker, goals_conceded_team_historical, saves_average_bookmaker, saves_average_historical, team_saves_average, bonus_points, opponents, fillvalue=-1):
                goals_average.append(g1 if g1 != -1 else max(g2, 0))
                ass_average.append(a1 if a1 != -1 else max(a2, 0))
                cs_odds.append(cs1 if cs1 != -1 else cs2 if cs2 != -1 else max(cs3, 0))
                goals_conceded_team.append(ga1 if ga1 != -1 else max(ga2, 0))

                if saves_button:
                    saves_avg = (2 * s2 + s3) / 3 if s2 != -1 and s3 != -1 else 0

                    if saves_avg > 0:
                        max_k = int(math.ceil(2 * saves_avg + 3))
                        saves_points_historical = expected_save_points(saves_avg, max_k)
                    else:
                        saves_points_historical = 0
                        
                else:
                    saves_avg = 0
                    saves_points_historical = 0

                if s1 != -1:
                    max_k = int(math.ceil(2 * s1 + 3))
                    saves_points_bookmaker = expected_save_points(s1, max_k)
                    saves_points.append(saves_points_bookmaker)
                    xsavp = saves_points_bookmaker
                else:
                    saves_points.append(saves_points_historical)
                    xsavp = saves_points_historical

                player_dict[player]['Expected Saves by Historical Data'].append(saves_avg)
                player_dict[player]['Expected Save Points'].append(xsavp)

                xg = g1 if g1 != -1 else max(g2, 0)
                xa = a1 if a1 != -1 else max(a2, 0)
                xcs = cs1 if cs1 != -1 else cs2 if cs2 != -1 else max(cs3, 0)
                xgc = ga1 if ga1 != -1 else max(ga2, 0)
                bp = bp1 if bp1 != -1 else 0

                points = 0

                if position in ('GKP'):
                    points = chance_of_playing * (2 + xsavp +
                    xcs * 4 - expected_conceded_deductions(xgc) + bp + dc_points)

                if position in ('DEF'):
                    points = chance_of_playing * (
                    mins_played_points + xg * 6 + xa * 3 +
                    (min(mins_per_game/60, 1) * xcs) * 4
                    - expected_conceded_deductions(xgc) + bp + dc_points)

                if position in ('MID'):
                    points = chance_of_playing * (
                    mins_played_points + xg * 5 + xa * 3 +
                    min(mins_per_game/60, 1) * xcs + 
                    bp + dc_points)

                if position in ('FWD'):
                    points = chance_of_playing * (
                    mins_played_points + xg * 4 + xa * 3 +
                    bp + dc_points)

                if position in ('Unknown'):
                    points = chance_of_playing * (2 +
                    xg * 4 + xa * 3)

                points_all_gws.append(round(points, 3))

            player_dict[player]['Expected Points'] = points_all_gws

            player_dict[player]['Expected Points Sum'] = round(sum(points_all_gws), 3)
            
        except Exception as e:
            print(f"Could not calculate points for {player}: {e}")
            st.write(f"[DEBUG] Error calculating points for player {player}: {e}")

def initialize_predicted_points_df(all_odds_dict, fixtures, start_gw, saves_button: bool, bps_button: bool, gws: int):
    extra_gws_to_predict = [start_gw + i for i in range(1, gws)]
    extra_fixtures = [fixture for fixture in fixtures if (fixture['event'] in extra_gws_to_predict) and (fixture['started'] == False)]

    data, teams_data, players_data, team_id_to_name, player_id_to_name = fetch_fpl_data()
    element_types = position_mapping(data)

    team_stats_dict, player_stats_dict = construct_team_and_player_data(data, team_id_to_name, player_id_to_name, fixtures)
    player_dict = player_dict_constructor(players_data, team_stats_dict, player_stats_dict, element_types, team_id_to_name)

    for fixture in extra_fixtures:
        home_team_id = fixture['team_h']
        away_team_id = fixture['team_a']
        home_team_name = team_id_to_name.get(home_team_id, "Unknown Team")
        away_team_name = team_id_to_name.get(away_team_id, "Unknown Team")
        home_team = TEAM_NAMES_ODDSCHECKER.get(home_team_name, home_team_name)
        away_team = TEAM_NAMES_ODDSCHECKER.get(away_team_name, away_team_name)
        if home_team is None:
            home_team = home_team_name
        if away_team is None:
            away_team = away_team_name
        match_title = home_team + " v " + away_team

        all_odds_dict[match_title] = {}
        all_odds_dict[match_title]['home_team'] = home_team
        all_odds_dict[match_title]['away_team'] = away_team

    for match, details in all_odds_dict.items():
        home_team_name = details.get('home_team', 'Unknown')
        away_team_name = details.get('away_team', 'Unknown')
        home_team = TEAM_NAMES_ODDSCHECKER.get(home_team_name, home_team_name)
        away_team = TEAM_NAMES_ODDSCHECKER.get(away_team_name, away_team_name)
        for player in player_dict:
            if player_dict[player].get('Team', ['Unknown'])[0] == home_team:
                player_dict[player]['Opponent'].append(away_team)
            if player_dict[player].get('Team', ['Unknown'])[0] == away_team:
                player_dict[player]['Opponent'].append(home_team)

    for match, details in all_odds_dict.items():
        home_team_name = details.get('home_team', 'Unknown')
        away_team_name = details.get('away_team', 'Unknown')
        home_team = TEAM_NAMES_ODDSCHECKER.get(home_team_name, home_team_name)
        away_team = TEAM_NAMES_ODDSCHECKER.get(away_team_name, away_team_name)
        
        total_home_goals_probs = None
        total_away_goals_probs = None
        home_margin = 0.05
        away_margin = 0.05

        if home_team is not None and away_team is not None:
            calc_team_xgs(home_team, away_team, team_stats_dict, player_dict)

        if details.get('Total Home Goals', 'Unknown') != 'Unknown':    
            total_home_goals_probs, home_margin = get_total_goals_over_probs(details['Total Home Goals'], "home") 

        if details.get('Total Away Goals', 'Unknown') != 'Unknown':
            total_away_goals_probs, away_margin = get_total_goals_over_probs(details['Total Away Goals'], "away")

        total_combined_goals_dict = total_home_goals_probs | total_away_goals_probs if total_home_goals_probs and total_away_goals_probs else None
        if total_combined_goals_dict:
            if home_team is not None and away_team is not None:
                add_total_goals_probs_to_dict(total_combined_goals_dict, home_team, away_team, player_dict)
                bookmaker_margin = (home_margin + away_margin) / 2
            else:
                # Handle the case where home_team or away_team is None
                print("Error adding Total Goals: home_team or away_team is None")
                bookmaker_margin = 0.05

        for odd_type, odds in details.items():
            if odd_type == 'Player Assists':
                if home_team is not None and away_team is not None:
                    get_player_over_probs(odd_type, odds, player_dict, home_team, away_team, bookmaker_margin)
                else:
                    # Handle the case where home_team or away_team is None
                    print("Error adding Player Assists: home_team or away_team is None")

            if odd_type == 'Goalkeeper Saves':
                if home_team is not None and away_team is not None:
                    get_player_over_probs(odd_type, odds, player_dict, home_team, away_team, bookmaker_margin)
                else:
                    # Handle the case where home_team or away_team is None
                    print("Error adding Goalkeeper Saves: home_team or away_team is None")

            if odd_type == 'To Score A Hat-Trick':
                if home_team is not None and away_team is not None:
                    add_probs_to_dict(odd_type, odds, player_dict, home_team, away_team, bookmaker_margin)
                else:
                    # Handle the case where home_team or away_team is None
                    print("Error adding To Score A Hat-Trick: home_team or away_team is None")

            if odd_type == 'Anytime Goalscorer':
                if home_team is not None and away_team is not None:
                    add_probs_to_dict(odd_type, odds, player_dict, home_team, away_team, bookmaker_margin)
                else:
                    # Handle the case where home_team or away_team is None
                    print("Error adding Anytime Goalscorer: home_team or away_team is None")

            if odd_type == 'To Score 2 Or More Goals':
                if home_team is not None and away_team is not None:
                    add_probs_to_dict(odd_type, odds, player_dict, home_team, away_team, bookmaker_margin)
                else:
                    # Handle the case where home_team or away_team is None
                    print("Error adding To Score 2 Or More Goals: home_team or away_team is None") 

            if odd_type == 'Clean Sheet':
                home_cs_odds = odds.get(home_team, [])
                away_cs_odds = odds.get(away_team, [])

                home_no_cs_odds = odds.get(f"{home_team} - No", [])
                away_no_cs_odds = odds.get(f"{away_team} - No", [])

                ave_home_cs_odd = sum(home_cs_odds)/len(home_cs_odds) if len(home_cs_odds) != 0 else 0
                ave_away_cs_odd = sum(away_cs_odds)/len(away_cs_odds) if len(away_cs_odds) != 0 else 0

                ave_home_no_cs_odd = sum(home_no_cs_odds)/len(home_no_cs_odds) if len(home_no_cs_odds) != 0 else 0
                ave_away_no_cs_odd = sum(away_no_cs_odds)/len(away_no_cs_odds) if len(away_no_cs_odds) != 0 else 0

                home_cs_prob = (1 / float(ave_home_cs_odd)) if ave_home_cs_odd != 0 else 0
                away_cs_prob = (1 / float(ave_away_cs_odd)) if ave_away_cs_odd != 0 else 0

                home_no_cs_prob = (1 / float(ave_home_no_cs_odd)) if ave_home_no_cs_odd != 0 else 0
                away_no_cs_prob = (1 / float(ave_away_no_cs_odd)) if ave_away_no_cs_odd != 0 else 0

                if home_cs_prob != 0 and home_no_cs_prob != 0:
                    home_margin = (home_cs_prob + home_no_cs_prob) - 1
                if away_cs_prob != 0 and away_no_cs_prob != 0:
                    away_margin = (away_cs_prob + away_no_cs_prob) - 1

                for player in player_dict:
                    if player_dict[player].get('Team', ['Unknown'])[0] == home_team:
                        player_dict[player]['Clean Sheet Probability by Stats Betting Market'].append(home_cs_prob / (1 + home_margin))
                    if player_dict[player].get('Team', ['Unknown'])[0] == away_team:
                        player_dict[player]['Clean Sheet Probability by Stats Betting Market'].append(away_cs_prob / (1 + away_margin))
    
    calc_specific_probs(player_dict)
    if bps_button:
        with st.spinner("Calculating predicted bonus points..."):
            calc_avg_bps(player_dict, saves_button)
            match_bps_dict = defaultdict(list)
            for match, details in all_odds_dict.items():
                match_bps_home = []
                match_bps_away = []
                home_team_name = details.get('home_team')
                away_team_name = details.get('away_team')
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

                match_bps_home = sorted(match_bps_home, reverse=True)[:12]
                match_bps_away = sorted(match_bps_away, reverse=True)[:12]
                match_bps = match_bps_home + match_bps_away
                match_bps_dict[home_team].append(sorted(match_bps, reverse=True)[:22])
                match_bps_dict[away_team].append(sorted(match_bps, reverse=True)[:22])

            for player in player_dict:
                team = player_dict[player].get('Team', ['Unknown'])[0]
                match_bps_list = match_bps_dict.get(team, [[0.0]])
                player_bps = player_dict[player].get('Estimated BPS', [0.0])
                if len(player_bps) != gws:
                    player_dict[player]['Estimated Bonus Points'] = [0.0] * gws
                    continue
                for match_bps, p_bps in zip_longest(match_bps_list, player_bps):
                    if match_bps is None:
                        continue
                    if p_bps == 0.0 or p_bps is None or sum(match_bps) == 0.0:
                        player_bonus_points = 0.0
                    else:
                        player_bonus_points = max((p_bps / (sum(match_bps) + p_bps)) * 6, 0.0)
                    player_dict[player]['Estimated Bonus Points'].append(player_bonus_points)

    calc_points(player_dict, saves_button)

    # Create and save DataFrames with all player data and a summary of expected points.
    player_data_df = pd.DataFrame.from_dict(player_dict, orient='index')
    player_data_df.index.name = 'Player'
    
    # Convert all columns: if value is a list of length 1, replace with the value contained in the list.
    for col in player_data_df.columns:
        player_data_df[col] = player_data_df[col].apply(lambda x: x[0] if isinstance(x, list) and len(x) == 1 else x)

    return player_data_df, player_stats_dict, team_stats_dict

st.set_page_config(page_title="FPL Predicted Points", page_icon="📈")

st.markdown("# FPL Predicted Points")
st.write(
    """This is a FPL Predicted Points tool for viewing Fantasy Premier League predicted points according to the bookmaker odds scraped from Oddschecker.com"""
)

fixtures = get_all_fixtures()
next_gw = get_next_gw(fixtures)

cur_dir = os.getcwd()
fixtures_dir = os.path.join(cur_dir, "data", "fixture_data")
odds_filename = os.path.join(fixtures_dir, f"gw{next_gw}_all_odds_")

odds_json_files = glob.glob(f"{odds_filename}*.json")

if odds_json_files:
    latest_odds_path = max(odds_json_files)
    latest_odds_name = latest_odds_path.replace(fixtures_dir, '')
    git_parts = latest_odds_name.replace(".json", '').split('_')
    git_timestamp = f"{git_parts[3][2:]}.{git_parts[3][:2]} {git_parts[4][:2]}:{git_parts[4][2:]}"
    st.info(f"Github repository's latest scraped odds file for next gameweek has a timestamp of {git_timestamp}")
    upload_new_odds_button = st.toggle("Upload more recent odds file for predicted points calculation",
    value=False)
    if upload_new_odds_button:
        uploaded_odds = st.file_uploader("Choose a file", type="json")
        if uploaded_odds:
            uploaded_odds_name = uploaded_odds.name
            parts = uploaded_odds_name.replace(".json", '').split('_')
            gw = parts[0].replace("gw", '')
            timestamp = f"{parts[3][2:]}.{parts[3][:2]} {parts[4][:2]}:{parts[4][2:]}"
            if next_gw == int(gw):
                try:
                    all_odds_dict = json.load(uploaded_odds)
                    st.info(f"Using uploaded odds file with a timestamp of {timestamp} instead of Github repository odds file with timestamp of {git_timestamp}")
                except Exception as e:
                    st.warning(f"Could not load all odds file {uploaded_odds_name} into dictionary.")
                    all_odds_dict = {}
            else:
                st.warning(f"Odds in uploaded file {uploaded_odds_name} are not for the next gameweek ({next_gw}).")
                all_odds_dict = {}
    else:
        try:
            with open(latest_odds_path, 'r') as file:
                all_odds_dict = json.load(file)
                st.info(f"Using odds file with a timestamp of {git_timestamp}")
        except IOError:
            st.warning(f"Could not open all odds file {latest_odds_path} found in Github repository.")
            all_odds_dict = {}
else:
    st.warning("Latest scraped odds file for next gameweek not found in Github repository, please upload odds file for the next gameweek.")
    uploaded_odds = st.file_uploader("Choose a file", type="json")
    if uploaded_odds:
        uploaded_odds_name = uploaded_odds.name
        parts = uploaded_odds_name.replace(".json", '').split('_')
        gw = parts[0].replace("gw", '')
        timestamp = f"{parts[3][2:]}.{parts[3][:2]} {parts[4][:2]}:{parts[4][2:]}"
        if next_gw == int(gw):
            try:
                all_odds_dict = json.load(uploaded_odds)
                st.info(f"Using uploaded odds file with timestamp of {timestamp}")
            except Exception as e:
                st.warning(f"Could not load all odds file {uploaded_odds_name} into dictionary.")
                all_odds_dict = {}
        else:
            st.warning(f"Odds in uploaded file {uploaded_odds_name} are not for the next gameweek ({next_gw}).")
            all_odds_dict = {}

st.header("Step 1: Select metrics to use in predicted points calculations")
saves_button = st.toggle(
    "Use Saves per Game in predicted points calculation for goalkeepers if odds for Goalkeeper Saves are not available",
    value=True
)
bps_button = st.toggle(
    "Include Estimated Bonus Points for predicted points calculation",
    value=False
)
    
gws_to_predict = st.slider("Select amount of gameweeks to calculate predicted points for", min_value=1, max_value=38 - next_gw + 1, value=1)
current_time = datetime.now()

if st.button("Fetch Latest Player and Team Statistics"):
    with st.spinner("Fetching latest Statistics...", show_time=True):
        data, teams_data, players_data, team_id_to_name, player_id_to_name = fetch_fpl_data()
        element_types = position_mapping(data)
        team_stats_dict, player_stats_dict = construct_team_and_player_data(data, team_id_to_name, player_id_to_name, fixtures)
        st.session_state.player_stats_dict = player_stats_dict
        st.session_state.team_stats_dict = team_stats_dict
        st.success("Player and Team Statistics Fetched Successfully!")

if st.button("Calculate Predicted Points"):
    with st.spinner("Calculating Predicted Points...", show_time=True):
        st.session_state.df, st.session_state.player_stats_dict, st.session_state.team_stats_dict = initialize_predicted_points_df(
            all_odds_dict, fixtures, next_gw, saves_button, bps_button, gws_to_predict
        )

if "player_stats_dict" in st.session_state:
    st.subheader("Player Statistics Data")
    player_stats_json = json.dumps(st.session_state.player_stats_dict, indent=4).encode('utf-8')
    st.download_button(
        label="Download Player Statistics as JSON",
        data=player_stats_json,
        file_name=f"gw{next_gw}_{current_time.strftime('%m')}{current_time.strftime('%d')}_{current_time.strftime('%H')}{current_time.strftime('%M')}_player_statistics.json",
        mime="text/json"
    )

if "team_stats_dict" in st.session_state:
    st.subheader("Team Statistics Data")
    team_stats_json = json.dumps(st.session_state.team_stats_dict, indent=4).encode('utf-8')
    st.download_button(
        label="Download Team Statistics as JSON",
        data=team_stats_json,
               file_name=f"gw{next_gw}_{current_time.strftime('%m')}{current_time.strftime('%d')}_{current_time.strftime('%H')}{current_time.strftime('%M')}_team_statistics.json",
        mime="text/json"
    )
# Step 3: Show filters and calculation only if data is loaded
if "df" in st.session_state:
    df = st.session_state.df
    chart_df = df

    columns = df.columns.tolist()
    column_names = st.multiselect("Select Columns to Display", columns, default=columns)
    if column_names:
        df = df.loc[:, column_names]

    # Position filter
    if "Position" in df.columns:
        all_positions = sorted(df["Position"].dropna().unique())
        selected_positions = st.multiselect("Select Player Position(s)", all_positions)
        if selected_positions:
            df = df[df["Position"].isin(selected_positions)]

    # Price filter
    if "Price" in df.columns:
        min_price = float(df["Price"].min())
        max_price = float(df["Price"].max())
        selected_price_range = st.slider("Select Price Range (in £m)", min_value=min_price, max_value=max_price, value=(min_price, max_price))
        df = df[(df["Price"] >= selected_price_range[0]) & (df["Price"] <= selected_price_range[1])]

    # Final calculation and display
    if st.button("Show Predicted Points"):
        st.subheader("Predicted Points for Filtered Players")
        st.dataframe(df)

        # Download button
        df_csv = df.to_csv(index=False).encode('utf-8')
        st.download_button(
            label="Download Predicted Points as CSV",
            data=df_csv,
            file_name=f"gw{next_gw}_filtered_predicted_points.csv",
            mime="text/csv"
        )
        
        # Separate goalkeepers and others
        df_gk = chart_df[chart_df["Position"] == "GKP"]
        df_others = chart_df[chart_df["Position"] != "GKP"]

        # For goalkeepers, keep only one per team with highest predicted points
        df_gk_sorted = df_gk.sort_values("Expected Points Sum", ascending=False)
        df_gk_one_per_team = df_gk_sorted.drop_duplicates(subset="Team", keep="first")

        # Combine and get top 5 per position
        df_combined = pd.concat([df_gk_one_per_team, df_others])

        # Get top 5 players per position
        top_players = df_combined.groupby("Position", group_keys=False).apply(lambda x: x.nlargest(5, "Expected Points Sum"))

        # Create chart
        fig = px.bar(
            top_players,
            x="Nickname",
            y="Expected Points Sum",
            color="Position",
            title="Top 5 FPL Players by Position",
            labels={"Predicted Points": "Expected Points Sum"},
            hover_data=["Minutes per Game", "Team"]
        )

        # Display in Streamlit
        st.plotly_chart(fig, use_container_width=True)


