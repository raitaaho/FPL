import pandas as pd
import ast
import requests
from collections import defaultdict

def get_pos_range(position: int) -> str:
    """
    Return the league position range string for a given position (1-5, 6-10, etc.).

    Args:
        position (int): League position.

    Returns:
        str: Position range as string.
    """
    if position <= 5:
        return '1-5'
    elif position <= 10:
        return '6-10'
    elif position <= 15:
        return '11-15'
    elif position <= 20:
        return '16-20'
    else:
        return 'Unknown'
    
def get_team_template(pos_22_23: int, pos_23_24: int, pos: int) -> dict:
    """
    Create a template dictionary for storing team statistics, initialized to default values.

    Args:
        pos_22_23 (int): Team's position in 2022/23 season.
        pos_23_24 (int): Team's position in 2023/24 season.
        pos (int): Current league position.

    Returns:
        dict: Team statistics template.
    """
    team_template = {'League Position': pos,
        '22/23 League Position': pos_22_23,
        '23/24 League Position': pos_23_24,                                                         
        'ELO': 1000,
        'Home ELO': 1000,
        'Away ELO': 1000,
        'Home ELO 22/23': 1000,
        'Away ELO 22/23': 1000,
        'Home ELO 23/24': 1000,
        'Away ELO 23/24': 1000,
        'Home ELO 24/25': 1000,
        'Away ELO 24/25': 1000,
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
        '22/23 Home Goals': 0,
        '22/23 Away Goals': 0,
        '22/23 Home Assists': 0,
        '22/23 Away Assists': 0,
        '22/23 Goals Conceded Home': 0,
        '22/23 Goals Conceded Away': 0,
        '22/23 Home Goalkeeper Saves': 0,
        '22/23 Away Goalkeeper Saves': 0,
        '23/24 Home Goals': 0,
        '23/24 Away Goals': 0,
        '23/24 Home Assists': 0,
        '23/24 Away Assists': 0,
        '23/24 Goals Conceded Home': 0,
        '23/24 Goals Conceded Away': 0,
        '23/24 Home Goalkeeper Saves': 0,
        '23/24 Away Goalkeeper Saves': 0,
        'Home Games Against 1-5': 0,
        'Home Goals Against 1-5': 0,
        'Home Goals Conceded Against 1-5': 0,
        'Home Games Against 6-10': 0,
        'Home Goals Against 6-10': 0,
        'Home Goals Conceded Against 6-10': 0,
        'Home Games Against 11-15': 0,
        'Home Goals Against 11-15': 0,
        'Home Goals Conceded Against 11-15': 0,
        'Home Games Against 16-20': 0,
        'Home Goals Against 16-20': 0,
        'Home Goals Conceded Against 16-20': 0,
        'Away Games Against 1-5': 0,
        'Away Goals Against 1-5': 0,
        'Away Goals Conceded Against 1-5': 0,
        'Away Games Against 6-10': 0,
        'Away Goals Against 6-10': 0,
        'Away Goals Conceded Against 6-10': 0,
        'Away Games Against 11-15': 0,
        'Away Goals Against 11-15': 0,
        'Away Goals Conceded Against 11-15': 0,
        'Away Games Against 16-20': 0,
        'Away Goals Against 16-20': 0,
        'Away Goals Conceded Against 16-20': 0,
        '22/23 Home Games Against 1-5': 0,
        '22/23 Home Goals Against 1-5': 0,
        '22/23 Home Goals Conceded Against 1-5': 0,
        '22/23 Home Games Against 6-10': 0,
        '22/23 Home Goals Against 6-10': 0,
        '22/23 Home Goals Conceded Against 6-10': 0,
        '22/23 Home Games Against 11-15': 0,
        '22/23 Home Goals Against 11-15': 0,
        '22/23 Home Goals Conceded Against 11-15': 0,
        '22/23 Home Games Against 16-20': 0,
        '22/23 Home Goals Against 16-20': 0,
        '22/23 Home Goals Conceded Against 16-20': 0,
        '22/23 Away Games Against 1-5': 0,
        '22/23 Away Goals Against 1-5': 0,
        '22/23 Away Goals Conceded Against 1-5': 0,
        '22/23 Away Games Against 6-10': 0,
        '22/23 Away Goals Against 6-10': 0,
        '22/23 Away Goals Conceded Against 6-10': 0,
        '22/23 Away Goals Against 11-15': 0,
        '22/23 Away Games Against 11-15': 0,
        '22/23 Away Goals Conceded Against 11-15': 0,
        '22/23 Away Games Against 16-20': 0,
        '22/23 Away Goals Against 16-20': 0,
        '22/23 Away Goals Conceded Against 16-20': 0,
        '23/24 Home Games Against 1-5': 0,
        '23/24 Home Goals Against 1-5': 0,
        '23/24 Home Goals Conceded Against 1-5': 0,
        '23/24 Home Games Against 6-10': 0,
        '23/24 Home Goals Against 6-10': 0,
        '23/24 Home Goals Conceded Against 6-10': 0,
        '23/24 Home Games Against 11-15': 0,
        '23/24 Home Goals Against 11-15': 0,
        '23/24 Home Goals Conceded Against 11-15': 0,
        '23/24 Home Games Against 16-20': 0,
        '23/24 Home Goals Against 16-20': 0,
        '23/24 Home Goals Conceded Against 16-20': 0,
        '23/24 Away Games Against 1-5': 0,
        '23/24 Away Goals Against 1-5': 0,
        '23/24 Away Goals Conceded Against 1-5': 0,
        '23/24 Away Games Against 6-10': 0,
        '23/24 Away Goals Against 6-10': 0,
        '23/24 Away Goals Conceded Against 6-10': 0,
        '23/24 Away Goals Against 11-15': 0,
        '23/24 Away Games Against 11-15': 0,
        '23/24 Away Goals Conceded Against 11-15': 0,
        '23/24 Away Games Against 16-20': 0,
        '23/24 Away Goals Against 16-20': 0,
        '23/24 Away Goals Conceded Against 16-20': 0,}
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
            '22/23 Home Games Played for Current Team': 0,
            '22/23 Away Games Played for Current Team': 0,
            '22/23 Home Goals for Current Team': 0,
            '22/23 Away Goals for Current Team': 0,
            '22/23 Home Assists for Current Team': 0,
            '22/23 Away Assists for Current Team': 0,
            '22/23 Goalkeeper Saves for Current Team': 0,
            '23/24 Home Games Played for Current Team': 0,
            '23/24 Away Games Played for Current Team': 0,
            '23/24 Home Goals for Current Team': 0,
            '23/24 Away Goals for Current Team': 0,
            '23/24 Home Assists for Current Team': 0,
            '23/24 Away Assists for Current Team': 0,
            '23/24 Goalkeeper Saves for Current Team': 0,
            'BPS for Current Team': 0,
            '22/23 BPS for Current Team': 0,
            '23/24 BPS for Current Team': 0,
            'Home Games Against 1-5': 0,
            'Home Goals Against 1-5': 0,
            'Home Assists Against 1-5': 0,
            'Home Games Against 6-10': 0,
            'Home Goals Against 6-10': 0,
            'Home Assists Against 6-10': 0,
            'Home Games Against 11-15': 0,
            'Home Goals Against 11-15': 0,
            'Home Assists Against 11-15': 0,
            'Home Games Against 16-20': 0,
            'Home Goals Against 16-20': 0,
            'Home Assists Against 16-20': 0,
            'Away Games Against 1-5': 0,
            'Away Goals Against 1-5': 0,
            'Away Assists Against 1-5': 0,
            'Away Games Against 6-10': 0,
            'Away Goals Against 6-10': 0,
            'Away Assists Against 6-10': 0,
            'Away Games Against 11-15': 0,
            'Away Goals Against 11-15': 0,
            'Away Assists Against 11-15': 0,
            'Away Games Against 16-20': 0,
            'Away Goals Against 16-20': 0,
            'Away Assists Against 16-20': 0,
            '22/23 Home Games Against 1-5': 0,
            '22/23 Home Goals Against 1-5': 0,
            '22/23 Home Assists Against 1-5': 0,
            '22/23 Home Games Against 6-10': 0,
            '22/23 Home Goals Against 6-10': 0,
            '22/23 Home Assists Against 6-10': 0,
            '22/23 Home Games Against 11-15': 0,
            '22/23 Home Goals Against 11-15': 0,
            '22/23 Home Assists Against 11-15': 0,
            '22/23 Home Games Against 16-20': 0,
            '22/23 Home Goals Against 16-20': 0,
            '22/23 Home Assists Against 16-20': 0,
            '22/23 Away Games Against 1-5': 0,
            '22/23 Away Goals Against 1-5': 0,
            '22/23 Away Assists Against 1-5': 0,
            '22/23 Away Games Against 6-10': 0,
            '22/23 Away Goals Against 6-10': 0,
            '22/23 Away Assists Against 6-10': 0,
            '22/23 Away Games Against 11-15': 0,
            '22/23 Away Goals Against 11-15': 0,
            '22/23 Away Assists Against 11-15': 0,
            '22/23 Away Games Against 16-20': 0,
            '22/23 Away Goals Against 16-20': 0,
            '22/23 Away Assists Against 16-20': 0,
            '23/24 Home Games Against 1-5': 0,
            '23/24 Home Goals Against 1-5': 0,
            '23/24 Home Assists Against 1-5': 0,
            '23/24 Home Games Against 6-10': 0,
            '23/24 Home Goals Against 6-10': 0,
            '23/24 Home Assists Against 6-10': 0,
            '23/24 Home Games Against 11-15': 0,
            '23/24 Home Goals Against 11-15': 0,
            '23/24 Home Assists Against 11-15': 0,
            '23/24 Home Games Against 16-20': 0,
            '23/24 Home Goals Against 16-20': 0,
            '23/24 Home Assists Against 16-20': 0,
            '23/24 Away Games Against 1-5': 0,
            '23/24 Away Goals Against 1-5': 0,
            '23/24 Away Assists Against 1-5': 0,
            '23/24 Away Games Against 6-10': 0,
            '23/24 Away Goals Against 6-10': 0,
            '23/24 Away Assists Against 6-10': 0,
            '23/24 Away Games Against 11-15': 0,
            '23/24 Away Goals Against 11-15': 0,
            '23/24 Away Assists Against 11-15': 0,
            '23/24 Away Games Against 16-20': 0,
            '23/24 Away Goals Against 16-20': 0,
            '23/24 Away Assists Against 16-20': 0,}
    return player_template

TEAM_NAMES_ODDSCHECKER = {
    "Nott'm Forest": "Nottingham Forest",
    "Wolves": "Wolverhampton",
    "Spurs": "Tottenham",
    }

season_23_24_team_positions = {
        'Man City': 1,
        'Arsenal': 2,
        'Man Utd': 8,
        'Newcastle': 7,
        'Liverpool': 3,
        'Brighton': 11,
        'Aston Villa': 4,
        'Tottenham': 5,
        'Brentford': 16,
        'Fulham': 14,
        'Crystal Palace': 10,
        'Chelsea': 6,
        'Wolverhampton': 15,
        'West Ham': 9,
        'Bournemouth': 13,
        'Nottingham Forest': 17,
        'Everton': 12,
        'Sheffield Utd': 20,
        'Burnley': 19,
        'Luton': 18
        }

fixtures_url = "https://raw.githubusercontent.com/vaastav/Fantasy-Premier-League//master/data/2023-24/fixtures.csv"
teams_url = "https://raw.githubusercontent.com/vaastav/Fantasy-Premier-League//master/data/2023-24/teams.csv"
fixtures_df = pd.read_csv(fixtures_url)
teams_df = pd.read_csv(teams_url)

api_url = "https://fantasy.premierleague.com/api/bootstrap-static/"
api_response = requests.get(api_url)
if api_response.status_code != 200:
    raise Exception(f"Failed to fetch teams: {api_response.status_code}")
data = api_response.json()
# Get team data from FPL API
teams_data = data['teams']
# Get player data from FPL API
players_data = data['elements']
# A dictionary containing the team name corresponding to each team id
team_id_to_name = {int(team['id']): TEAM_NAMES_ODDSCHECKER.get(team['name'], team['name']) for team in teams_data}
player_id_to_name = {int(player['id']): player["first_name"] + " " + player['second_name'] for player in players_data}

team_id_to_name_23_24 = {int(team['id']): TEAM_NAMES_ODDSCHECKER.get(team['name'], team['name']) for team in teams_df.to_dict('records')}
teams_dict = {}

for col in fixtures_df.columns:
    if 'stats' in col:
        fixtures_df[col] = fixtures_df[col].apply(lambda x: ast.literal_eval(x) if isinstance(x, str) else x)

fixtures_23_24 = fixtures_df.to_dict('records')

print(teams_dict)