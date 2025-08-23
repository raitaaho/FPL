import requests
import pandas as pd
import plotly.express as px
import webbrowser
import ast
import sys
from collections import defaultdict
import streamlit as st

def get_team_template():
    team_template = {                                                         
            'ELO': 1000,
            'Home ELO': 1000,
            'Away ELO': 1000,
            'Home Games': 0,
            'Away Games': 0,
            'Home Goals': 0,
            'Away Goals': 0,
            'Goals Conceded Home': 0,
            'Goals Conceded Away': 0,
            }
    return team_template

TEAM_NAMES_ODDSCHECKER = {
    "Nott'm Forest": "Nottingham Forest",
    "Wolves": "Wolverhampton",
    "Spurs": "Tottenham",
    }

# --- Error handling for CSV loading ---

def load_previous_seasons_csv_data(teams_api_data, finished_fixtures, team_id_to_name_25_26):
    try:
        fixtures_24_25_df = pd.read_csv("https://raw.githubusercontent.com/vaastav/Fantasy-Premier-League/master/data/2024-25/fixtures.csv")
        teams_24_25_df = pd.read_csv("https://raw.githubusercontent.com/vaastav/Fantasy-Premier-League/master/data/2024-25/teams.csv")

        # Convert DataFrames to lists of dictionaries
        fixtures_24_25 = fixtures_24_25_df.to_dict(orient='records')
        teams_24_25 = teams_24_25_df.to_dict(orient='records')
    except Exception as e:
        print(f"Error loading CSV data: {e}", file=sys.stderr)
        fixtures_22_23 = []
        fixtures_23_24 = []
        fixtures_24_25 = []
        teams_22_23 = []
        teams_23_24 = []
        teams_24_25 = []

    for row in fixtures_24_25:
        # Convert the 'stats' field from a string to a Python object (list of dictionaries)
        if 'stats' in row:
            row['stats'] = ast.literal_eval(row['stats'])

    team_id_to_name_24_25 = {int(team['id']): team['name'] for team in teams_24_25}

    teams_dict = {}

    for team in teams_api_data:
        team_name = team['name'] if team['name'] is not None else ""
        teams_dict[team_name] = get_team_template()

    for fixture in fixtures_24_25:
        home_team_id = int(fixture['team_h'])
        away_team_id = int(fixture['team_a'])
        if home_team_id is None or away_team_id is None:
            continue
        home_team_name = team_id_to_name_24_25.get(home_team_id, "Unknown")
        away_team_name = team_id_to_name_24_25.get(away_team_id, "Unknown")
        teams_dict[home_team_name] = teams_dict.get(home_team_name, get_team_template())
        teams_dict[away_team_name] = teams_dict.get(away_team_name, get_team_template())

        home_goals = int(fixture['team_h_score'])
        away_goals = int(fixture['team_a_score'])

        home_overall_elo = teams_dict[home_team_name]['ELO']
        away_overall_elo = teams_dict[away_team_name]['ELO']

        home_elo = teams_dict[home_team_name]['Home ELO']
        away_elo = teams_dict[away_team_name]['Away ELO']

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

        home_elo_change = (actual_home - expected_home)
        away_elo_change = (actual_away - expected_away)

        home_overall_elo_change = (actual_home - expected_home_overall)
        away_overall_elo_change = (actual_away - expected_away_overall)

        teams_dict[home_team_name]['Home Games'] += 1
        teams_dict[away_team_name]['Away Games'] += 1

        teams_dict[home_team_name]['Home ELO'] += 20 * home_elo_change
        teams_dict[away_team_name]['Away ELO'] += 20 * away_elo_change

        teams_dict[home_team_name]['ELO'] += 20 * home_overall_elo_change
        teams_dict[away_team_name]['ELO'] += 20 * away_overall_elo_change

        teams_dict[home_team_name]['Home Goals'] += home_goals
        teams_dict[away_team_name]['Away Goals'] += away_goals

        teams_dict[home_team_name]['Goals Conceded Home'] += away_goals
        teams_dict[away_team_name]['Goals Conceded Away'] += home_goals

    for fixture in finished_fixtures:
        home_team_id = int(fixture['team_h'])
        away_team_id = int(fixture['team_a'])
        if home_team_id is None or away_team_id is None:
            continue
        home_team_name = team_id_to_name_25_26.get(home_team_id, "Unknown")
        away_team_name = team_id_to_name_25_26.get(away_team_id, "Unknown")
        teams_dict[home_team_name] = teams_dict.get(home_team_name, get_team_template())
        teams_dict[away_team_name] = teams_dict.get(away_team_name, get_team_template())

        home_goals = int(fixture['team_h_score'])
        away_goals = int(fixture['team_a_score'])

        home_overall_elo = teams_dict[home_team_name]['ELO']
        away_overall_elo = teams_dict[away_team_name]['ELO']

        home_elo = teams_dict[home_team_name]['Home ELO']
        away_elo = teams_dict[away_team_name]['Away ELO']

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

        home_elo_change = (actual_home - expected_home)
        away_elo_change = (actual_away - expected_away)

        home_overall_elo_change = (actual_home - expected_home_overall)
        away_overall_elo_change = (actual_away - expected_away_overall)

        teams_dict[home_team_name]['Home Games'] += 1
        teams_dict[away_team_name]['Away Games'] += 1

        teams_dict[home_team_name]['Home ELO'] += 20 * home_elo_change
        teams_dict[away_team_name]['Away ELO'] += 20 * away_elo_change

        teams_dict[home_team_name]['ELO'] += 20 * home_overall_elo_change
        teams_dict[away_team_name]['ELO'] += 20 * away_overall_elo_change

        teams_dict[home_team_name]['Home Goals'] += home_goals
        teams_dict[away_team_name]['Away Goals'] += away_goals

        teams_dict[home_team_name]['Goals Conceded Home'] += away_goals
        teams_dict[away_team_name]['Goals Conceded Away'] += home_goals

    for team in teams_dict:
        teams_dict[team]['Goals per Home Game'] = float(teams_dict[team]['Home Goals']/teams_dict[team]['Home Games']) if teams_dict[team]['Home Games'] > 2 else 0.95
        teams_dict[team]['Goals per Away Game'] = float(teams_dict[team]['Away Goals']/teams_dict[team]['Away Games']) if teams_dict[team]['Away Games'] > 2 else 0.60
        teams_dict[team]['Goals Conceded per Home Game'] = float(teams_dict[team]['Goals Conceded Home']/teams_dict[team]['Home Games']) if teams_dict[team]['Home Games'] > 2 else 2.05
        teams_dict[team]['Goals Conceded per Away Game'] = float(teams_dict[team]['Goals Conceded Away']/teams_dict[team]['Away Games']) if teams_dict[team]['Away Games'] > 2 else 2.15

    return teams_dict

def value_to_strength(value, min_val, max_val, type):
    interval_len = (max_val - min_val) / 4

    if type == 'att':
        if value <= min_val + interval_len:
            return 2
        elif min_val + interval_len <= value <= min_val + 2 * interval_len:
            return 3
        elif min_val + 2 * interval_len <= value <= min_val + 3 * interval_len:
            return 4
        elif max_val - interval_len <= value <= max_val:
            return 5
        
    else:
        if value <= min_val + interval_len:
            return 5
        elif min_val + interval_len <= value <= min_val + 2 * interval_len:
            return 4
        elif min_val + 2 * interval_len <= value <= min_val + 3 * interval_len:
            return 3
        elif max_val - interval_len <= value <= max_val:
            return 2
    
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

def fetch_data_from_fpl_api():
    # Fetch data from the FPL API
    teams_api = requests.get("https://fantasy.premierleague.com/api/bootstrap-static/").json()
    teams_api_data = teams_api['teams']
    fixtures_data = requests.get("https://fantasy.premierleague.com/api/fixtures/").json()
    finished_fixtures = [fixture for fixture in fixtures_data if (fixture['finished_provisional'] == True)]
    fixtures = get_all_fixtures()
    next_gws = get_next_gws(fixtures, extra_gw = 'False')
    team_id_to_name_25_26 = {int(team['id']): team['name'] for team in teams_api_data}

    return teams_api_data, fixtures_data, finished_fixtures, next_gws, team_id_to_name_25_26

def calc_team_strengths(teams_data, fixtures_data, next_gws, team_id_to_name_25_26):
    """
    Calculate team strengths based on goals scored and conceded per game.
    
    Args:
        teams_data (dict): Dictionary containing team data.
        finished_fixtures (list): List of finished fixtures.

    Returns:
        dict: Dictionary containing team strengths.
    """

    current_season_team_data = {}

    for id, name in team_id_to_name_25_26.items():
        if teams_data.get(name, "Unknown") != "Unknown":
            current_season_team_data[name] = {}
            current_season_team_data[name].update({'Goals per Home Game': teams_data[name]['Goals per Home Game'], 'Goals per Away Game': teams_data[name]['Goals per Away Game'], 'Goals Conceded per Home Game': teams_data[name]['Goals Conceded per Home Game'], 'Goals Conceded per Away Game': teams_data[name]['Goals Conceded per Away Game']})

    keys = [
        'Goals per Home Game',
        'Goals per Away Game',
        'Goals Conceded per Home Game',
        'Goals Conceded per Away Game'
        ]

    results = {}
    team_strengths = {}
    for team in current_season_team_data:
        team_strengths[team] = {}

    for key in keys:
        min_team = min(current_season_team_data, key=lambda team: current_season_team_data[team][key])
        max_team = max(current_season_team_data, key=lambda team: current_season_team_data[team][key])

        min_val = current_season_team_data[min_team][key]
        max_val = current_season_team_data[max_team][key]
        
        results[key] = {
            'min': (min_team, current_season_team_data[min_team][key]),
            'max': (max_team, current_season_team_data[max_team][key]),
            'interval': (max_val - min_val) / 4
        }

    max_goals = max(results['Goals per Home Game']['max'][1], results['Goals per Away Game']['max'][1])
    min_goals = min(results['Goals per Home Game']['min'][1], results['Goals per Away Game']['min'][1])

    max_goals_conceded = max(results['Goals Conceded per Home Game']['max'][1], results['Goals Conceded per Away Game']['max'][1])
    min_goals_conceded = min(results['Goals Conceded per Home Game']['min'][1], results['Goals Conceded per Away Game']['min'][1])

    for team in current_season_team_data:
        home_att_strength = value_to_strength(current_season_team_data[team]['Goals per Home Game'], min_goals, max_goals, type='att')
        away_att_strength = value_to_strength(current_season_team_data[team]['Goals per Away Game'], min_goals, max_goals, type='att')

        home_def_strength = value_to_strength(current_season_team_data[team]['Goals Conceded per Home Game'], min_goals_conceded, max_goals_conceded, type='def')
        away_def_strength = value_to_strength(current_season_team_data[team]['Goals Conceded per Away Game'], min_goals_conceded, max_goals_conceded, type='def')

        team_strengths[team]['Home Attack Strength'] = home_att_strength
        team_strengths[team]['Away Attack Strength'] = away_att_strength

        team_strengths[team]['Home Defense Strength'] = home_def_strength
        team_strengths[team]['Away Defense Strength'] = away_def_strength

    # Calculate combined FDRs for attack and defense
    combined_fdr = {team_id: {'attack_next_3': 0, 'attack_next_5': 0, 'defense_next_3': 0, 'defense_next_5': 0} for team_id in team_id_to_name_25_26.keys()}
    all_gws_fdr = {team_id: [] for team_id in team_id_to_name_25_26.keys()}
    for team_id in team_id_to_name_25_26.keys():
        team_fixtures = [f for f in fixtures_data if f['team_h'] == team_id or f['team_a'] == team_id]
        team_fixtures = sorted(team_fixtures, key=lambda x: x['event'])[next_gws[0] - 1:]
        
        for i, fixture in enumerate(team_fixtures):
            if fixture['team_h'] == team_id:
                opponent_id = fixture['team_a']
                opponent_name = team_id_to_name_25_26.get(opponent_id, "Unknown")

                attack_fdr = team_strengths[opponent_name]['Away Defense Strength']
                defense_fdr = team_strengths[opponent_name]['Away Attack Strength']

                all_gws_fdr[team_id].append({
                    'Gameweek': fixture['event'],
                    'Opponent': opponent_name,
                    'Attack FDR': attack_fdr,
                    'Defense FDR': defense_fdr,
                    'Venue': 'Home'
                })
                
            else:
                opponent_id = fixture['team_h']
                opponent_name = team_id_to_name_25_26.get(opponent_id, "Unknown")

                attack_fdr = team_strengths[opponent_name]['Home Defense Strength']
                defense_fdr = team_strengths[opponent_name]['Home Attack Strength']

                all_gws_fdr[team_id].append({
                    'Gameweek': fixture['event'],
                    'Opponent': opponent_name,
                    'Attack FDR': attack_fdr,
                    'Defense FDR': defense_fdr,
                    'Venue': 'Away'
                })

            if i < 3:
                combined_fdr[team_id]['attack_next_3'] += attack_fdr
                combined_fdr[team_id]['defense_next_3'] += defense_fdr
            if i < 5:
                combined_fdr[team_id]['attack_next_5'] += attack_fdr
                combined_fdr[team_id]['defense_next_5'] += defense_fdr

    return combined_fdr, all_gws_fdr

def visualize_data(combined_fdr, team_id_to_name_25_26):
    # Prepare data for visualization
    fdr_df = pd.DataFrame([
        {
            'Team': team_id_to_name_25_26[team_id],
            'Attack - Next 3': data['attack_next_3'],
            'Attack - Next 5': data['attack_next_5'],
            'Defense - Next 3': data['defense_next_3'],
            'Defense - Next 5': data['defense_next_5']

        }
        for team_id, data in combined_fdr.items()
    ])
    fdr_melted = fdr_df.melt(id_vars='Team', value_vars=['Attack - Next 3', 'Attack - Next 5', 'Defense - Next 3', 'Defense - Next 5'],
                            var_name='Perspective & Fixture Range', value_name='Combined FDR')

    # Plot
    fig = px.bar(fdr_melted, x='Team', y='Combined FDR', color='Perspective & Fixture Range',
                barmode='group', title='Combined FDR for Next 3 and Next 5 Fixtures (Attack & Defense)')

    fig.update_layout(xaxis_tickangle=-45)

    st.plotly_chart(fig, use_container_width=True)
    st.download_button(
        label="Download FDR Chart as HTML",
        data=fig.to_html(),
        file_name="fdr_plot.html",
        mime="text/html"
    )

st.set_page_config(page_title="Oddschecker.com Odds Scraper", page_icon="📈")

st.markdown("# Fixture Difficulty Ratings (FDR) Visualization")
st.write(
    """This app fetches and visualizes the Fixture Difficulty Ratings (FDR) for Premier League teams based on their performance in the current season and previous seasons."""
)

if st.button("Fetch and Visualize FDR Data"):
    teams_api_data, fixtures_data, finished_fixtures, next_gws, team_id_to_name_25_26 = fetch_data_from_fpl_api()
    teams_data = load_previous_seasons_csv_data(teams_api_data, finished_fixtures, team_id_to_name_25_26)
    combined_fdr, all_gws_fdr = calc_team_strengths(teams_data, fixtures_data, next_gws, team_id_to_name_25_26)
    visualize_data(combined_fdr, team_id_to_name_25_26)