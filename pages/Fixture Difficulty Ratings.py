import requests
import pandas as pd
import plotly.express as px
import plotly.graph_objects as go
import ast
import sys
from collections import defaultdict
import streamlit as st
from itertools import combinations

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
            'Goals Conceded Away': 0
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
        fixtures_24_25 = []
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
        teams_dict[team]['Goals per Home Game'] = float(teams_dict[team]['Home Goals']/teams_dict[team]['Home Games']) if teams_dict[team]['Home Games'] > 3 else None
        teams_dict[team]['Goals per Away Game'] = float(teams_dict[team]['Away Goals']/teams_dict[team]['Away Games']) if teams_dict[team]['Away Games'] > 3 else None
        teams_dict[team]['Goals Conceded per Home Game'] = float(teams_dict[team]['Goals Conceded Home']/teams_dict[team]['Home Games']) if teams_dict[team]['Home Games'] > 3 else None
        teams_dict[team]['Goals Conceded per Away Game'] = float(teams_dict[team]['Goals Conceded Away']/teams_dict[team]['Away Games']) if teams_dict[team]['Away Games'] > 3 else None

    return teams_dict

def value_to_strength(value, min_val, max_val, type):
    if value is None:
        return 2  # Default strength if no data available
    interval_len = (max_val - min_val) / 5

    if type == 'att':
        if value <= (min_val - 0.25) + interval_len:
            return 2
        elif max_val - interval_len <= value <= max_val:
            return 5
        elif max_val - 2 * interval_len <= value <= max_val - interval_len:
            return 4   
        else:
            return 3
        
    else:
        if value <= min_val + interval_len:
            return 5
        elif (max_val + 0.25) - interval_len <= value <= (max_val + 0.25):
            return 2
        elif min_val + interval_len <= value <= min_val + 2 * interval_len:
            return 4
        else:
            return 3
    
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
    team_id_to_short_name_25_26 = {int(team['id']): team['short_name'] for team in teams_api_data}

    return teams_api_data, fixtures_data, finished_fixtures, next_gws, team_id_to_name_25_26, team_id_to_short_name_25_26

def calc_team_strengths(teams_data, fixtures_data, next_gws, team_id_to_name_25_26, team_id_to_short_name_25_26):
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
        min_team = min(current_season_team_data, key=lambda team: current_season_team_data[team][key] if current_season_team_data[team][key] is not None else float('inf'))
        max_team = max(current_season_team_data, key=lambda team: current_season_team_data[team][key] if current_season_team_data[team][key] is not None else float('-inf'))

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
    combined_fdr = {team_id: {'attack_next_3': 0, 'attack_next_5': 0, 'defense_next_3': 0, 'defense_next_5': 0} for team_id in team_id_to_short_name_25_26.keys()}
    all_gws_fdr = {team_id: [] for team_id in team_id_to_short_name_25_26.keys()}
    for team_id in team_id_to_short_name_25_26.keys():
        team_fixtures = [f for f in fixtures_data if f['team_h'] == team_id or f['team_a'] == team_id]
        team_fixtures = sorted(team_fixtures, key=lambda x: x['event'])[next_gws[0] - 1:]
        
        for i, fixture in enumerate(team_fixtures):
            if fixture['team_h'] == team_id:
                opponent_id = fixture['team_a']
                opponent_name = team_id_to_name_25_26.get(opponent_id, "Unknown")
                opponent_short_name = team_id_to_short_name_25_26.get(opponent_id, "Unknown")

                attack_fdr = team_strengths[opponent_name]['Away Defense Strength']
                defense_fdr = team_strengths[opponent_name]['Away Attack Strength']

                all_gws_fdr[team_id].append({
                    'Gameweek': fixture['event'],
                    'Opponent': opponent_short_name,
                    'Attack FDR': attack_fdr,
                    'Defense FDR': defense_fdr,
                    'Venue': 'Home'
                })
                
            else:
                opponent_id = fixture['team_h']
                opponent_name = team_id_to_name_25_26.get(opponent_id, "Unknown")
                opponent_short_name = team_id_to_short_name_25_26.get(opponent_id, "Unknown")

                attack_fdr = team_strengths[opponent_name]['Home Defense Strength']
                defense_fdr = team_strengths[opponent_name]['Home Attack Strength']

                all_gws_fdr[team_id].append({
                    'Gameweek': fixture['event'],
                    'Opponent': opponent_short_name,
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

def visualize_fixture_ticker(all_gws_fdr, team_id_to_name_25_26, team_id_to_short_name_25_26):
    for team_id, fixtures in all_gws_fdr.items():
        team_name = team_id_to_name_25_26[team_id]
        st.subheader(f"{team_name} Fixtures")

        # --- Attack FDR ---
        gw_labels = [f"GW{f['Gameweek']}" for f in fixtures]
        opp_labels = [f"{f['Opponent']} ({f['Venue'][0]})" for f in fixtures]
        attack_fdr_values = [f['Attack FDR'] for f in fixtures]
        color_map = {2: "#00C853", 3: "#E0E0E0", 4: "#FFFF00", 5: "#D50000"}
        attack_colors = [color_map.get(val, "#E0E0E0") for val in attack_fdr_values]

        fig_attack = go.Figure(go.Bar(
            x=gw_labels,
            y=[4]*len(gw_labels),
            text=[f"{opp}<br>{fdr}" for opp, fdr in zip(opp_labels, attack_fdr_values)],
            marker_color=attack_colors,
            width=[0.5]*len(gw_labels),
            textposition="inside",
            hovertext=[f"{opp} - Attack FDR: {fdr}" for opp, fdr in zip(opp_labels, attack_fdr_values)],
            hoverinfo="text",
            showlegend=False
        ))

        fig_attack.update_layout(
            xaxis=dict(title="", tickvals=gw_labels, ticktext=gw_labels),
            yaxis=dict(visible=False, range=[0, 4.5]),
            barmode='group',
            height=120,
            margin=dict(l=10, r=10, t=60, b=10)
        )
        st.plotly_chart(fig_attack, use_container_width=True)

        # --- Defense FDR ---
        defense_fdr_values = [f['Defense FDR'] for f in fixtures]
        defense_colors = [color_map.get(val, "#E0E0E0") for val in defense_fdr_values]

        fig_defense = go.Figure(go.Bar(
            x=gw_labels,
            y=[4]*len(gw_labels),
            text=[f"{opp}<br>{fdr}" for opp, fdr in zip(opp_labels, defense_fdr_values)],
            marker_color=defense_colors,
            width=[0.5]*len(gw_labels),
            textposition="inside",
            hovertext=[f"{opp} - Defense FDR: {fdr}" for opp, fdr in zip(opp_labels, defense_fdr_values)],
            hoverinfo="text",
            showlegend=False
        ))

        fig_defense.update_layout(
            xaxis=dict(title="", tickvals=gw_labels, ticktext=gw_labels),
            yaxis=dict(visible=False, range=[0, 4.5]),
            barmode='group',
            height=120,
            margin=dict(l=10, r=10, t=60, b=10)
        )
        st.plotly_chart(fig_defense, use_container_width=True)

def create_fixture_ticker_df(all_gws_fdr, team_id_to_short_name_25_26):
    all_gws_fdr = all_gws_fdr
    # Create a DataFrame: rows=teams, columns=GW, values=opponent short name (capitalized for home, lowercase for away)
    data = {}
    for team_id, fixtures in all_gws_fdr.items():
        team_row = {}
        for fixture in fixtures:
            gw = f"GW {fixture['Gameweek']}"
            venue = fixture['Venue'][0]  # 'H' or 'A'
            opp = fixture['Opponent']
            if venue == 'H':
                cell_value = opp.upper()
            else:
                cell_value = opp.lower()
            team_row[gw] = cell_value
        data[team_id_to_short_name_25_26[team_id]] = team_row
    df = pd.DataFrame.from_dict(data, orient='index')
    return df

def color_fdr(val, fdr):
    # val is like "liv (A)|5"
    if pd.isna(val):
        return ""
    color_map = {2: "#00C853", 3: "#E0E0E0", 4: "#FFFF00", 5: "#D50000"}
    color = color_map.get(fdr, "#E0E0E0")
    opp = val.split('|')[0]
    return f'background-color: {color}; color: black'

def get_best_rotation(all_gws_fdr: dict, gws: int):
    best_attack_pair = "Unknown"
    best_defense_pair = "Unknown"
    min_attack_sum = float('inf')
    min_defense_sum = float('inf')

    team_ids = list(all_gws_fdr.keys())

    for team1, team2 in combinations(team_ids, 2):
        attack_sum = 0
        defense_sum = 0

        fixtures1 = all_gws_fdr[team1][:gws]
        fixtures2 = all_gws_fdr[team2][:gws]

        for gw in range(gws):
            attack_sum += min(fixtures1[gw]['Attack FDR'], fixtures2[gw]['Attack FDR'])
            defense_sum += min(fixtures1[gw]['Defense FDR'], fixtures2[gw]['Defense FDR'])

        if attack_sum < min_attack_sum:
            min_attack_sum = attack_sum
            best_attack_pair = (team1, team2)

        if defense_sum < min_defense_sum:
            min_defense_sum = defense_sum
            best_defense_pair = (team1, team2)

    return {
        'best_attack_rotation': best_attack_pair,
        'attack_fdr_sum': min_attack_sum,
        'best_defense_rotation': best_defense_pair,
        'defense_fdr_sum': min_defense_sum
    }

def get_best_rotation_three_teams(all_gws_fdr: dict, gws: int):
    best_attack_triplet = "Unknown"
    best_defense_triplet = "Unknown"
    min_attack_sum = float('inf')
    min_defense_sum = float('inf')

    team_ids = list(all_gws_fdr.keys())

    for team1, team2, team3 in combinations(team_ids, 3):
        attack_sum = 0
        defense_sum = 0

        fixtures1 = all_gws_fdr[team1][:gws]
        fixtures2 = all_gws_fdr[team2][:gws]
        fixtures3 = all_gws_fdr[team3][:gws]

        for gw in range(gws):
            attack_sum += min(fixtures1[gw]['Attack FDR'], fixtures2[gw]['Attack FDR'], fixtures3[gw]['Attack FDR'])
            defense_sum += min(fixtures1[gw]['Defense FDR'], fixtures2[gw]['Defense FDR'], fixtures3[gw]['Defense FDR'])

        if attack_sum < min_attack_sum:
            min_attack_sum = attack_sum
            best_attack_triplet = (team1, team2, team3)

        if defense_sum < min_defense_sum:
            min_defense_sum = defense_sum
            best_defense_triplet = (team1, team2, team3)

    return {
        'best_attack_rotation': best_attack_triplet,
        'attack_fdr_sum': min_attack_sum,
        'best_defense_rotation': best_defense_triplet,
        'defense_fdr_sum': min_defense_sum
    }

def get_best_partner_for_two_teams(all_gws_fdr: dict, gws: int, team1_name: str, team2_name: str, team_id_to_name: dict):
    name_to_team_id = {v: k for k, v in team_id_to_name.items()}
    team1_id = name_to_team_id.get(team1_name)
    team2_id = name_to_team_id.get(team2_name)

    if team1_id is None or team2_id is None:
        return f"One or both team names not found: '{team1_name}', '{team2_name}'"

    min_attack_sum = float('inf')
    min_defense_sum = float('inf')
    best_attack_partner = "Unknown"
    best_defense_partner = "Unknown"

    for other_team_id in all_gws_fdr:
        if other_team_id in [team1_id, team2_id]:
            continue

        fixtures1 = all_gws_fdr[team1_id][:gws]
        fixtures2 = all_gws_fdr[team2_id][:gws]
        fixtures3 = all_gws_fdr[other_team_id][:gws]

        attack_sum = 0
        defense_sum = 0

        for gw in range(gws):
            attack_sum += min(fixtures1[gw]['Attack FDR'], fixtures2[gw]['Attack FDR'], fixtures3[gw]['Attack FDR'])
            defense_sum += min(fixtures1[gw]['Defense FDR'], fixtures2[gw]['Defense FDR'], fixtures3[gw]['Defense FDR'])

        if attack_sum < min_attack_sum:
            min_attack_sum = attack_sum
            best_attack_partner = other_team_id

        if defense_sum < min_defense_sum:
            min_defense_sum = defense_sum
            best_defense_partner = other_team_id

    return {
        'team1': team1_name,
        'team2': team2_name,
        'best_attack_partner': team_id_to_name[best_attack_partner],
        'attack_fdr_sum': min_attack_sum,
        'best_defense_partner': team_id_to_name[best_defense_partner],
        'defense_fdr_sum': min_defense_sum
    }

def get_best_partner_for_one_team(all_gws_fdr: dict, gws: int, team1_name: str, team_id_to_name: dict):
    name_to_team_id = {v: k for k, v in team_id_to_name.items()}
    team1_id = name_to_team_id.get(team1_name)

    if team1_id is None:
        return f"Team name not found: '{team1_name}'"

    min_attack_sum = float('inf')
    min_defense_sum = float('inf')
    best_attack_partner = "Unknown"
    best_defense_partner = "Unknown"
    for other_team_id in all_gws_fdr:
        if other_team_id == team1_id:
            continue

        fixtures1 = all_gws_fdr[team1_id][:gws]
        fixtures2 = all_gws_fdr[other_team_id][:gws]

        attack_sum = 0
        defense_sum = 0

        for gw in range(gws):
            attack_sum += min(fixtures1[gw]['Attack FDR'], fixtures2[gw]['Attack FDR'])
            defense_sum += min(fixtures1[gw]['Defense FDR'], fixtures2[gw]['Defense FDR'])

        if attack_sum < min_attack_sum:
            min_attack_sum = attack_sum
            best_attack_partner = other_team_id

        if defense_sum < min_defense_sum:
            min_defense_sum = defense_sum
            best_defense_partner = other_team_id

    return {
        'team1': team1_name,
        'best_attack_partner': team_id_to_name[best_attack_partner],
        'attack_fdr_sum': min_attack_sum,
        'best_defense_partner': team_id_to_name[best_defense_partner],
        'defense_fdr_sum': min_defense_sum
    }

# --- Initialize session state ---
if "team_id_to_name" not in st.session_state:
    st.session_state.team_id_to_name = {}

if "team_id_to_short_name" not in st.session_state:
    st.session_state.team_id_to_short_name = {}

if "all_gws_fdr" not in st.session_state:
    st.session_state.all_gws_fdr = {}

if "styled_attack_df" not in st.session_state:
    st.session_state.styled_attack_df = None

if "styled_defense_df" not in st.session_state:
    st.session_state.styled_defense_df = None

if "team1_input" not in st.session_state:
    st.session_state.team1_input = None

if "team2_input" not in st.session_state:
    st.session_state.team2_input = None

if "enable_three_team_rotation" not in st.session_state:
    st.session_state.enable_three_team_rotation = None

if "all_gws_fdr" not in st.session_state:
    st.session_state.all_gws_fdr = {}

if "rotation_result" not in st.session_state:
    st.session_state.rotation_result = {}

# --- Page Config ---
st.set_page_config(page_title="FPL Fixture Difficulty Ratings", page_icon="📈")

st.title("📊 Fixture Difficulty Ratings (FDR) Visualization")
st.write("This app fetches and visualizes the Fixture Difficulty Ratings (FDR) for Premier League teams based on their performance.")

# --- Gameweek Input ---
num_gws = st.number_input("How many gameweeks to show?", min_value=1, max_value=10, value=5, step=1)

# --- Fetch and Visualize Button ---
if st.button("Fetch and Visualize FDR Data"):
    teams_api_data, fixtures_data, finished_fixtures, next_gws, team_id_to_name, team_id_to_short_name = fetch_data_from_fpl_api()
    teams_data = load_previous_seasons_csv_data(teams_api_data, finished_fixtures, team_id_to_name)
    combined_fdr, st.session_state.all_gws_fdr = calc_team_strengths(teams_data, fixtures_data, next_gws, team_id_to_name, team_id_to_short_name)

    # Store in session state
    st.session_state.team_id_to_name = team_id_to_name
    st.session_state.team_id_to_short_name = team_id_to_short_name
    st.session_state.all_gws_fdr = st.session_state.all_gws_fdr

    # --- FDR Table Logic ---
    df_attack = create_fixture_ticker_df(st.session_state.all_gws_fdr, team_id_to_short_name)
    fdr_attack_df = pd.DataFrame.from_dict({
        team_id_to_short_name[team_id]: {
            f"GW {fixture['Gameweek']}": fixture['Attack FDR']
            for fixture in fixtures[:num_gws]
        }
        for team_id, fixtures in st.session_state.all_gws_fdr.items()
    }, orient='index')

    df_attack = df_attack.iloc[:, :num_gws]
    df_attack['FDR Sum'] = fdr_attack_df.sum(axis=1)
    sorted_idx = df_attack['FDR Sum'].sort_values().index
    df_attack = df_attack.loc[sorted_idx]
    fdr_attack_df = fdr_attack_df.loc[sorted_idx]

    def color_fdr_with_sum(val, fdr, col_name):
        if col_name == 'FDR Sum':
            return 'background-color: #FFF9C4; font-weight: bold; color: black'
        return color_fdr(val, fdr)

    styled_attack_df = df_attack.style.apply(lambda col: [
        color_fdr_with_sum(val, fdr_attack_df.loc[df_attack.index[i], col.name] if col.name != 'FDR Sum' else None, col.name)
        for i, val in enumerate(col)
    ], axis=0)

    df_defense = create_fixture_ticker_df(st.session_state.all_gws_fdr, team_id_to_short_name)
    fdr_defense_df = pd.DataFrame.from_dict({
        team_id_to_short_name[team_id]: {
            f"GW {fixture['Gameweek']}": fixture['Defense FDR']
            for fixture in fixtures[:num_gws]
        }
        for team_id, fixtures in st.session_state.all_gws_fdr.items()
    }, orient='index')

    df_defense = df_defense.iloc[:, :num_gws]
    df_defense['FDR Sum'] = fdr_defense_df.sum(axis=1)
    sorted_idx_def = df_defense['FDR Sum'].sort_values().index
    df_defense = df_defense.loc[sorted_idx_def]
    fdr_defense_df = fdr_defense_df.loc[sorted_idx_def]

    def color_def_fdr_with_sum(val, fdr, col_name):
        if col_name == 'FDR Sum':
            return 'background-color: #FFF9C4; font-weight: bold; color: black'
        color_map = {2: "#00C853", 3: "#E0E0E0", 4: "#FFFF00", 5: "#D50000"}
        color = color_map.get(fdr, "#E0E0E0")
        return f'background-color: {color}; color: black'

    styled_defense_df = df_defense.style.apply(lambda col: [
        color_def_fdr_with_sum(val, fdr_defense_df.loc[df_defense.index[i], col.name] if col.name != 'FDR Sum' else None, col.name)
        for i, val in enumerate(col)
    ], axis=0)

    # Store styled tables
    st.session_state.styled_attack_df = styled_attack_df
    st.session_state.styled_defense_df = styled_defense_df

# --- Always Show Tables if Available ---
if st.session_state.styled_attack_df is not None and st.session_state.styled_defense_df is not None:
    col1, col2 = st.columns(2)
    with col1:
        st.markdown("## Attack FDR Table")
        st.markdown(st.session_state.styled_attack_df.to_html(), unsafe_allow_html=True)
    with col2:
        st.markdown("## Defense FDR Table")
        st.markdown(st.session_state.styled_defense_df.to_html(), unsafe_allow_html=True)

st.session_state.enable_three_team_rotation = st.checkbox("Find best rotation among three teams")

team_names = list(st.session_state.team_id_to_name.values())
st.session_state.team1_input = st.selectbox("Select first team", options=team_names)

if st.session_state.enable_three_team_rotation:
    st.session_state.team2_input = st.selectbox("Select second team", options=[name for name in team_names if name != st.session_state.team1_input])
else:
    st.session_state.team2_input = None
# --- Rotation Analysis Button Below Tables ---
if st.button("Run Rotation Analysis"):
    st.markdown("## 🔄 Rotation Analysis")

    st.session_state.rotation_result = get_best_rotation(st.session_state.all_gws_fdr, num_gws)
    st.markdown("### 🔝 Best Rotation Pair (All Teams)")
    st.write(f"**Attack Rotation:** {st.session_state.team_id_to_name[st.session_state.rotation_result['best_attack_rotation'][0]]} + {st.session_state.team_id_to_name[st.session_state.rotation_result['best_attack_rotation'][1]]} → Total FDR: {st.session_state.rotation_result['attack_fdr_sum']}")
    st.write(f"**Defense Rotation:** {st.session_state.team_id_to_name[st.session_state.rotation_result['best_defense_rotation'][0]]} + {st.session_state.team_id_to_name[st.session_state.rotation_result['best_defense_rotation'][1]]} → Total FDR: {st.session_state.rotation_result['defense_fdr_sum']}")

    # --- Extended Rotation ---
    st.markdown("## 🔄 Extended Rotation Analysis")

    if st.session_state.enable_three_team_rotation:
        rotation_three_result = get_best_rotation_three_teams(st.session_state.all_gws_fdr, num_gws)
        st.markdown("### 🔝 Best Rotation Trio (All Teams)")
        st.write(f"**Attack Rotation:** {', '.join([st.session_state.team_id_to_name[t] for t in rotation_three_result['best_attack_rotation']])} → Total FDR: {rotation_three_result['attack_fdr_sum']}")
        st.write(f"**Defense Rotation:** {', '.join([st.session_state.team_id_to_name[t] for t in rotation_three_result['best_defense_rotation']])} → Total FDR: {rotation_three_result['defense_fdr_sum']}")
    else:
        rotation_two_result = get_best_partner_for_one_team(st.session_state.all_gws_fdr, num_gws, st.session_state.team1_input, st.session_state.team_id_to_name)
        st.markdown(f"### 🔝 Best Rotation Partner for **{st.session_state.team1_input}**")
        st.write(f"**Attack Partner:** {rotation_two_result['best_attack_partner']} → Total FDR: {rotation_two_result['attack_fdr_sum']}")
        st.write(f"**Defense Partner:** {rotation_two_result['best_defense_partner']} → Total FDR: {rotation_two_result['defense_fdr_sum']}")

    if st.session_state.team1_input and st.session_state.team2_input:
        specific_two_team_result = get_best_partner_for_two_teams(
            st.session_state.all_gws_fdr,
            num_gws,
            st.session_state.team1_input,
            st.session_state.team2_input,
            st.session_state.team_id_to_name
        )

        if isinstance(specific_two_team_result, str):
            st.error(specific_two_team_result)
        else:
            st.markdown(f"### 🔍 Best Rotation Partner for **{st.session_state.team1_input} + {st.session_state.team2_input}**")
            st.write(f"**Attack Partner:** {specific_two_team_result['best_attack_partner']} → Total FDR: {specific_two_team_result['attack_fdr_sum']}")
            st.write(f"**Defense Partner:** {specific_two_team_result['best_defense_partner']} → Total FDR: {specific_two_team_result['defense_fdr_sum']}")

