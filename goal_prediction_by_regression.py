import requests
import pandas as pd
import time
import json
import numpy as np
import matplotlib.pyplot as mp

def get_team_template() -> dict:
    """
    Create a template dictionary for storing player statistics, initialized to default values.

    Args:
        team_name (str): Name of the player's team.
        minutes (int): Total minutes played.
        starts (int): Number of starts.

    Returns:
        dict: Player statistics template.
    """
    team_template = {
            'Total Home Games': 0,
            'Total Home Goals': 0,
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
            'Total Away Games': 0,
            'Total Away Goals': 0,
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
            'Home Games Against Unknown': 0,
            'Home Goals Against Unknown': 0,
            'Home Assists Against Unknown': 0,
            'Away Games Against Unknown': 0,
            'Away Goals Against Unknown': 0,
            'Away Assists Against Unknown': 0,}
    return team_template

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

team_dict = {}
league_ids = ['PL', 'BL1', 'SA', 'PD', 'FL1']  # Premier League, Bundesliga, Serie A, La Liga, Ligue 1
for league_id in league_ids:
    for year in range(2024, 2022, -1):
        uri = f"https://api.football-data.org/v4/competitions/{league_id}/matches?season={str(year)}&status=FINISHED"
        #headers = { 'xxxxxx', 'Accept-Encoding': '' }
        response = requests.get(uri, headers=headers)
        data = response.json()['matches']
        standings_dict = {}
        time.sleep(6)
        for match in data:
            matchday = match['season']['currentMatchday']
            if standings_dict.get(matchday) is None:
                standings_link = f"https://api.football-data.org/v4/competitions/{league_id}/standings?season={str(year)}&matchday={matchday}"
                standings_response = requests.get(standings_link, headers=headers)
                time.sleep(6)
                standings_data = standings_response.json()['standings'][0]['table']
                standings_dict[matchday] = standings_data
                standings = standings_dict[matchday]
            else:
                standings = standings_dict[matchday]
            home_team = match['homeTeam']['name']
            away_team = match['awayTeam']['name']

            home_rank = next((team['position'] for team in standings if team['team']['name'] == home_team), 21)
            away_rank = next((team['position'] for team in standings if team['team']['name'] == away_team), 21)

            home_goals = match['score']['fullTime'].get('home', 0)
            away_goals = match['score']['fullTime'].get('away', 0)

            home_pos_range = get_pos_range(home_rank)
            away_pos_range = get_pos_range(away_rank)

            home_games_against_string = f"Home Games Against {away_pos_range}"
            home_goals_against_string = f"Home Goals Against {away_pos_range}"
            home_assists_against_string = f"Home Assists Against {away_pos_range}"

            away_games_against_string = f"Away Games Against {home_pos_range}"
            away_goals_against_string = f"Away Goals Against {home_pos_range}"
            away_assists_against_string = f"Away Assists Against {home_pos_range}"

            if home_team not in team_dict:
                team_dict[home_team] = get_team_template()
            if away_team not in team_dict:
                team_dict[away_team] = get_team_template()

            team_dict[away_team][away_games_against_string] += 1
            team_dict[away_team]['Total Away Games'] += 1
            team_dict[away_team][away_goals_against_string] += away_goals
            team_dict[away_team]['Total Away Goals'] += away_goals

            team_dict[home_team][home_games_against_string] += 1
            team_dict[home_team]['Total Home Games'] += 1
            team_dict[home_team][home_goals_against_string] += home_goals
            team_dict[home_team]['Total Home Goals'] += home_goals

for team in team_dict:
    team_dict[team]['Goals per Home Game Deviation From Home Average Against 1-4'] = float(team_dict[team]['Home Goals Against 1-4']/team_dict[team]['Home Games Against 1-4']) - float(team_dict[team]['Total Home Goals']/team_dict[team]['Total Home Games']) if team_dict[team]['Home Games Against 1-4'] != 0 and team_dict[team]['Total Home Games'] != 0 else 0
    team_dict[team]['Goals per Home Game Deviation From Home Average Against 5-8'] = float(team_dict[team]['Home Goals Against 5-8']/team_dict[team]['Home Games Against 5-8']) - float(team_dict[team]['Total Home Goals']/team_dict[team]['Total Home Games']) if team_dict[team]['Home Games Against 5-8'] != 0 and team_dict[team]['Total Home Games'] != 0 else 0
    team_dict[team]['Goals per Home Game Deviation From Home Average Against 9-12'] = float(team_dict[team]['Home Goals Against 9-12']/team_dict[team]['Home Games Against 9-12']) - float(team_dict[team]['Total Home Goals']/team_dict[team]['Total Home Games']) if team_dict[team]['Home Games Against 9-12'] != 0 and team_dict[team]['Total Home Games'] != 0 else 0
    team_dict[team]['Goals per Home Game Deviation From Home Average Against 13-16'] = float(team_dict[team]['Home Goals Against 13-16']/team_dict[team]['Home Games Against 13-16']) - float(team_dict[team]['Total Home Goals']/team_dict[team]['Total Home Games']) if team_dict[team]['Home Games Against 13-16'] != 0 and team_dict[team]['Total Home Games'] != 0 else 0
    team_dict[team]['Goals per Home Game Deviation From Home Average Against 17-20'] = float(team_dict[team]['Home Goals Against 17-20']/team_dict[team]['Home Games Against 17-20']) - float(team_dict[team]['Total Home Goals']/team_dict[team]['Total Home Games']) if team_dict[team]['Home Games Against 17-20'] != 0 and team_dict[team]['Total Home Games'] != 0 else 0

    team_dict[team]['Goals per Away Game Deviation From Away Average Against 1-4'] = float(team_dict[team]['Away Goals Against 1-4']/team_dict[team]['Away Games Against 1-4']) - float(team_dict[team]['Total Away Goals']/team_dict[team]['Total Away Games']) if team_dict[team]['Away Games Against 1-4'] != 0 and team_dict[team]['Total Away Games'] != 0 else 0
    team_dict[team]['Goals per Away Game Deviation From Away Average Against 5-8'] = float(team_dict[team]['Away Goals Against 5-8']/team_dict[team]['Away Games Against 5-8']) - float(team_dict[team]['Total Away Goals']/team_dict[team]['Total Away Games']) if team_dict[team]['Away Games Against 5-8'] != 0 and team_dict[team]['Total Away Games'] != 0 else 0
    team_dict[team]['Goals per Away Game Deviation From Away Average Against 9-12'] = float(team_dict[team]['Away Goals Against 9-12']/team_dict[team]['Away Games Against 9-12']) - float(team_dict[team]['Total Away Goals']/team_dict[team]['Total Away Games']) if team_dict[team]['Away Games Against 9-12'] != 0 and team_dict[team]['Total Away Games'] != 0 else 0
    team_dict[team]['Goals per Away Game Deviation From Away Average Against 13-16'] = float(team_dict[team]['Away Goals Against 13-16']/team_dict[team]['Away Games Against 13-16']) - float(team_dict[team]['Total Away Goals']/team_dict[team]['Total Away Games']) if team_dict[team]['Away Games Against 13-16'] != 0 and team_dict[team]['Total Away Games'] != 0 else 0
    team_dict[team]['Goals per Away Game Deviation From Away Average Against 17-20'] = float(team_dict[team]['Away Goals Against 17-20']/team_dict[team]['Away Games Against 17-20']) - float(team_dict[team]['Total Away Goals']/team_dict[team]['Total Away Games']) if team_dict[team]['Away Games Against 17-20'] != 0 and team_dict[team]['Total Away Games'] != 0 else 0

team_data_df = pd.DataFrame.from_dict(team_dict, orient='index')

with pd.ExcelWriter(f"teams_output.xlsx") as writer:
    team_data_df.to_excel(writer, sheet_name='Players')

total_home_games_against_1_4 = team_data_df['Home Games Against 1-4'].sum()
total_home_games_against_5_8 = team_data_df['Home Games Against 5-8'].sum()
total_home_games_against_9_12 = team_data_df['Home Games Against 9-12'].sum()
total_home_games_against_13_16 = team_data_df['Home Games Against 13-16'].sum()
total_home_games_against_17_20 = team_data_df['Home Games Against 17-20'].sum()

total_away_games_against_1_4 = team_data_df['Away Games Against 1-4'].sum()
total_away_games_against_5_8 = team_data_df['Away Games Against 5-8'].sum()
total_away_games_against_9_12 = team_data_df['Away Games Against 9-12'].sum()
total_away_games_against_13_16 = team_data_df['Away Games Against 13-16'].sum()
total_away_games_against_17_20 = team_data_df['Away Games Against 17-20'].sum()

total_home_goals_against_1_4 = team_data_df['Home Goals Against 1-4'].sum()
total_home_goals_against_5_8 = team_data_df['Home Goals Against 5-8'].sum()
total_home_goals_against_9_12 = team_data_df['Home Goals Against 9-12'].sum()
total_home_goals_against_13_16 = team_data_df['Home Goals Against 13-16'].sum()
total_home_goals_against_17_20 = team_data_df['Home Goals Against 17-20'].sum()

total_away_goals_against_1_4 = team_data_df['Away Goals Against 1-4'].sum()
total_away_goals_against_5_8 = team_data_df['Away Goals Against 5-8'].sum()
total_away_goals_against_9_12 = team_data_df['Away Goals Against 9-12'].sum()
total_away_goals_against_13_16 = team_data_df['Away Goals Against 13-16'].sum()
total_away_goals_against_17_20 = team_data_df['Away Goals Against 17-20'].sum()

average_home_goals_against_1_4 = team_data_df['Goals per Home Game Deviation From Home Average Against 1-4'].sum() / len(team_dict)
average_home_goals_against_5_8 = team_data_df['Goals per Home Game Deviation From Home Average Against 5-8'].sum() / len(team_dict)
average_home_goals_against_9_12 = team_data_df['Goals per Home Game Deviation From Home Average Against 9-12'].sum() / len(team_dict)
average_home_goals_against_13_16 = team_data_df['Goals per Home Game Deviation From Home Average Against 13-16'].sum() / len(team_dict)
average_home_goals_against_17_20 = team_data_df['Goals per Home Game Deviation From Home Average Against 17-20'].sum() / len(team_dict)

average_away_goals_against_1_4 = team_data_df['Goals per Away Game Deviation From Away Average Against 1-4'].sum() / len(team_dict)
average_away_goals_against_5_8 = team_data_df['Goals per Away Game Deviation From Away Average Against 5-8'].sum() / len(team_dict)
average_away_goals_against_9_12 = team_data_df['Goals per Away Game Deviation From Away Average Against 9-12'].sum() / len(team_dict)
average_away_goals_against_13_16 = team_data_df['Goals per Away Game Deviation From Away Average Against 13-16'].sum() / len(team_dict)
average_away_goals_against_17_20 = team_data_df['Goals per Away Game Deviation From Away Average Against 17-20'].sum() / len(team_dict)

pos_list = [1, 5, 10, 15, 20]
home_goal_list = [total_home_goals_against_1_4/total_home_games_against_1_4, 
                 total_home_goals_against_5_8/total_home_games_against_5_8,
                 total_home_goals_against_9_12/total_home_games_against_9_12,
                 total_home_goals_against_13_16/total_home_games_against_13_16,
                 total_home_goals_against_17_20/total_home_games_against_17_20]
away_goal_list = [total_away_goals_against_1_4/total_away_games_against_1_4,
                 total_away_goals_against_5_8/total_away_games_against_5_8,
                 total_away_goals_against_9_12/total_away_games_against_9_12,
                 total_away_goals_against_13_16/total_away_games_against_13_16,
                 total_away_goals_against_17_20/total_away_games_against_17_20]

home_goal_coefficients = np.polyfit(np.array(pos_list), np.array(home_goal_list), 3)
away_goal_coefficients = np.polyfit(np.array(pos_list), np.array(away_goal_list), 4)
home_goal_regression = np.poly1d(home_goal_coefficients)
away_goal_regression = np.poly1d(away_goal_coefficients)
with open('home_goal_regression.json', 'w') as f:
    json.dump(home_goal_regression.coefficients.tolist(), f)
with open('away_goal_regression.json', 'w') as f:
    json.dump(away_goal_regression.coefficients.tolist(), f)

mp.plot(pos_list, home_goal_list, 'ro', label='Goals per Home Game')
mp.plot(pos_list, home_goal_regression(pos_list), 'r-', label='Home Goal Regression')
mp.plot(pos_list, away_goal_list, 'bo', label='Goals per Away Game')
mp.plot(pos_list, away_goal_regression(pos_list), 'b-', label='Away Goal Regression')
mp.xlabel('Position Range')
mp.ylabel('Goals per Game')
mp.title('Goals per Game by Opposition Position')
mp.xticks(pos_list, ['1', '5', '10', '15', '20'])
mp.legend()

home_goal_list2 = [average_home_goals_against_1_4, 
                 average_home_goals_against_5_8,
                 average_home_goals_against_9_12,
                 average_home_goals_against_13_16,
                 average_home_goals_against_17_20]
away_goal_list2 = [average_away_goals_against_1_4,
                 average_away_goals_against_5_8,
                 average_away_goals_against_9_12,
                 average_away_goals_against_13_16,
                 average_away_goals_against_17_20]

home_goal_coefficients2 = np.polyfit(np.array(pos_list), np.array(home_goal_list2), 3)
away_goal_coefficients2 = np.polyfit(np.array(pos_list), np.array(away_goal_list2), 3)
home_goal_regression2 = np.poly1d(home_goal_coefficients2)
away_goal_regression2 = np.poly1d(away_goal_coefficients2)
with open('home_goal_regression2.json', 'w') as f:
    json.dump(home_goal_regression2.coefficients.tolist(), f)
with open('away_goal_regression2.json', 'w') as f:
    json.dump(away_goal_regression2.coefficients.tolist(), f)

mp.plot(pos_list, home_goal_list2, 'ro', label='Goals per Home Game Deviation From Home Average')
mp.plot(pos_list, home_goal_regression2(pos_list), 'r-', label='Home Goal Regression')
mp.plot(pos_list, away_goal_list2, 'bo', label='Goals per Away Game Deviation From Away Average')
mp.plot(pos_list, away_goal_regression2(pos_list), 'b-', label='Away Goal Regression')
mp.legend()

mp.show()