  ## Streamlit app for Fantasy Premier League 

  ## The application is now [**live**](https://fplraita.streamlit.app/)

  ### Overview

  Fantasy Premier League game is open to the public and is contested annually by millions worldwide. Participants must select a team based on real-life Premier League footballers who scored fantasy points based on those players' real-life statistical performances. Points accumulate across the season in order to declare a champion. As well as the overall global leaderboard, there are smaller automatic public leaderboards categorised by home country and Premier League club supported.

  This Streamlit app is a simple, yet comprehensive tool designed to predict player points for the next gameweek(s) In Fantasy Premier League. This project leverages data from various sources to provide accurate and insightful predictions, helping users make informed decisions for their FPL teams.

  ### Features

  - **Data Collection**: Fetches player data from the FPL API and bookmakers' odds from Oddschecker website.
  - **Data Cleaning**: Ensures data integrity by preventing erroneous values such as 'Unknown' for Team and Position.
  - **Name Matching**: Compares and matches player names from different data sources to ensure consistency.
  - **Prediction Model**: Utilizes advanced algorithms to predict player points based on historical data and current performance metrics.
  - **Fixture Difficulty Ratings tool**: Visualizes Fixture Difficulty Ratings calculated according to current season and previous season for Premier League teams.

  ### Usage

  1. **Odds Scraping**: Select `Odds Scraper` from the sidebar to fetch the latest bookmakers' odds from Oddschecker.com for next Premier League matches.
  2. **Data Cleaning**: The app automatically cleans the data to remove any inconsistencies.
  3. **Name Matching**: Ensures that player names from different sources are correctly matched.
  4. **Points Prediction**: Select `Predicted Points` from the sidebar to get predicted points for player.
  5. **Fixture DIfficulty Ratings**: Select `Fixture Difficulty Ratings` from the sidebar to visualize Fixture Difficulty Ratings.

  ## Prerequisites

  - Python 3.10 or later
  - Google Chrome browser

  ### Installation

  In order to use this `Streamlit app`, follow these steps:

  1. Clone the repository:
     ```bash
     git clone https://github.com/raitaaho/FPL.git
     ```
  2. Navigate to the project directory:
     ```bash
     cd FPL
     ```
  3. Install the required dependencies:
     ```bash
     pip install -r requirements.txt
     ```
  4. Ensure that the Chrome browser is installed on your system. The `chromedriver-autoinstaller` package will automatically download and install the appropriate   version of ChromeDriver.

  ## Running the App

  1. Open the app in browser:
     ```bash
     streamlit run Home.py
     ```
  2. Select a functionality from the sidebar

  ## Notes

- Assisting and goalscoring odds for players are usually available a couple of days before the game, so this script is very likely to return an empty file or a file containing a lot of missing values if there are still several days until the first game of the gameweek.
- Webdrivers run or drive a browser from inside your code. The version of the webdriver must match the version of your browser. The `chromedriver-autoinstaller` package will handle the installation of the appropriate ChromeDriver version automatically.
