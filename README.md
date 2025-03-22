
  ## Predicted_Points_All_Players Notebook

  ### Overview

  Fantasy Premier League game is open to the public and is contested annually by millions worldwide. Participants must select a team based on real-life Premier League footballers who scored fantasy points based on those players' real-life statistical performances. Points accumulate across the season in order to declare a champion. As well as the overall global leaderboard, there are smaller automatic public leaderboards categorised by home country and Premier League club supported.

  The `Predicted_Points_All_Players` notebook is a comprehensive tool designed to predict player points for the next gameweek(s) In Fantasy Premier League. This project leverages data from various sources to provide accurate and insightful predictions, helping users make informed decisions for their FPL teams.

  ### Features

  - **Data Collection**: Fetches player data from the FPL API and bookmakers' odds from Oddschecker website.
  - **Data Cleaning**: Ensures data integrity by preventing erroneous values such as 'Unknown' for Team and Position.
  - **Name Matching**: Compares and matches player names from different data sources to ensure consistency.
  - **Prediction Model**: Utilizes advanced algorithms to predict player points based on historical data and current performance metrics.

  ### Usage

  1. **Data Fetching**: Run the notebook to fetch the latest player data from the FPL API and Oddschecker.
  2. **Data Cleaning**: The notebook automatically cleans the data to remove any inconsistencies.
  3. **Name Matching**: Ensures that player names from different sources are correctly matched.
  4. **Prediction**: Executes the prediction model to generate point predictions for all players.

  ## Prerequisites

  - Python 3.10 or later
  - Google Chrome browser

  ### Installation

  To use the `Predicted_Points_All_Players` notebook, follow these steps:

  1. Clone the repository:
     ```bash
     !git clone https://github.com/raitaaho/FPL.git
     ```
  2. Navigate to the project directory:
     ```bash
     cd FPL
     ```
  3. Install the required dependencies:
     ```bash
     !pip install -r requirements.txt
     ```
  4. Ensure that the Chrome browser is installed on your system. The `chromedriver-autoinstaller` package will automatically download and install the appropriate   version of ChromeDriver.

  ## Running the Notebook

  1. Run the notebook in Jupyter:
     ```bash
     jupyter nbconvert --to notebook --execute Predicted_Points_All_Players.ipynb
     ```

  ## Notes

- Assisting and goalscoring odds for players are usually available a couple of days before the game, so this script is very likely to return an empty file or a file containing a lot of missing values if there are still several days until the first game of the gameweek.
- The script has been improved to handle game weeks where a team may play more than one match.
- Webdrivers run or drive a browser from inside your code. The version of the webdriver must match the version of your browser. The `chromedriver-autoinstaller` package will handle the installation of the appropriate ChromeDriver version automatically.
