import streamlit as st

st.set_page_config(
    page_title="Hello",
    page_icon="👋",
)

st.write("# Welcome! 👋")

st.sidebar.success("Select functionality above")

st.markdown(
    """
    This is a web scraper for Oddschecker.com, an odds comparison website that shows real-time odds from all the top bookmakers.
    It scrapes odds for Total Home and Away Goals, Player Assists, Goalkeeper Saves and Player Goals for Premier League matches.
    The odds are saved to a match specific JSON files and a single JSON file containing odds for every match.

    **👈 Select to scrape odds or view Fantasy Premier League predicted points according to the bookmaker odds**
"""
)