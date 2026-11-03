# Timetable Generator

A Tkinter desktop timetable generator with CSV inputs for subjects, faculty, labs, and rooms. This prepared folder keeps the `complete.py` implementation and the supplied CSV files it reads. Other alternate versions, the pre-existing SQLite database, and prompt documents were left out.

## Requirements

- Python 3.10 or 3.11 recommended, installed with Tcl/Tk
- Packages in `requirements.txt`

## Setup and run (Windows PowerShell)

```powershell
py -3.11 -m venv .venv
.\.venv\Scripts\Activate.ps1
python -m pip install --upgrade pip
pip install -r requirements.txt
python complete.py
```

Run the command from this project folder so the program can find `data/`. It creates/uses its SQLite database locally; that database is ignored by Git.

## Data

The `data/` contains the CSV inputs used by the selected implementation. Faculty names and IDs in `subject_teachers.csv` have been replaced with synthetic labels and numeric IDs. The separate `lab_teachers.csv` file was omitted because this implementation does not read it and it contains identifiable faculty information. The CSVs may still contain institution-specific course and scheduling data, so confirm you have permission to publish them.

## Before publishing

Confirm the source and data are yours to share. If they are not, keep this repository private or replace the CSVs with anonymized sample data.
