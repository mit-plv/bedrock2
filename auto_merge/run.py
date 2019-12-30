#!/usr/bin/env python

import json
import os

import requests


def create_session(github_token=None):
    sess = requests.Session()
    sess.headers = {
        "Accept": "; ".join([
            "application/vnd.github.v3+json",
            "application/vnd.github.antiope-preview+json",
        ]),
        "User-Agent": f"GitHub Actions script in {__file__}"
    }
    if github_token:
        sess.headers["Authorization"] = f"token {github_token}"

    def raise_for_status(resp, *args, **kwargs):
        try:
            resp.raise_for_status()
        except Exception:
            print(resp.text)
            sys.exit("Error: Invalid repo, token or network issue!")

    sess.hooks["response"].append(raise_for_status)
    return sess

def jprint(d):
    print(json.dumps(d, indent=4, sort_keys=True))

if __name__ == "__main__":
    print("run.py launched!")

    event_path = os.environ["GITHUB_EVENT_PATH"]
    event_data = json.load(open(event_path))
    jprint(event_data)

    github_token = os.environ.get("GITHUB_TOKEN")

    sess = create_session(github_token)

    checks_data = sess.get("/repos/mit-plv/bedrock2/commits/18bf9eb1993d04b6a7f8919373c8beeb30f4a35c/check-runs").json()

    jprint(checks_data)

    if "check_run" in event_data:
        check_run = event_data["check_run"]
        name = check_run["name"]

        if check_run["status"] != "completed":
            print(f"*** Check run {name} has not completed")
            sys.exit(78)

        if check_run["conclusion"] != "success":
            print(f"*** Check run {name} has not succeeded")
            sys.exit(1)
    else:
        print("no 'check_run' key")
