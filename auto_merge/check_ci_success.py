#!/usr/bin/env python3

# This python3 script can be run locally or in a github workflow.
# It requires "pip3 install requests".

import json
import os
import sys

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

def act_on(check_run):
    # status
    if check_run["status"] == "queued" or check_run["status"] == "in_progress":
        print("Check run has not completed, run this script again later.")
        sys.exit(78)
    if check_run["status"] != "completed":
        print(f"Unexpected check run status: {check_run['status']}")
        sys.exit(1)

    # conclusion
    if check_run["conclusion"] != "success":
        print(f"Check run conclusion: {check_run['conclusion']}")
        sys.exit(1)

    sys.exit(0)

def test_act_on():
    check_run = json.load(open("/home/sam/tmp/sample_check_run.json"))
    act_on(check_run)

if __name__ == "__main__":
    if len(sys.argv) != 5:
        print("Error: Expecting exactly four arguments: repo owner, repo name, branch name, check name")
        sys.exit(1)
    repo_owner = sys.argv[1]
    repo_name = sys.argv[2]
    branch_name = sys.argv[3]
    check_name = sys.argv[4]

    sess = create_session(None)
    checks_data = sess.get(
        f"https://api.github.com/repos/{repo_owner}/{repo_name}/commits/{branch_name}/check-runs",
        params={'check_name': check_name, 'filter': 'latest'}
    ).json()

    assert(len(checks_data['check_runs']) == 1)
    check_run = checks_data['check_runs'][0]
    act_on(check_run)
