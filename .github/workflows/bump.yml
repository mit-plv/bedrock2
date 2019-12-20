on:
  check_run:
    types: [completed]
name: wip action test
jobs:
  updateBranch:
    if: github.ref == 'refs/heads/dev'
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v2
    - run: |
        git branch -a
        git status
        git show HEAD --stat
        echo "$GITHUB_EVENT_PATH"
        cat "$GITHUB_EVENT_PATH"
