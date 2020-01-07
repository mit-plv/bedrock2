FROM python:3-alpine

MAINTAINER Samuel Gruetter <gruetter@mit.edu>

LABEL "com.github.actions.name"="wip"
LABEL "com.github.actions.description"="wip"
LABEL "com.github.actions.icon"="activity"
LABEL "com.github.actions.color"="green"

RUN pip3 install requests

COPY check_ci_success.py /
ENTRYPOINT ["python3", "/check_ci_success.py"]
