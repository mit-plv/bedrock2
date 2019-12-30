FROM python:3-alpine

MAINTAINER Samuel Gruetter <gruetter@mit.edu>

LABEL "com.github.actions.name"="wip"
LABEL "com.github.actions.description"="wip"
LABEL "com.github.actions.icon"="activity"
LABEL "com.github.actions.color"="green"

RUN pip3 install requests

COPY run.py /
ENTRYPOINT ["python3", "/run.py"]
