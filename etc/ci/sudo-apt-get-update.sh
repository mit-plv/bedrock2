#!/usr/bin/env bash

# When "apt-get update" fails to connect to the repo servers, it still exits with 0 (success), and then it can happen that Coq from the Ubuntu repos (very outdated) is installed instead of Coq from the PPA. This wrapper makes sure "apt-get update" has a non-zero exit code if it failed to fetch the packet metadata.

(sudo apt-get update "$@" 2>&1 || echo 'E: update failed') | tee /tmp/apt.err
! grep -q '^\(E:\|W: Failed to fetch\)' /tmp/apt.err || exit $?
