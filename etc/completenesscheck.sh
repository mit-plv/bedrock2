#!/bin/bash

comm -1 -3 <(grep -v '^#' etc/all-files.txt | sort) <(find . -name '*.v' | sort)
