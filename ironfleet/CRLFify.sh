#!/bin/bash

awk 'sub("$", "\r")' $1 > $2
echo $1