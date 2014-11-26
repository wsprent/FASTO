#!/bin/bash
#
# Compile and run a FASTO program.  Assumes that you have a program 'mars' in
# your PATH, or have set MARS, or have a Mars.jar in your home folder.
#
# This script works on Windows under Cygwin

set -e # Exit on first error.

if [ "$1" = -o ]; then
    flags=-o
    shift
else
    flags=-c
fi

IS_CYGWIN=""
if [[ $(uname -o 2> /dev/null) == "Cygwin" ]]; then
    IS_CYGWIN="true"
fi

RUNMARS=$(which mars &> /dev/null || echo '')

if [ -z $RUNMARS ]; then

    if [ -z "$MARS" ]; then
        MARS="$HOME/Mars*.jar"

        if [ $IS_CYGWIN ]; then
            MARS=$(cygpath -w $MARS)
        fi
    fi

    RUNMARS="java -jar $MARS"
fi

"$(dirname "$0")/../bin/fasto" $flags "$1"
$RUNMARS nc "$(dirname "$1")/$(basename "$1" .fo).asm" 2> /dev/null
