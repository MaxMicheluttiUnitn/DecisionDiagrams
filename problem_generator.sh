#!/bin/bash
if [ $# -eq 4 ]
then
python3 problem_generator.py -s $1 -b $2 -r $3 -d $4
else
echo "4 args are required. Usage: ./problem_generator.sh SEED #BOOL #REAL DEPTH"
fi