#!/bin/bash
if [ $# -eq 5 ]
then
rm -rf problems_and_solutions_synth/*
mkdir logs/run_b$2_r$3_d$4_m1
n=$1
while [ $n -le 10 ]
do
python3 problem_generator.py -s $n -b $2 -r $3 -d $4 -m 1

echo $n

echo "======================================================="
echo "Problem $n"
timeout $5s python3 main.py -i problems_and_solutions_synth/synthetic_problems_b$2_r$3_d$4_m1_s$n/01/b$2_d$4_r$3_s${n}_1.smt2 --sdd >  logs/run_b$2_r$3_d$4_m1/log_$n.txt
if [ $? -eq 0 ]
then
    echo "SDD generated"
else
    echo "SDD was not generated: timeout"
fi
echo "Problem done" 

echo "======================================================="
((n++))
done
else
echo "5 args are required. Usage: ./generate_and_time.sh SEED #BOOL #REAL DEPTH TIME_LIMIT"
fi