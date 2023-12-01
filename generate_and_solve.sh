#!/bin/bash
if [ $# -eq 4 ]
then
./problem_generator.sh $1 $2 $3 $4

for n in {1..9..1}; 
do
    echo "======================================================="
    echo "Problem $n" 
    ./problem_solver.sh synthetic_problems_b$2_r$3_d$4_m20_s$1/0$n b$2_d$4_r$3_s$1_0$n.smt2
    echo "Problem $n done" 
done

for n in {10..20..1}; 
do
    echo "======================================================="
    echo "Problem $n" 
    ./problem_solver.sh synthetic_problems_b$2_r$3_d$4_m20_s$1/$n b$2_d$4_r$3_s$1_$n.smt2
    echo "Problem $n done" 
done

echo "======================================================="
else
echo "2 args are required. Format: problem_solver PROBLEM_FILE_LOCATION PROBLEM_FILE_NAME"
fi