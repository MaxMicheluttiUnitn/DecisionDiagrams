#!/bin/bash
if [ $# -eq 2 ]
then
timeout 10s python3 main.py -i problems_and_solutions/$1/$2 --sdd --sdd_output problems_and_solutions/$1/sdd.dot > problems_and_solutions/$1/sdd_logs.txt
if [ $? -eq 0 ]
then
    echo "SDD generated"
    timeout 10s dot -Tsvg problems_and_solutions/$1/sdd.dot > problems_and_solutions/$1/sdd.svg
else
    echo "SDD was not generated: timeout"
fi
timeout 10s python3 main.py -i problems_and_solutions/$1/$2 --bdd --bdd_output problems_and_solutions/$1/bdd.dot > problems_and_solutions/$1/bdd_logs.txt
if [ $? -eq 0 ]
then
    echo "BDD generated"
    timeout 10s dot -Tsvg problems_and_solutions/$1/bdd.dot > problems_and_solutions/$1/bdd.svg
else
    echo "BDD was not generated: timeout"
fi
timeout 10s python3 main.py -i problems_and_solutions/$1/$2 --xsdd > problems_and_solutions/$1/xsdd_logs.txt
if [ $? -eq 0 ]
then
    echo "XSDD generated"
    timeout 10s dot -Tsvg sdd_0.dot > problems_and_solutions/$1/xsdd.svg
    rm sdd_0.dot
else
    echo "XSDD was not generated: timeout"
fi
timeout 10s python3 main.py -i problems_and_solutions/$1/$2 --sdd --sdd_output problems_and_solutions/$1/sdd_balanced.dot --vtree balanced > /dev/null 2>&1
if [ $? -eq 0 ]
then
    echo "Balanced V-tree SDD generated"
    timeout 10s dot -Tsvg problems_and_solutions/$1/sdd_balanced.dot > problems_and_solutions/$1/sdd_balanced.svg
else
    echo "Balanced V-tree was not generated: timeout"
fi
else
echo "2 args are required. Usage: problem_solver PROBLEM_FILE_LOCATION PROBLEM_FILE_NAME"
fi