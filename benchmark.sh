#!/bin/bash
if [ $# -eq 4 ]
then
    min_seed=$1
    max_seed=$2
    seed_displacement=$3
    timeout_time=$4
    seed=$min_seed
    # bool vars go from 4 to 10
    # real vars go from 4 to 10
    # depth go from 4 to 10
    bool=4
    real=4
    depth=4
    rm -rf problems_and_solutions_synth
    mkdir problems_and_solutions_synth
    while [ $bool -le 10 ]; do
        while [ $real -le 10 ]; do
            while [ $depth -le 10 ]; do
                    # mkdir logs/run_b${bool}_r${real}_d${depth}_m1
                    while [ $seed -le $max_seed ]; do
                        echo "Iteration: BOOL = $bool REAL = $real DEPTH = $depth SEED = $seed"
                        python3 problem_generator.py -s $seed -b $bool -r $real -d $depth -m 1 
                        timeout ${timeout_time}s python3 main.py -i problems_and_solutions_synth/synthetic_problems_b${bool}_r${real}_d${depth}_m1_s${seed}/01/b${bool}_d${depth}_r${real}_s${seed}_1.smt2 --sdd --sdd_output sdd_remove.dot >  logs/run_b${bool}_r${real}_d${depth}_m1/log_${seed}.txt
                        if [ $? -eq 0 ]
                        then
                            rm -f sdd_remove.dot
                            echo "SDD generated"
                        else
                            echo "SDD was not generated: timeout"
                        fi
                        seed=$(($seed+$seed_displacement))
                    done
                    seed=$min_seed
                ((depth++))
            done
            depth=4
            ((real++))
        done
        real=4
        ((bool++))
    done
else
    echo "4 args are required: MIN_SEED  MAX_SEED  SEED_DISPACEMENT  TIMEOUT_TIME"
fi