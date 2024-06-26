#!/bin/bash

mkdir ./benchmarks/ldd_randgen/output_abstraction_sdd

for gen in ./benchmarks/ldd_randgen/data/*
do
    outputgen="${gen/data/output_abstraction_sdd}"
    mkdir $outputgen
    for probs in $gen/*
    do
        outputprobs="${probs/data/output_abstraction_sdd}"
        mkdir $outputprobs
        for item in $probs/*
        do
            smtfilename="${item#"$probs"/}"
            jsonfilename="${smtfilename/.smt2/.json}"
            #echo $smtfilename
            #echo $jsonfilename
            if [ -f "$outputprobs"/"$jsonfilename" ]; then
                echo "Skipping task on $smtfilename"
            else
                echo "Performing task on $smtfilename"
                timeout 3600s python main.py -i "$item" --abstraction_sdd --count_nodes --count_models -d "$outputprobs"/"$jsonfilename" --abstraction_vtree balanced
                if [ $? -eq 0 ]; then
                    echo "Task completed on $smtfilename"
                else
                    echo "Timeout on $smtfilename"
                    echo "{}" > "$outputprobs"/"$jsonfilename"
                fi
            fi
        done
    done
done
