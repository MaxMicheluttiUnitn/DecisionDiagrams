#!/bin/bash

mkdir ./benchmarks/smtlib/output_abstraction_sdd
mkdir ./benchmarks/smtlib/output_abstraction_sdd/non-incremental
mkdir ./benchmarks/smtlib/output_abstraction_sdd/non-incremental/QF_RDL

for folder in ./benchmarks/smtlib/data/non-incremental/QF_RDL/*
do
    outputfolder="${gen/data/output_abstraction_sdd}"
    mkdir $outputfolder
    for item in $folder/*
    do
        smtfilename="${item#"$folder"/}"
        jsonfilename="${smtfilename/.smt2/.json}"
        #echo $smtfilename
        #echo $jsonfilename
        if [ -f "$outputfolder"/"$jsonfilename" ]; then
            echo "Skipping task on $smtfilename"
        else
            echo "Performing task on $smtfilename"
            timeout 3600s python main.py -i "$item" --sdd --count_nodes --count_models --pure_abstraction -d "$outputfolder"/"$jsonfilename" --vtree balanced
            if [ $? -eq 0 ]; then
                echo "Task completed on $smtfilename"
            else
                echo "Timeout on $smtfilename"
                echo "{}" > "$outputfolder"/"$jsonfilename"
            fi
        fi
    done
done