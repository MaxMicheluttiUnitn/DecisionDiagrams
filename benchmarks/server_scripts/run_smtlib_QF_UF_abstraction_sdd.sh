#!/bin/bash

mkdir ./benchmarks/smtlib/output_abstraction_sdd
mkdir ./benchmarks/smtlib/output_abstraction_sdd/non-incremental
mkdir ./benchmarks/smtlib/output_abstraction_sdd/non-incremental/QF_UF

for folder in ./benchmarks/smtlib/data/non-incremental/QF_UF/*
do
    outputfolder="${folder/data/output_abstraction_sdd}"
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
            timeout 3600s python main.py -i "$item" --abstraction_sdd --count_nodes --count_models -d "$outputfolder"/"$jsonfilename" --abstraction_vtree balanced
            if [ $? -eq 0 ]; then
                echo "Task completed on $smtfilename"
            else
                echo "Timeout on $smtfilename"
                echo "{}" > "$outputfolder"/"$jsonfilename"
            fi
        fi
    done
done