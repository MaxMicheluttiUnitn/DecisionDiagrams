#!/bin/bash

mkdir ./benchmarks/smtlib/output_ldd
mkdir ./benchmarks/smtlib/output_ldd/non-incremental
mkdir ./benchmarks/smtlib/output_ldd/non-incremental/QF_RDL


for folder in ./benchmarks/smtlib/data/non-incremental/QF_RDL/*
do
	outputfolder="${folder/data/output_ldd}"
	mkdir $outputfolder
	for item in $folder/*
	do
        smtfilename="${item#"$folder"/}"
        jsonfilename="${smtfilename/.smt2/.json}"
        # echo $smtfilename
        # echo $jsonfilename
        # echo $tmpfile
        if [ -f "$outputfolder"/"$jsonfilename" ]; then
            echo "Skipping task on $smtfilename"
        else
            echo "Performing task on $smtfilename"
timeout 3600s python main.py -i "$item" --ldd --count_nodes --count_models -d "$outputfolder"/"$jsonfilename"
            if [ $? -eq 0 ]; then
                echo "Task completed on $smtfilename"
            else
                echo "Timeout on $smtfilename"
                echo "{\"timeout\":\"DD\"}" > "$outputfolder"/"$jsonfilename"
            fi
        fi
	done
done
