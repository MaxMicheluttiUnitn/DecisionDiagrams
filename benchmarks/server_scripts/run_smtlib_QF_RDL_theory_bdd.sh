#!/bin/bash

mkdir ./benchmarks/smtlib/output_bdd
mkdir ./benchmarks/smtlib/output_bdd/non-incremental
mkdir ./benchmarks/smtlib/output_bdd/non-incremental/QF_RDL
mkdir ./benchmarks/smtlib/tmp
mkdir ./benchmarks/smtlib/tmp/non-incremental
mkdir ./benchmarks/smtlib/tmp/non-incremental/QF_RDL


for folder in ./benchmarks/smtlib/data/non-incremental/QF_RDL/*
do
	outputfolder="${gen/data/output_bdd}"
	tmpfolder="${gen/data/tmp}"
	mkdir $outputfolder
	mkdir $tmpfolder
	for item in $folder/*
	do
        smtfilename="${item#"$folder"/}"
        jsonfilename="${smtfilename/.smt2/.json}"
        tmpfile="${item/data/tmp}"
        # echo $smtfilename
        # echo $jsonfilename
        # echo $tmpfile
        if [ -f "$outputfolder"/"$jsonfilename" ]; then
            echo "Skipping task on $smtfilename"
        else
            echo "Performing task on $smtfilename"
            if [ -f "$tmpfile" ]; then
                timeout 3600s python main.py -i "$item" --load_lemmas "$tmpfile"  --bdd --count_nodes --count_models -d "$outputfolder"/"$jsonfilename"
                if [ $? -eq 0 ]; then
                    echo "Task completed on $smtfilename"
                else
                    echo "Timeout on $smtfilename"
                    echo "{\"timeout\":\"DD\"}" > "$outputfolder"/"$jsonfilename"
                fi
            else
                timeout 3600s python main.py -i "$item" --save_lemmas "$tmpfile"
                if [ $? -eq 0 ]; then
                    timeout 3600s python main.py -i "$item" --load_lemmas "$tmpfile"  --bdd --count_nodes --count_models -d "$outputfolder"/"$jsonfilename"
                    if [ $? -eq 0 ]; then
                        echo "Task completed on $smtfilename"
                    else
                        echo "Timeout on $smtfilename"
                        echo "{\"timeout\":\"DD\"}" > "$outputfolder"/"$jsonfilename"
                    fi
                else
                    echo "Timeout on $smtfilename"
                    echo "{\"timeout\":\"ALL SMT\"}" > "$outputfolder"/"$jsonfilename"
                fi
            fi
        fi
	done
done
