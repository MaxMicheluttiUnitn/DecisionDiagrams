#!/bin/bash

mkdir ./benchmarks/smtlib/output_sdd
mkdir ./benchmarks/smtlib/output_sdd/non-incremental
mkdir ./benchmarks/smtlib/output_sdd/non-incremental/QF_UF
mkdir ./benchmarks/smtlib/tmp
mkdir ./benchmarks/smtlib/tmp/non-incremental
mkdir ./benchmarks/smtlib/tmp/non-incremental/QF_UF


for folder in ./benchmarks/smtlib/data/non-incremental/QF_UF/*
do
	outputfolder="${folder/data/output_sdd}"
	tmpfolder="${folder/data/tmp}"
	mkdir $outputfolder
	mkdir $tmpfolder
	for item in $folder/*
	do
        smtfilename="${item#"$folder"/}"
        jsonfilename="${smtfilename/.smt2/.json}"
        tmpfile="${item/data/tmp}"
        tmpjsonfilename="${tmpfile/.smt2/.json}" 
        # echo $smtfilename
        # echo $jsonfilename
        # echo $tmpfile
        if [ -f "$outputfolder"/"$jsonfilename" ]; then
            echo "Skipping task on $smtfilename"
        else
            echo "Performing task on $smtfilename"
            if [ -f "$tmpfile" ]; then
                timeout 3600s python main.py -i "$item" --load_details "$tmpjsonfilename" --load_lemmas "$tmpfile"  --tsdd --count_nodes --count_models -d "$outputfolder"/"$jsonfilename" --tvtree balanced
                if [ $? -eq 0 ]; then
                    echo "Task completed on $smtfilename"
                else
                    echo "Timeout on $smtfilename"
                    echo "{\"timeout\":\"DD\"}" > "$outputfolder"/"$jsonfilename"
                fi
            else
                # ASSUMING ALL SMT ALREADY PERFORMED ON ALL FILES
                echo "Timeout on $smtfilename"
                echo "{\"timeout\":\"ALL SMT\"}" > "$outputfolder"/"$jsonfilename"
                # ASSUMING ALL SMT NOT ALREDY PERFORMED ON SOME FILE
                # timeout 3600s python main.py -i "$item" --save_lemmas "$tmpfile" --solver partial -d "$outputfolder"/"$jsonfilename" --count_models
                # if [ $? -eq 0 ]; then
                #     timeout 3600s python main.py -i "$item" --load_details "$tmpjsonfilename" --load_lemmas "$tmpfile"  --tsdd --count_nodes --count_models -d "$outputfolder"/"$jsonfilename" --tvtree balanced
                #     if [ $? -eq 0 ]; then
                #         echo "Task completed on $smtfilename"
                #     else
                #         echo "Timeout on $smtfilename"
                #         echo "{\"timeout\":\"DD\"}" > "$outputfolder"/"$jsonfilename"
                #     fi
                # else
                #     echo "Timeout on $smtfilename"
                #     echo "{\"timeout\":\"ALL SMT\"}" > "$outputfolder"/"$jsonfilename"
                # fi
            fi
        fi
	done
done
