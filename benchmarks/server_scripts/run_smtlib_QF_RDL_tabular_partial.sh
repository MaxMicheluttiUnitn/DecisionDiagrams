#!/bin/bash

mkdir ./benchmarks/smtlib/tmp_tabular_partial
mkdir ./benchmarks/smtlib/tmp_tabular_partial/non-incremental
mkdir ./benchmarks/smtlib/tmp_tabular_partial/non-incremental/QF_RDL


for folder in ./benchmarks/smtlib/data/non-incremental/QF_RDL/*
do
	tmpfolder="${folder/data/tmp_tabular_partial}"
	mkdir $tmpfolder
	for item in $folder/*
	do
        smtfilename="${item#"$folder"/}"
        jsonfilename="${smtfilename/.smt2/.json}"
        tmpfile="${item/data/tmp_tabular_partial}"
        tmpjsonfilename="${tmpfile/.smt2/.json}" 
        # echo $smtfilename
        # echo $jsonfilename
        # echo $tmpfile
        echo "Performing task on $smtfilename"
        timeout 3600s python main.py -i "$item" --save_lemmas "$tmpfile" --solver tabular_partial -d "$tmpjsonfilename" --count_models
        if [ $? -eq 0 ]; then
            echo "Task completed on $smtfilename"
        else
            echo "Timeout on $smtfilename"
        fi
	done
done
