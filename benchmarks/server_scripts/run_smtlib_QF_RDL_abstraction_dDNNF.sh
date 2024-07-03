#!/bin/bash

mkdir ./benchmarks/smtlib/output_ddnnf_abstract
mkdir ./benchmarks/smtlib/output_ddnnf_abstract/non-incremental
mkdir ./benchmarks/smtlib/output_ddnnf_abstract/non-incremental/QF_RDL
mkdir ./benchmarks/smtlib/tmp_abstract
mkdir ./benchmarks/smtlib/tmp_abstract/non-incremental
mkdir ./benchmarks/smtlib/tmp_abstract/non-incremental/QF_RDL


for folder in ./benchmarks/smtlib/data/non-incremental/QF_RDL/*
do
	outputfolder="${folder/data/output_ddnnf_abstract}"
	tmpfolder="${folder/data/tmp_abstract}"
	mkdir $outputfolder
	mkdir $tmpfolder
	for item in $folder/*
	do
        smtfilename="${item#"$folder"/}"
        jsonfilename="${smtfilename/.smt2/.json}"
        tmpfile="${item/data/tmp_abstract}"
        tmpjsonfilename="${tmpfile/.smt2/.json}"
        tmpfolder="${tmpfile/.smt2/_c2d}" 
        # echo $smtfilename
        # echo $jsonfilename
        # echo $tmpfile
        if [ -f "$outputfolder"/"$jsonfilename" ]; then
            echo "Skipping task on $smtfilename"
        else
            echo "Performing task on $smtfilename"
            python main.py -i "$item" --load_lemmas "$tmpfile"  --abstraction_dDNNF -d "$outputfolder"/"$jsonfilename" --no_dDNNF_to_pysmt --keep_c2d_temp "$tmpfolder"
            echo "Task completed on $smtfilename"
        fi
	done
done
