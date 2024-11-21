#!/bin/bash

mkdir ./benchmarks/randgen/tmp_tabular_total


for gen in ./benchmarks/randgen/data/*
do
	tmpgen="${gen/data/tmp_tabular_total}"
	mkdir $tmpgen
	for probs in $gen/*
	do
		tmpprobs="${probs/data/tmp_tabular_total}"
		mkdir $tmpprobs
		for item in $probs/*
		do
			smtfilename="${item#"$probs"/}"
			jsonfilename="${smtfilename/.smt2/.json}"
			tmpfile="${item/data/tmp_tabular_total}"
			jsontmpfile="${tmpfile/.smt2/.json}"
			#echo $smtfilename
			#echo $jsonfilename
			#echo $tmpfile
			echo "Performing task on $smtfilename"	
			timeout 3600s python main.py -i "$item" --save_lemmas "$tmpfile" --solver tabular_total -d "$jsontmpfile" --count_models
			if [ $? -eq 0 ]; then	
				echo "Task completed on $smtfilename"
			else
				echo "Timeout on $smtfilename"
			fi
		done
	done
done
