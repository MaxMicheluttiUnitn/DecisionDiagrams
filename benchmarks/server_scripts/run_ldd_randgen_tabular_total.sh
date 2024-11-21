#!/bin/bash

mkdir ./benchmarks/ldd_randgen/tmp_tabular_total


for gen in ./benchmarks/ldd_randgen/data/*
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
			tmpjsonfile="${tmpfile/.smt2/.json}"
			#echo $smtfilename
			#echo $jsonfilename
			#echo $tmpfile
			echo "Performing task on $smtfilename"
			timeout 3600s python main.py -i "$item" --save_lemmas "$tmpfile" --solver tabular_total -d "$tmpjsonfile" --count_models
			if [ $? -eq 0 ]; then
				echo "Task completed on $smtfilename"
			else
				echo "Timeout on $smtfilename"
			fi
		done
	done
done
