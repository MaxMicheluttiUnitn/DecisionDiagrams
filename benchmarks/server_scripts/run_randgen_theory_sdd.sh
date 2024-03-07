#!/bin/bash

mkdir ./benchmarks/randgen/output_sdd

for gen in ./benchmarks/randgen/data/*
do
	outputgen="${gen/data/output_sdd}"
	tmpgen="${gen/data/tmp}"
	mkdir $outputgen
	mkdir $tmpgen
	for probs in $gen/*
	do
		outputprobs="${probs/data/output_sdd}"
		tmpprobs="${probs/data/tmp}"
		mkdir $outputprobs
		mkdir $tmpprobs
		for item in $probs/*
		do
			smtfilename="${item#"$probs"/}"
			jsonfilename="${smtfilename/.smt2/.json}"
			tmpfile="${item/data/tmp}"
			#echo $smtfilename
			#echo $jsonfilename
			#echo "$tmpfile"
			if [ -f "$outputprobs"/"$jsonfilename" ]; then
				echo "Skipping task on $smtfilename"
			else
				echo "Performing task on $smtfilename" 
				if [ -f "$tmpfile" ]; then
					timeout 3600s python main.py -i "$item" --load_lemmas "$tmpfile"  --sdd --count_nodes --count_models -d "$outputprobs"/"$jsonfilename" --vtree balanced
					if [ $? -eq 0 ]; then
						echo "Task completed on $smtfilename"
					else
						echo "Timeout on $smtfilename"
						echo "{\"timeout\":\"DD\"}" > "$outputprobs"/"$jsonfilename"
					fi
				else
					# ASSUMING ALL SMT ALREADY DONE
					echo "Timeout on $smtfilename"
					echo "{\"timeout\":\"ALL SMT\"}" > "$outputprobs"/"$jsonfilename"
					# ASSUMING ALL SMT NOT ALREADY DONE
					#timeout 3600s python main.py -i "$item" --save_lemmas "$tmpfile" --solver partial 
					#if [ $? -eq 0 ]; then
					#	timeout 3600s python main.py -i "$item" --load_lemmas "$tmpfile"  --sdd --count_nodes --count_models -d "$outputprobs"/"$jsonfilename"
					#	if [ $? -eq 0 ]; then
					#		echo "Task completed on $smtfilename"
					#	else
					#		echo "Timeout on $smtfilename"
					#		echo "{\"timeout\":\"DD\"}" > "$outputprobs"/"$jsonfilename"
					#	fi
					#else
					#	echo "Timeout on $smtfilename"
					#	echo "{\"timeout\":\"ALL SMT\"}" > "$outputprobs"/"$jsonfilename"
					#fi
				fi
			fi
		done
	done
done
