#!/bin/bash

mkdir ./benchmarks/randgen/output_ddnnf
mkdir ./benchmarks/randgen/tmp


for gen in ./benchmarks/randgen/data/*
do
	outputgen="${gen/data/output_ddnnf}"
	tmpgen="${gen/data/tmp}"
	mkdir $outputgen
	mkdir $tmpgen
	for probs in $gen/*
	do
		outputprobs="${probs/data/output_ddnnf}"
		tmpprobs="${probs/data/tmp}"
		mkdir $outputprobs
		mkdir $tmpprobs
		for item in $probs/*
		do
			smtfilename="${item#"$probs"/}"
			jsonfilename="${smtfilename/.smt2/.json}"
			tmpfile="${item/data/tmp}"
			jsontmpfile="${tmpfile/.smt2/.json}"
			#echo $smtfilename
			#echo $jsonfilename
			#echo $tmpfile
			if [ -f "$outputprobs"/"$jsonfilename" ]; then
				echo "Skipping task on $smtfilename"
			else
				echo "Performing task on $smtfilename"
				if [ -f "$tmpfile" ]; then
					timeout 3600s python main.py -i "$item" --load_lemmas "$tmpfile" --load_details "$jsontmpfile" --tdDNNF -d "$outputprobs"/"$jsonfilename"
					if [ $? -eq 0 ]; then
						echo "Task completed on $smtfilename"
					else
						echo "Timeout on $smtfilename"
						echo "{\"timeout\":\"DD\"}" > "$outputprobs"/"$jsonfilename"
					fi
				else
					timeout 3600s python main.py -i "$item" --save_lemmas "$tmpfile" --solver partial -d "$jsontmpfile" --count_models
					if [ $? -eq 0 ]; then
						timeout 3600s python main.py -i "$item" --load_lemmas "$tmpfile" --load_details "$jsontmpfile" --tdDNNF -d "$outputprobs"/"$jsonfilename"
						if [ $? -eq 0 ]; then
							echo "Task completed on $smtfilename"
						else
							echo "Timeout on $smtfilename"
							echo "{\"timeout\":\"DD\"}" > "$outputprobs"/"$jsonfilename"
						fi
					else
						echo "Timeout on $smtfilename"
						echo "{\"timeout\":\"ALL SMT\"}" > "$outputprobs"/"$jsonfilename"
					fi
				fi
			fi
		done
	done
done
