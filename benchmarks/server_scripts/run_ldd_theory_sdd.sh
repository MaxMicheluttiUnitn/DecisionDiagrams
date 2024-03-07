#!/bin/bash

lddbenchfolder="./benchmarks/ldd/LDD_bench_no_exists/"
outputfolder="./benchmarks/ldd/output/theory_sdd/"

mkdir ./benchmarks/ldd/output/
mkdir ./benchmarks/ldd/output/theory_sdd/
mkdir ./benchmarks/ldd/tmp
mkdir ./benchmarks/ldd/tmp/LDD_bench_no_exists

for file in "$lddbenchfolder"*
do
	smtfilename="${file#"$lddbenchfolder"}"
	jsonfilename="${smtfilename/.smt/.json}"
	tmpfile="${file/LDD_bench_no_exists/tmp}"
	#echo "$smtfilename"
	#echo "$jsonfilename"
	if [ -f "$outputfolder""$jsonfilename" ]; then
		echo "Skipping task on $smtfilename"
	else
		echo "Performing task on $smtfilename"
		if [ -f "$tmpfile" ]; then
timeout 3600s python main.py -i "$lddbenchfolder""$smtfilename" --load_lemmas "$tmpfile" --sdd --count_models --count_nodes -d "$outputfolder""$jsonfilename" --vtree balanced
			if [ $? -eq 0 ]; then
				echo "Task completed for $smtfilename"
			else
				echo "Timeout for $smtfilename"
				echo "{\"timeout\":\"DD\"}" > "$outputfolder""$jsonfilename"
			fi
		else
            # ASSUMING ALL SMT HAS ALREADY BEEN COMPUTED
            echo "Timeout for $smtfilename"
			echo "{\"timeout\":\"ALL SMT\"}" > "$outputfolder""$jsonfilename"
            # ASSUMING ALL SMT HAS NOT BEEN COMPUTED YET
timeout 3600s python main.py -i "$lddbenchfolder""$smtfilename" --save_lemmas "$tmpfile" --solver partial 
			if [ $? -eq 0 ]; then
timeout 3600s python main.py -i "$lddbenchfolder""$smtfilename" --load_lemmas "$tmpfile" --sdd --count_models --count_nodes -d "$outputfolder""$jsonfilename" --vtree balanced
				if [ $? -eq 0 ]; then
					echo "Task completed for $smtfilename"
				else
					echo "Timeout for $smtfilename"
					echo "{\"timeout\":\"DD\"}" > "$outputfolder""$jsonfilename"
				fi
			else
				echo "Timeout for $smtfilename"
				echo "{\"timeout\":\"ALL SMT\"}" > "$outputfolder""$jsonfilename"
			fi
		fi
	fi
done
