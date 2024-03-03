#!/bin/bash

lddbenchfolder="./benchmarks/ldd/LDD_bench_no_exists/"
outputfolder="./benchmarks/ldd/output/abstraction_sdd/"

mkdir ./benchmarks/ldd/output/
mkdir ./benchmarks/ldd/output/abstraction_sdd/

for file in "$lddbenchfolder"*
do
	smtfilename="${file#"$lddbenchfolder"}"
	jsonfilename="${smtfilename/.smt/.json}"
	tmpfile="${file/LDD_bench_no_exists/tmp}"
    if [ -f "$outputfolder""$jsonfilename" ]; then
		echo "Skipping task on $smtfilename"
	else
        echo "Performing task on $smtfilename"
timeout 3600s python main.py -i "$lddbenchfolder""$smtfilename" --pure_abstraction --sdd --count_models --count_nodes -d "$outputfolder""$jsonfilename" --vtree balanced
        if [ $? -eq 0 ]; then
            echo "task completed on $smtfilename"
        else
            echo "Timeout for $smtfilename"
			echo "{\"timeout\":\"DD\"}" > "$outputfolder""$jsonfilename"
        fi
    fi
done