#!/bin/bash

mkdir ./benchmarks/ldd_randgen/output_dDNNF
mkdir ./benchmarks/ldd_randgen/tmp


for gen in ./benchmarks/ldd_randgen/data/*
do
	outputgen="${gen/data/output_dDNNF}"
	tmpgen="${gen/data/tmp}"
	mkdir $outputgen
	mkdir $tmpgen
	for probs in $gen/*
	do
		outputprobs="${probs/data/output_dDNNF}"
		tmpprobs="${probs/data/tmp}"
		mkdir $outputprobs
		mkdir $tmpprobs
		for item in $probs/*
		do
			smtfilename="${item#"$probs"/}"
			jsonfilename="${smtfilename/.smt2/.json}"
			tmpfile="${item/data/tmp}"
			tmpjsonfile="${tmpfile/.smt2/.json}"
			tmpfolder="${tmpfile/.smt2/_c2d}"
			#echo $smtfilename
			#echo $jsonfilename
			#echo $tmpfile
			if [ -f "$outputprobs"/"$jsonfilename" ]; then
				echo "Skipping task on $smtfilename"
			else
				echo "Performing task on $smtfilename"
				if [ -f "$tmpfile" ]; then
					timeout 3600s python main.py -i "$item" --load_lemmas "$tmpfile" --load_details "$tmpjsonfile" --tdDNNF -d "$outputprobs"/"$jsonfilename" --no_dDNNF_to_pysmt --keep_c2d_temp "$tmpfolder"
					if [ $? -eq 0 ]; then
						echo "Task completed on $smtfilename"
					else
						echo "Timeout on $smtfilename"
						echo "{\"timeout\":\"DD\"}" > "$outputprobs"/"$jsonfilename"
					fi
				else
                    ### IF LEMMAS NOT AVAILABLE
                    # timeout 3600s python main.py -i "$item" --save_lemmas "$tmpfile" --solver partial -d "$tmpjsonfile" --count_models
                    # if [ $? -eq 0 ]; then
                    #     timeout 3600s python main.py -i "$item" --load_lemmas "$tmpfile" --load_details "$tmpjsonfile" --tdDNNF --count_nodes --count_models -d "$outputprobs"/"$jsonfilename" --no_dDNNF_to_pysmt --keep_c2d_temp "$tmpfolder"
                    #     if [ $? -eq 0 ]; then
                    #         echo "Task completed on $smtfilename"
                    #     else
                    #         echo "Timeout on $smtfilename"
                    #         echo "{\"timeout\":\"DD\"}" > "$outputprobs"/"$jsonfilename"
                    #     fi
                    # else
                    #     echo "Timeout on $smtfilename"
                    #     echo "{\"timeout\":\"ALL SMT\"}" > "$outputprobs"/"$jsonfilename"
                    # fi
                    ### IF LEMMAS AVAILABLE
                    echo "{\"timeout\":\"ALL SMT\"}" > "$outputprobs"/"$jsonfilename"
				fi
			fi
		done
	done
done
