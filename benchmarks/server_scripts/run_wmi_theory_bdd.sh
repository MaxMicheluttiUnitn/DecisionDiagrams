#!/bin/bash
wmi_data_folder_mutex="./benchmarks/wmi/data/mutex/"
wmi_data_folder_xor="./benchmarks/wmi/data/xor/"
output_folder_mutex="./benchmarks/wmi/output/mutex/"
output_folder_xor="./benchmarks/wmi/output/xor/"

mkdir ./benchmarks/wmi/output
mkdir ./benchmarks/wmi/tmp
mkdir ./benchmarks/wmi/tmp/mutex
mkdir ./benchmarks/wmi/tmp/xor
mkdir "$output_folder_mutex"
mkdir "$output_folder_xor"

for filem in $wmi_data_folder_mutex*
do
	smtfilename="${filem#"$wmi_data_folder_mutex"}"
	jsonfilename="${smtfilename/.smt2/.json}"
	tmpsmtfilename="${filem/data/tmp}"
	if [ -f "$output_folder_mutex""$jsonfilename" ]; then
		echo "Skipping task on $smtfilename"
	else
		echo "Performing task on $smtfilename"
		if [ -f "$tmpsmtfilename" ]; then
timeout 3600s python main.py -i "$wmi_data_folder_mutex""$smtfilename" --load_lemmas "$tmpsmtfilename" --bdd --count_models --count_nodes -d "$output_folder_mutex""$jsonfilename"
			if [ $? -eq 0 ]; then
				echo "Task completed on $smtfilename"
			else
				echo "DD Timeout on $smtfilename"
				echo "{\"timeout\":\"DD\"}" > "$output_folder_mutex""$jsonfilename"
			fi
		else
timeout 3600s python main.py -i "$wmi_data_folder_mutex""$smtfilename" --save_lemmas "$tmpsmtfilename"
			if [ $? -eq 0 ]; then
timeout 3600s python main.py -i "$wmi_data_folder_mutex""$smtfilename" --load_lemmas "$tmpsmtfilename" --bdd --count_models --count_nodes -d "$output_folder_mutex""$jsonfilename"
				if [ $?-eq 0 ]; then
					echo "Task completed on $smtfilename"
				else
					echo "DD timeout on $smtfilename"
					echo "{\"timeout\":\"DD\"}" > "$output_folder_mutex""$jsonfilename"
				fi
			else
				echo "ALL-SMT Timeout on $smtfilename"
				echo "{\"timeout\":\"ALL SMT\"}" > "$output_folder_mutex""$jsonfilename"
			fi
		fi
	fi
done

for filex in $wmi_data_folder_xor*
do
	smtfilename="${filex#"$wmi_data_folder_xor"}"
	jsonfilename="${smtfilename/.smt2/.json}"
	tmpsmtfilename="${filex/data/tmp}"
	if [ -f "$output_folder_xor""$jsonfilename" ]; then
		echo "Skipping task on $smtfilename"
	else
		echo "Performing task on $smtfilename"
		if [ -f "$tmpsmtfilename" ]; then
timeout 3600s python main.py -i "$wmi_data_folder_xor""$smtfilename" --load_lemmas "$tmpsmtfilename" --bdd --count_models --count_nodes -d "$output_folder_xor""$jsonfilename"
			if [ $? -eq 0 ]; then
				echo "Task completed on $smtfilename"
			else
				echo "DD Timeout on $smtfilename"
				echo "{\"timeout\":\"DD\"}" > "$output_folder_xor""$jsonfilename"
			fi
		else
timeout 3600s python main.py -i "$wmi_data_folder_xor""$smtfilename" --save_lemmas "$tmpsmtfilename"
			if [ $? -eq 0 ]; then
timeout 3600s python main.py -i "$wmi_data_folder_xor""$smtfilename" --load_lemmas "$tmpsmtfilename" --bdd --count_models --count_nodes -d "$output_folder_xor""$jsonfilename"
				if [ $?-eq 0 ]; then
					echo "Task completed on $smtfilename"
				else
					echo "DD timeout on $smtfilename"
					echo "{\"timeout\":\"DD\"}" > "$output_folder_xor""$jsonfilename"
				fi
			else
				echo "ALL-SMT Timeout on $smtfilename"
				echo "{\"timeout\":\"ALL SMT\"}" > "$output_folder_xor""$jsonfilename"
			fi
		fi
	fi
done
