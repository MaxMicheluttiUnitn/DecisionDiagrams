#!/bin/bash
wmi_data_folder_mutex="./benchmarks/wmi/data/mutex/"
wmi_data_folder_xor="./benchmarks/wmi/data/xor/"
output_folder_mutex="./benchmarks/wmi/output_sdd/mutex/"
output_folder_xor="./benchmarks/wmi/output_sdd/xor/"

mkdir ./benchmarks/wmi/output_sdd
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
	echo $tmpsmtfilename
	if [ -f "$output_folder_mutex""$jsonfilename" ]; then
		echo "Skipping task on $smtfilename"
	else
		echo "Performing task on $smtfilename"
		if [ -f "$tmpsmtfilename" ]; then
timeout 3600s python main.py -i "$wmi_data_folder_mutex""$smtfilename" --load_lemmas "$tmpsmtfilename" --tsdd --count_models --count_nodes -d "$output_folder_mutex""$jsonfilename" --tvtree balanced
			if [ $? -eq 0 ]; then
				echo "Task completed on $smtfilename"
			else
				echo "DD Timeout on $smtfilename"
				echo "{\"timeout\":\"DD\"}" > "$output_folder_mutex""$jsonfilename"
			fi
		else
timeout 3600s python main.py -i "$wmi_data_folder_mutex""$smtfilename" --save_lemmas "$tmpsmtfilename" --solver partial -d "$output_folder_mutex""$jsonfilename" --count_models
			if [ $? -eq 0 ]; then
timeout 3600s python main.py -i "$wmi_data_folder_mutex""$smtfilename" --load_lemmas "$tmpsmtfilename" --tsdd --count_models --count_nodes -d "$output_folder_mutex""$jsonfilename" --tvtree balanced
				if [ $? -eq 0 ]; then
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
timeout 3600s python main.py -i "$wmi_data_folder_xor""$smtfilename" --load_lemmas "$tmpsmtfilename" --tsdd --count_models --count_nodes -d "$output_folder_xor""$jsonfilename" --tvtree balanced
			if [ $? -eq 0 ]; then
				echo "Task completed on $smtfilename"
			else
				echo "DD Timeout on $smtfilename"
				echo "{\"timeout\":\"DD\"}" > "$output_folder_xor""$jsonfilename"
			fi
		else
timeout 3600s python main.py -i "$wmi_data_folder_xor""$smtfilename" --save_lemmas "$tmpsmtfilename" -d "$output_folder_xor""$jsonfilename" --count_models
			if [ $? -eq 0 ]; then
timeout 3600s python main.py -i "$wmi_data_folder_xor""$smtfilename" --load_lemmas "$tmpsmtfilename" --tsdd --count_models --count_nodes -d "$output_folder_xor""$jsonfilename" --tvtree balanced
				if [ $? -eq 0 ]; then
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
