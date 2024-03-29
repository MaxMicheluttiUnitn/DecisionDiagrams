#!/bin/bash
wmi_data_folder_mutex="./benchmarks/wmi/data/mutex/"
wmi_data_folder_xor="./benchmarks/wmi/data/xor/"
output_folder_mutex="./benchmarks/wmi/output_abstraction/mutex/"
output_folder_xor="./benchmarks/wmi/output_abstraction/xor/"

for filem in $wmi_data_folder_mutex*
do
    smtfilename="${filem#"$wmi_data_folder_mutex"}"
    jsonfilename="${smtfilename/.smt2/.json}"
    if [ -f "$output_folder_mutex""$jsonfilename" ]; then
        echo "Skipping task on $smtfilename"
    else
        echo "Performing task on $smtfilename"
timeout 3600s python main.py -i "$wmi_data_folder_mutex""$smtfilename" --abstraction_bdd --count_models --count_nodes -d "$output_folder_mutex""$jsonfilename"
        if [ $? -eq 0 ]; then
            echo "Task completed on $smtfilename"
        else
            echo "Timeout on $smtfilename"
            echo "{}" > "$output_folder_mutex""$jsonfilename"
        fi
    fi
done

for filex in $wmi_data_folder_xor*
do
    smtfilename="${filex#"$wmi_data_folder_xor"}"
    jsonfilename="${smtfilename/.smt2/.json}"
    if [ -f "$output_folder_xor""$jsonfilename" ]; then
        echo "Skipping task on $smtfilename"
    else
        echo "Performing task on $smtfilename"
timeout 3600s python main.py -i "$wmi_data_folder_xor""$smtfilename" --abstraction_bdd --count_models --count_nodes -d "$output_folder_xor""$jsonfilename"
        if [ $? -eq 0 ]; then
            echo "Task completed on $smtfilename"
        else
            echo "Timeout on $smtfilename"
            echo "{}" > "$output_folder_xor""$jsonfilename"
        fi
    fi
done
