from rela import *
import time
import os
import json
import pandas as pd

def get_full_paths(directory_path):
    """
    Returns a list of full paths for all files and directories
    within the specified directory.
    """
    full_paths = []
    try:
        for item in os.listdir(directory_path):
            full_path = os.path.join(directory_path, item)
            full_paths.append(full_path)
    except FileNotFoundError:
        print(f"Error: Directory not found at '{directory_path}'")
    except NotADirectoryError:
        print(f"Error: '{directory_path}' is not a directory.")
    return full_paths

file_paths = get_full_paths('./dataset/graph_change_anonymized')
output_file = 'combined.json'


def combine_json_files(file_paths, output_file):
    combined_data = []
    for file_path in file_paths:
        with open(file_path, 'r') as f:
            data = json.load(f)
            combined_data += data
    with open(output_file, 'w') as f:
        json.dump(combined_data, f, indent=4)

combine_json_files(file_paths, output_file)

