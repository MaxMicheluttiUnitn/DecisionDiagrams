"""utility functions for query_ddnnf"""
import os


def is_tddnnf_loading_folder_correct(folder: str) -> bool:
    """checks if the folder where the dDNNF files are stored 
    has all the required content to load the T-dDNNF

    Args:
        folder (str): the path to the folder where the dDNNF files are stored

    Returns:
        bool: True if the folder has all required files and subfolders, False otherwise
    """
    # check that the folder exists
    if not os.path.exists(folder):
        return False
    # trim if path finishes with /
    if folder.endswith("/"):
        folder = folder[:-1]
    # check that mapping subfolder exists
    if not os.path.exists(os.path.join(folder, "/mapping")):
        return False
    # check that the mapping subfolder has a mapping.json file
    if not os.path.exists(os.path.join(folder, "/mapping/mapping.json")):
        return False
    # check that the file dimacs.cnf.nnf exists
    if not os.path.exists(os.path.join(folder, "/dimacs.cnf.nnf")):
        return False
    return True
