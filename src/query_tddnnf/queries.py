"""module where all the queries functions are defined"""

def check_consistency(source_folder: str):
    """function to check if the encoded formula is consistent
    
    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
    """
    raise NotImplementedError()

def check_validity(source_folder: str):
    """function to check if the encoded formula is valid
    
    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
    """
    raise NotImplementedError()

def check_entail_clause(source_folder: str, clause_file: str):
    """function to check if the encoded formula entails the clause specifoied in the clause_file
    
    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
        clause_file (str): the path to the smt2 file containing the clause to check
    """
    raise NotImplementedError()

def check_implicant(source_folder: str, term_file: str):
    """function to check if the term specified in term_file is an implicant for the encoded formula
    
    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
        term_file (str): the path to the smt2 file containing the term to check
    """
    raise NotImplementedError()

def count_models(source_folder: str):
    """function to count the number of models for the encoded formula
    
    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
    """
    raise NotImplementedError()

def enumerate_models(source_folder: str):
    """function to enumerate all models for the encoded formula
    
    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
    """
    raise NotImplementedError()

def condition_tddnnf(source_folder: str, alpha_file: str, output_file: str | None = None):
    """function to transform the T-dDNNF in T-dDNNF | alpha, where alpha is a literal or a conjuction of literals specified in the provided .smt2 file
    
    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
        alpha_file (str): the path to the smt2 file containing the literal (or conjunction of literals) to condition the T-dDNNF
        output_file (str, optional): the path to the .smt2 file where the conditioned T-dDNNF will be saved. Defaults to None.
    """
    raise NotImplementedError()