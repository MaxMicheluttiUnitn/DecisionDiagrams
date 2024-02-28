"""utility functions module"""


def get_string_from_atom(atom):
    '''Changes special characters into ASCII encoding'''
    # svg format special characters source:
    # https://rdrr.io/cran/RSVGTipsDevice/man/encodeSVGSpecialChars.html
    atom_str = str(atom).replace('&', '&#38;').replace('\'', "&#30;").replace(
        '"', "&#34;").replace('<', '&#60;').replace('>', "&#62;")
    if atom_str.startswith('('):
        return atom_str[1:len(atom_str)-1]
    return atom_str