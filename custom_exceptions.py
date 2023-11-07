'''this module defines custom exceptions for this project'''

class UnsupportedNodeException(Exception):
    '''An exception for unsupported nodes'''
    def __init__(self, message):
        super().__init__(message)
