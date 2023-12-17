# Get the next token. If it matches the expected, pop it from 
# the list of tokens, else throw an error.
def match(expected: token):
    if lexical_analyser.next_token() == expected:
        lexical_analyser.pop_token()
    else:
        raise error("Unexpected token")