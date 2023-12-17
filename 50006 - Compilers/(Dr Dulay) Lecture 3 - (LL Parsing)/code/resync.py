# match a token, if necessary report and error, return boolean if the token matched expected.
def match(expected) -> bool:
    if next_token() == expected:
        pop_token()
        return True
    else:
        add_error(next_token(), parser_pos(), [expected], INCORRECT_TOKEN)
        return False

# Skip until at the end of the file, or token matches the sync set
def skipto(syncset):
    while next_token() not in syncset and next_token() != EOF:
        pop_token()


def check(expectset, syncset, error):
    if next_token() not in expectset:
        add_error(next_token(), parser_pos(), expectset, error)
        skipto(expectset + syncset)