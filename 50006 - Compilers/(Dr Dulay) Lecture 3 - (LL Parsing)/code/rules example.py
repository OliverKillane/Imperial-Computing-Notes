def Stat() -> Statement:
    if next_token == IF:
        return IfStat()
    elif next_token == BEGIN:
        return BeginStat()
    elif next_token == PRINT:
        return PrintStat()
    else:
        raise error("Expected Statement Starting Token")

# Parse an if statement, returning the statement if parse succeeds.
def IfStat() -> Statement:
    match(IF)
    cond = Expr()
    match(THEN)
    if_branch = Stat()
    else_branch = None
    if next_token() == ELSE:
        match(ELSE)
        else_branch = Stat()
    match(FI)
    return IfStatement(cond, if_branch, else_branch)

# Parse a block of statements, returning the block statement if successful
def BeginStat() -> Statement:
    stats = []
    match(BEGIN)
    stats.append(Stat())
    while next_token() == SEMICOLON:
        match(SEMICOLON)
        stats.append(Stat())
    match(END)
    return Block(stats)

# Parse a print statement, returning the statement if successful.
def PrintStat() -> Statement:
    match(PRINT)
    return PrintStatement(Expr())

