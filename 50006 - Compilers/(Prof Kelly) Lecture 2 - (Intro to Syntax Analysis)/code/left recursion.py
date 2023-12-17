def parse_add(input):
    (add_parse_tree, rest) = parse_add(input)
    rest = parse_plus(rest) # infinite recursion
    (mul_parse_tree, rest) = parse_mul(rest)
    return (tree(add_parse_tree, mul_parse_tree), rest)