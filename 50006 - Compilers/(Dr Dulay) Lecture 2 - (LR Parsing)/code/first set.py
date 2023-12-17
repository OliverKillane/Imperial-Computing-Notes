def get_first_set(non_terminal):
    first_set = []
    # go through each alternative
    for alternative in non_terminal:
        # iterate through all terminal/non-terminals in the alternative until 
        # one does not have an epsilon.

        # If it has an epsilon, it means we could potentially skip through to 
        # the next production (e.g in "i*j" the first if i has epsilon, as we 
        # can skip it, hence we must also consider j).

        for b in alternative:
            b_first_set = get_first_set(b)
            first_set += b_first_set - EPSILON

            # if no epsilon in the next terminal/non-terminal, we stop adding 
            # to the first set.
            if EPSILON not in get_first_set(b):
                break
