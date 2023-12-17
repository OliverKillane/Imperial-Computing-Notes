def get_reach_sets(program):

    # set all reachin, reachout sets to {}
    for instr in program:
        instr.reachin = []
        instr.reachout = []
    
    changed_set = True
    while changed_set:
        # until there is no change, continue to update the sets. This eventually 
        # terminates as the sets are finite, and at each step they can only remain
        # the same size (no change) or grow.

        changed_set = False

        for instr in program:
            # Reachin(n) = all predecessor's reachouts
            new_reachin = union([pred.reachout for pred in instr.preds])
            if new_reachin != instr.reachin:
                changed = True
                instr.reachin = new_reachin

            # Reachout(n) = Gen(n) U (Reachin(n) \ Kill(n))
            new_reachout = instr.gen + (instr.reachin - instr.kill)
            if new_reachout != instr.reachout:
                changed = True
                instr.reachout = new_reachout
