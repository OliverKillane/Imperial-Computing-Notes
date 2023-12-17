for node in CFG {
    LiveIn(node) = {}
    LiveOut(node) = {}
}

repeat {
    for node in CFG {
        LiveIn(node) = uses(node) set-or (LiveOut(node) - defines(node))
        LiveOut(node) = set-or of LiveIn(all successors to node)
    }
} until LiveIn and LiveOut do not change