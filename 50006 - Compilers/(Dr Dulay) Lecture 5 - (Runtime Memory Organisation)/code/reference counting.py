# used for assigments such as a = b
def assign(lval, rval):
    if rval.on_heap():
        rval.references += 1
    
    if lval.on_heap():
        lval.references -= 1
        if lval.references == 0:
            gc.reclaim(lval.block)

    lval.value = rval.value
    