def allocate(size: int) -> Address:
    # Search through the blocks, can use a better algorithm:
    block = free_blocks.search(size)
    if block.size == size:
        # found exactly the size needed
        free_blocks.remove(block)
        return block.start_address
    elif block.size > size:
        # split the block
        (size_block, other) = free_blocks.split(size)
        free_blocks.remove(size_block)
        return block.start_address
    else:
        # we need more memory
        if os.give_me_more_mem():
           # try again with allocation
        else:
            # OS could not provide
            return NULL

# Can be implemented to takes the block size as a parameter also
def deallocate(ptr: Address):
    # Check free is valid
    if free_blocks.check(address):
        # return block to free blocks, coalesce/merge with another block to 
        # reduce fragmentation
        free_blocks.insert_and_coalesce(ptr)
        

    