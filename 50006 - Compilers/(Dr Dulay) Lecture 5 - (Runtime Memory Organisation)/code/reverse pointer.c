// Variables used to keep track of location
void **current_ptr;
void **next_ptr;
void* current_block;

// traverse downwards
next_ptr = find_ptr_in_block(current_block);

current_block = *next_ptr; // current_block = address of next block
*next_ptr = current_ptr; // next_ptr now contains the address of where the old current_ptr was stored
current_ptr = next_ptr;

// we can mark the block we are current at
mark_block(current_block);

// traversing upwards (assuming no next_ptr)
next_ptr = *current_ptr; // the next pointer is now previous (traversing back)
*current_ptr = current_block; // set the current ptr back to being the next block
current_ptr = next_ptr; // current pointer moves to the previous
current_block = block_from_ptr(*current_ptr); //get the block we are now in
