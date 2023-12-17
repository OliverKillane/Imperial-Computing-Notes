/* Loop with array indexes */
for ( size_t i = 0; i < length; ++i )
	dst[i] = src[i];

/* Loop with pointers */
const int* s = src;
int* d = dst;
const int*const dend = dst + n;
while ( d != dend )
	*d++ = *s++;

/* Loop with get/set function calls */
int get( const int*const src, const size_t index ) { return src[index]; }
int set( int*const dst, const size_t index, const int value ) { dst[index] = value; }

for ( size_t i = 0; i < n; ++i )
	set( dst, i, get( src, i ) );

/* Memcpy (two regions are disjoint) */
memcpy( (void*)dst, (void*)src, n * sizeof(int) );

/* Memmove (for when regions may overlap) */
memmove( (void*)dst, (void*)src, n * sizeof(int) );