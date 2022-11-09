interface Queue<T> {
  	val count: Int
    	get

  	val isEmpty: Boolean
    	get() = count == 0
    
    fun enq(item: T): Boolean
    fun deq(): T?
}

class CircularQueue<T>(val capacity: Int) : Queue<T> {
    var head: Int = 0  // next pop present here
    var tail: Int = 0  // next item pushed here
    var items = MutableList<T?>(capacity){null}
    
  	override val count: Int
    	get() = if  (head >= tail) head - tail else head + (capacity - tail)

  	override val isEmpty: Boolean
    	get() = count == 0
    
    override fun enq(item: T): Boolean {
        if (count < capacity) {
        	items[head] = item    
            head = (head + 1) % capacity
            return true
        } else {
            return false
        }
    }
    
    override fun deq(): T? {
        if (isEmpty) {
            return null
        } else {
            val retval: T = items[tail]!!
            tail = (tail + 1) % capacity
            return retval
        }
    }
}