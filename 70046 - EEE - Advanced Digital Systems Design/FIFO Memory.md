## Definition
A queue based buffer.
- Used for IO devices, input (e.g. network interface, smooth bursts from unsynchronised IO pins to constant rate synchronised CPU), and output (e.g. generate audio in bursts, but output at constant rate by DAC) 
- Can be implemented as a circular queue.