import java.io.IOException;
import java.net.DatagramPacket;
import java.net.DatagramSocket;
import java.net.InetAddress;

public class exampleUDPServer {
    static final int port = 2251;

    public static void main(String[] args) throws IOException {
        // Create a socket to receive datagrams on.
        DatagramSocket socket = new DatagramSocket(port);

        // Server runs in forever loop to deal with packets.
        while (true) {
            // Allocate a buffer to store packet data
            byte buffer[] = new byte[256];

            // Create a packet to use buffer.
            DatagramPacket packet = new DatagramPacket(buffer, buffer.length);

            // Receive data, write to buffer.
            socket.receive(packet);

            // Print the data received to the console.
            System.out.println(new String(packet.getData(), 0, packet.getLength()));

            // Take response from standard input.
            buffer = System.console().readLine().getBytes();

            // Get the address of the sender from the received packet.
            InetAddress clientAddress = packet.getAddress();
            int clientPort = packet.getPort();

            // Create a new packet from the buffer.
            packet = new DatagramPacket(buffer, buffer.length, clientAddress, clientPort);

            // Send the response.
            socket.send(packet);
        }
    }
}
