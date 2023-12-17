import java.io.IOException;
import java.net.DatagramPacket;
import java.net.DatagramSocket;
import java.net.InetAddress;

public class exampleUDPClient {
    // connect to localhost (this machine) on port 2251
    static final int port = 2251;
    static final String ip = "127.0.0.1";

    public static void main(String[] args) throws IOException {
        // Create a buffer to store data to send & receive, place contents from 
        // the console.
        byte buffer[] = System.console().readLine().getBytes();

        // Create a new packet sourced from the buffer to the target ip and port.
        DatagramPacket packet = new DatagramPacket(buffer, buffer.length, InetAddress.getByName(ip), port);

        // Create a datagram socket to send & receive packets
        DatagramSocket socket = new DatagramSocket();

        // send the packet, the ip and port and inside the packet.
        socket.send(packet);

        // reallocate the buffer to take the response packet
        buffer = new byte[256];

        // take the response from the socket and store in buffer.
        packet = new DatagramPacket(buffer, buffer.length);
        socket.receive(packet);

        // print the received data to the console.
        System.out.println(new String(packet.getData()));

        // Socket no longer used, so close.
        socket.close();
    }
}