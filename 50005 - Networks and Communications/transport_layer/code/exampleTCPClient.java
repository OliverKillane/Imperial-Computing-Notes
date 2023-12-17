import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.UnknownHostException;

public class exampleTCPClient {
    // connect to localhost (this machine) on port 2251
    static final int port = 2251;
    static final String ip = "127.0.0.1";

    public static void main(String[] args) throws UnknownHostException, IOException {
        // Create a socket and implicitly connect.
        Socket socket = new Socket(ip, port);

        // create reader and writer for sending and receiving
        BufferedReader receive = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        PrintWriter send = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()), true);

        // send a message from console input
        send.println(System.console().readLine());

        // print a received message from the socket to the console
        System.out.println(receive.readLine());

        // close the socket
        socket.close();
    }
}