import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

public class exampleTCPServer {
    static final int port = 2251;

    public static void main(String[] args) throws IOException {
        // Bind and set socket to listen.
        ServerSocket serverSocket = new ServerSocket(port);

        // status message
        System.out.println("Started listening on port " + port);

        while (true) {
            // accept a new connection and create socket to handle connection.
            Socket socket = serverSocket.accept();

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
}
