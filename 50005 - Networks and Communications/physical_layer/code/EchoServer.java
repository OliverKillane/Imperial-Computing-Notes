import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

public class EchoServer {

    static int portNumber;
    public static void main(String args[]) {

        // try with resources statement closes the writer, reader and sockets 
        // after the statement
        try (
            ServerSocket serverSocket = new ServerSocket(portNumber);

            // wait for the client to connect
            Socket clientSocket = serverSocket.accept();
            PrintWriter out = new PrintWriter(clientSocket.getOutputStream(), true);
            BufferedReader in = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()));
            ) {
            
            System.out.println("Client connected on port " + portNumber + ". Servicing requests.");
            String inputLine;
            while ((inputLine = in.readLine()) != null) {
                System.out.println("Received message: " + inputLine + " from " + clientSocket.toString());
                out.println(inputLine);
            }
        } catch (IOException e) {
            System.out.println("Exception caught either when trying to listen on port " + portNumber + " or while listening for a connection");
        }
    }
}
