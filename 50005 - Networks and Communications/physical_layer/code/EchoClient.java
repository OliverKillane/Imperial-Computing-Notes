import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.net.UnknownHostException;

class EchoClient {

    static String hostName;
    static int portNumber;

    public static void main(String args[]) {
        try (Socket echoSocket = new Socket(hostName, portNumber);

            // Communication with the server through the socket
            PrintWriter out = new PrintWriter(echoSocket.getOutputStream(), true);
            BufferedReader in = new BufferedReader(new InputStreamReader(echoSocket.getInputStream()));

            // Read user input from terminal
            BufferedReader stdIn = new BufferedReader(new InputStreamReader(System.in))) {
            
            
            String userInput;
                while ((userInput = stdIn.readLine()) != null) {
                out.println(userInput);
                System.out.println("echo: " + in.readLine());
            }

        } catch (UnknownHostException e) {
            System.err.println("Don't know about host " + hostName);
            System.exit(1);

        } catch (IOException e) {
            System.err.println("Couldn't get I/O for the connection to " + hostName);
            System.exit(1);

        }
    }
}
