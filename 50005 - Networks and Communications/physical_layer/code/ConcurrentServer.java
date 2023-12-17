import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

public class ConcurrentServer {
    static int threads = 5;
    static int portNumber;
    public static void main(String args[]) {
        try (ServerSocket serverSocket = new ServerSocket(portNumber);) {
            ExecutorService executor = Executors.newFixedThreadPool(threads);
    
            System.out.println("Waiting for clients to connect...");
    
            while (true) {
                Socket clientSocket = serverSocket.accept();
                executor.execute(new RequestHandler(clientSocket));
            }

        } catch (IOException e) {
            System.out.println("Exception caught when trying to listen on port " + portNumber + " or listening for a connection");
        }
        
    }
}

class RequestHandler implements Runnable {
    Socket clientsocket;

    RequestHandler(Socket clientsocket) {
        this.clientsocket = clientsocket;
    }

    @Override
    public void run() {

        try (
            BufferedReader in = new BufferedReader(new InputStreamReader(clientsocket.getInputStream()));
            BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(clientsocket.getOutputStream()));
            ) {
            System.out.println("Thread started with name:" + Thread.currentThread().getName());

            String userInput;
            while ((userInput = in.readLine()) != null) {
                userInput = userInput.replaceAll("[^A-Za-z0-9 ]", "");
                System.out.println("Received message from " + Thread.currentThread().getName() + " : " + userInput);
                writer.write("You entered : " + userInput);
                writer.newLine();
                writer.flush();
            }

        } catch (IOException e) {
            System.out.println("Exception raised while attempting to handle request");

        }
    }
}