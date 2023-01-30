import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;

public class Client {

    public static void main(String[] args) {
        try {
            Socket socket = new Socket("localhost", 12345);

            BufferedReader in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            PrintWriter out = new PrintWriter(socket.getOutputStream());
            BufferedReader stdin = new BufferedReader(new InputStreamReader(System.in));

            String userInput;
            String serverResponse;
            while ((userInput = stdin.readLine()) != null) {
                out.println(userInput);
                out.flush();

                serverResponse = in.readLine();
                System.out.println("Server total response: " + serverResponse);
            }
            // fecha-se a extremidade de escrita
            socket.shutdownOutput();              // vai avisar o server que houve end of file

            serverResponse = in.readLine();
            System.out.println("Server media response: " + serverResponse);

            // fecha-se a extremidade de leitura
            socket.shutdownInput();
            socket.close();

        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}