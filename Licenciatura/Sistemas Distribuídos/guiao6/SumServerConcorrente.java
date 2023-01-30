import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

public class SumServerConcorrente {

    public static void main(String[] args) {
        try {
            ServerSocket ss = new ServerSocket(12345);

            while (true) {
                Socket socket = ss.accept();

                // vários clientes
                // SessionServerWorker é uma classe que tem um método run()
                Thread worker = new Thread(new SessionServerWorker(socket));
                worker.start();
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
