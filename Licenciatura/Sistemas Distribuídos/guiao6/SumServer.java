import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

public class SumServer {

    public static void main(String[] args) {
        try {
            ServerSocket ss = new ServerSocket(12345);

            while (true) {
                Socket socket = ss.accept();
                System.out.println("New cliente connection...");

                BufferedReader in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
                PrintWriter out = new PrintWriter(socket.getOutputStream());

                String line;
                int total = 0;
                int n = 0;
                while ((line = in.readLine()) != null) {
                    // imprime a mensagem do cliente
                    System.out.println("Cliente message: " + line);

                    // converte string para inteiro
                    int num = Integer.parseInt(line);
                    // calcula a soma de todos os inteiros enviados pelo cliente até agora
                    total += num;
                    // incrementa mais um número enviado
                    n++;

                    out.println(total);
                    // para garantir que a mensagem é enviada
                    out.flush();
                }
                // existe end of file quando a extremidade de escrita do CLIENTE for fechada.
                // ou seja, quando o ficheiro do cliente fizer socket.shutdownOutput()
                out.println((double) total/n);
                out.flush();

                socket.shutdownOutput();
                socket.shutdownInput();
                socket.close();
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
