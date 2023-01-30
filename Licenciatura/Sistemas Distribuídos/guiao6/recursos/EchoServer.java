import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

/*
/////////////////////// IMPORTANTE /////////////////////////

Imaginemos que o cliente diz "olá". Queremos que o server diga "olá" de volta.
O server precisa de um IP e de uma porta para poder ler e responder às mensagens do cliente.
É criado um socket que é ligado a um IP e a uma porta para haver comunicação entre o cliente e o server.
Ele fica à escuta de todas as mensagens que lhe chegam.
Depois,  vai-se ligar a uma extermidade de escrita e vai enviar para lá os dados.
*/
public class EchoServer {

    public static void main(String[] args) {
        try {
            // o socket do server
            ServerSocket ss = new ServerSocket(12345);

            // condição true porque não interessam quantas conexões são feitas entre o cliente e o server
            while (true) {
                Socket socket = ss.accept();
                System.out.println("New cliente connection...");

                // para ler, eu quero ler da extremidade de leitura do socket
                // este buffer vai guardando as mensagens que chegam
                BufferedReader in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
                PrintWriter out = new PrintWriter(socket.getOutputStream());

                String line;
                // fica à espera de mensagens (vamos lendo de linha à linha)
                while ((line = in.readLine()) != null) {
                    System.out.println("Cliente message: " + line);
                    // o server retribuirá a mensagem (enviará a mensagem de volta)
                    out.println(line);
                    // temos de fazer um flush para garantir que a mensagem é, de facto, enviada
                    out.flush();
                }

                // fecha a extremidade de escrita
                socket.shutdownOutput();
                // fecha a extremidade de leitura
                socket.shutdownInput();
                // fecha o socket
                socket.close();
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
