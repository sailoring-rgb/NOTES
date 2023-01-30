import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

// VERSÃO DA CALCREGISTER 

public class SessionServerWorker implements Runnable {

    private Socket socket;
    private CalcRegister register;

    public SessionServerWorker(Socket socket) {
        this.socket = socket;
        this.register = register;
    }

    public void run() {
        try {
            System.out.println("New connection established #" + Thread.currentThread().getId());
            BufferedReader in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            PrintWriter out = new PrintWriter(socket.getOutputStream());

            int sum = 0;
            String line;
            // lista com os números enviados pelo cliente
            List<Integer> nums = new ArrayList<>();
            while ((line = in.readLine()) != null) {
                try{
                    int value = Integer.parseInt(line);
                    sum += value;
                    register.add(value);
                } catch (NumberFormatException e){
                    // ignore invalid integers...
                }
                out.println(sum);
                out.flush();
            }
            out.println(register.avg());
            out.flush();
            
            socket.shutdownOutput();
            socket.shutdownInput();
            socket.close();

        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}

