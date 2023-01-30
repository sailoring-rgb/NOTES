import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;

public class SessionServerWorker implements Runnable {

    private Socket socket;

    public SessionServerWorker(Socket socket) {
        this.socket = socket;
    }

    public void run() {
        try {
            BufferedReader in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            PrintWriter out = new PrintWriter(socket.getOutputStream());

            String line;
            // lista com os números enviados pelo cliente
            List<Integer> nums = new ArrayList<>();
            while ((line = in.readLine()) != null) {
                nums.add(Integer.parseInt(line));
                out.println(nums.stream().reduce(0, Integer::sum));
                out.flush();
            }

            out.println(nums.stream().reduce(0, Integer::sum) / nums.size());
            out.flush();

            socket.shutdownOutput();
            socket.shutdownInput();
            socket.close();

        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}

