import java.net.ServerSocket;
import java.net.Socket;

import static TaggedConnection.Frame;

/*
                Cliente
                   |
            FramedConnection       Threads that read
                   |             /
                   | -----------
                   |             \
                Server             Threads that write
*/

public class SimpleServerWithWorkers {
    final static int WORKERS_PER_CONNECTION = 3;

    private ReadWriteLock lockRW = new ReentrantReadWriteLock();
    private Lock readlock = lockRW.readlock();
    private Lock writelock = lockRW.writelock();

    public static void main(String[] args) throws Exception {
        ServerSocket ss = new ServerSocket(12345);

        // O socket não pode ser privado de modo a que haverá um controlo de leitura e um controlo de escrita
        // Como muitas threads estão a fazer a leitura, então temos de criar um lock só para leitura
        // Como muitas threads estão a fazer a escrita, então temos de criar um lock só para escrita

        while(true) {
            Socket s = ss.accept();
            FramedConnection c = new FramedConnection(s);
        
            Runnable worker = () -> {
                try (c) {
                    for (;;) {
                        // Isto é que cada worker terá de fazer:
                        readlock.lock();
                        byte[] b = c.receive();
                        writelock.lock();
                        String msg = new String(b);
                        readlock.unlock();
                        System.out.println("Replying to: " + msg);
                        c.send(msg.toUpperCase().getBytes());
                        writelock.unlock();
                    }
                } catch (Exception ignored) { }
            };

            // Para cada conexão (são 3), ele cria N threads
            for (int i = 0; i < WORKERS_PER_CONNECTION; ++i)
                new Thread(worker).start();
        }
    }
}