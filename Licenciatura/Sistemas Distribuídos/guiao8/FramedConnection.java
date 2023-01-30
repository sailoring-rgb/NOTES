public class FramedConnection implements AutoCloseable{

    private final Socket s;
    private final DataInputStream is;
    private final DataOutputStream os;
    private final Lock wlock = new ReentrantLock();
    private final Lock rlock = new ReentrantLock();

    // Quando o conteúdo é lido por uma thread, este é consumido. Deixa de estar lá.

    public FramedConnection(Socket socket) throws IOException{
        this.s = socket;
        this.is = new DataInputStream(new BufferedInputStream(socket.getInputStream()));
        this.os = new DataOutputStream(new BufferedOutputStream(socket.getOutputStream()));
    }

    public void send(byte[] data) throws IOException{
        try{
            wlock.lock();
            os.writeInt(data.length);
            os.write(data);
            os.flush();
        } finally {
            wlock.unlock():
        }
    }

    public byte[] receive() throws IOException{
        byte[] data;
        try{
            rlock.lock();
            data = new byte[is.readInt()];
            is.readFully(data); // tenta ler o máximo que está associado ao sistema operativo do socket e minimiza o consumo de bytes a serem lidos (é uma otimização)
        } finally {
            rlock.unlock():
        }
        return data;
    }

    public void close() throws IOException{
        this.is.close();
        this.os.close();
    }
}