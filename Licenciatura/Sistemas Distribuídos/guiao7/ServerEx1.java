public class ServerEx1 {
    
    public static void main (String[] args) throws IOException {
        ServerSocket serverSocket = new ServerSocket(12345);
        ContactManager manager = new ContactManager();

        while(true){
            Socket socket = serverSocket.accept();
            Thread worker = new Thread(new ServerWorker(socket,manager));
            worker.start();
        }
    }
}