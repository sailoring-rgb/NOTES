class ServerWorker implements Runnable {
    private Socket socket;
    private ContactManager manager;

    public ServerWorker(Socket socket, ContactManager manager) {
        this.socket = socket;
        this.manager = manager;
    }

    //@TODO
    public void run() {
        try {
            DataInputStream in = new DataInputStream( new BufferedInputStream(this.socket.getInputStream()));
            boolean open = true;

            while(open) {
                Contact c = Contact.deserialize(in);

                if(c == null)
                    open = false;
                else manager.update(c);
            }
            socket.shutdownInput();
            socket.shutdownOutput();
            socket.close();

        } catch (IOException e){
            e.printStackTrace();
        }
    }
}