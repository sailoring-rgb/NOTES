import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import static java.util.Arrays.asList;

// EXERCÍCIO 4

class ContactManager {
    private HashMap<String, Contact> contacts;
    private ReentrantLock lock;

    public ContactManager() {
        contacts = new HashMap<>();
        // example pre-population
        contacts.update(new Contact("John", 20, 253123321, null, asList("john@mail.com")));
        contacts.update(new Contact("Alice", 30, 253987654, "CompanyInc.", asList("alice.personal@mail.com", "alice.business@mail.com")));
        contacts.update(new Contact("Bob", 40, 253123456, "Comp.Ld", asList("bob@mail.com", "bob.work@mail.com")));
    }


    // @TODO
    public void update(Contact c){
        lock.lock();
        try{
            contacts.put(c.getName(),c);
        } finally {
            lock.unlock();
        }
    }

    // @TODO
    public ContactList getContacts(){
        lock.lock();
        try{
            ContactList l = new ContactList();
            for(Contact c: contacts.values())
                l.add(c);
        } finally {
            lock.unlock();
        }
    }
}

class ServerWorker implements Runnable {
    private Socket socket;
    private ContactList contactList;

    public ServerWorker(Socket socket, ContactManager manager) {
        this.socket = socket;
        this.contactList = contactList;
    }

    //@TODO
    public void run() {
        try {
            DataInputStream in = new DataInputStream( new BufferedInputStream(this.socket.getInputStream()));
            boolean open = true;

            while(open) {
                contactList.getContacts(out);
            }
            socket.shutdownInput();
            socket.shutdownOutput();
            socket.close();

        } catch (EOFException e) {
            System.out.println("Connection closed");
        } catch (IOException e) {
            e.printStackTrace();
        } 
    }

}



public class ServerEx1 {
    
    public static void main (String[] args) throws IOException {
        ServerSocket serverSocket = new ServerSocket(12345);
        this.contactList = contactList;

        for(int i = 0; i < contactList.size(); i++){
            Socket socket = serverSocket.accept();
            Thread worker = new Thread(new ServerWorker(socket, contactList));
            worker.start();
        }
    }

}
