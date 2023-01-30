import java.io.*;
import java.net.Socket;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

// A questão é por exemplo o cliente manda a mensagem1 "olá", depois manda a mensagem2 "hola" e depois a mensagem3 "hello".
// O que acontece é que temos de garantir que estas mensagens são respondidas pela ordem correta.

// As threads leram do socket e guardaram as mensagens numa estrutura partilha de queues.
// Deste modo, a thread1 responderá às mensagens armazenadas na queue1, a thread2 responderá às mensagens armazenadas na queue2, por aí em diante.
// Quando as queues estiverem vazias, funcionará como um buffer em que se tem de esperar que seja preenchida por novas mensagens.
// Por isso, podemos usar uma condition.

public class Demultiplexer implements AutoCloseable{
    
    private TaggedConnection tagged;
    private ReentrantLock lock = new ReentrantLock();
    private Map<Integer, Entry> map = new HashMap<>();
    private IOException exception = null;

    // É uma entrada.
    private class Entry{
        // Conta quantos estão à espera.
        int waiters = 0;
        // A estrutura partilhada onde estão todas as queues para cada tag (Integer).
        Queue<byte[]> queue = new ArrayDeque<>();
        // Permitirá esperar por novas mensagens caso a queue esvazie.
        Condition cond = lock.newCondition();
    }

    public Demultiplexer(TaggedConnection connection) throws IOException{
        this.tagged = connection;
    }

    public void start(){
        new Thread(() -> {
            try {
                while(true){
                    TaggedConnection.Frame frame = tagged.receive();
                    lock.lock();
                    try{
                        Entry entry = map.get(frame.tag);
                        if(entry == null){
                            entry = new Entry();
                            map.put(frame.tag, Entry);
                        }
                        entry.queue.add(frame.data);
                        entry.cond.signal();
                    }
                    finally { lock.unlock(); }
                }
            }
            catch(IOException e){
                exception = e;
            }
        }).start();
    }

    public void send(TaggedConnection.Frame frame) throws IOException{
        tagged.send(frame);
    }

    public void send(int tag, byte[] data) throws IOException{
        tagged.send(tag,data);
    }

    public byte[] receive(int tag) throws IOException, InterruptedException{
        lock.lock();
        Entry entry;
        try{
            entry = map.get(tag);
            if(entry == null){
                entry = new Entry();
                map.put(tag, entry);
            }
            entry.waiters++;
            while(true){
                if(!entry.queue.isEmpty()){
                    entry.waiters--;
                    byte[] reply = entry.queue.poll();
                    if(entry.waiters == 0 && entry.queue.isEmpty())
                        map.remove(tag);
                    return reply;
                }
                if(exception != null){ throw exception; }
                entry.cond.await();
            }
        }
        finally{ lock.unlock(); }
    }

    public void close() throws IOException{
        tagged.close();
    }
}