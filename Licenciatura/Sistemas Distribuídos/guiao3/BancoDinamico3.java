import java.util.*;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;


///////////////////////////////////////// EXERCÍCIO 3 /////////////////////////////////////////

/*
    IMPORTANTE !!!!!

    readLock.lock();
        This means that if any other thread is writing (i.e. holds a write lock), then stop here until no other thread is writing.
        Once the lock is granted, no other thread will be allowed to write (i.e. take a write lock) until the lock is released.

    writeLock.lock();
        This means that if any other thread is reading or writing, stop here and wait until no other thread is reading or writing.
        Once the lock is granted, no other thread will be allowed to read or write (i.e. take a read or write lock) until the lock is released.

    Every time you want to read from the structure, take a read lock.
    Every time you want to write, take a write lock.
    This way whenever a write happens no-one is reading (you can imagine you have exclusive access),
    but there can be many readers reading at the same time so long as no-one is writing.

    PORTANTO,
    Quando estamos apenas a ler, não estamos a alterar os dados e, como tal, podemos ter mais do que uma leitura (apenas leituras) a acontecer.
    No entanto, o mesmo não acontece quando estamos a escrever. Nesse caso, apenas podemos ter uma escrita a ser feita.
*/

/*
    MÉTODOS PARA READLOCK: por exemplo, get, size.. métodos que NÃO ALTEREM os dados.
    MÉTODOS PARA WRITELOCK: por exemplo, put, add, remove... métodos que ALTEREM os dados.
*/ 

class Bank {

    //////////////////////////////////////////// ISTO É AO NÍVEL DA CONTA //////////////////////////////////////////////

    private static class Account {                           
        Lock lock = new ReentrantLock();
        private int balance;
        Account(int balance) { this.balance = balance; }
        int balance() { return balance; }
        boolean deposit(int value) {
            balance += value;
            return true;
        }
        boolean withdraw(int value) {
            if (value > balance)
                return false;
            balance -= value;
            return true;
        }
    }

    //////////////////////////////////////////// ISTO É AO NÍVEL DO BANCO ////////////////////////////////////////////

    private Map<Integer, Account> map = new HashMap<Integer, Account>();
    private int nextId = 0;

    // private Lock lock = new ReentrantLock();
    private ReadWriteLock lockRW = new ReentrantReadWriteLock();

    private Lock readlock = lockRW.readlock();
    private Lock writelock = lockRW.writelock();

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    // create account and return account id
    public int createAccount(int balance) {
        Account c = new Account(balance);
        writelock.lock();                   
        try{
            int id = nextId;            
            nextId += 1;
            map.put(id, c);
            return id;
        } finally{ writelock.unlock(); }
    }

    // close account and return balance, or 0 if no such account
    public int closeAccount(int id) {
        Account c;
        writelock.lock();                      
        c = map.remove(id); 

        if (c == null)
            return 0;

        c.readlock.lock(); 
        writelock.unlock();  
        int balance = c.balance();
        c.readlock.unlock();
        return balance;
    }

    // account balance; 0 if no such account
    public int balance(int id) {
        Account c;
        readlock.lock();
        c = map.get(id);

        if (c == null)
            return 0;

        c.readlock.lock();
        readlock.unlock();                        // assim garantimos que, até fazermos o lock da conta, mais nenhuma thread pode aceder ao banco
        int balance = c.balance();
        c.readlock.unlock();
        return balance;
    }

    /*
        Isto evita o quê? Imaginemos este cenário:
                      Thread 1 faz o método balance.
                      Thread 2 faz o método closeAccount.
        Se não fizessemos o lock.unlock() depois do c.lock.lock(), então a Thread 2 poderia apagar a conta e, consequentemente,
        já não poderíamos fazer c.balance() porque a conta c já não existe.
    */


    // deposit; fails if no such account
    public boolean deposit(int id, int value) {
        Account c;
        readlock.lock();                   // este lock é para proteger a estrutura do banco
        c = map.get(id);

        if (c == null)
            return false;

        c.writelock.lock();                 // este lock é para proteger a estrutura da conta
        readlock.unlock();                  // já obtive o id da conta, então não preciso mais de aceder aos "dados" do banco (map) -- isto para ser mais rápido
        boolean deposit = c.deposit(value);
        c.writelock.unlock();
        return deposit;
    }

    // withdraw; fails if no such account or insufficient balance
    public boolean withdraw(int id, int value) {
        Account c;

        readlock.lock();
        c = map.get(id);

        if (c == null)
            return false;

        c.writelock.lock();
        readlock.unlock();
        boolean withdraw = c.withdraw(value);
        c.writelock.unlock();
        return withdraw;
    }

    // transfer value between accounts;
    // fails if either account does not exist or insufficient balance
    public boolean transfer(int from, int to, int value) {
        Account cfrom, cto;

        readlock.lock();                 // lock do banco
        cfrom = map.get(from);
        cto = map.get(to);

        if (cfrom == null || cto ==  null)
            return false;

        cfrom.lockRW.lock();
        cto.lockRW.lock();
        readlock.unlock();
        cfrom.lockRW.unlock();
        cto.lockRW.unlock();
        boolean result = cfrom.withdraw(value) && cto.deposit(value);
        return result;
    }

    /*
    Ao nível das contas, utilizamos apenas um lock e não um lock de escrita porque, ao nível do banco, estamos a fazer um lock de leitura. Ora,
    isso quer dizer que várias threads (para leitura) podem entrar. Deste modo, se houvesse uma transferência da conta A para a conta B e outra transferência
    da conta B para a conta A, isto provocaria um deadlock. Porquê? Porque ambas as transferências aconteceram ao mesmo tempo, o que não era suposto.
    */

    // sum of balances in set of accounts; 0 if some does not exist
    public int totalBalance(int[] ids) {
        Account[] accs = new Account[ids.length];
        readlock.lock();
        int total = 0;
        for (int i : ids) {
            accs[i] = map.get(i);
            accs[i].readlock.lock();
        }
        readlock.unlock();
        
        for(int i : ids){
            if (accs[i] == 0)
                return false;
        }

        for(int i : ids) {
            total += accs[i].balance();
            accs[i].readlock.unlock();
        }
        return total;
  }
}