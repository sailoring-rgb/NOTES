import java.util.*;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;


///////////////////////////////////////// EXERCÍCIO 1 /////////////////////////////////////////


class Bank {

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

    private Map<Integer, Account> map = new HashMap<Integer, Account>();
    private int nextId = 0;
    private Lock lock = new ReentrantLock();

    // create account and return account id
    public int createAccount(int balance) {
        Account c = new Account(balance);
        lock.lock();                      // ainda não existe conta; como tal, o que nós queremos proteger é o banco e não uma conta
        try{
            int id = nextId;              // porque estão a ser partilhados o id e o map (com os dados de todas as contas daquele banco)
            nextId += 1;
            map.put(id, c);
            return id;
        } finally{ lock.unlock(); }
    }

    // close account and return balance, or 0 if no such account
    public int closeAccount(int id) {
        Account c;
        lock.lock();                            // tem de ser protegido o banco
        c = map.remove(id);                     // estão a ser partilhados o id e o map 

        if (c == null)
            return 0;

        c.lock.lock();
        lock.unlock();                        // assim garantimos que, até fazermos o lock da conta, mais nenhuma thread pode aceder ao banco
        int balance = c.balance();
        c.lock.unlock();
        return balance;
    }

    // account balance; 0 if no such account
    public int balance(int id) {
        Account c;
        lock.lock();
        c = map.get(id);

        if (c == null)
            return 0;

        c.lock.lock();
        lock.unlock;                        // assim garantimos que, até fazermos o lock da conta, mais nenhuma thread pode aceder ao banco
        int balance = c.balance();
        c.lock.unlock();
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
        lock.lock();                   // este lock é para proteger a estrutura do banco
        c = map.get(id);

        if (c == null)
            return false;

        c.lock.lock();                 // este lock é para proteger a estrutura da conta
        lock.unlock();                 // já obtive o id da conta, então não preciso mais de aceder aos "dados" do banco (map) -- isto para ser mais rápido
        boolean deposit = c.deposit(value);
        c.lock.unlock();
        return deposit;
    }

    // withdraw; fails if no such account or insufficient balance
    public boolean withdraw(int id, int value) {
        Account c;

        lock.lock();
        c = map.get(id);

        if (c == null)
            return false;

        c.lock.lock();
        lock.unlock();
        boolean withdraw = c.withdraw(value);
        c.lock.unlock();
        return withdraw;
    }

    // transfer value between accounts;
    // fails if either account does not exist or insufficient balance
    public boolean transfer(int from, int to, int value) {
        Account cfrom, cto;

        lock.lock();                 // lock do banco
        cfrom = map.get(from);
        cto = map.get(to);

        if (cfrom == null || cto ==  null)
            return false;

        cfrom.lock.lock();
        cto.lock.lock();
        lock.unlock();
        boolean result = cfrom.withdraw(value) && cto.deposit(value);
        cfrom.lock.unlock();
        cto.lock.unlock();
        return result;
    }

    // sum of balances in set of accounts; 0 if some does not exist
    public int totalBalance(int[] ids) {
        Account[] accs;
        lock.lock();
        int total = 0;
        for (int i : ids) {
            accs[i] = map.get(i);
            accs[i].lock.lock();
        }
        lock.unlock();
        
        for(int i : ids) {
            total += accs[i].balance();
            accs[i].lock.unlock();
        }
        return total;
  }
}