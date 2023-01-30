import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

class Bank {

    private static class Account {
        private int balance;

        Account(int balance){
            this.balance = balance;
        }
        int balance(){
            return balance;
        }
        boolean deposit(int value){
            balance += value;
            return true;
        }
        boolean withdraw(int value){
            if (value > balance)
                return false;
            balance -= value;
            return true;
        }
    }

    // Bank slots and vector of accounts
    private int slots;
    private Account[] av;             // são várias contas

    // Bank mutex
    private ReentrantLock l;          // tem um contador interno que conta quantas vezes ocorreu o lock e quantas vezes terá de ser libertado

    public Bank(int n)
    {
        l = new ReentrantLock();
        slots=n;
        av = new Account[slots];
        for (int i=0; i<slots; i++) av[i]=new Account(0);
    }

    // EXERCÍCIO 1

    // Account balance
    public int balance(int id) {
        if (id < 0 || id >= slots)
            return 0;
        l.lock();                   // garante que não há sobreposição de escrita das threads nem que há repetição de valores antigos
        try {
            return av[id].balance();
        } finally {                    // garante que o lock é libertado mesmo que ocorra algum erro
            l.unlock();
        }
    }

    // Deposit
    public boolean deposit(int id, int value) {
        if (id < 0 || id >= slots)
            return false;
        l.lock();
        try {
            return av[id].deposit(value);
        } finally {
            l.unlock();
        }
    }

    // Withdraw; fails if no such account or insufficient balance
    public boolean withdraw(int id, int value) {
        if (id < 0 || id >= slots)
            return false;
        l.unlock();
        try {
            return av[id].withdraw(value);
        } finally {
            l.unlock();
        }
    }

    // EXERCÍCIO 2

    // Quando eu faço diretamente da thread, dá correto. Quando eu chamo apenas o método withdraw, já dá erro.

    public boolean transfer (int from, int to, int value){
        if ( (from < 0 || from >= slots) && (to < 0 || to >= slots) )
            return false;

        l.lock();                        // lock para o banco

        av[from].l.lock();               // lock para a conta from
        av[to].l.lock();                 // lock para a conta to

        l.unlock();                      // unlock para o banco

        boolean with = withdraw(from, value);
        boolean dep = deposit(to, value);
        
        av[from].l.unlock();
        av[to].l.unlock();

        return with && dep;
    }

    public int totalBalance(){
        int sum = 0;

        for(int i = 0; i < slots; i++)
            av[i].l.lock();

        for(int i = 0; i < slots; i++) {
            sum += av[i].balance();
            av[i].l.unlock();
        }
        return sum;
    }

}

