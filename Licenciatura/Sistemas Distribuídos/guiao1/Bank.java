class Bank {

    private static class Account {
        private int balance;
        Account(int balance) { this.balance = balance; }
        int balance() { return balance; }
        boolean deposit(int value) {
            balance += value;
            return true;
        }
    }

    // Our single account, for now
    private Account savings = new Account(0);

    // Account balance
    public int balance() {
        return savings.balance();
    }

    // Deposit
    boolean deposit(int value) {
        return savings.deposit(value);
    }

    class Ex2{

        public static void main(String args[]) throws InterruptedException {
            final int N = 10;
            Thread[] t = new Thread[N];
            Bank value = new Bank();
            // temos que colocar o Bank na main porque se colocarmos no método Increment2
            // estaríamos a criar uma conta para cada thread e nao a ter uma conta partilhada pelas threads

            for(int i=0; i<N;i++){
                t[i]=new Thread(new Deposit(value));
            }

            for(int i=0; i<N;i++){
                t[i].start();
            }

            for(int i=0; i<N;i++) {
                t[i].join();
            }

        }
    }

}
