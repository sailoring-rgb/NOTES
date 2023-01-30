import java.sql.SQLOutput;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

///////////////////////////////////////// VERSÃO 1 (EXERCÍCIO 1.1) /////////////////////////////////////////

/*
    IMPORTANTE !!!!!

    O await implicitamente já faz unlock. O lock é libertado atomicamente e a execução da thread é suspendida.

    A signalAll acorda todas as threads e estas competem pelo lock, ganhando a que se “despachar” primeiro. Ou seja,
    se sinalizou todas as threads, mesmo se não “ganharam” o lock em primeiro lugar, todas saem do estado wait-set e passam a esperar pelo lock.

    Para verificar as condições, precisamos sempre de um ciclo em vez de um if. Isto porquê? Às vezes há bugs no sistema que levam a que
    as threads saiam do await sem ter havido um signalAll. Utilizando um ciclo, o programa vai estar sempre a verificar se a thread está no await.
*/


class Barrier {

    // Precisamos de uma condição e, para termos uma condição, precisamos de um lock.
    private Lock lock = new ReentrantLock();
    private Condition cond = lock.newCondition();

    private int contador = 0;
    private int N;

    private boolean open = false;

    Barrier (int N) {
        this.N = N;
    }

    void await() throws InterruptedException {
        lock.lock();

        contador++;

        if (contador < N) {
            while (contador < N)
                cond.await();
        }
        else {
            cond.signalAll();
        }
        lock.unlock();
    }

}