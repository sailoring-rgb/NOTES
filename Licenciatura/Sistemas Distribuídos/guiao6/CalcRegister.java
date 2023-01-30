import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.concurrent.locks.ReentrantLock;

class CalcRegister{
    private ReentrantLock lock = new ReentrantLock();
    private int sum = 0;
    private int n = 0;

    public void add (int value){
        lock.lock();
        try{
            sum += value;
            n++;
        } finally {
            lock.unlock();
        }
    }

    public double avg(){
        lock.lock();
        try{
            if (n < 1){
                return 0;
            }
            return (double) sum/n;
        } finally {
            lock.unlock();
        }
    }
}