import java.util.*;
import java.sql.SQLOutput;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

class Warehouse {
    private Map<String, Product> map =  new HashMap<String, Product>();

    private Lock lock = new ReentrantLock();
    // private Condition cond = lock.newCondition();
    // se tivessemos a condition aqui então esta estaria associada ao lock global ( ao lock de todos os produtos )

    private class Product {
        int quantity = 0;
        private Condition cond = lock.newCondition();
        // esta condition é associada ao lock do produto e não ao lock global 
        // é pertinente termos uma condition para cada item porque assim, ao fazer consume de algum produto, não acordamos (com o signalAll)
        // desnecessariamente as threads de outro produto qualquer
    }

    private Product get(String item) {
        Product p = map.get(item);
        if (p != null) return p;
        p = new Product();
        map.put(item, p);
        return p;
    }

    public void supply(String item, int quantity) {
        lock.lock();

        // como só vamos abastecer o produto, não precisamos de colocar nada em espera
        Product p = get(item);
        p.quantity += quantity;
        p.cond.signalAll();

        lock.unlock();
    }

    // EGOÍSTA:
    // Erro se faltar um...
    public void consume(Set<String> items) {
        lock.lock();

        for ( String item : items ){

            // quando a quantidade do produto for igual a 0 (faltar o produto) então colocamos em espera
            if ( get(item).quantity == 0 )
                while ( get(item).quantity == 0 )
                    get(item).cond.await();
            else {
                // quando alguém fizer supply (abastecer) do produto então sinalizamos as threads e retiramos o produto
                get(item).cond.signalAll();
                get(item).quantity--;
            }
        }
        lock.unlock();
    }
    
}