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

  // COOPERATIVA:
  // Imaginemos que damos a volta a um supermercado porque estamos à procura de 3 items:
  //        O item1 tem quantidade suficiente para ser consumido.
  //        O item2 tem quantidade suficiente para ser consumido.
  //        O item3 não tem quantidade suficiente para ser consumido, então fica em espera.
  // O que é que fazemos? Ficamos à espera até o supermercado ser reabastecido. Entretanto, houve um supply do item3.
  // O que é que fazemos? Damos uma outra volta ao supermercado para ver se todos os items têm quantidade suficiente para agora serem consumidos.

    public void consume(Set<String> items) {
        lock.lock();

        int i = 0;
        for ( i < items.length ){
            Item it = this.get(items[i]);
            i++;
            // se o produto não existir, espero.
            while ( get(item).quantity == 0 ){
                get(item).cond.await();
                // houve um restock to produto. vou voltar a fazer uma nova ronda para verificar se ainda existem os outros produtos.
                i = 0;
            }
        }
        // se eu conseguir sair do primeiro for, então quer dizer que já verifiquei todos os produtos e todos os produtos existem.
        // agora vamos consumir os produtos.
        for ( String item : items )
                get(item).quantity--;
                get(item).cond.signalAll();
            }
        }
        lock.unlock();
    }
}
