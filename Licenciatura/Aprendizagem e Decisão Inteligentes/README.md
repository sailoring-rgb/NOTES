# Aprendizagem e Decisão Inteligentes

#
![Image 29-05-2022 at 5 09 PM](https://user-images.githubusercontent.com/62114404/170879855-09342a2a-7ec8-4e77-98fa-54bb0e28f534.jpg)
![Image 29-05-2022 at 5 09 PM (1)](https://user-images.githubusercontent.com/62114404/170879867-1895a733-27e2-4a1d-b49f-e72263461319.jpg)

### Sistemas de Aprendizagem:

* Aprendizagem Não Supervisionada

Treinamos a máquina usando informações que não estão rotulados -> O algoritmo atua nestas infos sem orientação -> Objetivo: agrupar infos não rotuladas de acordo com semelhanças/diferenças.

* Aprendizagem supervisionada

	— <ins>Regressão</ins>: prever/estimar um valor numérico.\
	— <ins>Classificação</ins>: prever uma categoria/classe.

Treinamos (ou ensinamos) a máquina usando dados bem rotulados: dados que já estão marcados com a resposta correta. Depois a máquina recebe um novo dataset para que os dados de treino sejam analisados e produz um resultado correto a partir destes dados.

Os dados contém padrões -> Um algoritmo de Machine Learning encontra esses padrões e gera um modelo -> O modelo reconhece esses padrões (mesmo quando lhes são apresentados novos dados.


### Dataset de treino, teste e validação:

- <ins>Dataset de treino</ins>: usado para treinar o modelo.\
- <ins>Dataset de validação</ins>: usado para comparação de diferentes modelos e hiperparâmetros.\
- <ins>Dataset de teste</ins>: usado para provar que aquele modelo realmente funciona.

### Stratified Sampling:

A forma mais simples de criar um dataset de teste é selecionar uma parte dos dados aleatoriamente. A isto chamamos Simple Random Sampling. Este método é bom se o dataset for grande o suficiente; se não, estamos a enviesar os dados.

**Stratified Sampling** é um método de amostragem que reduz o erro de amostragem nos casos em que a população pode ser dividida em subgrupos. Realizamos este método dividindo a população em subgrupos homogéneos e aplicamos o Simple Random Sampling em cada subgrupo. Assim, o dataset de teste é representativo da população.

<img width="400" alt="Untitled 2" src="https://user-images.githubusercontent.com/62114404/170880318-6a6f94b2-e775-4a89-8ed5-b28dadd5f797.png">

Os dados são sorteados aleatoriamente, mas como existem mais azuis do que vermelhos, então são selecionados mais azuis do que vermelhos.

#

**(ACOMPANHAR OS SLIDES DA AULA 3)**

<ins>Perfect inverse correlation</ins>: quando uma variável sobe, a outra variável desce.

<ins>Moderate negative correlation</ins>: tal como temos pontos que estão muito próximos da reta, também temos alguns longe.

Quando há uma correlação positiva entre duas variáveis, quer dizer que estas duas variáveis se relacionam imenso. Quando uma aumenta, a outra também aumenta. Aliás, se o valor positivo entre ambas for muito elevado (quase +1), então pode-se considerar que ambas evidenciam os mesmos efeitos e, portanto, remover uma delas não causaria consequências nenhumas aos dados.

Se tivermos duas colunas altamente correlacionadas, é muito provável termos informação repetida. Então, não nos interessa manter todas as high-correlated features.

Se tivermos mais do que uma feature para um label, nós devemos selecionar aquelas que nos interessam. Esta seleção (feature selection) pode ser feita de vários métodos.

É preciso termos muitos dados para termos uma correlação correta. Quantos mais dados tivermos, mais correta será a nossa correlação, mais accurate será o nosso resultado.

Nós queremos que os nossos dados sejam distribuídos e, como tal, temos de normalizá-los. Isto para garantir que a ordem de grandeza dos dados não influencie os resultados.

Quando se converte uma string para nominal, o que o nodo faz é um rank. Ou seja, atribui um número a essa string (os filmes de categoria drama têm o valor 1 e os filmes de categoria aventura têm o número 2). O único problema é quando essas strings não são ordinais, i.e. não assumem uma ordem, e, assim, estamos a dizer que os filmes de drama são mais importantes que os de aventura, o que não é o caso. 

<img width="415" alt="2" src="https://user-images.githubusercontent.com/62114404/170880448-823dec73-9cbc-43db-97fd-8ca0ccce61b8.png">
 
Existem features que não nos dizem nada, das quais não podes retirar informação a partir delas. O que o feature engineering faz é desmontar uma feature para conseguirmos utilizar parte dessa informação que pode ser útil para outras features.

#
### REGRESSÃO LINEAR / LINEAR REGRESSION:

Um modelo de RL tenta explicar a relação entre 2 variáveis usando uma linha chamada linha de regressão (“best fitting straight line”).

A nossa variável independente (x) tenta prever o valor da nossa variável dependente (y).

A estratégia mais popular é chamada “least squares”.

![Image 29-05-2022 at 5 09 PM (2)](https://user-images.githubusercontent.com/62114404/170879879-4e2b3132-84a4-4e2c-a8e4-b09111a5c3de.jpg)
![Image 29-05-2022 at 5 09 PM (3)](https://user-images.githubusercontent.com/62114404/170879890-4804763f-2942-4f32-84cc-0b068e94105f.jpg)

#
(ACOMPANHAR OS SLIDES DA AULA 5)

### ÁRVORES DE DECISÃO

Os parâmetros são uma configuração interna do modelo. Os hiper-parâmetros são uma configuração externa feita por nós.

* Random Forest:

Combina a simplicidade das árvores de decisão com a flexibilidade que lhes falta        = +accuracy.

1. Criar um “bootstrap” dataset: escolhemos amostras do nosso dataset original de forma aleatória; este novo dataset tem que ter o mesmo tamanho que o original, podendo conter amostras repetidas.
2. Criamos uma árvore de decisão com o novo dataset, mas usamos um conjunto de colunas aleatórias para cada passo. 

Os dados que ficam de fora denominam-se por out-of-bag dataset.

#
### REDES NEURONAIS

As sinapses são o local onde as redes aprendem.

Temos neurónio de entrada e outro de saída, no mínimo. 

O modelo está demasiado exposto àquilo que os dados representam. O modelo criado aprendeu a imitar aquilo que os dados representam, mas não tem capacidade para fazer previsões adequados sobre o futuro porque não tem precisão sobre experiências, sobre aquilo que acontecia no passado. 

![Image 29-05-2022 at 5 09 PM (4)](https://user-images.githubusercontent.com/62114404/170879907-a420ccbb-daae-4b08-8430-978423badca2.jpg)

Quantos mais layers tivermos, mais “esmioçado” vai ser o conteúdo — mais contribuímos para a aprendizagem. No entanto, chegamos a um certo ponto em que adicionar mais layers, já não é rentável, só prejudica a aprendizagem.

* Signed:

	- [0,1]
	- vanish gradient problem -> problema de aprendizagem curto.

![Image 29-05-2022 at 5 09 PM (5)](https://user-images.githubusercontent.com/62114404/170879935-fec26fc2-5a1b-4902-8155-597c1cc50cca.jpg)

* ReLU:

	- ReLU(x) = max(0,x)
	- VGP

![Image 29-05-2022 at 5 09 PM (6)](https://user-images.githubusercontent.com/62114404/170879943-e0243708-2085-4307-a5db-c3eafdaa4df7.jpg)

* LeaRy ReLU:

	- Leaky ReLU(x) = max(0.1x,x)

![Image 29-05-2022 at 5 09 PM (7)](https://user-images.githubusercontent.com/62114404/170879953-be0b923e-1eb3-4057-8f49-f9ea086b5260.jpg)
