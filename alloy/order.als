module order[exactly item]
/*
'exactly' перед item говорит о том, что сигнатура item должна всегда
включать максимальное количество элементов допустимое текущей конфигурацией поиска моделей.

Например:
  `run {} for 5 item`
  обычно говорит о том, что Alloy Analizer будет просматривать модели с
  числом элементов в сигнатуре 'item' от 0 до 5.
  Но, если мы подключим этот модуль 'open order[item]', то
  количество атомов в сигнатуре 'item' всегда будет ровно 5.

Почему для модуля порядка нужно всегда максимальное наполнение сигнатуры?
Не вдаваясь в тонкости, можно сказать, что при неполной сигнатуре возможны
противоречия в логических формулах модели, что приведёт к неверным результатам
моделирования.

Детально можно об этом почитать в книге Daniel Jackson "Software abstractions"
*/

/*
Служебное слово 'private' говорит о том, что сигнатура 'Order' и связанные с ней
отношения не будут видны в тех модулях, в которые будет подключаться данный модуль.
Действительно, зачем пользователям видеть детали реализации?
*/

/*
'one' перед 'sig' говорит о том, что в сигнатуре 'Order' будет всегда и ровно один атом.
Это аналог синглетона в ООП языках программирования, типа Java, C++ и др.

'First', 'Last', 'Next' и 'Prev' - это всё отношения.

Особенностью Alloy является то, что отношения можно определять только вместе с сигнатурой,
как методы в языке Java. В Java нет свободных функций (в отличии от C++, например).

Так же и здесь. Все отношения должны быть привязаны к какой-либо сигнатуре и первый элемент
в этих отношениях - это атом из этой сигнатуры.

В нашем случае сигнатура 'Order' чисто вспомогательная, примерно как класс 'Main' в Java для
статичного метода 'main'.
*/

private one sig Order {
  First: set item, -- первый элемент
  Last: set item, -- последний элемент
  Next: item -> item, -- отношение следования
  Prev: item -> item -- отношение предшествования
  /*
  'Last' и 'Prev' - немного избыточны, так как определяются через 'First' и 'Next':
  'Last = item - item.(~Next)' - 'Last' - это все элементы 'item' минус все предшествующе элементы 'item'
  'Prev = ~Next' - 'Prev' это обращение/инверсия отношения 'Next'
  'Last' и 'Prev' просто позволят удобнее и понятнее записать дальнейшие предикаты и функции
  */
} {
  /*
  блок, который идёт сразу за объявлением сигнатуры, это неявный блок 'fact', который
  задаёт свойства отношений определённых на этой сигнатруре.
  В использовании этих отношений в блоке неявно будет подразумеваться сигнатура 'Order'
  'sig A { F: ... } { ... F ...}' то же самое, что:
  'sig A { F: ... } .... .... fact { for all a: A { ... a.F ... } }

  Подробнее можно почитать в книге Daniel Jackson "Software abstractions"

  Такая форма записи просто упрощает запись. Она в чём-то похожа на определение методов
  в теле определение класса в C++, когда не нужно перед именем метода в объявлении
  писать имя класса, в отличии от определение вне тела определения класса, когда нужно
  писать полное имя со всемы квалификаторами.
  */

  one First -- единственный первый элемент
  one Last -- единственный второй элемент
  First != Last -- они не равны
  no Last.Next -- у последнего элемента нет следующего
  no Next.First -- у первого - предыдущего
  all i: item - Last { -- для всех кроме последнего
    one i.Next -- единственный последующий
    /*
    Оператор '^' - это транзитивное замыкание бинарного отношения.
    Например, отношение 'A = {1->2, 2->3}', тогда транзитивное замыкание даст:
    '^A = {1->2, 2->3, 1->3}', то есть добавит в отношение все пары достижимости
    элементов для каждого элемента.
    */
    Last in i.^Next -- и от этого элемента 'i' в цепочке следующих за ним есть элемент 'Last'
                    -- причем он же должен оказаться и последним в этой цепочке.
                    -- (вопрос для самостоятельного размышления: почему 'Last' обязательно
                    --  в этих цепочках последующих всегдя будет оказываться финальным элементом?)
  }
  /*
  'all i,j: item ...' - говорит: для всех сочетаний элементов 'i' и 'j' из 'item'
  'all disj i,j: item ...' - говорит: для всех сочетаний различных элементов 'i' и 'j' из 'item'
                             'disj' от 'disjoint'
  */
  all disj i,j: item - Last |  i.Next != j.Next -- для всех различных 'i' и 'j' последующие не должны
                                                -- совпадать
  Prev = ~Next -- отношение предшествования - это обращение отношения следования
               -- 'Next' - это множество пар 'предыдущий' -> 'следующий'
               -- а 'Prev' - 'следующий' -> 'предыдущий'
}

/*
Теперь API модуля для пользователя. Основные функции и предикаты.
*/

fun next : item->item { Order.Next }
fun prev : item->item { Order.Prev }
fun first : one item { Order.First }
fun last : one item { Order.Last }
/*
'this/next' вместо просто 'next' из-за того, что Alloy, начиная с 5 версии ко всем модулям
неявно подключает модуль 'Integer', где 'next' уже определён. Поэтому приходится указывать
явно полное имя с 'this'.
Как вариант, можно выбрать другое имя, но 'next' мне показалось наиболее удобным.
*/
fun all_greater : item->item { ^this/next }
fun all_smaller : item->item { ^this/prev }
fun minimum(items : set item) : lone item { items - items.all_greater }
fun maximum(items : set item) : lone item { items - items.all_smaller }
pred less [lhs, rhs: item] { lhs in rhs.all_smaller }
pred greater [lhs, rhs: item] { lhs in rhs.all_greater }
pred less_or_equal [lhs, rhs: item] { lhs = rhs or less[lhs, rhs] }
pred greater_or_equal [lhs, rhs: item] { lhs = rhs or greater [lhs, rhs] }

/*
Предикат корректности определений
*/
assert module_is_correct {
  next.this/prev in iden -- последующий, потом предыдущий - это сам в себя : a -> b join b -> a = a -> a
  this/prev.next in iden -- то же самое только предыдущий, потом последующий
  item - first = first.all_greater -- все, кроме первого, больше первого
  item - last = last.all_smaller -- все, кроме последнего, меньше последнего
  no first.all_smaller -- нет элемента меньше первого
  no last.all_greater -- нет элемента больше последнего
  all i : item | lone i.next -- последующих элементов меньше или равно одному
  all i : item | lone i.prev -- то же самое для предыдущих
  all i : item | i not in i.all_greater -- элемент не больше самого себя
  all i : item | i not in i.all_smaller -- не меньше самого себя
  all i : item | (i != first) implies (one i.prev) -- у всех, кроме первого, есть единственный предыдущий
  all i : item | (i != last) implies (one i.next) -- у всех, кроме последнего, есть единственный последующий
  item = first.*next -- из первого элемента достижимы все через отношение следования
  item = last.*prev -- у последнего любой элемент в предшествующих через отношение предшествования
  all disj i,j:item | less[i, j] or less[j, i] -- для любых различных j, i либо i меньше j, либо j меньше i
  no disj i,j:item | less[i, j] and greater[i, j] -- для любых различных i и j, либо i меньше j, либо больше
  all disj i,j,k:item | less[i, j] and less[j, k] implies less[i, k] -- i < j и j < k, следовательно i < k
  all disj i,j,k:item | greater[i, j] and greater[j, k] implies greater[i, k] -- то же самое для больше
  all i,j:item | less_or_equal[i,j] and greater_or_equal[i,j] implies i=j -- если для любых i и j i<= j и j <= i, то они равны
  all disj i,j,k:item | less[i, j] and less[j, k] implies minimum[i + j + k] = i -- для всех различных i,j,k: i < j и j < k, то минимальный - это i
  all disj i,j,k:item | less[i, j] and less[j, k] implies maximum[i + j + k] = k -- аналогично для максимального
}

-- можно глянуть примеры получающихся моделей
example: run {} for exactly 4 item

-- тут проверка, что условие корректности функций модуля выполняется для всех моделей
-- с размером сигнатур вплоть до 7 элементов включительно
validate: check module_is_correct for 7
