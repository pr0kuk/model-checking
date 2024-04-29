--------------------------------- MODULE list ---------------------------------
EXTENDS Integers, TLC, Sequences
Elem_num == 5
Status == {"in_list", "deleted"}
Number == 1..Elem_num
Prev_v == 1..Elem_num
Next_v == 1..Elem_num
Elems == [i: Number, p: Prev_v, n: Next_v, st: Status]

ELM(number, prev, next, status) == [i |-> number, p |-> prev, n |-> next, st |-> status]
fPrev(i) == Elems[i].p
fNext(i) == Elems[i].n
ElemWithNumber(i) == ELM(i, fPrev(i), fNext(i), "in_list")

IsInList(elem) ==
    LET ST == "in_list"
    IN ST \in Status /\ elem.st = ST

IsDeleted(elem) ==
    LET ST == "deleted"
    IN ST \in Status /\ elem.st = ST

NextElemNumber(elem) == elem.next
PrevElemNumber(elem) == elem.prev

ForEach(op(_,_), acc) ==
    LET getelem[i \in Number] ==
        IF i = Elem_num THEN acc
        ELSE
            LET elem == ElemWithNumber(i)
            IN op(elem, getelem[NextElemNumber(elem)])
    IN getelem[1]

AllElems == ForEach(LAMBDA b, acc: {b} \union acc, {})
AllListElems == ForEach(LAMBDA b, acc: IF IsInList(b) THEN {b} \union acc ELSE acc, {})
AllDeleted == ForEach(LAMBDA b, acc: IF IsDeleted(b) THEN {b} \union acc ELSE acc, {})




(*--fair algorithm list
variables
    first \in 1..Elem_num,
    last \in 1..Elem_num,
define
    \* invariants
    HavingHead == (Elems[first].st = "in_list")
    HavingTail == (Elems[last].st = "in_list")
    Acyclicity == ~(first = last)
    Linearity == \A e \in AllListElems: ~(e.n = e.p)
    LastIsTail == (Elems[last].n = -1)
    FirstIsHead == (Elems[first].p = -1)
    DeletedUnconnectivity == 
        \A e \in AllDeleted:
            (Elems[e].n = -1) /\ (Elems[e].p = -1)
    Acyclicity2 ==
        \A e \in AllListElems:
            (~(Elems[e].n = e.i)) /\ (~(Elems[e].p = e.i))
    Connectivity ==
        (\A e \in AllListElems \ Elems[first]: Elems[e].p \in Number)
        /\
        (\A e \in AllListElems \ Elems[last]: Elems[e].n \in Number)
   DoubleLinkage ==
        (\A e \in AllListElems \ Elems[first]: Elems[Elems[e].p].n = e.i)
        /\
        (\A e \in AllListElems \ Elems[last]: Elems[Elems[e].n].p = e.i)
   \*Connectivity2
   
end define


\*procedure pop_back() 
\*begin
\*end procedure;
\*
\*procedure pop_front() 
\*begin
\*end procedure;
\*
\*procedure push_back() 
\*begin
\*end procedure;
\*
\*procedure push_front() 
\*begin
\*end procedure;
\*
\*procedure clear() 
\*begin
\*end procedure;

fair process Main = "Main" begin
    s0: first := 6;
end process;

fair process User = "User" begin
    s1: first := 7;
end process;
end algorithm;*)
====