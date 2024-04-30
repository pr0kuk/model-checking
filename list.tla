--------------------------------- MODULE list ---------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets
Elem_num == 5
Status == {"in_list", "deleted"}
Number == 1..Elem_num
Prev_v == 0..Elem_num
Next_v == 0..Elem_num
Elems == [i: Number, p: Prev_v, n: Next_v, st: Status]
IsInList(elem) == "in_list" \in Status /\ elem.st = "in_list"
IsDeleted(elem) == "deleted" \in Status /\ elem.st = "deleted"
InitialList == [i \in Number |-> CHOOSE e \in Elems: e.i = i /\ e.p = i - 1 /\ (e.n = i + 1 \/ (e.n = 0 /\ e.i = Elem_num))]

(*--fair algorithm list
variables
    elems = InitialList,
    first = 1,
    last = Elem_num,
define
    ForEach(op(_,_), acc) ==
        LET getelem[i \in Number] ==
            IF i = Elem_num THEN acc
            ELSE
                LET elem == elems[i]
                IN op(elem, getelem[elem.i + 1])
        IN getelem[1]
    
    AllElems == ForEach(LAMBDA b, acc: {b} \union acc, {})
    AllListElems == ForEach(LAMBDA b, acc: IF IsInList(b) THEN {b} \union acc ELSE acc, {})
    AllDeleted == ForEach(LAMBDA b, acc: IF IsDeleted(b) THEN {b} \union acc ELSE acc, {})

    \* invariants
    HavingHead == (elems[first].st = "in_list")
    HavingTail == (elems[last].st = "in_list")
    Acyclicity == ~(first = last)
    Linearity == \A e \in AllListElems: ~(e.n = e.p)
    LastIsTail == (elems[last].n = 0)
    FirstIsHead == (elems[first].p = 0)
    DeletedUnconnectivity == 
        \A e \in AllDeleted:
            (e.n = 0) /\ (e.p = 0)
    Acyclicity2 ==
        \A e \in AllListElems:
            (~(e.n = e.i)) /\ (~(e.p = e.i))
    Connectivity ==
        (\A e \in AllListElems: e.p \in 1..Elem_num \/ (e.p = 0 /\ e.i = first))
        /\
        (\A e \in AllListElems: e.n \in 1..Elem_num \/ (e.n = 0 /\ e.i = last))
   DoubleLinkage ==
         (\A e \in AllListElems: e.i = first \/ elems[e.p].n = e.i)
         /\
         (\A e \in AllListElems: e.i = last \/ elems[e.n].p = e.i)
   \*Connectivity2
   invariants == HavingHead /\ HavingTail /\ Acyclicity /\ Acyclicity2 /\ Linearity /\ LastIsTail /\ FirstIsHead /\ DeletedUnconnectivity /\ Connectivity /\ DoubleLinkage
end define


procedure pop_back() 
begin
    pop_back: if Cardinality(AllListElems) > 2 then
        elems[last].st := "deleted" || elems[elems[last].p].n := 0 || last := elems[last].p || elems[last].p := 0;
    end if;
end procedure;

procedure pop_front() 
begin
    pop_front: if Cardinality(AllListElems) > 2 then
        elems[first].st := "deleted" || elems[elems[first].n].p := 0 || first := elems[first].n || elems[first].n := 0;
    end if;
end procedure;
\*
\*procedure push_back() 
\*begin
\*    ss3: first := 3;
\*end procedure;
\*
\*procedure push_front() 
\*begin
\*    ss4: first := 3;
\*end procedure;
\*
\*procedure clear() 
\*begin
\*    ss5: first := 3;
\*end procedure;

fair process Main = "Main" begin
    main_loop:

    either
        call pop_back();
    or
        call pop_front();
\*    or
\*        call push_back();
\*    or
\*        call push_front();
\*    or
\*        call clear();
    end either;
end process;

\*fair process User = "User" begin
\*    s1: first := 7;
\*end process;
end algorithm;*)
====