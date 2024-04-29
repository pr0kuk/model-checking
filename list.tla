--------------------------------- MODULE list ---------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets
Elem_num == 5
Status == {"in_list", "deleted"}
Number == 1..Elem_num
Prev_v == 1..Elem_num
Next_v == 1..Elem_num
Elems == [i: Number, p: Prev_v, n: Next_v, st: Status]

IsInList(elem) ==
    LET ST == "in_list"
    IN ST \in Status /\ elem.st = ST

IsDeleted(elem) ==
    LET ST == "deleted"
    IN ST \in Status /\ elem.st = ST


InitialList == [i \in Number |-> CHOOSE e: e \in Elems]

(*--fair algorithm list
variables
    elems = InitialList,
    first \in 1..Elem_num,
    last \in 1..Elem_num,
define
    ForEach(op(_,_), acc) ==
        LET getelem[i \in Number] ==
            IF i = Elem_num THEN acc
            ELSE
                LET elem == elems[i]
                IN op(elem, getelem[elems[i].n])
        IN getelem[1]
    
    AllElems == ForEach(LAMBDA b, acc: {b} \union acc, {})
    AllListElems == ForEach(LAMBDA b, acc: IF IsInList(b) THEN {b} \union acc ELSE acc, {})
    AllDeleted == ForEach(LAMBDA b, acc: IF IsDeleted(b) THEN {b} \union acc ELSE acc, {})

    \* invariants
    HavingHead == (elems[first].st = "in_list")
    HavingTail == (elems[last].st = "in_list")
    Acyclicity == ~(first = last)
    Linearity == \A e \in AllListElems: ~(e.n = e.p)
    LastIsTail == (elems[last].n = -1)
    FirstIsHead == (elems[first].p = -1)
    DeletedUnconnectivity == 
        \A e \in AllDeleted:
            (elems[e].n = -1) /\ (elems[e].p = -1)
    Acyclicity2 ==
        \A e \in AllListElems:
            (~(elems[e].n = e.i)) /\ (~(elems[e].p = e.i))
    Connectivity ==
        (\A e \in AllListElems \ elems[first]: elems[e].p \in Number)
        /\
        (\A e \in AllListElems \ elems[last]: elems[e].n \in Number)
   DoubleLinkage ==
        (\A e \in AllListElems \ elems[first]: elems[elems[e].p].n = e.i)
        /\
        (\A e \in AllListElems \ elems[last]: elems[elems[e].n].p = e.i)
   \*Connectivity2
   
end define


procedure pop_back() 
begin
    pop_back: if Cardinality(AllListElems) > 2 then
        ss2: elems[first].st := "deleted";
        ss3: first := elems[first].n;
        ss0: elems[first].n := -1;
        ss1: elems[first].p := -1;
    end if;
end procedure;

procedure pop_front() 
begin
    ss2: first := 7;
end procedure;

procedure push_back() 
begin
    ss3: first := 7;
end procedure;

procedure push_front() 
begin
    ss4: first := 7;
end procedure;

procedure clear() 
begin
    ss5: first := 7;
end procedure;

fair process Main = "Main" begin
    main_loop:
    either
        call pop_back();
    or
        call pop_front();
    or
        call push_back();
    or
        call push_front();
    or
        call clear();
    end either;
end process;

fair process User = "User" begin
    s1: first := 7;
end process;
end algorithm;*)
====