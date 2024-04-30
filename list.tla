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
    \* ForEach by numbers of nodes
    ForEach(op(_,_), acc) ==
        LET getelem[i \in Number] ==
            IF i = Elem_num THEN op(elems[i], acc)
            ELSE
                LET elem == elems[i]
                IN op(elem, getelem[elem.i + 1])
        IN getelem[1]
    
    \* ForEach by pointers of nodes
    ForEach2(op(_,_), acc) ==
        LET getelem[i \in Number] ==
            IF i = last THEN op(elems[i], acc)
            ELSE
                LET elem == elems[i]
                IN op(elem, getelem[elem.n])
        IN getelem[first]
    
    AllElems == ForEach(LAMBDA b, acc: {b} \union acc, {})
    AllListElems == ForEach(LAMBDA b, acc: IF IsInList(b) THEN {b} \union acc ELSE acc, {})
    AllDeleted == ForEach(LAMBDA b, acc: IF IsDeleted(b) THEN {b} \union acc ELSE acc, {})
    AllInnerListElems == ForEach(LAMBDA b, acc: IF IsInList(b) /\ ~(b.i = first) /\ ~(b.i = last) THEN {b} \union acc ELSE acc, {})

    \* invariants
    HavingHead == (elems[first].st = "in_list")
    HavingTail == (elems[last].st = "in_list")
    Acyclicity == ~(first = last)
    Linearity == \A e \in AllListElems: ~(e.n = e.p)
    LastIsTail == (elems[last].n = 0)
    FirstIsHead == (elems[first].p = 0)
    DeletedUnconnectivity ==  \A e \in AllDeleted: (e.n = 0) /\ (e.p = 0)
    Acyclicity2 == \A e \in AllListElems: (~(e.n = e.i)) /\ (~(e.p = e.i))
    Connectivity == (\A e \in AllListElems: e.p \in Number \/ (e.p = 0 /\ e.i = first)) /\ (\A e \in AllListElems: e.n \in Number \/ (e.n = 0 /\ e.i = last))
    DoubleLinkage == (\A e \in AllListElems: e.i = first \/ elems[e.p].n = e.i) /\ (\A e \in AllListElems: e.i = last \/ elems[e.n].p = e.i)
    Connectivity2 == (elems[last] \in ForEach2(LAMBDA b, acc: {b} \union acc, {}))
    invariants == HavingHead /\ HavingTail /\ Acyclicity /\ Acyclicity2 /\ Linearity /\ LastIsTail /\ FirstIsHead /\ DeletedUnconnectivity /\ Connectivity /\ DoubleLinkage /\ Connectivity2
end define


macro pop_back() 
begin
    elems[last].st := "deleted" || elems[elems[last].p].n := 0 || last := elems[last].p || elems[last].p := 0;
end macro;

macro pop_front() 
begin
    elems[first].st := "deleted" || elems[elems[first].n].p := 0 || first := elems[first].n || elems[first].n := 0;
end macro;

macro push_back(e) 
begin
    elems[e.i].st := "in_list" || elems[last].n := e.i || last := e.i || elems[e.i].p := last;
end macro;

macro push_front(e) 
begin
    elems[e.i].st := "in_list" || elems[first].p := e.i || first := e.i || elems[e.i].n := first;
end macro;

procedure clear() 
begin
    clear: while Cardinality(AllListElems) > 2 do
        with e \in AllInnerListElems do
            elems[e.i].st := "deleted" || elems[e.i].n := 0 || elems[e.i].p := 0 || elems[elems[e.i].p].n := elems[elems[e.i].n].i || elems[elems[e.i].n].p := elems[elems[e.i].p].i;
        end with
    end while
end procedure;

fair process Main \in 1..2 begin
    main_loop:
    either
        pop_back: if Cardinality(AllListElems) > 2 then
            pop_back();
        end if;
    or
        pop_front: if Cardinality(AllListElems) > 2 then
            pop_front();
        end if;
    or
        push_back: if Cardinality(AllDeleted) > 0 then
            with e \in AllDeleted do
                push_back(e);
            end with;
        end if;
    or
        push_front: if Cardinality(AllDeleted) > 0 then
            with e \in AllDeleted do
                push_front(e);
            end with;
        end if;
    or
        call clear();
    end either;
    end_main_loop: goto main_loop;
end process;
end algorithm;*)
====