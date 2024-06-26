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
    last = Elem_num
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
\* BEGIN TRANSLATION (chksum(pcal) = "f6a39b7a" /\ chksum(tla) = "27947906")
\* Label clear of procedure clear at line 80 col 12 changed to clear_
VARIABLES elems, first, last, pc, stack

(* define statement *)
ForEach(op(_,_), acc) ==
    LET getelem[i \in Number] ==
        IF i = Elem_num THEN op(elems[i], acc)
        ELSE
            LET elem == elems[i]
            IN op(elem, getelem[elem.i + 1])
    IN getelem[1]


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


vars == << elems, first, last, pc, stack >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ elems = InitialList
        /\ first = 1
        /\ last = Elem_num
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "main_loop"]

clear_(self) == /\ pc[self] = "clear_"
                /\ IF Cardinality(AllListElems) > 2
                      THEN /\ \E e \in AllInnerListElems:
                                elems' = [elems EXCEPT ![e.i].st = "deleted",
                                                       ![e.i].n = 0,
                                                       ![e.i].p = 0,
                                                       ![elems[e.i].p].n = elems[elems[e.i].n].i,
                                                       ![elems[e.i].n].p = elems[elems[e.i].p].i]
                           /\ pc' = [pc EXCEPT ![self] = "clear_"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                           /\ elems' = elems
                /\ UNCHANGED << first, last, stack >>

clear(self) == clear_(self)

main_loop(self) == /\ pc[self] = "main_loop"
                   /\ \/ /\ pc' = [pc EXCEPT ![self] = "pop_back"]
                         /\ stack' = stack
                      \/ /\ pc' = [pc EXCEPT ![self] = "pop_front"]
                         /\ stack' = stack
                      \/ /\ pc' = [pc EXCEPT ![self] = "push_back"]
                         /\ stack' = stack
                      \/ /\ pc' = [pc EXCEPT ![self] = "push_front"]
                         /\ stack' = stack
                      \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "clear",
                                                                  pc        |->  "end_main_loop" ] >>
                                                              \o stack[self]]
                         /\ pc' = [pc EXCEPT ![self] = "clear_"]
                   /\ UNCHANGED << elems, first, last >>

pop_back(self) == /\ pc[self] = "pop_back"
                  /\ IF Cardinality(AllListElems) > 2
                        THEN /\ /\ elems' = [elems EXCEPT ![last].st = "deleted",
                                                          ![elems[last].p].n = 0,
                                                          ![last].p = 0]
                                /\ last' = elems[last].p
                        ELSE /\ TRUE
                             /\ UNCHANGED << elems, last >>
                  /\ pc' = [pc EXCEPT ![self] = "end_main_loop"]
                  /\ UNCHANGED << first, stack >>

pop_front(self) == /\ pc[self] = "pop_front"
                   /\ IF Cardinality(AllListElems) > 2
                         THEN /\ /\ elems' = [elems EXCEPT ![first].st = "deleted",
                                                           ![elems[first].n].p = 0,
                                                           ![first].n = 0]
                                 /\ first' = elems[first].n
                         ELSE /\ TRUE
                              /\ UNCHANGED << elems, first >>
                   /\ pc' = [pc EXCEPT ![self] = "end_main_loop"]
                   /\ UNCHANGED << last, stack >>

push_back(self) == /\ pc[self] = "push_back"
                   /\ IF Cardinality(AllDeleted) > 0
                         THEN /\ \E e \in AllDeleted:
                                   /\ elems' = [elems EXCEPT ![e.i].st = "in_list",
                                                             ![last].n = e.i,
                                                             ![e.i].p = last]
                                   /\ last' = e.i
                         ELSE /\ TRUE
                              /\ UNCHANGED << elems, last >>
                   /\ pc' = [pc EXCEPT ![self] = "end_main_loop"]
                   /\ UNCHANGED << first, stack >>

push_front(self) == /\ pc[self] = "push_front"
                    /\ IF Cardinality(AllDeleted) > 0
                          THEN /\ \E e \in AllDeleted:
                                    /\ elems' = [elems EXCEPT ![e.i].st = "in_list",
                                                              ![first].p = e.i,
                                                              ![e.i].n = first]
                                    /\ first' = e.i
                          ELSE /\ TRUE
                               /\ UNCHANGED << elems, first >>
                    /\ pc' = [pc EXCEPT ![self] = "end_main_loop"]
                    /\ UNCHANGED << last, stack >>

end_main_loop(self) == /\ pc[self] = "end_main_loop"
                       /\ pc' = [pc EXCEPT ![self] = "main_loop"]
                       /\ UNCHANGED << elems, first, last, stack >>

Main(self) == main_loop(self) \/ pop_back(self) \/ pop_front(self)
                 \/ push_back(self) \/ push_front(self)
                 \/ end_main_loop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: clear(self))
           \/ (\E self \in 1..2: Main(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in 1..2 : WF_vars(Main(self)) /\ WF_vars(clear(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
