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
\*define
\*
\*end define


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
\* BEGIN TRANSLATION (chksum(pcal) = "b915c4c1" /\ chksum(tla) = "ce76ac44")
VARIABLES first, last, pc

vars == << first, last, pc >>

ProcSet == {"Main"} \cup {"User"}

Init == (* Global variables *)
        /\ first \in 1..Elem_num
        /\ last \in 1..Elem_num
        /\ pc = [self \in ProcSet |-> CASE self = "Main" -> "s0"
                                        [] self = "User" -> "s1"]

s0 == /\ pc["Main"] = "s0"
      /\ first' = 6
      /\ pc' = [pc EXCEPT !["Main"] = "Done"]
      /\ last' = last

Main == s0

s1 == /\ pc["User"] = "s1"
      /\ first' = 7
      /\ pc' = [pc EXCEPT !["User"] = "Done"]
      /\ last' = last

User == s1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Main \/ User
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(Main)
        /\ WF_vars(User)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
