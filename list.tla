--------------------------------- MODULE list ---------------------------------
EXTENDS Integers, TLC, Sequences
elem_num == 5
status == {"in_list", "deleted"}
number == 1..elem_num
prev == 1..elem_num
next == 1..elem_num
elems == [i: number, p: prev, n: next, st: status]
    
(*--fair algorithm list
variables
    first \in 1..elem_num,
    last \in 1..elem_num,
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
====
