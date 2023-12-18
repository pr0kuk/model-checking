--------------------------------- MODULE v1 ---------------------------------
EXTENDS Integers, TLC, Sequences

(*--algorithm ATM
variables
    c = FALSE;
    i = TRUE;
    p = FALSE;
    b = FALSE;
    u = FALSE;
    menu = FALSE;
    out = FALSE;
    in = FALSE;
    balance = 2;
    sum_to_change \in 0..3;
    
define

\*SAFETY
    NoUseBlocked == (b ~> ~p)
    NoJustCurtain == (c ~> (i /\ p))
    NoOpenCurtain == ((in \/ out) ~> ~c)
    NoMenuWOPin == (menu ~> p)
    NoRandomBalanceUpdate == (u ~> (in \/ out))
    FalseStatement == (menu ~> b) \* For check
    
\*LIVENESS
    WillMenu == (p ~> <>menu)
    WillTerminate == <>(~i \/ b)
    WillUpdate == ((in \/ out) ~> (<>u))
end define

procedure Withdrawal()
begin
    s4:
    if sum_to_change <= balance then
        s5: 
        c := TRUE;
        s6: 
        c := FALSE || out := TRUE || u := TRUE;
        s7:
        balance := balance + sum_to_change;
        u := FALSE || in := FALSE || out := FALSE;
    end if;
    return_to_menu: return;
end procedure;

procedure Deposit() 
begin
    s8:
    c := TRUE;
    s9:
    c := FALSE || in := TRUE || u := TRUE;
    s7:
    balance := balance + sum_to_change;
    u := FALSE || in := FALSE || out := FALSE;
    return;
end procedure;

fair process Main = "Main" begin
    s0:
    while(~b /\ i) do
        s1:
        either
            s12: \* card blocked
            b := TRUE;
        or
            goto s1; \* pin incorrect
        or
            s2: \* pin correct
            if ~b then
                p := TRUE;
                menu := TRUE;
                    if (p = TRUE) then
                        either
                            print <<balance>>;
                        or
                            call Withdrawal();
                        or
                            call Deposit();
                        or
                            t1: menu:= FALSE || p:=FALSE || i:=FALSE;
                        or
                            goto s2;
                        end either;
                    end if;
                t2: menu:= FALSE || p:=FALSE || i:=FALSE;
            end if;
        end either;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "21361c2c" /\ chksum(tla) = "8ebe1103")
\* Label s7 of procedure Withdrawal at line 42 col 9 changed to s7_
VARIABLES c, i, p, b, u, menu, out, in, balance, sum_to_change, pc, stack

(* define statement *)
NoUseBlocked == (b ~> ~p)
NoJustCurtain == (c ~> (i /\ p))
NoOpenCurtain == ((in \/ out) ~> ~c)
NoMenuWOPin == (menu ~> p)
NoRandomBalanceUpdate == (u ~> (in \/ out))
FalseStatement == (menu ~> b)


WillMenu == (p ~> <>menu)
WillTerminate == <>(~i \/ b)
WillUpdate == ((in \/ out) ~> (<>u))


vars == << c, i, p, b, u, menu, out, in, balance, sum_to_change, pc, stack >>

ProcSet == {"Main"}

Init == (* Global variables *)
        /\ c = FALSE
        /\ i = TRUE
        /\ p = FALSE
        /\ b = FALSE
        /\ u = FALSE
        /\ menu = FALSE
        /\ out = FALSE
        /\ in = FALSE
        /\ balance = 2
        /\ sum_to_change \in 0..3
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "s0"]

s4(self) == /\ pc[self] = "s4"
            /\ IF sum_to_change <= balance
                  THEN /\ pc' = [pc EXCEPT ![self] = "s5"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "return_to_menu"]
            /\ UNCHANGED << c, i, p, b, u, menu, out, in, balance, 
                            sum_to_change, stack >>

s5(self) == /\ pc[self] = "s5"
            /\ c' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "s6"]
            /\ UNCHANGED << i, p, b, u, menu, out, in, balance, sum_to_change, 
                            stack >>

s6(self) == /\ pc[self] = "s6"
            /\ /\ c' = FALSE
               /\ out' = TRUE
               /\ u' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "s7_"]
            /\ UNCHANGED << i, p, b, menu, in, balance, sum_to_change, stack >>

s7_(self) == /\ pc[self] = "s7_"
             /\ balance' = balance + sum_to_change
             /\ /\ in' = FALSE
                /\ out' = FALSE
                /\ u' = FALSE
             /\ pc' = [pc EXCEPT ![self] = "return_to_menu"]
             /\ UNCHANGED << c, i, p, b, menu, sum_to_change, stack >>

return_to_menu(self) == /\ pc[self] = "return_to_menu"
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << c, i, p, b, u, menu, out, in, balance, 
                                        sum_to_change >>

Withdrawal(self) == s4(self) \/ s5(self) \/ s6(self) \/ s7_(self)
                       \/ return_to_menu(self)

s8(self) == /\ pc[self] = "s8"
            /\ c' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "s9"]
            /\ UNCHANGED << i, p, b, u, menu, out, in, balance, sum_to_change, 
                            stack >>

s9(self) == /\ pc[self] = "s9"
            /\ /\ c' = FALSE
               /\ in' = TRUE
               /\ u' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "s7"]
            /\ UNCHANGED << i, p, b, menu, out, balance, sum_to_change, stack >>

s7(self) == /\ pc[self] = "s7"
            /\ balance' = balance + sum_to_change
            /\ /\ in' = FALSE
               /\ out' = FALSE
               /\ u' = FALSE
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << c, i, p, b, menu, sum_to_change >>

Deposit(self) == s8(self) \/ s9(self) \/ s7(self)

s0 == /\ pc["Main"] = "s0"
      /\ IF (~b /\ i)
            THEN /\ pc' = [pc EXCEPT !["Main"] = "s1"]
            ELSE /\ pc' = [pc EXCEPT !["Main"] = "Done"]
      /\ UNCHANGED << c, i, p, b, u, menu, out, in, balance, sum_to_change, 
                      stack >>

s1 == /\ pc["Main"] = "s1"
      /\ \/ /\ pc' = [pc EXCEPT !["Main"] = "s12"]
         \/ /\ pc' = [pc EXCEPT !["Main"] = "s1"]
         \/ /\ pc' = [pc EXCEPT !["Main"] = "s2"]
      /\ UNCHANGED << c, i, p, b, u, menu, out, in, balance, sum_to_change, 
                      stack >>

s12 == /\ pc["Main"] = "s12"
       /\ b' = TRUE
       /\ pc' = [pc EXCEPT !["Main"] = "s0"]
       /\ UNCHANGED << c, i, p, u, menu, out, in, balance, sum_to_change, 
                       stack >>

s2 == /\ pc["Main"] = "s2"
      /\ IF ~b
            THEN /\ p' = TRUE
                 /\ menu' = TRUE
                 /\ IF (p' = TRUE)
                       THEN /\ \/ /\ PrintT(<<balance>>)
                                  /\ pc' = [pc EXCEPT !["Main"] = "t2"]
                                  /\ stack' = stack
                               \/ /\ stack' = [stack EXCEPT !["Main"] = << [ procedure |->  "Withdrawal",
                                                                             pc        |->  "t2" ] >>
                                                                         \o stack["Main"]]
                                  /\ pc' = [pc EXCEPT !["Main"] = "s4"]
                               \/ /\ stack' = [stack EXCEPT !["Main"] = << [ procedure |->  "Deposit",
                                                                             pc        |->  "t2" ] >>
                                                                         \o stack["Main"]]
                                  /\ pc' = [pc EXCEPT !["Main"] = "s8"]
                               \/ /\ pc' = [pc EXCEPT !["Main"] = "t1"]
                                  /\ stack' = stack
                               \/ /\ pc' = [pc EXCEPT !["Main"] = "s2"]
                                  /\ stack' = stack
                       ELSE /\ pc' = [pc EXCEPT !["Main"] = "t2"]
                            /\ stack' = stack
            ELSE /\ pc' = [pc EXCEPT !["Main"] = "s0"]
                 /\ UNCHANGED << p, menu, stack >>
      /\ UNCHANGED << c, i, b, u, out, in, balance, sum_to_change >>

t2 == /\ pc["Main"] = "t2"
      /\ /\ i' = FALSE
         /\ menu' = FALSE
         /\ p' = FALSE
      /\ pc' = [pc EXCEPT !["Main"] = "s0"]
      /\ UNCHANGED << c, b, u, out, in, balance, sum_to_change, stack >>

t1 == /\ pc["Main"] = "t1"
      /\ /\ i' = FALSE
         /\ menu' = FALSE
         /\ p' = FALSE
      /\ pc' = [pc EXCEPT !["Main"] = "t2"]
      /\ UNCHANGED << c, b, u, out, in, balance, sum_to_change, stack >>

Main == s0 \/ s1 \/ s12 \/ s2 \/ t2 \/ t1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Main
           \/ (\E self \in ProcSet: Withdrawal(self) \/ Deposit(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Main) /\ WF_vars(Withdrawal("Main")) /\ WF_vars(Deposit("Main"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====
