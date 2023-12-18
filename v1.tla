--------------------------------- MODULE v1 ---------------------------------
EXTENDS Integers, TLC, Sequences

(*--algorithm ATM
variables
    c = FALSE,
    i = FALSE,
    p = FALSE,
    b = FALSE,
    u = FALSE,
    menu = FALSE,
    out = FALSE,
    in = FALSE,
    input_pin = FALSE,
    balance = 2,
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
    await i = TRUE;
    s1:
    while(~b /\ i) do
        await input_pin = TRUE;
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

fair process User = "USER" begin
    init:
    i := TRUE;
    input_pin := TRUE;
end process;

end algorithm;*)
====