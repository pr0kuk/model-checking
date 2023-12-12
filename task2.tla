--------------------------------- MODULE v1 ---------------------------------
EXTENDS Integers, TLC, Sequences

(*--algorithm ATM
variables
    c = FALSE;
    sleep_ticks = 0;
    i = TRUE;
    p = FALSE;
    b = FALSE;
    u = FALSE;
    menu = FALSE;
    out = FALSE;
    in = FALSE;
    card = 1101;
    balance = 2000;
    count_wrong = 0;
    number_of_actions = 9;
    actions_stack = <<1, 1234, 1 , 2 ,700, 1, 3, 1, 4>>;
    stack_ptr = 1;
    button = 0;
    correct_pin = 1234;
    
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
	WillTerminate == [](<><<~i \/ b>>_vars)
	WillUpdate == ((in \/ out) ~> (<>u))
end define

procedure UpdateBalance(tsum) begin
    s7:
    balance := balance + tsum;
    u := FALSE || in := FALSE || out := FALSE;
    return;
end procedure;

procedure Withdrawal()
variables
    t = 0, sum = 500;
begin
    s4: 
    call ButtonStack();
    user: sum:= button;
    s5: 
    if sum <= balance then
        c := TRUE;
        t := 0;
        s6: 
        c := FALSE || out := TRUE || u := TRUE;
        call UpdateBalance(-sum);
    end if;
    return_to_menu: return;
end procedure;

procedure Deposit() 
variables
    t = 0, sum = 500;
begin
    s8:
    c := TRUE;
    s9:
    c := FALSE || in := TRUE || u := TRUE;
    call UpdateBalance(sum);
    return;
end procedure;

procedure Menu()
variables
    t = 0;
begin
    s2:
    menu := TRUE;
    menu:
    while(t <= sleep_ticks /\ p) do
        call ButtonStack();
        cycle_step: menu := FALSE || t := t + 1;
        if (p = TRUE) then
            s3:
            if button = 1 then print <<balance>>; t:= 0; end if;
            s4:
            if button = 2 then call Withdrawal(); t1: t:= 0; end if;
            s8:
            if button = 3 then call Deposit(); t2: t:= 0; end if;
            s0:
            if button = 4 then menu:= FALSE || p:=FALSE || i:=FALSE; end if;
        end if;
    end while;
    menu:= FALSE || p:=FALSE || i:=FALSE;
    return;
end procedure;

procedure ButtonStack() begin
    user:
    button := actions_stack[stack_ptr];
    s0:
    if stack_ptr <= number_of_actions then
        stack_ptr := stack_ptr + 1;
    else menu:= FALSE || p:=FALSE || i:=FALSE; end if;
    return;
end procedure;

procedure Auth()
variables
    pin = 0;
begin
    s1:
    call ButtonStack();
    user: pin := button;
    s2:
    if pin = correct_pin /\ ~b then
        count_wrong := 0 || p := TRUE;
        call Menu();
    else count_wrong := count_wrong + 1; end if;
    s12:
    if count_wrong >= 2 then
        count_wrong := 0 || b := TRUE;
    end if;
    return;
end procedure;

process Main = "Main" begin
    s0:
    while(~b /\ i) do
        call Auth();
    end while;
end process;

end algorithm;*)
====