--------------------------------- MODULE v1 ---------------------------------
EXTENDS Integers, TLC, Sequences

(*--algorithm ATM
variables
    c = FALSE;
    sleep_ticks = 0;
    i = TRUE,
    p = FALSE,
    b = FALSE,
    u1 = FALSE,
    u2 = FALSE,
    menu = FALSE,
    out = FALSE,
    in = FALSE,
    card = 1101,
    balance = 2000,
    count_wrong = 0,
    number_of_actions = 9;
    button_stack = <<1, 1234, 1 , 2 ,700, 1, 3, 1, 4>>;
    stack_ptr = 1,
    button,
    correct_pin = 1234;
define
\*SAFETY
    NoUseBlocked == (b ~> ~p)
    NoJustCurtain == (c ~> (i /\ p))
    NoOpenCurtain == ((in \/ out) ~> ~c)
    NoMenuWOPin == (menu ~> p)
    NoRandomBalanceUpdate == (u2 ~> (in \/ out))
    FalseStatement == (menu ~> b)
\*    LIVENESS
    WillMenu == (p ~> <>menu)
    WillTerminate == <>(~i \/ b)
    WillUpdate == ((in \/ out) ~> (<>u1))
    \* h == p \/ b \/ menu
    \*NoInfLoopAuth == (i ~> (h \/ h'))
end define
procedure Auth()
variables
    pin,
begin
    input_pin: call ButtonStack();
    pin_defined: pin := button;
s1: if pin = correct_pin /\ ~b then
        count_wrong := 0;
        p := TRUE;
        call Menu();
    else count_wrong := count_wrong + 1; end if;
    s12: if count_wrong >= 2 then
        count_wrong := 0;
        b := TRUE;
    end if;
    to_init: return;
end procedure;

procedure ButtonStack()
begin
    s_button: button := button_stack[stack_ptr];
    if stack_ptr <= number_of_actions then
        s_stack_ptr: stack_ptr := stack_ptr + 1;
    else menu:= FALSE; p:=FALSE; i:=FALSE; end if;
    input2: return;
end procedure

procedure Menu()
begin
menu_p0: menu := TRUE;
t := 0;
s2: while(t <= sleep_ticks /\ p) do
        call ButtonStack();
menu_p3:menu := FALSE;
      set_t0: t := t + 1;
        s_if_p: if (p = TRUE) then
        s3_0: if button = 1 then print <<balance>>; t:= 0; end if;
        s4_0: if button = 2 then call Withdrawal(); set_t1:t:= 0;end if;
        s8_0: if button = 3 then call Deposit();set_t2: t:= 0;end if;
    menu_p1:  menu := TRUE;
        s1_0: if button = 4 then menu:= FALSE; p:=FALSE; i:=FALSE; end if;
        end if;
    end while;
menu_p2:menu := FALSE;
    too_auth: return;
end procedure;

procedure Deposit()
variables
    t = 0,
    sum = 500;
begin
s8_0:c := TRUE;
s8: while(t<sleep_ticks) do
        t := t + 1;
    end while;
s9: c := FALSE;
    in := TRUE;
u_p2: u1 := TRUE;
u2_p2: u2 := TRUE;
s11:call UpdateBalance(sum);
to_menu_8:return;
end procedure;

procedure Withdrawal()
variables
    t = 0,
    sum = 0;
begin
s4: call ButtonStack();
    setting_sum: sum:= button;
    if sum <= balance then
        c := TRUE;
        t := 0;
s5: while(t < sleep_ticks) do
        t := t + 1;
    end while;
    c := FALSE;
    out := TRUE;
u_p1:u1 := TRUE;
u2_p1:u2 := TRUE;
s7: call UpdateBalance(-sum);

    end if;
to_menu_1: return;
end procedure;

procedure UpdateBalance(sum)
begin
s7: balance := balance + sum;
u2_p0:u2 := FALSE;
in_p0:in := FALSE;
out_p0:out := FALSE;
u_p0:u1 := FALSE;
to_menu_2: return;
end procedure;

process Main = "Main"
variables
begin
s0: while(~b /\ i) do
        call Auth();
    end while;
end process;
end algorithm;*)