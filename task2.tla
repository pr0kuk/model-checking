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
\* BEGIN TRANSLATION (chksum(pcal) = "7014ef13" /\ chksum(tla) = "d6af55c7")
\* Label s8_0 of procedure Menu at line 77 col 15 changed to s8_0_
\* Label s7 of procedure Withdrawal at line 120 col 5 changed to s7_
\* Procedure variable t of procedure Deposit at line 88 col 5 changed to t_
\* Procedure variable sum of procedure Deposit at line 89 col 5 changed to sum_
\* Procedure variable sum of procedure Withdrawal at line 106 col 5 changed to sum_W
CONSTANT defaultInitValue
VARIABLES c, sleep_ticks, i, p, b, u1, u2, menu, out, in, card, balance, 
          count_wrong, number_of_actions, button_stack, stack_ptr, button, 
          correct_pin, pc, stack

(* define statement *)
NoUseBlocked == (b ~> ~p)
NoJustCurtain == (c ~> (i /\ p))
NoOpenCurtain == ((in \/ out) ~> ~c)
NoMenuWOPin == (menu ~> p)
NoRandomBalanceUpdate == (u2 ~> (in \/ out))
FalseStatement == (menu ~> b)

WillMenu == (p ~> <>menu)
WillTerminate == <>(~i \/ b)
WillUpdate == ((in \/ out) ~> (<>u1))

VARIABLES pin, t_, sum_, t, sum_W, sum

vars == << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, card, balance, 
           count_wrong, number_of_actions, button_stack, stack_ptr, button, 
           correct_pin, pc, stack, pin, t_, sum_, t, sum_W, sum >>

ProcSet == {"Main"}

Init == (* Global variables *)
        /\ c = FALSE
        /\ sleep_ticks = 0
        /\ i = TRUE
        /\ p = FALSE
        /\ b = FALSE
        /\ u1 = FALSE
        /\ u2 = FALSE
        /\ menu = FALSE
        /\ out = FALSE
        /\ in = FALSE
        /\ card = 1101
        /\ balance = 2000
        /\ count_wrong = 0
        /\ number_of_actions = 9
        /\ button_stack = <<1, 1234, 1 , 2 ,700, 1, 3, 1, 4>>
        /\ stack_ptr = 1
        /\ button = defaultInitValue
        /\ correct_pin = 1234
        (* Procedure Auth *)
        /\ pin = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Deposit *)
        /\ t_ = [ self \in ProcSet |-> 0]
        /\ sum_ = [ self \in ProcSet |-> 500]
        (* Procedure Withdrawal *)
        /\ t = [ self \in ProcSet |-> 0]
        /\ sum_W = [ self \in ProcSet |-> 0]
        (* Procedure UpdateBalance *)
        /\ sum = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "s0"]

input_pin(self) == /\ pc[self] = "input_pin"
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ButtonStack",
                                                            pc        |->  "pin_defined" ] >>
                                                        \o stack[self]]
                   /\ pc' = [pc EXCEPT ![self] = "s_button"]
                   /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, 
                                   in, card, balance, count_wrong, 
                                   number_of_actions, button_stack, stack_ptr, 
                                   button, correct_pin, pin, t_, sum_, t, 
                                   sum_W, sum >>

pin_defined(self) == /\ pc[self] = "pin_defined"
                     /\ pin' = [pin EXCEPT ![self] = button]
                     /\ pc' = [pc EXCEPT ![self] = "s1"]
                     /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, 
                                     out, in, card, balance, count_wrong, 
                                     number_of_actions, button_stack, 
                                     stack_ptr, button, correct_pin, stack, t_, 
                                     sum_, t, sum_W, sum >>

s1(self) == /\ pc[self] = "s1"
            /\ IF pin[self] = correct_pin /\ ~b
                  THEN /\ count_wrong' = 0
                       /\ p' = TRUE
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Menu",
                                                                pc        |->  "s12" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "menu_p0"]
                  ELSE /\ count_wrong' = count_wrong + 1
                       /\ pc' = [pc EXCEPT ![self] = "s12"]
                       /\ UNCHANGED << p, stack >>
            /\ UNCHANGED << c, sleep_ticks, i, b, u1, u2, menu, out, in, card, 
                            balance, number_of_actions, button_stack, 
                            stack_ptr, button, correct_pin, pin, t_, sum_, t, 
                            sum_W, sum >>

s12(self) == /\ pc[self] = "s12"
             /\ IF count_wrong >= 2
                   THEN /\ count_wrong' = 0
                        /\ b' = TRUE
                   ELSE /\ TRUE
                        /\ UNCHANGED << b, count_wrong >>
             /\ pc' = [pc EXCEPT ![self] = "to_init"]
             /\ UNCHANGED << c, sleep_ticks, i, p, u1, u2, menu, out, in, card, 
                             balance, number_of_actions, button_stack, 
                             stack_ptr, button, correct_pin, stack, pin, t_, 
                             sum_, t, sum_W, sum >>

to_init(self) == /\ pc[self] = "to_init"
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ pin' = [pin EXCEPT ![self] = Head(stack[self]).pin]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, 
                                 in, card, balance, count_wrong, 
                                 number_of_actions, button_stack, stack_ptr, 
                                 button, correct_pin, t_, sum_, t, sum_W, sum >>

Auth(self) == input_pin(self) \/ pin_defined(self) \/ s1(self) \/ s12(self)
                 \/ to_init(self)

s_button(self) == /\ pc[self] = "s_button"
                  /\ button' = button_stack[stack_ptr]
                  /\ IF stack_ptr <= number_of_actions
                        THEN /\ pc' = [pc EXCEPT ![self] = "s_stack_ptr"]
                             /\ UNCHANGED << i, p, menu >>
                        ELSE /\ menu' = FALSE
                             /\ p' = FALSE
                             /\ i' = FALSE
                             /\ pc' = [pc EXCEPT ![self] = "input2"]
                  /\ UNCHANGED << c, sleep_ticks, b, u1, u2, out, in, card, 
                                  balance, count_wrong, number_of_actions, 
                                  button_stack, stack_ptr, correct_pin, stack, 
                                  pin, t_, sum_, t, sum_W, sum >>

s_stack_ptr(self) == /\ pc[self] = "s_stack_ptr"
                     /\ stack_ptr' = stack_ptr + 1
                     /\ pc' = [pc EXCEPT ![self] = "input2"]
                     /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, 
                                     out, in, card, balance, count_wrong, 
                                     number_of_actions, button_stack, button, 
                                     correct_pin, stack, pin, t_, sum_, t, 
                                     sum_W, sum >>

input2(self) == /\ pc[self] = "input2"
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                                card, balance, count_wrong, number_of_actions, 
                                button_stack, stack_ptr, button, correct_pin, 
                                pin, t_, sum_, t, sum_W, sum >>

ButtonStack(self) == s_button(self) \/ s_stack_ptr(self) \/ input2(self)

menu_p0(self) == /\ pc[self] = "menu_p0"
                 /\ menu' = TRUE
                 /\ t' = [t EXCEPT ![self] = 0]
                 /\ pc' = [pc EXCEPT ![self] = "s2"]
                 /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, out, in, 
                                 card, balance, count_wrong, number_of_actions, 
                                 button_stack, stack_ptr, button, correct_pin, 
                                 stack, pin, t_, sum_, sum_W, sum >>

s2(self) == /\ pc[self] = "s2"
            /\ IF (t[self] <= sleep_ticks /\ p)
                  THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ButtonStack",
                                                                pc        |->  "menu_p3" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "s_button"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "menu_p2"]
                       /\ stack' = stack
            /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                            card, balance, count_wrong, number_of_actions, 
                            button_stack, stack_ptr, button, correct_pin, pin, 
                            t_, sum_, t, sum_W, sum >>

menu_p3(self) == /\ pc[self] = "menu_p3"
                 /\ menu' = FALSE
                 /\ pc' = [pc EXCEPT ![self] = "set_t0"]
                 /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, out, in, 
                                 card, balance, count_wrong, number_of_actions, 
                                 button_stack, stack_ptr, button, correct_pin, 
                                 stack, pin, t_, sum_, t, sum_W, sum >>

set_t0(self) == /\ pc[self] = "set_t0"
                /\ t' = [t EXCEPT ![self] = t[self] + 1]
                /\ pc' = [pc EXCEPT ![self] = "s_if_p"]
                /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                                card, balance, count_wrong, number_of_actions, 
                                button_stack, stack_ptr, button, correct_pin, 
                                stack, pin, t_, sum_, sum_W, sum >>

s_if_p(self) == /\ pc[self] = "s_if_p"
                /\ IF (p = TRUE)
                      THEN /\ pc' = [pc EXCEPT ![self] = "s3_0"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "s2"]
                /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                                card, balance, count_wrong, number_of_actions, 
                                button_stack, stack_ptr, button, correct_pin, 
                                stack, pin, t_, sum_, t, sum_W, sum >>

s3_0(self) == /\ pc[self] = "s3_0"
              /\ IF button = 1
                    THEN /\ PrintT(<<balance>>)
                         /\ t' = [t EXCEPT ![self] = 0]
                    ELSE /\ TRUE
                         /\ t' = t
              /\ pc' = [pc EXCEPT ![self] = "s4_0"]
              /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                              card, balance, count_wrong, number_of_actions, 
                              button_stack, stack_ptr, button, correct_pin, 
                              stack, pin, t_, sum_, sum_W, sum >>

s4_0(self) == /\ pc[self] = "s4_0"
              /\ IF button = 2
                    THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Withdrawal",
                                                                  pc        |->  "set_t1",
                                                                  t         |->  t[self],
                                                                  sum_W     |->  sum_W[self] ] >>
                                                              \o stack[self]]
                         /\ t' = [t EXCEPT ![self] = 0]
                         /\ sum_W' = [sum_W EXCEPT ![self] = 0]
                         /\ pc' = [pc EXCEPT ![self] = "s4"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "s8_0_"]
                         /\ UNCHANGED << stack, t, sum_W >>
              /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                              card, balance, count_wrong, number_of_actions, 
                              button_stack, stack_ptr, button, correct_pin, 
                              pin, t_, sum_, sum >>

set_t1(self) == /\ pc[self] = "set_t1"
                /\ t' = [t EXCEPT ![self] = 0]
                /\ pc' = [pc EXCEPT ![self] = "s8_0_"]
                /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                                card, balance, count_wrong, number_of_actions, 
                                button_stack, stack_ptr, button, correct_pin, 
                                stack, pin, t_, sum_, sum_W, sum >>

s8_0_(self) == /\ pc[self] = "s8_0_"
               /\ IF button = 3
                     THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Deposit",
                                                                   pc        |->  "set_t2",
                                                                   t_        |->  t_[self],
                                                                   sum_      |->  sum_[self] ] >>
                                                               \o stack[self]]
                          /\ t_' = [t_ EXCEPT ![self] = 0]
                          /\ sum_' = [sum_ EXCEPT ![self] = 500]
                          /\ pc' = [pc EXCEPT ![self] = "s8_0"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "menu_p1"]
                          /\ UNCHANGED << stack, t_, sum_ >>
               /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                               card, balance, count_wrong, number_of_actions, 
                               button_stack, stack_ptr, button, correct_pin, 
                               pin, t, sum_W, sum >>

set_t2(self) == /\ pc[self] = "set_t2"
                /\ t' = [t EXCEPT ![self] = 0]
                /\ pc' = [pc EXCEPT ![self] = "menu_p1"]
                /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                                card, balance, count_wrong, number_of_actions, 
                                button_stack, stack_ptr, button, correct_pin, 
                                stack, pin, t_, sum_, sum_W, sum >>

menu_p1(self) == /\ pc[self] = "menu_p1"
                 /\ menu' = TRUE
                 /\ pc' = [pc EXCEPT ![self] = "s1_0"]
                 /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, out, in, 
                                 card, balance, count_wrong, number_of_actions, 
                                 button_stack, stack_ptr, button, correct_pin, 
                                 stack, pin, t_, sum_, t, sum_W, sum >>

s1_0(self) == /\ pc[self] = "s1_0"
              /\ IF button = 4
                    THEN /\ menu' = FALSE
                         /\ p' = FALSE
                         /\ i' = FALSE
                    ELSE /\ TRUE
                         /\ UNCHANGED << i, p, menu >>
              /\ pc' = [pc EXCEPT ![self] = "s2"]
              /\ UNCHANGED << c, sleep_ticks, b, u1, u2, out, in, card, 
                              balance, count_wrong, number_of_actions, 
                              button_stack, stack_ptr, button, correct_pin, 
                              stack, pin, t_, sum_, t, sum_W, sum >>

menu_p2(self) == /\ pc[self] = "menu_p2"
                 /\ menu' = FALSE
                 /\ pc' = [pc EXCEPT ![self] = "too_auth"]
                 /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, out, in, 
                                 card, balance, count_wrong, number_of_actions, 
                                 button_stack, stack_ptr, button, correct_pin, 
                                 stack, pin, t_, sum_, t, sum_W, sum >>

too_auth(self) == /\ pc[self] = "too_auth"
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, 
                                  in, card, balance, count_wrong, 
                                  number_of_actions, button_stack, stack_ptr, 
                                  button, correct_pin, pin, t_, sum_, t, sum_W, 
                                  sum >>

Menu(self) == menu_p0(self) \/ s2(self) \/ menu_p3(self) \/ set_t0(self)
                 \/ s_if_p(self) \/ s3_0(self) \/ s4_0(self)
                 \/ set_t1(self) \/ s8_0_(self) \/ set_t2(self)
                 \/ menu_p1(self) \/ s1_0(self) \/ menu_p2(self)
                 \/ too_auth(self)

s8_0(self) == /\ pc[self] = "s8_0"
              /\ c' = TRUE
              /\ pc' = [pc EXCEPT ![self] = "s8"]
              /\ UNCHANGED << sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                              card, balance, count_wrong, number_of_actions, 
                              button_stack, stack_ptr, button, correct_pin, 
                              stack, pin, t_, sum_, t, sum_W, sum >>

s8(self) == /\ pc[self] = "s8"
            /\ IF (t_[self]<sleep_ticks)
                  THEN /\ t_' = [t_ EXCEPT ![self] = t_[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "s8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s9"]
                       /\ t_' = t_
            /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                            card, balance, count_wrong, number_of_actions, 
                            button_stack, stack_ptr, button, correct_pin, 
                            stack, pin, sum_, t, sum_W, sum >>

s9(self) == /\ pc[self] = "s9"
            /\ c' = FALSE
            /\ in' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "u_p2"]
            /\ UNCHANGED << sleep_ticks, i, p, b, u1, u2, menu, out, card, 
                            balance, count_wrong, number_of_actions, 
                            button_stack, stack_ptr, button, correct_pin, 
                            stack, pin, t_, sum_, t, sum_W, sum >>

u_p2(self) == /\ pc[self] = "u_p2"
              /\ u1' = TRUE
              /\ pc' = [pc EXCEPT ![self] = "u2_p2"]
              /\ UNCHANGED << c, sleep_ticks, i, p, b, u2, menu, out, in, card, 
                              balance, count_wrong, number_of_actions, 
                              button_stack, stack_ptr, button, correct_pin, 
                              stack, pin, t_, sum_, t, sum_W, sum >>

u2_p2(self) == /\ pc[self] = "u2_p2"
               /\ u2' = TRUE
               /\ pc' = [pc EXCEPT ![self] = "s11"]
               /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, menu, out, in, 
                               card, balance, count_wrong, number_of_actions, 
                               button_stack, stack_ptr, button, correct_pin, 
                               stack, pin, t_, sum_, t, sum_W, sum >>

s11(self) == /\ pc[self] = "s11"
             /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateBalance",
                                                         pc        |->  "to_menu_8",
                                                         sum       |->  sum[self] ] >>
                                                     \o stack[self]]
                /\ sum' = [sum EXCEPT ![self] = sum_[self]]
             /\ pc' = [pc EXCEPT ![self] = "s7"]
             /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                             card, balance, count_wrong, number_of_actions, 
                             button_stack, stack_ptr, button, correct_pin, pin, 
                             t_, sum_, t, sum_W >>

to_menu_8(self) == /\ pc[self] = "to_menu_8"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ t_' = [t_ EXCEPT ![self] = Head(stack[self]).t_]
                   /\ sum_' = [sum_ EXCEPT ![self] = Head(stack[self]).sum_]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, 
                                   in, card, balance, count_wrong, 
                                   number_of_actions, button_stack, stack_ptr, 
                                   button, correct_pin, pin, t, sum_W, sum >>

Deposit(self) == s8_0(self) \/ s8(self) \/ s9(self) \/ u_p2(self)
                    \/ u2_p2(self) \/ s11(self) \/ to_menu_8(self)

s4(self) == /\ pc[self] = "s4"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ButtonStack",
                                                     pc        |->  "setting_sum" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "s_button"]
            /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                            card, balance, count_wrong, number_of_actions, 
                            button_stack, stack_ptr, button, correct_pin, pin, 
                            t_, sum_, t, sum_W, sum >>

setting_sum(self) == /\ pc[self] = "setting_sum"
                     /\ sum_W' = [sum_W EXCEPT ![self] = button]
                     /\ IF sum_W'[self] <= balance
                           THEN /\ c' = TRUE
                                /\ t' = [t EXCEPT ![self] = 0]
                                /\ pc' = [pc EXCEPT ![self] = "s5"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "to_menu_1"]
                                /\ UNCHANGED << c, t >>
                     /\ UNCHANGED << sleep_ticks, i, p, b, u1, u2, menu, out, 
                                     in, card, balance, count_wrong, 
                                     number_of_actions, button_stack, 
                                     stack_ptr, button, correct_pin, stack, 
                                     pin, t_, sum_, sum >>

s5(self) == /\ pc[self] = "s5"
            /\ IF (t[self] < sleep_ticks)
                  THEN /\ t' = [t EXCEPT ![self] = t[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "s5"]
                       /\ UNCHANGED << c, out >>
                  ELSE /\ c' = FALSE
                       /\ out' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "u_p1"]
                       /\ t' = t
            /\ UNCHANGED << sleep_ticks, i, p, b, u1, u2, menu, in, card, 
                            balance, count_wrong, number_of_actions, 
                            button_stack, stack_ptr, button, correct_pin, 
                            stack, pin, t_, sum_, sum_W, sum >>

u_p1(self) == /\ pc[self] = "u_p1"
              /\ u1' = TRUE
              /\ pc' = [pc EXCEPT ![self] = "u2_p1"]
              /\ UNCHANGED << c, sleep_ticks, i, p, b, u2, menu, out, in, card, 
                              balance, count_wrong, number_of_actions, 
                              button_stack, stack_ptr, button, correct_pin, 
                              stack, pin, t_, sum_, t, sum_W, sum >>

u2_p1(self) == /\ pc[self] = "u2_p1"
               /\ u2' = TRUE
               /\ pc' = [pc EXCEPT ![self] = "s7_"]
               /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, menu, out, in, 
                               card, balance, count_wrong, number_of_actions, 
                               button_stack, stack_ptr, button, correct_pin, 
                               stack, pin, t_, sum_, t, sum_W, sum >>

s7_(self) == /\ pc[self] = "s7_"
             /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateBalance",
                                                         pc        |->  "to_menu_1",
                                                         sum       |->  sum[self] ] >>
                                                     \o stack[self]]
                /\ sum' = [sum EXCEPT ![self] = -sum_W[self]]
             /\ pc' = [pc EXCEPT ![self] = "s7"]
             /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                             card, balance, count_wrong, number_of_actions, 
                             button_stack, stack_ptr, button, correct_pin, pin, 
                             t_, sum_, t, sum_W >>

to_menu_1(self) == /\ pc[self] = "to_menu_1"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ t' = [t EXCEPT ![self] = Head(stack[self]).t]
                   /\ sum_W' = [sum_W EXCEPT ![self] = Head(stack[self]).sum_W]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, 
                                   in, card, balance, count_wrong, 
                                   number_of_actions, button_stack, stack_ptr, 
                                   button, correct_pin, pin, t_, sum_, sum >>

Withdrawal(self) == s4(self) \/ setting_sum(self) \/ s5(self) \/ u_p1(self)
                       \/ u2_p1(self) \/ s7_(self) \/ to_menu_1(self)

s7(self) == /\ pc[self] = "s7"
            /\ balance' = balance + sum[self]
            /\ pc' = [pc EXCEPT ![self] = "u2_p0"]
            /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, 
                            card, count_wrong, number_of_actions, button_stack, 
                            stack_ptr, button, correct_pin, stack, pin, t_, 
                            sum_, t, sum_W, sum >>

u2_p0(self) == /\ pc[self] = "u2_p0"
               /\ u2' = FALSE
               /\ pc' = [pc EXCEPT ![self] = "in_p0"]
               /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, menu, out, in, 
                               card, balance, count_wrong, number_of_actions, 
                               button_stack, stack_ptr, button, correct_pin, 
                               stack, pin, t_, sum_, t, sum_W, sum >>

in_p0(self) == /\ pc[self] = "in_p0"
               /\ in' = FALSE
               /\ pc' = [pc EXCEPT ![self] = "out_p0"]
               /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, 
                               card, balance, count_wrong, number_of_actions, 
                               button_stack, stack_ptr, button, correct_pin, 
                               stack, pin, t_, sum_, t, sum_W, sum >>

out_p0(self) == /\ pc[self] = "out_p0"
                /\ out' = FALSE
                /\ pc' = [pc EXCEPT ![self] = "u_p0"]
                /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, in, 
                                card, balance, count_wrong, number_of_actions, 
                                button_stack, stack_ptr, button, correct_pin, 
                                stack, pin, t_, sum_, t, sum_W, sum >>

u_p0(self) == /\ pc[self] = "u_p0"
              /\ u1' = FALSE
              /\ pc' = [pc EXCEPT ![self] = "to_menu_2"]
              /\ UNCHANGED << c, sleep_ticks, i, p, b, u2, menu, out, in, card, 
                              balance, count_wrong, number_of_actions, 
                              button_stack, stack_ptr, button, correct_pin, 
                              stack, pin, t_, sum_, t, sum_W, sum >>

to_menu_2(self) == /\ pc[self] = "to_menu_2"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ sum' = [sum EXCEPT ![self] = Head(stack[self]).sum]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, 
                                   in, card, balance, count_wrong, 
                                   number_of_actions, button_stack, stack_ptr, 
                                   button, correct_pin, pin, t_, sum_, t, 
                                   sum_W >>

UpdateBalance(self) == s7(self) \/ u2_p0(self) \/ in_p0(self)
                          \/ out_p0(self) \/ u_p0(self) \/ to_menu_2(self)

s0 == /\ pc["Main"] = "s0"
      /\ IF (~b /\ i)
            THEN /\ stack' = [stack EXCEPT !["Main"] = << [ procedure |->  "Auth",
                                                            pc        |->  "s0",
                                                            pin       |->  pin["Main"] ] >>
                                                        \o stack["Main"]]
                 /\ pin' = [pin EXCEPT !["Main"] = defaultInitValue]
                 /\ pc' = [pc EXCEPT !["Main"] = "input_pin"]
            ELSE /\ pc' = [pc EXCEPT !["Main"] = "Done"]
                 /\ UNCHANGED << stack, pin >>
      /\ UNCHANGED << c, sleep_ticks, i, p, b, u1, u2, menu, out, in, card, 
                      balance, count_wrong, number_of_actions, button_stack, 
                      stack_ptr, button, correct_pin, t_, sum_, t, sum_W, sum >>

Main == s0

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Main
           \/ (\E self \in ProcSet:  \/ Auth(self) \/ ButtonStack(self)
                                     \/ Menu(self) \/ Deposit(self)
                                     \/ Withdrawal(self) \/ UpdateBalance(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Nov 29 03:24:07 MSK 2023 by alex-
\* Last modified Mon Oct 15 18:38:35 PDT 2018 by rebcabin
\* Created Mon Oct 15 13:09:48 PDT 2018 by rebcabin
