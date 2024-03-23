module list
open order[Time] as T
sig Time{}
sig item {}
one sig List {
	First: item one -> Time,
	Last: item one -> Time,
	Next: item -> item -> Time,
	Prev: item -> item  -> Time,
	elems: item set -> Time,
	deleted: item set -> Time
	} {
	all t:Time {
		First.t in elems.t
		Last.t in elems.t
		no Last.t.Next.t
		no Next.t.First.t
		all i: item | i in elems.t or i in deleted.t
		all i: elems.t | i not in deleted.t
		all i: deleted.t | i not in elems.t
		all i: deleted.t |no i.Next.t
	}
	all t:Time, i: item - Last.t - deleted.t {
		one i.Next.t
		i.Next.t != i
		i.Next.t not in deleted.t
		Last.t in i.^(Next.t)
	} 
	all t:Time, disj i,j: item - Last.t{ i.Next.t != j.Next.t }
	all t:Time { Prev.t = ~(Next.t) }
}

fun v_next[t:Time] : item->item { List.Next.t }
fun v_prev[t:Time]  : item->item { List.Prev.t }
fun v_first[t:Time]  : one item { List.First.t }
fun v_last[t:Time]  : one item { List.Last.t }

pred pop_back[now:Time] {
	let past = now.prev {
		List.deleted.now = List.deleted.past + v_last[past]
		List.Last.now = (v_last[past]).(v_prev[past])
		noChangeExcept2Items[now, v_last[past], v_last[now]]
	}
}

pred push_back[now:Time, e: item] {
	let past = now.prev {
		e in List.deleted.past
		v_last[now] = e
		(v_last[now]).(v_prev[now]) = v_last[past]
		noChangeExcept2Items[now, v_last[past], v_last[now]]
	}
}

pred pop_front[now:Time] {
	let past = now.prev {
		List.deleted.now = List.deleted.past + v_first[past]
		List.First.now = (v_first[past]).(v_next[past])
		noChangeExcept2Items[now, v_first[past], v_first[now]]
	}
}

pred push_front[now:Time, e: item] {
	let past = now.prev {
		e in List.deleted.past
		v_first[now] = e
		(v_first[now]).(v_next[now]) = v_first[past]
		noChangeExcept2Items[now, v_first[past], v_first[now]]
	}
}

pred noChangeExcept2Items [now: Time, i1, i2: item] {
	let past = now.prev {
		all i:item - i1 - i2 {i.(v_next[now]) = i.(v_next[past])}
	}
}

pred noChange [now: Time] {
	let past = now.prev {
		all i:item {i.(v_next[now]) = i.(v_next[past])}
	}
}

pred clear[now: Time] { let past = now.prev { all i: item - v_last[past] | i in List.deleted.now }}

pred nop [t: Time] { noChange[t] }

pred transitions[t: Time] {
	//nop[t] or
	//pop_back[t] or 
	//(some e: item | push_back[t, e]) or 
	//pop_front[t] or 
	(some e: item | push_front[t, e])-- or 
	//clear[t]
}

pred System { 
	#item > 4
	all t: Time - T/first | transitions [t] 
	all t: Time | ListIsValid[t]
	-- uncomment any of sanity-check predicates to check it
	--sc1
	--sc2
	--sc3
	--sc4
	--sc5
}

run {
	System
} for 5 but 2 Time 

pred ListIsValid[t:Time] { -- Correctness Invariant
	v_first[t] in List.elems.t -- L has the Head
	v_last[t] in List.elems.t -- L has the Tail
	all i: item | i in List.elems.t or i in List.deleted.t -- No initialize items
	all i: List.elems.t | i not in List.deleted.t -- List item cannot be deleted
	all i: List.deleted.t | i not in List.elems.t -- Deleted item cannot be in List
	all i: List.elems.t - v_last[t] {
		one i.(v_next[t]) -- Every List item has Next pointer
		i.(v_next[t]) != i -- Acyclicity
		v_last[t] in i.^(v_next[t]) -- Connectivity
	}
	all i: List.deleted.t {
		no i.(v_next[t]) -- Deleted elements have no pointers to the List
	}
	all disj i,j: item - v_last[t]{ i.(v_next[t]) != j.(v_next[t]) } -- Linearity
	List.Prev.t = ~(List.Next.t)  -- Double Linkage
}

---------------------------
-- Sanity-check predicates
---------------------------

pred sc1 [] {
	-- deleting is possible
	some t: Time | some deleted.t
}
pred sc2 [] {
	-- full list is possible
	some t: Time | no deleted.t
}
pred sc3 [] {
	-- nop happens
	some t: Time | noChange[t]
}
pred sc4 [] {
	-- push happens
	some t: Time | some e: item {
		e in List.deleted.(t.prev)
		e in List.elems.t
	}
}
pred sc5 [] {
	-- pop happens
	some t: Time | some e: item {
		e in List.elems.(t.prev)
		e in List.deleted.t
	}
}

