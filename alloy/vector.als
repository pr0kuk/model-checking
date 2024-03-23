module vector
open order[Time] as T
sig Time{}
sig item {}
one sig Vector {
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

fun v_next[t:Time] : item->item { Vector.Next.t }
fun v_prev[t:Time]  : item->item { Vector.Prev.t }
fun v_first[t:Time]  : one item { Vector.First.t }
fun v_last[t:Time]  : one item { Vector.Last.t }

pred pop_back[now:Time] {
	let past = now.prev {
		Vector.deleted.now = Vector.deleted.past + v_last[past]
		Vector.Last.now = (v_last[past]).(v_prev[past])
		noChangeExcept2Items[now, v_last[past], v_last[now]]
	}
}

pred push_back[now:Time, e: item] {
	e in Vector.deleted.now
	let past = now.prev {
		Vector.Last.now = e
		noChangeExcept2Items[now, v_last[past], v_last[now]]
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


pred clear[now: Time] { let past = now.prev { all i: item - v_last[past] | i in Vector.deleted.now }}

pred init [t: Time] { no deleted.t }
pred init2 [t: Time] { #deleted.t > 0 }
pred nop [t: Time] { noChange[t] }
pred transitions[t: Time] {
//	pop_back[t] or nop[t] or (some e: item | push_back[t, e]) or clear[t]
//	nop[t]
//	pop_back[t]
//	some e: item | push_back[t, e]
//	clear[t]
}

pred System {
	init [T/first]
	//all t: Time | #elems.t > 1
	//all t: Time | #deleted.t > 1
	//all t: Time - T/first | #deleted.t > 0
	//all t: Time | (#elems.t + #deleted.t) > 4
	all t: Time - T/first | transitions [t]
}

run {
	System
} for 9 but 2 Time 
