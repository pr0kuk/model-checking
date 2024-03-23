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
	let past = now.prev {
		e in Vector.deleted.past
		Vector.Last.now = e
		(v_last[now]).(v_prev[now]) = v_last[past]
		noChangeExcept2Items[now, v_last[past], v_last[now]]
	}
}

pred pop_front[now:Time] {
	let past = now.prev {
		Vector.deleted.now = Vector.deleted.past + v_first[past]
		Vector.First.now = (v_first[past]).(v_next[past])
		noChangeExcept2Items[now, v_first[past], v_first[now]]
	}
}

pred push_front[now:Time, e: item] {
	let past = now.prev {
		e in Vector.deleted.past
		Vector.First.now = e
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

pred clear[now: Time] { let past = now.prev { all i: item - v_last[past] | i in Vector.deleted.now }}

pred nop [t: Time] { noChange[t] }

pred transitions[t: Time] {
	pop_back[t] or nop[t] or (some e: item | push_back[t, e]) or pop_front[t] or (some e: item | push_front[t, e]) or clear[t]
//	nop[t]
//	pop_back[t]
//	some e: item | push_back[t, e]
//	clear[t]
//	pop_front[t]
//	some e: item | push_front[t, e]
}

pred System { 
	all t: Time - T/first | transitions [t] 
}

run {
	System
} for 2 but 2 Time 

