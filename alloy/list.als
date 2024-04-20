module list
sig item {}
one sig List {
	var First: one item,
	var Last: one item,
	var Next: item -> item,
	var Prev: item -> item,
	var elems: set item,
	var deleted: set item
	}

fun v_next : item->item { List.Next }
fun v_prev  : item->item { List.Prev }
fun v_first  : one item { List.First }
fun v_last  : one item { List.Last }

pred ListIsValid {
	always List.First in List.elems
	always List.Last in List.elems
	always List.First != List.Last
	always no List.Last.v_next
	always no List.Next.v_first
	always all i: item | i in List.elems or i in List.deleted
	always all i: List.elems | i not in List.deleted
	always all i: List.deleted | i not in List.elems
	always all i: List.deleted | no i.v_next
	always all i: List.elems - List.Last {
		one i.v_next
		i.v_next != i
		i.v_next not in List.deleted
		List.Last in i.^v_next	
	}
	always all disj i,j: List.elems {(i.v_next) != (j.v_next)}
	always {List.Prev = ~(List.Next)}
}

pred pop_back {
	List.deleted'= List.deleted+ v_last
	List.Last' = (v_last).(v_prev)
	noChangeExcept2Items[v_last, v_last']
}

pred push_back[e: item] {
		e in List.deleted
		v_last' = e
		(v_last').(v_prev') = v_last
		noChangeExcept2Items[v_last, v_last']
}

pred pop_front {
		List.deleted' = List.deleted+ v_first
		List.First' = (v_first).(v_next)
		noChangeExcept2Items[v_first, v_first']
}

pred push_front[e: item] {
		e in List.deleted
		v_first' = e
		(v_first').(v_next') = v_first
		noChangeExcept2Items[v_first, v_first']
}

pred noChangeExcept2Items [i1, i2: item] { all i:item - i1 - i2 {i.(v_next') = i.(v_next)} }

pred noChange { all i:item {i.(v_next') = i.(v_next)} }

pred clear{ all i: item - v_last - v_first | i in List.deleted' }

pred transitions {
	pop_back or 
	(some e: item | push_back[e]) or 
	pop_front or 
	(some e: item | push_front[e]) or 
	clear
}

fact "init" {
	#item > 4
	#List.elems > 3
}

pred System { 
	eventually transitions
	always ListIsValid
	-- uncomment any of sanity-check predicates to check it
//	sc1
//	sc2
//	sc3
//	sc4
}

run {
	System
} for 5 but 1..2 steps

---------------------------
-- Sanity-check predicates
---------------------------
//
pred sc1 [] {
	-- deleting is possible
	eventually some deleted
}
pred sc2 [] {
	-- full list is possible
	eventually no deleted
}
pred sc3 [] {
	-- push happens
	eventually some e: item {
		e in List.deleted
		e in List.elems'
	}
}
pred sc4 [] {
	-- pop happens
	eventually some e: item {
		e in List.elems
		e in List.deleted'
		#List.elems > 2
	}
}

