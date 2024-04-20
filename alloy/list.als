module list
sig item {}
one sig List {
	var First: one item, -- list head
	var Last: one item, -- list tail
	var Next: item -> item,
	var Prev: item -> item,
	var elems: set item, -- items belong to the list
	var deleted: set item -- items do not belong to the list
}

fun v_next : item->item { List.Next }
fun v_prev  : item->item { List.Prev }
fun v_first  : one item { List.First }
fun v_last  : one item { List.Last }

pred pop_back {
	--prereq
		#elems > 2

	--action
		List.deleted'= List.deleted+ v_last
		List.Last' = (v_last).(v_prev)

	--postreq
	noChangeExcept2Items[v_last, v_last']
}

pred push_back[e: item] {
	--prereq
		e in List.deleted

	--action
		v_last' = e
		(v_last').(v_prev') = v_last

	--postreq
		noChangeExcept2Items[v_last, v_last']
}

pred pop_front {
	--prereq
		#elems > 2

	--action
		List.deleted' = List.deleted+ v_first
		List.First' = (v_first).(v_next)

	--postreq
		noChangeExcept2Items[v_first, v_first']
}

pred push_front[e: item] {
	--prereq
		e in List.deleted

	--action
		v_first' = e
		(v_first').(v_next') = v_first

	--postreq
		noChangeExcept2Items[v_first, v_first']
}

pred clear{ all i: item - v_last - v_first | i in List.deleted' }

pred noChangeExcept2Items [i1, i2: item] { all i:item - i1 - i2 {i.(v_next') = i.(v_next)} }

pred noChange { all i:item {i.(v_next') = i.(v_next)} }

pred transitions { -- all possible actions with a List
	pop_back or 
	(some e: item | push_back[e]) or 
	pop_front or 
	(some e: item | push_front[e]) or 
	clear
}

pred ListIsValid {
	always List.First in List.elems -- L has the Head
	always List.Last in List.elems -- L has the Tail
	always List.First != List.Last -- Acyclicity
	always List.Prev = ~(List.Next) -- Double Linkage
	always no List.Last.v_next -- Last is a Tail
	always no List.Next.v_first -- First is a Head
	always all i: item | i in List.elems or i in List.deleted -- The union of Elems and Deleted is a complete set
	always all i: List.elems | i not in List.deleted -- Elems and Deleted are non-crossing sets
	always all i: List.deleted | i not in List.elems -- Elems and Deleted are non-crossing sets
	always all i: List.deleted | no i.v_next -- Unconnectivity of Deleted
	always all i: List.elems - List.Last  | i.v_next != i -- Acyclicity
	always all i: List.elems - List.Last  | one i.v_next -- Connectivity
	always all i: List.elems - List.Last  | i.v_next not in List.deleted -- Connectivity
	always all i: List.elems - List.Last  | List.Last in i.^v_next	-- Connectivity
	always all disj i,j: List.elems {(i.v_next) != (j.v_next)} -- Linearity
}

fact "init" {
	#item > 4
	#List.elems > 3
	ListIsValid
}

run {
	eventually transitions

	---------------------------
	-- eventually !ListIsValid -- invariant check !SHOUULD RETURN NO INSTANCE FOUND!
	---------------------------

	-- uncomment any of sanity-check predicates to check it
	---------------------------
	--sc1 -- deleting is possible
	--sc2 -- full list is possible
	--sc3 -- push happens
	--sc4 -- pop happens
	---------------------------

} for 5 but 1..2 steps

---------------------------
-- Sanity-check predicates
---------------------------

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

