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
fun v_prev : item->item { List.Prev }
fun v_first  : one item { List.First }
fun v_last  : one item { List.Last }

pred pop_back {
	--prereq
		#elems > 2

	--action
		List.deleted' = List.deleted + v_last
		List.elems' = List.elems - v_last
		v_last' = v_last.v_prev
		v_last'.v_prev' = v_last'.v_prev
		no v_last'.v_next'

	--postreq
		no v_last.v_next'
		no v_last.v_prev'
		v_first' = v_first
		noChangeExcept2Items[v_last, v_last']
}

pred push_back[e: item] {
	--prereq
		e in List.deleted

	--action
		List.deleted' = List.deleted - e
		List.elems' = List.elems + e
		v_last' = e
		v_last'.v_prev' = v_last
		v_last.v_next' = v_last'

	--postreq
		no v_last'.v_next'
		v_last.v_prev' = v_last.v_prev
		v_first' = v_first
		noChangeExcept2Items[v_last, v_last']
}

pred pop_front {
	--prereq
		#elems > 2

	--action
		List.deleted' = List.deleted+ v_first
		List.elems' = List.elems - v_first
		v_first' = v_first.v_next
		v_first'.v_next' = v_first'.v_next
		no v_first'.v_prev'

	--postreq
		no v_first.v_prev'
		no v_first.v_next'
		v_last' = v_last
		noChangeExcept2Items[v_first, v_first']
}

pred push_front[e: item] {
	--prereq
		e in List.deleted

	--action
		List.deleted' = List.deleted - e
		List.elems' = List.elems + e
		v_first' = e
		v_first'.v_next' = v_first
		v_first.v_prev' = v_first'

	--postreq
		no v_first'.v_prev'
		v_first.v_next'=v_first.v_next
		v_last' = v_last
		noChangeExcept2Items[v_first, v_first']
}

pred clear{ 
	--prereq

	--action
		all i: item - v_last - v_first | i in List.deleted' 
		List.deleted' = item - v_last - v_first
		List.elems' =v_last + v_first

	--postreq
		all i : List.deleted' | no i.v_next' && no i.v_prev'
		v_last' = v_last
		v_first' = v_first
		v_first'.v_next'=v_last'
		v_last'.v_prev'=v_first'
		no v_first'.v_prev'
		no v_last'.v_next'
}

pred noChangeExcept2Items [i1, i2: item] { all i: item - i1 - i2 {i.v_next' = i.v_next && i.v_prev' = i.v_prev} }

pred noChange { all i:item {i.v_next' = i.v_next && i.v_prev' = i.v_prev && List.deleted'=List.deleted && List.elems' = List.elems && v_first' = v_first && v_last' = v_last} }

pred transitions { -- all possible actions with a List
	pop_back or 
	(some e: item | push_back[e]) or 
	pop_front or 
	(some e: item | push_front[e]) or 
	clear or
	noChange
}

pred ListIsValid {
	#List.elems > 1
	List.First in List.elems -- L has the Head
	List.Last in List.elems -- L has the Tail
	List.First != List.Last -- Acyclicity
	List.Prev = ~(List.Next) -- Double Linkage
	no List.Last.v_next -- Last is a Tail
	no List.Next.v_first -- First is a Head
	all i: item | i in List.elems or i in List.deleted -- The union of Elems and Deleted is a complete set
	all i: List.elems | i not in List.deleted -- Elems and Deleted are non-crossing sets
	all i: List.deleted | i not in List.elems -- Elems and Deleted are non-crossing sets
	all i: List.deleted | no i.v_next -- Unconnectivity of Deleted
	all i: List.elems - List.Last  | i.v_next != i -- Acyclicity
	all i: List.elems - List.Last  | one i.v_next -- Connectivity
	all i: List.elems - List.Last  | i.v_next not in List.deleted -- Connectivity
	all i: List.elems - List.Last  | List.Last in i.^v_next	-- Connectivity
	all disj i,j: List.elems {(i.v_next) != (j.v_next)} -- Linearity
}

fact "init" {
	#item > 4
	#List.elems > 3
	ListIsValid
}

run {

	 always transitions

	---------------------------
	 -- eventually !ListIsValid -- invariant check !SHOULD RETURN "NO INSTANCE FOUND"!
	---------------------------

	-- uncomment any of sanity-check predicates to check it
	---------------------------
	-- sc1 -- deleting is possible
	-- sc2 -- full list is possible
	-- sc3 -- push happens
	-- sc4 -- pop happens
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

