module ordering[exactly item]

one sig Order {
	First: set item,
	Last: set item,
	Next: item -> item,
	Prev: item -> item
	} {
	one First
	one Last
	First != Last
	no Last.Next
	no Next.First
	all i: item - Last {
		one i.Next 
		Last in i.^Next
	} 
	all disj i,j: item - Last {
		i.Next != j.Next
	}
	Prev = ~Next
}

fun next(i: one item) : set item {
	Order.Next[i]
}

fun previous(i: one item): set item {
	Order.Prev[i]
}
run {} for 4
