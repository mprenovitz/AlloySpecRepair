sig List {
    header: set Node
}

sig Node {
    link: set Node,
    elem: set Int
}

// Correct
fact CardinalityConstraints {
    all l: List | lone l.header
    all n: Node | lone n.link
    all n: Node | one n.elem
}

// Fixed Loop predicate to define a loop in the list.
pred Loop(This: List) {
    some This.header and all n: This.header.*link | n !in n.link
}

assert repair_assert_1{
    all l : List | Loop[l] <=> {no l.header or one n: l.header.*link | n = n.link}
}
check repair_assert_1

pred repair_pred_1{
    all l : List | Loop[l] <=> {no l.header or one n: l.header.*link | n = n.link}
}
run repair_pred_1

// Fixed Sorted predicate to define sortedness of elements in the list.
pred Sorted(This: List) {
    all n: This.header.*link - This.header.last | let next = n.link | some next and n.elem < next.elem
}

pred RepOk(This: List) {
    Loop[This]
    Sorted[This]
}

// Fixed Count predicate to count occurrences of x in the list.
pred Count(This: List, x: Int, result: Int) {
    RepOk[This]
    result = #(n: This.header.*link | n.elem = x)
}

abstract sig Boolean {}
one sig True, False extends Boolean {}

// Fixed Contains predicate to check if x is in the list.
pred Contains(This: List, x: Int, result: Boolean) {
    RepOk[This]
    result = (some n: This.header.*link | n.elem = x) => result = True else result = False
}

fact IGNORE {
    one List
    List.header.*link = Node
}