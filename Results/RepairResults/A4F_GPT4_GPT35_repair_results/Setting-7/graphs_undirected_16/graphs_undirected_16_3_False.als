sig Node {
    adj: set Node
}

pred undirected {
    all n: Node | n.adj = ~n.adj
}

pred oriented {
    all n: Node | no (n.adj & ~n.adj)
}

pred acyclic {
    all n: Node | n not in n.^adj
}

pred complete {
    all n: Node | Node - n in n.adj
}

pred noLoops {
    all n: Node | n not in n.adj
}

pred weaklyConnected {
    all n: Node | Node in n.*(adj + ~adj)
}

pred stronglyConnected {
    all n: Node | Node in n.*adj
}

pred transitive {
    all n, m, o: Node | (n -> m in adj and m -> o in adj) implies n -> o in adj
}

assert undirectedRepaired {
    undirected[] iff (all n: Node | n.adj = ~n.adj)
}

assert orientedRepaired {
    oriented[] iff (all n: Node | no (n.adj & ~n.adj))
}

assert acyclicRepaired {
    acyclic[] iff (all n: Node | n not in n.^adj)
}

assert completeRepaired {
    complete[] iff (all n: Node | Node - n in n.adj)
}

assert noLoopsRepaired {
    noLoops[] iff (all n: Node | n not in n.adj)
}

assert weaklyConnectedRepaired {
    weaklyConnected[] iff (all n: Node | Node in n.*(adj + ~adj))
}

assert stronglyConnectedRepaired {
    stronglyConnected[] iff (all n: Node | Node in n.*adj)
}

assert transitiveRepaired {
    transitive[] iff (all n, m, o: Node | (n -> m in adj and m -> o in adj) implies n -> o in adj)
}

check undirectedRepaired expect 0
check orientedRepaired expect 0
check acyclicRepaired expect 0
check completeRepaired expect 0
check noLoopsRepaired expect 0
check weaklyConnectedRepaired expect 0
check stronglyConnectedRepaired expect 0
check transitiveRepaired expect 0