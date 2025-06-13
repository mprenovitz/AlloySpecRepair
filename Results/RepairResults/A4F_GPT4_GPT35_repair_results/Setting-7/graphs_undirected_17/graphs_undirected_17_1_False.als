sig Node {
    adj: set Node
}

pred undirected {
    all n, m: Node | n in m.adj iff m in n.adj
}

pred oriented {
    no n: Node | n in n.adj
}

pred acyclic {
    all n: Node | n not in n.^adj
}

pred complete {
    all n: Node | Node - n in n.adj
}

pred noLoops {
    no n: Node | n in n.adj
}

pred weaklyConnected {
    all n, m: Node | m in n.*(adj + ~adj)
}

pred stronglyConnected {
    all n, m: Node | m in n.*adj
}

pred transitive {
    all n, m, o: Node | (m in n.adj and o in m.adj) implies o in n.adj
}

pred undirectedOK {
    adj = ~adj
}

assert undirectedRepaired {
    undirected[] iff undirectedOK[]
}

pred orientedOK {
    no n: Node | n in n.adj
}

assert orientedRepaired {
    oriented[] iff orientedOK[]
}

pred acyclicOK {
    all n: Node | n not in n.^adj
}

assert acyclicRepaired {
    acyclic[] iff acyclicOK[]
}

pred completeOK {
    all n: Node | Node - n in n.adj
}

assert completeRepaired {
    complete[] iff completeOK[]
}

pred noLoopsOK {
    no n: Node | n in n.adj
}

assert noLoopsRepaired {
    noLoops[] iff noLoopsOK[]
}

pred weaklyConnectedOK {
    all n, m: Node | m in n.*(adj + ~adj)
}

assert weaklyConnectedRepaired {
    weaklyConnected[] iff weaklyConnectedOK[]
}

pred stronglyConnectedOK {
    all n, m: Node | m in n.*adj
}

assert stronglyConnectedRepaired {
    stronglyConnected[] iff stronglyConnectedOK[]
}

pred transitiveOK {
    all n, m, o: Node | (m in n.adj and o in m.adj) implies o in n.adj
}

assert transitiveRepaired {
    transitive[] iff transitiveOK[]
}

check undirectedRepaired expect 0
check orientedRepaired expect 0
check acyclicRepaired expect 0
check completeRepaired expect 0
check noLoopsRepaired expect 0
check weaklyConnectedRepaired expect 0
check stronglyConnectedRepaired expect 0
check transitiveRepaired expect 0