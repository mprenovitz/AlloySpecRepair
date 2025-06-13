sig Node {
    adj: set Node
}

pred undirected {
    all n1, n2: Node | n1 in n2.adj iff n2 in n1.adj
}

pred oriented {
    all n1, n2: Node | n1 in n2.adj implies n2 not in n1.adj
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
    all n1, n2, n3: Node | n2 in n1.adj and n3 in n2.adj implies n3 in n1.adj
}

pred undirectedOK {
    all n1, n2: Node | n1 in n2.adj iff n2 in n1.adj
}

assert undirectedRepaired {
    undirected[] iff undirectedOK[]
}

pred orientedOK {
    all n1, n2: Node | n1 in n2.adj implies n2 not in n1.adj
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
    all n: Node | n not in n.adj
}

assert noLoopsRepaired {
    noLoops[] iff noLoopsOK[]
}

pred weaklyConnectedOK {
    all n: Node | Node in n.*(adj + ~adj)
}

assert weaklyConnectedRepaired {
    weaklyConnected[] iff weaklyConnectedOK[]
}

pred stronglyConnectedOK {
    all n: Node | Node in n.*adj
}

assert stronglyConnectedRepaired {
    stronglyConnected[] iff stronglyConnectedOK[]
}

pred transitiveOK {
    all n1, n2, n3: Node | n2 in n1.adj and n3 in n2.adj implies n3 in n1.adj
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