sig Person  {
    Tutors : set Person,
    Teaches : set Class
}

sig Group {}

sig Class  {
    Groups : Person -> Group
}

sig Teacher extends Person  {}

sig Student extends Person  {}

pred inv1 {
    all p: Person | p in Student
}

pred inv2 {
    no Teacher
}

pred inv3 {
    no Student & Teacher
}

pred inv4 {
    all p: Person | p in (Student + Teacher)
}

pred inv5 {
    some t: Teacher | some t.Teaches
}

pred inv6 {
    all t: Teacher | some t.Teaches
}

pred inv7 {
    all c: Class | some t: Teacher | c in t.Teaches
}

pred inv8 {
    all t: Teacher | lone t.Teaches
}

pred inv9 {
    all c: Class | lone t: Teacher | c in t.Teaches
}

pred inv10 {
    all c: Class, s: Student | some g: Group | s -> g in c.Groups
}

pred inv11 {
    all c: Class | (some g: Group | some p: Person | p -> g in c.Groups) implies some t: Teacher | c in t.Teaches
}

pred inv12 {
    all t: Teacher | some g: Group | some c: Class | c in t.Teaches and some p: Person | p -> g in c.Groups
}

pred inv13 {
    all p: Person | (p in Teacher implies no p.Tutors) and (p in Student implies some p.Tutors)
}

pred inv14 {
    all s: Student, c: Class | (some g: Group | s -> g in c.Groups) implies all t: Teacher | c in t.Teaches implies t -> s in Tutors
}

pred inv15 {
    all s: Person | some t: Teacher | t in ^(s.Tutors)
}

assert inv1_Repaired {
    inv1[]
}

assert inv2_Repaired {
    inv2[]
}

assert inv3_Repaired {
    inv3[]
}

assert inv4_Repaired {
    inv4[]
}

assert inv5_Repaired {
    inv5[]
}

assert inv6_Repaired {
    inv6[]
}

assert inv7_Repaired {
    inv7[]
}

assert inv8_Repaired {
    inv8[]
}

assert inv9_Repaired {
    inv9[]
}

assert inv10_Repaired {
    inv10[]
}

assert inv11_Repaired {
    inv11[]
}

assert inv12_Repaired {
    inv12[]
}

assert inv13_Repaired {
    inv13[]
}

assert inv14_Repaired {
    inv14[]
}

assert inv15_Repaired {
    inv15[]
}

check inv1_Repaired expect 0
check inv2_Repaired expect 0
check inv3_Repaired expect 0
check inv4_Repaired expect 0
check inv5_Repaired expect 0
check inv6_Repaired expect 0
check inv7_Repaired expect 0
check inv8_Repaired expect 0
check inv9_Repaired expect 0
check inv10_Repaired expect 0
check inv11_Repaired expect 0
check inv12_Repaired expect 0
check inv13_Repaired expect 0
check inv14_Repaired expect 0
check inv15_Repaired expect 0