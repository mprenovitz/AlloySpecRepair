/* The registered persons. */
sig Person  {
/* Each person tutors a set of persons. */
Tutors : set Person,
/* Each person teaches a set of classes. */
Teaches : set Class
}

/* The registered groups. */
sig Group {}

/* The registered classes. */
sig Class  {
/* Each class has a set of persons assigned to a group. */
Groups : Person -> Group
}

/* Some persons are teachers. */
sig Teacher extends Person  {}

/* Some persons are students. */
sig Student extends Person  {}

/* Every person is a student. */
pred inv1 {
  all p: Person | p in Student
}

/* There are no teachers. */
pred inv2 {
  no Teacher
}

/* No person is both a student and a teacher. */
pred inv3 {
  no Student & Teacher
}

/* No person is neither a student nor a teacher. */
pred inv4 {
  all p: Person | p in (Student + Teacher)
}

/* There are some classes assigned to teachers. */
pred inv5 {
  some t: Teacher | some t.Teaches
}

/* Every teacher has classes assigned. */
pred inv6 {
  all t: Teacher | some t.Teaches
}

/* Every class has teachers assigned. */
pred inv7 {
  all c: Class | some t: Teacher | c in t.Teaches
}

/* Teachers are assigned at most one class. */
pred inv8 {
  all t: Teacher | lone t.Teaches
}

/* No class has more than one teacher assigned. */
pred inv9 {
  all c: Class | lone t: Teacher | c in t.Teaches
}

/* For every class, every student has a group assigned. */
pred inv10 {
  all c: Class, s: Student | some g: Group | s -> g in c.Groups
}

/* A class only has groups if it has a teacher assigned. */
pred inv11 {
  all c: Class | (some g: Group | some p: Person | p -> g in c.Groups) implies some t: Teacher | c in t.Teaches
}

/* Each teacher is responsible for some groups. */
pred inv12 {
  all t: Teacher | some g: Group | some c: Class | c in t.Teaches and some p: Person | p -> g in c.Groups
}

/* Only teachers tutor, and only students are tutored. */
pred inv13 {
  all p: Person | (p in Teacher iff some p.Tutors) and (p in Student iff some q: Person | q in p.~Tutors)
}

/* Every student in a class is at least tutored by all the teachers assigned to that class. */
pred inv14 {
  all s: Student, c: Class | some g: Group | s -> g in c.Groups implies all t: Teacher | c in t.Teaches implies t -> s in Tutors
}

/* The tutoring chain of every person eventually reaches a Teacher. */
pred inv15 {
  all p: Person | some t: Teacher | t in ^(p.Tutors)
}

/*======== Assertions for Validation ===============*/
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

/*======== Commands for Validation ===============*/
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