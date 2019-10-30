abstract sig User {}
sig EndUser extends User {
violationsSent: set ViolationData,
violationsSeen: set Violation
}
sig Authority extends User {
violations: set ViolationData,
notifications: set ViolationData,
checked: set ViolationData,
warned: set ViolationData,
assignedArea: set Position
}
sig ViolationData {
violation: one Violation,
position: one Position
}
sig Violation {
position: Position
}
sig Position {}

--FACT
--1. a checked violation cannot be in notifications
fact {
all a: Authority |
 all vd: ViolationData |
 (vd in a.notifications implies not(vd in a.checked)) or
 (vd in a.checked implies not(vd in a.notifications))
}

--2. a checked violation cannot be in checked by other authorities
fact {
all vd: ViolationData, a1, a2: Authority |
  not ((a1 != a2 and vd in a1.checked) implies (vd in a2.checked)) 
}

--3. all ViolationData must be in all authority.violations
fact {
all a: Authority |
  ViolationData in a.violations
}

--4. all ViolationData in a.checked cannot be also in a.warned and viceversa
fact {
all a: Authority |
 all vd: ViolationData |
 (vd in a.warned implies not(vd in a.checked)) or
 (vd in a.checked implies not(vd in a.warned))
}

--5. all ViolationData in  a.warned cannot be in a.notifications
fact {
all a: Authority |
 all vd: ViolationData |
 (vd in a.notifications implies not(vd in a.warned)) or
 (vd in a.warned implies not(vd in a.notifications))
}

--6. all ViolationData must be in one user.violationsSent
fact {
all vd: ViolationData | 
one eu: EndUser |
vd in eu.violationsSent
}

--7. two different eu cannot have the same violationdata in eu.vionationssent
fact {
no disj eu1, eu2: EndUser |
(eu1.violationsSent & eu2.violationsSent) != none
}

--8. all the violationdata sent by the end user must be seen by it (and sent 
--from the position the violation occurred)
fact {
all vd: ViolationData, eu: EndUser |
(vd in eu.violationsSent) <=> (vd.violation in eu.violationsSeen)
}

--9. all violationdata must be in a.notifications only if vd.position in 
--a.assignedarea
fact {
all vd: ViolationData, a: Authority |
(vd in a.notifications) <=> (vd.position in a.assignedArea)
}

--10. all violationdata.position must be equal to violationdata.violatio.position
fact {
all vd: ViolationData, v: Violation |
(vd.violation = v) <=> (vd.position = v.position)
}

--PREDICATES
--1. an end user sees a new violation and sends it
pred seeViolation [v: Violation, vd: ViolationData, eu, eu': EndUser] {
eu'.violationsSeen = eu.violationsSeen + v
eu'.violationsSent = eu.violationsSent + vd
}

--2. an authority checks a violationdata
pred checkViolation [a, a': Authority, vd: ViolationData] {
a'.checked = a.checked + vd
a'.notifications = a.notifications - vd
}


pred show  [a, a': Authority, vd: ViolationData] {
checkViolation [a, a', vd]
}
--run show for 5


--ASSERTIONS
--1. if a end user sees and send a violation, the violation must be 
--viewable by all the authorities
assert viewSentViolation {
all a: Authority, v: Violation, vd: ViolationData, eu, eu': EndUser |
seeViolation [v, vd, eu, eu'] implies
            vd in a.violations
}
--check viewSentViolation for 3

--2. if an end user send a new violationdata, another end user cannot see it
assert seeAnotherUserSentViolation {
all vd: ViolationData, v: Violation |
no eu1, eu1', eu2: EndUser |
(seeViolation [v, vd, eu1, eu1'] and eu1 != eu2 and eu1' != eu2 and
(eu1'.violationsSent & eu2.violationsSent != none))
}
--check seeAnotherUserSentViolation for 10

--3. if an authority checks a violationdata another authority cannot check the 
-- same violationdata
assert doubleCheck {
all vd: ViolationData |
no a1, a1', a2: Authority |
  (a1 != a2 and a1' != a2 and checkViolation [a1, a1', vd] and 
        (a1'.checked & a2.checked != none))
}
--check doubleCheck for 10




