abstract sig User {}
sig EndUser extends User {
violationsSent: set ViolationData,
violationsSeen: set Violation
}
sig Authority extends User {
violations: set ViolationData,
notifications: set ViolationData,
checked: set ViolationData,
warned: set ViolationData
}
sig ViolationData {
violation: one Violation
}
sig Violation {}

--FACT
--1. a checked violation cannot be in notifications
fact {
all a: Authority |
 all vd: ViolationData |
 (vd in a.notifications implies not(vd in a.checked)) or
 (vd in a.checked implies not(vd in a.notifications))
}

--2. a checked violation cannot be in notifications of other authorities and 
--also in their checked
fact {
all vd: ViolationData |
no disj a1, a2: Authority |
  ((vd in a1.checked) implies not (vd in a2.checked)) 
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


--PREDICATES
--1. an end user sees a new violation and sends it
pred seeViolation [v: Violation, vd: ViolationData, eu, eu': EndUser] {
eu'.violationsSeen = eu.violationsSeen + v
vd.violation = v
eu'.violationsSent = eu.violationsSent + vd
}


pred show [v: Violation, vd: ViolationData, eu, eu': EndUser] {
seeViolation [v, vd, eu, eu']
}
--run show for 15


--ASSERTIONS
--1. if a end user sees and send a violation, the violation must be 
--viewable by all the authorities
assert viewSentViolation {
all a: Authority |
 one v: Violation, vd: ViolationData, eu, eu': EndUser |
seeViolation [v, vd, eu, eu'] implies
            vd in a.violations
}

check viewSentViolation for 3







