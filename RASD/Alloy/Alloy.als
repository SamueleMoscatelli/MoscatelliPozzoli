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
sig Municipality extends User{
unsafeareas: set UnsafeArea
}
sig UnsafeArea{
area: set Position,
intervention: lone Intervention
}
sig Intervention{}


--FACT
--1. a checked violation cannot be in notifications
fact {
all a: Authority |
 no vd: ViolationData |
 vd in a.notifications and vd in a.checked
}

--2. a checked violation cannot be in checked by other authorities
fact {
all vd: ViolationData |
no disj a1, a2: Authority |
  vd in a1.checked and vd in a2.checked
}

--3. all ViolationData must be in all authority.violations
fact {
all a: Authority |
  ViolationData in a.violations
}

--4. all ViolationData in a.checked cannot be also in a.warned and viceversa
fact {
all a: Authority |
 no vd: ViolationData |
 vd in a.warned and vd in a.checked
}

--5. all ViolationData in  a.warned cannot be in a.notifications
fact {
all a: Authority |
 no vd: ViolationData |
  vd in a.notifications and vd in a.warned
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
all a: Authority, vd: ViolationData |
(vd in a.notifications) implies (vd.position in a.assignedArea)
}

--10. all violationdata.position must be equal to violationdata.violation.position
fact {
all vd: ViolationData, v: Violation |
(vd.violation = v) <=> (vd.position = v.position)
}

--11. two different municipality cannot have the same unsafearea
fact{
no disj mun1, mun2: Municipality |
(mun1.unsafeareas & mun2.unsafeareas) != none
}

--12. unsafe area must be in a municipality
fact{
all ua: UnsafeArea | 
some mun: Municipality |
ua in mun.unsafeareas
}

--13. all interventions must be in at least one usafearea
fact{
all inte: Intervention |
some ua: UnsafeArea |
inte in ua.intervention
}

--14. two different unsafeareas cannot have the same area
fact{
no disj ua1, ua2: UnsafeArea |
(ua1.area & ua2.area) != none
}

--15. all unsafe area must have at least one position
fact{
all ua: UnsafeArea |
some pos: Position |
pos in ua.area
}



--PREDICATES
--1. an end user sees a new violation and sends it
pred seeViolation [v: Violation, vd: ViolationData, eu, eu': EndUser] {
--preconditions
vd not in eu.violationsSent
v not in eu.violationsSeen
--postconditions
eu'.violationsSeen = eu.violationsSeen + v
eu'.violationsSent = eu.violationsSent + vd
}

--run seeViolation for 5 but exactly 3 EndUser, exactly 1 UnsafeArea, exactly 1 Authority, exactly 3 ViolationData

--2. an authority checks a violationdata
pred checkViolation [a, a': Authority, vd: ViolationData] {
--preconditions
vd not in a.checked
vd in a.notifications
--postconditions
a'.checked = a.checked + vd
a'.notifications = a.notifications - vd
}

--run checkViolation for 3 but exactly 2 Authority, exactly 3 ViolationData, exactly 1 EndUser

--3. authority notified
pred notifyAuthority [a, a': Authority, vd: ViolationData] {
--preconditions
vd.position in a.assignedArea
--postconditions
a'.notifications = a.notifications + vd
}

--run notifyAuthority for 4 but exactly 2 EndUser, 3 Violation 

--4. a new unsafearea is detected 
pred newUnsafeArea [mun, mun': Municipality, ua: UnsafeArea]{
--preconditions
ua not in mun.unsafeareas
--postconditions
mun'.unsafeareas = mun.unsafeareas + ua
}

--run newUnsafeArea for 4 but exactly 4 UnsafeArea


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

--4. if a violationdata is notified to an authoritiy it must be notified to all the 
-- other authorities assigned to an area which comprehend the position of the 
-- violation
assert allInterestedAuthoritiesNotified {
all a1, a1', a2: Authority, vd: ViolationData |
 (notifyAuthority [a1, a1', vd] and a1 != a2 and a1' != a2 and
   vd.position in a2.assignedArea) implies
							(vd in a2.notifications)
}
--check allInterestedAuthoritiesNotified for 3

--5. if a new UnsafeArea is inserted, it is associated to only one municipality
assert onlyOneMunicipalityAssociated{
all mun, mun1, mun2: Municipality, ua: UnsafeArea |
(newUnsafeArea [mun, mun1, ua] and mun1!=mun2) implies
(ua in mun1.unsafeareas and ua not in mun.unsafeareas and ua not in mun2.unsafeareas)
}
--check onlyOneMunicipalityAssociated for 5

