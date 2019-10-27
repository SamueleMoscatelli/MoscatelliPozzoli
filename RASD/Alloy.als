sig abstract User {
read: some  TrafficViolationStatistics
}

sig EndUser extends User {
send: set ViolationData
}

sig Authority extends User {
see: set ViolationData,
position: position
notifications: set ViolationData
warned: set ViolationData
checked: set ViolationData
}

sig Municipality extends User {
see: set UnsafeArea,
send: AccidentData
}

sig ViolationData {
description: Description,
licensePlate: LicencePlate,
type: ViolationType,
date: Date,
time:Time,
position: Position
}

sig TrafficViolationStatistics {}

sig UnsafeArea {
position: Position,
interventions: set Intervention
}

sig Intervention {}

sig AccidentData {
date: Date,
time: Time,
position: Position
}

sig LicensePlate {}

sig Date {}

sig Time {}

sig ViolationType{}

sig Position {}

sig Description {}



-- FACTS
--1. a violation can belong to no more than one EndUser
fact {
no disj eu1, eu2: EndUser | 
        all v: ViolationData |
         ( v in eu1.send and  v in eu2.send)
}

--2. each violation has an EndUser who sent it
fact {
all v: ViolationData | 
  one eu: EndUser |
     v in eu.send
}

--3. all warned violations can't be in notifications (for authority)
fact {
no one a: Autority |
       one v: ViolationData | 
         ( v in a.notifications and v in a.warned)
}

--4. a violation checked by an authority can't be chacked by another one
fact {
all v: ViolationData |
  no disj a1, a2: Authority |
         ( v in a1.chacked and v in a2.checked)
}

--5. a violation can't be at the same time warned and checked for the same 
--authority
fact {
all a: authority |
  (a.warned & a. checked = none)
}
--alternativa
fact {
no v: ViolationData |
  one a: Authority |
    (v in a.warned and v in a.checked)
}











