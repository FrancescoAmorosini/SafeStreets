abstract sig ReportType{}
sig Municipality{
}
sig Location{
	municipality: Municipality
}
one sig Incident extends ReportType{}
one sig TrafficViolation extends ReportType{}

abstract sig Client {}
sig Guest extends Client {}
abstract sig User extends Client {
	id: one Int
} {id >0}
sig Citizen extends User {
	send: Report -> ReportManager 
}
sig Authority extends User {
	badgeNumber: one Int,
	municipality: Municipality
}{badgeNumber>0}

sig Report {
	type: one ReportType,
	location: one Location,
	//date: one Date,
	//time: one Time,
	//picture: lone Picture,
	sender: one Citizen,
}
sig ReportManager{
	notify: Report-> Authority
}

fact ReportSender{
	all r:Report, c:Citizen,rm:ReportManager | (r.sender=c) <=>( r->rm in c.send)
}

fact NotifyReportBasedOnTypeAndMunicipality{
	all a:Authority,r:Report,rm:ReportManager | ((r.type = TrafficViolation) and (r.location.municipality =a.municipality)) <=> (r->a in rm.notify) 
}
fact IdDifferentFromBadge{
	all disj u1,u2:User | u1.id!=u2.id 
	all c1:Citizen, a1:Authority | (c1.id!=a1.badgeNumber)
	all a:Authority | a.id!=a.badgeNumber
	all disj a1,a2:Authority | a1.badgeNumber!=a2.badgeNumber
	
}
/*
pred pred1[a:Authority, r:Report, rm:ReportManager]{
	
	((r.type = TrafficViolation) and (r.location.municipality =a.municipality)) <=> (r->a in rm.notify)
}


assert assert1{
	no r :Report, a: Authority, rm: ReportManager | (r->a in rm.notify) and (r.location.municipality != a.municipality) 
}
check assert1
*/
pred showUser{
#Citizen =3
#Authority=3
#Municipality=4
}
run showUser for 6 User, 4 Report,6 Client,1 ReportManager,4 Municipality, 4 Location
//run pred1  for 6 User, 4 Report,6 Client,1 ReportManager,4 Municipality, 4 Location

	
