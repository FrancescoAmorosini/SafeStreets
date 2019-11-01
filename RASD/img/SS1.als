/*SIGNATURE*/
abstract sig ReportType{}
abstract sig Client {}

sig Municipality{
}
sig Location{
	municipality: Municipality
}
one sig Incident extends ReportType{}
one sig TrafficViolation extends ReportType{}


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
sig Statistic{}
sig Suggestion{}
one sig DBMS{
}
sig InformationManager{
	retrieve: DBMS,
	compute: Statistic,
	give: Suggestion
}

/*FACT*/
fact ReportSender{
	all r:Report, c:Citizen,rm:ReportManager | (r.sender=c) <=>( r->rm in c.send)
}

fact NotifyReportBasedOnTypeAndMunicipality{
	all a:Authority,r:Report,rm:ReportManager | ((r.type = TrafficViolation) and (r.location.municipality =a.municipality)) <=> (r->a in rm.notify) 
}
fact UserIdDifferent{
	all disj u1,u2:User | u1.id!=u2.id 
	//all c1:Citizen, a1:Authority | (c1.id!=a1.badgeNumber)
	//all a:Authority | a.id!=a.badgeNumber
	//all disj a1,a2:Authority | a1.badgeNumber!=a2.badgeNumber
	
}
fact IdDifferentFromBadge{
	all c1:Citizen, a1:Authority | (c1.id!=a1.badgeNumber) and (a1.id!=a1.badgeNumber) 
}
fact BadgeNumberDifferent{
	all disj a1,a2:Authority | a1.badgeNumber!=a2.badgeNumber 
}
/*ASSERTION*/

assert notifyReportBasedOnMunicipality{
	no r :Report, a: Authority, rm: ReportManager | (r->a in rm.notify) and (r.location.municipality != a.municipality) 
}
assert notifyReportBasedOnType{
	no r :Report, a: Authority, rm: ReportManager | (r->a in rm.notify) and (r.type = Incident) 
}
assert WriterReportDifferent{
	no disj c1,c2:Citizen, r:Report | r.sender=c1 and r.sender=c2
}
assert OneMunicipalityOneAuthority{
	no disj m1,m2:Municipality, a:Authority | a.municipality=m1 and a.municipality=m2
}
/*check notifyReportBasedOnType
check notifyReportBasedOnMunicipality
check WriterReportDifferent
check OneMunicipalityOneAuthority
*/

/*PREDICATE*/

pred newReport[r:Report, c:Citizen,rm:ReportManager]{
	c.send=c.send + (r -> rm)
}
pred changeMunicipalityofAuthority[a:Authority,m:Municipality]{
	a.municipality=m
}

pred showUser{
#Citizen =3
#Authority=3
#Municipality=4
}
run changeMunicipalityofAuthority for exactly 6 User, 6 Report,6 Client,1 ReportManager,4 Municipality, 4 Location,1 InformationManager,3 Statistic, 1 Suggestion

run newReport for exactly 6 User, 6 Report,6 Client,1 ReportManager,4 Municipality, 4 Location,1 InformationManager,3 Statistic, 1 Suggestion
run showUser for 6 User, 6 Report,6 Client,1 ReportManager,4 Municipality, 4 Location,1 InformationManager,3 Statistic,1 Suggestion


	
