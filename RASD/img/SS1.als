/*SIGNATURES*/
abstract sig ReportType{}
abstract sig Client {}

sig Municipality{
	authority : Authority,
	location : some Location
}
sig Location{
	municipality: one Municipality,
	report: Report
}
lone abstract sig Incident extends ReportType{}
lone abstract sig TrafficViolation extends ReportType{}

sig Guest extends Client {}
abstract sig User extends Client {
	id: one Int
} {id >0}
sig Citizen extends User {
	send: Report -> ReportManager 
}
sig Authority extends User {
	badgeNumber: one Int,
	municipality: one Municipality
}{badgeNumber>0}

sig Report {
	type: one ReportType,
	location: one Location,
	sender: one Citizen,
}
sig ReportManager{
	notify: Report-> Authority,
	store: Report -> DBMS
}
sig Statistics{}
sig Suggestion{}

one sig DBMS{
}
sig InformationManager{
	retrieve: DBMS,
	build: some Statistics,
	compute: some Suggestion
}

/*FUNCTIONS*/
fun getMunicipality[r:Report] : Municipality{
	r.(location.municipality)
}

/*FACTS*/
fact ReportSender{
	all r:Report, c:Citizen,rm:ReportManager | (r.sender=c) <=>( r->rm in c.send)
}
fact ReportStore{
	all rm:ReportManager, r:Report, db:DBMS | r->db in rm.store
}

fact NotifyReportBasedOnTypeAndMunicipality{
	all a:Authority,r:Report,rm:ReportManager | ((r.type = TrafficViolation) and (r.location.municipality =a.municipality)) <=> (r->a in rm.notify) 
}

fact IdsAndBadgesDifferent{
	all disj u1,u2:User | u1.id!=u2.id 
	all c1:Citizen, a1:Authority | (c1.id!=a1.badgeNumber) and (a1.id!=a1.badgeNumber)
	all disj a1,a2:Authority | a1.badgeNumber!=a2.badgeNumber 
}
//UNA LOCATION NON PUO AVERE DUE MUNICIPALITÀ DIVERSE
fact differentLocationSameMunicipality{
	no disj m1,m2:Municipality, l:Location | l.municipality=m1 and l.municipality=m2 
}
/*fact noReportNoMunicipality{
//	all m:Municipality | (some r:Report | getMunicipality[r] = m ) or (some a:Authority | a.municipality = m )	
	//CLAUSOLA CHE FA APPARIRE LE FRECCE ROSSE
	//no l:Location | (all r:Report | l = r.location)
}*/
fact noReportNoMunicipality{
	all m:Municipality, a:Authority | m in a.municipality <=> a in m.authority
}
fact noReportNoLocation{
	all l:Location,r:Report | l in r.location <=> r in l.report
}
fact noMunicipalityNoLocation{
	all l:Location, m:Municipality | l in m.location <=> m in l.municipality
}
fact noInfoManagerNoStatistics{
	no s:Statistics, i:InformationManager  | no (s & i.build)
}

fact noInfoManagerNoSuggestion{
	all s:Suggestion,i:InformationManager | s in i.compute
}

/*ASSERTIONS*/
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

/*PREDICATES*/
pred newReport[r:Report, c:Citizen, rm:ReportManager]{
	c.send=c.send + (r -> rm)

}
pred changeMunicipalityofAuthority[a:Authority,m:Municipality]{
	a.municipality=m
}

pred showUser{
}

/*EXECUTION*/
//run changeMunicipalityofAuthority for exactly 6 User, 6 Report,6 Client,1 ReportManager,4 Municipality, 4 Location,1 InformationManager,3 Statistics, 1 Suggestion
//run newReport for exactly 4 User, 6 Report,4 Client ,1 ReportManager,4 Municipality, 4 Location, 1 InformationManager,1 Statistics,1 Suggestion
run showUser for exactly 4 User, 6 Report, 4 Client,1 ReportManager,2 Municipality, 4 Location, 1 InformationManager, 3 Statistics, 3 Suggestion

check notifyReportBasedOnType
check notifyReportBasedOnMunicipality
check WriterReportDifferent
check OneMunicipalityOneAuthority	
