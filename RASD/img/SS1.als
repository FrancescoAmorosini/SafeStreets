/*SIGNATURES*/
abstract sig ReportType{}
abstract sig Client {}

sig Municipality{
}
sig Location{
	municipality: one Municipality
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
lone sig ReportManager{
	notify: Report-> Authority,
	store: Report -> DBMS
}
lone sig Statistics{}
lone sig Suggestions{}

lone sig DBMS{
}
lone sig InformationManager{
	retrieve: DBMS,
	build: some Statistics,
	compute: some Suggestions,
	giveStats: Statistics -> User,
	giveSugg: Suggestions -> User
}
lone sig LoginManager{
	guests : set Guest,
	logged : Int -> User
}

/*FUNCTIONS*/
fun getMunicipality[r:Report] : Municipality{
	r.(location.municipality)
}

/*FACTS*/
fact ReportSender{
	all r:Report, c:Citizen |one rm:ReportManager | (r.sender=c) <=>( r->rm in c.send)
}
fact ReportStore{
	all rm:ReportManager, r:Report |one db:DBMS | r->db in rm.store
}
fact NotifyReportBasedOnTypeAndMunicipality{
	all a:Authority,r:Report |one rm:ReportManager | ((r.type = TrafficViolation) and (r.location.municipality =a.municipality)) <=> (r->a in rm.notify) 
}
fact IdsAndBadgesDifferent{
	all disj u1,u2:User | u1.id!=u2.id 
	all c1:Citizen, a1:Authority | (c1.id!=a1.badgeNumber) and (a1.id!=a1.badgeNumber)
	all disj a1,a2:Authority | a1.badgeNumber!=a2.badgeNumber 
}
fact noReportNoMunicipality{
	all m:Municipality | (some r:Report | getMunicipality[r] = m ) or (some a:Authority | a.municipality = m )	
	no l:Location | (no r:Report | l = r.location)
}
fact noInfoManagerNoStatistics{
	all s:Statistics| one i:InformationManager | s in i.build 
	all s:Suggestions| one i:InformationManager | s in i.compute
}
fact giveStatsAndSuggs{
	all im:InformationManager, u:User, s:Statistics, su: Suggestions | (u.badgeNumber != none and s->u in im.giveStats) <=> (su -> u in im.giveSugg)
}
fact allClientsInLM{
	all g:Guest | one  lm:LoginManager | g in lm.guests
	all u:User | one lm:LoginManager | u.id -> u in lm.logged
	//no i1:Int, i2:Int, u:User, lm:LoginManager| (i1->u in lm.logged) and (i2->u in lm.logged)
}
fact PositiveId{
	all i:Int, u:User, lm:LoginManager |  i->u in lm.logged => i>0 
}
fact SingleId{
	 no disj i1,i2:Int, u:User, lm:LoginManager | i1->u in lm.logged and i2->u in lm.logged 
	//all c:Citizen,lm:LoginManager | #lm.logged.indsOf[c] =1	 
	//#lm.logged.indsOf[u] =1
}
fact IDBadge{
all a:Authority,i:Int | one lm:LoginManager | i->a in lm.logged implies a.badgeNumber!=a.id
}
fact fact2{
	no v:TrafficViolation| ( no r: Report | r.type = v)
	no i:Incident| ( no r: Report | r.type = i)	
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
assert aa{
no a:Authority | a.id = a.badgeNumber
}


/*PREDICATES*/
pred newReport[r:Report, c:Citizen, rm:ReportManager]{
	c.send=c.send + (r -> rm)

	#Municipality = 4
	#ReportManager = 1
	#Citizen = 3
	#Authority = 3

}
pred changeMunicipalityofAuthority[a:Authority,m:Municipality]{
	a.municipality=m
}
pred loginUser[u:User, id:Int, lm:LoginManager]{
	#lm.guests = #lm.guests - 1
	lm.logged = lm.logged + (id -> u) 
	
	

	#InformationManager = 0
	#ReportManager = 0
	#LoginManager = 1

}

pred showUser{
	#InformationManager = 1
	#ReportManager = 1
	#LoginManager = 1
}

pred giveStatistics[u:User, im:InformationManager]{
	im.giveStats = im.giveStats + (im.build -> u)
	
	u.badgeNumber != none => (im.giveSugg = im.giveSugg + im.compute -> u)

	#im.giveStats = 3
}

/*EXECUTION*/
//run changeMunicipalityofAuthority for exactly 6 User, 6 Report,6 Client,1 ReportManager,4 Municipality, 4 Location,1 InformationManager,3 Statistics, 1 Suggestions
//run newReport for exactly 6 User, 6 Report,6 Client ,1 ReportManager,4 Municipality, 4 Location, 0 InformationManager,0 Statistics,0 Suggestions
//run giveStatistics for exactly 6 User, 0 Report, 6 Client,0 ReportManager,4 Municipality, 4 Location, 1 InformationManager
//run loginUser for 4

run showUser 

check notifyReportBasedOnType
check notifyReportBasedOnMunicipality
check WriterReportDifferent
check OneMunicipalityOneAuthority
