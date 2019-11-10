
	/*SIGNATURES*/
	abstract sig ReportType{}
	lone abstract sig Incident extends ReportType{}
	lone abstract sig TrafficViolation extends ReportType{}
	lone sig Statistics{}
	lone sig Suggestions{}
	lone sig DBMS{}
	
	sig Municipality{}
	sig Location{
		municipality: one Municipality
	}
	
	abstract sig Client {}
	sig Guest extends Client {}
	abstract sig User extends Client {
		id: one Int
	}
	sig Citizen extends User {
		send: Report -> ReportManager 
	}
	sig Authority extends User {
		badgeNumber: one Int,
		municipality: one Municipality
	}
	
	sig Report {
		type: one ReportType,
		location: one Location,
		sender: one Citizen,
	}
	
	lone sig ReportManager{
		notify: Report-> Authority,
		store: Report -> DBMS
	}
	lone sig InformationManager{
		retrieve: DBMS,
		build: lone Statistics,
		compute: lone Suggestions,
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
	fact reportSend{
		all r:Report, c:Citizen |one rm:ReportManager | (r.sender=c) <=>( r->rm in c.send)
	}
	fact reportStore{
		all rm:ReportManager, r:Report |one db:DBMS | r->db in rm.store
	}
	fact notifyReportBasedOnTypeAndMunicipality{
		all a:Authority,r:Report |one rm:ReportManager | ((r.type = TrafficViolation) and (r.location.municipality =a.municipality)) <=> (r->a in rm.notify) 
	}
	fact idsAndBadgesDifferent{
		all disj u1,u2:User | u1.id!=u2.id 
		all disj a1,a2:Authority | a1.badgeNumber!=a2.badgeNumber 
		all u1:User, a1:Authority | (u1.id!=a1.badgeNumber) and (a1.id!=a1.badgeNumber)
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
		all u:User, im:InformationManager | (im.build != none) implies (im.build -> u in im.giveStats)
		all im:InformationManager, u:User, s:Statistics, su: Suggestions | (u.badgeNumber != none and s->u in im.giveStats) <=> (su -> u in im.giveSugg)
		no c:Citizen, s:Suggestions, im:InformationManager | s->c in im.giveSugg
	}
	fact allUsersInLM{
		lone g:Guest | one  lm:LoginManager | !(g in lm.guests)
		no u:User| one lm:LoginManager | !u.id -> u in lm.logged
		all c:Citizen | (#LoginManager = 0 and #ReportManager = 1) implies #c.send > 0
		#LoginManager = 0 implies #Guest = 0

	}
	fact positiveId{
		all i:Int, u:User | (u.id = i implies i > 0) and (u.badgeNumber != none implies u.badgeNumber > 0)
		all i:Int, u:User, lm:LoginManager |  i->u in lm.logged implies i>0 
	}
	fact singleId{
		no disj i1,i2:Int, u:User, lm:LoginManager | i1->u in lm.logged and i2->u in lm.logged 
	}
	fact noTypesWithoutReport{
		no v:TrafficViolation| ( no r: Report | r.type = v)
		no i:Incident| ( no r: Report | r.type = i)	
	}
	fact aloneDBMS{
		(#InformationManager = 0 and #ReportManager = 0) implies #DBMS = 0
	}
	
	/*ASSERTIONS*/
	assert allDifferendIdsBadges{
	no disj u1,u2:User| (u1.id = u2.id) or (u2.badgeNumber != none and u1.id = u2.badgeNumber) or (u1.badgeNumber != none and u2.badgeNumber != none and  u1.badgeNumber = u2.badgeNumber)
	}
	assert oneMunicipalityOneAuthority{
		no disj m1,m2:Municipality, a:Authority | a.municipality=m1 and a.municipality=m2
	}
	assert writerReportDifferent{
		no disj c1,c2:Citizen, r:Report | r.sender=c1 and r.sender=c2
	}
	assert allReportHasWriter{
		no r:Report | no c:Citizen | r.sender = c
	}
	assert notifyReportBasedOnMunicipality{
		no r :Report, a: Authority, rm: ReportManager | (r->a in rm.notify) and (r.location.municipality != a.municipality) 
	}
	assert notifyReportBasedOnType{
		no r :Report, a: Authority, rm: ReportManager | (r->a in rm.notify) and (r.type = Incident) 
	}
	assert suggestionsVisibility{
		no c:Citizen, im:InformationManager |(im.compute != none) and (im.compute -> c in im.giveSugg)
	}
	assert allUsersCanSeeStatistics{
		no u:User, im:InformationManager | (im.build != none) and !(im.build -> u in im.giveStats)
	}
	assert noWanderingClient{
		all c:Client | all r:Report, im:InformationManager, lm:LoginManager| (r.sender = c) or (c in lm.guests or c.id->c in lm.logged) or (im.build ->c in im.giveStats) or (c.municipality != none)
	} 
	assert allUsersLoggedWithID{
		no u:User, lm:LoginManager, i:Int | (i->u in lm.logged) and (i != u.id)
	}
	assert onlyRMandIMaccessDBMS{
		no d:DBMS, rm:ReportManager, im:InformationManager | rm = none and im = none and d != none
	}
	
	/*PREDICATES*/
	pred newReport[r:Report, c:Citizen, rm:ReportManager]{
		!disconnectedGuest
		c.send=c.send + (r -> rm)

		#LoginManager = 0
		#InformationManager = 0
		#ReportManager = 1
		#ReportManager.notify = 1
	}
	pred loginUser[g:Guest, u:User, id:Int, lm:LoginManager]{
		disconnectedGuest
		lm.logged = lm.logged + (id -> u) 

		#ReportManager = 0
		#InformationManager = 0
		#User = 2
		#Guest = 2
	}
	pred disconnectedGuest{
		one g:Guest | one  lm:LoginManager | !(g in lm.guests)
	}
	pred showUser{
		!disconnectedGuest

		#LoginManager = 1
		#InformationManager = 1
		#ReportManager = 1
		#InformationManager.giveSugg = 1
		#InformationManager.giveStats = 2
		#ReportManager.notify = 2
	}
	pred giveStatistics[u:User, im:InformationManager, s:Statistics, sugg:Suggestions]{
		im.giveStats = im.giveStats + (s -> u)

		#im.giveStats = 1
		#im.giveSugg = 2
	}
	pred giveAll[s:Statistics, sugg:Suggestions, im:InformationManager]{
		all u:User | giveStatistics[u, im, s, sugg]

		#ReportManager = 0
		#LoginManager = 0
	}

/*EXECUTION*/
run showUser for 6 but 4 Int
run newReport for 6 but 4 Int
run giveAll for 6 but 4 Int
run loginUser for 6 but 4 Int

check allDifferendIdsBadges
check oneMunicipalityOneAuthority
check writerReportDifferent
check notifyReportBasedOnType
check notifyReportBasedOnMunicipality
check allUsersCanSeeStatistics
check suggestionsVisibility
check allUsersLoggedWithID
check noWanderingClient
check onlyRMandIMaccessDBMS