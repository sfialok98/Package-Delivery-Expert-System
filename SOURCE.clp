;Group No 8
;Section B

(deffacts startup 
(clear)
(start-reading-file)

;****************************************************************************************************************

;Path to input files

;****************************************************************************************************************
(CITIES-FILE-PATH "cities.txt")
(TRUCKS-FILE-PATH "trucks.txt")
(PACKAGES-FILE-PATH "packages.txt")


;****************************************************************************************************************
;	FACTS ASSERTED DETAILS:
;
;			Truck-statistics -> Contains the statistics for each truck by its index.
;			Package-statistics -> Contains the statistics for each package by its index.
;			Trucks -> Holds the truck properties by reading from input file.
;			packages -> Holds the package properties by reading from input files.
;			Truck-count -> Number(Count) of trucks.
;			Package-count -> Number of packages which are not delivered.
;			time n -> Global Time
;****************************************************************************************************************


(truck-count 0)
(package-count 0)
(city-count 0)
)

;****************************************************************************************************************
;This rule reads city data from input file and store it into Factbase
;****************************************************************************************************************


(defrule READ-CITIES-INPUT
(initial-fact)
(city-count ?n&:(= ?n 0))
(CITIES-FILE-PATH ?path)
=>
(printout t crlf "TRYING TO READ CITY DATA FROM FILE PATH : " ?path crlf crlf)
(open ?path cities "r")
(bind ?i (read cities))
(bind ?j (read cities))
(bind ?k (read cities))
(while (neq ?i EOF) do
(assert (cities ?i ?j ?k))
(assert (cities ?j ?i ?k))
(assert (city-count (+ ?n 1)))
(printout t ?n crlf)
(assert (cities ?i 0))
(assert (min-dist ?i ?i 0))
(assert (cities ?j 0))
(assert (min-dist ?j ?j 0))
(bind ?i (read cities))
(bind ?j (read cities))
(bind ?k (read cities)))
(close))

;****************************************************************************************************************
;Rule to read package data from input file and store it in factbase
;****************************************************************************************************************



(defrule PACKAGES-READ-INPUT
(initial-fact)
?pcountfact<-(package-count ?z&:(eq ?z 0))
(PACKAGES-FILE-PATH ?path)
=>
(printout t crlf "TRYING TO READ PACKAGE DATA FROM FILE PATH : " ?path crlf crlf)
(open ?path packages "r")
(bind ?i (read packages))
(bind ?j (read packages))
(bind ?k (read packages))
(bind ?l (read packages))
(bind ?m (read packages))
(bind ?n (read packages))
(while (neq ?i EOF) do
(assert (packages ?i ?j ?k ?l ?m ?n))
(assert (package-stats ?i 0 0 0 0 0))
(retract ?pcountfact)
(assert(package-count ?i))
(bind ?i (read packages))
(bind ?j (read packages))
(bind ?k (read packages))
(bind ?l (read packages))
(bind ?m (read packages))
(bind ?n (read packages)))
(close))



;****************************************************************************************************************
;This rule READ TRUCK DATA FROM Input FILE AND STORE INTO FACTBase
;****************************************************************************************************************




(defrule INPUT-TRUCK-DATA
(declare (salience -1))
(initial-fact)
(truck-count ?z&:(eq ?z 0))
(TRUCKS-FILE-PATH ?path)
=>
(printout t crlf "TRYING TO READ TRUCK DATA FROM FILE PATH : " ?path crlf crlf)
(open ?path trucks "r")
(bind ?i (read trucks))
(bind ?j (read trucks))
(bind ?k (read trucks))
(bind ?l (read trucks))
(bind ?m (read trucks))
(bind ?n (read trucks))
(bind ?o (read trucks))
(while (neq ?i EOF) do
(assert (trucks ?i ?j ?k ?l ?m ?n ?o))
(assert (truck-stats ?i 0 0 0 0 0 0 0))
(assert(truck-count ?i))
(bind ?i (read trucks))
(bind ?j (read trucks))
(bind ?k (read trucks))
(bind ?l (read trucks))
(bind ?m (read trucks))
(bind ?n (read trucks))
(bind ?o (read trucks)))
(close)
(assert(time -1)))



;****************************************************************************************************************
;READING is done and below is the implementation of logic
;****************************************************************************************************************




;****************************************************************************************************************
;THIS RULE IS FIRED AFTER THE MINIMUM DISTANCE BETWEEN DIFFERENT CITIES
;****************************************************************************************************************





(defrule INITIALIZE-TIME-START-PROCESSING
?c3<-(time -1)
(package-count ?pcount)
=>
(undefrule CALCULATE-DISTANCES)   
(assert(cities Delhi Delhi 0))
(assert(pkt-avg 0 0 0 0))
(retract ?c3)
(assert(original-packet-count ?pcount))
(assert(time 0))                                ;inits time
)




;****************************************************************************************************************
;The following rule does the following
;SENDING THE TRUCKS TO THE DISPATCH LOCATION JUST AFTER THE PACKAGES ARRIVAL
;IT CHECKS FOR TRUCKS WHICH ARE IDLE AND PACKAGE ARRIVAL TIME IS MATCHED WITH CURRENT GLOBAL TIME. 
;CHECK IF TRUCK TIMES ARE IN SYNCRONIZATION WITH GLOBAL TIME
;****************************************************************************************************************

(defrule TRUCK-GO-TO-DISPATCH-LOCATION
(declare (salience 60))
(time ?n)
?p1<-(packages ?pnum ?dep ?del ?size ?n1 ?delivery)
?t1<-(trucks ?tnum Delhi none ?space_ava&:(>= ?space_ava ?size) ?n2&:(>= ?n2 ?n1) idle none)
(not(trucks ?tnum2 Delhi none ?space_ava2&:(>= ?space_ava2 ?size)&:(< ?space_ava2 ?space_ava) ?n idle none))
(not(trucks ?a ?b ?c ?d ?e&:(< ?e ?n) idle ?h))
(min-dist Delhi ?dep ?dist)
(cities Delhi $?route ?dep ?dist)
;Order 1 out for pickup at Delhi on truck 6 at time 1
=>
(assert(simulation ?n for ?pnum ?tnum dispatched ?dep (+ ?dist ?n)))
(retract ?t1)
(retract ?p1)
(assert(packages ?pnum ?dep ?del ?size ?n ?delivery taken-care-of ?tnum))
(if (= (length $?route) 0)
then(assert(trucks ?tnum ?dep ?dep (- ?space_ava ?size) (+ 1 ?n) dispatched none))
else(assert(trucks ?tnum (first$ $?route) ?dep (- ?space_ava ?size) (+ 1 ?n) dispatched none))
)
(printout t "Package " ?pnum " out for pickup at " ?dep " on Truck " ?tnum " at time " ?n crlf)
)





;****************************************************************************************************************
;THE BELOW RULE CHANGING STATUS FROM PICK UP TRUCKS TO DELIVERING TRUCKS.
;IT IS AFTER THE PICKUP OF PACKAGE BY THE TRUCK AT THE DISPATCH LOCATION.
;FIRES ONLY IF TRUCK TIMES ARE IN SYNC WITH GLOBAL TIME AND THE 
;PACKAGE DATA AND TRUCK ASSOCIATED WITH IT MATCHES
;****************************************************************************************************************






(defrule CHANGE-TRUCK-STATE-FROM-PICKUP-TO-DELIVERING
(declare (salience 60))
;time 7
(time ?n)
(simulation ?nn for ?pnum ?tnum dispatched ?dep ?n)
?p1<-(packages ?pnum ?dep ?del ?size ?o ?delivery taken-care-of ?tnum)
?t1<-(trucks ?tnum ?now ?dest ?space_ava ?m dispatched none)
(min-dist ?dep ?del ?dist)
(cities ?dep $?route ?del ?dist)
?t2<-(truck-stats ?tnum ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 ?b8)
?pstats<-(package-stats ?pnum ?ps1 ?ps2 ?ps3 ?ps4 ?ps5)
=>
(retract ?t1)
(if (= (length $?route) 0)
then(assert(trucks ?tnum ?dep ?del ?space_ava (+ ?n 1) delivering 1))
else(assert(trucks ?tnum (first$ $?route) ?del ?space_ava (+ 1 ?n) delivering 1)))
(assert(simulation ?n ?pnum ?tnum delivering ?del (+ ?dist ?n)))
(retract ?t2)
(assert(truck-stats ?tnum ?b2 (+ ?b3 (- ?n (- ?m 1))) ?b4 ?b5 (+ ?b6 (- ?n (- ?m 1))) ?b7 ?b8))
(retract ?pstats)
(assert(package-stats ?pnum (- ?n ?o) ?n ?ps3 ?ps4 ?ps5))
;Order 1 is being delivered to Jacksonville on truck 6 at time 1
(printout t "Package " ?pnum " is being delivered to " ?del " on Truck " ?tnum " at time " ?n crlf)
)



;****************************************************************************************************************
;THE FOLLOWING RULE DELIVERS THE PACKAGES AT ITS DESTINATION AT THE TIME CALCULATED BY THE
;MINIMUM DISTANCES BETWEEN THE CITIES. AFTER DELIVERY THE TRUCKS ARE DIRECTED BACK TO DELHI
;****************************************************************************************************************



(defrule SEND-TRUCKS-BACK-TO-DELHI
(declare (salience 60))
;time 7
(time ?n)
(simulation ?nn ?pnum ?tnum delivering ?del ?n)
?p1<-(packages ?pnum ?dep ?del ?size ?o ?delivery taken-care-of ?tnum)
?t1<-(trucks ?tnum ?now ?del ?space_ava ?m delivering 1)
(min-dist ?del Delhi ?dist)
(cities ?del $?route Delhi ?dist)
?t2<-(truck-stats ?tnum ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 ?b8)
?pstats<-(package-stats ?pnum ?ps1 ?ps2 ?ps3 ?ps4 ?ps5)
=>
(retract ?t1)
(if (= (length $?route) 0)
then(assert(trucks ?tnum ?dep Delhi (+ ?space_ava ?size) (+ ?n 1) returning 1))
else(assert(trucks ?tnum (first$ $?route) Delhi (+ ?space_ava ?size) (+ 1 ?n) returning 1)))
(assert(simulation ?n - ?tnum returning Delhi (+ ?dist ?n)))
(retract ?t2)
(assert(truck-stats ?tnum ?b2 (+ ?b3 (- ?n (- ?m 1))) ?b4 ?b5 ?b6 ?b7 (+ ?b8 (* ?size (- ?n (- ?m 1))))))
(retract ?pstats)
(if(> ?n ?delivery) then(assert(package-stats ?pnum ?ps1 ?ps2 ?n LATE (- ?n ?delivery))) else(assert(package-stats ?pnum ?ps1 ?ps2 ?n - 0)))
;(assert(package-stats ?pnum ?ps1 ?ps2 ?n (> ?n ?delivery) ?ps5))
(printout t "Package " ?pnum " has been delivered to " ?del " on Truck " ?tnum " at time "?n ". EXPECTED TIME WAS " ?delivery crlf)
)



;****************************************************************************************************************
;THIS RULE FIRES AFTER TRUCK HAS REACHED DELHI THE STATUS(TRUCK)  IS NOW CHANGED TO IDLE 
;****************************************************************************************************************



(defrule CHANGE-TRUCK-STATUS-TO-IDLE-AND-END-TRIP-AT-DELHI
(declare (salience 60))
;time 7
(time ?n)
(simulation ?nn - ?tnum returning Delhi ?n)
?p1<-(packages ?pnum ?dep ?del ?size ?o ?delivery taken-care-of ?tnum)
?t1<-(trucks ?tnum ?now Delhi ?space_ava ?m returning 1)
?t2<-(truck-stats ?tnum ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 ?b8)
?pfact<-(package-count ?pcount)
=>
(retract ?t1)
(assert(trucks ?tnum Delhi none ?space_ava ?n idle none))
(assert(simulation ?n - ?tnum returned-to Delhi ?n))
(retract ?t2)
(assert(truck-stats ?tnum ?b2 (+ ?b3 (- ?n (- ?m 1))) ?b4 (+ ?b5 1) (+ ?b6 (- ?n (- ?m 1))) ?b7 ?b8))
(retract ?p1)
(assert(packages ?pnum ?dep ?del ?size ?o ?delivery DONE))
;Truck 6 arrived back at Delhi at time 7
(printout t "Truck " ?tnum " arrived back at Delhi at time " ?n crlf) 
(retract ?pfact)
(assert(package-count (- ?pcount 1)))
)


;****************************************************************************************************************
;INCREMENTING TIME COUNTER BY 1
;****************************************************************************************************************

(defrule INCREASE-TIME-GLOBALLY-ONE-UNIT
(declare (salience 50))
?ti1<-(time ?n)
;1 Delhi none 10 0 idle none
;4 Delhi none 7 0 1 idle none
(not(trucks ?a ?b ?c ?d ?e&:(!= ?e ?n) idle ?h))
(not(packet-report-generated-for ?))
=>
(retract ?ti1)
(assert(time (+ ?n 1)))
)





;****************************************************************************************************************
; SYNCING TIMES OF IDLE TRUCKS  WITH GLOBAL TIME
;****************************************************************************************************************




(defrule IDLE-TRUCK-INCREASE-TIME
(declare (salience 50))
?ti1<-(time ?n)
?t1<-(trucks ?a ?b ?c ?d ?e&:(< ?e ?n) idle ?h)
?t2<- (truck-stats ?a ?wt ?a1 ?a2 ?a3 ?a4 ?a5 ?a6)
=>
(retract ?t1)
(assert(trucks ?a ?b ?c ?d (+ ?e 1) idle ?h))
(retract ?t2)
(assert(truck-stats ?a (+ 1 ?wt) ?a1 ?a2 ?a3 ?a4 ?a5 ?a6))
)


;*******************************************DISTANCE CALCULATIONS***********************************************
;CALCULATING ALL POSSIBLE ROUTES BETWEEN CITIES AND THE DISTANCES BETWEEN THEM.
;THEY ARE NOT NECESSARILY THE SHORTEST
;For EXAMPLE-
;If we have X->Y = 5
;and        E->F = 7
;then a new fact X-> Y-> E-> F = 12 is derived
;****************************************************************************************************************



(defrule CALCULATE-DISTANCES
(declare (salience 100))
(cities ?y $?x ?d1)
(cities $?x ?dx)
(cities $?x ?end&:(neq ?y ?end) ?d2)
=>
(printout t "COMPUTING MINIMUM DISTANCES between " ?y " and " ?end  crlf )
(assert(cities ?y $?x ?end (-(+ ?d1 ?d2) ?dx)))
)

;****************************************************************************************************************
;RULE GOES THROUGH ALL POSSIBLE DERIVED ROUTES AND FILTERS  MINIMUM DISTANCES REPRESENTED BY FACTS
;****************************************************************************************************************

(defrule FIND-CITIES-MIN-DISTANCES
(declare (salience 99))
(cities ?x $?i ?y ?d)
(not(cities ?x $?j ?y ?d2&:(< ?d2 ?d)))
=>
(assert(min-dist ?x ?y ?d))
)



;****************************************************************************************************************
;ELIMINATES DUPLICACY BETWEEN MINIMUM DISTANCES
;****************************************************************************************************************




(defrule REMOVING-DUPLICACY-MIN-DISTANCE
(declare (salience 98))

?f1<-(min-dist ?x ?y ?d)
?f2<-(min-dist ?x ?y ?d2)
(test(neq ?f1 ?f2))
=>
(retract ?f1 ?f2)
(assert(min-dist ?x ?y (min ?d ?d2))))




;**************************************WHEN TO HALT*************************************************************


;****************************************************************************************************************
; WHEN ALL TRUCKS ARE IN IDLE STATE AND ALL PACKAGE ARE DELIVERED AT THEIR LOCATION TIME IS STOPPED
;IT ALSO GENERATES THE HEADER FOR THE REPORT PRINTING
;****************************************************************************************************************


(defrule PRINT-REPORT-HEADER
(declare (salience 51))
(time ?n&:(> ?n 0))
(package-count 0)
?pstats1<-(package-stats ?pnum ?p1 ?p2 ?p3 ?p4 ?p5)
(not(trucks ?a ?b ?c ?d ?e&:(< ?e ?n) idle ?h))
(not(package-stats ?pnum2&:(< ?pnum2 ?pnum) ?p12 ?p22 ?p32 ?p42 ?p52))
(not (package-header 1))
=>
(printout t crlf crlf "PACKAGE REPORT:" crlf)
(format t "%n%6s      %6s     %6s     %6s      %6s      %6s      %n" PackageIndex WaitTime PickUpTime DeliveryTime IsLate? LateTime)
(assert(package-header 1))
)



;****************************************************************************************************************
;THIS RULE PRINTS REPORT FOR VARIOUS PACKAGES
;****************************************************************************************************************



(defrule PACKAGE-REPORT-PRINT
(declare (salience 51))
(time ?n&:(> ?n 0))
(package-count 0)
?pstats1<-(package-stats ?pnum ?p1 ?p2 ?p3 ?p4 ?p5)
(not(package-stats ?pnum2&:(< ?pnum2 ?pnum) ?p12 ?p22 ?p32 ?p42 ?p52))
(package-header 1)
?pavg<-(pkt-avg ?pwait ?ontime ?nolate ?avglateness)
=>
(retract ?pavg)
(if(eq ?p4 LATE) then(assert(pkt-avg (+ ?pwait ?p1) ?ontime (+ ?nolate 1) (+ ?avglateness ?p5)))
 else(assert(pkt-avg (+ ?pwait ?p1) (+ ?ontime 1) ?nolate ?avglateness)))

(retract ?pstats1)
(format t "%6d         %6d        %6d            %6d           %6s        %6d      %n" ?pnum ?p1 ?p2 ?p3 ?p4 ?p5)
;(printout t ?pnum " " ?p1 " " ?p2 " " ?p3 " " ?p4 " " ?p5 " " crlf)
(assert(packet-report-generated-for ?pnum)) 
)


;****************************************************************************************************************
;PRINTS THE TRUCK DELIVERY  HEADER FOR REPORT
;****************************************************************************************************************


(defrule TRUCK-DELIVERY-REPORT-PRINT
(declare (salience 51))
(time ?n&:(> ?n 0))
(package-count 0)
?tstats1<-(truck-stats ?tnum ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7)
(not(trucks ?a ?b ?c ?d ?e&:(< ?e ?n) idle ?h))
(not(truck-stats ?tnum2&:(< ?tnum2 ?tnum) ?p12 ?p22 ?p32 ?p42 ?p52 ?p62 ?p72))
(not (truck-header 1))
=>
(printout t crlf crlf "TRUCK REPORT:" crlf)
(format t "%n%12s      %12s     %12s     %12s      %12s      %12s      %12s     %12s %n" TruckIndex TotalWaitTime TotalBusyTime %TimeBusy #Pkgs Non.DeliveryTime %OfBusyTimeDelivering WeightedAvgOfTruckOccupied)
(assert(truck-header 1))
)

;****************************************************************************************************************
;THIS RULE PRINTS TRUCK DELIVERY REPORT
;****************************************************************************************************************


(defrule TRUCK-REPORT-PRINTING
(declare (salience 51))
(time ?n&:(> ?n 0))
(package-count 0)
?tstats1<-(truck-stats ?tnum ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7)
(not(truck-stats ?tnum2&:(< ?tnum2 ?tnum) ?p12 ?p22 ?p32 ?p42 ?p52 ?p62 ?p72))
;1 Delhi none 10 0 idle none
(trucks ?tnum ?truckcity ?truckdest ?truckcap ?trucktime idle ?truckp)
(truck-header 1)
=>
(retract ?tstats1)
(if(= ?p2 0) then(format t "%12d      %12d     %12d     %12.2f%%      %12d      %12d          %12.2f%%           %12.2f%%     %n" ?tnum ?p1 ?p2 (* (/ ?p2 ?n) 100) ?p4 ?p5 0 0) else(format t "%12d      %12d     %12d     %12.2f%%      %12d      %12d          %12.2f%%           %12.2f%%     %n" ?tnum ?p1 ?p2 (* (/ ?p2 ?n) 100) ?p4 ?p5 (* (/ (- ?p2 ?p5) ?p2) 100) (* 100 (/ (/ ?p7 (- ?p2 ?p5)) ?truckcap ))))
;(format t "%8d      %8d     %8d     %8.2f%%      %8d      %8d     %8.2f%%      %n" ?tnum ?p1 ?p2 (* (/ ?p2 ?n) 100) ?p4 ?p5 (* (/ (- ?p2 ?p5) ?p2) 100))
;(printout t ?tnum " " ?p1 " " ?p2 " " ?p3 " " ?p4 " " ?p5 " " crlf)
(assert(truck-report-generated-for ?tnum)) 
)


;****************************************************************************************************************
;THIS RULE PRINTS AVERAGE REPORT AND ENDS PROGRAM 
;****************************************************************************************************************




(defrule JUST-HALT-IT
(declare (salience 51))
(time ?n&:(> ?n 0))
(package-count 0)
(not(package-stats ?pnum ?p1 ?p2 ?p3 ?p4 ?p5))
(not(truck-stats ?tnum ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7))
(original-packet-count ?numc)
(pkt-avg ?pwait ?ontime ?nolate ?avglateness)
=> 
(printout t crlf crlf crlf "AVERAGE REPORT:" crlf crlf)
(printout t "Average Wait Time/Package = " (/ ?pwait ?numc)  crlf)
(printout t "#Packages on time = " ?ontime  crlf)
(printout t "#Late = " ?nolate  crlf)
(printout t "Avg Lateness FOR ALL PACKAGES = " (/ ?avglateness ?numc)  crlf)
(printout t "Avg Lateness FOR LATE PACKAGES = " (/ ?avglateness ?nolate)  crlf crlf crlf crlf)
(halt))

;*******************************************************END OF CODE*****************************************************





