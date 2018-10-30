Group No. - 8
Section B

README
======

----------------
Introduction
----------------
This is a package delivery simulation expert system programmed using CLIPS.
In this, a truck is required to drive through the shortest route to the pickup city to pick the package up, then drive the
shortest route to the destination city, deliver the package, and then drive through the shortest route back to Delhi to wait for the next shipping order.

---------------------------
Main Exec File: SOURCE.clp
City data:cities.txt
Truck data: trucks.txt
Package data: packages.txt
---------------------------

---------------------------
Executing Source
---------------------------
All data for cities, trucks and pakages are stored in files cities.txt, trucks.txt and packages.txt
These file should be in the same folder as the SOURCE.clp file.

Commands :- 
							CLIPS (Beta 3/26/08)
	CLIPS> (load "SOURCE.clp")
	CLIPS> (reset)
	CLIPS> (run)
			
=====END OF README=====
