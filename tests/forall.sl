(synth-fun t12f34 () Bool
	(
		(Start Bool (Formula))
		(Formula Bool
			(
				Atom
				(not Formula)
				(and Formula Formula)
				(or Formula Formula)
				(forall ((x0 U) (x1 U)) Formula)
				(forall ((x1 U)) Formula)
				(exists ((x0 U)) Formula)
				(exists ((x1 U)) Formula)
			)
		)
		(Atom Bool
			(
				true 						
				false 			
				(E Term Term) 	
				(= Term Term)
			)
		)
		(Term U
			(
				x0
				x1
				s
				t
			)
		)
	)
)