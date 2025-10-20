(synth-fun phi () Bool
    (
		(Start Bool)
		(Term U)
	)
	(
		(Start Bool
			(
				true 						
				false 			
				(E Term Term) 	
				(= Term Term)
				(fol.not Start)
				(fol.and Start Start)
				(fol.or Start Start)
				(fol.forall ((x0 U)) Start)
				(fol.forall ((x1 U)) Start)
				(fol.exists ((x0 U)) Start)
				(fol.exists ((x1 U)) Start)
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
