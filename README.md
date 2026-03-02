The goal of these projects are to formalise various (well known) proofs of non existence of solutions 
(over integers or rationals)  of various binary polynomial equations f(x,y).
While the proofs in human language are classical, translating them to Lean4 code is challenging.
Currently some of the challenges come from how Lean understands polynomial rings and their quotients 
and proving within Lean that certain quotient rings defined by adjoining roots of some polynomials, are ID or UFD or ED etc.
