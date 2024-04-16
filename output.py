# Generated using the MPIR Compiler.

# Type Declaration of NumericalPos :: σ | 0 <= σ (Statically Verified) 
NumericalPos = type('NumericalPos', (), {})

# Type Declaration of Bool :: σ | (1 == σ or 0 == σ) (Statically Verified) 
Bool = type('Bool', (), {})

Numerical = type('Numerical', (float, ), {})

def IsPositive(num: NumericalPos) -> Bool:
	ret_val: Numerical
	if (num >= 0.0) ==  1.0: ret_valI = 1.0
	elif (num >= 0.0) ==  0.0: ret_valII = 0.0
	
	return(ret_valIII)


