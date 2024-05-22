# Generated using the MPIR Compiler.

# Type Declaration of One :: σ | (1 == σ or 0 == σ) (Statically Verified) 
One = type('One', (), {})

Numerical = type('Numerical', (float, ), {})

def OneCons(num: Numerical) -> One:
	retval: One
	if((1 == num or 0 == num)) == True: retval = num
	elif((1 == num or 0 == num)) == False: retval = 1.0
	
	return(retval)


