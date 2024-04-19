# Generated using the MPIR Compiler.

# Type Declaration of Balance :: σ | 0 <= σ (Statically Verified) 
Balance = type('Balance', (), {})

Numerical = type('Numerical', (float, ), {})

def createBalance(bal: Numerical) -> Balance:
	new_bal: Balance
	new_bal = 5.0
	return(new_bal)


