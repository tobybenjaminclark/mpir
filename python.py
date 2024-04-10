# Generated using the MPIR Compiler.

Hundred = type('Hundred', (), {})

Ten = type('Ten', (), {})

def CreateEven() -> Ten:
	new_bal: Ten
	new_bal = bal
	new_balI = new_bal * new_bal
	new_balII = new_balI / 2.0
	return(new_balII)


