# Generated using the MPIR Compiler.

Balance = type('Balance', (), {})

Accounts = type('Accounts', (), {})

def createBalance() -> Balance:
	new_bal: Balance
	new_bal = 0.0
	anon2: Numerical
	anon2 = 0 <= bal
	if (anon2  ==1.0):
		new_bal = bal
	if (anon2  ==0.0):
		bal = -1.0
	anon: Numerical
	anon = bal <= -1.0
	if (anon  ==1.0):
		bal = 1.0
	return(new_bal)


def addToBalance(