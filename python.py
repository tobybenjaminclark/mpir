# Generated using the MPIR Compiler.

Hundred = type('Hundred', (), {})

One = type('One', (), {})

Thousand = type('Thousand', (), {})

def CreateOne(one: Numerical) -> One:
	return(1.0)


def CreateEven(a: Thousand) -> Hundred:
	returned_value: Hundred
	returned_value = a / 11.0
	return(CreateOne(1.0) * 99.0)


