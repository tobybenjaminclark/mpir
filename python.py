# Generated using the MPIR Compiler.

Hundred = type('Hundred', (), {})

Thousand = type('Thousand', (), {})

def CreateEven(a: Thousand) -> Hundred:
	returned_value: Hundred
	returned_value = a / 11.0

print(CreateEven(500))