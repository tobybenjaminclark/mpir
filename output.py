# Line 18.0Function Call to return, argument 0 - Found invalid possible value of 2

Typing Context 'Ψ' :
 · num                      :: σ | And(num > -2147483648, num < 2147483648)
 · return_val               :: σ | Or(1 == σ, 0 == σ)
 · return_val_test          :: σ | 1 == return_val_test
 · num_succ                 :: σ | Or(1 == σ, 0 == σ)
 · num_fail                 :: σ | And(num > -2147483648, num < 2147483648)
 · return_val_testI         :: σ | 2 == return_val_testI
 · return_val_test_combined :: σ | Or(1 == return_val_test_combined,
   2 == return_val_test_combined)
