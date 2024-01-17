**If Then Else**
**if** p **then** q1 **else** q2 = **ite** p q1 q2 = `(p => q1) ^ (!p => q2)`
x **iff** p = **ite** p (x = true)(f = false)

**Type**<br>
This includes refinement types

typeof x: Top -> {v = typeof(x)}

**OR Statement**<br>
(||) x:Top --> y:Top --> {ite (!x) (v=y) (v=x)}

**AND Statement**<br>
(&&) x:Top --> y:Top --> {ite (x) (v=y) (v=x)}

**EQUALITY**<br>
Add stuff to make sure the type set has common members<br>
(==)  x:Top → y:Top → {Bool(ν) ∧ (tag(x) == bool) ∧ (domain_intersection (typeof x) (typeof y) > 0) ∧ (ν iff (x = y && x ≠ NaN))}

**Domain Intersection**<br>
di : a:Type -> b:Type -> domain_intersection(A, B) = { count(v) | v in A and v in B }