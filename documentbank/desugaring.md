**If Then Else**
**if** p **then** q1 **else** q2 = **ite** p q1 q2 = `(p => q1) ^ (!p => q2)`
x **iff** p = **ite** p (x = true)(f = false)

**OR Statement**<br>
(||) x:Top --> y:Top --> {ite (!x) (v=y) (v=x)}

**AND Statement**<br>
(&&) x:Top --> y:Top --> {ite (x) (v=y) (v=x)}

**EQUALITY**<br>
Add stuff to make sure the type set has common members<br>
(==) x:Top --> y:Top --> {tag(v) == bool ^ (tag x == tag y) => iff (x = y && x != NaN}