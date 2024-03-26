
Integer = type('Integer', (), {})
TwoInt = type('TwoInt', (), {})
SmallInt = type('SmallInt', (), {})
Numerical = type('Numerical', (), {})


def two(x: Integer) -> TwoInt:
        return(2.0)



def int_to_smallint(x: Integer) -> SmallInt:
        y: SmallInt
        anon2: Numerical
        anon2 = int(0 < x and 100 > x)
        if ( anon2  == 1): y = x
        if ( anon2  == 0): y = 1.0
        return(y)



def multiply_show(x: SmallInt) -> Integer:
        z: SmallInt
        anon2: Numerical
        anon2 = 0 < x ^ 100 > x
        if ( anon2  ==1.0 ): z = 1.0
        if ( anon2  ==2.0 ): z = 2.0
        anon: Numerical
        anon = z > 2.0
        if ( anon  ==1.0 ): z = 3.0
        if ( anon  ==0.0 ): z = 4.0
        return(z)


