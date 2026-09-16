def check_padic_S(p):
    import fractions
    s = fractions.Fraction(0)
    for k in range(1, p):
        s += fractions.Fraction((-1)**k, k)
    return (s.numerator % p) == 0

print("1093:", check_padic_S(1093))
