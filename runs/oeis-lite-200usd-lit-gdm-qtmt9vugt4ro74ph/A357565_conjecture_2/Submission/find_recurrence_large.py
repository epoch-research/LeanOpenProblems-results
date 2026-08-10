from sage.all import *

def a(n):
    sum2 = 0
    sum3 = 0
    for k in range(n + 1):
        b = binomial(n + k - 1, k)
        sum2 += b**2
        sum3 += b**3
    return 3 * sum2 + 2 * sum3

print("Generating 80 terms...")
terms = [a(n) for n in range(1, 81)]
print("Done.")

def find_recurrence(seq, max_order=6, max_deg=6):
    for order in range(1, max_order + 1):
        for deg in range(0, max_deg + 1):
            num_coeffs = (order + 1) * (deg + 1)
            if len(seq) < num_coeffs + order + 5:
                continue
            rows = []
            for n in range(len(seq) - order):
                row = []
                for i in range(order + 1):
                    for j in range(deg + 1):
                        row.append( (n+1)**j * seq[n+i] )
                rows.append(row)
            M = matrix(QQ, rows)
            K = M.right_kernel()
            if K.dimension() > 0:
                print(f"Found recurrence of order {order} and degree {deg}!")
                vec = K.basis()[0]
                terms_str = []
                idx = 0
                for i in range(order + 1):
                    poly_terms = []
                    for j in range(deg + 1):
                        coeff = vec[idx]
                        if coeff != 0:
                            poly_terms.append(f"{coeff}*n^{j}")
                        idx += 1
                    poly_str = " + ".join(poly_terms)
                    if poly_str:
                        terms_str.append(f"({poly_str}) * a(n+{i})")
                print(" + ".join(terms_str) + " = 0")
                return True
    print("No recurrence found.")
    return False

find_recurrence(terms, 8, 8)
