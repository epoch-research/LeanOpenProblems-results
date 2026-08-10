import numpy as np

c_coeffs = [1/1154560, -19/1731840, 37/865920, -1/15744, 1/31488]
d_coeffs = [9/9020, -1313/27060, 26501/54120, -71119/54120, 1]

print("Roots of P:")
for r in np.roots(c_coeffs[::-1]):
    print(r)

print("Roots of Q:")
for r in np.roots(d_coeffs[::-1]):
    print(r)
