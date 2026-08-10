def s_q(x, q):
    # sum of digits of x in base q
    s = 0
    while x > 0:
        s += x % q
        x //= q
    return s

def v_q(k, q):
    # valuation of a(2k+1) at prime q >= 3
    # ratio of factorials: (4k+2)! (9k+4)! / ( (8k+4)! (2k+1)! (3k+1)! )
    # 4^(6k+3) has no q factor since q >= 3.
    # So the valuation is:
    # (v(4k+2) + v(9k+4) - v(8k+4) - v(2k+1) - v(3k+1))
    # where v(n) = (n - s_q(n)) / (q - 1)
    # The linear terms: 4k+2 + 9k+4 - (8k+4 + 2k+1 + 3k+1) = 13k+6 - (13k+6) = 0.
    # So the valuation is exactly:
    # (- s_q(4k+2, q) - s_q(9k+4, q) + s_q(8k+4, q) + s_q(2k+1, q) + s_q(3k+1, q)) / (q - 1)
    val = - s_q(4*k+2, q) - s_q(9*k+4, q) + s_q(8*k+4, q) + s_q(2*k+1, q) + s_q(3*k+1, q)
    return val

# Let's search for any k and q >= 3 where v_q(k, q) < 0
found = False
for k in range(200):
    for q in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]:
        val = v_q(k, q)
        if val < 0:
            print(f"FAILED: k={k} (n={2*k+1}), q={q}, valuation numerator={val}")
            found = True
            break
    if found:
        break

if not found:
    print("All tested k and q have non-negative valuation numerator!")
