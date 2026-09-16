N = 2 * 100943 * 3^39101 - 1

F = IntegerModRing(N)
R.<x> = F[]
S.<a> = F.extension(x^2 - 3)

alpha = S(2 + a)

M2 = 100943 * 3^39101
M3 = 2 * 100943 * 3^39100
Mp = 2 * 3^39101

v2 = alpha^M2
v3 = alpha^M3
vp = alpha^Mp

inv2 = (v2 - 1)^-1
inv3 = (v3 - 1)^-1
invp = (vp - 1)^-1

def to_u_v(val):
    pol = val.polynomial()
    u = pol[0] if pol.degree() >= 0 else 0
    v = pol[1] if pol.degree() >= 1 else 0
    return u, v

i2u, i2v = to_u_v(inv2)
i3u, i3v = to_u_v(inv3)
ipu, ipv = to_u_v(invp)

with open("/workspace/leanproject/Submission/TestCertVals.lean", "w") as f:
    f.write("import FormalConjectures.Util.ProblemImports\n")
    f.write("namespace R\n")
    f.write("def my_N : ℕ := 2 * 100943 * 3^39101 - 1\n")
    f.write(f"def inv2_u : ℕ := {i2u}\n")
    f.write(f"def inv2_v : ℕ := {i2v}\n")
    f.write(f"def inv3_u : ℕ := {i3u}\n")
    f.write(f"def inv3_v : ℕ := {i3v}\n")
    f.write(f"def invp_u : ℕ := {ipu}\n")
    f.write(f"def invp_v : ℕ := {ipv}\n")
    f.write("end R\n")
