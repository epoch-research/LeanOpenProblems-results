import FormalConjectures.Util.ProblemImports

def pow_mod (base exp mod : ℕ) : ℕ :=
  Id.run do
    let mut res := 1
    let mut b := base % mod
    let mut e := exp
    while e > 0 do
      if e % 2 == 1 then
        res := (res * b) % mod
      b := (b * b) % mod
      e := e / 2
    return res

def sum_inv (n p3 : ℕ) : ℕ :=
  Id.run do
    let mut s : ℕ := 0
    -- phi(p^3) = p^2(p-1)
    let exp := 16843 * 16843 * 16842 - 1
    for i in [1:n+1] do
      s := (s + pow_mod i exp p3) % p3
    return s

#eval sum_inv 16842 (16843^3)
