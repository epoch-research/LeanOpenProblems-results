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

def sum_inv (n p p2 : ℕ) : ℕ :=
  Id.run do
    let mut s : ℕ := 0
    let exp := p * (p - 1) - 1
    for i in [1:n+1] do
      if i % p != 0 then
        s := (s + pow_mod i exp p2) % p2
    return s

#eval sum_inv 283686647 16843 283686649
