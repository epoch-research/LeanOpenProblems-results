import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

variable (A135508 : ℕ → ℕ) (x_seq : ℕ → ℕ)

example (q : ℕ) (hq : Nat.Prime q) (hq3 : q ≥ 3) (hq2_prime : ¬Nat.Prime (q - 2))
    (h_A : A135508 (q - 1) = q) (h_nz : ¬x_seq ((q - 2) * q) % q = 0)
    (h_not : ¬q ∣ x_seq ((q - 2) * q - 1)) (G : ℕ)
    (hG : (x_seq ((q - 2) * q - 1)).gcd ((q - 2) * q) = G) (h_G_dvd : G ∣ q - 2)
    (h_eq : q - 2 = G * ((q - 2) / G)) (h_ne : (q - 2) * q - 1 ≠ 0)
    (h_eq_A : A135508 ((q - 2) * q - 1) = (q - 2) / G * q) (hq_ge11 : q ≥ 11)
    (hd1 : (q - 2) / G = 1) : False := by
  aesop


