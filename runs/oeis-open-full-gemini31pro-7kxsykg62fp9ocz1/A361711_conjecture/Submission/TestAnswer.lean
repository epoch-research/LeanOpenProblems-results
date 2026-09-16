import Submission.Spec

theorem A361711_conjecture_test (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) (k : ℕ) (hk : k > 0) :
    A361711 (p ^ k) ≡ A361711 (p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℕ)] :=
  answer(sorry)

#print A361711_conjecture_test
