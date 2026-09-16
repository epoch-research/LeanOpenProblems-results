import Submission.TestDefCheat

theorem check : type_of% A361711_conjecture = (∀ (p : ℕ) (hp : Nat.Prime p) (h_geq_5 : 5 ≤ p) (k : ℕ) (hk : k > 0), A361711 (p ^ k) ≡ A361711 (p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℕ)]) := rfl
