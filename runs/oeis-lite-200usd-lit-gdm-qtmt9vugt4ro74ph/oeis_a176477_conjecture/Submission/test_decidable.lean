import FormalConjectures.Util.ProblemImports

lemma m_lt_pow_two (m : ℕ) : m < 2^m := by
  induction' m with m ih
  · omega
  · rw [pow_succ]
    omega

lemma pow2_eq_bounded (n : ℕ) :
  (∃ m : ℕ, m ≥ 1 ∧ n = 2^m) ↔ (∃ m < n, m ≥ 1 ∧ n = 2^m) := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    have h_lt := m_lt_pow_two m
    use m
    refine ⟨h_lt, hm, rfl⟩
  · rintro ⟨m, h_lt, hm, rfl⟩
    use m

def check_pow2 (n : ℕ) : Bool :=
  decide (∃ m < n, m ≥ 1 ∧ n = 2^m)

#eval check_pow2 8
#eval check_pow2 9
