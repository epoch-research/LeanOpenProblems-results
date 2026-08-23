import FormalConjectures.Util.ProblemImports

open Nat

lemma exists_prime_ge_le_of_L_le {L q : ℕ} (hq0 : 0 < q) (hL : 1 ≤ L)
    (hLq : L ≤ 2 * q + 1) :
    ∃ p, p.Prime ∧ L ≤ p ∧ p ≤ L + 2 * q := by
  by_cases hLp : L.Prime
  · exact ⟨L, hLp, le_rfl, Nat.le_add_right _ _⟩
  rcases eq_or_ne L 1 with rfl | hLne
  · refine ⟨2, Nat.prime_two, by omega, ?_⟩
    omega
  have hL2 : 2 ≤ L := by omega
  have hLpos : L ≠ 0 := by omega
  obtain ⟨p, hp, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul L hLpos
  refine ⟨p, hp, Nat.le_of_lt hpgt, ?_⟩
  have p_ne : p ≠ 2 * L := by
    intro h
    have hpr : (2 * L).Prime := h ▸ hp
    have : ¬ (2 * L).Prime :=
      Nat.not_prime_mul (by omega) (by omega)
    exact this hpr
  have hp_lt : p < 2 * L := lt_of_le_of_ne hple p_ne
  have hp_le' : p ≤ 2 * L - 1 := Nat.le_pred_of_lt hp_lt
  have : 2 * L - 1 ≤ L + 2 * q := by omega
  exact hp_le'.trans this

lemma sqrt_n_add_p_prime {n p q : ℕ} (hq : q.Prime)
    (hlo : q ^ 2 ≤ n + p) (hhi : n + p < (q + 1) ^ 2) :
    (Nat.sqrt (n + p)).Prime := by
  have : Nat.sqrt (n + p) = q :=
    ((Nat.eq_sqrt' (a := q) (n := n + p)).mpr ⟨hlo, hhi⟩).symm
  rwa [this]

/-- For `q ≥ 7`, `q² + 2q < 2(q² - 2q - 1)`. -/
lemma q_sq_add_two_q_lt {q : ℕ} (hq : 7 ≤ q) :
    q ^ 2 + 2 * q < 2 * (q ^ 2 - 2 * q - 1) := by
  have hnonneg : 2 * q + 1 ≤ q ^ 2 := by
    have : (2 * (q : ℤ) + 1) ≤ (q : ℤ) ^ 2 := by nlinarith
    exact_mod_cast this
  have heq : q ^ 2 - 2 * q - 1 = q ^ 2 - (2 * q + 1) := by omega
  rw [heq]
  have hcast : ((q ^ 2 - (2 * q + 1) : ℕ) : ℤ) = (q : ℤ) ^ 2 - (2 * q + 1) := by
    rw [Nat.cast_sub hnonneg]
    norm_cast
  zify
  rw [hcast]
  nlinarith

/-- If there is a prime `q ≥ 7` with `q^2 - 2*q - 1 ≤ n < q^2`, the conjecture holds. -/
lemma exists_of_nearby_prime_square {n q : ℕ} (hn : n > 2) (hq : q.Prime)
    (hq7 : 7 ≤ q) (h1 : q ^ 2 - 2 * q - 1 ≤ n) (h2 : n < q ^ 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  have hq0 : 0 < q := hq.pos
  set L := q ^ 2 - n with hLdef
  have hL_pos : 1 ≤ L := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact Nat.sub_ne_zero_of_lt h2
  have hLq : L ≤ 2 * q + 1 := by
    rw [hLdef]
    have : q ^ 2 ≤ n + (2 * q + 1) := by
      have hnonneg : 2 * q + 1 ≤ q ^ 2 := by
        have : (2 * (q : ℤ) + 1) ≤ (q : ℤ) ^ 2 := by nlinarith
        exact_mod_cast this
      have : q ^ 2 - (2 * q + 1) ≤ n := by
        have heq : q ^ 2 - 2 * q - 1 = q ^ 2 - (2 * q + 1) := by omega
        rwa [heq] at h1
      omega
    exact Nat.sub_le_iff_le_add.mpr (by simpa [Nat.add_comm] using this)
  obtain ⟨p, hp, hpL, hpU⟩ := exists_prime_ge_le_of_L_le hq0 hL_pos hLq
  have hlo : q ^ 2 ≤ n + p := by
    exact (Nat.sub_le_iff_le_add').mp hpL
  have hhi : n + p < (q + 1) ^ 2 := by
    have : n + p ≤ n + (L + 2 * q) := Nat.add_le_add_left hpU n
    have heq : n + (L + 2 * q) = q ^ 2 + 2 * q := by
      rw [hLdef]
      have : n ≤ q ^ 2 := Nat.le_of_lt h2
      omega
    have : n + p ≤ q ^ 2 + 2 * q := by
      rwa [heq] at this
    have : q ^ 2 + 2 * q < (q + 1) ^ 2 := by
      rw [add_sq]; omega
    omega
  have hpn : p < n := by
    have : p ≤ q ^ 2 - n + 2 * q := hpU
    have hbound : q ^ 2 - n + 2 * q < n := by
      have hlt := q_sq_add_two_q_lt hq7
      have hn' : q ^ 2 - 2 * q - 1 ≤ n := h1
      have hnonneg : 2 * q + 1 ≤ q ^ 2 := by
        have : (2 * (q : ℤ) + 1) ≤ (q : ℤ) ^ 2 := by nlinarith
        exact_mod_cast this
      omega
    omega
  exact ⟨p, hp, hpn, sqrt_n_add_p_prime hq hlo hhi⟩

/-- If `⌊√(n+2)⌋` is prime and `n > 2`, then `p = 2` works. -/
lemma exists_of_sqrt_n_add_two_prime {n : ℕ} (hn : n > 2)
    (hp : (Nat.sqrt (n + 2)).Prime) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime :=
  ⟨2, Nat.prime_two, hn, hp⟩
