import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
A309132: a(n) is the denominator of F(n) = A027641(n-1)/n + A027642(n-1)/n^2.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let n_q : ℚ := n
    let B_nm1 : ℚ := bernoulli (n - 1)
    let F_n : ℚ := (B_nm1.num : ℚ) / n_q + (B_nm1.den : ℚ) / (n_q * n_q)
    F_n.den

lemma bernoulli_of_even (n : ℕ) (h_even : Even n) (h_gt2 : n > 2) : bernoulli (n - 1) = 0 := by
  have h_odd : Odd (n - 1) := by
    rcases h_even with ⟨k, rfl⟩
    use k - 1
    omega
  have h_gt1 : 1 < n - 1 := by
    omega
  exact bernoulli_eq_zero_of_odd h_odd h_gt1

lemma a_of_bernoulli_zero (n : ℕ) (hn : n ≠ 0) (hB : bernoulli (n - 1) = 0) :
    a n = n ^ 2 := by
  unfold a
  split_ifs with h
  · contradiction
  · dsimp
    set n_q : ℚ := (n : ℚ)
    set B_nm1 : ℚ := bernoulli (n - 1)
    set F_n : ℚ := (B_nm1.num : ℚ) / n_q + (B_nm1.den : ℚ) / (n_q * n_q)
    have hB_num : B_nm1.num = 0 := by
      rw [hB]
      rfl
    have hB_den : B_nm1.den = 1 := by
      rw [hB]
      rfl
    have h_F : F_n = (↑(n * n))⁻¹ := by
      dsimp [F_n, B_nm1]
      rw [hB_num, hB_den]
      simp [n_q]
    rw [h_F]
    have h_pos : 0 < n * n := Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hn)
    have h_den := Rat.inv_natCast_den_of_pos h_pos
    rw [sq]
    exact h_den

lemma not_squarefree_sq (n : ℕ) (hn : n > 1) : ¬ Squarefree (n ^ 2) := by
  intro h_sq
  rw [Squarefree] at h_sq
  have h_dvd : n * n ∣ n ^ 2 := by
    rw [sq]
  have h_unit := h_sq n h_dvd
  have : n = 1 := by
    exact Nat.isUnit_iff.mp h_unit
  omega

lemma a_dvd_n_sq (n : ℕ) (hn : n ≠ 0) : a n ∣ n ^ 2 := by
  unfold a
  split_ifs with h
  · simp [h]
  · dsimp
    set B_nm1 := bernoulli (n - 1)
    set n_q : ℚ := (n : ℚ)
    set F_n : ℚ := (B_nm1.num : ℚ) / n_q + (B_nm1.den : ℚ) / (n_q * n_q)
    have h_eq : F_n = ((B_nm1.num * n + B_nm1.den : ℤ) : ℚ) / (n_q * n_q) := by
      dsimp [F_n]
      have h1 : (B_nm1.num : ℚ) / n_q = ((B_nm1.num : ℚ) * n_q) / (n_q * n_q) := by
        have hn_q : n_q ≠ 0 := by positivity
        rw [mul_div_mul_right _ _ hn_q]
      rw [h1]
      rw [← add_div]
      push_cast
      rfl
    have h_div : F_n = (B_nm1.num * n + B_nm1.den : ℤ) /. (n * n : ℕ) := by
      rw [h_eq]
      rw [Rat.divInt_eq_div]
      push_cast
      rfl
    have h_den_dvd_int : (F_n.den : ℤ) ∣ (n * n : ℕ) := by
      rw [h_div]
      exact Rat.den_dvd (B_nm1.num * n + B_nm1.den : ℤ) (n * n : ℕ)
    have h_den_dvd : F_n.den ∣ n * n := by
      exact Int.natCast_dvd_natCast.mp h_den_dvd_int
    rw [sq]
    exact h_den_dvd


lemma prime_coe_int {p : ℕ} (hp : Nat.Prime p) : _root_.Prime (p : ℤ) := by
  rw [Int.prime_iff_natAbs_prime]
  have : (p : ℤ).natAbs = p := Int.natAbs_natCast p
  rwa [this]

lemma a_dvd_bernoulli_den (n : ℕ) (hn : n ≠ 0) (h_sq : Squarefree (a n)) :
    a n ∣ (bernoulli (n - 1)).den := by
  have h_dvd_n : a n ∣ n := by
    have h_dvd_sq := a_dvd_n_sq n hn
    exact (Squarefree.dvd_pow_iff_dvd h_sq (by decide)).mp h_dvd_sq
  rcases h_dvd_n with ⟨k, hk⟩
  set B_nm1 := bernoulli (n - 1)
  set F_n : ℚ := (B_nm1.num : ℚ) / n + (B_nm1.den : ℚ) / (n * n)
  have h_eq : F_n = ((B_nm1.num * n + B_nm1.den : ℤ) : ℚ) / (n * n : ℚ) := by
    dsimp [F_n]
    have h1 : (B_nm1.num : ℚ) / n = ((B_nm1.num : ℚ) * n) / (n * n : ℚ) := by
      have hn_q : (n : ℚ) ≠ 0 := by positivity
      rw [mul_div_mul_right _ _ hn_q]
    rw [h1]
    rw [← add_div]
    push_cast
    rfl
  have h_div : F_n = Rat.divInt (B_nm1.num * n + B_nm1.den : ℤ) (n * n : ℕ) := by
    rw [h_eq]
    rw [Rat.divInt_eq_div]
    push_cast
    rfl
  have h_nz : (n * n : ℤ) ≠ 0 := by positivity
  rcases Rat.num_den_mk h_nz h_div with ⟨c, h_num, h_den⟩
  have h_F_den : F_n.den = a n := by
    unfold a
    split_ifs with h_cond
    · contradiction
    · rfl
  have h_rel_cast : (B_nm1.num * n + B_nm1.den : ℤ) * (a n : ℤ) =
      ((n : ℤ) * (n : ℤ)) * F_n.num := by
    have h_rel' : (B_nm1.num * n + B_nm1.den : ℤ) * F_n.den = (n * n : ℤ) * F_n.num := by
      calc
        _ = (c * F_n.num : ℤ) * F_n.den := by rw [h_num]
        _ = (c * F_n.den : ℤ) * F_n.num := by ring
        _ = _ := by rw [← h_den]
    rw [h_F_den] at h_rel'
    exact_mod_cast h_rel'
  have h_an_pos : (a n : ℤ) ≠ 0 := by
    have : a n ≠ 0 := by
      unfold a
      split_ifs with h_cond
      · contradiction
      · exact Rat.den_nz _
    exact_mod_cast this
  have hk_int : (n : ℤ) = (a n : ℤ) * (k : ℤ) := by exact_mod_cast hk
  set A : ℤ := (a n : ℤ)
  change (n : ℤ) = A * (k : ℤ) at hk_int
  have h_an_pos' : A ≠ 0 := h_an_pos
  have h_eq_mul : A * B_nm1.den = A * (A * (k * k * F_n.num - B_nm1.num * k)) := by
    calc
      _ = (B_nm1.num * n + B_nm1.den : ℤ) * A - B_nm1.num * A * k * A := by
        rw [hk_int]
        ring
      _ = ((n : ℤ) * (n : ℤ)) * F_n.num - B_nm1.num * A * k * A := by rw [h_rel_cast]
      _ = _ := by
        rw [hk_int]
        ring
  have h_eq : (B_nm1.den : ℤ) = A * (k * k * F_n.num - B_nm1.num * k) := by
    exact mul_left_cancel₀ h_an_pos' h_eq_mul
  have h_dvd_int : A ∣ (B_nm1.den : ℤ) := by
    rw [h_eq]
    exact dvd_mul_right A (k * k * F_n.num - B_nm1.num * k)
  change (a n : ℤ) ∣ (B_nm1.den : ℤ) at h_dvd_int
  exact Int.natCast_dvd_natCast.mp h_dvd_int

lemma p_sq_dvd_a_of_not_dvd_bernoulli_den (n : ℕ) (hn : n ≠ 0) {p : ℕ} (hp : Nat.Prime p)
    (hp_n : p ∣ n) (hp_den : ¬ p ∣ (bernoulli (n - 1)).den) : p ^ 2 ∣ a n := by
  set B_nm1 := bernoulli (n - 1)
  set F_n : ℚ := (B_nm1.num : ℚ) / n + (B_nm1.den : ℚ) / (n * n)
  have h_eq : F_n = ((B_nm1.num * n + B_nm1.den : ℤ) : ℚ) / (n * n : ℚ) := by
    dsimp [F_n]
    have h1 : (B_nm1.num : ℚ) / n = ((B_nm1.num : ℚ) * n) / (n * n : ℚ) := by
      have hn_q : (n : ℚ) ≠ 0 := by positivity
      rw [mul_div_mul_right _ _ hn_q]
    rw [h1]
    rw [← add_div]
    push_cast
    rfl
  have h_div : F_n = Rat.divInt (B_nm1.num * n + B_nm1.den : ℤ) (n * n : ℕ) := by
    rw [h_eq]
    rw [Rat.divInt_eq_div]
    push_cast
    rfl
  have h_nz : (n * n : ℤ) ≠ 0 := by positivity
  rcases Rat.num_den_mk h_nz h_div with ⟨c, h_num, h_den⟩
  have h_F_den : F_n.den = a n := by
    unfold a
    split_ifs with h_cond
    · contradiction
    · rfl
  have h_rel_cast : (B_nm1.num * n + B_nm1.den : ℤ) * (a n : ℤ) =
      ((n : ℤ) * (n : ℤ)) * F_n.num := by
    have h_rel' : (B_nm1.num * n + B_nm1.den : ℤ) * F_n.den = (n * n : ℤ) * F_n.num := by
      calc
        _ = (c * F_n.num : ℤ) * F_n.den := by rw [h_num]
        _ = (c * F_n.den : ℤ) * F_n.num := by ring
        _ = _ := by rw [← h_den]
    rw [h_F_den] at h_rel'
    exact_mod_cast h_rel'
  have h_p2_dvd_nn : (p^2 : ℤ) ∣ (n * n : ℤ) := by
    have : (p^2 : ℕ) ∣ (n * n : ℕ) := by
      have h1 : p * p ∣ n * n := mul_dvd_mul hp_n hp_n
      rwa [← sq] at h1
    exact_mod_cast this
  have h_p2_dvd_rhs : (p^2 : ℤ) ∣ ((n : ℤ) * (n : ℤ)) * F_n.num := by
    have : ((n : ℤ) * (n : ℤ)) = (n * n : ℕ) := by push_cast; rfl
    rw [this]
    exact dvd_mul_of_dvd_left h_p2_dvd_nn F_n.num
  have h_p2_dvd_lhs : (p^2 : ℤ) ∣ (B_nm1.num * n + B_nm1.den : ℤ) * (a n : ℤ) := by
    rw [h_rel_cast]
    exact h_p2_dvd_rhs
  have h_p_dvd_num_n : (p : ℤ) ∣ B_nm1.num * n := by
    have : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hp_n
    exact dvd_mul_of_dvd_right this B_nm1.num
  have h_not_p_dvd_lhs : ¬ (p : ℤ) ∣ (B_nm1.num * n + B_nm1.den : ℤ) := by
    intro h
    have : (p : ℤ) ∣ (B_nm1.den : ℤ) := by
      have : (B_nm1.den : ℤ) = (B_nm1.num * n + B_nm1.den : ℤ) - B_nm1.num * n := by ring
      rw [this]
      exact dvd_sub h h_p_dvd_num_n
    have : p ∣ B_nm1.den := by exact_mod_cast this
    contradiction
  have h_p_dvd_lhs : (p : ℤ) ∣ (B_nm1.num * n + B_nm1.den : ℤ) * (a n : ℤ) := by
    have : (p : ℤ) ∣ (p^2 : ℤ) := by
      use (p : ℤ)
      ring
    exact dvd_trans this h_p2_dvd_lhs
  have h_p_dvd_an : (p : ℤ) ∣ (a n : ℤ) := by
    rcases (prime_coe_int hp).dvd_mul.mp h_p_dvd_lhs with h_div_X | h_div_an
    · contradiction
    · exact h_div_an
  rcases h_p_dvd_an with ⟨K, h_K⟩
  have h_sub : (p : ℤ) * (p : ℤ) ∣ (p : ℤ) * ((B_nm1.num * n + B_nm1.den : ℤ) * K) := by
    have h_ring : (B_nm1.num * n + B_nm1.den : ℤ) * (a n : ℤ) = (p : ℤ) * ((B_nm1.num * n + B_nm1.den : ℤ) * K) := by
      rw [h_K]
      ring
    have h_p2_ring : (p^2 : ℤ) = (p : ℤ) * (p : ℤ) := by ring
    rw [h_p2_ring] at h_p2_dvd_lhs
    rw [h_ring] at h_p2_dvd_lhs
    exact h_p2_dvd_lhs
  have h_p_nz : (p : ℤ) ≠ 0 := by
    have : p ≠ 0 := by
      have : p > 1 := hp.one_lt
      omega
    exact_mod_cast this
  have h_div_p := Int.dvd_of_mul_dvd_mul_left h_p_nz h_sub
  have h_p_dvd_K : (p : ℤ) ∣ K := by
    rcases (prime_coe_int hp).dvd_mul.mp h_div_p with h_div_X | h_div_K
    · contradiction
    · exact h_div_K
  rcases h_p_dvd_K with ⟨L, rfl⟩
  have h_p2_dvd : (p^2 : ℤ) ∣ (a n : ℤ) := by
    use L
    rw [h_K]
    ring
  exact Int.natCast_dvd_natCast.mp h_p2_dvd

lemma prime_dvd_bernoulli_den_of_squarefree {n : ℕ} (hn : n ≠ 0) (h_sq : Squarefree (a n))
    {p : ℕ} (hp : Nat.Prime p) (hp_n : p ∣ n) : p ∣ (bernoulli (n - 1)).den := by
  by_contra hp_den
  have h_p2 : p * p ∣ a n := by
    have h1 : p ^ 2 ∣ a n := p_sq_dvd_a_of_not_dvd_bernoulli_den n hn hp hp_n hp_den
    rwa [sq] at h1
  have h_unit := h_sq p h_p2
  have : p = 1 := Nat.isUnit_iff.mp h_unit
  have : p > 1 := hp.one_lt
  omega

lemma prime_sq_dvd_of_not_squarefree {n : ℕ} (h : ¬ Squarefree n) (hn : n > 1) :
    ∃ p : ℕ, Nat.Prime p ∧ p^2 ∣ n := by
  rw [squarefree_iff_prime_squarefree] at h
  push_neg at h
  rcases h with ⟨p, hp, hp_dvd⟩
  rw [Nat.prime_iff] at hp
  rw [sq]
  exact ⟨p, hp, hp_dvd⟩

lemma gcd_one_plus_div_self {n p : ℕ} (hp : Nat.Prime p) (hp2_n : p^2 ∣ n) :
    Nat.gcd (1 + n / p) n = 1 := by
  by_contra h_gcd
  have h_gt1 : Nat.gcd (1 + n / p) n > 1 := by
    have : Nat.gcd (1 + n / p) n ≠ 1 := h_gcd
    omega
  obtain ⟨q, hq, hq_dvd⟩ := Nat.exists_prime_and_dvd (by omega)
  have hq_n : q ∣ n := dvd_trans hq_dvd (Nat.gcd_dvd_right (1 + n / p) n)
  have hq_b : q ∣ 1 + n / p := dvd_trans hq_dvd (Nat.gcd_dvd_left (1 + n / p) n)
  have hq_div : q ∣ n / p := by
    by_cases hqp : q = p
    · subst hqp
      rcases hp2_n with ⟨m, rfl⟩
      have hp_pos : p > 0 := hp.pos
      have h_div_eq : p^2 * m / p = p * m := by
        rw [sq]
        rw [Nat.mul_assoc]
        exact Nat.mul_div_cancel_left (p * m) hp_pos
      rw [h_div_eq]
      exact dvd_mul_right p m
    · have hp_pos : p > 0 := hp.pos
      have hd_eq : n = p * (n / p) := by
        have : p ∣ n := by
          have : p ∣ p^2 := dvd_sq p
          exact dvd_trans this hp2_n
        exact (Nat.mul_div_cancel' this).symm
      have hp_prime : Prime (p : ℕ) := hp
      have hq_prime : Prime (q : ℕ) := hq
      have hq_dvd_mul : q ∣ p * (n / p) := by rwa [← hd_eq]
      rcases hq_prime.dvd_mul.mp hq_dvd_mul with hqp | hq_div'
      · have : q = p := (Nat.Prime.dvd_iff_eq hp hq.one_lt).mp hqp
        contradiction
      · exact hq_div'
  have hq_one : q ∣ 1 := by
    have : q ∣ 1 + n / p - n / p := Nat.dvd_sub' hq_b hq_div
    rwa [Nat.add_sub_cancel] at this
  have : q > 1 := hq.one_lt
  have : q ∣ 1 := hq_one
  have : q ≤ 1 := Nat.le_of_dvd (by decide) hq_one
  omega

lemma one_plus_mul_pow_mod_sq (p X k : ℕ) :
    (1 + X * p) ^ k ≡ 1 + k * X * p [MOD X * p^2] := by
  induction k with
  | zero =>
    simp [Nat.ModEq]
  | succ k ih =>
    have h_mul : (1 + X * p) ^ (k + 1) = (1 + X * p) ^ k * (1 + X * p) := by ring
    rw [h_mul]
    have ih' := Nat.ModEq.mul ih (Nat.ModEq.refl (1 + X * p))
    have h_ring : (1 + k * X * p) * (1 + X * p) = 1 + (k + 1) * X * p + k * X * (X * p^2) := by ring
    rw [h_ring] at ih'
    have h_mod : 1 + (k + 1) * X * p + k * X * (X * p^2) ≡ 1 + (k + 1) * X * p [MOD X * p^2] := by
      dsimp [Nat.ModEq]
      rw [Nat.add_assoc]
      rw [Nat.add_mul_mod_self_left]
    exact Nat.ModEq.trans ih' h_mod

lemma carmichael_squarefree (n : ℕ) (hc : is_carmichael_number n) : Squarefree n := by
  by_contra h_not_sf
  have hn : n > 1 := hc.1.2
  rcases prime_sq_dvd_of_not_squarefree h_not_sf hn with ⟨p, hp, hp2_n⟩
  have h_gcd : Nat.gcd (1 + n / p) n = 1 := gcd_one_plus_div_self hp hp2_n
  have hc_prop := hc.2 (1 + n / p) h_gcd
  rcases hp2_n with ⟨m, rfl⟩
  have hp_pos : p > 0 := hp.pos
  have h_div_eq : p^2 * m / p = m * p := by
    rw [sq]
    rw [Nat.mul_assoc]
    rw [Nat.mul_div_cancel_left (p * m) hp_pos]
    ring
  have h_n_eq : p^2 * m = m * p^2 := by ring
  rw [h_div_eq] at hc_prop
  rw [h_n_eq] at hc_prop
  have h_mod_thm := one_plus_mul_pow_mod_sq p m (p^2 * m - 1)
  have h_trans := Nat.ModEq.trans (Nat.ModEq.symm h_mod_thm) hc_prop
  have h_dvd : m * p^2 ∣ 1 + (p^2 * m - 1) * m * p - 1 := by
    exact Nat.ModEq.dvd h_trans
  have h_sub_eq : 1 + (p^2 * m - 1) * m * p - 1 = (p^2 * m - 1) * m * p := by omega
  rw [h_sub_eq] at h_dvd
  have h_ring_dvd : m * p^2 = (m * p) * p := by ring
  rw [h_ring_dvd] at h_dvd
  have h_ring_rhs : (p^2 * m - 1) * m * p = p * ((p^2 * m - 1) * m) := by ring
  rw [h_ring_rhs] at h_dvd
  have h_mp_pos : m * p > 0 := by
    have : m ≠ 0 := by
      rintro rfl
      omega
    have : m > 0 := by omega
    exact Nat.mul_pos this hp_pos
  have h_p_pos : p > 0 := hp_pos
  rw [Nat.mul_comm (m * p) p] at h_dvd
  have h_dvd' := Nat.dvd_of_mul_dvd_mul_left h_p_pos h_dvd
  have h_m_pos : m > 0 := by
    have : m ≠ 0 := by
      rintro rfl
      omega
    omega
  rw [Nat.mul_comm (p^2 * m - 1) m] at h_dvd'
  have h_p_dvd_lhs' := Nat.dvd_of_mul_dvd_mul_left h_m_pos h_dvd'
  have h_p_dvd_pm : p ∣ p^2 * m := by
    use p * m
    ring
  have h_dvd_one : p ∣ p^2 * m - (p^2 * m - 1) := Nat.dvd_sub' h_p_dvd_pm h_p_dvd_lhs'
  have : p^2 * m - (p^2 * m - 1) = 1 := by omega
  rw [this] at h_dvd_one
  have : p > 1 := hp.one_lt
  have : p ≤ 1 := Nat.le_of_dvd (by decide) h_dvd_one
  omega

lemma squarefree_of_dvd {a n : ℕ} (h_sq : Squarefree n) (h_dvd : a ∣ n) : Squarefree a := by
  exact Squarefree.dvd h_sq h_dvd

lemma a_dvd_n_of_n_dvd_bernoulli_den (n : ℕ) (hn : n ≠ 0) (h_dvd : n ∣ (bernoulli (n - 1)).den) :
    a n ∣ n := by
  rcases h_dvd with ⟨d, hd⟩
  unfold a
  split_ifs with h_cond
  · contradiction
  · dsimp
    set B_nm1 := bernoulli (n - 1)
    set n_q : ℚ := (n : ℚ)
    set F_n : ℚ := (B_nm1.num : ℚ) / n_q + (B_nm1.den : ℚ) / (n_q * n_q)
    have h_eq : F_n = ((B_nm1.num + (d : ℤ) : ℤ) : ℚ) / n_q := by
      have hn_q : n_q ≠ 0 := by positivity
      have hd_cast : (B_nm1.den : ℚ) = (n : ℚ) * (d : ℚ) := by
        exact_mod_cast hd
      calc
        F_n = (B_nm1.num : ℚ) / n_q + ((n : ℚ) * (d : ℚ)) / (n_q * n_q) := by rw [hd_cast]
        _ = (B_nm1.num : ℚ) / n_q + (d : ℚ) / n_q := by
          have : ((n : ℚ) * (d : ℚ)) / (n_q * n_q) = (d : ℚ) / n_q := by
            dsimp [n_q]
            rw [mul_comm (n : ℚ) (d : ℚ)]
            rw [sq]
            rw [mul_div_mul_right _ _ hn_q]
          rw [this]
        _ = ((B_nm1.num : ℚ) + (d : ℚ)) / n_q := by rw [← add_div]
        _ = ((B_nm1.num + (d : ℤ) : ℤ) : ℚ) / n_q := by push_cast; rfl
    have h_div : F_n = (B_nm1.num + d : ℤ) /. n := by
      rw [h_eq]
      rw [Rat.divInt_eq_div]
      push_cast
      rfl
    have h_den_dvd_int : (F_n.den : ℤ) ∣ (n : ℤ) := by
      rw [h_div]
      exact Rat.den_dvd (B_nm1.num + d : ℤ) n
    exact Int.natCast_dvd_natCast.mp h_den_dvd_int





/-- Helper definition for "composite number" -/
def is_composite (n : ℕ) : Prop := ¬ Nat.Prime n ∧ n > 1

/-- Definition of a Carmichael number $n$: a composite number s.t. $b^{n-1} \equiv 1 \pmod n$ for all $b$ coprime to $n$. -/
def is_carmichael_number (n : ℕ) : Prop :=
  (¬ Nat.Prime n ∧ n > 1) ∧ (∀ b : ℕ, Nat.gcd b n = 1 → b ^ (n - 1) ≡ 1 [MOD n])

lemma mod_sq_one (n : ℕ) (hn : n > 2) : (n - 1) ^ 2 ≡ 1 [MOD n] := by
  rcases n with _ | _ | _ | m
  · contradiction
  · contradiction
  · contradiction
  · dsimp [Nat.ModEq]
    have h1 : (m + 2) ^ 2 = (m + 3) * (m + 1) + 1 := by ring
    rw [h1]
    have h2 : (m + 3) * (m + 1) + 1 = 1 + (m + 3) * (m + 1) := by omega
    rw [h2]
    rw [Nat.add_mul_mod_self_left]

lemma even_not_carmichael (n : ℕ) (h_even : Even n) : ¬ is_carmichael_number n := by
  intro h_carm
  have h_comp := h_carm.1
  have h_gt2 : n > 2 := by
    have h_gt1 := h_comp.2
    have h_ne2 : n ≠ 2 := by
      intro h_eq
      subst h_eq
      exact h_comp.1 Nat.prime_two
    omega
  have h_odd : Odd (n - 1) := by
    rcases h_even with ⟨k, rfl⟩
    use k - 1
    omega
  rcases h_odd with ⟨k, hk⟩
  have h_gcd : Nat.gcd (n - 1) n = 1 := by
    rw [Nat.gcd_comm]
    have : 1 ≤ n := by omega
    have hg := Nat.gcd_self_sub_right this
    rw [hg]
    exact Nat.gcd_one_right n
  have h_carm_prop := h_carm.2 (n - 1) h_gcd
  have h_pow : (n - 1) ^ (n - 1) ≡ n - 1 [MOD n] := by
    nth_rw 2 [hk]
    have h_step : (n - 1) ^ (2 * k + 1) = ((n - 1) ^ 2) ^ k * (n - 1) := by
      ring
    rw [h_step]
    have h_base := mod_sq_one n h_gt2
    have h_pow_base := Nat.ModEq.pow k h_base
    have h_mul := Nat.ModEq.mul h_pow_base (Nat.ModEq.refl (n - 1))
    rw [one_pow] at h_mul
    simp only [one_mul] at h_mul
    exact h_mul
  have h_trans := Nat.ModEq.trans (Nat.ModEq.symm h_pow) h_carm_prop
  -- h_trans : n - 1 ≡ 1 [MOD n]
  -- which is (n - 1) % n = 1 % n
  change (n - 1) % n = 1 % n at h_trans
  have h_mod1 : (n - 1) % n = n - 1 := Nat.mod_eq_of_lt (by omega)
  have h_mod2 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h_mod1, h_mod2] at h_trans
  omega

lemma prime_case (n : ℕ) (hp : Nat.Prime n) :
    (is_composite n ∧ Squarefree (a n)) ↔ is_carmichael_number n := by
  constructor
  · rintro ⟨h_comp, h_sq⟩
    unfold is_composite at h_comp
    have : ¬ Nat.Prime n := h_comp.1
    contradiction
  · intro h_carm
    unfold is_carmichael_number at h_carm
    have : ¬ Nat.Prime n := h_carm.1.1
    contradiction

lemma le_one_case (n : ℕ) (hn : n ≤ 1) :
    (is_composite n ∧ Squarefree (a n)) ↔ is_carmichael_number n := by
  constructor
  · rintro ⟨h_comp, h_sq⟩
    unfold is_composite at h_comp
    have : n > 1 := h_comp.2
    omega
  · intro h_carm
    unfold is_carmichael_number at h_carm
    have : n > 1 := h_carm.1.2
    omega


lemma carmichael_dvd_of_carmichael {n : ℕ} (hn : n > 1)
    (hc : ∀ b : ℕ, Nat.gcd b n = 1 → b ^ (n - 1) ≡ 1 [MOD n]) :
    ArithmeticFunction.Carmichael n ∣ n - 1 := by
  haveI : NeZero n := ⟨by omega⟩
  rw [ArithmeticFunction.carmichael_eq_exponent' n]
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro g
  ext
  push_cast
  set b := (g : ZMod n).val
  have h_gcd : b.Coprime n := ZMod.val_coe_unit_coprime g
  have h_modeq := hc b h_gcd
  have h_cast : ((b ^ (n - 1) : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact h_modeq
  have hb : (b : ZMod n) = (g : ZMod n) := by simp [b]
  rw [← hb]
  push_cast at h_cast
  exact h_cast

lemma carmichael_iff_carmichael_dvd {n : ℕ} (hn : n > 1) (h_comp : ¬ Nat.Prime n) :
    is_carmichael_number n ↔ ArithmeticFunction.Carmichael n ∣ n - 1 := by
  constructor
  · rintro ⟨_, hc⟩
    exact carmichael_dvd_of_carmichael hn hc
  · intro h_dvd
    refine ⟨⟨h_comp, hn⟩, ?_⟩
    intro b hb
    haveI : NeZero n := ⟨by omega⟩
    rcases h_dvd with ⟨k, hk⟩
    have h_unit : IsUnit (b : ZMod n) := by
      rwa [ZMod.isUnit_iff_coprime]
    let g := h_unit.unit
    have hg_pow : g ^ ArithmeticFunction.Carmichael n = 1 := ArithmeticFunction.pow_carmichael g
    have hg_pow_k : g ^ (n - 1) = 1 := by
      rw [hk, pow_mul, hg_pow, one_pow]
    have h_val : (g : ZMod n) ^ (n - 1) = 1 := by
      have h_val' := congr_arg (Units.val) hg_pow_k
      push_cast at h_val'
      exact h_val'
    have h_eq : (g : ZMod n) = b := by
      simp [g]
    rw [h_eq] at h_val
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact h_val

lemma not_squarefree_zero_nat : ¬ Squarefree (0 : ℕ) := by
  intro h
  have h_dvd : 0 * 0 ∣ 0 := by simp
  have h_unit := h 0 h_dvd
  have : 0 = 1 := Nat.isUnit_iff.mp h_unit
  omega

lemma dvd_of_squarefree_dvd {n d : ℕ} (hn : Squarefree n)
    (h_dvd : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ d) : n ∣ d := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h0 : n = 0
  · subst h0
    have := not_squarefree_zero_nat
    contradiction
  by_cases h1 : n = 1
  · subst h1
    exact one_dvd d
  have hn1 : n > 1 := by
    have : n ≠ 0 := h0
    have : n ≠ 1 := h1
    omega
  obtain ⟨p, hp, hp_n⟩ := Nat.exists_prime_and_dvd (by omega)
  rcases hp_n with ⟨m, rfl⟩
  have h_pm : p.Prime := hp
  have h_sf : Squarefree (p * m) := hn
  have h_p_not_dvd_m : ¬ p ∣ m := by
    intro h_div
    have h_p2 : p * p ∣ p * m := mul_dvd_mul_left p h_div
    have h_unit := h_sf p h_p2
    have : p = 1 := Nat.isUnit_iff.mp h_unit
    have : p > 1 := h_pm.one_lt
    omega
  have h_sf_m : Squarefree m := by
    exact Squarefree.of_mul_right h_sf
  have h_rec_dvd : ∀ q : ℕ, Nat.Prime q → q ∣ m → q ∣ d := by
    intro q hq hq_m
    have hq_n : q ∣ p * m := dvd_mul_of_dvd_right hq_m p
    exact h_dvd q hq hq_n
  have h_m_lt : m < p * m := by
    have : p > 1 := h_pm.one_lt
    have : m > 0 := by
      by_contra h_zero
      have : m = 0 := by omega
      subst this
      rw [mul_zero] at hn
      have := not_squarefree_zero_nat
      contradiction
    exact lt_mul_of_one_lt_left this hp.one_lt
  have h_m_dvd : m ∣ d := ih m h_m_lt h_sf_m h_rec_dvd
  have h_p_dvd : p ∣ d := h_dvd p h_pm (dvd_mul_right p m)
  have h_coprime : Nat.Coprime p m := by
    rwa [Nat.Prime.coprime_iff_not_dvd h_pm]
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h_coprime h_p_dvd h_m_dvd

lemma carmichael_prime_odd {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ArithmeticFunction.Carmichael p = p - 1 := by
  have h1 : p = p^1 := by ring
  nth_rw 1 [h1]
  rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two 1 hp hp2]
  rw [pow_one]
  exact Nat.totient_prime hp

lemma carmichael_dvd_of_factors_dvd {n : ℕ} (hn : n > 1) (h_sf : Squarefree n) (h_odd : Odd n)
    (h_dvd : ∀ p : ℕ, Nat.Prime p → p ∣ n → (p - 1) ∣ n - 1) :
    ArithmeticFunction.Carmichael n ∣ n - 1 := by
  haveI : NeZero n := ⟨by omega⟩
  rw [ArithmeticFunction.carmichael_factorization n]
  rw [Finset.lcm_dvd_iff]
  intro p hp_p
  rw [Nat.mem_primeFactors] at hp_p
  rcases hp_p with ⟨hp, hp_n⟩
  have h_fac : n.factorization p = 1 := by
    have h_le := (squarefree_iff_factorization_le_one (by omega : n ≠ 0)).mp h_sf p
    have h_pos := hp.factorization_pos_of_dvd (by omega : n ≠ 0) hp_n.left
    omega
  rw [h_fac, pow_one]
  have hp2 : p ≠ 2 := by
    intro h_eq
    subst h_eq
    have h_even : Even n := by
      use n / 2
      omega
    rcases h_odd with ⟨k, hk⟩
    omega
  rw [carmichael_prime_odd hp hp2]
  exact h_dvd p hp hp_n.left

lemma p_dvd_den_of_p_mul_coprime {p : ℕ} (hp : Nat.Prime p) (q : ℚ)
    (h_num : ¬ (p : ℤ) ∣ (p * q).num) : p ∣ q.den := by
  have h_eq : q * (p : ℚ) = (p * q) := by ring
  have h_rel2 : (q.num : ℚ) / (q.den : ℚ) * (p : ℚ) = ((p * q).num : ℚ) / ((p * q).den : ℚ) := by
    rw [Rat.num_div_den, h_eq, Rat.num_div_den]
  have h_den_q : (q.den : ℚ) ≠ 0 := by positivity
  have h_den_pq : ((p * q).den : ℚ) ≠ 0 := by positivity
  have h_rel3 := congr_arg (fun x => x * (q.den : ℚ) * ((p * q).den : ℚ)) h_rel2
  dsimp at h_rel3
  have h_lhs : ((q.num : ℚ) / (q.den : ℚ) * (p : ℚ)) * (q.den : ℚ) * ((p * q).den : ℚ) = (q.num : ℚ) * (p : ℚ) * ((p * q).den : ℚ) := by
    calc
      _ = ((q.num : ℚ) / (q.den : ℚ) * (q.den : ℚ)) * (p : ℚ) * ((p * q).den : ℚ) := by ring
      _ = (q.num : ℚ) * (p : ℚ) * ((p * q).den : ℚ) := by rw [div_mul_cancel₀ _ h_den_q]
  have h_rhs : (((p * q).num : ℚ) / ((p * q).den : ℚ)) * (q.den : ℚ) * ((p * q).den : ℚ) = (q.den : ℚ) * ((p * q).num : ℚ) := by
    calc
      _ = (((p * q).num : ℚ) / ((p * q).den : ℚ) * ((p * q).den : ℚ)) * (q.den : ℚ) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ h_den_pq]; ring
  rw [h_lhs, h_rhs] at h_rel3
  have h_mul_int : (q.num : ℤ) * (p : ℤ) * ((p * q).den : ℤ) = (q.den : ℤ) * ((p * q).num : ℤ) := by
    exact_mod_cast h_rel3
  have h_p_dvd_lhs : ((p : ℤ) ∣ (q.num : ℤ) * (p : ℤ) * ((p * q).den : ℤ)) := by
    use (q.num : ℤ) * ((p * q).den : ℤ)
    ring
  have h_p_dvd_rhs : ((p : ℤ) ∣ (q.den : ℤ) * ((p * q).num : ℤ)) := by
    rwa [← h_mul_int]
  have hp_prime : _root_.Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    have : (p : ℤ).natAbs = p := Int.natAbs_natCast p
    rwa [this]
  rcases hp_prime.dvd_mul.mp h_p_dvd_rhs with h_dvd_den | h_dvd_num
  · have : (p : ℤ) ∣ (q.den : ℤ) := h_dvd_den
    exact_mod_cast this
  · contradiction

lemma bernoulli_identity (p k : ℕ) :
    ((k + 1 : ℚ) * (p : ℚ) * bernoulli k) =
      (k + 1 : ℚ) * (∑ x ∈ range p, (x : ℚ) ^ k) -
        ∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i)) := by
  have h_sum := sum_range_pow p k
  have h_sum' := congr_arg (fun x => (k + 1 : ℚ) * x) h_sum
  dsimp at h_sum'
  simp only [mul_sum] at h_sum'
  have h_nz : (k + 1 : ℚ) ≠ 0 := by positivity
  have h_cancel : (∑ x ∈ range (k + 1), (↑k + 1 : ℚ) * (bernoulli x * ↑((k + 1).choose x) * (p : ℚ) ^ (k + 1 - x) / (↑k + 1))) =
      ∑ x ∈ range (k + 1), bernoulli x * ↑((k + 1).choose x) * (p : ℚ) ^ (k + 1 - x) := by
    apply sum_congr rfl
    intro x hx
    field_simp [h_nz]
  rw [h_cancel] at h_sum'
  rw [← mul_sum] at h_sum'
  rw [sum_range_succ] at h_sum'
  have h_last : bernoulli k * ↑((k + 1).choose k) * (p : ℚ) ^ (k + 1 - k) = (k + 1 : ℚ) * (p : ℚ) * bernoulli k := by
    have h_choose : ((k + 1).choose k : ℚ) = (k + 1 : ℚ) := by
      rw [choose_succ_self_right]
      push_cast
      rfl
    rw [h_choose]
    have h_pow : (p : ℚ) ^ (k + 1 - k) = (p : ℚ) := by
      have : k + 1 - k = 1 := by omega
      rw [this, pow_one]
    rw [h_pow]
    ring
  rw [h_last] at h_sum'
  rw [h_sum']
  ring


/--
OEIS A309132 Conjecture: composite numbers n such that a(n) is squarefree are only the Carmichael numbers A002997.
-/




def IsPIntegral (p : ℕ) (q : ℚ) : Prop :=
  ¬ p ∣ q.den

lemma isPIntegral_add {p : ℕ} (hp : Nat.Prime p) {x y : ℚ}
    (hx : IsPIntegral p x) (hy : IsPIntegral p y) : IsPIntegral p (x + y) := by
  intro h
  have h_dvd := Rat.add_den_dvd x y
  have h_p_dvd : p ∣ x.den * y.den := h.trans h_dvd
  rcases hp.dvd_mul.mp h_p_dvd with h1 | h2
  · exact hx h1
  · exact hy h2

lemma isPIntegral_sub {p : ℕ} (hp : Nat.Prime p) {x y : ℚ}
    (hx : IsPIntegral p x) (hy : IsPIntegral p y) : IsPIntegral p (x - y) := by
  intro h
  have h_dvd := Rat.sub_den_dvd x y
  have h_p_dvd : p ∣ x.den * y.den := h.trans h_dvd
  rcases hp.dvd_mul.mp h_p_dvd with h1 | h2
  · exact hx h1
  · exact hy h2

lemma isPIntegral_mul {p : ℕ} (hp : Nat.Prime p) {x y : ℚ}
    (hx : IsPIntegral p x) (hy : IsPIntegral p y) : IsPIntegral p (x * y) := by
  intro h
  have h_dvd := Rat.mul_den_dvd x y
  have h_p_dvd : p ∣ x.den * y.den := h.trans h_dvd
  rcases hp.dvd_mul.mp h_p_dvd with h1 | h2
  · exact hx h1
  · exact hy h2

lemma isPIntegral_natCast (p : ℕ) (hp : Nat.Prime p) (n : ℕ) : IsPIntegral p (n : ℚ) := by
  intro h
  rw [Rat.den_natCast] at h
  have : p ∣ 1 := h
  have : p ≤ 1 := Nat.le_of_dvd (by decide) this
  have : p > 1 := hp.one_lt
  omega

lemma isPIntegral_div_coprime {p : ℕ} (hp : Nat.Prime p) {x : ℚ} (hx : IsPIntegral p x)
    {m : ℕ} (hm : Nat.Coprime p m) (hm0 : m ≠ 0) : IsPIntegral p (x / (m : ℚ)) := by
  have : x / (m : ℚ) = x * (m : ℚ)⁻¹ := div_eq_mul_inv x (m : ℚ)
  rw [this]
  apply isPIntegral_mul hp hx
  unfold IsPIntegral
  have hm_num : (m : ℚ).num = m := Rat.num_natCast m
  have h_den : ((m : ℚ)⁻¹).den = m := by
    rw [Rat.den_inv]
    split_ifs with h_cond
    · rw [Rat.num_natCast] at h_cond
      have : m = 0 := by exact_mod_cast h_cond
      contradiction
    · rw [hm_num, Int.natAbs_natCast]
  rw [h_den]
  intro hp_dvd_m
  have h_dvd : p ∣ m := hp_dvd_m
  have h_gcd : Nat.gcd p m = p := Nat.gcd_eq_left h_dvd
  rw [Nat.Coprime] at hm
  rw [h_gcd] at hm
  have : p > 1 := hp.one_lt
  omega

lemma not_psq_dvd_den_of_p_mul_integral {p : ℕ} (hp : Nat.Prime p) (q : ℚ)
    (h_int : ¬ p ∣ ((p : ℚ) * q).den) : ¬ p^2 ∣ q.den := by
  intro h_sq_dvd
  have h_pos : p > 0 := hp.pos
  have h_ne : (p : ℚ) ≠ 0 := by positivity
  have h_q_eq : q = ((p : ℚ) * q) * (p : ℚ)⁻¹ := by
    calc
      q = 1 * q := by rw [one_mul]
      _ = ((p : ℚ) * (p : ℚ)⁻¹) * q := by rw [mul_inv_cancel₀ h_ne]
      _ = ((p : ℚ) * q) * (p : ℚ)⁻¹ := by ring
  have h_inv_den : ((p : ℚ)⁻¹).den = p := by
    have hm_num : (p : ℚ).num = p := Rat.num_natCast p
    rw [Rat.den_inv]
    split_ifs with h_cond
    · rw [Rat.num_natCast] at h_cond
      have : p = 0 := by exact_mod_cast h_cond
      have : p > 1 := hp.one_lt
      omega
    · rw [hm_num, Int.natAbs_natCast]
  have h_mul_dvd := Rat.mul_den_dvd ((p : ℚ) * q) (p : ℚ)⁻¹
  rw [h_inv_den] at h_mul_dvd
  rw [← h_q_eq] at h_mul_dvd
  have h_p2_dvd : p^2 ∣ ((p : ℚ) * q).den * p := dvd_trans h_sq_dvd h_mul_dvd
  rw [sq] at h_p2_dvd
  rw [mul_comm ((p : ℚ) * q).den p] at h_p2_dvd
  have h_p_dvd := Nat.dvd_of_mul_dvd_mul_left h_pos h_p2_dvd
  exact h_int h_p_dvd

lemma dvd_of_p_pow_dvd {p : ℕ} (hp : Nat.Prime p) {A X : ℤ}
    (h_dvd : (p^4 : ℤ) ∣ A * X) (h_not : ¬ (p^2 : ℤ) ∣ X) : (p^3 : ℤ) ∣ A := by
  have hp_prime : _root_.Prime (p : ℤ) := prime_coe_int hp
  have h_p : (p : ℤ) ≠ 0 := by
    have : p > 0 := hp.pos
    exact_mod_cast this.ne'
  by_cases h1 : (p : ℤ) ∣ A
  · rcases h1 with ⟨A1, rfl⟩
    have h_dvd3 : (p^3 : ℤ) ∣ A1 * X := by
      rcases h_dvd with ⟨C, hC⟩
      use C
      have h_eq : (p : ℤ) * (A1 * X) = (p : ℤ) * (p^3 * C) := by
        calc
          (p : ℤ) * (A1 * X) = p * A1 * X := by ring
          _ = p^4 * C := hC
          _ = p * (p^3 * C) := by ring
      exact mul_left_cancel₀ h_p h_eq
    by_cases h2 : (p : ℤ) ∣ A1
    · rcases h2 with ⟨A2, rfl⟩
      have h_dvd2 : (p^2 : ℤ) ∣ A2 * X := by
        rcases h_dvd3 with ⟨C, hC⟩
        use C
        have h_eq : (p : ℤ) * (A2 * X) = (p : ℤ) * (p^2 * C) := by
          calc
            (p : ℤ) * (A2 * X) = p * A2 * X := by ring
            _ = p^3 * C := hC
            _ = p * (p^2 * C) := by ring
        exact mul_left_cancel₀ h_p h_eq
      by_cases h3 : (p : ℤ) ∣ A2
      · rcases h3 with ⟨A3, rfl⟩
        use A3
        ring
      · have hp_dvd : (p : ℤ) ∣ A2 * X := by
          have : (p : ℤ) ∣ (p^2 : ℤ) := by use (p : ℤ); ring
          exact dvd_trans this h_dvd2
        have h_dvd_X : (p : ℤ) ∣ X := by
          rcases hp_prime.dvd_mul.mp hp_dvd with h_div | h_div
          · contradiction
          · exact h_div
        rcases h_dvd_X with ⟨X1, rfl⟩
        have h_p_dvd' : (p : ℤ) ∣ A2 * X1 := by
          rcases h_dvd2 with ⟨C, hC⟩
          use C
          have h_eq : (p : ℤ) * (A2 * X1) = (p : ℤ) * (p * C) := by
            calc
              (p : ℤ) * (A2 * X1) = A2 * (p * X1) := by ring
              _ = p^2 * C := hC
              _ = p * (p * C) := by ring
          exact mul_left_cancel₀ h_p h_eq
        have h_X1 : (p : ℤ) ∣ X1 := by
          rcases hp_prime.dvd_mul.mp h_p_dvd' with h_div | h_div
          · contradiction
          · exact h_div
        rcases h_X1 with ⟨X2, rfl⟩
        have h_contra : (p^2 : ℤ) ∣ (p : ℤ) * ((p : ℤ) * X2) := by
          use X2
          ring
        contradiction
    · have hp_dvd : (p : ℤ) ∣ A1 * X := by
        have : (p : ℤ) ∣ (p^3 : ℤ) := by use (p^2 : ℤ); ring
        exact dvd_trans this h_dvd3
      have h_dvd_X : (p : ℤ) ∣ X := by
        rcases hp_prime.dvd_mul.mp hp_dvd with h_div | h_div
        · contradiction
        · exact h_div
      rcases h_dvd_X with ⟨X1, rfl⟩
      have h_p2_dvd' : (p^2 : ℤ) ∣ A1 * X1 := by
        rcases h_dvd3 with ⟨C, hC⟩
        use C
        have h_eq : (p : ℤ) * (A1 * X1) = (p : ℤ) * (p^2 * C) := by
          calc
            (p : ℤ) * (A1 * X1) = A1 * (p * X1) := by ring
            _ = p^3 * C := hC
            _ = p * (p^2 * C) := by ring
        exact mul_left_cancel₀ h_p h_eq
      have hp_dvd2 : (p : ℤ) ∣ A1 * X1 := by
        have : (p : ℤ) ∣ (p^2 : ℤ) := by use (p : ℤ); ring
        exact dvd_trans this h_p2_dvd'
      have h_X2 : (p : ℤ) ∣ X1 := by
        rcases hp_prime.dvd_mul.mp hp_dvd2 with h_div | h_div
        · contradiction
        · exact h_div
      rcases h_X2 with ⟨X2, rfl⟩
      have h_contra : (p^2 : ℤ) ∣ (p : ℤ) * ((p : ℤ) * X2) := by
        use X2
        ring
      contradiction
  · have hp_dvd : (p : ℤ) ∣ A * X := by
      have : (p : ℤ) ∣ (p^4 : ℤ) := by use (p^3 : ℤ); ring
      exact dvd_trans this h_dvd
    have h_dvd_X : (p : ℤ) ∣ X := by
      rcases hp_prime.dvd_mul.mp hp_dvd with h_div | h_div
      · contradiction
      · exact h_div
    rcases h_dvd_X with ⟨X1, rfl⟩
    have h_p3_dvd' : (p^3 : ℤ) ∣ A * X1 := by
      rcases h_dvd with ⟨C, hC⟩
      use C
      have h_eq : (p : ℤ) * (A * X1) = (p : ℤ) * (p^3 * C) := by
        calc
          (p : ℤ) * (A * X1) = A * (p * X1) := by ring
          _ = p^4 * C := hC
          _ = p * (p^3 * C) := by ring
      exact mul_left_cancel₀ h_p h_eq
    have hp_dvd2 : (p : ℤ) ∣ A * X1 := by
      have : (p : ℤ) ∣ (p^3 : ℤ) := by use (p^2 : ℤ); ring
      exact dvd_trans this h_p3_dvd'
    have h_X2 : (p : ℤ) ∣ X1 := by
      rcases hp_prime.dvd_mul.mp hp_dvd2 with h_div | h_div
      · contradiction
      · exact h_div
    rcases h_X2 with ⟨X2, rfl⟩
    have h_contra : (p^2 : ℤ) ∣ (p : ℤ) * ((p : ℤ) * X2) := by
      use X2
      ring
    contradiction

lemma p_sq_dvd_of_p_pow_dvd {p : ℕ} (hp : Nat.Prime p) {B X : ℤ}
    (h_dvd : (p^3 : ℤ) ∣ B * X) (h_not : ¬ (p^2 : ℤ) ∣ X) : (p^2 : ℤ) ∣ B := by
  have hp_prime : _root_.Prime (p : ℤ) := prime_coe_int hp
  have h_p : (p : ℤ) ≠ 0 := by
    have : p > 0 := hp.pos
    exact_mod_cast this.ne'
  by_cases h1 : (p : ℤ) ∣ B
  · rcases h1 with ⟨B1, rfl⟩
    have h_dvd2 : (p^2 : ℤ) ∣ B1 * X := by
      rcases h_dvd with ⟨C, hC⟩
      use C
      have h_eq : (p : ℤ) * (B1 * X) = (p : ℤ) * (p^2 * C) := by
        calc
          (p : ℤ) * (B1 * X) = p * B1 * X := by ring
          _ = p^3 * C := hC
          _ = p * (p^2 * C) := by ring
      exact mul_left_cancel₀ h_p h_eq
    by_cases h2 : (p : ℤ) ∣ B1
    · rcases h2 with ⟨B2, rfl⟩
      use B2
      ring
    · have hp_dvd : (p : ℤ) ∣ B1 * X := by
        have : (p : ℤ) ∣ (p^2 : ℤ) := by use (p : ℤ); ring
        exact dvd_trans this h_dvd2
      have h_dvd_X : (p : ℤ) ∣ X := by
        rcases hp_prime.dvd_mul.mp hp_dvd with h_div | h_div
        · contradiction
        · exact h_div
      rcases h_dvd_X with ⟨X1, rfl⟩
      have h_p_dvd' : (p : ℤ) ∣ B1 * X1 := by
        rcases h_dvd2 with ⟨C, hC⟩
        use C
        have h_eq : (p : ℤ) * (B1 * X1) = (p : ℤ) * (p * C) := by
          calc
            (p : ℤ) * (B1 * X1) = B1 * (p * X1) := by ring
            _ = p^2 * C := hC
            _ = p * (p * C) := by ring
        exact mul_left_cancel₀ h_p h_eq
      have h_X1 : (p : ℤ) ∣ X1 := by
        rcases hp_prime.dvd_mul.mp h_p_dvd' with h_div | h_div
        · contradiction
        · exact h_div
      rcases h_X1 with ⟨X2, rfl⟩
      have h_contra : (p^2 : ℤ) ∣ (p : ℤ) * ((p : ℤ) * X2) := by
        use X2
        ring
      contradiction
  · have hp_dvd : (p : ℤ) ∣ B * X := by
      have : (p : ℤ) ∣ (p^3 : ℤ) := by use (p^2 : ℤ); ring
      exact dvd_trans this h_dvd
    have h_dvd_X : (p : ℤ) ∣ X := by
      rcases hp_prime.dvd_mul.mp hp_dvd with h_div | h_div
      · contradiction
      · exact h_div
    rcases h_dvd_X with ⟨X1, rfl⟩
    have h_p2_dvd' : (p^2 : ℤ) ∣ B * X1 := by
      rcases h_dvd with ⟨C, hC⟩
      use C
      have h_eq : (p : ℤ) * (B * X1) = (p : ℤ) * (p^2 * C) := by
        calc
          (p : ℤ) * (B * X1) = B * (p * X1) := by ring
          _ = p^3 * C := hC
          _ = p * (p^2 * C) := by ring
      exact mul_left_cancel₀ h_p h_eq
    have hp_dvd2 : (p : ℤ) ∣ B * X1 := by
      have : (p : ℤ) ∣ (p^2 : ℤ) := by use (p : ℤ); ring
      exact dvd_trans this h_p2_dvd'
    have h_X2 : (p : ℤ) ∣ X1 := by
      rcases hp_prime.dvd_mul.mp hp_dvd2 with h_div | h_div
      · contradiction
      · exact h_div
    rcases h_X2 with ⟨X2, rfl⟩
    have h_contra : (p^2 : ℤ) ∣ (p : ℤ) * ((p : ℤ) * X2) := by
      use X2
      ring
    contradiction

lemma p_sq_dvd_bernoulli_den_of_not_dvd_a (n : ℕ) (hn : n ≠ 0) {p : ℕ} (hp : Nat.Prime p)
    (hp2_n : p^2 ∣ n) (hp_den : p ∣ (bernoulli (n - 1)).den) (h_not_dvd_an : ¬ (p^2 : ℤ) ∣ (a n : ℤ)) : p^2 ∣ (bernoulli (n - 1)).den := by
  set B_nm1 := bernoulli (n - 1)
  set F_n : ℚ := (B_nm1.num : ℚ) / n + (B_nm1.den : ℚ) / (n * n)
  have h_eq : F_n = ((B_nm1.num * n + B_nm1.den : ℤ) : ℚ) / (n * n : ℚ) := by
    dsimp [F_n]
    have h1 : (B_nm1.num : ℚ) / n = ((B_nm1.num : ℚ) * n) / (n * n : ℚ) := by
      have hn_q : (n : ℚ) ≠ 0 := by positivity
      rw [mul_div_mul_right _ _ hn_q]
    rw [h1]
    rw [← add_div]
    push_cast
    rfl
  have h_div : F_n = Rat.divInt (B_nm1.num * n + B_nm1.den : ℤ) (n * n : ℕ) := by
    rw [h_eq]
    rw [Rat.divInt_eq_div]
    push_cast
    rfl
  have h_nz : (n * n : ℤ) ≠ 0 := by positivity
  rcases Rat.num_den_mk h_nz h_div with ⟨c, h_num, h_den⟩
  have h_F_den : F_n.den = a n := by
    unfold a
    split_ifs with h_cond
    · contradiction
    · rfl
  have h_rel_cast : (B_nm1.num * n + B_nm1.den : ℤ) * (a n : ℤ) =
      ((n : ℤ) * (n : ℤ)) * F_n.num := by
    have h_rel' : (B_nm1.num * n + B_nm1.den : ℤ) * F_n.den = (n * n : ℤ) * F_n.num := by
      calc
        _ = (c * F_n.num : ℤ) * F_n.den := by rw [h_num]
        _ = (c * F_n.den : ℤ) * F_n.num := by ring
        _ = _ := by rw [← h_den]
    rw [h_F_den] at h_rel'
    exact_mod_cast h_rel'
  have hp_n : p ∣ n := dvd_trans (dvd_sq p) hp2_n
  rcases hp2_n with ⟨m, rfl⟩
  have h_n_n : ( (p * p * m : ℕ) * (p * p * m : ℕ) : ℤ ) = (p : ℤ)^4 * (m * m : ℤ) := by ring
  have h_p4_dvd_nn : (p^4 : ℤ) ∣ ( (p * p * m : ℕ) * (p * p * m : ℕ) : ℤ ) := by
    rw [h_n_n]
    exact dvd_mul_right _ _
  have h_p4_dvd_rhs : (p^4 : ℤ) ∣ (( (p * p * m : ℕ) : ℤ) * (( p * p * m : ℕ) : ℤ)) * F_n.num := by
    exact dvd_mul_of_dvd_left h_p4_dvd_nn F_n.num
  have h_p4_dvd_lhs : (p^4 : ℤ) ∣ (B_nm1.num * (p * p * m : ℕ) + B_nm1.den : ℤ) * (a (p * p * m) : ℤ) := by
    have h_cast : ((p * p * m : ℕ) : ℤ) = (p * p * m : ℤ) := by push_cast; rfl
    rw [h_cast] at h_rel_cast
    rw [h_rel_cast]
    exact h_p4_dvd_rhs
  have h_p3_dvd_B : (p^3 : ℤ) ∣ (B_nm1.num * (p * p * m : ℕ) + B_nm1.den : ℤ) := by
    have h_not' : ¬ p^2 ∣ (a (p * p * m) : ℤ) := h_not_dvd_an
    exact dvd_of_p_pow_dvd hp h_p4_dvd_lhs h_not'
  rcases hp_den with ⟨d, hd⟩
  have hd_int : (B_nm1.den : ℤ) = p * d := by exact_mod_cast hd
  have h_B_eq : (B_nm1.num * (p * p * m : ℕ) + B_nm1.den : ℤ) = (p : ℤ) * (B_nm1.num * p * m + d) := by
    calc
      (B_nm1.num * (p * p * m : ℕ) + B_nm1.den : ℤ) = B_nm1.num * (p * p * m) + p * d := by rw [hd_int]; push_cast; rfl
      _ = (p : ℤ) * (B_nm1.num * p * m + d) := by ring
  rw [h_B_eq] at h_p3_dvd_B
  have h_p : (p : ℤ) ≠ 0 := by
    have : p > 0 := hp.pos
    exact_mod_cast this.ne'
  have h_p2_dvd_sum : (p^2 : ℤ) ∣ (B_nm1.num * p * m + d : ℤ) := by
    rcases h_p3_dvd_B with ⟨C, hC⟩
    use C
    have h_eq : (p : ℤ) * (B_nm1.num * p * m + d : ℤ) = (p : ℤ) * (p^2 * C) := by
      calc
        _ = (p : ℤ)^3 * C := hC.symm
        _ = (p : ℤ) * (p^2 * C) := by ring
    exact mul_left_cancel₀ h_p h_eq
  have hp_prime : _root_.Prime (p : ℤ) := prime_coe_int hp
  have h_p_dvd_sum : (p : ℤ) ∣ (B_nm1.num * p * m + d : ℤ) := by
    have : (p : ℤ) ∣ (p^2 : ℤ) := by use (p : ℤ); ring
    exact dvd_trans this h_p2_dvd_sum
  have h_p_dvd_pm : (p : ℤ) ∣ B_nm1.num * p * m := by
    use B_nm1.num * m
    ring
  have h_p_dvd_d : (p : ℤ) ∣ (d : ℤ) := by
    have : (d : ℤ) = (B_nm1.num * p * m + d) - B_nm1.num * p * m := by ring
    rw [this]
    exact dvd_sub h_p_dvd_sum h_p_dvd_pm
  rcases h_p_dvd_d with ⟨d', hd'⟩
  have hd'_nat : d = p * d' := by exact_mod_cast hd'
  have h_p2_dvd_den : p^2 ∣ B_nm1.den := by
    use d'
    rw [hd, hd'_nat]
    ring
  exact h_p2_dvd_den

lemma term_p_integral (p k : ℕ) (hp : Nat.Prime p) (i : ℕ) (hi : i < k)
    (ih : ∀ m < k, IsPIntegral p (p * bernoulli m)) :
    IsPIntegral p (bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k + 1 - i)) := by
  have h_eq : bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k + 1 - i) =
      ((p : ℚ) * bernoulli i) * (((k + 1).choose i : ℚ) * (p : ℚ) ^ (k - i)) := by
    have h_pow : (p : ℚ) ^ (k + 1 - i) = (p : ℚ) * (p : ℚ) ^ (k - i) := by
      have : k + 1 - i = 1 + (k - i) := by omega
      rw [this, pow_add, pow_one]
    rw [h_pow]
    ring
  rw [h_eq]
  apply isPIntegral_mul hp
  · exact ih i hi
  · apply isPIntegral_mul hp
    · exact isPIntegral_natCast p hp ((k + 1).choose i)
    · have : (p : ℚ) ^ (k - i) = ((p ^ (k - i) : ℕ) : ℚ) := by push_cast; rfl
      rw [this]
      exact isPIntegral_natCast p hp (p ^ (k - i))

lemma isPIntegral_sum {α : Type*} {p : ℕ} (hp : Nat.Prime p) (s : Finset α) (f : α → ℚ)
    (h : ∀ x ∈ s, IsPIntegral p (f x)) : IsPIntegral p (∑ x ∈ s, f x) := by
  haveI := Classical.decEq α
  induction' s using Finset.induction with x s hx ih
  · simp only [Finset.sum_empty]
    exact isPIntegral_natCast p hp 0
  · simp only [Finset.sum_insert hx]
    apply isPIntegral_add hp
    · exact h x (Finset.mem_insert_self x s)
    · apply ih
      intro y hy
      exact h y (Finset.mem_insert_of_mem hy)

lemma sum_term_p_integral (p k : ℕ) (hp : Nat.Prime p)
    (ih : ∀ m < k, IsPIntegral p (p * bernoulli m)) :
    IsPIntegral p (∑ i ∈ Finset.range k, (bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k + 1 - i))) := by
  apply isPIntegral_sum hp
  intro i hi
  rw [Finset.mem_range] at hi
  exact term_p_integral p k hp i hi ih

lemma term_eq_choose (k i : ℕ) (hi : i < k) :
    ((k + 1).choose i : ℚ) / (k + 1 : ℚ) = (k.choose i : ℚ) / ((k + 1 - i : ℕ) : ℚ) := by
  have h1 : ((k.choose i * (k + 1) : ℕ) : ℚ) = (((k + 1).choose i * (k + 1 - i) : ℕ) : ℚ) := by
    congr 1
    rw [Nat.choose_mul_succ_eq]
  push_cast at h1
  have h2 : (k + 1 : ℚ) ≠ 0 := by positivity
  have h3 : ((k + 1 - i : ℕ) : ℚ) ≠ 0 := by
    have : k + 1 - i > 0 := by omega
    positivity
  rw [div_eq_div_iff h2 h3]
  exact h1.symm

lemma term_eq_choose_rearranged (k i : ℕ) (p : ℕ) (hi : i < k) :
    bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k + 1 - i) / (k + 1 : ℚ) =
      (p * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ)) := by
  have h1 : ((k + 1).choose i : ℚ) / (k + 1 : ℚ) = (k.choose i : ℚ) / ((k + 1 - i : ℕ) : ℚ) := term_eq_choose k i hi
  have h_pow : (p : ℚ) ^ (k + 1 - i) = (p : ℚ) * (p : ℚ) ^ (k - i) := by
    have : k + 1 - i = 1 + (k - i) := by omega
    rw [this, pow_add, pow_one]
  rw [h_pow]
  calc
    bernoulli i * ((k + 1).choose i : ℚ) * ((p : ℚ) * (p : ℚ) ^ (k - i)) / (k + 1 : ℚ)
      = (bernoulli i * (p : ℚ) * (p : ℚ) ^ (k - i)) * (((k + 1).choose i : ℚ) / (k + 1 : ℚ)) := by ring
    _ = (bernoulli i * (p : ℚ) * (p : ℚ) ^ (k - i)) * ((k.choose i : ℚ) / ((k + 1 - i : ℕ) : ℚ)) := by rw [h1]
    _ = (p * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ)) := by ring

lemma bernoulli_identity_divided (p k : ℕ) (hk : k > 0) :
    (p : ℚ) * bernoulli k =
      (∑ x ∈ range p, (x : ℚ) ^ k) -
        ∑ i ∈ range k, ((p * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) := by
  have h_nz : (k + 1 : ℚ) ≠ 0 := by positivity
  have h_id := bernoulli_identity p k
  have h_div : ((k + 1 : ℚ) * (p : ℚ) * bernoulli k) / (k + 1 : ℚ) =
      ((k + 1 : ℚ) * (∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i))) / (k + 1 : ℚ) := by
    rw [h_id]
  have h_lhs : ((k + 1 : ℚ) * (p : ℚ) * bernoulli k) / (k + 1 : ℚ) = (p : ℚ) * bernoulli k := by
    calc
      _ = (k + 1 : ℚ) * ((p : ℚ) * bernoulli k) / (k + 1 : ℚ) := by ring
      _ = (p : ℚ) * bernoulli k := by rw [mul_div_cancel_left₀ _ h_nz]
  have h_rhs : ((k + 1 : ℚ) * (∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i))) / (k + 1 : ℚ) =
      (∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, ((p * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) := by
    calc
      _ = ((k + 1 : ℚ) * (∑ x ∈ range p, (x : ℚ) ^ k)) / (k + 1 : ℚ) - (∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i))) / (k + 1 : ℚ) := by rw [sub_div]
      _ = (∑ x ∈ range p, (x : ℚ) ^ k) - (∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i))) / (k + 1 : ℚ) := by rw [mul_div_cancel_left₀ _ h_nz]
      _ = (∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i) / (k + 1 : ℚ)) := by rw [sum_div]
      _ = (∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, ((p * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) := by
        congr 1
        apply sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        exact term_eq_choose_rearranged k i p hi
  rw [h_lhs] at h_div
  rw [h_rhs] at h_div
  exact h_div

lemma p_pow_div_m_p_integral (p : ℕ) (hp : Nat.Prime p) (m : ℕ) (hm : m ≥ 2) :
    IsPIntegral p ((p : ℚ) ^ (m - 1) / (m : ℚ)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hpm : p ∣ m
    · rcases hpm with ⟨a, rfl⟩
      have ha0 : a ≠ 0 := by
        rintro rfl
        omega
      have ha_pos : a > 0 := Nat.pos_of_ne_zero ha0
      by_cases ha1 : a = 1
      · subst ha1
        have hp2 : p ≥ 2 := hp.two_le
        have h_goal : (p : ℚ) ^ (p * 1 - 1) / ((p * 1 : ℕ) : ℚ) = (p : ℚ) ^ (p - 1) / (p : ℚ) := by
          have h_m_eq : p * 1 = p := by omega
          rw [h_m_eq]
        rw [h_goal]
        have : ((p : ℚ) ^ (p - 1) / (p : ℚ)) = (p : ℚ) ^ (p - 2) := by
          have : p - 1 = (p - 2) + 1 := by omega
          rw [this, pow_add, pow_one]
          have h_nz : (p : ℚ) ≠ 0 := by positivity
          rw [mul_div_cancel_right₀ _ h_nz]
        rw [this]
        have : (p : ℚ) ^ (p - 2) = ((p ^ (p - 2) : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact isPIntegral_natCast p hp (p ^ (p - 2))
      · have ha2 : a ≥ 2 := by omega
        have h_am : a < p * a := by
          have hp2 : p ≥ 2 := hp.two_le
          nlinarith
        have ih_a := ih a h_am ha2
        have h_eq : (p : ℚ) ^ (p * a - 1) / ((p * a : ℕ) : ℚ) = (p : ℚ) ^ (p * a - 2) / (a : ℚ) := by
          have hp2 : p ≥ 2 := hp.two_le
          have : p * a - 1 = (p * a - 2) + 1 := by omega
          rw [this, pow_add, pow_one]
          have h_nz : (p : ℚ) ≠ 0 := by positivity
          calc
            (p : ℚ) ^ (p * a - 2) * (p : ℚ) / ((p * a : ℕ) : ℚ)
              = (p : ℚ) ^ (p * a - 2) * (p : ℚ) / ((p : ℚ) * (a : ℚ)) := by push_cast; rfl
            _ = (p : ℚ) * (p : ℚ) ^ (p * a - 2) / ((p : ℚ) * (a : ℚ)) := by ring
            _ = (p : ℚ) ^ (p * a - 2) / (a : ℚ) := by rw [mul_div_mul_left _ _ h_nz]
        rw [h_eq]
        have h_sub : p * a - 2 ≥ a - 1 := by
          have hp2 : p ≥ 2 := hp.two_le
          have : p * a ≥ 2 * a := Nat.mul_le_mul_right a hp2
          omega
        have h_eq2 : (p : ℚ) ^ (p * a - 2) / (a : ℚ) = (p : ℚ) ^ (p * a - 2 - (a - 1)) * ((p : ℚ) ^ (a - 1) / (a : ℚ)) := by
          rw [← mul_div_assoc]
          congr 1
          rw [← pow_add]
          congr 1
          omega
        rw [h_eq2]
        apply isPIntegral_mul hp
        · have : (p : ℚ) ^ (p * a - 2 - (a - 1)) = ((p ^ (p * a - 2 - (a - 1)) : ℕ) : ℚ) := by push_cast; rfl
          rw [this]
          exact isPIntegral_natCast p hp _
        · exact ih_a
    · have h_cop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
      apply isPIntegral_div_coprime hp
      · have : (p : ℚ) ^ (m - 1) = ((p ^ (m - 1) : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact isPIntegral_natCast p hp _
      · exact h_cop
      · omega

lemma p_bernoulli_p_integral (p : ℕ) (hp : Nat.Prime p) (k : ℕ) :
    IsPIntegral p (p * bernoulli k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst hk
      have : (p : ℚ) * bernoulli 0 = (p : ℚ) := by
        rw [bernoulli_zero]
        ring
      rw [this]
      exact isPIntegral_natCast p hp p
    · have hk_pos : k > 0 := Nat.pos_of_ne_zero hk
      rw [bernoulli_identity_divided p k hk_pos]
      apply isPIntegral_sub hp
      · apply isPIntegral_sum hp
        intro x hx
        have : (x : ℚ) ^ k = ((x ^ k : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact isPIntegral_natCast p hp (x ^ k)
      · apply isPIntegral_sum hp
        intro i hi
        rw [Finset.mem_range] at hi
        apply isPIntegral_mul hp
        · exact ih i hi
        · set m := k + 1 - i
          have hm : m ≥ 2 := by
            have : i < k := hi
            omega
          have h_pow_eq : (p : ℚ) ^ (k - i) = (p : ℚ) ^ (m - 1) := by
            congr 1
            omega
          have h_den_eq : ((k + 1 - i : ℕ) : ℚ) = (m : ℚ) := by
            dsimp [m]
          rw [h_pow_eq]
          rw [h_den_eq]
          have h_mul : ((k.choose i : ℚ) * (p : ℚ) ^ (m - 1) / (m : ℚ)) = (k.choose i : ℚ) * ((p : ℚ) ^ (m - 1) / (m : ℚ)) := by ring
          rw [h_mul]
          apply isPIntegral_mul hp
          · exact isPIntegral_natCast p hp (k.choose i)
          · exact p_pow_div_m_p_integral p hp m hm

lemma p_pow_sub_two_div_m_p_integral (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (m : ℕ) (hm : m ≥ 2) :
    IsPIntegral p ((p : ℚ) ^ (m - 2) / (m : ℚ)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hpm : p ∣ m
    · rcases hpm with ⟨a, rfl⟩
      have ha0 : a ≠ 0 := by
        rintro rfl
        omega
      have ha_pos : a > 0 := Nat.pos_of_ne_zero ha0
      by_cases ha1 : a = 1
      · subst ha1
        have h_goal : (p : ℚ) ^ (p * 1 - 2) / ((p * 1 : ℕ) : ℚ) = (p : ℚ) ^ (p - 2) / (p : ℚ) := by
          have h_m_eq : p * 1 = p := by omega
          have h_sub_eq : p * 1 - 2 = p - 2 := by omega
          rw [h_m_eq, h_sub_eq]
        rw [h_goal]
        have : ((p : ℚ) ^ (p - 2) / (p : ℚ)) = (p : ℚ) ^ (p - 3) := by
          have : p - 2 = (p - 3) + 1 := by omega
          rw [this, pow_add, pow_one]
          have h_nz : (p : ℚ) ≠ 0 := by positivity
          rw [mul_div_cancel_right₀ _ h_nz]
        rw [this]
        have : (p : ℚ) ^ (p - 3) = ((p ^ (p - 3) : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact isPIntegral_natCast p hp (p ^ (p - 3))
      · have ha2 : a ≥ 2 := by omega
        have h_am : a < p * a := by
          nlinarith
        have ih_a := ih a h_am ha2
        have h_eq : (p : ℚ) ^ (p * a - 2) / ((p * a : ℕ) : ℚ) = (p : ℚ) ^ (p * a - 3) / (a : ℚ) := by
          have : p * a - 2 = (p * a - 3) + 1 := by omega
          rw [this, pow_add, pow_one]
          have h_nz : (p : ℚ) ≠ 0 := by positivity
          calc
            (p : ℚ) ^ (p * a - 3) * (p : ℚ) / ((p * a : ℕ) : ℚ)
              = (p : ℚ) ^ (p * a - 3) * (p : ℚ) / ((p : ℚ) * (a : ℚ)) := by push_cast; rfl
            _ = (p : ℚ) * (p : ℚ) ^ (p * a - 3) / ((p : ℚ) * (a : ℚ)) := by ring
            _ = (p : ℚ) ^ (p * a - 3) / (a : ℚ) := by rw [mul_div_mul_left _ _ h_nz]
        rw [h_eq]
        have h_sub : p * a - 3 ≥ a - 2 := by
          have : p * a ≥ 3 * a := Nat.mul_le_mul_right a hp3
          omega
        have h_eq2 : (p : ℚ) ^ (p * a - 3) / (a : ℚ) = (p : ℚ) ^ (p * a - 2 - (a - 1)) * ((p : ℚ) ^ (a - 1) / (a : ℚ)) := by
          rw [← mul_div_assoc]
          congr 1
          rw [← pow_add]
          congr 1
          omega
        rw [h_eq2]
        apply isPIntegral_mul hp
        · have : (p : ℚ) ^ (p * a - 2 - (a - 1)) = ((p ^ (p * a - 2 - (a - 1)) : ℕ) : ℚ) := by push_cast; rfl
          rw [this]
          exact isPIntegral_natCast p hp _
        · exact ih_a
    · have h_cop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
      apply isPIntegral_div_coprime hp
      · have : (p : ℚ) ^ (m - 2) = ((p ^ (m - 2) : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact isPIntegral_natCast p hp _
      · exact h_cop
      · omega

lemma bernoulli_identity_divided_add_one_div_p (p k : ℕ) (hp : Nat.Prime p) (hk : k > 0) :
    bernoulli k + (1 : ℚ) / (p : ℚ) =
      ((∑ x ∈ range p, (x : ℚ) ^ k) + 1) / (p : ℚ) -
        ∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) := by
  have h_nz : (p : ℚ) ≠ 0 := by
    have : p ≠ 0 := hp.ne_zero
    positivity
  have h_id := bernoulli_identity_divided p k hk
  have h_div : bernoulli k = (∑ x ∈ range p, (x : ℚ) ^ k) / (p : ℚ) -
      (∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) / (p : ℚ) := by
    calc
      bernoulli k = ((p : ℚ) * bernoulli k) / (p : ℚ) := by rw [mul_div_cancel_left₀ _ h_nz]
      _ = ((∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) / (p : ℚ) := by rw [h_id]
      _ = _ := by rw [sub_div]
  rw [h_div]
  have h_sum_div : (∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) / (p : ℚ) =
      ∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h_pow : (p : ℚ) ^ (k - i) = (p : ℚ) * (p : ℚ) ^ (k - 1 - i) := by
      have : k - i = 1 + (k - 1 - i) := by omega
      rw [this, pow_add, pow_one]
    rw [h_pow]
    calc
      ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * ((p : ℚ) * (p : ℚ) ^ (k - 1 - i)) / ((k + 1 - i : ℕ) : ℚ)) / (p : ℚ)
        = ((p : ℚ) * bernoulli i) * (((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) * (p : ℚ)) / (p : ℚ) := by ring
      _ = ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) * (p : ℚ) / (p : ℚ) := by ring
      _ = ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) := by rw [mul_div_cancel_right₀ _ h_nz]
  rw [h_sum_div]
  ring

lemma sum_pow_zmod (p i : ℕ) [Fact p.Prime] (hi : i > 0) :
    (∑ x : ZMod p, x ^ i) = if p - 1 ∣ i then -1 else 0 := by
  have h_univ : (∑ x : ZMod p, x ^ i) = ∑ x ∈ univ \ {0}, x ^ i := by
    rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton, zero_pow hi.ne', add_zero]
  let phi := Function.Embedding.mk (fun x : Units (ZMod p) ↦ (x : ZMod p)) Units.val_injective
  have h_map : univ.map phi = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton] using isUnit_iff_ne_zero
  rw [← h_map, sum_map] at h_univ
  rw [h_univ]
  have h_card : Fintype.card (ZMod p) = p := ZMod.card p
  have h_sum := FiniteField.sum_pow_units (ZMod p) i
  rw [h_card] at h_sum
  exact h_sum

lemma bernoulli_p_integral_of_not_dvd (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (k : ℕ) (hk : k > 0)
    (h_not_dvd : ¬ (p - 1) ∣ k) (ih : ∀ i < k, IsPIntegral p (p * bernoulli i)) :
    IsPIntegral p (bernoulli k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h_nz : (p : ℚ) ≠ 0 := by
    have : p ≠ 0 := hp.ne_zero
    positivity
  have h_div : bernoulli k = (∑ x ∈ range p, (x : ℚ) ^ k) / (p : ℚ) -
      ∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) := by
    calc
      bernoulli k = ((p : ℚ) * bernoulli k) / (p : ℚ) := by rw [mul_div_cancel_left₀ _ h_nz]
      _ = ((∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) / (p : ℚ) := by
        rw [bernoulli_identity_divided p k hk]
      _ = _ := by
        rw [sub_div]
        apply congrArg₂ _ rfl
        rw [sum_div]
        apply sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have h_pow : (p : ℚ) ^ (k - i) = (p : ℚ) * (p : ℚ) ^ (k - 1 - i) := by
          have : k - i = 1 + (k - 1 - i) := by omega
          rw [this, pow_add, pow_one]
        rw [h_pow]
        calc
          ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * ((p : ℚ) * (p : ℚ) ^ (k - 1 - i)) / ((k + 1 - i : ℕ) : ℚ)) / (p : ℚ)
            = ((p : ℚ) * bernoulli i) * (((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) * (p : ℚ)) / (p : ℚ) := by ring
          _ = ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) * (p : ℚ) / (p : ℚ) := by ring
          _ = ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) := by rw [mul_div_cancel_right₀ _ h_nz]
  rw [h_div]
  apply isPIntegral_sub hp
  · have h_sum_zero : ((∑ x ∈ range p, x ^ k : ℕ) : ZMod p) = 0 := by
      have h_cast : ((∑ x ∈ range p, x ^ k : ℕ) : ZMod p) = ∑ x ∈ range p, (x : ZMod p) ^ k := by
        push_cast
        rfl
      rw [h_cast]
      have h_univ : (∑ x ∈ range p, (x : ZMod p) ^ k) = ∑ x : ZMod p, x ^ k := by
        have h_fin := Fin.sum_univ_eq_sum_range (n := p) (fun (x : ℕ) ↦ (x : ZMod p) ^ k)
        rw [← h_fin]
        change (∑ i : Fin p, ((i : ℕ) : ZMod p) ^ k) = ∑ x : ZMod p, x ^ k
        apply sum_congr rfl
        intro i hi
        congr 1
        rcases p with _ | p_pred
        · contradiction
        · apply Fin.ext
          exact Nat.mod_eq_of_lt i.is_lt
      rw [h_univ]
      rw [sum_pow_zmod (p := p) (i := k) (hi := hk)]
      rw [if_neg h_not_dvd]
    have h_dvd : p ∣ ∑ x ∈ range p, x ^ k := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h_sum_zero
    rcases h_dvd with ⟨M, hM⟩
    have h_eq_M : ((∑ x ∈ range p, (x : ℚ) ^ k) / (p : ℚ)) = (M : ℚ) := by
      have h_cast2 : (∑ x ∈ range p, (x : ℚ) ^ k) = ((∑ x ∈ range p, x ^ k : ℕ) : ℚ) := by
        exact_mod_cast rfl
      rw [h_cast2]
      rw [hM]
      push_cast
      exact mul_div_cancel_left₀ _ h_nz
    rw [h_eq_M]
    exact isPIntegral_natCast p hp M
  · apply isPIntegral_sum hp
    intro i hi
    rw [Finset.mem_range] at hi
    apply isPIntegral_mul hp
    · exact ih i hi
    · set m := k + 1 - i
      have hm : m ≥ 2 := by omega
      have h_pow_eq : (p : ℚ) ^ (k - 1 - i) = (p : ℚ) ^ (m - 2) := by
        congr 1
        omega
      rw [h_pow_eq]
      have h_mul : ((k.choose i : ℚ) * (p : ℚ) ^ (m - 2) / (m : ℚ)) = (k.choose i : ℚ) * ((p : ℚ) ^ (m - 2) / (m : ℚ)) := by ring
      rw [h_mul]
      apply isPIntegral_mul hp
      · exact isPIntegral_natCast p hp (k.choose i)
      · exact p_pow_sub_two_div_m_p_integral p hp hp3 m hm

lemma p_dvd_den_of_isPIntegral {p : ℕ} (hp : Nat.Prime p) (k : ℕ)
    (h_int : IsPIntegral p (bernoulli k + (1 : ℚ) / (p : ℚ))) : p ∣ (bernoulli k).den := by
  by_contra h_not_dvd
  have h_int_bernoulli : IsPIntegral p (bernoulli k) := h_not_dvd
  have h_diff : IsPIntegral p (bernoulli k + (1 : ℚ) / (p : ℚ) - bernoulli k) := by
    apply isPIntegral_sub hp h_int h_int_bernoulli
  have h_simpl : bernoulli k + (1 : ℚ) / (p : ℚ) - bernoulli k = (1 : ℚ) / (p : ℚ) := by ring
  rw [h_simpl] at h_diff
  have h_den : ((1 : ℚ) / (p : ℚ)).den = p := by
    have hp_pos : p > 0 := hp.pos
    have h_inv : (1 : ℚ) / (p : ℚ) = (p : ℚ) ^-1 := by ring
    rw [h_inv]
    exact Rat.inv_natCast_den_of_pos hp_pos
  unfold IsPIntegral at h_diff
  rw [h_den] at h_diff
  have h_dvd_self : p ∣ p := dvd_rfl
  contradiction

theorem A309132_conjecture_carmichael : ∀ (n : ℕ),
  (is_composite n ∧ Squarefree (a n)) ↔ is_carmichael_number n :=
by
  intro n
  by_cases hn : n ≤ 1
  · exact le_one_case n hn
  · by_cases hp : Nat.Prime n
    · exact prime_case n hp
    · by_cases h_even : Even n
      · -- even composite
        have : n > 1 := by omega
        have h_comp : is_composite n := ⟨hp, this⟩
        constructor
        · rintro ⟨_, h_sq⟩
          have h_gt2 : n > 2 := by
            have h_ne2 : n ≠ 2 := by
              intro h_eq
              subst h_eq
              exact hp Nat.prime_two
            omega
          have h_B : bernoulli (n - 1) = 0 := bernoulli_of_even n h_even h_gt2
          have h_a : a n = n ^ 2 := a_of_bernoulli_zero n (by omega) h_B
          rw [h_a] at h_sq
          have h_not_sq := not_squarefree_sq n (by omega)
          contradiction
        · intro h_carm
          have h_not_carm := even_not_carmichael n h_even
          contradiction
      · -- odd composite
        have hn_gt1 : n > 1 := by omega
        have h_comp : is_composite n := ⟨hp, hn_gt1⟩
        have h_odd : Odd n := by
          by_contra h_e
          exact h_even h_e
        rw [carmichael_iff_carmichael_dvd hn_gt1 hp]
        constructor
        · rintro ⟨_, h_sq⟩
          -- We have h_sq : Squarefree (a n)
          -- We want to show Carmichael n ∣ n - 1
          -- We use carmichael_dvd_of_factors_dvd
          apply carmichael_dvd_of_factors_dvd hn_gt1
          · -- Prove Squarefree n
            by_contra h_not_sf
            obtain ⟨p, hp_prime, hp2_dvd⟩ := prime_sq_dvd_of_not_squarefree h_not_sf hn_gt1
            have hp_n : p ∣ n := by
              have : p ∣ p^2 := dvd_sq p
              exact dvd_trans this hp2_dvd
            have h_not_p2_an : ¬ p^2 ∣ a n := by
              intro hp2_an
              have h_p2 : p * p ∣ a n := by rwa [← sq] at hp2_an
              have h_unit := h_sq p h_p2
              have : p = 1 := Nat.isUnit_iff.mp h_unit
              have : p > 1 := hp_prime.one_lt
              omega
            by_cases hp_den : p ∣ (bernoulli (n - 1)).den
            · have h_not_p2_an_int : ¬ (p : ℤ)^2 ∣ (a n : ℤ) := by
                intro h_dvd
                have : p^2 ∣ a n := by exact_mod_cast h_dvd
                exact h_not_p2_an this
              have hp2_den : p^2 ∣ (bernoulli (n - 1)).den :=
                p_sq_dvd_bernoulli_den_of_not_dvd_a n (by omega) hp_prime hp2_dvd hp_den h_not_p2_an_int
              have h_not_p2_den := not_psq_dvd_den_of_p_mul_integral hp_prime (bernoulli (n - 1))
                (p_bernoulli_p_integral p hp_prime (n - 1))
              exact h_not_p2_den hp2_den
            · have hp2_an : p^2 ∣ a n :=
                p_sq_dvd_a_of_not_dvd_bernoulli_den n (by omega) hp_prime hp_n hp_den
              exact h_not_p2_an hp2_an
          · -- Prove ∀ p : ℕ, Prime p → p ∣ n → (p - 1) ∣ n - 1
            intro q hq hq_n
            have h_pq := prime_dvd_bernoulli_den_of_squarefree (by omega : n ≠ 0) h_sq hq hq_n
            by_contra h_not_dvd_nm1
            have hq3 : q ≥ 3 := by
              have : q ≠ 2 := by
                intro h_eq
                subst h_eq
                have : Even n := by
                  use n / 2
                  omega
                exact h_even this
              have : q > 1 := hq.one_lt
              omega
            have h_int_B := bernoulli_p_integral_of_not_dvd q hq hq3 (n - 1) (by omega) h_not_dvd_nm1
              (fun i hi ↦ p_bernoulli_p_integral q hq i)
            exact h_int_B h_pq
      · intro h_carm_dvd
        refine ⟨h_comp, ?_⟩
        have h_carm : is_carmichael_number n := by
          rwa [carmichael_iff_carmichael_dvd hn_gt1 hp]
        have h_sf_n := carmichael_squarefree n h_carm
        have h_n_dvd_den : n ∣ (bernoulli (n - 1)).den := by
          apply dvd_of_squarefree_dvd h_sf_n
          intro p hp hp_n
          have hp2 : p ≠ 2 := by
            intro h_eq
            subst h_eq
            have h_even_n : Even n := by
              use n / 2
              omega
            exact h_even h_even_n
          have h_carm_p_dvd : ArithmeticFunction.Carmichael p ∣ ArithmeticFunction.Carmichael n := by
            exact ArithmeticFunction.carmichael_dvd hp_n
          have h_carm_p_eq : ArithmeticFunction.Carmichael p = p - 1 := carmichael_prime_odd hp hp2
          rw [h_carm_p_eq] at h_carm_p_dvd
          have h_p_sub_one_dvd_nm1 : (p - 1) ∣ n - 1 := dvd_trans h_carm_p_dvd h_carm_dvd
          have h_int : IsPIntegral p (bernoulli (n - 1) + (1 : ℚ) / (p : ℚ)) := by
            rw [bernoulli_identity_divided_add_one_div_p p (n - 1) hp (by omega)]
            apply isPIntegral_sub hp
            · have h_sum_neg_one : ((∑ x ∈ range p, x ^ (n - 1) : ℕ) : ZMod p) = -1 := by
                have h_cast : ((∑ x ∈ range p, x ^ (n - 1) : ℕ) : ZMod p) = ∑ x ∈ range p, (x : ZMod p) ^ (n - 1) := by
                  push_cast
                  rfl
                rw [h_cast]
                have h_univ : (∑ x ∈ range p, (x : ZMod p) ^ (n - 1)) = ∑ x : ZMod p, x ^ (n - 1) := by
                  have h_fin := Fin.sum_univ_eq_sum_range (n := p) (fun (x : ℕ) ↦ (x : ZMod p) ^ (n - 1))
                  rw [← h_fin]
                  change (∑ i : Fin p, ((i : ℕ) : ZMod p) ^ (n - 1)) = ∑ x : ZMod p, x ^ (n - 1)
                  congr 1
                  ext i
                  congr 1
                  rcases p with _ | p_pred
                  · contradiction
                  · apply Fin.ext
                    exact Nat.mod_eq_of_lt i.is_lt
                rw [h_univ]
                haveI : Fact p.Prime := ⟨hp⟩
                rw [sum_pow_zmod (p := p) (i := n - 1) (hi := by omega)]
                rw [if_pos h_p_sub_one_dvd_nm1]
              have h_dvd : p ∣ (∑ x ∈ range p, x ^ (n - 1) : ℕ) + 1 := by
                rw [← ZMod.natCast_eq_zero_iff]
                push_cast
                rw [h_sum_neg_one]
                ring
              rcases h_dvd with ⟨M, hM⟩
              have h_eq_M : (((∑ x ∈ range p, (x : ℚ) ^ (n - 1)) + 1) / (p : ℚ)) = (M : ℚ) := by
                have h_cast2 : (∑ x ∈ range p, (x : ℚ) ^ (n - 1)) + 1 = (((∑ x ∈ range p, x ^ (n - 1) : ℕ) + 1 : ℕ) : ℚ) := by
                  push_cast
                  rfl
                rw [h_cast2]
                rw [hM]
                push_cast
                have : (p : ℚ) ≠ 0 := by
                  have : p ≠ 0 := hp.ne_zero
                  positivity
                exact mul_div_cancel_left₀ _ this
              rw [h_eq_M]
              exact isPIntegral_natCast p hp M
            · apply isPIntegral_sum hp
              intro i hi
              rw [Finset.mem_range] at hi
              apply isPIntegral_mul hp
              · exact p_bernoulli_p_integral p hp i
              · set m := n - 1 + 1 - i
                have hm : m ≥ 2 := by omega
                have h_pow_eq : (p : ℚ) ^ (n - 1 - 1 - i) = (p : ℚ) ^ (m - 2) := by
                  congr 1
                  omega
                rw [h_pow_eq]
                have h_mul : (((n - 1).choose i : ℚ) * (p : ℚ) ^ (m - 2) / (m : ℚ)) = ((n - 1).choose i : ℚ) * ((p : ℚ) ^ (m - 2) / (m : ℚ)) := by ring
                rw [h_mul]
                apply isPIntegral_mul hp
                · exact isPIntegral_natCast p hp ((n - 1).choose i)
                · have hp3 : p ≥ 3 := by
                    have : p > 1 := hp.one_lt
                    omega
                  exact p_pow_sub_two_div_m_p_integral p hp hp3 m hm
          exact p_dvd_den_of_isPIntegral hp (n - 1) h_int
          have h_an_dvd_n := a_dvd_n_of_n_dvd_bernoulli_den n (by omega) h_n_dvd_den
          exact squarefree_of_dvd h_sf_n h_an_dvd_n





