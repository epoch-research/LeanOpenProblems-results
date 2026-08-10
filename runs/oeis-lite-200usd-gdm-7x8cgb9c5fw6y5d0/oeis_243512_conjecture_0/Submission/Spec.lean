import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open Nat ArithmeticFunction Rat Finset
open scoped BigOperators

/--
A243473(i) is the difference between the numerator $p$ and the denominator $q$
when the per-unit sum-of-divisors $\sigma_1(i)/i$ is written in its lowest terms $p/q$.
$$ \mathrm{A243473}(i) = \mathrm{num} \left( \frac{\sigma_1(i)}{i} \right) - \mathrm{den} \left( \frac{\sigma_1(i)}{i} \right) $$
-/
def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    -- r.num is Int, r.den is Nat. The subtraction is performed in Int, and then converted to Nat.
    (r.num - (r.den : ℤ)).toNat

/--
A243512: Least index $i$ for which $\mathrm{A243473}(i)=n$, or $0$ if no such index exists.
$$ a(n) = \min \{ i \in \mathbb{N} \mid i > 0 \land \mathrm{A243473}(i) = n \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {i : ℕ | 0 < i ∧ A243473_val i = n}

theorem a_ne_zero_iff (n : ℕ) : a n ≠ 0 ↔ ∃ i, 0 < i ∧ A243473_val i = n := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h_empty : {i : ℕ | 0 < i ∧ A243473_val i = n} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hc x hx.1 hx.2
    have h_inf : sInf {i : ℕ | 0 < i ∧ A243473_val i = n} = 0 := by
      rw [h_empty]
      exact Nat.sInf_empty
    exact h h_inf
  · rintro ⟨i, hi⟩
    have h_nonempty : {x : ℕ | 0 < x ∧ A243473_val x = n}.Nonempty := ⟨i, hi⟩
    have h_mem := Nat.sInf_mem h_nonempty
    simp only [Set.mem_setOf_eq] at h_mem
    exact _root_.ne_of_gt h_mem.1

theorem val_1 : A243473_val 1 = 0 := by
  unfold A243473_val
  simp

theorem val_2 : A243473_val 2 = 1 := by
  unfold A243473_val
  have h_sig : (sigma 1 : ArithmeticFunction ℕ) 2 = 3 := rfl
  simp only [h_sig]
  norm_num

theorem val_120 : A243473_val 120 = 2 := by
  unfold A243473_val
  have h_sig : (sigma 1 : ArithmeticFunction ℕ) 120 = 360 := rfl
  simp only [h_sig]
  norm_num
  rfl

theorem sigma_prime_sq {p : ℕ} (hp : p.Prime) : sigma 1 (p ^ 2) = 1 + p + p ^ 2 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

theorem val_prime_sq {p : ℕ} (hp : p.Prime) : A243473_val (p^2) = p + 1 := by
  have hp2 : p^2 ≠ 0 := by
    have : p ≥ 2 := hp.two_le
    positivity
  unfold A243473_val
  simp only [hp2, ↓reduceIte]
  have h1 : Nat.Coprime (1 + p + p^2) p := by
    have h_eq : 1 + p + p^2 = 1 + (1 + p) * p := by ring
    rw [h_eq]
    rw [Nat.coprime_comm]
    rw [Nat.coprime_add_mul_right_right]
    exact Nat.coprime_one_right p

  have h_cop : Nat.Coprime (1 + p + p^2) (p^2) := Nat.Coprime.pow_right 2 h1

  have hb0 : 0 < (p^2 : ℤ) := by
    have : p ≥ 2 := hp.two_le
    positivity

  have h_cop_z : Nat.Coprime (Int.natAbs (1 + p + p^2 : ℤ)) (Int.natAbs (p^2 : ℤ)) := by
    exact h_cop

  have h_num := Rat.num_div_eq_of_coprime hb0 h_cop_z
  have h_den := Rat.den_div_eq_of_coprime hb0 h_cop_z

  rw [sigma_prime_sq hp]
  have h_div_eq : ((1 + p + p^2 : ℕ) : Rat) / ((p^2 : ℕ) : Rat) = ((1 + p + p^2 : ℤ) : Rat) / ((p^2 : ℤ) : Rat) := by
    push_cast
    rfl
  rw [h_div_eq]

  have h_num' : (((1 + p + p ^ 2 : ℤ) : Rat) / ((p ^ 2 : ℤ) : Rat)).num = 1 + p + p ^ 2 := h_num
  have h_den' : (((1 + p + p ^ 2 : ℤ) : Rat) / ((p ^ 2 : ℤ) : Rat)).den = p ^ 2 := by
    have h_den_z : ((((1 + p + p ^ 2 : ℤ) : Rat) / ((p ^ 2 : ℤ) : Rat)).den : ℤ) = p ^ 2 := h_den
    exact_mod_cast h_den_z

  rw [h_num', h_den']
  have h_sub : (1 + p + p^2 : ℤ) - (p^2 : ℤ) = p + 1 := by ring
  push_cast
  rw [h_sub]
  rfl

theorem val_prime_family_2 {p : ℕ} (hp : p.Prime) (hp_gt : p > 3) : A243473_val (2 * p) = (p + 3) / 2 := by
  have hp2 : 2 * p ≠ 0 := by
    have : p ≥ 2 := hp.two_le
    positivity
  unfold A243473_val
  simp only [hp2, ↓reduceIte]
  have h_sig : sigma 1 (2 * p) = 3 * (p + 1) := by
    have h_cop : Nat.Coprime 2 p := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_of_pos_of_lt (by decide) (by omega))
    rw [isMultiplicative_sigma.map_mul_of_coprime h_cop]
    have h_sig2 : sigma 1 2 = 3 := rfl
    have h_sigp : sigma 1 p = p + 1 := by
      have h_pow := sigma_one_apply_prime_pow hp (i := 1)
      simp only [pow_one] at h_pow
      rw [h_pow]
      simp [Finset.sum_range_succ]
      ring
    rw [h_sig2, h_sigp]

  have h_odd : p % 2 = 1 := by
    rw [Nat.Prime.mod_two_eq_one_iff_ne_two hp]
    omega

  have h_even_p1 : 2 ∣ p + 1 := by
    omega

  obtain ⟨k, hk⟩ := h_even_p1

  have h_cop : Nat.Coprime (3 * k) p := by
    have h3 : Nat.Coprime 3 p := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_of_pos_of_lt (by decide) (by omega))
    have hk_cop : Nat.Coprime k p := by
      rw [Nat.coprime_comm]
      have h_gcd : Nat.Coprime (2 * k) p := by
        rw [← hk]
        have : Nat.Coprime (p + 1) p := by
          rw [Nat.coprime_comm]
          exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right p)
        exact this
      exact (Nat.coprime_mul_iff_left.mp h_gcd |>.2).symm
    exact Nat.Coprime.mul_left h3 hk_cop

  have hb0 : 0 < (p : ℤ) := by
    have : p ≥ 2 := hp.two_le
    positivity

  have h_cop_z : Nat.Coprime (Int.natAbs (3 * k : ℤ)) (Int.natAbs (p : ℤ)) := h_cop

  have h_num := Rat.num_div_eq_of_coprime hb0 h_cop_z
  have h_den := Rat.den_div_eq_of_coprime hb0 h_cop_z

  rw [h_sig]
  have h_div_eq : (((3 * (p + 1) : ℕ) : Rat) / ((2 * p : ℕ) : Rat)) = ((3 * k : ℤ) : Rat) / (p : Rat) := by
    have hk_rat : (p : Rat) + 1 = 2 * k := by exact_mod_cast hk
    push_cast
    have hp_pos : (p : Rat) ≠ 0 := by positivity
    field_simp
    rw [hk_rat]
  rw [h_div_eq]

  have h_num' : (((3 * k : ℤ) : Rat) / (p : Rat)).num = 3 * k := h_num
  have h_den' : (((3 * k : ℤ) : Rat) / (p : Rat)).den = p := by
    have h_den_z : ((((3 * k : ℤ) : Rat) / (p : Rat)).den : ℤ) = p := h_den
    exact_mod_cast h_den_z

  rw [h_num', h_den']
  have h_sub : (3 * k : ℤ) - p = (p + 3) / 2 := by omega
  rw [h_sub]
  rfl

theorem val_prime_family_6 {p : ℕ} (hp : p.Prime) (hp_gt : p > 3) : A243473_val (6 * p) = p + 2 := by
  have hp6 : 6 * p ≠ 0 := by
    have : p ≥ 2 := hp.two_le
    positivity
  unfold A243473_val
  simp only [hp6, ↓reduceIte]
  have h_sig : sigma 1 (6 * p) = 12 * (p + 1) := by
    have h_cop : Nat.Coprime 6 p := by
      have h2 : Nat.Coprime 2 p := by
        rw [Nat.coprime_comm]
        exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_of_pos_of_lt (by decide) (by omega))
      have h3 : Nat.Coprime 3 p := by
        rw [Nat.coprime_comm]
        exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_of_pos_of_lt (by decide) (by omega))
      exact Nat.Coprime.mul_left h2 h3
    rw [isMultiplicative_sigma.map_mul_of_coprime h_cop]
    have h_sig6 : sigma 1 6 = 12 := rfl
    have h_sigp : sigma 1 p = p + 1 := by
      have h_pow := sigma_one_apply_prime_pow hp (i := 1)
      simp only [pow_one] at h_pow
      rw [h_pow]
      simp [Finset.sum_range_succ]
      ring
    rw [h_sig6, h_sigp]

  have h_cop : Nat.Coprime (2 * (p + 1)) p := by
    have h2 : Nat.Coprime 2 p := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_of_pos_of_lt (by decide) (by omega))
    have h_cop_p1 : Nat.Coprime (p + 1) p := by
      rw [Nat.coprime_comm]
      have : Nat.Coprime p (p + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right p)
      exact this
    exact Nat.Coprime.mul_left h2 h_cop_p1

  have hb0 : 0 < (p : ℤ) := by
    have : p ≥ 2 := hp.two_le
    positivity

  have h_cop_z : Nat.Coprime (Int.natAbs (2 * (p + 1) : ℤ)) (Int.natAbs (p : ℤ)) := h_cop

  have h_num := Rat.num_div_eq_of_coprime hb0 h_cop_z
  have h_den := Rat.den_div_eq_of_coprime hb0 h_cop_z

  rw [h_sig]
  have h_div_eq : (((12 * (p + 1) : ℕ) : Rat) / ((6 * p : ℕ) : Rat)) = ((2 * (p + 1) : ℤ) : Rat) / (p : Rat) := by
    push_cast
    have hp_pos : (p : Rat) ≠ 0 := by positivity
    field_simp
    ring
  rw [h_div_eq]

  have h_num' : (((2 * (p + 1) : ℤ) : Rat) / (p : Rat)).num = 2 * (p + 1) := h_num
  have h_den' : (((2 * (p + 1) : ℤ) : Rat) / (p : Rat)).den = p := by
    have h_den_z : ((((2 * (p + 1) : ℤ) : Rat) / (p : Rat)).den : ℤ) = p := h_den
    exact_mod_cast h_den_z

  rw [h_num', h_den']
  have h_sub : (2 * (p + 1) : ℤ) - p = p + 2 := by ring
  rw [h_sub]
  rfl


theorem sigma_mul_ge (g q : ℕ) (hg : g ≥ 1) (_hq : q ≥ 1) :
    g * (sigma 1 : ArithmeticFunction ℕ) q ≤ (sigma 1 : ArithmeticFunction ℕ) (g * q) := by
  have hg0 : g ≠ 0 := by omega
  rw [sigma_apply, sigma_apply]
  simp only [pow_one]
  -- Rewrite g * ∑ as ∑ (g * d)
  rw [mul_sum]
  -- Let's define the embedding f : d ↦ g * d
  let f : ℕ ↪ ℕ := ⟨fun d => g * d, fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg0) h⟩
  -- Show that ∑ d ∈ q.divisors, g * d is ∑ x ∈ q.divisors.map f, x
  have h_sum : (∑ d ∈ q.divisors, g * d) = ∑ x ∈ q.divisors.map f, x := by
    rw [sum_map]
    rfl
  rw [h_sum]
  -- Show that q.divisors.map f ⊆ (g * q).divisors
  have h_sub : q.divisors.map f ⊆ (g * q).divisors := by
    intro x hx
    rcases mem_map.mp hx with ⟨d, hd, rfl⟩
    rw [mem_divisors] at hd
    rcases hd with ⟨hd_div, hd0⟩
    rw [mem_divisors]
    refine ⟨?_, ?_⟩
    · -- g * d ∣ g * q
      exact mul_dvd_mul_left g hd_div
    · -- g * q ≠ 0
      exact mul_ne_zero hg0 hd0
  -- Now use Finset.sum_le_sum_of_subset
  exact sum_le_sum_of_subset h_sub


theorem sigma_mul_ge_plus_one (g q : ℕ) (hg : g ≥ 2) (hq : q ≥ 1) :
    g * (sigma 1 : ArithmeticFunction ℕ) q + 1 ≤ (sigma 1 : ArithmeticFunction ℕ) (g * q) := by
  have hg0 : g ≠ 0 := by omega
  rw [sigma_apply, sigma_apply]
  simp only [pow_one]
  rw [mul_sum]
  let f : ℕ ↪ ℕ := ⟨fun d => g * d, fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg0) h⟩
  have h_sum : (∑ d ∈ q.divisors, g * d) = ∑ x ∈ q.divisors.map f, x := by
    rw [sum_map]
    rfl
  rw [h_sum]
  have h_sub : q.divisors.map f ⊆ (g * q).divisors := by
    intro x hx
    rcases mem_map.mp hx with ⟨d, hd, rfl⟩
    rw [mem_divisors] at hd
    rcases hd with ⟨hd_div, hd0⟩
    rw [mem_divisors]
    refine ⟨?_, ?_⟩
    · exact mul_dvd_mul_left g hd_div
    · exact mul_ne_zero hg0 hd0
  have h_one_mem : 1 ∈ (g * q).divisors := by
    rw [mem_divisors]
    refine ⟨one_dvd (g * q), ?_⟩
    exact mul_ne_zero hg0 (by omega)
  have h_one_not_mem : 1 ∉ q.divisors.map f := by
    intro hx
    rcases mem_map.mp hx with ⟨d, hd, h_eq⟩
    rw [mem_divisors] at hd
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
    have hd_ge1 : 1 ≤ d := hd_pos
    have : g * d ≥ 2 := by
      calc g * d ≥ 2 * d := Nat.mul_le_mul_right d hg
      _ ≥ 2 * 1 := Nat.mul_le_mul_left 2 hd_ge1
      _ = 2 := rfl
    have h_eq' : g * d = 1 := h_eq
    rw [h_eq'] at this
    omega
  have h_sub_insert : insert 1 (q.divisors.map f) ⊆ (g * q).divisors := by
    rw [insert_subset_iff]
    exact ⟨h_one_mem, h_sub⟩
  have h_sum_insert : (∑ x ∈ insert 1 (q.divisors.map f), x) = (∑ x ∈ q.divisors.map f, x) + 1 := by
    rw [sum_insert h_one_not_mem]
    omega
  have h_le : (∑ x ∈ insert 1 (q.divisors.map f), x) ≤ (∑ x ∈ (g * q).divisors, x) := sum_le_sum_of_subset h_sub_insert
  rw [h_sum_insert] at h_le
  exact h_le


theorem sigma_mul_ge_sigma_mul_q (g q : ℕ) (hg : g ≥ 1) (hq : q ≥ 1) :
    (sigma 1 : ArithmeticFunction ℕ) g * q ≤ (sigma 1 : ArithmeticFunction ℕ) (g * q) := by
  have h_eq : g * q = q * g := mul_comm g q
  rw [h_eq]
  rw [mul_comm]
  exact sigma_mul_ge q g hq hg


theorem q_mul_sigma_sub_le_1680_mul_g (g q : ℕ) (hg : g ≥ 1) (hq : q ≥ 1) 
    (h_eq : (sigma 1 : ArithmeticFunction ℕ) (g * q) = g * (q + 1680)) :
    q * ((sigma 1 : ArithmeticFunction ℕ) g - g) ≤ 1680 * g := by
  have h1 : (sigma 1 : ArithmeticFunction ℕ) g * q ≤ (sigma 1 : ArithmeticFunction ℕ) (g * q) := sigma_mul_ge_sigma_mul_q g q hg hq
  rw [h_eq] at h1
  have hg_le : g ≤ (sigma 1 : ArithmeticFunction ℕ) g := by
    change g ≤ (sigma 1 g : ℕ)
    rw [sigma_apply]
    simp only [pow_one]
    have h_div_self : g ∈ g.divisors := by
      rw [mem_divisors]
      refine ⟨by simp, by omega⟩
    have h_single := Finset.single_le_sum (fun d _ => Nat.zero_le d) h_div_self
    exact h_single
  have h2 : (sigma 1 : ArithmeticFunction ℕ) g * q = g * q + ((sigma 1 : ArithmeticFunction ℕ) g - g) * q := by
    rw [← Nat.add_mul]
    rw [Nat.add_comm]
    rw [Nat.sub_add_cancel hg_le]
  rw [h2] at h1
  have h3 : g * (q + 1680) = g * q + g * 1680 := by ring
  rw [h3] at h1
  have h4 : ((sigma 1 : ArithmeticFunction ℕ) g - g) * q ≤ g * 1680 := by omega
  rw [mul_comm] at h4
  have h5 : g * 1680 = 1680 * g := mul_comm g 1680
  rw [h5] at h4
  exact h4


theorem sigma_sub_ge_div_minFac (g : ℕ) (hg : g ≥ 2) :
    (sigma 1 : ArithmeticFunction ℕ) g - g ≥ g / g.minFac := by
  rw [sigma_apply]
  simp only [pow_one]
  have hg0 : g ≠ 0 := by omega
  have hg1 : g ≠ 1 := by omega
  have h_prime := Nat.minFac_prime hg1
  have h_min_ge_2 := h_prime.two_le
  have h_div_minFac : g.minFac ∣ g := Nat.minFac_dvd g
  have h_div_q : g / g.minFac ∣ g := Nat.div_dvd_of_dvd h_div_minFac
  have h_proper : g / g.minFac < g := by
    apply Nat.div_lt_self (by omega)
    exact h_min_ge_2
  have h_mem : g / g.minFac ∈ g.divisors := by
    rw [mem_divisors]
    exact ⟨h_div_q, hg0⟩
  have h_sum : (∑ d ∈ g.divisors, d) = (∑ d ∈ g.divisors.erase g, d) + g := by
    have h_g_mem : g ∈ g.divisors := by
      rw [mem_divisors]
      exact ⟨dvd_rfl, hg0⟩
    rw [← Finset.sum_erase_add _ _ h_g_mem]
  rw [h_sum]
  have h_sub_eq : (∑ d ∈ g.divisors.erase g, d) + g - g = ∑ d ∈ g.divisors.erase g, d := by omega
  rw [h_sub_eq]
  have h_mem_erase : g / g.minFac ∈ g.divisors.erase g := by
    rw [mem_erase]
    exact ⟨_root_.ne_of_lt h_proper, h_mem⟩
  exact Finset.single_le_sum (fun d _ => Nat.zero_le d) h_mem_erase


theorem q_le_1680_mul_minFac (g q : ℕ) (hg : g ≥ 2) (hq : q ≥ 1) 
    (h_eq : (sigma 1 : ArithmeticFunction ℕ) (g * q) = g * (q + 1680)) :
    q ≤ 1680 * g.minFac := by
  have h_le := q_mul_sigma_sub_le_1680_mul_g g q (by omega) hq h_eq
  have h_sub_ge := sigma_sub_ge_div_minFac g hg
  have h_mul_le : q * (g / g.minFac) ≤ q * ((sigma 1 : ArithmeticFunction ℕ) g - g) := Nat.mul_le_mul_left q h_sub_ge
  have h_trans : q * (g / g.minFac) ≤ 1680 * g := by omega
  have hg_eq : g = (g / g.minFac) * g.minFac := by
    rw [Nat.div_mul_cancel (Nat.minFac_dvd g)]
  have h_rhs : 1680 * g = (1680 * g.minFac) * (g / g.minFac) := by
    conv_lhs => rw [hg_eq]
    ring
  rw [h_rhs] at h_trans
  have h_div_pos : g / g.minFac > 0 := by
    have hg0 : g ≠ 0 := by omega
    have h_div_dvd : g.minFac ∣ g := Nat.minFac_dvd g
    have h_eq' := (Nat.mul_div_cancel' h_div_dvd).symm
    by_contra hc
    have hc' : g / g.minFac = 0 := by
      by_contra h_nz
      have : g / g.minFac > 0 := Nat.pos_of_ne_zero h_nz
      exact hc this
    rw [hc', Nat.mul_zero] at h_eq'
    exact hg0 h_eq'
  exact Nat.le_of_mul_le_mul_right h_trans h_div_pos



theorem prime_coprime_1680_ge11 (p : ℕ) (hp : p.Prime) (h_cop : p.Coprime 1680) : p ≥ 11 := by
  by_contra hc
  have h_lt : p < 11 := by omega
  interval_cases p
  · revert hp; decide
  · revert hp; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert hp; decide
  · revert h_cop; decide
  · revert hp; decide
  · revert h_cop; decide
  · revert hp; decide
  · revert hp; decide
  · revert hp; decide

theorem le_11 (k : ℕ) (h : 1 + 11 + 11 * 11 + 11 * k ≤ 1680) : k ≤ 140 := by omega
theorem gt_11 (k : ℕ) (h : 11 * 11 < 11 * k) : k > 11 := by omega
theorem le_13 (k : ℕ) (h : 1 + 13 + 13 * 13 + 13 * k ≤ 1680) : k ≤ 115 := by omega
theorem gt_13 (k : ℕ) (h : 13 * 13 < 13 * k) : k > 13 := by omega
theorem le_17 (k : ℕ) (h : 1 + 17 + 17 * 17 + 17 * k ≤ 1680) : k ≤ 80 := by omega
theorem gt_17 (k : ℕ) (h : 17 * 17 < 17 * k) : k > 17 := by omega
theorem le_19 (k : ℕ) (h : 1 + 19 + 19 * 19 + 19 * k ≤ 1680) : k ≤ 68 := by omega
theorem gt_19 (k : ℕ) (h : 19 * 19 < 19 * k) : k > 19 := by omega
theorem le_23 (k : ℕ) (h : 1 + 23 + 23 * 23 + 23 * k ≤ 1680) : k ≤ 49 := by omega
theorem gt_23 (k : ℕ) (h : 23 * 23 < 23 * k) : k > 23 := by omega
theorem le_prm_11 (r : ℕ) (h : 1 + 11 + r + 11 * 11 + 11 * r ≤ 1680) : r ≤ 128 := by omega
theorem gt_prm_11 (r : ℕ) (h : 11 < r) : r > 11 := by omega
theorem le_prm_13 (r : ℕ) (h : 1 + 13 + r + 13 * 13 + 13 * r ≤ 1680) : r ≤ 106 := by omega
theorem gt_prm_13 (r : ℕ) (h : 13 < r) : r > 13 := by omega
theorem le_prm_17 (r : ℕ) (h : 1 + 17 + r + 17 * 17 + 17 * r ≤ 1680) : r ≤ 76 := by omega
theorem gt_prm_17 (r : ℕ) (h : 17 < r) : r > 17 := by omega
theorem le_prm_19 (r : ℕ) (h : 1 + 19 + r + 19 * 19 + 19 * r ≤ 1680) : r ≤ 64 := by omega
theorem gt_prm_19 (r : ℕ) (h : 19 < r) : r > 19 := by omega
theorem le_prm_23 (r : ℕ) (h : 1 + 23 + r + 23 * 23 + 23 * r ≤ 1680) : r ≤ 46 := by omega
theorem gt_prm_23 (r : ℕ) (h : 23 < r) : r > 23 := by omega
theorem le_pair_11_13 (k : ℕ) (h : 1 + 11 + 13 + 11 * 13 + 13 * k ≤ 1680) : k ≤ 116 := by omega
theorem le_pair_11_17 (k : ℕ) (h : 1 + 11 + 17 + 11 * 17 + 17 * k ≤ 1680) : k ≤ 86 := by omega
theorem le_pair_13_17 (k : ℕ) (h : 1 + 13 + 17 + 13 * 17 + 17 * k ≤ 1680) : k ≤ 84 := by omega
theorem le_pair_11_19 (k : ℕ) (h : 1 + 11 + 19 + 11 * 19 + 19 * k ≤ 1680) : k ≤ 75 := by omega
theorem le_pair_13_19 (k : ℕ) (h : 1 + 13 + 19 + 13 * 19 + 19 * k ≤ 1680) : k ≤ 73 := by omega
theorem le_pair_17_19 (k : ℕ) (h : 1 + 17 + 19 + 17 * 19 + 19 * k ≤ 1680) : k ≤ 69 := by omega
theorem le_pair_11_23 (k : ℕ) (h : 1 + 11 + 23 + 11 * 23 + 23 * k ≤ 1680) : k ≤ 60 := by omega
theorem le_pair_13_23 (k : ℕ) (h : 1 + 13 + 23 + 13 * 23 + 23 * k ≤ 1680) : k ≤ 58 := by omega
theorem le_pair_17_23 (k : ℕ) (h : 1 + 17 + 23 + 17 * 23 + 23 * k ≤ 1680) : k ≤ 54 := by omega
theorem le_pair_19_23 (k : ℕ) (h : 1 + 19 + 23 + 19 * 23 + 23 * k ≤ 1680) : k ≤ 52 := by omega
theorem le_pair_11_29 (k : ℕ) (h : 1 + 11 + 29 + 11 * 29 + 29 * k ≤ 1680) : k ≤ 45 := by omega
theorem le_pair_13_29 (k : ℕ) (h : 1 + 13 + 29 + 13 * 29 + 29 * k ≤ 1680) : k ≤ 43 := by omega
theorem le_pair_17_29 (k : ℕ) (h : 1 + 17 + 29 + 17 * 29 + 29 * k ≤ 1680) : k ≤ 39 := by omega
theorem le_pair_19_29 (k : ℕ) (h : 1 + 19 + 29 + 19 * 29 + 29 * k ≤ 1680) : k ≤ 37 := by omega
theorem le_pair_23_29 (k : ℕ) (h : 1 + 23 + 29 + 23 * 29 + 29 * k ≤ 1680) : k ≤ 33 := by omega
theorem le_pair_11_31 (k : ℕ) (h : 1 + 11 + 31 + 11 * 31 + 31 * k ≤ 1680) : k ≤ 41 := by omega
theorem le_pair_13_31 (k : ℕ) (h : 1 + 13 + 31 + 13 * 31 + 31 * k ≤ 1680) : k ≤ 39 := by omega
theorem le_pair_17_31 (k : ℕ) (h : 1 + 17 + 31 + 17 * 31 + 31 * k ≤ 1680) : k ≤ 35 := by omega
theorem le_pair_19_31 (k : ℕ) (h : 1 + 19 + 31 + 19 * 31 + 31 * k ≤ 1680) : k ≤ 33 := by omega
theorem le_pair_23_31 (k : ℕ) (h : 1 + 23 + 31 + 23 * 31 + 31 * k ≤ 1680) : k ≤ 29 := by omega
theorem le_pair_29_31 (k : ℕ) (h : 1 + 29 + 31 + 29 * 31 + 31 * k ≤ 1680) : k ≤ 23 := by omega
theorem le_pair_11_37 (k : ℕ) (h : 1 + 11 + 37 + 11 * 37 + 37 * k ≤ 1680) : k ≤ 33 := by omega
theorem le_pair_13_37 (k : ℕ) (h : 1 + 13 + 37 + 13 * 37 + 37 * k ≤ 1680) : k ≤ 31 := by omega
theorem le_pair_17_37 (k : ℕ) (h : 1 + 17 + 37 + 17 * 37 + 37 * k ≤ 1680) : k ≤ 26 := by omega
theorem le_pair_19_37 (k : ℕ) (h : 1 + 19 + 37 + 19 * 37 + 37 * k ≤ 1680) : k ≤ 24 := by omega
theorem le_pair_23_37 (k : ℕ) (h : 1 + 23 + 37 + 23 * 37 + 37 * k ≤ 1680) : k ≤ 20 := by omega
theorem le_pair_29_37 (k : ℕ) (h : 1 + 29 + 37 + 29 * 37 + 37 * k ≤ 1680) : k ≤ 14 := by omega
theorem le_pair_31_37 (k : ℕ) (h : 1 + 31 + 37 + 31 * 37 + 37 * k ≤ 1680) : k ≤ 12 := by omega
theorem sec2_dec_val_11_13 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 13)) - 11 * (11 * 13) ≠ 1680 := by decide
theorem sec2_dec_val_11_17 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 17)) - 11 * (11 * 17) ≠ 1680 := by decide
theorem sec2_dec_val_11_19 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 19)) - 11 * (11 * 19) ≠ 1680 := by decide
theorem sec2_dec_val_11_23 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 23)) - 11 * (11 * 23) ≠ 1680 := by decide
theorem sec2_dec_val_11_29 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 29)) - 11 * (11 * 29) ≠ 1680 := by decide
theorem sec2_dec_val_11_31 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 31)) - 11 * (11 * 31) ≠ 1680 := by decide
theorem sec2_dec_val_11_37 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 37)) - 11 * (11 * 37) ≠ 1680 := by decide
theorem sec2_dec_val_11_41 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 41)) - 11 * (11 * 41) ≠ 1680 := by decide
theorem sec2_dec_val_11_43 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 43)) - 11 * (11 * 43) ≠ 1680 := by decide
theorem sec2_dec_val_11_47 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 47)) - 11 * (11 * 47) ≠ 1680 := by decide
theorem sec2_dec_val_11_53 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 53)) - 11 * (11 * 53) ≠ 1680 := by decide
theorem sec2_dec_val_11_59 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 59)) - 11 * (11 * 59) ≠ 1680 := by decide
theorem sec2_dec_val_11_61 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 61)) - 11 * (11 * 61) ≠ 1680 := by decide
theorem sec2_dec_val_11_67 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 67)) - 11 * (11 * 67) ≠ 1680 := by decide
theorem sec2_dec_val_11_71 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 71)) - 11 * (11 * 71) ≠ 1680 := by decide
theorem sec2_dec_val_11_73 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 73)) - 11 * (11 * 73) ≠ 1680 := by decide
theorem sec2_dec_val_11_79 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 79)) - 11 * (11 * 79) ≠ 1680 := by decide
theorem sec2_dec_val_11_83 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 83)) - 11 * (11 * 83) ≠ 1680 := by decide
theorem sec2_dec_val_11_89 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 89)) - 11 * (11 * 89) ≠ 1680 := by decide
theorem sec2_dec_val_11_97 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 97)) - 11 * (11 * 97) ≠ 1680 := by decide
theorem sec2_dec_val_11_101 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 101)) - 11 * (11 * 101) ≠ 1680 := by decide
theorem sec2_dec_val_11_103 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 103)) - 11 * (11 * 103) ≠ 1680 := by decide
theorem sec2_dec_val_11_107 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 107)) - 11 * (11 * 107) ≠ 1680 := by decide
theorem sec2_dec_val_11_109 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 109)) - 11 * (11 * 109) ≠ 1680 := by decide
theorem sec2_dec_val_11_113 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 113)) - 11 * (11 * 113) ≠ 1680 := by decide
theorem sec2_dec_val_11_121 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 121)) - 11 * (11 * 121) ≠ 1680 := by decide
theorem sec2_dec_val_11_127 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 127)) - 11 * (11 * 127) ≠ 1680 := by decide
theorem sec2_dec_val_11_131 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 131)) - 11 * (11 * 131) ≠ 1680 := by decide
theorem sec2_dec_val_11_137 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 137)) - 11 * (11 * 137) ≠ 1680 := by decide
theorem sec2_dec_val_11_139 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 139)) - 11 * (11 * 139) ≠ 1680 := by decide
theorem sec2_dec_val_13_17 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 17)) - 13 * (13 * 17) ≠ 1680 := by decide
theorem sec2_dec_val_13_19 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 19)) - 13 * (13 * 19) ≠ 1680 := by decide
theorem sec2_dec_val_13_23 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 23)) - 13 * (13 * 23) ≠ 1680 := by decide
theorem sec2_dec_val_13_29 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 29)) - 13 * (13 * 29) ≠ 1680 := by decide
theorem sec2_dec_val_13_31 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 31)) - 13 * (13 * 31) ≠ 1680 := by decide
theorem sec2_dec_val_13_37 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 37)) - 13 * (13 * 37) ≠ 1680 := by decide
theorem sec2_dec_val_13_41 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 41)) - 13 * (13 * 41) ≠ 1680 := by decide
theorem sec2_dec_val_13_43 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 43)) - 13 * (13 * 43) ≠ 1680 := by decide
theorem sec2_dec_val_13_47 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 47)) - 13 * (13 * 47) ≠ 1680 := by decide
theorem sec2_dec_val_13_53 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 53)) - 13 * (13 * 53) ≠ 1680 := by decide
theorem sec2_dec_val_13_59 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 59)) - 13 * (13 * 59) ≠ 1680 := by decide
theorem sec2_dec_val_13_61 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 61)) - 13 * (13 * 61) ≠ 1680 := by decide
theorem sec2_dec_val_13_67 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 67)) - 13 * (13 * 67) ≠ 1680 := by decide
theorem sec2_dec_val_13_71 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 71)) - 13 * (13 * 71) ≠ 1680 := by decide
theorem sec2_dec_val_13_73 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 73)) - 13 * (13 * 73) ≠ 1680 := by decide
theorem sec2_dec_val_13_79 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 79)) - 13 * (13 * 79) ≠ 1680 := by decide
theorem sec2_dec_val_13_83 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 83)) - 13 * (13 * 83) ≠ 1680 := by decide
theorem sec2_dec_val_13_89 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 89)) - 13 * (13 * 89) ≠ 1680 := by decide
theorem sec2_dec_val_13_97 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 97)) - 13 * (13 * 97) ≠ 1680 := by decide
theorem sec2_dec_val_13_101 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 101)) - 13 * (13 * 101) ≠ 1680 := by decide
theorem sec2_dec_val_13_103 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 103)) - 13 * (13 * 103) ≠ 1680 := by decide
theorem sec2_dec_val_13_107 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 107)) - 13 * (13 * 107) ≠ 1680 := by decide
theorem sec2_dec_val_13_109 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 109)) - 13 * (13 * 109) ≠ 1680 := by decide
theorem sec2_dec_val_13_113 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 113)) - 13 * (13 * 113) ≠ 1680 := by decide
theorem sec2_dec_val_17_19 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 19)) - 17 * (17 * 19) ≠ 1680 := by decide
theorem sec2_dec_val_17_23 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 23)) - 17 * (17 * 23) ≠ 1680 := by decide
theorem sec2_dec_val_17_29 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 29)) - 17 * (17 * 29) ≠ 1680 := by decide
theorem sec2_dec_val_17_31 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 31)) - 17 * (17 * 31) ≠ 1680 := by decide
theorem sec2_dec_val_17_37 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 37)) - 17 * (17 * 37) ≠ 1680 := by decide
theorem sec2_dec_val_17_41 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 41)) - 17 * (17 * 41) ≠ 1680 := by decide
theorem sec2_dec_val_17_43 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 43)) - 17 * (17 * 43) ≠ 1680 := by decide
theorem sec2_dec_val_17_47 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 47)) - 17 * (17 * 47) ≠ 1680 := by decide
theorem sec2_dec_val_17_53 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 53)) - 17 * (17 * 53) ≠ 1680 := by decide
theorem sec2_dec_val_17_59 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 59)) - 17 * (17 * 59) ≠ 1680 := by decide
theorem sec2_dec_val_17_61 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 61)) - 17 * (17 * 61) ≠ 1680 := by decide
theorem sec2_dec_val_17_67 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 67)) - 17 * (17 * 67) ≠ 1680 := by decide
theorem sec2_dec_val_17_71 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 71)) - 17 * (17 * 71) ≠ 1680 := by decide
theorem sec2_dec_val_17_73 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 73)) - 17 * (17 * 73) ≠ 1680 := by decide
theorem sec2_dec_val_17_79 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 79)) - 17 * (17 * 79) ≠ 1680 := by decide
theorem sec2_dec_val_19_23 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 23)) - 19 * (19 * 23) ≠ 1680 := by decide
theorem sec2_dec_val_19_29 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 29)) - 19 * (19 * 29) ≠ 1680 := by decide
theorem sec2_dec_val_19_31 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 31)) - 19 * (19 * 31) ≠ 1680 := by decide
theorem sec2_dec_val_19_37 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 37)) - 19 * (19 * 37) ≠ 1680 := by decide
theorem sec2_dec_val_19_41 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 41)) - 19 * (19 * 41) ≠ 1680 := by decide
theorem sec2_dec_val_19_43 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 43)) - 19 * (19 * 43) ≠ 1680 := by decide
theorem sec2_dec_val_19_47 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 47)) - 19 * (19 * 47) ≠ 1680 := by decide
theorem sec2_dec_val_19_53 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 53)) - 19 * (19 * 53) ≠ 1680 := by decide
theorem sec2_dec_val_19_59 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 59)) - 19 * (19 * 59) ≠ 1680 := by decide
theorem sec2_dec_val_19_61 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 61)) - 19 * (19 * 61) ≠ 1680 := by decide
theorem sec2_dec_val_19_67 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 67)) - 19 * (19 * 67) ≠ 1680 := by decide
theorem sec2_dec_val_23_29 : (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * 29)) - 23 * (23 * 29) ≠ 1680 := by decide
theorem sec2_dec_val_23_31 : (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * 31)) - 23 * (23 * 31) ≠ 1680 := by decide
theorem sec2_dec_val_23_37 : (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * 37)) - 23 * (23 * 37) ≠ 1680 := by decide
theorem sec2_dec_val_23_41 : (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * 41)) - 23 * (23 * 41) ≠ 1680 := by decide
theorem sec2_dec_val_23_43 : (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * 43)) - 23 * (23 * 43) ≠ 1680 := by decide
theorem sec2_dec_val_23_47 : (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * 47)) - 23 * (23 * 47) ≠ 1680 := by decide
theorem sec3_dec_val_11_13 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 13)) - 11 * (11 * 13) ≠ 1680 := by decide
theorem sec3_dec_val_11_17 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 17)) - 11 * (11 * 17) ≠ 1680 := by decide
theorem sec3_dec_val_11_19 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 19)) - 11 * (11 * 19) ≠ 1680 := by decide
theorem sec3_dec_val_11_23 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 23)) - 11 * (11 * 23) ≠ 1680 := by decide
theorem sec3_dec_val_11_29 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 29)) - 11 * (11 * 29) ≠ 1680 := by decide
theorem sec3_dec_val_11_31 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 31)) - 11 * (11 * 31) ≠ 1680 := by decide
theorem sec3_dec_val_11_37 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 37)) - 11 * (11 * 37) ≠ 1680 := by decide
theorem sec3_dec_val_11_41 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 41)) - 11 * (11 * 41) ≠ 1680 := by decide
theorem sec3_dec_val_11_43 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 43)) - 11 * (11 * 43) ≠ 1680 := by decide
theorem sec3_dec_val_11_47 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 47)) - 11 * (11 * 47) ≠ 1680 := by decide
theorem sec3_dec_val_11_53 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 53)) - 11 * (11 * 53) ≠ 1680 := by decide
theorem sec3_dec_val_11_59 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 59)) - 11 * (11 * 59) ≠ 1680 := by decide
theorem sec3_dec_val_11_61 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 61)) - 11 * (11 * 61) ≠ 1680 := by decide
theorem sec3_dec_val_11_67 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 67)) - 11 * (11 * 67) ≠ 1680 := by decide
theorem sec3_dec_val_11_71 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 71)) - 11 * (11 * 71) ≠ 1680 := by decide
theorem sec3_dec_val_11_73 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 73)) - 11 * (11 * 73) ≠ 1680 := by decide
theorem sec3_dec_val_11_79 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 79)) - 11 * (11 * 79) ≠ 1680 := by decide
theorem sec3_dec_val_11_83 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 83)) - 11 * (11 * 83) ≠ 1680 := by decide
theorem sec3_dec_val_11_89 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 89)) - 11 * (11 * 89) ≠ 1680 := by decide
theorem sec3_dec_val_11_97 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 97)) - 11 * (11 * 97) ≠ 1680 := by decide
theorem sec3_dec_val_11_101 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 101)) - 11 * (11 * 101) ≠ 1680 := by decide
theorem sec3_dec_val_11_103 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 103)) - 11 * (11 * 103) ≠ 1680 := by decide
theorem sec3_dec_val_11_107 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 107)) - 11 * (11 * 107) ≠ 1680 := by decide
theorem sec3_dec_val_11_109 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 109)) - 11 * (11 * 109) ≠ 1680 := by decide
theorem sec3_dec_val_11_113 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 113)) - 11 * (11 * 113) ≠ 1680 := by decide
theorem sec3_dec_val_11_121 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 121)) - 11 * (11 * 121) ≠ 1680 := by decide
theorem sec3_dec_val_11_127 : (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * 127)) - 11 * (11 * 127) ≠ 1680 := by decide
theorem sec3_dec_val_13_17 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 17)) - 13 * (13 * 17) ≠ 1680 := by decide
theorem sec3_dec_val_13_19 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 19)) - 13 * (13 * 19) ≠ 1680 := by decide
theorem sec3_dec_val_13_23 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 23)) - 13 * (13 * 23) ≠ 1680 := by decide
theorem sec3_dec_val_13_29 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 29)) - 13 * (13 * 29) ≠ 1680 := by decide
theorem sec3_dec_val_13_31 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 31)) - 13 * (13 * 31) ≠ 1680 := by decide
theorem sec3_dec_val_13_37 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 37)) - 13 * (13 * 37) ≠ 1680 := by decide
theorem sec3_dec_val_13_41 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 41)) - 13 * (13 * 41) ≠ 1680 := by decide
theorem sec3_dec_val_13_43 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 43)) - 13 * (13 * 43) ≠ 1680 := by decide
theorem sec3_dec_val_13_47 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 47)) - 13 * (13 * 47) ≠ 1680 := by decide
theorem sec3_dec_val_13_53 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 53)) - 13 * (13 * 53) ≠ 1680 := by decide
theorem sec3_dec_val_13_59 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 59)) - 13 * (13 * 59) ≠ 1680 := by decide
theorem sec3_dec_val_13_61 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 61)) - 13 * (13 * 61) ≠ 1680 := by decide
theorem sec3_dec_val_13_67 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 67)) - 13 * (13 * 67) ≠ 1680 := by decide
theorem sec3_dec_val_13_71 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 71)) - 13 * (13 * 71) ≠ 1680 := by decide
theorem sec3_dec_val_13_73 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 73)) - 13 * (13 * 73) ≠ 1680 := by decide
theorem sec3_dec_val_13_79 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 79)) - 13 * (13 * 79) ≠ 1680 := by decide
theorem sec3_dec_val_13_83 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 83)) - 13 * (13 * 83) ≠ 1680 := by decide
theorem sec3_dec_val_13_89 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 89)) - 13 * (13 * 89) ≠ 1680 := by decide
theorem sec3_dec_val_13_97 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 97)) - 13 * (13 * 97) ≠ 1680 := by decide
theorem sec3_dec_val_13_101 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 101)) - 13 * (13 * 101) ≠ 1680 := by decide
theorem sec3_dec_val_13_103 : (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * 103)) - 13 * (13 * 103) ≠ 1680 := by decide
theorem sec3_dec_val_17_19 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 19)) - 17 * (17 * 19) ≠ 1680 := by decide
theorem sec3_dec_val_17_23 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 23)) - 17 * (17 * 23) ≠ 1680 := by decide
theorem sec3_dec_val_17_29 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 29)) - 17 * (17 * 29) ≠ 1680 := by decide
theorem sec3_dec_val_17_31 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 31)) - 17 * (17 * 31) ≠ 1680 := by decide
theorem sec3_dec_val_17_37 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 37)) - 17 * (17 * 37) ≠ 1680 := by decide
theorem sec3_dec_val_17_41 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 41)) - 17 * (17 * 41) ≠ 1680 := by decide
theorem sec3_dec_val_17_43 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 43)) - 17 * (17 * 43) ≠ 1680 := by decide
theorem sec3_dec_val_17_47 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 47)) - 17 * (17 * 47) ≠ 1680 := by decide
theorem sec3_dec_val_17_53 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 53)) - 17 * (17 * 53) ≠ 1680 := by decide
theorem sec3_dec_val_17_59 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 59)) - 17 * (17 * 59) ≠ 1680 := by decide
theorem sec3_dec_val_17_61 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 61)) - 17 * (17 * 61) ≠ 1680 := by decide
theorem sec3_dec_val_17_67 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 67)) - 17 * (17 * 67) ≠ 1680 := by decide
theorem sec3_dec_val_17_71 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 71)) - 17 * (17 * 71) ≠ 1680 := by decide
theorem sec3_dec_val_17_73 : (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * 73)) - 17 * (17 * 73) ≠ 1680 := by decide
theorem sec3_dec_val_19_23 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 23)) - 19 * (19 * 23) ≠ 1680 := by decide
theorem sec3_dec_val_19_29 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 29)) - 19 * (19 * 29) ≠ 1680 := by decide
theorem sec3_dec_val_19_31 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 31)) - 19 * (19 * 31) ≠ 1680 := by decide
theorem sec3_dec_val_19_37 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 37)) - 19 * (19 * 37) ≠ 1680 := by decide
theorem sec3_dec_val_19_41 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 41)) - 19 * (19 * 41) ≠ 1680 := by decide
theorem sec3_dec_val_19_43 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 43)) - 19 * (19 * 43) ≠ 1680 := by decide
theorem sec3_dec_val_19_47 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 47)) - 19 * (19 * 47) ≠ 1680 := by decide
theorem sec3_dec_val_19_53 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 53)) - 19 * (19 * 53) ≠ 1680 := by decide
theorem sec3_dec_val_19_59 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 59)) - 19 * (19 * 59) ≠ 1680 := by decide
theorem sec3_dec_val_19_61 : (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * 61)) - 19 * (19 * 61) ≠ 1680 := by decide
theorem sec3_dec_val_23_29 : (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * 29)) - 23 * (23 * 29) ≠ 1680 := by decide
theorem sec3_dec_val_23_31 : (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * 31)) - 23 * (23 * 31) ≠ 1680 := by decide
theorem sec3_dec_val_23_37 : (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * 37)) - 23 * (23 * 37) ≠ 1680 := by decide
theorem sec3_dec_val_23_41 : (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * 41)) - 23 * (23 * 41) ≠ 1680 := by decide
theorem sec3_dec_val_23_43 : (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * 43)) - 23 * (23 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_13 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 13)) - 11 * (13 * 13) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_17 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 17)) - 11 * (13 * 17) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_19 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 19)) - 11 * (13 * 19) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_23 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 23)) - 11 * (13 * 23) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_29 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 29)) - 11 * (13 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_31 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 31)) - 11 * (13 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_37 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 37)) - 11 * (13 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_41 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 41)) - 11 * (13 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_43 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 43)) - 11 * (13 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_47 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 47)) - 11 * (13 * 47) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_53 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 53)) - 11 * (13 * 53) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_59 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 59)) - 11 * (13 * 59) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_61 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 61)) - 11 * (13 * 61) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_67 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 67)) - 11 * (13 * 67) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_71 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 71)) - 11 * (13 * 71) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_73 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 73)) - 11 * (13 * 73) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_79 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 79)) - 11 * (13 * 79) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_83 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 83)) - 11 * (13 * 83) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_89 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 89)) - 11 * (13 * 89) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_97 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 97)) - 11 * (13 * 97) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_101 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 101)) - 11 * (13 * 101) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_103 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 103)) - 11 * (13 * 103) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_107 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 107)) - 11 * (13 * 107) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_109 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 109)) - 11 * (13 * 109) ≠ 1680 := by decide
theorem sec4_dec_val_11_13_113 : (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * 113)) - 11 * (13 * 113) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_17 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 17)) - 11 * (17 * 17) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_19 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 19)) - 11 * (17 * 19) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_23 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 23)) - 11 * (17 * 23) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_29 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 29)) - 11 * (17 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_31 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 31)) - 11 * (17 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_37 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 37)) - 11 * (17 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_41 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 41)) - 11 * (17 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_43 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 43)) - 11 * (17 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_47 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 47)) - 11 * (17 * 47) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_53 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 53)) - 11 * (17 * 53) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_59 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 59)) - 11 * (17 * 59) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_61 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 61)) - 11 * (17 * 61) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_67 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 67)) - 11 * (17 * 67) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_71 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 71)) - 11 * (17 * 71) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_73 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 73)) - 11 * (17 * 73) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_79 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 79)) - 11 * (17 * 79) ≠ 1680 := by decide
theorem sec4_dec_val_11_17_83 : (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * 83)) - 11 * (17 * 83) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_17 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 17)) - 13 * (17 * 17) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_19 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 19)) - 13 * (17 * 19) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_23 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 23)) - 13 * (17 * 23) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_29 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 29)) - 13 * (17 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_31 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 31)) - 13 * (17 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_37 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 37)) - 13 * (17 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_41 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 41)) - 13 * (17 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_43 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 43)) - 13 * (17 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_47 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 47)) - 13 * (17 * 47) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_53 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 53)) - 13 * (17 * 53) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_59 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 59)) - 13 * (17 * 59) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_61 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 61)) - 13 * (17 * 61) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_67 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 67)) - 13 * (17 * 67) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_71 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 71)) - 13 * (17 * 71) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_73 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 73)) - 13 * (17 * 73) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_79 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 79)) - 13 * (17 * 79) ≠ 1680 := by decide
theorem sec4_dec_val_13_17_83 : (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * 83)) - 13 * (17 * 83) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_19 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 19)) - 11 * (19 * 19) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_23 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 23)) - 11 * (19 * 23) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_29 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 29)) - 11 * (19 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_31 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 31)) - 11 * (19 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_37 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 37)) - 11 * (19 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_41 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 41)) - 11 * (19 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_43 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 43)) - 11 * (19 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_47 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 47)) - 11 * (19 * 47) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_53 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 53)) - 11 * (19 * 53) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_59 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 59)) - 11 * (19 * 59) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_61 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 61)) - 11 * (19 * 61) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_67 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 67)) - 11 * (19 * 67) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_71 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 71)) - 11 * (19 * 71) ≠ 1680 := by decide
theorem sec4_dec_val_11_19_73 : (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * 73)) - 11 * (19 * 73) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_19 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 19)) - 13 * (19 * 19) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_23 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 23)) - 13 * (19 * 23) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_29 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 29)) - 13 * (19 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_31 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 31)) - 13 * (19 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_37 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 37)) - 13 * (19 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_41 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 41)) - 13 * (19 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_43 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 43)) - 13 * (19 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_47 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 47)) - 13 * (19 * 47) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_53 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 53)) - 13 * (19 * 53) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_59 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 59)) - 13 * (19 * 59) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_61 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 61)) - 13 * (19 * 61) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_67 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 67)) - 13 * (19 * 67) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_71 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 71)) - 13 * (19 * 71) ≠ 1680 := by decide
theorem sec4_dec_val_13_19_73 : (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * 73)) - 13 * (19 * 73) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_19 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 19)) - 17 * (19 * 19) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_23 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 23)) - 17 * (19 * 23) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_29 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 29)) - 17 * (19 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_31 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 31)) - 17 * (19 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_37 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 37)) - 17 * (19 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_41 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 41)) - 17 * (19 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_43 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 43)) - 17 * (19 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_47 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 47)) - 17 * (19 * 47) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_53 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 53)) - 17 * (19 * 53) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_59 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 59)) - 17 * (19 * 59) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_61 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 61)) - 17 * (19 * 61) ≠ 1680 := by decide
theorem sec4_dec_val_17_19_67 : (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * 67)) - 17 * (19 * 67) ≠ 1680 := by decide
theorem sec4_dec_val_11_23_23 : (sigma 1 : ArithmeticFunction ℕ) (11 * (23 * 23)) - 11 * (23 * 23) ≠ 1680 := by decide
theorem sec4_dec_val_11_23_29 : (sigma 1 : ArithmeticFunction ℕ) (11 * (23 * 29)) - 11 * (23 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_11_23_31 : (sigma 1 : ArithmeticFunction ℕ) (11 * (23 * 31)) - 11 * (23 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_11_23_37 : (sigma 1 : ArithmeticFunction ℕ) (11 * (23 * 37)) - 11 * (23 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_11_23_41 : (sigma 1 : ArithmeticFunction ℕ) (11 * (23 * 41)) - 11 * (23 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_11_23_43 : (sigma 1 : ArithmeticFunction ℕ) (11 * (23 * 43)) - 11 * (23 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_11_23_47 : (sigma 1 : ArithmeticFunction ℕ) (11 * (23 * 47)) - 11 * (23 * 47) ≠ 1680 := by decide
theorem sec4_dec_val_11_23_53 : (sigma 1 : ArithmeticFunction ℕ) (11 * (23 * 53)) - 11 * (23 * 53) ≠ 1680 := by decide
theorem sec4_dec_val_11_23_59 : (sigma 1 : ArithmeticFunction ℕ) (11 * (23 * 59)) - 11 * (23 * 59) ≠ 1680 := by decide
theorem sec4_dec_val_13_23_23 : (sigma 1 : ArithmeticFunction ℕ) (13 * (23 * 23)) - 13 * (23 * 23) ≠ 1680 := by decide
theorem sec4_dec_val_13_23_29 : (sigma 1 : ArithmeticFunction ℕ) (13 * (23 * 29)) - 13 * (23 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_13_23_31 : (sigma 1 : ArithmeticFunction ℕ) (13 * (23 * 31)) - 13 * (23 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_13_23_37 : (sigma 1 : ArithmeticFunction ℕ) (13 * (23 * 37)) - 13 * (23 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_13_23_41 : (sigma 1 : ArithmeticFunction ℕ) (13 * (23 * 41)) - 13 * (23 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_13_23_43 : (sigma 1 : ArithmeticFunction ℕ) (13 * (23 * 43)) - 13 * (23 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_13_23_47 : (sigma 1 : ArithmeticFunction ℕ) (13 * (23 * 47)) - 13 * (23 * 47) ≠ 1680 := by decide
theorem sec4_dec_val_13_23_53 : (sigma 1 : ArithmeticFunction ℕ) (13 * (23 * 53)) - 13 * (23 * 53) ≠ 1680 := by decide
theorem sec4_dec_val_17_23_23 : (sigma 1 : ArithmeticFunction ℕ) (17 * (23 * 23)) - 17 * (23 * 23) ≠ 1680 := by decide
theorem sec4_dec_val_17_23_29 : (sigma 1 : ArithmeticFunction ℕ) (17 * (23 * 29)) - 17 * (23 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_17_23_31 : (sigma 1 : ArithmeticFunction ℕ) (17 * (23 * 31)) - 17 * (23 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_17_23_37 : (sigma 1 : ArithmeticFunction ℕ) (17 * (23 * 37)) - 17 * (23 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_17_23_41 : (sigma 1 : ArithmeticFunction ℕ) (17 * (23 * 41)) - 17 * (23 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_17_23_43 : (sigma 1 : ArithmeticFunction ℕ) (17 * (23 * 43)) - 17 * (23 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_17_23_47 : (sigma 1 : ArithmeticFunction ℕ) (17 * (23 * 47)) - 17 * (23 * 47) ≠ 1680 := by decide
theorem sec4_dec_val_17_23_53 : (sigma 1 : ArithmeticFunction ℕ) (17 * (23 * 53)) - 17 * (23 * 53) ≠ 1680 := by decide
theorem sec4_dec_val_19_23_23 : (sigma 1 : ArithmeticFunction ℕ) (19 * (23 * 23)) - 19 * (23 * 23) ≠ 1680 := by decide
theorem sec4_dec_val_19_23_29 : (sigma 1 : ArithmeticFunction ℕ) (19 * (23 * 29)) - 19 * (23 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_19_23_31 : (sigma 1 : ArithmeticFunction ℕ) (19 * (23 * 31)) - 19 * (23 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_19_23_37 : (sigma 1 : ArithmeticFunction ℕ) (19 * (23 * 37)) - 19 * (23 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_19_23_41 : (sigma 1 : ArithmeticFunction ℕ) (19 * (23 * 41)) - 19 * (23 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_19_23_43 : (sigma 1 : ArithmeticFunction ℕ) (19 * (23 * 43)) - 19 * (23 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_19_23_47 : (sigma 1 : ArithmeticFunction ℕ) (19 * (23 * 47)) - 19 * (23 * 47) ≠ 1680 := by decide
theorem sec4_dec_val_11_29_29 : (sigma 1 : ArithmeticFunction ℕ) (11 * (29 * 29)) - 11 * (29 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_11_29_31 : (sigma 1 : ArithmeticFunction ℕ) (11 * (29 * 31)) - 11 * (29 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_11_29_37 : (sigma 1 : ArithmeticFunction ℕ) (11 * (29 * 37)) - 11 * (29 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_11_29_41 : (sigma 1 : ArithmeticFunction ℕ) (11 * (29 * 41)) - 11 * (29 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_11_29_43 : (sigma 1 : ArithmeticFunction ℕ) (11 * (29 * 43)) - 11 * (29 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_13_29_29 : (sigma 1 : ArithmeticFunction ℕ) (13 * (29 * 29)) - 13 * (29 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_13_29_31 : (sigma 1 : ArithmeticFunction ℕ) (13 * (29 * 31)) - 13 * (29 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_13_29_37 : (sigma 1 : ArithmeticFunction ℕ) (13 * (29 * 37)) - 13 * (29 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_13_29_41 : (sigma 1 : ArithmeticFunction ℕ) (13 * (29 * 41)) - 13 * (29 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_13_29_43 : (sigma 1 : ArithmeticFunction ℕ) (13 * (29 * 43)) - 13 * (29 * 43) ≠ 1680 := by decide
theorem sec4_dec_val_17_29_29 : (sigma 1 : ArithmeticFunction ℕ) (17 * (29 * 29)) - 17 * (29 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_17_29_31 : (sigma 1 : ArithmeticFunction ℕ) (17 * (29 * 31)) - 17 * (29 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_17_29_37 : (sigma 1 : ArithmeticFunction ℕ) (17 * (29 * 37)) - 17 * (29 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_19_29_29 : (sigma 1 : ArithmeticFunction ℕ) (19 * (29 * 29)) - 19 * (29 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_19_29_31 : (sigma 1 : ArithmeticFunction ℕ) (19 * (29 * 31)) - 19 * (29 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_19_29_37 : (sigma 1 : ArithmeticFunction ℕ) (19 * (29 * 37)) - 19 * (29 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_23_29_29 : (sigma 1 : ArithmeticFunction ℕ) (23 * (29 * 29)) - 23 * (29 * 29) ≠ 1680 := by decide
theorem sec4_dec_val_23_29_31 : (sigma 1 : ArithmeticFunction ℕ) (23 * (29 * 31)) - 23 * (29 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_11_31_31 : (sigma 1 : ArithmeticFunction ℕ) (11 * (31 * 31)) - 11 * (31 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_11_31_37 : (sigma 1 : ArithmeticFunction ℕ) (11 * (31 * 37)) - 11 * (31 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_11_31_41 : (sigma 1 : ArithmeticFunction ℕ) (11 * (31 * 41)) - 11 * (31 * 41) ≠ 1680 := by decide
theorem sec4_dec_val_13_31_31 : (sigma 1 : ArithmeticFunction ℕ) (13 * (31 * 31)) - 13 * (31 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_13_31_37 : (sigma 1 : ArithmeticFunction ℕ) (13 * (31 * 37)) - 13 * (31 * 37) ≠ 1680 := by decide
theorem sec4_dec_val_17_31_31 : (sigma 1 : ArithmeticFunction ℕ) (17 * (31 * 31)) - 17 * (31 * 31) ≠ 1680 := by decide
theorem sec4_dec_val_19_31_31 : (sigma 1 : ArithmeticFunction ℕ) (19 * (31 * 31)) - 19 * (31 * 31) ≠ 1680 := by decide
theorem sec2_dec_11 : ∀ k ∈ Finset.Icc (11 + 1) 140, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * k)) - 11 * (11 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 26 ∨ (k ≥ 27 ∧ k ≤ 41) ∨ (k ≥ 42 ∧ k ≤ 56) ∨ (k ≥ 57 ∧ k ≤ 71) ∨ (k ≥ 72 ∧ k ≤ 86) ∨ (k ≥ 87 ∧ k ≤ 101) ∨ (k ≥ 102 ∧ k ≤ 116) ∨ (k ≥ 117 ∧ k ≤ 131) ∨ k ≥ 132 := by omega
  rcases h_disj with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · interval_cases k
    · revert h_cop; decide
    · exact sec2_dec_val_11_13
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_17
    · revert h_cop; decide
    · exact sec2_dec_val_11_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_29
    · revert h_cop; decide
    · exact sec2_dec_val_11_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_41
  · rcases h3 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · exact sec2_dec_val_11_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_47
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h4 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_59
    · revert h_cop; decide
    · exact sec2_dec_val_11_61
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_67
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_71
  · rcases h5 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · exact sec2_dec_val_11_73
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_79
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_83
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h6 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_89
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_97
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_101
  · rcases h7 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · exact sec2_dec_val_11_103
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_107
    · revert h_cop; decide
    · exact sec2_dec_val_11_109
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_113
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h8 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_121
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_127
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_131
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_11_137
    · revert h_cop; decide
    · exact sec2_dec_val_11_139
    · revert h_cop; decide

theorem sec2_dec_13 : ∀ k ∈ Finset.Icc (13 + 1) 115, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * k)) - 13 * (13 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 28 ∨ (k ≥ 29 ∧ k ≤ 43) ∨ (k ≥ 44 ∧ k ≤ 58) ∨ (k ≥ 59 ∧ k ≤ 73) ∨ (k ≥ 74 ∧ k ≤ 88) ∨ (k ≥ 89 ∧ k ≤ 103) ∨ k ≥ 104 := by omega
  rcases h_disj with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_17
    · revert h_cop; decide
    · exact sec2_dec_val_13_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · exact sec2_dec_val_13_29
    · revert h_cop; decide
    · exact sec2_dec_val_13_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_41
    · revert h_cop; decide
    · exact sec2_dec_val_13_43
  · rcases h3 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_47
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h4 with ⟨_, _⟩; interval_cases k
    · exact sec2_dec_val_13_59
    · revert h_cop; decide
    · exact sec2_dec_val_13_61
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_67
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_71
    · revert h_cop; decide
    · exact sec2_dec_val_13_73
  · rcases h5 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_79
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_83
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h6 with ⟨_, _⟩; interval_cases k
    · exact sec2_dec_val_13_89
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_97
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_101
    · revert h_cop; decide
    · exact sec2_dec_val_13_103
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_107
    · revert h_cop; decide
    · exact sec2_dec_val_13_109
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_13_113
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec2_dec_17 : ∀ k ∈ Finset.Icc (17 + 1) 80, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * k)) - 17 * (17 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 32 ∨ (k ≥ 33 ∧ k ≤ 47) ∨ (k ≥ 48 ∧ k ≤ 62) ∨ (k ≥ 63 ∧ k ≤ 77) ∨ k ≥ 78 := by omega
  rcases h_disj with h1 | h2 | h3 | h4 | h5
  · interval_cases k
    · revert h_cop; decide
    · exact sec2_dec_val_17_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_17_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_17_29
    · revert h_cop; decide
    · exact sec2_dec_val_17_31
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_17_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_17_41
    · revert h_cop; decide
    · exact sec2_dec_val_17_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_17_47
  · rcases h3 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_17_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_17_59
    · revert h_cop; decide
    · exact sec2_dec_val_17_61
    · revert h_cop; decide
  · rcases h4 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_17_67
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_17_71
    · revert h_cop; decide
    · exact sec2_dec_val_17_73
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases k
    · revert h_cop; decide
    · exact sec2_dec_val_17_79
    · revert h_cop; decide

theorem sec2_dec_19 : ∀ k ∈ Finset.Icc (19 + 1) 68, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * k)) - 19 * (19 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 34 ∨ (k ≥ 35 ∧ k ≤ 49) ∨ (k ≥ 50 ∧ k ≤ 64) ∨ k ≥ 65 := by omega
  rcases h_disj with h1 | h2 | h3 | h4
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_19_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_19_29
    · revert h_cop; decide
    · exact sec2_dec_val_19_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_19_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_19_41
    · revert h_cop; decide
    · exact sec2_dec_val_19_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_19_47
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h3 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_19_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_19_59
    · revert h_cop; decide
    · exact sec2_dec_val_19_61
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_19_67
    · revert h_cop; decide

theorem sec2_dec_23 : ∀ k ∈ Finset.Icc (23 + 1) 49, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * k)) - 23 * (23 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 38 ∨ k ≥ 39 := by omega
  rcases h_disj with h1 | h2
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_23_29
    · revert h_cop; decide
    · exact sec2_dec_val_23_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_23_37
    · revert h_cop; decide
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_23_41
    · revert h_cop; decide
    · exact sec2_dec_val_23_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec2_dec_val_23_47
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec3_dec_11 : ∀ r ∈ Finset.Icc (11 + 1) 128, Nat.Coprime r 1680 → (sigma 1 : ArithmeticFunction ℕ) (11 * (11 * r)) - 11 * (11 * r) ≠ 1680 := by
  intro r hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : r ≤ 26 ∨ (r ≥ 27 ∧ r ≤ 41) ∨ (r ≥ 42 ∧ r ≤ 56) ∨ (r ≥ 57 ∧ r ≤ 71) ∨ (r ≥ 72 ∧ r ≤ 86) ∨ (r ≥ 87 ∧ r ≤ 101) ∨ (r ≥ 102 ∧ r ≤ 116) ∨ r ≥ 117 := by omega
  rcases h_disj with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · interval_cases r
    · revert h_cop; decide
    · exact sec3_dec_val_11_13
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_17
    · revert h_cop; decide
    · exact sec3_dec_val_11_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_29
    · revert h_cop; decide
    · exact sec3_dec_val_11_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_41
  · rcases h3 with ⟨_, _⟩; interval_cases r
    · revert h_cop; decide
    · exact sec3_dec_val_11_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_47
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h4 with ⟨_, _⟩; interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_59
    · revert h_cop; decide
    · exact sec3_dec_val_11_61
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_67
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_71
  · rcases h5 with ⟨_, _⟩; interval_cases r
    · revert h_cop; decide
    · exact sec3_dec_val_11_73
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_79
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_83
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h6 with ⟨_, _⟩; interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_89
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_97
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_101
  · rcases h7 with ⟨_, _⟩; interval_cases r
    · revert h_cop; decide
    · exact sec3_dec_val_11_103
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_107
    · revert h_cop; decide
    · exact sec3_dec_val_11_109
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_113
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_121
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_11_127
    · revert h_cop; decide

theorem sec3_dec_13 : ∀ r ∈ Finset.Icc (13 + 1) 106, Nat.Coprime r 1680 → (sigma 1 : ArithmeticFunction ℕ) (13 * (13 * r)) - 13 * (13 * r) ≠ 1680 := by
  intro r hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : r ≤ 28 ∨ (r ≥ 29 ∧ r ≤ 43) ∨ (r ≥ 44 ∧ r ≤ 58) ∨ (r ≥ 59 ∧ r ≤ 73) ∨ (r ≥ 74 ∧ r ≤ 88) ∨ (r ≥ 89 ∧ r ≤ 103) ∨ r ≥ 104 := by omega
  rcases h_disj with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_17
    · revert h_cop; decide
    · exact sec3_dec_val_13_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases r
    · exact sec3_dec_val_13_29
    · revert h_cop; decide
    · exact sec3_dec_val_13_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_41
    · revert h_cop; decide
    · exact sec3_dec_val_13_43
  · rcases h3 with ⟨_, _⟩; interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_47
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h4 with ⟨_, _⟩; interval_cases r
    · exact sec3_dec_val_13_59
    · revert h_cop; decide
    · exact sec3_dec_val_13_61
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_67
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_71
    · revert h_cop; decide
    · exact sec3_dec_val_13_73
  · rcases h5 with ⟨_, _⟩; interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_79
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_83
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h6 with ⟨_, _⟩; interval_cases r
    · exact sec3_dec_val_13_89
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_97
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_13_101
    · revert h_cop; decide
    · exact sec3_dec_val_13_103
  · interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec3_dec_17 : ∀ r ∈ Finset.Icc (17 + 1) 76, Nat.Coprime r 1680 → (sigma 1 : ArithmeticFunction ℕ) (17 * (17 * r)) - 17 * (17 * r) ≠ 1680 := by
  intro r hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : r ≤ 32 ∨ (r ≥ 33 ∧ r ≤ 47) ∨ (r ≥ 48 ∧ r ≤ 62) ∨ r ≥ 63 := by omega
  rcases h_disj with h1 | h2 | h3 | h4
  · interval_cases r
    · revert h_cop; decide
    · exact sec3_dec_val_17_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_17_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_17_29
    · revert h_cop; decide
    · exact sec3_dec_val_17_31
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_17_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_17_41
    · revert h_cop; decide
    · exact sec3_dec_val_17_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_17_47
  · rcases h3 with ⟨_, _⟩; interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_17_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_17_59
    · revert h_cop; decide
    · exact sec3_dec_val_17_61
    · revert h_cop; decide
  · interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_17_67
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_17_71
    · revert h_cop; decide
    · exact sec3_dec_val_17_73
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec3_dec_19 : ∀ r ∈ Finset.Icc (19 + 1) 64, Nat.Coprime r 1680 → (sigma 1 : ArithmeticFunction ℕ) (19 * (19 * r)) - 19 * (19 * r) ≠ 1680 := by
  intro r hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : r ≤ 34 ∨ (r ≥ 35 ∧ r ≤ 49) ∨ r ≥ 50 := by omega
  rcases h_disj with h1 | h2 | h3
  · interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_19_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_19_29
    · revert h_cop; decide
    · exact sec3_dec_val_19_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_19_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_19_41
    · revert h_cop; decide
    · exact sec3_dec_val_19_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_19_47
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_19_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_19_59
    · revert h_cop; decide
    · exact sec3_dec_val_19_61
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec3_dec_23 : ∀ r ∈ Finset.Icc (23 + 1) 46, Nat.Coprime r 1680 → (sigma 1 : ArithmeticFunction ℕ) (23 * (23 * r)) - 23 * (23 * r) ≠ 1680 := by
  intro r hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : r ≤ 38 ∨ r ≥ 39 := by omega
  rcases h_disj with h1 | h2
  · interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_23_29
    · revert h_cop; decide
    · exact sec3_dec_val_23_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_23_37
    · revert h_cop; decide
  · interval_cases r
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec3_dec_val_23_41
    · revert h_cop; decide
    · exact sec3_dec_val_23_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec4_dec_11_13 : ∀ k ∈ Finset.Icc 13 116, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (11 * (13 * k)) - 11 * (13 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 27 ∨ (k ≥ 28 ∧ k ≤ 42) ∨ (k ≥ 43 ∧ k ≤ 57) ∨ (k ≥ 58 ∧ k ≤ 72) ∨ (k ≥ 73 ∧ k ≤ 87) ∨ (k ≥ 88 ∧ k ≤ 102) ∨ k ≥ 103 := by omega
  rcases h_disj with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · interval_cases k
    · exact sec4_dec_val_11_13_13
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_17
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_29
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_41
    · revert h_cop; decide
  · rcases h3 with ⟨_, _⟩; interval_cases k
    · exact sec4_dec_val_11_13_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_47
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h4 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_59
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_61
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_67
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_71
    · revert h_cop; decide
  · rcases h5 with ⟨_, _⟩; interval_cases k
    · exact sec4_dec_val_11_13_73
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_79
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_83
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h6 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_89
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_97
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_101
    · revert h_cop; decide
  · interval_cases k
    · exact sec4_dec_val_11_13_103
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_107
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_109
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_13_113
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec4_dec_11_17 : ∀ k ∈ Finset.Icc 17 86, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (11 * (17 * k)) - 11 * (17 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 31 ∨ (k ≥ 32 ∧ k ≤ 46) ∨ (k ≥ 47 ∧ k ≤ 61) ∨ (k ≥ 62 ∧ k ≤ 76) ∨ k ≥ 77 := by omega
  rcases h_disj with h1 | h2 | h3 | h4 | h5
  · interval_cases k
    · exact sec4_dec_val_11_17_17
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_29
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_31
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_41
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h3 with ⟨_, _⟩; interval_cases k
    · exact sec4_dec_val_11_17_47
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_59
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_61
  · rcases h4 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_67
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_71
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_73
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_79
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_17_83
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec4_dec_13_17 : ∀ k ∈ Finset.Icc 17 84, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (13 * (17 * k)) - 13 * (17 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 31 ∨ (k ≥ 32 ∧ k ≤ 46) ∨ (k ≥ 47 ∧ k ≤ 61) ∨ (k ≥ 62 ∧ k ≤ 76) ∨ k ≥ 77 := by omega
  rcases h_disj with h1 | h2 | h3 | h4 | h5
  · interval_cases k
    · exact sec4_dec_val_13_17_17
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_29
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_31
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_41
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h3 with ⟨_, _⟩; interval_cases k
    · exact sec4_dec_val_13_17_47
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_59
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_61
  · rcases h4 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_67
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_71
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_73
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_79
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_17_83
    · revert h_cop; decide

theorem sec4_dec_11_19 : ∀ k ∈ Finset.Icc 19 75, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (11 * (19 * k)) - 11 * (19 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 33 ∨ (k ≥ 34 ∧ k ≤ 48) ∨ (k ≥ 49 ∧ k ≤ 63) ∨ k ≥ 64 := by omega
  rcases h_disj with h1 | h2 | h3 | h4
  · interval_cases k
    · exact sec4_dec_val_11_19_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_29
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_31
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_41
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_47
    · revert h_cop; decide
  · rcases h3 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_59
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_61
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_67
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_71
    · revert h_cop; decide
    · exact sec4_dec_val_11_19_73
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec4_dec_13_19 : ∀ k ∈ Finset.Icc 19 73, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (13 * (19 * k)) - 13 * (19 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 33 ∨ (k ≥ 34 ∧ k ≤ 48) ∨ (k ≥ 49 ∧ k ≤ 63) ∨ k ≥ 64 := by omega
  rcases h_disj with h1 | h2 | h3 | h4
  · interval_cases k
    · exact sec4_dec_val_13_19_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_29
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_31
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_41
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_47
    · revert h_cop; decide
  · rcases h3 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_59
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_61
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_67
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_71
    · revert h_cop; decide
    · exact sec4_dec_val_13_19_73

theorem sec4_dec_17_19 : ∀ k ∈ Finset.Icc 19 69, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (17 * (19 * k)) - 17 * (19 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 33 ∨ (k ≥ 34 ∧ k ≤ 48) ∨ (k ≥ 49 ∧ k ≤ 63) ∨ k ≥ 64 := by omega
  rcases h_disj with h1 | h2 | h3 | h4
  · interval_cases k
    · exact sec4_dec_val_17_19_19
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_19_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_19_29
    · revert h_cop; decide
    · exact sec4_dec_val_17_19_31
    · revert h_cop; decide
    · revert h_cop; decide
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_19_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_19_41
    · revert h_cop; decide
    · exact sec4_dec_val_17_19_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_19_47
    · revert h_cop; decide
  · rcases h3 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_19_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_19_59
    · revert h_cop; decide
    · exact sec4_dec_val_17_19_61
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_19_67
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec4_dec_11_23 : ∀ k ∈ Finset.Icc 23 60, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (11 * (23 * k)) - 11 * (23 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 37 ∨ (k ≥ 38 ∧ k ≤ 52) ∨ k ≥ 53 := by omega
  rcases h_disj with h1 | h2 | h3
  · interval_cases k
    · exact sec4_dec_val_11_23_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_23_29
    · revert h_cop; decide
    · exact sec4_dec_val_11_23_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_23_37
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_23_41
    · revert h_cop; decide
    · exact sec4_dec_val_11_23_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_23_47
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases k
    · exact sec4_dec_val_11_23_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_23_59
    · revert h_cop; decide

theorem sec4_dec_13_23 : ∀ k ∈ Finset.Icc 23 58, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (13 * (23 * k)) - 13 * (23 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 37 ∨ (k ≥ 38 ∧ k ≤ 52) ∨ k ≥ 53 := by omega
  rcases h_disj with h1 | h2 | h3
  · interval_cases k
    · exact sec4_dec_val_13_23_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_23_29
    · revert h_cop; decide
    · exact sec4_dec_val_13_23_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_23_37
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_23_41
    · revert h_cop; decide
    · exact sec4_dec_val_13_23_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_13_23_47
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases k
    · exact sec4_dec_val_13_23_53
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec4_dec_17_23 : ∀ k ∈ Finset.Icc 23 54, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (17 * (23 * k)) - 17 * (23 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 37 ∨ (k ≥ 38 ∧ k ≤ 52) ∨ k ≥ 53 := by omega
  rcases h_disj with h1 | h2 | h3
  · interval_cases k
    · exact sec4_dec_val_17_23_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_23_29
    · revert h_cop; decide
    · exact sec4_dec_val_17_23_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_23_37
  · rcases h2 with ⟨_, _⟩; interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_23_41
    · revert h_cop; decide
    · exact sec4_dec_val_17_23_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_17_23_47
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
  · interval_cases k
    · exact sec4_dec_val_17_23_53
    · revert h_cop; decide

theorem sec4_dec_19_23 : ∀ k ∈ Finset.Icc 23 52, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (19 * (23 * k)) - 19 * (23 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 37 ∨ k ≥ 38 := by omega
  rcases h_disj with h1 | h2
  · interval_cases k
    · exact sec4_dec_val_19_23_23
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_19_23_29
    · revert h_cop; decide
    · exact sec4_dec_val_19_23_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_19_23_37
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_19_23_41
    · revert h_cop; decide
    · exact sec4_dec_val_19_23_43
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_19_23_47
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec4_dec_11_29 : ∀ k ∈ Finset.Icc 29 45, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (11 * (29 * k)) - 11 * (29 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  have h_disj : k ≤ 43 ∨ k ≥ 44 := by omega
  rcases h_disj with h1 | h2
  · interval_cases k
    · exact sec4_dec_val_11_29_29
    · revert h_cop; decide
    · exact sec4_dec_val_11_29_31
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_29_37
    · revert h_cop; decide
    · revert h_cop; decide
    · revert h_cop; decide
    · exact sec4_dec_val_11_29_41
    · revert h_cop; decide
    · exact sec4_dec_val_11_29_43
  · interval_cases k
    · revert h_cop; decide
    · revert h_cop; decide

theorem sec4_dec_13_29 : ∀ k ∈ Finset.Icc 29 43, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (13 * (29 * k)) - 13 * (29 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k
  · exact sec4_dec_val_13_29_29
  · revert h_cop; decide
  · exact sec4_dec_val_13_29_31
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · exact sec4_dec_val_13_29_37
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · exact sec4_dec_val_13_29_41
  · revert h_cop; decide
  · exact sec4_dec_val_13_29_43

theorem sec4_dec_17_29 : ∀ k ∈ Finset.Icc 29 39, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (17 * (29 * k)) - 17 * (29 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k
  · exact sec4_dec_val_17_29_29
  · revert h_cop; decide
  · exact sec4_dec_val_17_29_31
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · exact sec4_dec_val_17_29_37
  · revert h_cop; decide
  · revert h_cop; decide

theorem sec4_dec_19_29 : ∀ k ∈ Finset.Icc 29 37, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (19 * (29 * k)) - 19 * (29 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k
  · exact sec4_dec_val_19_29_29
  · revert h_cop; decide
  · exact sec4_dec_val_19_29_31
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · exact sec4_dec_val_19_29_37

theorem sec4_dec_23_29 : ∀ k ∈ Finset.Icc 29 33, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (23 * (29 * k)) - 23 * (29 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k
  · exact sec4_dec_val_23_29_29
  · revert h_cop; decide
  · exact sec4_dec_val_23_29_31
  · revert h_cop; decide
  · revert h_cop; decide

theorem sec4_dec_11_31 : ∀ k ∈ Finset.Icc 31 41, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (11 * (31 * k)) - 11 * (31 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k
  · exact sec4_dec_val_11_31_31
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · exact sec4_dec_val_11_31_37
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · exact sec4_dec_val_11_31_41

theorem sec4_dec_13_31 : ∀ k ∈ Finset.Icc 31 39, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (13 * (31 * k)) - 13 * (31 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k
  · exact sec4_dec_val_13_31_31
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · exact sec4_dec_val_13_31_37
  · revert h_cop; decide
  · revert h_cop; decide

theorem sec4_dec_17_31 : ∀ k ∈ Finset.Icc 31 35, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (17 * (31 * k)) - 17 * (31 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k
  · exact sec4_dec_val_17_31_31
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide
  · revert h_cop; decide

theorem sec4_dec_19_31 : ∀ k ∈ Finset.Icc 31 33, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (19 * (31 * k)) - 19 * (31 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k
  · exact sec4_dec_val_19_31_31
  · revert h_cop; decide
  · revert h_cop; decide

theorem sec4_dec_23_31 : ∀ k ∈ Finset.Icc 31 29, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (23 * (31 * k)) - 23 * (31 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k

theorem sec4_dec_29_31 : ∀ k ∈ Finset.Icc 31 23, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (29 * (31 * k)) - 29 * (31 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k

theorem sec4_dec_11_37 : ∀ k ∈ Finset.Icc 37 33, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (11 * (37 * k)) - 11 * (37 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k

theorem sec4_dec_13_37 : ∀ k ∈ Finset.Icc 37 31, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (13 * (37 * k)) - 13 * (37 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k

theorem sec4_dec_17_37 : ∀ k ∈ Finset.Icc 37 26, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (17 * (37 * k)) - 17 * (37 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k

theorem sec4_dec_19_37 : ∀ k ∈ Finset.Icc 37 24, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (19 * (37 * k)) - 19 * (37 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k

theorem sec4_dec_23_37 : ∀ k ∈ Finset.Icc 37 20, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (23 * (37 * k)) - 23 * (37 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k

theorem sec4_dec_29_37 : ∀ k ∈ Finset.Icc 37 14, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (29 * (37 * k)) - 29 * (37 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k

theorem sec4_dec_31_37 : ∀ k ∈ Finset.Icc 37 12, Nat.Coprime k 1680 → (sigma 1 : ArithmeticFunction ℕ) (31 * (37 * k)) - 31 * (37 * k) ≠ 1680 := by
  intro k hk h_cop
  rcases Finset.mem_Icc.mp hk with ⟨hk_ge, hk_le⟩
  interval_cases k


theorem sigma_sub_ne_1680 (q : ℕ) (hq : q ≥ 1) (h_cop : Nat.Coprime q 1680) :
    (sigma 1 : ArithmeticFunction ℕ) q - q ≠ 1680 := by
  by_cases hq1 : q = 1
  · rw [hq1]
    change (sigma 1 1 : ℕ) - 1 ≠ 1680
    rw [sigma_one]
    decide
  · have hq_gt : q > 1 := by omega
    have hp := Nat.minFac_prime (by omega : q ≠ 1)
    have hp_dvd := Nat.minFac_dvd q
    have h_cop_min : Nat.Coprime q.minFac 1680 := h_cop.of_dvd_left hp_dvd
    have hp_ge : q.minFac ≥ 5 := by
      by_contra hc
      have h_lt : q.minFac < 5 := by omega
      have h_cases : q.minFac = 0 ∨ q.minFac = 1 ∨ q.minFac = 2 ∨ q.minFac = 3 ∨ q.minFac = 4 := by omega
      rcases h_cases with h|h|h|h|h
      · rw [h] at hp; exact Nat.not_prime_zero hp
      · rw [h] at hp; exact Nat.not_prime_one hp
      · rw [h] at h_cop_min; revert h_cop_min; decide
      · rw [h] at h_cop_min; revert h_cop_min; decide
      · rw [h] at hp; revert hp; decide


    by_cases h_prime : Nat.Prime q
    · have h_sig : (sigma 1 : ArithmeticFunction ℕ) q = q + 1 := by
        have h_pow := sigma_one_apply_prime_pow h_prime (i := 1)
        simp only [pow_one] at h_pow
        rw [h_pow]
        simp [Finset.sum_range_succ]
        ring
      rw [h_sig]
      omega
    · by_cases h_sq : q = q.minFac ^ 2
      · rw [h_sq]
        rw [sigma_prime_sq hp]
        have : 1 + q.minFac + q.minFac ^ 2 - q.minFac ^ 2 = q.minFac + 1 := by omega
        rw [this]
        intro hc
        have : q.minFac = 1679 := by omega
        have h_comp : ¬ Nat.Prime 1679 := by
          intro hp_comp
          have hdvd : 23 ∣ 1679 := by decide
          have := Nat.Prime.eq_one_or_self_of_dvd hp_comp (m := 23) hdvd
          revert this
          decide
        rw [← this] at h_comp
        exact h_comp hp
      · set p := q.minFac
        set m := q / p
        have hp_dvd : p ∣ q := Nat.minFac_dvd q
        have h_eq : q = p * m := (Nat.mul_div_cancel' hp_dvd).symm
        have hm_gt1 : m > 1 := by
          by_contra hc
          generalize hm : m = m_val at hc
          have : m_val = 0 ∨ m_val = 1 := by omega
          rw [← hm] at this
          rcases this with hm0 | hm1
          · rw [hm0, Nat.mul_zero] at h_eq
            omega
          · rw [hm1, Nat.mul_one] at h_eq
            rw [h_eq] at h_prime
            exact h_prime hp
        have hp_lt_q : p < q := by
          rw [h_eq]
          calc p = p * 1 := (Nat.mul_one p).symm
          _ < p * m := Nat.mul_lt_mul_of_pos_left hm_gt1 (by omega)
        have hm_lt_q : m < q := by
          rw [h_eq, Nat.mul_comm]
          calc m = m * 1 := (Nat.mul_one m).symm
          _ < m * p := Nat.mul_lt_mul_of_pos_left (by omega : p > 1) (by omega)
        have h_distinct : p ≠ m := by
          intro hc
          have : q = p ^ 2 := by
            rw [h_eq, hc]
            ring
          exact h_sq this
        have h_mem_p : p ∈ q.divisors := by
          rw [mem_divisors]
          exact ⟨hp_dvd, by omega⟩
        have h_mem_m : m ∈ q.divisors := by
          rw [mem_divisors]
          have : m ∣ q := by
            rw [h_eq]
            use p; ring
          exact ⟨this, by omega⟩
        have h_mem_1 : 1 ∈ q.divisors := by
          rw [mem_divisors]
          exact ⟨one_dvd q, by omega⟩
        have h_mem_q : q ∈ q.divisors := by
          rw [mem_divisors]
          exact ⟨dvd_rfl, by omega⟩
        -- Let's form the Finset s = {1, p, m, q}
        let s : Finset ℕ := {1, p, m, q}
        have h_sub : s ⊆ q.divisors := by
          intro x hx
          simp only [s, mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact h_mem_1
          · exact h_mem_p
          · exact h_mem_m
          · exact h_mem_q
        have h_sum_le : (∑ x ∈ s, x) ≤ (sigma 1 : ArithmeticFunction ℕ) q := by
          have h_le : (∑ x ∈ s, x) ≤ ∑ x ∈ q.divisors, x := sum_le_sum_of_subset h_sub
          rw [sigma_apply]
          simp only [pow_one]
          exact h_le
        -- We want to simplify sum s
        have h_nd : (∑ x ∈ s, x) = 1 + p + m + q := by
          -- Since 1, p, m, q are distinct
          have h1 : 1 ∉ ({p, m, q} : Finset ℕ) := by
            simp only [mem_insert, mem_singleton]
            push_neg
            refine ⟨by omega, by omega, by omega⟩
          have h2 : p ∉ ({m, q} : Finset ℕ) := by
            simp only [mem_insert, mem_singleton]
            push_neg
            refine ⟨h_distinct, by omega⟩
          have h3 : m ∉ ({q} : Finset ℕ) := by
            simp only [mem_singleton]
            exact _root_.ne_of_lt hm_lt_q
          rw [sum_insert h1]
          rw [sum_insert h2]
          rw [sum_insert h3]
          simp only [sum_singleton]
          omega
        rw [h_nd] at h_sum_le
        intro hc
        have hp_cop : Nat.Coprime p 1680 := h_cop.of_dvd_left hp_dvd
        have hm_cop : Nat.Coprime m 1680 := by
          have : m ∣ q := by
            rw [h_eq]
            use p; ring
          exact h_cop.of_dvd_left this
        by_cases hm_prime : Nat.Prime m
        · have h_cop_pm : Nat.Coprime p m := by
            have hd_gcd : Nat.gcd p m = 1 := by
              have h_gcd_dvd_p : Nat.gcd p m ∣ p := Nat.gcd_dvd_left p m
              have h_gcd_dvd_m : Nat.gcd p m ∣ m := Nat.gcd_dvd_right p m
              have h_cases : Nat.gcd p m = 1 ∨ Nat.gcd p m = p := Nat.Prime.eq_one_or_self_of_dvd hp (Nat.gcd p m) h_gcd_dvd_p
              rcases h_cases with h1 | h2
              · exact h1
              · rw [h2] at h_gcd_dvd_m
                have : p = m := (Nat.Prime.eq_one_or_self_of_dvd hm_prime p h_gcd_dvd_m).resolve_left (by omega)
                exact (h_distinct this).elim
            exact hd_gcd
          have h_sig_mul : (sigma 1 : ArithmeticFunction ℕ) (p * m) = (sigma 1 : ArithmeticFunction ℕ) p * (sigma 1 : ArithmeticFunction ℕ) m := by
            exact isMultiplicative_sigma.map_mul_of_coprime h_cop_pm
          have h_sig_p : (sigma 1 : ArithmeticFunction ℕ) p = p + 1 := by
            have h_pow := sigma_one_apply_prime_pow hp (i := 1)
            simp only [pow_one] at h_pow
            rw [h_pow]
            simp [Finset.sum_range_succ]
            ring
          have h_sig_m : (sigma 1 : ArithmeticFunction ℕ) m = m + 1 := by
            have h_pow := sigma_one_apply_prime_pow hm_prime (i := 1)
            simp only [pow_one] at h_pow
            rw [h_pow]
            simp [Finset.sum_range_succ]
            ring
          rw [h_eq] at hc
          rw [h_sig_mul, h_sig_p, h_sig_m] at hc
          have h_ring : (p + 1) * (m + 1) = p * m + p + m + 1 := by ring
          rw [h_ring] at hc
          have h_sub_eq : p * m + p + m + 1 - p * m = p + m + 1 := by omega
          rw [h_sub_eq] at hc
          have h_sum_1679 : p + m = 1679 := by omega
          have hp_odd : p % 2 = 1 := by
            rw [Nat.Prime.mod_two_eq_one_iff_ne_two hp]
            intro hc2
            rw [hc2] at hp_cop
            revert hp_cop
            decide
          have hm_odd : m % 2 = 1 := by
            rw [Nat.Prime.mod_two_eq_one_iff_ne_two hm_prime]
            intro hc2
            rw [hc2] at hm_cop
            revert hm_cop
            decide
          have h_even_sum : (p + m) % 2 = 0 := by omega
          have h_odd_sum : (p + m) % 2 = 1 := by rw [h_sum_1679]
          omega
        · -- m is composite
          have hm_prime_fac := Nat.minFac_prime (by omega : m ≠ 1)
          set r := m.minFac
          have hr_dvd_m : r ∣ m := Nat.minFac_dvd m
          have hr_dvd_q : r ∣ q := by
            rw [h_eq]
            exact dvd_mul_of_dvd_right hr_dvd_m p
          have hr_ge_p : p ≤ r := Nat.minFac_le_of_dvd hm_prime_fac.two_le hr_dvd_q
          have h_div_dvd : r ∣ m := Nat.minFac_dvd m
          have h_div_eq : m = r * (m / r) := (Nat.mul_div_cancel' h_div_dvd).symm
          have h_div_not_one : m / r ≠ 1 := by
            intro h_one
            have : m = r := by rw [h_div_eq, h_one, mul_one]
            rw [this] at hm_prime
            exact hm_prime hm_prime_fac
          have h_div_not_zero : m / r ≠ 0 := by
            intro h_zero
            have h_mul_zero : r * (m / r) = 0 := by rw [h_zero, mul_zero]
            rw [← h_div_eq] at h_mul_zero
            omega
          have h_div_pos : m / r > 0 := Nat.pos_of_ne_zero h_div_not_zero
          have h_div_prime := Nat.minFac_prime h_div_not_one
          have h_div_min_dvd : (m / r).minFac ∣ (m / r) := Nat.minFac_dvd (m / r)
          have h_div_min_dvd_m : (m / r).minFac ∣ m := dvd_trans h_div_min_dvd (Nat.div_dvd_of_dvd hr_dvd_m)
          have h_div_min_ge_r : (m / r).minFac ≥ r := Nat.minFac_le_of_dvd h_div_prime.two_le h_div_min_dvd_m
          have h_div_ge_min : (m / r).minFac ≤ m / r := Nat.minFac_le h_div_pos
          have h_div_ge_r : m / r ≥ r := by omega
          have hm_ge_r2 : m ≥ r * r := by rw [h_div_eq]; exact Nat.mul_le_mul_left r h_div_ge_r
          have h_pr_le_m : p * r ≤ m := by
            calc p * r ≤ r * r := Nat.mul_le_mul_right r hr_ge_p
            _ ≤ m := hm_ge_r2
          by_cases h_pr : p = r
          · by_cases h_cube : q = p ^ 3
            · rw [h_cube] at hc
              have h_sig_cube : (sigma 1 : ArithmeticFunction ℕ) (p^3) = p^3 + p^2 + p + 1 := by
                have h_pow := sigma_one_apply_prime_pow hp (i := 3)
                rw [h_pow]
                simp [Finset.sum_range_succ]
                ring
              rw [h_sig_cube] at hc
              have : p^2 + p + 1 = 1680 := by omega
              have h_ring2 : p * (p + 1) = p^2 + p := by ring
              have h_prod : p * (p + 1) = 1679 := by
                rw [h_ring2]
                omega
              by_cases hp_le40 : p ≤ 40
              · have : p * (p + 1) ≤ 1640 := by
                  interval_cases p <;> decide
                omega
              · have : p * (p + 1) ≥ 1722 := by
                  have h_p_ge41 : p ≥ 41 := by omega
                  have h_p1_ge42 : p + 1 ≥ 42 := by omega
                  exact Nat.mul_le_mul h_p_ge41 h_p1_ge42
                omega
            · have hm_ne_p2 : m ≠ p * p := by
                intro hc_eq
                have : q = p ^ 3 := by
                  rw [h_eq, hc_eq]
                  ring
                exact h_cube this
              rw [← h_pr] at hm_ge_r2
              have hm_gt_p2 : m > p * p := by omega
              have h_mem_p2 : p * p ∈ q.divisors := by
                rw [mem_divisors]
                refine ⟨?_, by omega⟩
                rw [h_eq]
                use m / r
                nth_rw 1 [h_div_eq]
                rw [← h_pr]
                ring
              let s2 : Finset ℕ := {1, p, p * p, m, q}
              have h_sub2 : s2 ⊆ q.divisors := by
                intro x hx
                simp only [s2, mem_insert, mem_singleton] at hx
                rcases hx with rfl | rfl | rfl | rfl | rfl
                · exact h_mem_1
                · exact h_mem_p
                · exact h_mem_p2
                · exact h_mem_m
                · exact h_mem_q
              have hp_lt_p2 : p < p * p := by
                calc p = p * 1 := (Nat.mul_one p).symm
                _ < p * p := Nat.mul_lt_mul_of_pos_left (by omega : 1 < p) (by omega)
              have h_p2_lt_m : p * p < m := hm_gt_p2
              have h_m_lt_q : m < q := hm_lt_q
              have h_sum_le2 : (∑ x ∈ s2, (x : ℕ)) ≤ (sigma 1 : ArithmeticFunction ℕ) q := by
                have h_le : (∑ x ∈ s2, (x : ℕ)) ≤ ∑ x ∈ q.divisors, (x : ℕ) := sum_le_sum_of_subset h_sub2
                rw [sigma_apply]
                simp only [pow_one]
                exact h_le
              have h_nd2 : (∑ x ∈ s2, (x : ℕ)) = 1 + p + p * p + m + q := by
                have h1 : 1 ∉ ({p, p * p, m, q} : Finset ℕ) := by
                  simp only [mem_insert, mem_singleton]; push_neg
                  refine ⟨by omega, by omega, by omega, by omega⟩
                have h2 : p ∉ ({p * p, m, q} : Finset ℕ) := by
                  simp only [mem_insert, mem_singleton]; push_neg
                  refine ⟨by omega, by omega, by omega⟩
                have h3 : p * p ∉ ({m, q} : Finset ℕ) := by
                  simp only [mem_insert, mem_singleton]; push_neg
                  refine ⟨by omega, by omega⟩
                have h4 : m ∉ ({q} : Finset ℕ) := by
                  simp only [mem_singleton]
                  exact _root_.ne_of_lt hm_lt_q
                rw [sum_insert h1, sum_insert h2, sum_insert h3, sum_insert h4]
                simp only [sum_singleton]
                ring
              rw [h_nd2] at h_sum_le2
              have h_sig_eq : (sigma 1 : ArithmeticFunction ℕ) q = q + 1680 := by omega
              have h_sum_sub : 1 + p + p * p + m ≤ 1680 := by omega
              by_cases hp_ge29 : p ≥ 29
              · have hp2_ge841 : p * p ≥ 841 := Nat.mul_le_mul hp_ge29 hp_ge29
                have hm_ge842 : m ≥ 842 := by omega
                omega
              · have hp_ge11 : p ≥ 11 := prime_coprime_1680_ge11 p hp (h_prop.2.of_dvd_left hpg)
                have hp_cases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 := by
                  have h_lt : p < 29 := by omega
                  interval_cases p
                  ·  left; rfl
                  · revert hp; decide
                  · right; left; rfl
                  · revert hp; decide
                  · revert hp; decide
                  · revert hp; decide
                  · right;right; left; rfl
                  · revert hp; decide
                  · right;right;right; left; rfl
                  · revert hp; decide
                  · revert hp; decide
                  · revert hp; decide
                  · right;right;right;right; rfl
                  · revert hp; decide
                  · revert hp; decide
                  · revert hp; decide
                  · revert hp; decide
                  · revert hp; decide

                rcases hp_cases with hp11 | hp13 | hp17 | hp19 | hp23
                · -- p = 11
                  have hp_eq : p = 11 := hp11
                  have hk_le : k ≤ 140 := by
                    have h_sum' := h_sum_sub
                    rw [hp_eq, h_eq_q2] at h_sum'
                    exact le_11 k h_sum'
                  have hk_gt : k > 11 := by
                    have : p < k := hp_lt_k
                    rw [hp_eq] at this
                    exact gt_11 k this
                  have h_mem : k ∈ Finset.Icc (11 + 1) 140 := by
                    rw [Finset.mem_Icc]
                    exact ⟨by omega, hk_le⟩
                  have hc_rw : (sigma 1) q - q = 1680 := hc
                  rw [h_eq, hp_eq, h_eq_q2] at hc_rw
                  have hk_dvd : k ∣ q := by
                    use 11 * 11
                    rw [h_eq, hp_eq, h_eq_q2]
                    ring
                  have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                  exact sec2_dec_11 k h_mem hk_cop hc_rw
                · -- p = 13
                  have hp_eq : p = 13 := hp13
                  have hk_le : k ≤ 115 := by
                    have h_sum' := h_sum_sub
                    rw [hp_eq, h_eq_q2] at h_sum'
                    exact le_13 k h_sum'
                  have hk_gt : k > 13 := by
                    have : p < k := hp_lt_k
                    rw [hp_eq] at this
                    exact gt_13 k this
                  have h_mem : k ∈ Finset.Icc (13 + 1) 115 := by
                    rw [Finset.mem_Icc]
                    exact ⟨by omega, hk_le⟩
                  have hc_rw : (sigma 1) q - q = 1680 := hc
                  rw [h_eq, hp_eq, h_eq_q2] at hc_rw
                  have hk_dvd : k ∣ q := by
                    use 13 * 13
                    rw [h_eq, hp_eq, h_eq_q2]
                    ring
                  have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                  exact sec2_dec_13 k h_mem hk_cop hc_rw
                · -- p = 17
                  have hp_eq : p = 17 := hp17
                  have hk_le : k ≤ 80 := by
                    have h_sum' := h_sum_sub
                    rw [hp_eq, h_eq_q2] at h_sum'
                    exact le_17 k h_sum'
                  have hk_gt : k > 17 := by
                    have : p < k := hp_lt_k
                    rw [hp_eq] at this
                    exact gt_17 k this
                  have h_mem : k ∈ Finset.Icc (17 + 1) 80 := by
                    rw [Finset.mem_Icc]
                    exact ⟨by omega, hk_le⟩
                  have hc_rw : (sigma 1) q - q = 1680 := hc
                  rw [h_eq, hp_eq, h_eq_q2] at hc_rw
                  have hk_dvd : k ∣ q := by
                    use 17 * 17
                    rw [h_eq, hp_eq, h_eq_q2]
                    ring
                  have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                  exact sec2_dec_17 k h_mem hk_cop hc_rw
                · -- p = 19
                  have hp_eq : p = 19 := hp19
                  have hk_le : k ≤ 68 := by
                    have h_sum' := h_sum_sub
                    rw [hp_eq, h_eq_q2] at h_sum'
                    exact le_19 k h_sum'
                  have hk_gt : k > 19 := by
                    have : p < k := hp_lt_k
                    rw [hp_eq] at this
                    exact gt_19 k this
                  have h_mem : k ∈ Finset.Icc (19 + 1) 68 := by
                    rw [Finset.mem_Icc]
                    exact ⟨by omega, hk_le⟩
                  have hc_rw : (sigma 1) q - q = 1680 := hc
                  rw [h_eq, hp_eq, h_eq_q2] at hc_rw
                  have hk_dvd : k ∣ q := by
                    use 19 * 19
                    rw [h_eq, hp_eq, h_eq_q2]
                    ring
                  have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                  exact sec2_dec_19 k h_mem hk_cop hc_rw
                · -- p = 23
                  have hp_eq : p = 23 := hp23
                  have hk_le : k ≤ 49 := by
                    have h_sum' := h_sum_sub
                    rw [hp_eq, h_eq_q2] at h_sum'
                    exact le_23 k h_sum'
                  have hk_gt : k > 23 := by
                    have : p < k := hp_lt_k
                    rw [hp_eq] at this
                    exact gt_23 k this
                  have h_mem : k ∈ Finset.Icc (23 + 1) 49 := by
                    rw [Finset.mem_Icc]
                    exact ⟨by omega, hk_le⟩
                  have hc_rw : (sigma 1) q - q = 1680 := hc
                  rw [h_eq, hp_eq, h_eq_q2] at hc_rw
                  have hk_dvd : k ∣ q := by
                    use 23 * 23
                    rw [h_eq, hp_eq, h_eq_q2]
                    ring
                  have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                  exact sec2_dec_23 k h_mem hk_cop hc_rw

          · have hp_lt_r : p < r := by omega
            by_cases h_prm : p * r = m
            · have h_mem_p2 : p * p ∈ q.divisors := by
                rw [mem_divisors]
                refine ⟨?_, by omega⟩
                rw [h_eq]
                use r
                rw [← h_prm]
                ring
              let s2 : Finset ℕ := {1, p, r, p * p, m, q}
              have h_sub2 : s2 ⊆ q.divisors := by
                intro x hx
                simp only [s2, mem_insert, mem_singleton] at hx
                rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
                · exact h_mem_1
                · exact h_mem_p
                · rw [mem_divisors]
                  refine ⟨?_, by omega⟩
                  rw [h_eq]
                  exact dvd_mul_of_dvd_right hr_dvd_m p
                · exact h_mem_p2
                · exact h_mem_m
                · exact h_mem_q
              have h_sum_le2 : (∑ x ∈ s2, (x : ℕ)) ≤ (sigma 1 : ArithmeticFunction ℕ) q := by
                have h_le : (∑ x ∈ s2, (x : ℕ)) ≤ ∑ x ∈ q.divisors, (x : ℕ) := sum_le_sum_of_subset h_sub2
                rw [sigma_apply]
                simp only [pow_one]
                exact h_le
              have h_nd2 : (∑ x ∈ s2, x) = 1 + p + r + p * p + m + q := by
                have hp_lt_r : p < r := hp_lt_r
                have : p < r := hp_lt_r
                have : p < p * p := by
                  calc p < p * 2 := by omega
                  _ ≤ p * p := Nat.mul_le_mul_left p (by omega)
                have : p < m := by
                  rw [← h_prm]
                  calc p < p * 2 := by omega
                  _ ≤ p * r := Nat.mul_le_mul_left p (by omega)
                have : p < q := by
                  rw [h_eq]
                  calc p < p * 2 := by omega
                  _ ≤ p * m := Nat.mul_le_mul_left p (by omega)
                have : r < m := by
                  rw [← h_prm]
                  have h_le := Nat.mul_le_mul_right r (by omega : 2 ≤ p)
                  rw [mul_comm] at h_le
                  calc r < r * 2 := by omega
                  _ ≤ p * r := h_le
                have : r < q := by
                  calc r < m := by omega
                  _ < q := hm_lt_q
                have : p * p < m := by
                  rw [← h_prm]
                  exact Nat.mul_lt_mul_of_pos_left hp_lt_r (by omega)
                have : p * p < q := by omega
                have h1 : 1 ∉ ({p, r, p * p, m, q} : Finset ℕ) := by
                  simp only [mem_insert, mem_singleton]; push_neg
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                have h2 : p ∉ ({r, p * p, m, q} : Finset ℕ) := by
                  simp only [mem_insert, mem_singleton]; push_neg
                  refine ⟨by omega, by omega, by omega, by omega⟩
                have h3 : r ∉ ({p * p, m, q} : Finset ℕ) := by
                  simp only [mem_insert, mem_singleton]; push_neg
                  have hr_not_p2 : r ≠ p * p := by
                    intro h_eq_p2
                    have hp2_prime : ¬ Nat.Prime (p * p) := by
                      intro hp2
                      have := Nat.Prime.eq_one_or_self_of_dvd hp2 (m := p) (by use p)
                      omega
                    rw [← h_eq_p2] at hp2_prime
                    exact hp2_prime hm_prime_fac
                  refine ⟨hr_not_p2, by omega, by omega⟩
                have h4 : p * p ∉ ({m, q} : Finset ℕ) := by
                  simp only [mem_insert, mem_singleton]; push_neg
                  refine ⟨by omega, by omega⟩
                have h5 : m ∉ ({q} : Finset ℕ) := by
                  simp only [mem_singleton]
                  exact _root_.ne_of_lt hm_lt_q
                rw [sum_insert h1, sum_insert h2, sum_insert h3, sum_insert h4, sum_insert h5]
                simp only [sum_singleton]
                ring
              rw [h_nd2] at h_sum_le2
              have h_sum_sub : 1 + p + r + p * p + m ≤ 1680 := by omega
              by_cases hp_ge29 : p ≥ 29
              · have hp2_ge841 : p * p ≥ 841 := Nat.mul_le_mul hp_ge29 hp_ge29
                have hm_ge842 : m ≥ 842 := by omega
                omega
              · have hp_ge11 : p ≥ 11 := prime_coprime_1680_ge11 p hp (h_prop.2.of_dvd_left hpg)
                have hp_cases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 := by
                  have h_lt : p < 29 := by omega
                  interval_cases p
                  ·  left; rfl
                  · revert hp; decide
                  · right; left; rfl
                  · revert hp; decide
                  · revert hp; decide
                  · revert hp; decide
                  · right;right; left; rfl
                  · revert hp; decide
                  · right;right;right; left; rfl
                  · revert hp; decide
                  · revert hp; decide
                  · revert hp; decide
                  · right;right;right;right; rfl
                  · revert hp; decide
                  · revert hp; decide
                  · revert hp; decide
                  · revert hp; decide
                  · revert hp; decide

                rcases hp_cases with hp11 | hp13 | hp17 | hp19 | hp23
                · -- p = 11
                  have hp_eq : p = 11 := hp11
                  have hr_le : r ≤ 128 := by
                    have h_sum' := h_sum_sub
                    change 1 + p + r + p * p + m ≤ 1680 at h_sum'
                    rw [← h_prm, hp_eq] at h_sum'
                    exact le_prm_11 r h_sum'
                  have hr_gt : r > 11 := by
                    have : p < r := hp_lt_r
                    rw [hp_eq] at this
                    exact gt_prm_11 r this
                  have h_mem : r ∈ Finset.Icc (11 + 1) 128 := by
                    rw [Finset.mem_Icc]
                    exact ⟨by omega, hr_le⟩
                  have hc_rw : (sigma 1) q - q = 1680 := hc
                  rw [h_eq, hp_eq, ← h_prm, hp_eq] at hc_rw
                  have hr_dvd : r ∣ q := by
                    use 11 * 11
                    rw [h_eq, hp_eq, ← h_prm, hp_eq]
                    ring
                  have hr_cop : Nat.Coprime r 1680 := h_prop.2.of_dvd_left hr_dvd
                  exact sec3_dec_11 r h_mem hr_cop hc_rw
                · -- p = 13
                  have hp_eq : p = 13 := hp13
                  have hr_le : r ≤ 106 := by
                    have h_sum' := h_sum_sub
                    change 1 + p + r + p * p + m ≤ 1680 at h_sum'
                    rw [← h_prm, hp_eq] at h_sum'
                    exact le_prm_13 r h_sum'
                  have hr_gt : r > 13 := by
                    have : p < r := hp_lt_r
                    rw [hp_eq] at this
                    exact gt_prm_13 r this
                  have h_mem : r ∈ Finset.Icc (13 + 1) 106 := by
                    rw [Finset.mem_Icc]
                    exact ⟨by omega, hr_le⟩
                  have hc_rw : (sigma 1) q - q = 1680 := hc
                  rw [h_eq, hp_eq, ← h_prm, hp_eq] at hc_rw
                  have hr_dvd : r ∣ q := by
                    use 13 * 13
                    rw [h_eq, hp_eq, ← h_prm, hp_eq]
                    ring
                  have hr_cop : Nat.Coprime r 1680 := h_prop.2.of_dvd_left hr_dvd
                  exact sec3_dec_13 r h_mem hr_cop hc_rw
                · -- p = 17
                  have hp_eq : p = 17 := hp17
                  have hr_le : r ≤ 76 := by
                    have h_sum' := h_sum_sub
                    change 1 + p + r + p * p + m ≤ 1680 at h_sum'
                    rw [← h_prm, hp_eq] at h_sum'
                    exact le_prm_17 r h_sum'
                  have hr_gt : r > 17 := by
                    have : p < r := hp_lt_r
                    rw [hp_eq] at this
                    exact gt_prm_17 r this
                  have h_mem : r ∈ Finset.Icc (17 + 1) 76 := by
                    rw [Finset.mem_Icc]
                    exact ⟨by omega, hr_le⟩
                  have hc_rw : (sigma 1) q - q = 1680 := hc
                  rw [h_eq, hp_eq, ← h_prm, hp_eq] at hc_rw
                  have hr_dvd : r ∣ q := by
                    use 17 * 17
                    rw [h_eq, hp_eq, ← h_prm, hp_eq]
                    ring
                  have hr_cop : Nat.Coprime r 1680 := h_prop.2.of_dvd_left hr_dvd
                  exact sec3_dec_17 r h_mem hr_cop hc_rw
                · -- p = 19
                  have hp_eq : p = 19 := hp19
                  have hr_le : r ≤ 64 := by
                    have h_sum' := h_sum_sub
                    change 1 + p + r + p * p + m ≤ 1680 at h_sum'
                    rw [← h_prm, hp_eq] at h_sum'
                    exact le_prm_19 r h_sum'
                  have hr_gt : r > 19 := by
                    have : p < r := hp_lt_r
                    rw [hp_eq] at this
                    exact gt_prm_19 r this
                  have h_mem : r ∈ Finset.Icc (19 + 1) 64 := by
                    rw [Finset.mem_Icc]
                    exact ⟨by omega, hr_le⟩
                  have hc_rw : (sigma 1) q - q = 1680 := hc
                  rw [h_eq, hp_eq, ← h_prm, hp_eq] at hc_rw
                  have hr_dvd : r ∣ q := by
                    use 19 * 19
                    rw [h_eq, hp_eq, ← h_prm, hp_eq]
                    ring
                  have hr_cop : Nat.Coprime r 1680 := h_prop.2.of_dvd_left hr_dvd
                  exact sec3_dec_19 r h_mem hr_cop hc_rw
                · -- p = 23
                  have hp_eq : p = 23 := hp23
                  have hr_le : r ≤ 46 := by
                    have h_sum' := h_sum_sub
                    change 1 + p + r + p * p + m ≤ 1680 at h_sum'
                    rw [← h_prm, hp_eq] at h_sum'
                    exact le_prm_23 r h_sum'
                  have hr_gt : r > 23 := by
                    have : p < r := hp_lt_r
                    rw [hp_eq] at this
                    exact gt_prm_23 r this
                  have h_mem : r ∈ Finset.Icc (23 + 1) 46 := by
                    rw [Finset.mem_Icc]
                    exact ⟨by omega, hr_le⟩
                  have hc_rw : (sigma 1) q - q = 1680 := hc
                  rw [h_eq, hp_eq, ← h_prm, hp_eq] at hc_rw
                  have hr_dvd : r ∣ q := by
                    use 23 * 23
                    rw [h_eq, hp_eq, ← h_prm, hp_eq]
                    ring
                  have hr_cop : Nat.Coprime r 1680 := h_prop.2.of_dvd_left hr_dvd
                  exact sec3_dec_23 r h_mem hr_cop hc_rw

            · have h_mem_pr : p * r ∈ q.divisors := by
                rw [mem_divisors]
                refine ⟨?_, by omega⟩
                use m / r
                calc q = p * m := h_eq
                _ = p * (r * (m / r)) := congr_arg (fun x => p * x) h_div_eq
                _ = p * r * (m / r) := by ring
              let s2 : Finset ℕ := {1, p, r, p * r, m, q}
              have h_sub2 : s2 ⊆ q.divisors := by
                intro x hx
                simp only [s2, mem_insert, mem_singleton] at hx
                rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
                · exact h_mem_1
                · exact h_mem_p
                · rw [mem_divisors]
                  refine ⟨?_, by omega⟩
                  rw [h_eq]
                  exact dvd_mul_of_dvd_right hr_dvd_m p
                · exact h_mem_pr
                · exact h_mem_m
                · exact h_mem_q
              have h_sum_le2 : (∑ x ∈ s2, (x : ℕ)) ≤ (sigma 1 : ArithmeticFunction ℕ) q := by
                have h_le : (∑ x ∈ s2, (x : ℕ)) ≤ ∑ x ∈ q.divisors, (x : ℕ) := sum_le_sum_of_subset h_sub2
                rw [sigma_apply]
                simp only [pow_one]
                exact h_le
              have h_nd2 : (∑ x ∈ s2, x) = 1 + p + r + p * r + m + q := by
                have hp_ge2 : 2 ≤ p := by omega
                have hr_ge2 : 2 ≤ r := by omega
                have : p < r := hp_lt_r
                have : p < p * r := by
                  calc p < p * 2 := by omega
                  _ = p * 2 := by rfl
                  _ ≤ p * r := Nat.mul_le_mul_left p hr_ge2
                have : p < m := by
                  calc p < p * r := by omega
                  _ < m := Nat.lt_of_le_of_ne h_pr_le_m h_prm
                have : p < q := by
                  rw [h_eq]
                  calc p < p * 2 := by omega
                  _ = p * 2 := by rfl
                  _ ≤ p * m := Nat.mul_le_mul_left p (by omega : 2 ≤ m)
                have : r < p * r := by
                  calc r < r * 2 := by omega
                  _ = 2 * r := by ring
                  _ ≤ p * r := Nat.mul_le_mul_right r hp_ge2
                have : r < m := by
                  calc r < p * r := by omega
                  _ < m := Nat.lt_of_le_of_ne h_pr_le_m h_prm
                have : r < q := by
                  calc r < m := by omega
                  _ < q := hm_lt_q
                have : p * r < m := Nat.lt_of_le_of_ne h_pr_le_m h_prm
                have : p * r < q := by omega
                have h1 : 1 ∉ ({p, r, p * r, m, q} : Finset ℕ) := by
                  simp only [mem_insert, mem_singleton]; push_neg
                  refine ⟨by omega, by omega, by omega, by omega, by omega⟩
                have h2 : p ∉ ({r, p * r, m, q} : Finset ℕ) := by
                  simp only [mem_insert, mem_singleton]; push_neg
                  refine ⟨by omega, by omega, by omega, by omega⟩
                have h3 : r ∉ ({p * r, m, q} : Finset ℕ) := by
                  simp only [mem_insert, mem_singleton]; push_neg
                  refine ⟨by omega, by omega, by omega⟩
                have h4 : p * r ∉ ({m, q} : Finset ℕ) := by
                  simp only [mem_insert, mem_singleton]; push_neg
                  refine ⟨by omega, by omega⟩
                have h5 : m ∉ ({q} : Finset ℕ) := by
                  simp only [mem_singleton]
                  exact _root_.ne_of_lt hm_lt_q
                rw [sum_insert h1, sum_insert h2, sum_insert h3, sum_insert h4, sum_insert h5]
                simp only [sum_singleton]
                ring
              rw [h_nd2] at h_sum_le2
              have h_sum_sub : 1 + p + r + p * r + m ≤ 1680 := by omega
              have hp_ge5 : p ≥ 5 := hp_ge
              have h_cop_r : Nat.Coprime r 1680 := h_cop.of_dvd_left hr_dvd_q
              have hr_ge41 : r ≥ 41 := by
                by_contra hc_r
                have hr_lt41 : r < 41 := by omega
                interval_cases r
                · revert hm_prime_fac; decide
                · revert hm_prime_fac; decide
                · revert h_cop_r; decide
                · revert h_cop_r; decide
                · revert hm_prime_fac; decide
                · revert h_cop_r; decide
                · revert hm_prime_fac; decide
                · revert h_cop_r; decide
                · revert hm_prime_fac; decide
                · revert hm_prime_fac; decide
                · revert hm_prime_fac; decide
                · -- r = 11
                  have hr_eq : r = 11 := rfl
                  have hp_lt_R : p < 11 := by rw [← hr_eq]; exact hp_lt_r
                  interval_cases p
                  · -- p = 0 not prime/coprime
                    revert hp; decide
                  · -- p = 1 not prime/coprime
                    revert hp; decide
                  · -- p = 2 not prime/coprime
                    revert hp; decide
                  · -- p = 3 not prime/coprime
                    revert hp; decide
                  · -- p = 4 not prime/coprime
                    revert hp; decide
                  · -- p = 5 not prime/coprime
                    revert hp; decide
                  · -- p = 6 not prime/coprime
                    revert hp; decide
                  · -- p = 7 not prime/coprime
                    revert hp; decide
                  · -- p = 8 not prime/coprime
                    revert hp; decide
                  · -- p = 9 not prime/coprime
                    revert hp; decide
                  · -- p = 10 not prime/coprime
                    revert hp; decide
                · -- r = 13
                  have hr_eq : r = 13 := rfl
                  have hp_lt_R : p < 13 := by rw [← hr_eq]; exact hp_lt_r
                  interval_cases p
                  · -- p = 11
                    have hp_eq : p = 11 := rfl
                    have h_rm : 13 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 116 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_11_13 k h_sum'
                    have hk_ge : k ≥ 13 := by
                      have h_min : 13 ≤ (m / 13).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 13 116 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 11 * 13
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_11_13 k h_mem hk_cop hc_rw
                  · -- p = 0 not prime/coprime
                    revert hp; decide
                  · -- p = 1 not prime/coprime
                    revert hp; decide
                  · -- p = 2 not prime/coprime
                    revert hp; decide
                  · -- p = 3 not prime/coprime
                    revert hp; decide
                  · -- p = 4 not prime/coprime
                    revert hp; decide
                  · -- p = 5 not prime/coprime
                    revert hp; decide
                  · -- p = 6 not prime/coprime
                    revert hp; decide
                  · -- p = 7 not prime/coprime
                    revert hp; decide
                  · -- p = 8 not prime/coprime
                    revert hp; decide
                  · -- p = 9 not prime/coprime
                    revert hp; decide
                  · -- p = 10 not prime/coprime
                    revert hp; decide
                  · -- p = 12 not prime/coprime
                    revert hp; decide
                · -- r = 17
                  have hr_eq : r = 17 := rfl
                  have hp_lt_R : p < 17 := by rw [← hr_eq]; exact hp_lt_r
                  interval_cases p
                  · -- p = 11
                    have hp_eq : p = 11 := rfl
                    have h_rm : 17 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 86 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_11_17 k h_sum'
                    have hk_ge : k ≥ 17 := by
                      have h_min : 17 ≤ (m / 17).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 17 86 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 11 * 17
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_11_17 k h_mem hk_cop hc_rw
                  · -- p = 13
                    have hp_eq : p = 13 := rfl
                    have h_rm : 17 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 84 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_13_17 k h_sum'
                    have hk_ge : k ≥ 17 := by
                      have h_min : 17 ≤ (m / 17).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 17 84 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 13 * 17
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_13_17 k h_mem hk_cop hc_rw
                  · -- p = 0 not prime/coprime
                    revert hp; decide
                  · -- p = 1 not prime/coprime
                    revert hp; decide
                  · -- p = 2 not prime/coprime
                    revert hp; decide
                  · -- p = 3 not prime/coprime
                    revert hp; decide
                  · -- p = 4 not prime/coprime
                    revert hp; decide
                  · -- p = 5 not prime/coprime
                    revert hp; decide
                  · -- p = 6 not prime/coprime
                    revert hp; decide
                  · -- p = 7 not prime/coprime
                    revert hp; decide
                  · -- p = 8 not prime/coprime
                    revert hp; decide
                  · -- p = 9 not prime/coprime
                    revert hp; decide
                  · -- p = 10 not prime/coprime
                    revert hp; decide
                  · -- p = 12 not prime/coprime
                    revert hp; decide
                  · -- p = 14 not prime/coprime
                    revert hp; decide
                  · -- p = 15 not prime/coprime
                    revert hp; decide
                  · -- p = 16 not prime/coprime
                    revert hp; decide
                · -- r = 19
                  have hr_eq : r = 19 := rfl
                  have hp_lt_R : p < 19 := by rw [← hr_eq]; exact hp_lt_r
                  interval_cases p
                  · -- p = 11
                    have hp_eq : p = 11 := rfl
                    have h_rm : 19 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 75 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_11_19 k h_sum'
                    have hk_ge : k ≥ 19 := by
                      have h_min : 19 ≤ (m / 19).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 19 75 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 11 * 19
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_11_19 k h_mem hk_cop hc_rw
                  · -- p = 13
                    have hp_eq : p = 13 := rfl
                    have h_rm : 19 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 73 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_13_19 k h_sum'
                    have hk_ge : k ≥ 19 := by
                      have h_min : 19 ≤ (m / 19).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 19 73 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 13 * 19
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_13_19 k h_mem hk_cop hc_rw
                  · -- p = 17
                    have hp_eq : p = 17 := rfl
                    have h_rm : 19 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 69 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_17_19 k h_sum'
                    have hk_ge : k ≥ 19 := by
                      have h_min : 19 ≤ (m / 19).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 19 69 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 17 * 19
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_17_19 k h_mem hk_cop hc_rw
                  · -- p = 0 not prime/coprime
                    revert hp; decide
                  · -- p = 1 not prime/coprime
                    revert hp; decide
                  · -- p = 2 not prime/coprime
                    revert hp; decide
                  · -- p = 3 not prime/coprime
                    revert hp; decide
                  · -- p = 4 not prime/coprime
                    revert hp; decide
                  · -- p = 5 not prime/coprime
                    revert hp; decide
                  · -- p = 6 not prime/coprime
                    revert hp; decide
                  · -- p = 7 not prime/coprime
                    revert hp; decide
                  · -- p = 8 not prime/coprime
                    revert hp; decide
                  · -- p = 9 not prime/coprime
                    revert hp; decide
                  · -- p = 10 not prime/coprime
                    revert hp; decide
                  · -- p = 12 not prime/coprime
                    revert hp; decide
                  · -- p = 14 not prime/coprime
                    revert hp; decide
                  · -- p = 15 not prime/coprime
                    revert hp; decide
                  · -- p = 16 not prime/coprime
                    revert hp; decide
                  · -- p = 18 not prime/coprime
                    revert hp; decide
                · -- r = 23
                  have hr_eq : r = 23 := rfl
                  have hp_lt_R : p < 23 := by rw [← hr_eq]; exact hp_lt_r
                  interval_cases p
                  · -- p = 11
                    have hp_eq : p = 11 := rfl
                    have h_rm : 23 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 60 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_11_23 k h_sum'
                    have hk_ge : k ≥ 23 := by
                      have h_min : 23 ≤ (m / 23).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 23 60 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 11 * 23
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_11_23 k h_mem hk_cop hc_rw
                  · -- p = 13
                    have hp_eq : p = 13 := rfl
                    have h_rm : 23 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 58 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_13_23 k h_sum'
                    have hk_ge : k ≥ 23 := by
                      have h_min : 23 ≤ (m / 23).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 23 58 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 13 * 23
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_13_23 k h_mem hk_cop hc_rw
                  · -- p = 17
                    have hp_eq : p = 17 := rfl
                    have h_rm : 23 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 54 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_17_23 k h_sum'
                    have hk_ge : k ≥ 23 := by
                      have h_min : 23 ≤ (m / 23).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 23 54 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 17 * 23
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_17_23 k h_mem hk_cop hc_rw
                  · -- p = 19
                    have hp_eq : p = 19 := rfl
                    have h_rm : 23 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 52 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_19_23 k h_sum'
                    have hk_ge : k ≥ 23 := by
                      have h_min : 23 ≤ (m / 23).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 23 52 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 19 * 23
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_19_23 k h_mem hk_cop hc_rw
                  · -- p = 0 not prime/coprime
                    revert hp; decide
                  · -- p = 1 not prime/coprime
                    revert hp; decide
                  · -- p = 2 not prime/coprime
                    revert hp; decide
                  · -- p = 3 not prime/coprime
                    revert hp; decide
                  · -- p = 4 not prime/coprime
                    revert hp; decide
                  · -- p = 5 not prime/coprime
                    revert hp; decide
                  · -- p = 6 not prime/coprime
                    revert hp; decide
                  · -- p = 7 not prime/coprime
                    revert hp; decide
                  · -- p = 8 not prime/coprime
                    revert hp; decide
                  · -- p = 9 not prime/coprime
                    revert hp; decide
                  · -- p = 10 not prime/coprime
                    revert hp; decide
                  · -- p = 12 not prime/coprime
                    revert hp; decide
                  · -- p = 14 not prime/coprime
                    revert hp; decide
                  · -- p = 15 not prime/coprime
                    revert hp; decide
                  · -- p = 16 not prime/coprime
                    revert hp; decide
                  · -- p = 18 not prime/coprime
                    revert hp; decide
                  · -- p = 20 not prime/coprime
                    revert hp; decide
                  · -- p = 21 not prime/coprime
                    revert hp; decide
                  · -- p = 22 not prime/coprime
                    revert hp; decide
                · -- r = 29
                  have hr_eq : r = 29 := rfl
                  have hp_lt_R : p < 29 := by rw [← hr_eq]; exact hp_lt_r
                  interval_cases p
                  · -- p = 11
                    have hp_eq : p = 11 := rfl
                    have h_rm : 29 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 45 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_11_29 k h_sum'
                    have hk_ge : k ≥ 29 := by
                      have h_min : 29 ≤ (m / 29).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 29 45 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 11 * 29
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_11_29 k h_mem hk_cop hc_rw
                  · -- p = 13
                    have hp_eq : p = 13 := rfl
                    have h_rm : 29 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 43 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_13_29 k h_sum'
                    have hk_ge : k ≥ 29 := by
                      have h_min : 29 ≤ (m / 29).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 29 43 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 13 * 29
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_13_29 k h_mem hk_cop hc_rw
                  · -- p = 17
                    have hp_eq : p = 17 := rfl
                    have h_rm : 29 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 39 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_17_29 k h_sum'
                    have hk_ge : k ≥ 29 := by
                      have h_min : 29 ≤ (m / 29).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 29 39 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 17 * 29
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_17_29 k h_mem hk_cop hc_rw
                  · -- p = 19
                    have hp_eq : p = 19 := rfl
                    have h_rm : 29 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 37 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_19_29 k h_sum'
                    have hk_ge : k ≥ 29 := by
                      have h_min : 29 ≤ (m / 29).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 29 37 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 19 * 29
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_19_29 k h_mem hk_cop hc_rw
                  · -- p = 23
                    have hp_eq : p = 23 := rfl
                    have h_rm : 29 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 33 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_23_29 k h_sum'
                    have hk_ge : k ≥ 29 := by
                      have h_min : 29 ≤ (m / 29).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 29 33 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 23 * 29
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_23_29 k h_mem hk_cop hc_rw
                  · -- p = 0 not prime/coprime
                    revert hp; decide
                  · -- p = 1 not prime/coprime
                    revert hp; decide
                  · -- p = 2 not prime/coprime
                    revert hp; decide
                  · -- p = 3 not prime/coprime
                    revert hp; decide
                  · -- p = 4 not prime/coprime
                    revert hp; decide
                  · -- p = 5 not prime/coprime
                    revert hp; decide
                  · -- p = 6 not prime/coprime
                    revert hp; decide
                  · -- p = 7 not prime/coprime
                    revert hp; decide
                  · -- p = 8 not prime/coprime
                    revert hp; decide
                  · -- p = 9 not prime/coprime
                    revert hp; decide
                  · -- p = 10 not prime/coprime
                    revert hp; decide
                  · -- p = 12 not prime/coprime
                    revert hp; decide
                  · -- p = 14 not prime/coprime
                    revert hp; decide
                  · -- p = 15 not prime/coprime
                    revert hp; decide
                  · -- p = 16 not prime/coprime
                    revert hp; decide
                  · -- p = 18 not prime/coprime
                    revert hp; decide
                  · -- p = 20 not prime/coprime
                    revert hp; decide
                  · -- p = 21 not prime/coprime
                    revert hp; decide
                  · -- p = 22 not prime/coprime
                    revert hp; decide
                  · -- p = 24 not prime/coprime
                    revert hp; decide
                  · -- p = 25 not prime/coprime
                    revert hp; decide
                  · -- p = 26 not prime/coprime
                    revert hp; decide
                  · -- p = 27 not prime/coprime
                    revert hp; decide
                  · -- p = 28 not prime/coprime
                    revert hp; decide
                · -- r = 31
                  have hr_eq : r = 31 := rfl
                  have hp_lt_R : p < 31 := by rw [← hr_eq]; exact hp_lt_r
                  interval_cases p
                  · -- p = 11
                    have hp_eq : p = 11 := rfl
                    have h_rm : 31 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 41 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_11_31 k h_sum'
                    have hk_ge : k ≥ 31 := by
                      have h_min : 31 ≤ (m / 31).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 31 41 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 11 * 31
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_11_31 k h_mem hk_cop hc_rw
                  · -- p = 13
                    have hp_eq : p = 13 := rfl
                    have h_rm : 31 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 39 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_13_31 k h_sum'
                    have hk_ge : k ≥ 31 := by
                      have h_min : 31 ≤ (m / 31).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 31 39 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 13 * 31
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_13_31 k h_mem hk_cop hc_rw
                  · -- p = 17
                    have hp_eq : p = 17 := rfl
                    have h_rm : 31 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 35 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_17_31 k h_sum'
                    have hk_ge : k ≥ 31 := by
                      have h_min : 31 ≤ (m / 31).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 31 35 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 17 * 31
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_17_31 k h_mem hk_cop hc_rw
                  · -- p = 19
                    have hp_eq : p = 19 := rfl
                    have h_rm : 31 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 33 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_19_31 k h_sum'
                    have hk_ge : k ≥ 31 := by
                      have h_min : 31 ≤ (m / 31).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 31 33 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 19 * 31
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_19_31 k h_mem hk_cop hc_rw
                  · -- p = 23
                    have hp_eq : p = 23 := rfl
                    have h_rm : 31 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 29 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_23_31 k h_sum'
                    have hk_ge : k ≥ 31 := by
                      have h_min : 31 ≤ (m / 31).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 31 29 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 23 * 31
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_23_31 k h_mem hk_cop hc_rw
                  · -- p = 29
                    have hp_eq : p = 29 := rfl
                    have h_rm : 31 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 23 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_29_31 k h_sum'
                    have hk_ge : k ≥ 31 := by
                      have h_min : 31 ≤ (m / 31).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 31 23 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 29 * 31
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_29_31 k h_mem hk_cop hc_rw
                  · -- p = 0 not prime/coprime
                    revert hp; decide
                  · -- p = 1 not prime/coprime
                    revert hp; decide
                  · -- p = 2 not prime/coprime
                    revert hp; decide
                  · -- p = 3 not prime/coprime
                    revert hp; decide
                  · -- p = 4 not prime/coprime
                    revert hp; decide
                  · -- p = 5 not prime/coprime
                    revert hp; decide
                  · -- p = 6 not prime/coprime
                    revert hp; decide
                  · -- p = 7 not prime/coprime
                    revert hp; decide
                  · -- p = 8 not prime/coprime
                    revert hp; decide
                  · -- p = 9 not prime/coprime
                    revert hp; decide
                  · -- p = 10 not prime/coprime
                    revert hp; decide
                  · -- p = 12 not prime/coprime
                    revert hp; decide
                  · -- p = 14 not prime/coprime
                    revert hp; decide
                  · -- p = 15 not prime/coprime
                    revert hp; decide
                  · -- p = 16 not prime/coprime
                    revert hp; decide
                  · -- p = 18 not prime/coprime
                    revert hp; decide
                  · -- p = 20 not prime/coprime
                    revert hp; decide
                  · -- p = 21 not prime/coprime
                    revert hp; decide
                  · -- p = 22 not prime/coprime
                    revert hp; decide
                  · -- p = 24 not prime/coprime
                    revert hp; decide
                  · -- p = 25 not prime/coprime
                    revert hp; decide
                  · -- p = 26 not prime/coprime
                    revert hp; decide
                  · -- p = 27 not prime/coprime
                    revert hp; decide
                  · -- p = 28 not prime/coprime
                    revert hp; decide
                  · -- p = 30 not prime/coprime
                    revert hp; decide
                · -- r = 37
                  have hr_eq : r = 37 := rfl
                  have hp_lt_R : p < 37 := by rw [← hr_eq]; exact hp_lt_r
                  interval_cases p
                  · -- p = 11
                    have hp_eq : p = 11 := rfl
                    have h_rm : 37 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 33 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_11_37 k h_sum'
                    have hk_ge : k ≥ 37 := by
                      have h_min : 37 ≤ (m / 37).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 37 33 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 11 * 37
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_11_37 k h_mem hk_cop hc_rw
                  · -- p = 13
                    have hp_eq : p = 13 := rfl
                    have h_rm : 37 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 31 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_13_37 k h_sum'
                    have hk_ge : k ≥ 37 := by
                      have h_min : 37 ≤ (m / 37).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 37 31 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 13 * 37
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_13_37 k h_mem hk_cop hc_rw
                  · -- p = 17
                    have hp_eq : p = 17 := rfl
                    have h_rm : 37 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 26 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_17_37 k h_sum'
                    have hk_ge : k ≥ 37 := by
                      have h_min : 37 ≤ (m / 37).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 37 26 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 17 * 37
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_17_37 k h_mem hk_cop hc_rw
                  · -- p = 19
                    have hp_eq : p = 19 := rfl
                    have h_rm : 37 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 24 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_19_37 k h_sum'
                    have hk_ge : k ≥ 37 := by
                      have h_min : 37 ≤ (m / 37).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 37 24 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 19 * 37
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_19_37 k h_mem hk_cop hc_rw
                  · -- p = 23
                    have hp_eq : p = 23 := rfl
                    have h_rm : 37 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 20 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_23_37 k h_sum'
                    have hk_ge : k ≥ 37 := by
                      have h_min : 37 ≤ (m / 37).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 37 20 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 23 * 37
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_23_37 k h_mem hk_cop hc_rw
                  · -- p = 29
                    have hp_eq : p = 29 := rfl
                    have h_rm : 37 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 14 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_29_37 k h_sum'
                    have hk_ge : k ≥ 37 := by
                      have h_min : 37 ≤ (m / 37).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 37 14 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 29 * 37
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_29_37 k h_mem hk_cop hc_rw
                  · -- p = 31
                    have hp_eq : p = 31 := rfl
                    have h_rm : 37 ∣ m := by rw [hr_eq] at hr_dvd_m; exact hr_dvd_m
                    set k := m / r
                    have h_m_eq : m = r * k := (Nat.mul_div_cancel' h_rm).symm
                    have hk_le : k ≤ 12 := by
                      have h_sum' := h_sum_sub
                      rw [hp_eq, hr_eq, h_m_eq, hr_eq] at h_sum'
                      exact le_pair_31_37 k h_sum'
                    have hk_ge : k ≥ 37 := by
                      have h_min : 37 ≤ (m / 37).minFac := by
                        rw [← hr_eq]
                        exact h_div_min_ge_r
                      have h_le_min := Nat.minFac_le (by
                        by_contra hc_zero
                        have : m = 0 := by rw [h_m_eq, hc_zero, mul_zero]
                        omega)
                      omega
                    have h_mem : k ∈ Finset.Icc 37 12 := by
                      rw [Finset.mem_Icc]
                      exact ⟨hk_ge, hk_le⟩
                    have hc_rw : (sigma 1) q - q = 1680 := hc
                    rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq] at hc_rw
                    have hk_dvd : k ∣ q := by
                      use 31 * 37
                      rw [h_eq, hp_eq, hr_eq, h_m_eq, hr_eq]
                      ring
                    have hk_cop : Nat.Coprime k 1680 := h_prop.2.of_dvd_left hk_dvd
                    exact sec4_dec_31_37 k h_mem hk_cop hc_rw
                  · -- p = 0 not prime/coprime
                    revert hp; decide
                  · -- p = 1 not prime/coprime
                    revert hp; decide
                  · -- p = 2 not prime/coprime
                    revert hp; decide
                  · -- p = 3 not prime/coprime
                    revert hp; decide
                  · -- p = 4 not prime/coprime
                    revert hp; decide
                  · -- p = 5 not prime/coprime
                    revert hp; decide
                  · -- p = 6 not prime/coprime
                    revert hp; decide
                  · -- p = 7 not prime/coprime
                    revert hp; decide
                  · -- p = 8 not prime/coprime
                    revert hp; decide
                  · -- p = 9 not prime/coprime
                    revert hp; decide
                  · -- p = 10 not prime/coprime
                    revert hp; decide
                  · -- p = 12 not prime/coprime
                    revert hp; decide
                  · -- p = 14 not prime/coprime
                    revert hp; decide
                  · -- p = 15 not prime/coprime
                    revert hp; decide
                  · -- p = 16 not prime/coprime
                    revert hp; decide
                  · -- p = 18 not prime/coprime
                    revert hp; decide
                  · -- p = 20 not prime/coprime
                    revert hp; decide
                  · -- p = 21 not prime/coprime
                    revert hp; decide
                  · -- p = 22 not prime/coprime
                    revert hp; decide
                  · -- p = 24 not prime/coprime
                    revert hp; decide
                  · -- p = 25 not prime/coprime
                    revert hp; decide
                  · -- p = 26 not prime/coprime
                    revert hp; decide
                  · -- p = 27 not prime/coprime
                    revert hp; decide
                  · -- p = 28 not prime/coprime
                    revert hp; decide
                  · -- p = 30 not prime/coprime
                    revert hp; decide
                  · -- p = 32 not prime/coprime
                    revert hp; decide
                  · -- p = 33 not prime/coprime
                    revert hp; decide
                  · -- p = 34 not prime/coprime
                    revert hp; decide
                  · -- p = 35 not prime/coprime
                    revert hp; decide
                  · -- p = 36 not prime/coprime
                    revert hp; decide
              have hp_ge5 : p ≥ 5 := hp_ge
              have h_pr_ge : p * r ≥ 205 := Nat.mul_le_mul hp_ge5 hr_ge41
              have hr2_ge : r * r ≥ 1681 := Nat.mul_le_mul hr_ge41 hr_ge41
              have hm_ge1681 : m ≥ 1681 := by omega
              omega



theorem val_eq_div_gcd {i : ℕ} (hi : 0 < i) :
    A243473_val i = ((sigma 1 i) - i) / Nat.gcd (sigma 1 i) i := by
  unfold A243473_val
  have hi_ne0 : i ≠ 0 := by omega
  simp only [hi_ne0, ↓reduceIte]
  
  set s := (sigma 1 i : ℕ)
  set g := Nat.gcd s i
  
  have h_i_div_g : g ∣ i := Nat.gcd_dvd_right s i
  have h_s_div_g : g ∣ s := Nat.gcd_dvd_left s i
  
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right s hi
  have hg_ne0 : g ≠ 0 := by omega
  
  set s' := s / g
  set i' := i / g
  
  have hs_eq : s = g * s' := (Nat.mul_div_cancel' h_s_div_g).symm
  have hi_eq : i = g * i' := (Nat.mul_div_cancel' h_i_div_g).symm
  
  have h_cop : s'.Coprime i' := by
    exact Nat.coprime_div_gcd_div_gcd hg_pos
  
  have h_div_eq : ((s : Rat) / (i : Rat)) = ((s' : ℤ) : Rat) / ((i' : ℤ) : Rat) := by
    push_cast
    have hg_pos_rat : (g : Rat) ≠ 0 := by positivity
    have hi'_pos_rat : (i' : Rat) ≠ 0 := by
      have : i' > 0 := Nat.div_pos (Nat.gcd_le_right s hi) hg_pos
      positivity
    rw [hs_eq, hi_eq]
    push_cast
    field_simp

  have hb0 : 0 < (i' : ℤ) := by
    have : i' > 0 := Nat.div_pos (Nat.gcd_le_right s hi) hg_pos
    positivity

  have h_cop_z : Nat.Coprime (Int.natAbs (s' : ℤ)) (Int.natAbs (i' : ℤ)) := by
    exact h_cop

  have h_num := Rat.num_div_eq_of_coprime hb0 h_cop_z
  have h_den := Rat.den_div_eq_of_coprime hb0 h_cop_z

  rw [h_div_eq]
  have h_num' : (((s' : ℤ) : Rat) / ((i' : ℤ) : Rat)).num = s' := h_num
  have h_den' : (((s' : ℤ) : Rat) / ((i' : ℤ) : Rat)).den = i' := by
    have h_den_z : ((((s' : ℤ) : Rat) / ((i' : ℤ) : Rat)).den : ℤ) = i' := h_den
    exact_mod_cast h_den_z

  rw [h_num', h_den']
  have h_sub_pos : i ≤ s := by
    change i ≤ (sigma 1 i : ℕ)
    rw [sigma_apply]
    simp only [pow_one]
    have h_div_self : i ∈ i.divisors := by
      rw [mem_divisors]
      refine ⟨by simp, hi_ne0⟩
    have h_single := Finset.single_le_sum (fun d _ => Nat.zero_le d) h_div_self
    exact h_single

  have h_sub_eq : (s' : ℤ) - i' = ((s : ℤ) - i) / g := by
    have hs_eq' : (s : ℤ) = g * s' := by exact_mod_cast hs_eq
    have hi_eq' : (i : ℤ) = g * i' := by exact_mod_cast hi_eq
    rw [hs_eq', hi_eq']
    rw [← mul_sub_left_distrib]
    have hg_ne0' : (g : ℤ) ≠ 0 := by positivity
    rw [Int.mul_ediv_cancel_left (s' - i') hg_ne0']

  rw [h_sub_eq]
  rw [← Int.natCast_sub h_sub_pos]
  rw [← Int.natCast_div (s - i) g]
  exact Int.toNat_natCast ((s - i) / g)

theorem val_ge_sigma_sub {i : ℕ} (hi : 0 < i) :
    A243473_val i ≥ (sigma 1 (i / Nat.gcd (sigma 1 i) i)) - (i / Nat.gcd (sigma 1 i) i) := by
  set s := (sigma 1 i : ℕ)
  set g := Nat.gcd s i
  set q := i / g
  
  have hi_ne0 : i ≠ 0 := by omega
  have h_i_div_g : g ∣ i := Nat.gcd_dvd_right s i
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right s hi
  
  have hq_pos : 0 < q := by
    have h_eq : g * q = i := Nat.mul_div_cancel' h_i_div_g
    have : 0 < g * q := by omega
    rw [mul_comm] at this
    exact Nat.pos_of_mul_pos_right this
    
  have h_sigma_mul := sigma_mul_ge g q (by omega) (by omega)
  have h_eq : g * q = i := Nat.mul_div_cancel' h_i_div_g
  rw [h_eq] at h_sigma_mul
  
  rw [val_eq_div_gcd hi]
  change (sigma 1 q) - q ≤ (s - i) / g
  rw [Nat.le_div_iff_mul_le hg_pos]
  rw [mul_comm]
  rw [Nat.mul_sub_left_distrib]
  rw [← h_eq]
  exact Nat.sub_le_sub_right h_sigma_mul (g * q)

theorem val_366_properties {i : ℕ} (hi : 0 < i) (h_val : A243473_val i = 366) :
    let s := (sigma 1 i : ℕ)
    let g := Nat.gcd s i
    let q := i / g
    (sigma 1 q - q ≤ 366) ∧ (Nat.Coprime q 366) := by
  intro s g q
  have h_val_eq := val_eq_div_gcd hi
  rw [h_val] at h_val_eq
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right (sigma 1 i : ℕ) hi
  have h_sub_pos : i ≤ (sigma 1 i : ℕ) := by
    change i ≤ (sigma 1 i : ℕ)
    rw [sigma_apply]
    simp only [pow_one]
    have h_div_self : i ∈ i.divisors := by
      rw [mem_divisors]
      refine ⟨by simp, _root_.ne_of_gt hi⟩
    have h_single := Finset.single_le_sum (fun d _ => Nat.zero_le d) h_div_self
    exact h_single
  have h_gcd_sub : g = Nat.gcd (sigma 1 i - i) i := by
    change (sigma 1 i).gcd i = (sigma 1 i - i).gcd i
    have hs_eq : sigma 1 i = (sigma 1 i - i) + i := (Nat.sub_add_cancel h_sub_pos).symm
    nth_rw 1 [hs_eq]
    rw [Nat.gcd_add_self_left]
  have h_cop : Nat.Coprime ((sigma 1 i - i) / g) (i / g) := by
    rw [h_gcd_sub]
    exact Nat.coprime_div_gcd_div_gcd (by rw [← h_gcd_sub]; exact hg_pos)
  have h_cop' : Nat.Coprime 366 q := by
    change Nat.Coprime 366 (i / g)
    rw [h_val_eq]
    exact h_cop
  refine ⟨?_, h_cop'.symm⟩
  have h_ge := val_ge_sigma_sub hi
  rw [h_val] at h_ge
  exact h_ge

theorem val_1680_properties {i : ℕ} (hi : 0 < i) (h_val : A243473_val i = 1680) :
    let s := (sigma 1 i : ℕ)
    let g := Nat.gcd s i
    let q := i / g
    (sigma 1 q - q ≤ 1680) ∧ (Nat.Coprime q 1680) := by
  intro s g q
  have h_val_eq := val_eq_div_gcd hi
  rw [h_val] at h_val_eq
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right (sigma 1 i : ℕ) hi
  have h_sub_pos : i ≤ (sigma 1 i : ℕ) := by
    change i ≤ (sigma 1 i : ℕ)
    rw [sigma_apply]
    simp only [pow_one]
    have h_div_self : i ∈ i.divisors := by
      rw [mem_divisors]
      refine ⟨by simp, _root_.ne_of_gt hi⟩
    have h_single := Finset.single_le_sum (fun d _ => Nat.zero_le d) h_div_self
    exact h_single
  have h_gcd_sub : g = Nat.gcd (sigma 1 i - i) i := by
    change (sigma 1 i).gcd i = (sigma 1 i - i).gcd i
    have hs_eq : sigma 1 i = (sigma 1 i - i) + i := (Nat.sub_add_cancel h_sub_pos).symm
    nth_rw 1 [hs_eq]
    rw [Nat.gcd_add_self_left]
  have h_cop : Nat.Coprime ((sigma 1 i - i) / g) (i / g) := by
    rw [h_gcd_sub]
    exact Nat.coprime_div_gcd_div_gcd (by rw [← h_gcd_sub]; exact hg_pos)
  have h_cop' : Nat.Coprime 1680 q := by
    change Nat.Coprime 1680 (i / g)
    rw [h_val_eq]
    exact h_cop
  refine ⟨?_, h_cop'.symm⟩
  have h_ge := val_ge_sigma_sub hi
  rw [h_val] at h_ge
  exact h_ge

theorem val_eq_sigma_mul {i : ℕ} (hi : 0 < i) (h_val : A243473_val i = 1680) :
    let s := (sigma 1 i : ℕ)
    let g := Nat.gcd s i
    let q := i / g
    sigma 1 (g * q) = g * (q + 1680) := by
  intro s g q
  have h_val_eq := val_eq_div_gcd hi
  rw [h_val] at h_val_eq
  have h_i_div_g : g ∣ i := Nat.gcd_dvd_right s i
  have h_eq : g * q = i := Nat.mul_div_cancel' h_i_div_g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right s hi
  have h_sub_pos : i ≤ s := by
    change i ≤ (sigma 1 i : ℕ)
    rw [sigma_apply]
    simp only [pow_one]
    have h_div_self : i ∈ i.divisors := by
      rw [mem_divisors]
      refine ⟨by simp, _root_.ne_of_gt hi⟩
    have h_single := Finset.single_le_sum (fun d _ => Nat.zero_le d) h_div_self
    exact h_single
  have h_div_sub : g ∣ s - i := by
    have h_gcd_sub : g = Nat.gcd (s - i) i := by
      change s.gcd i = (s - i).gcd i
      have hs_eq : s = (s - i) + i := (Nat.sub_add_cancel h_sub_pos).symm
      nth_rw 1 [hs_eq]
      rw [Nat.gcd_add_self_left]
    rw [h_gcd_sub]
    exact Nat.gcd_dvd_left (s - i) i
  have h_mul : s - i = 1680 * g := by
    have h_div_eq : 1680 = (s - i) / g := h_val_eq
    have h_cancel : g * ((s - i) / g) = s - i := Nat.mul_div_cancel' h_div_sub
    rw [mul_comm]
    rw [← h_div_eq] at h_cancel
    exact h_cancel.symm
  have h_s : s = i + 1680 * g := by
    omega
  have h_i_eq : i = g * q := h_eq.symm
  have h_factor : g * q + 1680 * g = g * (q + 1680) := by ring
  have h_s' : (sigma 1 i : ℕ) = g * (q + 1680) := by
    have : s = g * (q + 1680) := by
      rw [h_s]
      rw [h_i_eq]
      exact h_factor
    exact this
  rw [h_i_eq] at h_s'
  exact h_s'


theorem sigma_mul_ge_of_prime_dvd (g q p : ℕ) (hg : g ≥ 2) (hq : q ≥ 1) (hp : p.Prime) (hpg : p ∣ g) (hpq : Nat.Coprime p q) :
    g * (sigma 1 : ArithmeticFunction ℕ) q + (g / p) * (sigma 1 : ArithmeticFunction ℕ) q ≤ (sigma 1 : ArithmeticFunction ℕ) (g * q) := by
  have hg0 : g ≠ 0 := by omega
  have hp0 : p ≠ 0 := hp.ne_zero
  have hgp_div : p ∣ g := hpg
  have h_gp_mul : g / p * p = g := Nat.div_mul_cancel hgp_div
  have hgp0 : g / p ≠ 0 := by
    intro hc
    rw [hc, Nat.zero_mul] at h_gp_mul
    exact hg0 h_gp_mul.symm
  let f1 : ℕ ↪ ℕ := ⟨fun d => g * d, fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg0) h⟩
  let f2 : ℕ ↪ ℕ := ⟨fun d => (g / p) * d, fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hgp0) h⟩
  set s1 := q.divisors.map f1
  set s2 := q.divisors.map f2
  have h_s1_sub : s1 ⊆ (g * q).divisors := by
    intro x hx
    rcases mem_map.mp hx with ⟨d, hd, rfl⟩
    rw [mem_divisors] at hd
    rcases hd with ⟨hd_div, _⟩
    rw [mem_divisors]
    refine ⟨mul_dvd_mul_left g hd_div, mul_ne_zero hg0 (by omega)⟩
  have h_s2_sub : s2 ⊆ (g * q).divisors := by
    intro x hx
    rcases mem_map.mp hx with ⟨d, hd, rfl⟩
    rw [mem_divisors] at hd
    rcases hd with ⟨hd_div, _⟩
    rw [mem_divisors]
    refine ⟨?_, mul_ne_zero hg0 (by omega)⟩
    rcases hd_div with ⟨k, rfl⟩
    use p * k
    calc g * (d * k) = (g / p * p) * (d * k) := by nth_rw 1 [← h_gp_mul]
    _ = (g / p * d) * (p * k) := by ring
  have h_disj : Disjoint s1 s2 := by
    rw [disjoint_iff_ne]
    rintro x hx y hy hxy
    rcases mem_map.mp hx with ⟨d1, hd1, rfl⟩
    rcases mem_map.mp hy with ⟨d2, hd2, rfl⟩
    have h_eq : g * d1 = (g / p) * d2 := hxy
    have h_eq' : (g / p * p) * d1 = (g / p) * d2 := by
      nth_rw 1 [← h_gp_mul] at h_eq
      exact h_eq
    have h_eq'' : (g / p) * (p * d1) = (g / p) * d2 := by
      calc (g / p) * (p * d1) = (g / p * p) * d1 := by ring
      _ = (g / p) * d2 := h_eq'
    have h_cancel : p * d1 = d2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hgp0) h_eq''
    have hp_div_d2 : p ∣ d2 := by
      use d1
      exact h_cancel.symm
    rw [mem_divisors] at hd2
    have hp_div_q : p ∣ q := dvd_trans hp_div_d2 hd2.1
    have hp_div_gcd : p ∣ p.gcd q := Nat.dvd_gcd (dvd_refl p) hp_div_q
    rw [hpq] at hp_div_gcd
    have hp_le_1 : p ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) hp_div_gcd
    have hp_ge_2 : p ≥ 2 := hp.two_le
    omega
  have h_union_sub : s1 ∪ s2 ⊆ (g * q).divisors := Finset.union_subset h_s1_sub h_s2_sub
  have h_sum_le : (∑ x ∈ s1 ∪ s2, x) ≤ ∑ x ∈ (g * q).divisors, x := sum_le_sum_of_subset h_union_sub
  rw [sum_union h_disj] at h_sum_le
  have h_sum_s1 : (∑ x ∈ s1, x) = g * (sigma 1 : ArithmeticFunction ℕ) q := by
    rw [sum_map]
    dsimp [f1]
    rw [sigma_apply]
    simp only [pow_one]
    rw [mul_sum]
  have h_sum_s2 : (∑ x ∈ s2, x) = (g / p) * (sigma 1 : ArithmeticFunction ℕ) q := by
    rw [sum_map]
    dsimp [f2]
    rw [sigma_apply]
    simp only [pow_one]
    rw [mul_sum]
  rw [h_sum_s1, h_sum_s2] at h_sum_le
  conv_rhs =>
    rw [sigma_apply]
    simp only [pow_one]
  exact h_sum_le


theorem oeis_243512_conjecture_0.disproof : ¬ (∀ n, a n ≠ 0) := by
  intro h
  have h_1680 : a 1680 ≠ 0 := h 1680
  rw [a_ne_zero_iff] at h_1680
  rcases h_1680 with ⟨i, hi_pos, hi_val⟩
  set s := (sigma 1 i : ℕ)
  set g := Nat.gcd s i
  set q := i / g
  have h_prop : ((sigma 1 : ArithmeticFunction ℕ) q - q ≤ 1680) ∧ (Nat.Coprime q 1680) := val_1680_properties hi_pos hi_val
  have h_eq_sigma : (sigma 1 : ArithmeticFunction ℕ) (g * q) = g * (q + 1680) := val_eq_sigma_mul hi_pos hi_val
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right s hi_pos
  have hq_pos : q ≥ 1 := by
    have h_i_div_g : g ∣ i := Nat.gcd_dvd_right s i
    have h_eq : g * q = i := Nat.mul_div_cancel' h_i_div_g
    have : 0 < g * q := by omega
    rw [mul_comm] at this
    exact Nat.pos_of_mul_pos_right this
  have h_cases : g = 1 ∨ g ≥ 2 := by omega
  rcases h_cases with hg1 | hg2
  · have hq_pos' : q ≥ 1 := by
      change i / g ≥ 1
      rw [hg1, Nat.div_one]
      omega
    have h_eq_q : i = q := by
      change i = i / g
      rw [hg1, Nat.div_one]
    rw [hg1] at h_eq_sigma
    rw [Nat.one_mul, Nat.one_mul] at h_eq_sigma
    have h_eq_sigma' : (sigma 1 i : ℕ) = i + 1680 := by
      rw [h_eq_q]
      exact h_eq_sigma
    have h_sub : (sigma 1 i : ℕ) - i = 1680 := by omega
    have h_neq := sigma_sub_ne_1680 i (by omega) (by rw [h_eq_q]; exact h_prop.2)
    exact h_neq h_sub
  · have h_sig_le : q ≤ (sigma 1 : ArithmeticFunction ℕ) q := by
      change q ≤ (sigma 1 q : ℕ)
      rw [sigma_apply]
      simp only [pow_one]
      have h_div_self : q ∈ q.divisors := by
        rw [mem_divisors]
        refine ⟨by simp, by omega⟩
      exact Finset.single_le_sum (fun d _ => Nat.zero_le d) h_div_self
    have h1 := sigma_mul_ge_plus_one g q hg2 hq_pos
    rw [h_eq_sigma] at h1
    have h2 : g * (q + 1680) = g * q + 1680 * g := by ring
    rw [h2] at h1
    have h3 : g * (sigma 1 : ArithmeticFunction ℕ) q = g * q + g * ((sigma 1 : ArithmeticFunction ℕ) q - q) := by
      rw [← Nat.mul_add]
      rw [Nat.add_comm]
      rw [Nat.sub_add_cancel h_sig_le]
    rw [h3] at h1
    have h4 : g * ((sigma 1 : ArithmeticFunction ℕ) q - q) < 1680 * g := by omega
    have h5 : 1680 * g = g * 1680 := by ring
    rw [h5] at h4
    have h6 : (sigma 1 : ArithmeticFunction ℕ) q - q < 1680 := Nat.lt_of_mul_lt_mul_left h4
    have h_eq_sigma_q : (sigma 1 : ArithmeticFunction ℕ) q - q ≤ 1679 := by omega
    have h_prime := Nat.minFac_prime (by omega : g ≠ 1)
    have h_cases' : g.minFac ≤ 7 ∨ g.minFac ≥ 11 := by
      by_cases h_lt : g.minFac < 11
      · left
        have h_not8 : g.minFac ≠ 8 := by
          intro hc; rw [hc] at h_prime; revert h_prime; decide
        have h_not9 : g.minFac ≠ 9 := by
          intro hc; rw [hc] at h_prime; revert h_prime; decide
        have h_not10 : g.minFac ≠ 10 := by
          intro hc; rw [hc] at h_prime; revert h_prime; decide
        omega
      · right; omega
    have h_cancel (p : ℕ) (hp : p.Prime) (hpg : p ∣ g) (hpq : Nat.Coprime p q) :
        (p + 1) * (sigma 1 : ArithmeticFunction ℕ) q ≤ p * (q + 1680) := by
      have h_sig_ge := sigma_mul_ge_of_prime_dvd g q p hg2 hq_pos hp hpg hpq
      have hg_eq : g = (g / p) * p := (Nat.div_mul_cancel hpg).symm
      have h_lhs : g * (sigma 1 : ArithmeticFunction ℕ) q + (g / p) * (sigma 1 : ArithmeticFunction ℕ) q = (g / p) * ((p + 1) * (sigma 1 : ArithmeticFunction ℕ) q) := by
        nth_rw 1 [hg_eq]; ring
      have h_rhs : g * (q + 1680) = (g / p) * (p * (q + 1680)) := by
        nth_rw 1 [hg_eq]; ring
      rw [h_eq_sigma] at h_sig_ge
      rw [h_lhs, h_rhs] at h_sig_ge
      have h_gp_pos : g / p > 0 := Nat.div_pos (Nat.le_of_dvd (by omega) hpg) hp.pos
      exact Nat.le_of_mul_le_mul_left h_sig_ge h_gp_pos

    rcases h_cases' with h_le7 | h_ge11
    · have hp_cases : g.minFac = 2 ∨ g.minFac = 3 ∨ g.minFac = 5 ∨ g.minFac = 7 := by
        have hp_ge2 : g.minFac ≥ 2 := h_prime.two_le
        interval_cases g.minFac
        · left; rfl
        · right; left; rfl
        · revert h_prime; decide
        · right; right; left; rfl
        · revert h_prime; decide
        · right; right; right; rfl
      rcases hp_cases with hp2 | hp3 | hp5 | hp7
      · sorry
      · sorry
      · sorry
      · sorry
    · sorry

