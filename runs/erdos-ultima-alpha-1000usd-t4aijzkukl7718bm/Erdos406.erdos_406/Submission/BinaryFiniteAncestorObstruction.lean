import FormalConjecturesUtil

/-! A fixed finite set of ternary-ancestor levels is not a closed binary
classifier, even after imposing any fixed ternary suffix guard and cutoff.
This is an obstruction to a proposed certificate, not a settlement of Erdős 406. -/
namespace Erdos406FiniteAncestorObstruction

/-- Two sufficiently large powers of two cannot differ by the bounded
remainders in two properly nested ancestor levels. -/
lemma nested_nonpower (b c n a e : ℕ) (hc : 1 < c) (ha : a < b)
    (hn : b * c ≤ n) (he : b * c * n + 1 = 2 ^ e) :
    ¬ (b * n + a).isPowerOfTwo := by
  rintro ⟨f, hf⟩
  have hb : 0 < b := by omega
  have hn0 : 0 < n := by nlinarith
  have hbn : n ≤ b * n + a := by nlinarith
  have hbc : 2 * b ≤ b * c := by nlinarith
  have hmul := Nat.mul_le_mul_right n hbc
  have hlt : b * n + a ≤ b * c * n + 1 := by nlinarith
  have hfe : f ≤ e := by
    by_contra h
    have hpow := Nat.pow_lt_pow_right (by decide : 1 < 2) (show e < f by omega)
    omega
  have hd : 2 ^ f ∣ 2 ^ e := pow_dvd_pow 2 hfe
  have hv : 1 < 2 ^ f := by nlinarith
  have hsmall : c * a < 2 ^ f := by nlinarith
  have hid : 2 ^ e + c * a = c * 2 ^ f + 1 := by nlinarith
  have hmod := congrArg (fun x : ℕ => x % 2 ^ f) hid
  simp only [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, zero_add,
    Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod,
    Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hsmall] at hmod
  have hdiv : c ∣ 1 := ⟨a, hmod.symm⟩
  have hle := Nat.le_of_dvd (by decide : 0 < 1) hdiv
  omega

/-- Powers congruent to one modulo a chosen power of three yield arbitrarily
large exact ancestors whose prescribed ternary suffix is zero. -/
lemma large_zero_suffix_ancestor (J G M E : ℕ) :
    ∃ n e : ℕ, M ≤ n ∧ E ≤ e ∧ n % 3 ^ G = 0 ∧
      3 ^ (J + 1) * n + 1 = 2 ^ e := by
  let m := 3 ^ (J + 1)
  let q := 3 ^ (J + 1 + G)
  let t := m * (M + 1) + E + 1
  let e := Nat.totient q * t
  have hm : 0 < m := by dsimp [m]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hp : 1 ≤ Nat.totient q := Nat.totient_pos.mpr hq
  have het : t ≤ e := by
    dsimp [e]
    simpa using Nat.mul_le_mul_right t hp
  have hcop : Nat.Coprime 2 q := (by decide : Nat.Coprime 2 3).pow_right _
  have hmod : Nat.ModEq q (2 ^ e) 1 := by
    have h := (Nat.ModEq.pow_totient hcop).pow t
    simpa only [← pow_mul, one_pow] using h
  have hpos : 1 ≤ 2 ^ e := Nat.one_le_pow _ _ (by decide)
  have hd : q ∣ 2 ^ e - 1 := (Nat.modEq_iff_dvd' hpos).mp hmod.symm
  obtain ⟨k, hk⟩ := hd
  let n := 3 ^ G * k
  have hqeq : q = m * 3 ^ G := by dsimp [q, m]; rw [pow_add]
  have hid : m * n + 1 = 2 ^ e := by
    have hh := Nat.sub_add_cancel hpos
    rw [hk, hqeq] at hh
    dsimp [n]
    nlinarith
  refine ⟨n, e, ?_, ?_, ?_, hid⟩
  · have hgrow : e < 2 ^ e := Nat.lt_two_pow_self
    dsimp [t] at het
    nlinarith
  · dsimp [t] at het
    omega
  · dsimp [n]
    simp

/-- The negative part of the finite-depth structural classifier. -/
def ancestor (J E n : ℕ) : Prop :=
  ∃ j ≤ J, ∃ a < 3 ^ j, Nat.digits 3 a ⊆ [0, 1] ∧
    ∃ e ≥ E, 3 ^ j * n + a = 2 ^ e

def classifier (D J E n : ℕ) : Prop :=
  Nat.digits 3 (n % 3 ^ D) ⊆ [0, 1] ∧ ¬ ancestor J E n

lemma next_level_not_short (J n e : ℕ) (hn : 3 ^ (J + 1) ≤ n)
    (he : 3 ^ (J + 1) * n + 1 = 2 ^ e) (E : ℕ) :
    ¬ ancestor J E n := by
  rintro ⟨j, hj, a, ha, _, f, _, hf⟩
  have hpow : 3 ^ j * 3 ^ (J + 1 - j) = 3 ^ (J + 1) := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : j ≤ J + 1)]
  have hc : 1 < 3 ^ (J + 1 - j) := by
    exact one_lt_pow₀ (by decide) (by omega)
  exact nested_nonpower (3 ^ j) (3 ^ (J + 1 - j)) n a e hc ha
    (by simpa only [hpow] using hn) (by simpa only [hpow] using he) ⟨f, hf⟩

/-- Every fixed-depth ancestor classifier fails closure at arbitrarily large
inputs in every fixed good-tail guard. These inputs are not asserted whole-good. -/
theorem no_fixed_guard (D J E : ℕ) (hJ : 0 < J) (G M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ Nat.digits 3 (n % 3 ^ G) ⊆ [0, 1] ∧
      classifier D J E n ∧ ¬ classifier D J E (3 * n) := by
  obtain ⟨n, e, hn, heE, hz, hid⟩ :=
    large_zero_suffix_ancestor J (max D G) (max M (3 ^ (J + 1))) E
  have zero_mod (r : ℕ) (hr : r ≤ max D G) : n % 3 ^ r = 0 := by
    exact Nat.mod_eq_zero_of_dvd ((pow_dvd_pow 3 hr).trans (Nat.dvd_of_mod_eq_zero hz))
  have hd : classifier D J E n := by
    refine ⟨?_, next_level_not_short J n e (le_trans (le_max_right _ _) hn) hid E⟩
    simp [zero_mod D (le_max_left _ _)]
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_, hd, ?_⟩
  · simp [zero_mod G (le_max_right _ _)]
  · intro h
    apply h.2
    refine ⟨J, le_rfl, 1, ?_, ?_, e, heE, ?_⟩
    · exact one_lt_pow₀ (by decide) (by omega)
    · norm_num
    · simpa only [pow_succ, mul_assoc] using hid

/-- In particular, neither increasing the construction cutoff nor a fixed
ternary suffix guard repairs this finite-depth predicate. -/
theorem not_eventually_guarded_closed (D J E : ℕ) (hJ : 0 < J) :
    ¬ ∃ G M : ℕ, ∀ n : ℕ, M ≤ n → Nat.digits 3 (n % 3 ^ G) ⊆ [0, 1] →
      classifier D J E n → classifier D J E (3 * n) := by
  rintro ⟨G, M, h⟩
  obtain ⟨n, hn, hg, ha, hna⟩ := no_fixed_guard D J E hJ G M
  exact hna (h n hn hg ha)

/-- The complete affine-closure obstruction also covers depth zero; there the
failing digit is one rather than zero. -/
theorem not_eventually_guarded_affine_closed (D J E : ℕ) :
    ¬ ∃ G M : ℕ, ∀ n c : ℕ, M ≤ n → c < 2 →
      Nat.digits 3 (n % 3 ^ G) ⊆ [0, 1] →
      classifier D J E n → classifier D J E (3 * n + c) := by
  rintro ⟨G, M, h⟩
  by_cases hJ : 0 < J
  · obtain ⟨n, hn, hg, ha, hna⟩ := no_fixed_guard D J E hJ G M
    exact hna (by simpa using h n 0 hn (by decide) hg ha)
  · have hzero : J = 0 := by omega
    subst J
    obtain ⟨n, e, hn, heE, hz, hid⟩ :=
      large_zero_suffix_ancestor 0 (max D G) (max M 3) E
    have zero_mod (r : ℕ) (hr : r ≤ max D G) : n % 3 ^ r = 0 := by
      exact Nat.mod_eq_zero_of_dvd ((pow_dvd_pow 3 hr).trans (Nat.dvd_of_mod_eq_zero hz))
    have ha : classifier D 0 E n := by
      refine ⟨?_, next_level_not_short 0 n e ?_ hid E⟩
      · simp [zero_mod D (le_max_left _ _)]
      · simpa using (le_trans (le_max_right M 3) hn)
    have hg : Nat.digits 3 (n % 3 ^ G) ⊆ [0, 1] := by
      simp [zero_mod G (le_max_right _ _)]
    have hout := h n 1 (le_trans (le_max_left _ _) hn) (by decide) hg ha
    apply hout.2
    exact ⟨0, le_rfl, 0, by decide, by simp, e, heE, by simpa using hid⟩

#print axioms not_eventually_guarded_affine_closed
#print axioms not_eventually_guarded_closed
#print axioms nested_nonpower
#print axioms large_zero_suffix_ancestor
#print axioms no_fixed_guard
end Erdos406FiniteAncestorObstruction
