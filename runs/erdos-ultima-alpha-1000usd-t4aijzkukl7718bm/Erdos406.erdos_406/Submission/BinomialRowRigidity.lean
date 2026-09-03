import Submission.CubicBlockRigidity

/-! Rigidity of ternary-good binomial rows. This restricts separated-block
binomial constructions; it does not control overlapping carries in powers of two. -/
namespace Erdos406Work

lemma good_sub_one_of_unit {u : ℕ} (hu : Nat.digits 3 u ⊆ [0, 1])
    (hmod : u % 3 = 1) : Nat.digits 3 (u - 1) ⊆ [0, 1] := by
  have hh := good_div_three_pow hu 1
  norm_num at hh
  have he : u - 1 = 3 * (u / 3) := by omega
  rw [he, good_mul_three_iff]
  exact hh

lemma good_normalized_three_part {n : ℕ} (hn : 0 < n)
    (hg : Nat.digits 3 n ⊆ [0, 1]) :
    ∃ s u : ℕ, n = 3 ^ s * u ∧ u % 3 = 1 ∧ Nat.digits 3 u ⊆ [0, 1] := by
  obtain ⟨s, u, hnu, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (ne_of_gt hn) 3 (by decide)
  have hu := hg
  rw [he, good_mul_three_pow_iff] at hu
  exact ⟨s, u, he, good_not_dvd_three_mod hu hnu, hu⟩

/-- A quotient whose normalized 3-adic unit is two cannot be ternary-good. -/
lemma bad_of_scaled_unit_equation {D A n s : ℕ}
    (hD : D % 3 = 2) (hA : A % 3 = 1) (he : D * n = 3 ^ s * A) :
    ¬ Nat.digits 3 n ⊆ [0, 1] := by
  intro hg
  have hcop : Nat.Coprime 3 D := Nat.prime_three.coprime_iff_not_dvd.mpr (by
    rw [Nat.dvd_iff_mod_eq_zero]; omega)
  have hd : 3 ^ s ∣ n := (hcop.pow_left s).dvd_of_dvd_mul_left (by
    rw [he]; exact dvd_mul_right _ _)
  obtain ⟨v, hv⟩ := hd
  have hvGood := hg
  rw [hv, good_mul_three_pow_iff] at hvGood
  have hcancel : D * v = A := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 3 ^ s by positivity)
    rw [hv] at he
    nlinarith only [he]
  have hmod := congrArg (fun a : ℕ => a % 3) hcancel
  change (D * v) % 3 = A % 3 at hmod
  rw [Nat.mul_mod, hD, hA] at hmod
  have hb := ternary_digit_bound hvGood 0
  norm_num at hb
  omega

lemma choose_two_identity (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  have hh := Nat.descFactorial_eq_factorial_mul_choose n 2
  simpa [Nat.descFactorial_succ, mul_comm] using hh.symm

lemma choose_four_identity (n : ℕ) :
    24 * n.choose 4 = n * (n - 1) * (n - 2) * (n - 3) := by
  have hh := Nat.descFactorial_eq_factorial_mul_choose n 4
  simpa [Nat.descFactorial_succ, mul_assoc, mul_comm, mul_left_comm] using hh.symm

lemma choose_six_identity (n : ℕ) :
    720 * n.choose 6 = n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) := by
  have hh := Nat.descFactorial_eq_factorial_mul_choose n 6
  simpa [Nat.descFactorial_succ, mul_assoc, mul_comm, mul_left_comm] using hh.symm

lemma good_unit_choose_two_bad {u : ℕ} (hu : Nat.digits 3 u ⊆ [0, 1])
    (hmod : u % 3 = 1) (hlarge : 1 < u) :
    ¬ Nat.digits 3 (u.choose 2) ⊆ [0, 1] := by
  obtain ⟨t, a, he, ha, _⟩ := good_normalized_three_part
    (by omega : 0 < u - 1) (good_sub_one_of_unit hu hmod)
  apply bad_of_scaled_unit_equation (D := 2) (A := u * a) (s := t) (by decide)
  · simp [Nat.mul_mod, hmod, ha]
  · rw [choose_two_identity, he]; ring

lemma good_multiple_nine_choose_four_bad {q : ℕ}
    (hq : 0 < q) (hg : Nat.digits 3 q ⊆ [0, 1]) (h9 : 9 ∣ q) :
    ¬ Nat.digits 3 (q.choose 4) ⊆ [0, 1] := by
  obtain ⟨s, u, he, hu, _⟩ := good_normalized_three_part hq hg
  obtain ⟨v, hv⟩ := h9
  have hvpos : 0 < v := by omega
  have hq1 : (q - 1) % 3 = 2 := by omega
  have hq2 : (q - 2) % 3 = 1 := by omega
  have hq3 : (q / 3 - 1) % 3 = 2 := by omega
  have hsub : q - 3 = 3 * (q / 3 - 1) := by omega
  let A := u * (q - 1) * (q - 2) * (q / 3 - 1)
  apply bad_of_scaled_unit_equation (D := 8) (A := A) (s := s) (by decide)
  · dsimp [A]; simp [Nat.mul_mod, hu, hq1, hq2, hq3]
  · have hh := choose_four_identity q
    rw [hsub] at hh
    have heq : 3 * (8 * q.choose 4) =
        3 * (3 ^ s * A) := by
      dsimp [A]
      calc
        _ = 24 * q.choose 4 := by ring
        _ = _ := hh
        _ = _ := by conv_lhs => lhs; lhs; lhs; rw [he]
                    ring
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3) heq

lemma good_triple_unit_choose_six_bad {u : ℕ}
    (hu : Nat.digits 3 u ⊆ [0, 1]) (hmod : u % 3 = 1) (hlarge : 1 < u) :
    ¬ Nat.digits 3 ((3 * u).choose 6) ⊆ [0, 1] := by
  obtain ⟨t, a, he, ha, _⟩ := good_normalized_three_part
    (by omega : 0 < u - 1) (good_sub_one_of_unit hu hmod)
  have hu4 : 4 ≤ u := by omega
  let A := u * a * (3 * u - 1) * (3 * u - 2) * (3 * u - 4) * (3 * u - 5)
  apply bad_of_scaled_unit_equation (D := 80) (A := A) (s := t) (by decide)
  · have h1 : (3 * u - 1) % 3 = 2 := by omega
    have h2 : (3 * u - 2) % 3 = 1 := by omega
    have h4 : (3 * u - 4) % 3 = 2 := by omega
    have h5 : (3 * u - 5) % 3 = 1 := by omega
    dsimp [A]; simp [Nat.mul_mod, hmod, ha, h1, h2, h4, h5]
  · have hh := choose_six_identity (3 * u)
    have hsub : 3 * u - 3 = 3 * (u - 1) := by omega
    rw [hsub, he] at hh
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 9)
    dsimp [A]
    calc
      9 * (80 * (3 * u).choose 6) = 720 * (3 * u).choose 6 := by ring
      _ = _ := hh
      _ = _ := by ring

/-- Four fixed entries already classify all ternary-good binomial rows. -/
theorem good_binomial_test_rigidity (q : ℕ)
    (h1 : Nat.digits 3 (q.choose 1) ⊆ [0, 1])
    (h2 : Nat.digits 3 (q.choose 2) ⊆ [0, 1])
    (h4 : Nat.digits 3 (q.choose 4) ⊆ [0, 1])
    (h6 : Nat.digits 3 (q.choose 6) ⊆ [0, 1]) : q = 0 ∨ q = 1 ∨ q = 3 := by
  simp only [Nat.choose_one_right] at h1
  by_cases hq : q = 0
  · exact Or.inl hq
  obtain ⟨s, u, he, hu, hgu⟩ := good_normalized_three_part (by omega : 0 < q) h1
  have hup : 0 < u := by omega
  by_cases hs : 2 ≤ s
  · have h9 : 9 ∣ q := by
      rw [he]
      exact dvd_mul_of_dvd_left (show 3 ^ 2 ∣ 3 ^ s from pow_dvd_pow 3 hs) u
    exact (good_multiple_nine_choose_four_bad (by omega) h1 h9 h4).elim
  have hsmall : s = 0 ∨ s = 1 := by omega
  rcases hsmall with rfl | rfl
  · simp only [pow_zero, one_mul] at he
    by_cases hu1 : u = 1
    · exact Or.inr (Or.inl (he.trans hu1))
    · rw [he] at h2
      exact (good_unit_choose_two_bad hgu hu (by omega) h2).elim
  · simp only [pow_one] at he
    by_cases hu1 : u = 1
    · exact Or.inr (Or.inr (by simpa [hu1] using he))
    · rw [he] at h6
      exact (good_triple_unit_choose_six_bad hgu hu (by omega) h6).elim

theorem good_binomial_row_iff (q : ℕ) :
    (∀ j : ℕ, Nat.digits 3 (q.choose j) ⊆ [0, 1]) ↔ q = 0 ∨ q = 1 ∨ q = 3 := by
  constructor
  · intro h
    exact good_binomial_test_rigidity q (h 1) (h 2) (h 4) (h 6)
  · rintro (rfl | rfl | rfl) j
    all_goals
      by_cases hj : j ≤ 3
      · interval_cases j <;> decide +kernel
      · rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp

lemma good_ofDigits_blocks_iff (L : ℕ) (w : List ℕ)
    (hw : ∀ a ∈ w, a < 3 ^ L) :
    Nat.digits 3 (Nat.ofDigits (3 ^ L) w) ⊆ [0, 1] ↔
      ∀ a ∈ w, Nat.digits 3 a ⊆ [0, 1] := by
  induction w with
  | nil => simp [Nat.ofDigits]
  | cons a w ih =>
    have ha := hw a (List.mem_cons_self ..)
    have ht : ∀ b ∈ w, b < 3 ^ L := fun b hb => hw b (List.mem_cons_of_mem _ hb)
    rw [Nat.ofDigits_cons, good_split_iff ha, ih ht]
    simp only [List.forall_mem_cons]

lemma ofDigits_map_range (b n : ℕ) (f : ℕ → ℕ) :
    Nat.ofDigits b ((List.range n).map f) = ∑ i ∈ Finset.range n, f i * b ^ i := by
  induction n with
  | zero => simp [Nat.ofDigits]
  | succ n ih =>
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ih,
      Finset.sum_range_succ]
    simp [mul_comm]

lemma ofDigits_binomial_row (b q : ℕ) :
    Nat.ofDigits b ((List.range (q + 1)).map (q.choose ·)) = (b + 1) ^ q := by
  rw [ofDigits_map_range, add_pow]
  simp [mul_comm]

/-- A separated binomial expansion is good exactly in degrees zero, one and
three. The size premise excludes overlap between consecutive coefficient
blocks; it is not available for arbitrary powers of two. -/
theorem separated_binomial_power_good_iff (q L : ℕ) (hsep : 2 ^ q < 3 ^ L) :
    Nat.digits 3 ((3 ^ L + 1) ^ q) ⊆ [0, 1] ↔ q = 0 ∨ q = 1 ∨ q = 3 := by
  rw [← ofDigits_binomial_row]
  have hb : ∀ a ∈ (List.range (q + 1)).map (q.choose ·), a < 3 ^ L := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact (Nat.choose_le_two_pow q j).trans_lt hsep
  rw [good_ofDigits_blocks_iff L _ hb]
  have he : (∀ a ∈ (List.range (q + 1)).map (q.choose ·),
      Nat.digits 3 a ⊆ [0, 1]) ↔
      ∀ j : ℕ, Nat.digits 3 (q.choose j) ⊆ [0, 1] := by
    constructor
    · intro h j
      by_cases hj : j ≤ q
      · exact h _ (List.mem_map.mpr ⟨j, by simpa using Nat.lt_succ_of_le hj, rfl⟩)
      · rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    · intro h a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact h j
  rw [he, good_binomial_row_iff]

#print axioms separated_binomial_power_good_iff
#print axioms good_binomial_row_iff
#print axioms good_binomial_test_rigidity
end Erdos406Work
