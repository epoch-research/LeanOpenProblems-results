import FormalConjecturesUtil
import Submission.SquarefreeBounds

/-!
# Elementary cubic-root gaps between squarefree numbers

We count the cover by prime squares with primes at most the interval length.
The reciprocal-square sum is at most `1/2`, and elementary residue-class
counting gives at most `H/3 + 4` such primes.  Survivors, if nonsquarefree,
have a prime-square divisor with prime larger than `H`; their positive
quotients are distinct.  No analytic prime-counting theorem is used.
-/

open scoped BigOperators

namespace SquarefreeCubic

/-- Primes at most `H`, viewed as a finite set. -/
def primesUpTo (H : ℕ) : Finset ℕ := (Finset.Icc 2 H).filter Nat.Prime

lemma mem_primesUpTo {H p : ℕ} : p ∈ primesUpTo H ↔ Nat.Prime p ∧ p ≤ H := by
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.two_le, h.2⟩, h.1⟩⟩

/-- The sum over positive odd integers, bounded by an elementary telescoping sum. -/
lemma odd_reciprocal_sq_sum_le (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (2 * (k : ℝ) + 1) ^ 2) ≤ 1 / 4 := by
  have hstrong :
      (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (2 * (k : ℝ) + 1) ^ 2) ≤
        1 / 4 - 1 / (4 * ((K : ℝ) + 1)) := by
    induction K with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hk1 : 0 < (k : ℝ) + 1 := by positivity
      have hk2 : 0 < (k : ℝ) + 2 := by positivity
      have htel : (1 : ℝ) / (4 * ((k : ℝ) + 1)) -
          1 / (4 * ((k : ℝ) + 2)) =
          1 / (4 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
        field_simp [ne_of_gt hk1, ne_of_gt hk2]
        ring
      have hstep : (1 : ℝ) / (2 * ((k : ℝ) + 1) + 1) ^ 2 ≤
          1 / (4 * ((k : ℝ) + 1)) - 1 / (4 * ((k : ℝ) + 2)) := by
        rw [htel]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring]
      linarith
  exact hstrong.trans (sub_le_self _ (by positivity))

/-- The sum of reciprocal squares of primes is at most `1/2`. -/
lemma prime_reciprocal_sq_sum_le (H : ℕ) :
    (∑ p ∈ primesUpTo H, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / 2 := by
  let O := (Finset.Icc 1 H).image (fun k : ℕ => 2 * k + 1)
  have htwo : 2 ∉ O := by
    simp only [O, Finset.mem_image, Finset.mem_Icc, not_exists, not_and]
    intro k hk hkH
    omega
  have hsub : primesUpTo H ⊆ insert 2 O := by
    intro p hp
    obtain ⟨hpp, hpH⟩ := mem_primesUpTo.mp hp
    rcases hpp.eq_two_or_odd with rfl | hodd
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨p / 2, Finset.mem_Icc.mpr ?_, ?_⟩
      · have hp2 := hpp.two_le
        omega
      · omega
  calc
    (∑ p ∈ primesUpTo H, (1 : ℝ) / (p : ℝ) ^ 2)
        ≤ ∑ p ∈ insert 2 O, (1 : ℝ) / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p _ _
      positivity
    _ = 1 / 4 + ∑ k ∈ Finset.Icc 1 H,
        (1 : ℝ) / (2 * (k : ℝ) + 1) ^ 2 := by
      rw [Finset.sum_insert htwo]
      dsimp [O]
      rw [Finset.sum_image (by
        intro a ha b hb hab
        change 2 * a + 1 = 2 * b + 1 at hab
        omega)]
      norm_num
    _ ≤ 1 / 2 := by have := odd_reciprocal_sq_sum_le H; linarith

/-- A prime other than `2` and `3` is in residue class `1` or `5` modulo `6`. -/
lemma prime_mod_six {p : ℕ} (hp : Nat.Prime p) :
    p = 2 ∨ p = 3 ∨ p % 6 = 1 ∨ p % 6 = 5 := by
  by_cases htwo : p = 2
  · exact Or.inl htwo
  by_cases hthree : p = 3
  · exact Or.inr (Or.inl hthree)
  have hodd := hp.mod_two_eq_one_iff_ne_two.mpr htwo
  have hndvd : ¬ 3 ∣ p := by
    intro h
    exact hthree ((hp.dvd_iff_eq (by decide)).mp h)
  have hmod : p % 3 ≠ 0 := fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
  omega

/-- A single residue class modulo `6` has at most `H/6 + 1` representatives. -/
lemma residue_card_le (H r : ℕ) :
    ((Finset.range (H + 1)).filter (fun p => p % 6 = r)).card ≤ H / 6 + 1 := by
  calc
    ((Finset.range (H + 1)).filter (fun p => p % 6 = r)).card
        ≤ (Finset.range (H / 6 + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun p : ℕ => p / 6)
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp ⊢
        omega
      · intro p hp q hq hpq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hq
        change p / 6 = q / 6 at hpq
        omega
    _ = H / 6 + 1 := Finset.card_range _

/-- An elementary prime-counting bound, requiring no analytic information on primes. -/
lemma primesUpTo_card_le (H : ℕ) : ((primesUpTo H).card : ℝ) ≤ (H : ℝ) / 3 + 4 := by
  let R := fun r : ℕ => (Finset.range (H + 1)).filter (fun p => p % 6 = r)
  have hsub : primesUpTo H ⊆ ({2, 3} ∪ R 1) ∪ R 5 := by
    intro p hp
    obtain ⟨hpp, hpH⟩ := mem_primesUpTo.mp hp
    rcases prime_mod_six hpp with h | h | h | h
    · simp [h]
    · simp [h]
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩)
  have hcard : (primesUpTo H).card ≤ 2 * (H / 6) + 4 := by
    have h1 := residue_card_le H 1
    have h5 := residue_card_le H 5
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hc' := Finset.card_union_le ({2, 3} : Finset ℕ) (R 1)
    have h23 : ({2, 3} : Finset ℕ).card = 2 := by norm_num
    dsimp [R] at hc hc'
    omega
  have hreal : ((primesUpTo H).card : ℝ) ≤ 2 * ((H / 6 : ℕ) : ℝ) + 4 := by
    exact_mod_cast hcard
  have hdiv := Nat.cast_div_le (α := ℝ) (m := H) (n := 6)
  norm_num at hdiv
  linarith

/-- The portion of the interval covered by squares of primes at most `H`. -/
def smallPrimeCover (N H : ℕ) : Finset ℕ :=
  (primesUpTo H).biUnion (fun p => (Finset.Ioc N (N + H)).filter (fun m => p ^ 2 ∣ m))

/-- Numbers in the interval not divisible by any small prime square. -/
def survivors (N H : ℕ) : Finset ℕ := Finset.Ioc N (N + H) \ smallPrimeCover N H

lemma smallPrimeCover_subset (N H : ℕ) : smallPrimeCover N H ⊆ Finset.Ioc N (N + H) := by
  intro m hm
  obtain ⟨p, hp, hm⟩ := Finset.mem_biUnion.mp hm
  exact (Finset.mem_filter.mp hm).1

lemma mem_survivors {N H m : ℕ} :
    m ∈ survivors N H ↔ N < m ∧ m ≤ N + H ∧
      ∀ p : ℕ, Nat.Prime p → p ≤ H → ¬ p ^ 2 ∣ m := by
  constructor
  · intro hm
    obtain ⟨hmI, hmC⟩ := Finset.mem_sdiff.mp hm
    refine ⟨(Finset.mem_Ioc.mp hmI).1, (Finset.mem_Ioc.mp hmI).2, ?_⟩
    intro p hp hpH hdiv
    exact hmC (Finset.mem_biUnion.mpr ⟨p, mem_primesUpTo.mpr ⟨hp, hpH⟩,
      Finset.mem_filter.mpr ⟨hmI, hdiv⟩⟩)
  · rintro ⟨hNm, hmNH, hex⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨hNm, hmNH⟩, ?_⟩
    intro hmC
    obtain ⟨p, hp, hm⟩ := Finset.mem_biUnion.mp hmC
    obtain ⟨hpp, hpH⟩ := mem_primesUpTo.mp hp
    exact hex p hpp hpH (Finset.mem_filter.mp hm).2

/-- The small-prime-square cover has cardinality at most `5H/6 + 4`. -/
lemma smallPrimeCover_card_le (N H : ℕ) :
    ((smallPrimeCover N H).card : ℝ) ≤ (5 / 6 : ℝ) * (H : ℝ) + 4 := by
  let A := fun p : ℕ => (Finset.Ioc N (N + H)).filter (fun m => p ^ 2 ∣ m)
  calc
    ((smallPrimeCover N H).card : ℝ)
        ≤ ∑ p ∈ primesUpTo H, ((A p).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le :
        ((primesUpTo H).biUnion A).card ≤ ∑ p ∈ primesUpTo H, (A p).card)
    _ ≤ ∑ p ∈ primesUpTo H, ((H : ℝ) / (p : ℝ) ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpos : 0 < p ^ 2 := pow_pos (mem_primesUpTo.mp hp).1.pos _
      simpa only [A, Nat.cast_pow] using SquarefreeSqrt.multiples_Ioc_card_le N H (p ^ 2) hpos
    _ = (H : ℝ) * (∑ p ∈ primesUpTo H, (1 : ℝ) / (p : ℝ) ^ 2) +
        ((primesUpTo H).card : ℝ) := by
      simp only [div_eq_mul_inv, one_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (H : ℝ) * (1 / 2) + ((H : ℝ) / 3 + 4) :=
      add_le_add (mul_le_mul_of_nonneg_left (prime_reciprocal_sq_sum_le H) (Nat.cast_nonneg H))
        (primesUpTo_card_le H)
    _ = (5 / 6 : ℝ) * (H : ℝ) + 4 := by ring

/-- At least `H/6 - 4` terms survive all small prime squares. -/
lemma survivors_card_ge (N H : ℕ) :
    (H : ℝ) / 6 - 4 ≤ ((survivors N H).card : ℝ) := by
  have hc := Finset.card_sdiff_add_card_eq_card (smallPrimeCover_subset N H)
  rw [Nat.card_Ioc, Nat.add_sub_cancel_left] at hc
  have hcreal : ((survivors N H).card : ℝ) + ((smallPrimeCover N H).card : ℝ) = (H : ℝ) := by
    exact_mod_cast hc
  have hcover := smallPrimeCover_card_le N H
  linarith

lemma survivors_card_ge_twelfth (N H : ℕ) (hH : 48 ≤ H) :
    (H : ℝ) / 12 ≤ ((survivors N H).card : ℝ) := by
  have hHreal : (48 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hc := survivors_card_ge N H
  linarith

/-- Distinct square bases larger than `H` are separated by more than `H`,
even after multiplication by a positive integer. -/
lemma large_square_separation {H p₁ p₂ q : ℕ}
    (hp₁ : H < p₁) (hp : p₁ < p₂) (hq : 0 < q) :
    q * p₁ ^ 2 + H < q * p₂ ^ 2 := by
  have hs : p₁ ^ 2 + (H + 1) ≤ p₂ ^ 2 := by nlinarith
  have hqH : H < q * (H + 1) := by nlinarith
  calc
    q * p₁ ^ 2 + H < q * p₁ ^ 2 + q * (H + 1) := Nat.add_lt_add_left hqH _
    _ = q * (p₁ ^ 2 + (H + 1)) := by ring
    _ ≤ q * p₂ ^ 2 := Nat.mul_le_mul_left q hs

/-- Two numbers in an interval of length `H` cannot have the same positive
quotient by squares of different bases greater than `H`. -/
lemma same_quotient_square_eq {N H p₁ p₂ q : ℕ}
    (hp₁ : H < p₁) (hp₂ : H < p₂) (hq : 0 < q)
    (hm₁ : N < q * p₁ ^ 2) (hm₁' : q * p₁ ^ 2 ≤ N + H)
    (hm₂ : N < q * p₂ ^ 2) (hm₂' : q * p₂ ^ 2 ≤ N + H) : p₁ = p₂ := by
  rcases lt_trichotomy p₁ p₂ with h | h | h
  · have := large_square_separation hp₁ h hq
    omega
  · exact h
  · have := large_square_separation hp₂ h hq
    omega

/-- If the whole interval is nonsquarefree, every survivor has a large
prime-square divisor and a positive quotient. -/
lemma survivor_large_square {N H m : ℕ} (hm : m ∈ survivors N H) (hbad : ¬ Squarefree m) :
    ∃ p q : ℕ, Nat.Prime p ∧ H < p ∧ 0 < q ∧ m = q * p ^ 2 := by
  obtain ⟨hNm, hmNH, hex⟩ := mem_survivors.mp hm
  rw [Nat.squarefree_iff_prime_squarefree] at hbad
  push_neg at hbad
  obtain ⟨p, hp, hdiv⟩ := hbad
  have hdiv' : p ^ 2 ∣ m := by simpa only [pow_two] using hdiv
  have hpH : H < p := by
    by_contra h
    exact hex p hp (by omega) hdiv'
  obtain ⟨q, heq⟩ := hdiv'
  have hq : 0 < q := by
    have hmpos : 0 < m := by omega
    by_contra h
    have : q = 0 := by omega
    simp [this] at heq
    omega
  exact ⟨p, q, hp, hpH, hq, heq.trans (mul_comm _ _)⟩

/-- Injection of survivors into the positive quotients up to
`(N+H)/(H+1)^2`. -/
lemma survivors_card_le_quotients (N H : ℕ)
    (hbad : ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m) :
    (survivors N H).card ≤ (N + H) / (H + 1) ^ 2 := by
  classical
  let S := survivors N H
  let Q := (N + H) / (H + 1) ^ 2
  have hw : ∀ m : S, ∃ p q : ℕ, Nat.Prime p ∧ H < p ∧ 0 < q ∧ (m : ℕ) = q * p ^ 2 := by
    intro m
    have hm := mem_survivors.mp m.property
    exact survivor_large_square m.property (hbad m hm.1 hm.2.1)
  choose p q hp hpH hq heq using hw
  have hqbound : ∀ m : S, q m ≤ Q := by
    intro m
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < (H + 1) ^ 2)).mpr
    have hs : (H + 1) ^ 2 ≤ (p m) ^ 2 := by have := hpH m; nlinarith
    calc
      q m * (H + 1) ^ 2 ≤ q m * (p m) ^ 2 := Nat.mul_le_mul_left _ hs
      _ = (m : ℕ) := (heq m).symm
      _ ≤ N + H := (mem_survivors.mp m.property).2.1
  let f : S → Finset.Icc 1 Q := fun m => ⟨q m, Finset.mem_Icc.mpr ⟨hq m, hqbound m⟩⟩
  have hinj : Function.Injective f := by
    intro m₁ m₂ hf
    have hqq : q m₁ = q m₂ := congrArg (fun x : Finset.Icc 1 Q => (x : ℕ)) hf
    have hm₁ := mem_survivors.mp m₁.property
    have hm₂ := mem_survivors.mp m₂.property
    have hpp : p m₁ = p m₂ := by
      apply same_quotient_square_eq (hpH m₁) (hpH m₂) (hq m₁)
      · simpa only [← heq m₁] using hm₁.1
      · simpa only [← heq m₁] using hm₁.2.1
      · simpa only [hqq, ← heq m₂] using hm₂.1
      · simpa only [hqq, ← heq m₂] using hm₂.2.1
    apply Subtype.ext
    rw [heq m₁, heq m₂, hqq, hpp]
  have hc : S.card ≤ (Finset.Icc 1 Q).card := Finset.card_le_card_of_injective hinj
  have hQ : (Finset.Icc 1 Q).card = Q := by simp only [Nat.card_Icc, Nat.add_sub_cancel]
  exact hc.trans_eq hQ

/-- A necessary size inequality for an entirely nonsquarefree interval. -/
lemma nonsquarefree_interval_mul_sq_le (N H : ℕ) (hH : 48 ≤ H)
    (hbad : ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m) :
    H * (H + 1) ^ 2 ≤ 12 * (N + H) := by
  have hlo := survivors_card_ge_twelfth N H hH
  have hhi : ((survivors N H).card : ℝ) ≤ (((N + H) / (H + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast survivors_card_le_quotients N H hbad
  have hdiv := Nat.cast_div_le (α := ℝ) (m := N + H) (n := (H + 1) ^ 2)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hdiv
  have ht : (H : ℝ) / 12 ≤ ((N : ℝ) + (H : ℝ)) / ((H : ℝ) + 1) ^ 2 :=
    hlo.trans (hhi.trans hdiv)
  have hm := (le_div_iff₀ (by positivity : (0 : ℝ) < ((H : ℝ) + 1) ^ 2)).mp ht
  have hreal : (H : ℝ) * ((H : ℝ) + 1) ^ 2 ≤ 12 * ((N : ℝ) + (H : ℝ)) := by
    nlinarith
  exact_mod_cast hreal

lemma nonsquarefree_interval_cubic_le (N H : ℕ) (hH : 48 ≤ H)
    (hbad : ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m) :
    H ^ 3 ≤ 12 * (N + H) := by
  have h := nonsquarefree_interval_mul_sq_le N H hH hbad
  nlinarith

/-- Explicit natural-interval criterion for the existence of a squarefree number. -/
theorem exists_squarefree_Ioc (N H : ℕ) (hH : 48 ≤ H)
    (hsize : 12 * (N + H) < H ^ 3) :
    ∃ m : ℕ, N < m ∧ m ≤ N + H ∧ Squarefree m := by
  by_contra h
  have hbad : ∀ m : ℕ, N < m → m ≤ N + H → ¬ Squarefree m := by
    intro m hm hm' hsf
    exact h ⟨m, hm, hm', hsf⟩
  have := nonsquarefree_interval_cubic_le N H hH hbad
  omega

/-- The integer length used for the explicit cubic-root bound. -/
noncomputable def cubicLength (N : ℕ) : ℕ := ⌈4 * (N : ℝ) ^ (1 / 3 : ℝ)⌉₊

/-- For `N ≥ 1728`, the rounded length satisfies the interval criterion and
is at most `5 N^(1/3)`. -/
lemma cubicLength_spec (N : ℕ) (hN : 1728 ≤ N) :
    48 ≤ cubicLength N ∧ 12 * (N + cubicLength N) < (cubicLength N) ^ 3 ∧
      (cubicLength N : ℝ) ≤ 5 * (N : ℝ) ^ (1 / 3 : ℝ) := by
  let x : ℝ := (N : ℝ) ^ (1 / 3 : ℝ)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hcube : x ^ 3 = (N : ℝ) := by
    simpa only [x, one_div, Nat.cast_ofNat] using
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) (by decide : (3 : ℕ) ≠ 0))
  have hx : 12 ≤ x := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 12) hx0
      (by decide : (3 : ℕ) ≠ 0)).mp
    rw [hcube]
    norm_num
    exact_mod_cast hN
  have hceil : 4 * x ≤ (cubicLength N : ℝ) := Nat.le_ceil _
  have hceil' : (cubicLength N : ℝ) < 4 * x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hHreal : (48 : ℝ) ≤ (cubicLength N : ℝ) := by linarith
  have hH : 48 ≤ cubicLength N := by exact_mod_cast hHreal
  have hupper : (cubicLength N : ℝ) ≤ 5 * x := by linarith
  have hxN : 2 * x ≤ (N : ℝ) := by
    have hsq : 0 ≤ x ^ 2 - 2 := by nlinarith
    have := mul_nonneg hsq hx0
    nlinarith [hcube]
  have hcH : (4 * x) ^ 3 ≤ (cubicLength N : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hceil 3
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsize : 12 * ((N : ℝ) + (cubicLength N : ℝ)) < (cubicLength N : ℝ) ^ 3 := by
    nlinarith [hcH]
  exact ⟨hH, by exact_mod_cast hsize, hupper⟩

/-- An explicit unconditional cubic-root bound for every `N ≥ 1728`. -/
theorem exists_squarefree_cubic (N : ℕ) (hN : 1728 ≤ N) :
    ∃ m : ℕ, Squarefree m ∧ N < m ∧
      (m : ℝ) ≤ (N : ℝ) + 5 * (N : ℝ) ^ (1 / 3 : ℝ) := by
  obtain ⟨hH, hsize, hlen⟩ := cubicLength_spec N hN
  obtain ⟨m, hNm, hm, hsf⟩ := exists_squarefree_Ioc N (cubicLength N) hH hsize
  refine ⟨m, hsf, hNm, ?_⟩
  have hmreal : (m : ℝ) ≤ (N : ℝ) + (cubicLength N : ℝ) := by exact_mod_cast hm
  linarith

/- ## Gaps in the increasing enumeration of squarefree natural numbers -/

open SquarefreeSqrt

/-- Eventually the gaps are at most `5 (s n)^(1/3)`; `n ≥ 1728` suffices. -/
theorem squarefree_gap_eventually_le_cubic :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((Nat.nth Squarefree (n + 1) : ℝ) - (Nat.nth Squarefree n : ℝ)) ≤
        5 * (Nat.nth Squarefree n : ℝ) ^ (1 / 3 : ℝ) := by
  change ∀ᶠ n : ℕ in Filter.atTop,
    ((s (n + 1) : ℝ) - (s n : ℝ)) ≤ 5 * (s n : ℝ) ^ (1 / 3 : ℝ)
  apply Filter.eventually_atTop.mpr
  refine ⟨1728, ?_⟩
  intro n hn
  have hsn : 1728 ≤ s n := hn.trans (s_strictMono.id_le n)
  obtain ⟨m, hsf, hNm, hm⟩ := exists_squarefree_cubic (s n) hsn
  have hnext : (s (n + 1) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast next_le_of_squarefree hsf hNm
  linarith

/-- Unconditional `O((s n)^ε)` squarefree gaps for every `ε ≥ 1/3`. -/
theorem squarefree_gap_isBigO {ε : ℝ} (hε : 1 / 3 ≤ ε) :
    (fun n => ((Nat.nth Squarefree (n + 1) : ℝ) - (Nat.nth Squarefree n : ℝ)))
      =O[Filter.atTop] (fun n => (Nat.nth Squarefree n : ℝ) ^ ε) := by
  change (fun n => ((s (n + 1) : ℝ) - (s n : ℝ)))
    =O[Filter.atTop] (fun n => (s n : ℝ) ^ ε)
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨5, ?_⟩
  have hgap : ∀ᶠ n : ℕ in Filter.atTop,
      ((s (n + 1) : ℝ) - (s n : ℝ)) ≤ 5 * (s n : ℝ) ^ (1 / 3 : ℝ) :=
    squarefree_gap_eventually_le_cubic
  filter_upwards [hgap] with n hn
  simp only [Real.norm_eq_abs, abs_of_pos (gap_pos n),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (s n)) ε)]
  apply hn.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 5)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast s_pos n) hε

/-- In particular, the exponent is exactly `1/3`, unconditionally. -/
theorem squarefree_gap_isBigO_cubic :
    (fun n => ((Nat.nth Squarefree (n + 1) : ℝ) - (Nat.nth Squarefree n : ℝ)))
      =O[Filter.atTop] (fun n => (Nat.nth Squarefree n : ℝ) ^ (1 / 3 : ℝ)) :=
  squarefree_gap_isBigO (le_refl _)

#print axioms prime_reciprocal_sq_sum_le
#print axioms prime_mod_six
#print axioms primesUpTo_card_le
#print axioms smallPrimeCover_card_le
#print axioms survivors_card_le_quotients
#print axioms nonsquarefree_interval_cubic_le
#print axioms exists_squarefree_Ioc
#print axioms cubicLength_spec
#print axioms exists_squarefree_cubic
#print axioms squarefree_gap_eventually_le_cubic
#print axioms squarefree_gap_isBigO
#print axioms squarefree_gap_isBigO_cubic

end SquarefreeCubic
