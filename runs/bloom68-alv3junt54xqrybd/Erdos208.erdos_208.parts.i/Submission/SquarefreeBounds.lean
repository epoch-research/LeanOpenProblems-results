import FormalConjecturesUtil

/-!
# An elementary square-root bound for gaps between squarefree natural numbers

We count multiples of every square `d^2`, not just prime squares.  The finite
reciprocal-square sum is at most `3/4`, by retaining the term `d = 2` exactly
and bounding the remaining terms by a telescoping sum.  Consequently at most
`3 H / 4 + Nat.sqrt (N + H)` numbers of `(N, N + H]` are nonsquarefree.
No analytic squarefree-counting theorem is used.
-/

open scoped BigOperators

namespace SquarefreeSqrt

/-- The number of multiples of a positive divisor in a translated interval. -/
lemma multiples_Ioc_card_le (N H a : ℕ) (ha : 0 < a) :
    (((Finset.Ioc N (N + H)).filter (fun m => a ∣ m)).card : ℝ) ≤
      (H : ℝ) / (a : ℝ) + 1 := by
  have hd : Disjoint
      ((Finset.Ioc 0 N).filter (fun m => a ∣ m))
      ((Finset.Ioc N (N + H)).filter (fun m => a ∣ m)) :=
    (Finset.Ioc_disjoint_Ioc_of_le (le_refl N)).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsplit := Finset.card_union_of_disjoint hd
  rw [← Finset.filter_union,
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le N) (Nat.le_add_right N H),
    Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.add_div ha] at hsplit
  have hcount : ((Finset.Ioc N (N + H)).filter (fun m => a ∣ m)).card ≤ H / a + 1 := by
    split_ifs at hsplit <;> omega
  calc
    (((Finset.Ioc N (N + H)).filter (fun m => a ∣ m)).card : ℝ)
        ≤ ((H / a + 1 : ℕ) : ℝ) := by exact_mod_cast hcount
    _ = ((H / a : ℕ) : ℝ) + 1 := by simp
    _ ≤ (H : ℝ) / (a : ℝ) + 1 :=
      add_le_add (Nat.cast_div_le (α := ℝ) (m := H) (n := a)) (le_refl 1)

/-- A finite, elementary bound for the sum of reciprocal squares from `2` onwards. -/
lemma reciprocal_sq_sum_le (K : ℕ) :
    (∑ d ∈ Finset.Icc 2 K, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 3 / 4 := by
  by_cases hK : 2 ≤ K
  · have hstrong :
        (∑ d ∈ Finset.Icc 2 K, (1 : ℝ) / (d : ℝ) ^ 2) ≤
          3 / 4 - 1 / (K : ℝ) := by
      induction K, hK using Nat.le_induction with
      | base => norm_num
      | succ k hk ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
        have hk1pos : 0 < (k : ℝ) + 1 := by positivity
        have htel : (1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1) =
            1 / ((k : ℝ) * ((k : ℝ) + 1)) := by
          field_simp [ne_of_gt hkpos, ne_of_gt hk1pos]
          ring
        have hstep : (1 : ℝ) / ((k : ℝ) + 1) ^ 2 ≤
            1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
          rw [htel]
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
        simp only [Nat.cast_add, Nat.cast_one]
        linarith
    exact hstrong.trans (sub_le_self _ (by positivity))
  · rw [Finset.Icc_eq_empty_of_lt (by omega)]
    norm_num

/-- The elementary union bound for nonsquarefree numbers in `(N, N+H]`. -/
lemma nonsquarefree_Ioc_card_le (N H : ℕ) :
    (((Finset.Ioc N (N + H)).filter (fun m => ¬ Squarefree m)).card : ℝ) ≤
      (3 / 4 : ℝ) * (H : ℝ) + (Nat.sqrt (N + H) : ℝ) := by
  let D := Finset.Icc 2 (Nat.sqrt (N + H))
  let A := fun d : ℕ => (Finset.Ioc N (N + H)).filter (fun m => d ^ 2 ∣ m)
  have hcover : (Finset.Ioc N (N + H)).filter (fun m => ¬ Squarefree m) ⊆
      D.biUnion A := by
    intro m hm
    obtain ⟨hmI, hmns⟩ := Finset.mem_filter.mp hm
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hmI).1
    rw [Nat.squarefree_iff_prime_squarefree] at hmns
    push_neg at hmns
    obtain ⟨p, hp, hpdvd⟩ := hmns
    have hpdvd' : p ^ 2 ∣ m := by simpa only [pow_two] using hpdvd
    have hpbound : p ^ 2 ≤ N + H :=
      (Nat.le_of_dvd hmpos hpdvd').trans (Finset.mem_Ioc.mp hmI).2
    exact Finset.mem_biUnion.mpr
      ⟨p, Finset.mem_Icc.mpr ⟨hp.two_le, Nat.le_sqrt'.mpr hpbound⟩,
        Finset.mem_filter.mpr ⟨hmI, hpdvd'⟩⟩
  have hDcard : (D.card : ℝ) ≤ (Nat.sqrt (N + H) : ℝ) := by
    apply Nat.cast_le.mpr
    dsimp [D]
    rw [Nat.card_Icc]
    omega
  calc
    (((Finset.Ioc N (N + H)).filter (fun m => ¬ Squarefree m)).card : ℝ)
        ≤ ((D.biUnion A).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ d ∈ D, ((A d).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le : (D.biUnion A).card ≤ ∑ d ∈ D, (A d).card)
    _ ≤ ∑ d ∈ D, ((H : ℝ) / (d : ℝ) ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d ^ 2 := by
        have : 2 ≤ d := (Finset.mem_Icc.mp hd).1
        positivity
      simpa only [A, Nat.cast_pow] using multiples_Ioc_card_le N H (d ^ 2) hdpos
    _ = (H : ℝ) * (∑ d ∈ D, (1 : ℝ) / (d : ℝ) ^ 2) + (D.card : ℝ) := by
      simp only [div_eq_mul_inv, one_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (H : ℝ) * (3 / 4) + (Nat.sqrt (N + H) : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left (reciprocal_sq_sum_le _) (Nat.cast_nonneg H)) hDcard
    _ = (3 / 4 : ℝ) * (H : ℝ) + (Nat.sqrt (N + H) : ℝ) := by ring

/-- Any interval long enough for the elementary union bound contains a squarefree number. -/
theorem exists_squarefree_Ioc (N H : ℕ) (hH : 4 * Nat.sqrt (N + H) < H) :
    ∃ m : ℕ, N < m ∧ m ≤ N + H ∧ Squarefree m := by
  by_contra h
  have hbad : (Finset.Ioc N (N + H)).filter (fun m => ¬ Squarefree m) =
      Finset.Ioc N (N + H) := by
    apply Finset.filter_eq_self.mpr
    intro m hm hsf
    exact h ⟨m, (Finset.mem_Ioc.mp hm).1, (Finset.mem_Ioc.mp hm).2, hsf⟩
  have hcount := nonsquarefree_Ioc_card_le N H
  rw [hbad, Nat.card_Ioc, Nat.add_sub_cancel_left] at hcount
  have hHreal : 4 * (Nat.sqrt (N + H) : ℝ) < (H : ℝ) := by exact_mod_cast hH
  linarith

/-- A fully explicit integer-length square-root gap bound, valid even at `N = 0`. -/
theorem exists_squarefree_nat_sqrt (N : ℕ) :
    ∃ m : ℕ, N < m ∧ m ≤ N + (8 * Nat.sqrt N + 32) ∧ Squarefree m := by
  apply exists_squarefree_Ioc
  have hroot : Nat.sqrt (N + (8 * Nat.sqrt N + 32)) ≤ Nat.sqrt N + 5 := by
    have hN := Nat.lt_succ_sqrt' N
    simp only [Nat.succ_eq_add_one] at hN
    have hs : N + (8 * Nat.sqrt N + 32) < (Nat.sqrt N + 6) ^ 2 := by nlinarith
    have ht := Nat.sqrt_lt'.mpr hs
    omega
  omega

/-- Every integer `N ≥ 16` has a squarefree integer in `(N, N + 16 √N]`. -/
theorem exists_squarefree_sqrt (N : ℕ) (hN : 16 ≤ N) :
    ∃ m : ℕ, Squarefree m ∧ N < m ∧ (m : ℝ) ≤ (N : ℝ) + 16 * Real.sqrt (N : ℝ) := by
  obtain ⟨m, hNm, hmupper, hmsf⟩ := exists_squarefree_nat_sqrt N
  refine ⟨m, hmsf, hNm, ?_⟩
  have hupper : (m : ℝ) ≤ (N : ℝ) + (8 * (Nat.sqrt N : ℝ) + 32) := by
    exact_mod_cast hmupper
  have hroot : 4 ≤ Real.sqrt (N : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)).mpr
    exact_mod_cast hN
  have hfloor := (Real.nat_sqrt_le_real_sqrt (a := N))
  linarith

/-- A version with a uniform constant for all positive integers. -/
theorem exists_squarefree_sqrt_pos (N : ℕ) (hN : 0 < N) :
    ∃ m : ℕ, Squarefree m ∧ N < m ∧ (m : ℝ) ≤ (N : ℝ) + 40 * Real.sqrt (N : ℝ) := by
  obtain ⟨m, hNm, hmupper, hmsf⟩ := exists_squarefree_nat_sqrt N
  refine ⟨m, hmsf, hNm, ?_⟩
  have hupper : (m : ℝ) ≤ (N : ℝ) + (8 * (Nat.sqrt N : ℝ) + 32) := by
    exact_mod_cast hmupper
  have hroot : 1 ≤ Real.sqrt (N : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg N)).mpr
    exact_mod_cast hN
  have hfloor := (Real.nat_sqrt_le_real_sqrt (a := N))
  linarith

/- ## Consequences for the increasing enumeration -/

noncomputable def s : ℕ → ℕ := Nat.nth Squarefree

lemma infinite_squarefree : {n : ℕ | Squarefree n}.Infinite :=
  Nat.infinite_setOf_prime.mono (fun _ hp => hp.squarefree)

lemma s_strictMono : StrictMono s := Nat.nth_strictMono infinite_squarefree

lemma s_squarefree (n : ℕ) : Squarefree (s n) :=
  Nat.nth_mem_of_infinite infinite_squarefree n

lemma s_pos (n : ℕ) : 0 < s n := Nat.pos_of_ne_zero (s_squarefree n).ne_zero

lemma s_next (n : ℕ) : s n < s (n + 1) := s_strictMono (Nat.lt_succ_self n)

lemma gap_pos (n : ℕ) : 0 < (s (n + 1) - s n : ℝ) :=
  sub_pos.mpr (by exact_mod_cast s_next n)

lemma next_le_of_squarefree {n m : ℕ} (hm : Squarefree m) (h : s n < m) :
    s (n + 1) ≤ m := by
  apply (Nat.isLeast_nth_of_infinite infinite_squarefree (n + 1)).2
  refine ⟨hm, ?_⟩
  intro k hk
  exact lt_of_le_of_lt (s_strictMono.monotone (by omega : k ≤ n)) h

/-- In particular the real-valued gaps are bounded by `40 √(s n)` for every index. -/
theorem gap_le_sqrt (n : ℕ) :
    (s (n + 1) - s n : ℝ) ≤ 40 * Real.sqrt (s n : ℝ) := by
  obtain ⟨m, hmsf, hNm, hmupper⟩ := exists_squarefree_sqrt_pos (s n) (s_pos n)
  have hnext : (s (n + 1) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast next_le_of_squarefree hmsf hNm
  linarith

/-- Eventually the gaps satisfy the sharper bound with constant `16` (indeed for `n ≥ 16`). -/
theorem squarefree_gap_eventually_le_sqrt :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Nat.nth Squarefree (n + 1) - Nat.nth Squarefree n : ℝ) ≤
        16 * Real.sqrt (Nat.nth Squarefree n : ℝ) := by
  change ∀ᶠ n : ℕ in Filter.atTop,
    (s (n + 1) - s n : ℝ) ≤ 16 * Real.sqrt (s n : ℝ)
  apply Filter.eventually_atTop.mpr
  refine ⟨16, ?_⟩
  intro n hn
  have hsn : 16 ≤ s n := hn.trans (s_strictMono.id_le n)
  obtain ⟨m, hmsf, hNm, hmupper⟩ := exists_squarefree_sqrt (s n) hsn
  have hnext : (s (n + 1) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast next_le_of_squarefree hmsf hNm
  linarith

/-- Unconditional `O(x^ε)` squarefree gaps for every `ε ≥ 1/2`. -/
theorem squarefree_gap_isBigO {ε : ℝ} (hε : 1 / 2 ≤ ε) :
    (fun n => (Nat.nth Squarefree (n + 1) - Nat.nth Squarefree n : ℝ))
      =O[Filter.atTop] (fun n => (Nat.nth Squarefree n : ℝ) ^ ε) := by
  change (fun n => (s (n + 1) - s n : ℝ))
    =O[Filter.atTop] (fun n => (s n : ℝ) ^ ε)
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨16, ?_⟩
  have hgap : ∀ᶠ n : ℕ in Filter.atTop,
      (s (n + 1) - s n : ℝ) ≤ 16 * Real.sqrt (s n : ℝ) :=
    squarefree_gap_eventually_le_sqrt
  filter_upwards [hgap] with n hn
  simp only [Real.norm_eq_abs, abs_of_pos (gap_pos n),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (s n)) ε)]
  apply hn.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast s_pos n) hε

#print axioms multiples_Ioc_card_le
#print axioms reciprocal_sq_sum_le
#print axioms nonsquarefree_Ioc_card_le
#print axioms exists_squarefree_Ioc
#print axioms exists_squarefree_nat_sqrt
#print axioms exists_squarefree_sqrt
#print axioms exists_squarefree_sqrt_pos
#print axioms gap_le_sqrt
#print axioms squarefree_gap_eventually_le_sqrt
#print axioms squarefree_gap_isBigO

end SquarefreeSqrt
