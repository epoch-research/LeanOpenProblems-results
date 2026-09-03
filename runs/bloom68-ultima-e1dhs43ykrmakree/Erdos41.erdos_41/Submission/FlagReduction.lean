import Submission.Flags

/-!
# Exact finite-flag reduction for the critical liminf question

These results do not prove the finite obstruction. They identify it exactly
with the original zero-liminf assertion, independently of `Submission.Spec`.
-/

open Filter Set

namespace Work

/-- Counting positive elements up to `N` is bounded by counting all elements below `N+1`. -/
theorem ncard_inter_Icc_le_count (A : Set ℕ) (N : ℕ) :
    (A ∩ Icc 1 N).ncard ≤ @Nat.count (· ∈ A) (Classical.decPred _) (N + 1) := by
  classical
  rw [Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
  intro a ha
  rcases ha with ⟨haA, haLower, haUpper⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), haA⟩

/-- A positive lower critical counting bound gives a cubic bound for the increasing enumeration. -/
theorem exists_cubic_enumeration_of_liminf_ne_zero {A : Set ℕ}
    (hTriple : NtupleCondition A 3) (hInfinite : A.Infinite)
    (hL : Filter.atTop.liminf
      (fun N : ℕ => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) ≠ 0) :
    ∃ K : ℕ, ∃ f : ℕ → ℕ, StrictMono f ∧
      (∀ i, f i ≤ K * (i + 1)^3) ∧ Set.range f = A := by
  classical
  obtain ⟨c, hc, htail⟩ := hTriple.liminf_ratio_ne_zero_iff.mp hL
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp htail
  obtain ⟨K, hK⟩ := exists_nat_gt (max ((max N₀ 1 : ℕ) : ℝ) ((1 / c)^3))
  have hKN : max N₀ 1 ≤ K := by
    exact_mod_cast (le_max_left _ _).trans hK.le
  have hKc : (1 / c)^3 ≤ (K : ℝ) := (le_max_right _ _).trans hK.le
  let f : ℕ → ℕ := Nat.nth (· ∈ A)
  have hf : StrictMono f := Nat.nth_strictMono hInfinite
  have hrange : Set.range f = A := Nat.range_nth_of_infinite hInfinite
  refine ⟨K, f, hf, ?_, hrange⟩
  intro i
  by_cases hsmall : f i < max N₀ 1
  · have hone : 1 ≤ (i + 1)^3 := one_le_pow₀ (by omega)
    calc
      f i ≤ K := (Nat.le_of_lt hsmall).trans hKN
      _ = K * 1 := (Nat.mul_one K).symm
      _ ≤ K * (i + 1)^3 := Nat.mul_le_mul_left K hone
  · have hbig : max N₀ 1 ≤ f i := Nat.le_of_not_gt hsmall
    have hpos : (0 : ℝ) < f i := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hbig))
    have hrootpos : 0 < (f i : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hpos _
    have hrootcube : ((f i : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (f i : ℝ) := by
      simpa only [one_div, Nat.cast_ofNat] using
        (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (f i)) (by decide : (3 : ℕ) ≠ 0))
    have hcount : (A ∩ Icc 1 (f i)).ncard ≤ i + 1 := by
      calc
        (A ∩ Icc 1 (f i)).ncard ≤ Nat.count (· ∈ A) (f i + 1) :=
          ncard_inter_Icc_le_count A (f i)
        _ = i + 1 := Nat.count_nth_succ_of_infinite hInfinite i
    have hcountR : ((A ∩ Icc 1 (f i)).ncard : ℝ) ≤ (i : ℝ) + 1 := by
      exact_mod_cast hcount
    have hcr : c * (f i : ℝ) ^ (1 / 3 : ℝ) ≤ (i : ℝ) + 1 :=
      ((le_div_iff₀ hrootpos).mp (hN₀ (f i) ((le_max_left _ _).trans hbig))).trans hcountR
    have hr : (f i : ℝ) ^ (1 / 3 : ℝ) ≤ ((i : ℝ) + 1) / c := by
      apply (le_div_iff₀ hc).mpr
      simpa [mul_comm] using hcr
    have hboundR : (f i : ℝ) ≤ (K : ℝ) * ((i : ℝ) + 1)^3 := by
      calc
        (f i : ℝ) = ((f i : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := hrootcube.symm
        _ ≤ (((i : ℝ) + 1) / c)^3 := pow_le_pow_left₀ hrootpos.le hr 3
        _ = (1 / c)^3 * ((i : ℝ) + 1)^3 := by ring
        _ ≤ (K : ℝ) * ((i : ℝ) + 1)^3 := mul_le_mul_of_nonneg_right hKc (by positivity)
    exact_mod_cast hboundR

/-- The first `k` positive-indexed values of an increasing sequence are distinct positive elements. -/
theorem index_le_ncard_of_le {f : ℕ → ℕ} (hf : StrictMono f) {k N : ℕ}
    (hN : f k ≤ N) : k ≤ (Set.range f ∩ Icc 1 N).ncard := by
  have hfinite : (Set.range f ∩ Icc 1 N).Finite :=
    (Set.finite_Icc 1 N).inter_of_right _
  have hcard : (Icc 1 k : Set ℕ).ncard = k := by
    rw [← Finset.coe_Icc, Set.ncard_coe_finset]
    simp [Nat.card_Icc]
  rw [← hcard]
  apply Set.ncard_le_ncard_of_injOn f _ hf.injective.injOn hfinite
  intro i hi
  refine ⟨⟨i, rfl⟩, ?_, ?_⟩
  · exact hi.1.trans (hf.id_le i)
  · exact (hf.monotone hi.2).trans hN

/-- A cubic-bounded infinite flag has a nonzero critical liminf; zero in the range causes no issue. -/
theorem liminf_range_ne_zero_of_cubic_bound {f : ℕ → ℕ} {K : ℕ}
    (hf : StrictMono f) (hbound : ∀ i, f i ≤ K * (i + 1)^3)
    (hTriple : NtupleCondition (Set.range f) 3) :
    Filter.atTop.liminf
      (fun N : ℕ => (Set.range f ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) ≠ 0 := by
  have hK : 0 < K := by
    have h1 : 1 ≤ f 1 := hf.id_le 1
    have h2 := hbound 1
    norm_num at h2
    nlinarith
  have hKcube : K ≤ K^3 := by
    have hKsq : 1 ≤ K^2 := one_le_pow₀ (Nat.one_le_iff_ne_zero.mpr hK.ne')
    nlinarith
  apply hTriple.liminf_ratio_ne_zero_iff.mpr
  refine ⟨1 / (2 * (K : ℝ)), by positivity, ?_⟩
  apply Filter.eventually_atTop.mpr
  refine ⟨max 1 (K * 27), ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hN))
  let m := (Set.range f ∩ Icc 1 N).ncard
  have hm : 2 ≤ m := by
    apply index_le_ncard_of_le hf
    have h2 := hbound 2
    norm_num at h2
    exact h2.trans ((le_max_right _ _).trans hN)
  have hnext : N < f (m + 1) := by
    by_contra! hbad
    have htoo := index_le_ncard_of_le hf hbad
    change m + 1 ≤ m at htoo
    omega
  have hNcube : N ≤ (2 * K * m)^3 := by
    calc
      N ≤ K * (m + 2)^3 := hnext.le.trans (by simpa [Nat.add_assoc] using hbound (m + 1))
      _ ≤ K * (2 * m)^3 := Nat.mul_le_mul_left K (Nat.pow_le_pow_left (by omega) 3)
      _ = 8 * K * m^3 := by ring
      _ ≤ 8 * K^3 * m^3 := Nat.mul_le_mul_right (m^3) (Nat.mul_le_mul_left 8 hKcube)
      _ = (2 * K * m)^3 := by ring
  have hroot : (N : ℝ) ^ (1 / 3 : ℝ) ≤ 2 * (K : ℝ) * (m : ℝ) := by
    rw [one_div]
    apply (Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg N) (by positivity)
      (by norm_num : (0 : ℝ) < 3)).mpr
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
    exact_mod_cast hNcube
  have hdenom : (0 : ℝ) < 2 * K := by positivity
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hNpos _)).mpr
  change 1 / (2 * (K : ℝ)) * (N : ℝ) ^ (1 / 3 : ℝ) ≤ (m : ℝ)
  calc
    1 / (2 * (K : ℝ)) * (N : ℝ) ^ (1 / 3 : ℝ) =
        ((N : ℝ) ^ (1 / 3 : ℝ)) / (2 * (K : ℝ)) := by ring
    _ ≤ (m : ℝ) := (div_le_iff₀ hdenom).mpr (by simpa [mul_comm] using hroot)

/-- Exact equivalence with a uniform finite obstruction. The right-hand side is not proved here. -/
theorem zero_liminf_iff_finite_cubic_flag_extinction :
    (∀ A : Set ℕ, NtupleCondition A 3 → A.Infinite →
      Filter.atTop.liminf
        (fun N : ℕ => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) = 0) ↔
    ∀ K : ℕ, ∃ n : ℕ, ¬ FiniteCubicFlag K n := by
  constructor
  · intro hZero K
    by_contra! hFlags
    obtain ⟨f, hf, hbound, hTriple⟩ := infiniteCubicFlag_of_forall_finiteCubicFlag hFlags
    exact liminf_range_ne_zero_of_cubic_bound hf hbound hTriple
      (hZero (Set.range f) hTriple (Set.infinite_range_of_injective hf.injective))
  · intro hFlags A hTriple hInfinite
    by_contra hL
    obtain ⟨K, f, hf, hbound, hRange⟩ :=
      exists_cubic_enumeration_of_liminf_ne_zero hTriple hInfinite hL
    have hFlag : InfiniteCubicFlag K := ⟨f, hf, hbound, hRange ▸ hTriple⟩
    obtain ⟨n, hn⟩ := hFlags K
    exact hn (hFlag.finiteCubicFlag n)

/-- The counterexample formulation is also exactly equivalent to unbounded finite flags
with one fixed cubic constant. Neither side is asserted here. -/
theorem counterexample_iff_unbounded_finite_cubic_flags :
    (∃ A : Set ℕ, NtupleCondition A 3 ∧ A.Infinite ∧
      Filter.atTop.liminf
        (fun N : ℕ => (A ∩ Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) ≠ 0) ↔
    ∃ K : ℕ, ∀ n : ℕ, FiniteCubicFlag K n := by
  constructor
  · rintro ⟨A, hTriple, hInfinite, hL⟩
    obtain ⟨K, f, hf, hbound, hRange⟩ :=
      exists_cubic_enumeration_of_liminf_ne_zero hTriple hInfinite hL
    have hFlag : InfiniteCubicFlag K := ⟨f, hf, hbound, hRange ▸ hTriple⟩
    exact ⟨K, hFlag.finiteCubicFlag⟩
  · rintro ⟨K, hFlags⟩
    obtain ⟨f, hf, hbound, hTriple⟩ := infiniteCubicFlag_of_forall_finiteCubicFlag hFlags
    exact ⟨Set.range f, hTriple, Set.infinite_range_of_injective hf.injective,
      liminf_range_ne_zero_of_cubic_bound hf hbound hTriple⟩

end Work

#print axioms Work.counterexample_iff_unbounded_finite_cubic_flags
#print axioms Work.exists_cubic_enumeration_of_liminf_ne_zero
#print axioms Work.liminf_range_ne_zero_of_cubic_bound
#print axioms Work.zero_liminf_iff_finite_cubic_flag_extinction
