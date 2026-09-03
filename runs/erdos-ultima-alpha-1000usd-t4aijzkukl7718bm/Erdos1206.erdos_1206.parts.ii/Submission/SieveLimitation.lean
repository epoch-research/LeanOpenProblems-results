import FormalConjecturesUtil

/-! Auxiliary results only. Avoiding one family of cubic collisions is not the same
as being cube-Sidon. -/

namespace Erdos1206
open Filter Finset

/-- The first root of the explicit polynomial taxicab family. -/
def taxicabFirst (m : ℕ) : ℕ :=
  1296 * m ^ 5 + 864 * m ^ 4 + 312 * m ^ 3 + 84 * m ^ 2 + 13 * m + 1

private lemma taxicabFirst_bound (m : ℕ) :
    648 * (m + 1) * (m + 2) ≤ taxicabFirst (m + 1) := by
  dsimp [taxicabFirst]
  ring_nf
  omega

private lemma taxicabFirst_gt (m : ℕ) : m < taxicabFirst (m + 1) := by
  dsimp [taxicabFirst]
  ring_nf
  omega

private lemma telescope_reciprocal (N : ℕ) :
    ∑ m ∈ range N, (1 : ℝ) / ((m + 1) * (m + 2)) = 1 - 1 / (N + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ, ih]
    push_cast
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

private lemma first_reciprocal_sum (N : ℕ) :
    ∑ m ∈ range N, (1 : ℝ) / taxicabFirst (m + 1) ≤ 1 / 648 := by
  calc
    _ ≤ ∑ m ∈ range N, (1 : ℝ) / (648 * (m + 1) * (m + 2)) := by
      apply sum_le_sum
      intro m hm
      apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast taxicabFirst_bound m
    _ = (1 / 648) * (1 - 1 / (N + 1)) := by
      rw [← telescope_reciprocal, mul_sum]
      apply sum_congr rfl
      intro m hm
      simp only [one_div, mul_inv_rev]
      ring
    _ ≤ 1 / 648 := by
      have : (0 : ℝ) ≤ 1 / (N + 1) := by positivity
      linarith

/-- A sieve avoiding every positive multiple of the first roots. -/
def taxicabFamilyAvoider : Set ℕ :=
  {n | ∀ m : ℕ, ¬ taxicabFirst (m + 1) ∣ n}

private lemma sieve_complement_count (N : ℕ) :
    ((Set.Iio N \ taxicabFamilyAvoider).ncard : ℝ) ≤ 1 + N / 648 := by
  classical
  let S (m : ℕ) := (range (N + 1)).filter
    (fun n => n ≠ 0 ∧ taxicabFirst (m + 1) ∣ n)
  let U := (range N).biUnion S
  have hsub : Set.Iio N \ taxicabFamilyAvoider ⊆ ({0} : Set ℕ) ∪ (U : Set ℕ) := by
    intro n hn
    have hnN : n < N := hn.1
    by_cases hn0 : n = 0
    · exact Or.inl hn0
    · apply Or.inr
      have hnA := hn.2
      simp only [taxicabFamilyAvoider, Set.mem_setOf_eq, not_forall, not_not] at hnA
      obtain ⟨m, hm⟩ := hnA
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hm
      have hmN : m < N := lt_trans (taxicabFirst_gt m) (lt_of_le_of_lt hle hn.1)
      exact mem_biUnion.mpr ⟨m, mem_range.mpr hmN,
        mem_filter.mpr ⟨mem_range.mpr (by omega), hn0, hm⟩⟩
  have hc := Set.ncard_le_ncard hsub ((Set.finite_singleton 0).union U.finite_toSet)
  have hu := Set.ncard_union_le ({0} : Set ℕ) (U : Set ℕ)
  have hb : U.card ≤ ∑ m ∈ range N, (S m).card := card_biUnion_le
  have heq (m : ℕ) : (S m).card = N / taxicabFirst (m + 1) :=
    Nat.card_multiples' N (taxicabFirst (m + 1))
  simp only [Set.ncard_singleton, Set.ncard_coe_finset] at hc hu
  have hn : (Set.Iio N \ taxicabFamilyAvoider).ncard ≤
      1 + ∑ m ∈ range N, N / taxicabFirst (m + 1) := by
    simp_rw [heq] at hb
    omega
  have hn' : ((Set.Iio N \ taxicabFamilyAvoider).ncard : ℝ) ≤
      1 + ∑ m ∈ range N, ((N / taxicabFirst (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast hn
  have hsum : (∑ m ∈ range N, ((N / taxicabFirst (m + 1) : ℕ) : ℝ)) ≤
      (N : ℝ) / 648 := by
    calc
      _ ≤ ∑ m ∈ range N, (N : ℝ) / taxicabFirst (m + 1) := by
        apply sum_le_sum
        intro m hm
        exact Nat.cast_div_le
      _ = (N : ℝ) * (∑ m ∈ range N, (1 : ℝ) / taxicabFirst (m + 1)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro m hm
        ring
      _ ≤ (N : ℝ) * (1 / 648) :=
        mul_le_mul_of_nonneg_left (first_reciprocal_sum N) (by positivity)
      _ = (N : ℝ) / 648 := by ring
  linarith

lemma taxicabFamilyAvoider_lowerDensity :
    647 / 648 ≤ taxicabFamilyAvoider.lowerDensity := by
  have hp (N : ℕ) : (647 / 648 : ℝ) * N ≤
      ((taxicabFamilyAvoider ∩ Set.Iio N).ncard : ℝ) + 1 := by
    have hcomp := sieve_complement_count N
    have hc : (Set.Iio N \ taxicabFamilyAvoider).ncard +
        (taxicabFamilyAvoider ∩ Set.Iio N).ncard = N := by
      simpa [Set.diff_inter, Nat.ncard_Iio] using
        Set.ncard_diff_add_ncard_of_subset
          (s := taxicabFamilyAvoider ∩ Set.Iio N) (t := Set.Iio N)
          Set.inter_subset_right
    have hc' : ((Set.Iio N \ taxicabFamilyAvoider).ncard : ℝ) +
        ((taxicabFamilyAvoider ∩ Set.Iio N).ncard : ℝ) = N := by exact_mod_cast hc
    linarith
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  have heps : 0 < (647 / 648 : ℝ) - c := by linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ((647 / 648 : ℝ) - c))
  have hev : ∀ᶠ N : ℕ in atTop, c ≤ taxicabFamilyAvoider.partialDensity Set.univ N := by
    apply eventually_atTop.mpr
    refine ⟨M + 1, fun N hN => ?_⟩
    have hN0 : 0 < N := by omega
    have hMN : (M : ℝ) < N := by exact_mod_cast (show M < N by omega)
    have hlarge := (div_lt_iff₀ heps).mp (hM.trans hMN)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    apply (le_div_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN0)).mpr
    nlinarith [hp N]
  exact le_liminf_of_le
    (isCoboundedUnder_ge_of_le atTop (fun N => Set.partialDensity_le_one _ Set.univ N)) hev

lemma avoids_dilated_polynomial_family (m r : ℕ) :
    r * taxicabFirst (m + 1) ∉ taxicabFamilyAvoider := by
  intro h
  exact h m (dvd_mul_left _ _)

/-- The sieve does not solve the original problem: it retains the 1729 collision. -/
lemma taxicabFamilyAvoider_not_cube_sidon :
    ¬ IsSidon ((fun a : ℕ => a ^ 3) '' taxicabFamilyAvoider) := by
  have hmem (n : ℕ) (hn : 0 < n) (hn12 : n ≤ 12) : n ∈ taxicabFamilyAvoider := by
    intro m hm
    have hle := Nat.le_of_dvd hn hm
    have hlarge : 12 < taxicabFirst (m + 1) := by
      dsimp [taxicabFirst]
      omega
    omega
  intro hA
  have h := hA (1 ^ 3) ⟨1, hmem 1 (by decide) (by decide), rfl⟩
    (9 ^ 3) ⟨9, hmem 9 (by decide) (by decide), rfl⟩
    (12 ^ 3) ⟨12, hmem 12 (by decide) (by decide), rfl⟩
    (10 ^ 3) ⟨10, hmem 10 (by decide) (by decide), rfl⟩ (by norm_num)
  norm_num at h

lemma dense_set_avoiding_polynomial_family :
    ∃ A : Set ℕ, A.Infinite ∧ 647 / 648 ≤ A.lowerDensity ∧
      (∀ m r : ℕ, r * taxicabFirst (m + 1) ∉ A) ∧
      ¬ IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  refine ⟨taxicabFamilyAvoider, ?_, taxicabFamilyAvoider_lowerDensity,
    avoids_dilated_polynomial_family, taxicabFamilyAvoider_not_cube_sidon⟩
  by_contra hfin
  have hzero : taxicabFamilyAvoider.lowerDensity = 0 :=
    (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
  have h := taxicabFamilyAvoider_lowerDensity
  rw [hzero] at h
  norm_num at h

end Erdos1206
