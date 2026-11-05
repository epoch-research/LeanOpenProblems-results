import FormalConjecturesUtil

/-!
# Erdős Problem 138

*References:*
- [erdosproblems.com/138](https://www.erdosproblems.com/138)
- [Be68] Berlekamp, E. R., A construction for partitions which avoid long arithmetic progressions. Canad. Math. Bull. (1968), 409-414.
- [Er80] Erdős, Paul, A survey of problems in combinatorial number theory. Ann. Discrete Math. (1980), 89-115.
- [Er81] Erdős, P., On the combinatorial problems which I would most like to see solved. Combinatorica (1981), 25-42.
- [Go01] Gowers, W. T., A new proof of Szemerédi's theorem. Geom. Funct. Anal. (2001), 465-588.
-/

open Nat Filter

namespace Erdos138

/--
The set of natural numbers that guarantee a monochromatic arithmetic progression.

A number `N` belongs to this set if, for a given number of colors `r` and an arithmetic
progression length `k`, any `r`-coloring of the integers `{1, ..., N}` must contain a
monochromatic arithmetic progression of length `k`.
-/
def monoAP_guarantee_set (r k : ℕ) : Set ℕ :=
  { N | ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k}

/--
The **van der Waerden number**, is the smallest integer `N` such that any `r`-coloring of
`{1, ..., N}` is guaranteed to contain a monochromatic arithmetic progression of
length `k`. It is defined as the infimum of the (non-empty) set of all such numbers `N`.
-/
noncomputable def monoAPNumber (r k : ℕ) : ℕ := sInf (monoAP_guarantee_set r k)

/--
An abbreviation for the van der Waerden number for 2 colors, commonly written as `W(k)`.
This represents the smallest integer `N` such that any 2-coloring of `{1, ..., N}`
must contain a monochromatic arithmetic progression of length `k`.
-/
noncomputable abbrev W : ℕ → ℕ := monoAPNumber 2


/- Verified threshold and quantitative-growth prerequisites. -/

open scoped BigOperators

def RootGrowth : Prop :=
  atTop.Tendsto (fun k => (W k : ℝ) ^ (1 / (k : ℝ))) atTop

-- At length 0 the empty progression works, provided a color exists.
theorem contains_zero {N : ℕ} (coloring : Finset.Icc 1 N → Fin 2) :
    ContainsMonoAPofLength coloring 0 := by
  refine ⟨0, ∅, ?_, ?_⟩ <;> simp


-- Every finite interval contains at most N distinct values.
theorem length_le_interval {N k : ℕ} (coloring : Finset.Icc 1 N → Fin 2)
    (h : ContainsMonoAPofLength coloring k) : k ≤ N := by
  obtain ⟨c, ap, hap, hc⟩ := h
  have hs : (Subtype.val '' ap : Set ℕ) ⊆ (↑(Finset.Icc 1 N) : Set ℕ) := by
    rintro x ⟨m, hm, rfl⟩
    exact m.property
  have hcard := Set.encard_le_encard hs
  change ENat.card (Subtype.val '' ap : Set ℕ) ≤
    ENat.card (↑(Finset.Icc 1 N) : Set ℕ) at hcard
  rw [hap.card] at hcard
  have hk : (k : ℕ∞) ≤ N := by
    simpa using hcard
  exact_mod_cast hk

theorem guarantee_requires_length {N k : ℕ} (hN : N ∈ monoAP_guarantee_set 2 k) :
    k ≤ N := length_le_interval (fun _ => 0) (hN (fun _ => 0))


-- The exact claim is equivalent to dominating every fixed exponential.
theorem exponential_threshold_iff {b : ℝ} (hb : 0 ≤ b) {k : ℕ} (hk : 0 < k) :
    b ≤ (W k : ℝ) ^ (1 / (k : ℝ)) ↔ b ^ k ≤ (W k : ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  simpa only [one_div, Real.rpow_natCast] using
    Real.le_rpow_inv_iff_of_pos hb (Nat.cast_nonneg (W k)) hkR

theorem claim_iff_all_exponentials : RootGrowth ↔
    ∀ b : ℝ, 1 < b → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → b ^ k ≤ (W k : ℝ) := by
  rw [RootGrowth, Filter.tendsto_atTop_atTop]
  constructor
  · intro h b hb
    obtain ⟨K, hK⟩ := h b
    refine ⟨max K 1, ?_⟩
    intro k hk
    have hk0 : 0 < k := lt_of_lt_of_le (by omega : 0 < 1)
      ((le_max_right K 1).trans hk)
    exact (exponential_threshold_iff (by linarith) hk0).mp
      (hK k ((le_max_left K 1).trans hk))
  · intro h b
    obtain ⟨K, hK⟩ := h (max b 2) (by have := le_max_right b 2; linarith)
    refine ⟨max K 1, ?_⟩
    intro k hk
    have hk0 : 0 < k := lt_of_lt_of_le (by omega : 0 < 1)
      ((le_max_right K 1).trans hk)
    apply (le_max_left b 2).trans
    exact (exponential_threshold_iff (by have := le_max_right b 2; linarith) hk0).mpr
      (hK k ((le_max_left K 1).trans hk))

theorem negation_iff_exponential_subsequence : (¬ RootGrowth) ↔
    ∃ b : ℝ, 1 < b ∧ ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ (W k : ℝ) < b ^ k := by
  rw [claim_iff_all_exponentials]
  push_neg
  rfl


theorem affine_isAP (k a d : ℕ) (hd : 0 < d) :
    (Set.range (fun t : Fin k => a + t.val * d)).IsAPOfLengthWith (k : ℕ∞) a d := by
  have hinj : Function.Injective (fun t : Fin k => a + t.val * d) := by
    intro i j h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
  constructor
  · change (Set.range (fun t : Fin k => a + t.val * d)).encard = _
    rw [← Set.image_univ, hinj.encard_image, Set.encard_univ]
    simp
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i.val, ?_, ?_⟩
      · exact_mod_cast i.isLt
      · simp
    · rintro ⟨n, hn, rfl⟩
      have hn' : n < k := by exact_mod_cast hn
      exact ⟨⟨n, hn'⟩, by simp⟩

-- Uniform finite bounds can be read directly from Hales-Jewett's finite dimension.
theorem guarantee_nonempty (k : ℕ) : (monoAP_guarantee_set 2 k).Nonempty := by
  classical
  obtain ⟨ι, instι, hι⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin k) (Fin 2)
  letI : Fintype ι := instι
  let N : ℕ := 1 + Fintype.card ι * k
  let f : (ι → Fin k) → Finset.Icc 1 N := fun v =>
    ⟨1 + ∑ i, (v i).val, by
      apply Finset.mem_Icc.mpr
      refine ⟨by omega, ?_⟩
      have hb : (∑ i, (v i).val) ≤ Fintype.card ι * k := by
        calc
          (∑ i, (v i).val) ≤ ∑ _i : ι, k :=
            Finset.sum_le_sum fun i _ => (v i).isLt.le
          _ = Fintype.card ι * k := by simp
      exact Nat.add_le_add_left hb 1⟩
  refine ⟨N, ?_⟩
  intro coloring
  obtain ⟨l, c, hc⟩ := hι (fun v => coloring (f v))
  let s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none)
  let d : ℕ := s.card
  let a : ℕ := 1 + ∑ i ∈ sᶜ, ((l.idxFun i).map Fin.val).getD 0
  have hd : 0 < d := by
    apply Finset.card_pos.mpr
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, by simp [s, hi]⟩
  have hf : ∀ t : Fin k, (f (l t)).val = a + t.val * d := by
    intro t
    change 1 + ∑ i, (l t i).val = _
    rw [← Finset.sum_add_sum_compl s]
    have hvar : (∑ i ∈ s, (l t i).val) = t.val * d := by
      calc
        (∑ i ∈ s, (l t i).val) = ∑ _i ∈ s, t.val := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : l.idxFun i = none := (Finset.mem_filter.mp hi).2
          rw [l.apply_none _ _ hi']
        _ = t.val * d := by simp [d, Nat.mul_comm]
    have hconst : (∑ i ∈ sᶜ, (l t i).val) =
        ∑ i ∈ sᶜ, ((l.idxFun i).map Fin.val).getD 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : l.idxFun i ≠ none := by simpa [s] using hi
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists.mp hi'
      simp [Combinatorics.Line.coe_apply, ← hj]
    rw [hvar, hconst]
    simp [a, Nat.add_comm, Nat.add_left_comm]
  refine ⟨c, Set.range (fun t : Fin k => f (l t)), ?_, ?_⟩
  · have himage : (Subtype.val '' Set.range (fun t : Fin k => f (l t)) : Set ℕ) =
        Set.range (fun t : Fin k => a + t.val * d) := by
      ext x
      constructor
      · rintro ⟨m, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, (hf t).symm⟩
      · rintro ⟨t, rfl⟩
        exact ⟨f (l t), ⟨t, rfl⟩, hf t⟩
    change (Subtype.val '' Set.range (fun t : Fin k => f (l t)) : Set ℕ).IsAPOfLength k
    rw [himage]
    exact ⟨a, d, affine_isAP k a d hd⟩
  · rintro m ⟨t, rfl⟩
    exact hc t

theorem W_guarantees (k : ℕ) : W k ∈ monoAP_guarantee_set 2 k :=
  Nat.sInf_mem (guarantee_nonempty k)

-- This proves that the infimum is an actual finite threshold, not a default 0.
theorem guarantee_upward_closed {k M N : ℕ} (hMN : M ≤ N)
    (hM : M ∈ monoAP_guarantee_set 2 k) : N ∈ monoAP_guarantee_set 2 k := by
  intro coloring
  let f : Finset.Icc 1 M → Finset.Icc 1 N := fun x =>
    ⟨x.val, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp x.property).1, (Finset.mem_Icc.mp x.property).2.trans hMN⟩⟩
  obtain ⟨c, ap, hap, hc⟩ := hM (fun x => coloring (f x))
  refine ⟨c, f '' ap, ?_, ?_⟩
  · have himage : ((fun x : Finset.Icc 1 N => x.val) '' (f '' ap) : Set ℕ) =
        ((fun x : Finset.Icc 1 M => x.val) '' ap : Set ℕ) := by
      rw [Set.image_image]
    change ((fun x : Finset.Icc 1 N => x.val) '' (f '' ap) : Set ℕ).IsAPOfLength k
    rw [himage]
    exact hap
  · rintro m ⟨x, hx, rfl⟩
    exact hc x hx

theorem guarantee_eq_Ici (k : ℕ) : monoAP_guarantee_set 2 k = Set.Ici (W k) :=
  Nat.eq_Ici_of_nonempty_of_upward_closed (guarantee_nonempty k)
    (fun _ _ hMN hM => guarantee_upward_closed hMN hM)

theorem length_le_W (k : ℕ) : k ≤ W k :=
  guarantee_requires_length (W_guarantees k)

theorem W_positive {k : ℕ} (hk : 0 < k) : 0 < W k :=
  hk.trans_le (length_le_W k)


-- A zero-step progression has at most one element, regardless of the intended length.
theorem zero_step_card {s : Set ℕ} {k a : ℕ}
    (h : s.IsAPOfLengthWith (k : ℕ∞) a 0) : k ≤ 1 := by
  have hs : s ⊆ {a} := by
    rw [h.eq]
    rintro x ⟨n, hn, rfl⟩
    simp
  have hc : (k : ℕ∞) ≤ 1 := by
    rw [← h.card]
    simpa using Set.encard_le_encard hs
  exact_mod_cast hc

theorem no_zero_step {s : Set ℕ} {k a : ℕ} (hk : 1 < k) :
    ¬ s.IsAPOfLengthWith (k : ℕ∞) a 0 := by
  intro h
  exact (not_le_of_gt hk) (zero_step_card h)


-- Exact standard-AP interpretation for every nontrivial length.
theorem contains_iff_standard {N k : ℕ} (hk : 1 < k)
    (coloring : Finset.Icc 1 N → Fin 2) :
    ContainsMonoAPofLength coloring k ↔
      ∃ a d : ℕ, 0 < d ∧ ∃ c : Fin 2,
        ∀ i : Fin k, ∃ m : Finset.Icc 1 N,
          m.val = a + i.val * d ∧ coloring m = c := by
  classical
  constructor
  · rintro ⟨c, ap, ⟨a, d, hap⟩, hc⟩
    have hd : 0 < d := by
      by_contra hd
      have hd0 : d = 0 := by omega
      subst d
      exact no_zero_step hk hap
    refine ⟨a, d, hd, c, ?_⟩
    intro i
    have hm : a + i.val * d ∈ ((fun m => m.val) '' ap : Set ℕ) := by
      rw [hap.eq]
      refine ⟨i.val, ?_, ?_⟩
      · exact_mod_cast i.isLt
      · simp
    obtain ⟨m, hm, hval⟩ := hm
    exact ⟨m, hval, hc m hm⟩
  · rintro ⟨a, d, hd, c, hc⟩
    let g : Fin k → Finset.Icc 1 N := fun i => (hc i).choose
    have hg : ∀ i : Fin k, (g i).val = a + i.val * d ∧ coloring (g i) = c :=
      fun i => (hc i).choose_spec
    refine ⟨c, Set.range g, ?_, ?_⟩
    · have himage : (Subtype.val '' Set.range g : Set ℕ) =
          Set.range (fun i : Fin k => a + i.val * d) := by
        ext x
        constructor
        · rintro ⟨m, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, (hg i).1.symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨g i, ⟨i, rfl⟩, (hg i).1⟩
      change (Subtype.val '' Set.range g : Set ℕ).IsAPOfLength k
      rw [himage]
      exact ⟨a, d, affine_isAP k a d hd⟩
    · rintro m ⟨i, rfl⟩
      exact (hg i).2


/-- Taking an initial segment of a monochromatic progression preserves its color. -/
theorem contains_length_mono {N k l : ℕ} (hkl : k ≤ l)
    (coloring : Finset.Icc 1 N → Fin 2)
    (h : ContainsMonoAPofLength coloring l) : ContainsMonoAPofLength coloring k := by
  by_cases hk0 : k = 0
  · subst k
    exact contains_zero coloring
  by_cases hl1 : l = 1
  · have hk1 : k = 1 := by omega
    simpa [hk1, hl1] using h
  have hl : 1 < l := by omega
  obtain ⟨a, d, hd, c, hc⟩ := (contains_iff_standard hl coloring).mp h
  by_cases hk1 : k = 1
  · subst k
    obtain ⟨m, hm, hmc⟩ := hc ⟨0, by omega⟩
    refine ⟨c, {m}, ?_, ?_⟩
    · simp
    · simpa using hmc
  have hk : 1 < k := by omega
  apply (contains_iff_standard hk coloring).mpr
  refine ⟨a, d, hd, c, ?_⟩
  intro i
  exact hc (Fin.castLE hkl i)

/-- The van der Waerden threshold is monotone in the required progression length. -/
theorem W_monotone : Monotone W := by
  intro k l hkl
  apply Nat.sInf_le
  intro coloring
  exact contains_length_mono hkl coloring (W_guarantees l coloring)

theorem negation_iff : (¬ RootGrowth) ↔
    ∃ b : ℝ, ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ (W k : ℝ) ^ (1 / (k : ℝ)) < b := by
  rw [RootGrowth, Filter.tendsto_atTop_atTop]
  push_neg
  rfl

-- A concrete sufficient route for a proof: long intervals with avoiding 2-colorings.
theorem claim_of_avoiding_colorings
    (h : ∀ b : ℕ, 2 ≤ b → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ coloring : Finset.Icc 1 (b ^ k) → Fin 2, ¬ ContainsMonoAPofLength coloring k) :
    RootGrowth := by
  apply claim_iff_all_exponentials.mpr
  intro B hB
  obtain ⟨b, hb⟩ := exists_nat_gt (max B 2)
  have hbb : B ≤ (b : ℝ) := ((le_max_left B 2).trans hb.le)
  have hb2 : 2 ≤ b := by
    have hb2R : (2 : ℝ) ≤ b := (le_max_right B 2).trans hb.le
    exact_mod_cast hb2R
  obtain ⟨K, hK⟩ := h b hb2
  refine ⟨K, ?_⟩
  intro k hk
  obtain ⟨coloring, hc⟩ := hK k hk
  have hnot : b ^ k ∉ monoAP_guarantee_set 2 k := fun hg => hc (hg coloring)
  rw [guarantee_eq_Ici] at hnot
  have hlt : b ^ k < W k := lt_of_not_ge hnot
  have hp : B ^ k ≤ (b : ℝ) ^ k := by gcongr
  apply hp.trans
  exact_mod_cast hlt.le

/-- Uniform superexponential lower bounds at prime lengths suffice for all lengths. -/
theorem claim_of_prime_lower_bounds
    (h : ∀ b : ℕ, 2 ≤ b → ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime →
      (b * b) ^ p < W p) : RootGrowth := by
  apply claim_iff_all_exponentials.mpr
  intro B hB
  obtain ⟨b, hb⟩ := exists_nat_gt (max B 2)
  have hBb : B ≤ (b : ℝ) := (le_max_left B 2).trans hb.le
  have hb2 : 2 ≤ b := by
    have hb2R : (2 : ℝ) ≤ b := (le_max_right B 2).trans hb.le
    exact_mod_cast hb2R
  obtain ⟨P, hP⟩ := h b hb2
  refine ⟨2 * max P 1, ?_⟩
  intro k hk
  have hn : k / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hlp, hpu⟩ := Nat.bertrand (k / 2) hn
  have hPp : P ≤ p := by omega
  have hpk : p ≤ k := by omega
  have hkp : k ≤ 2 * p := by omega
  have hpW := hP p hPp hp
  have hpow : b ^ k ≤ (b * b) ^ p := by
    calc
      b ^ k ≤ b ^ (2 * p) := Nat.pow_le_pow_right (by omega) hkp
      _ = (b * b) ^ p := by rw [Nat.pow_mul, pow_two]
  have hbound : b ^ k ≤ W k := hpow.trans (hpW.le.trans (W_monotone hpk))
  have hBpow : B ^ k ≤ (b : ℝ) ^ k := by gcongr
  apply hBpow.trans
  exact_mod_cast hbound

/-- Prime-length avoiding colorings with arbitrarily large fixed bases suffice. -/
theorem claim_of_prime_avoiding_colorings
    (h : ∀ b : ℕ, 2 ≤ b → ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime →
      ∃ coloring : Finset.Icc 1 ((b * b) ^ p) → Fin 2,
        ¬ ContainsMonoAPofLength coloring p) : RootGrowth := by
  apply claim_of_prime_lower_bounds
  intro b hb
  obtain ⟨P, hP⟩ := h b hb
  refine ⟨P, ?_⟩
  intro p hPp hp
  obtain ⟨coloring, hc⟩ := hP p hPp hp
  have hnot : (b * b) ^ p ∉ monoAP_guarantee_set 2 p := fun hg => hc (hg coloring)
  rw [guarantee_eq_Ici] at hnot
  exact lt_of_not_ge hnot

-- A concrete sufficient route for a disproof: cofinally many exponential-size guarantees.
theorem disproof_of_exponential_guarantees
    (h : ∃ b : ℕ, 2 ≤ b ∧ ∀ K : ℕ, ∃ k : ℕ,
      K ≤ k ∧ b ^ k ∈ monoAP_guarantee_set 2 k) : ¬ RootGrowth := by
  obtain ⟨b, hb, hK⟩ := h
  apply negation_iff.mpr
  refine ⟨(b : ℝ) + 1, ?_⟩
  intro K
  obtain ⟨k, hk, hG⟩ := hK (max K 1)
  have hk0 : 0 < k := lt_of_lt_of_le (by omega : 0 < 1)
    ((le_max_right K 1).trans hk)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk0
  have hW : (W k : ℝ) ≤ (b : ℝ) ^ k := by
    exact_mod_cast (Nat.sInf_le hG)
  have hr : (W k : ℝ) ^ (1 / (k : ℝ)) ≤ (b : ℝ) := by
    have hiff : ((W k : ℝ) ^ (1 / (k : ℝ)) ≤ (b : ℝ)) ↔
        (W k : ℝ) ≤ (b : ℝ) ^ k := by
      simpa only [one_div, Real.rpow_natCast] using
        Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg (W k)) (Nat.cast_nonneg b) hkR
    exact hiff.mpr hW
  exact ⟨k, (le_max_left K 1).trans hk, hr.trans_lt (by linarith)⟩


/--
In [Er80] Erdős asks whether
$$ \lim_{k \to \infty} (W(k))^{1/k} = \infty $$
-/
theorem erdos_138 : atTop.Tendsto (fun k => (W k : ℝ)^(1/(k : ℝ))) atTop := by
  sorry

end Erdos138

theorem Erdos138.erdos_138.disproof : ¬ (type_of% @Erdos138.erdos_138) := sorry
