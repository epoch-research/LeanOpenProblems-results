import Submission.CollisionBounds
import Submission.ElementarySquareSieve

/-!
Lower bounds on the density of quadratic residues for arbitrary moduli.
These are auxiliary estimates; no square-Sidon construction is asserted.
-/
namespace Erdos773.ResidueDensityLower
open Finset Filter
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

private def congruentPairs (q : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 q) ×ˢ (Icc 1 q)).filter
    (fun p => p.1 ^ 2 % q = p.2 ^ 2 % q)

private def increasingPairs (q : ℕ) : Finset (ℕ × ℕ) :=
  (congruentPairs q).filter (fun p => p.1 < p.2)

private lemma ordered_pair_count (q : ℕ) :
    (congruentPairs q).card ≤ q + 2 * (increasingPairs q).card := by
  let f : ℕ × ℕ → ℕ ⊕ ((ℕ × ℕ) ⊕ (ℕ × ℕ)) := fun p =>
    if p.1 = p.2 then Sum.inl p.1 else
      if p.1 < p.2 then Sum.inr (Sum.inl p) else Sum.inr (Sum.inr p.swap)
  have hc : (congruentPairs q).card ≤
      ((Icc 1 q).disjSum ((increasingPairs q).disjSum (increasingPairs q))).card := by
    apply Finset.card_le_card_of_injOn f
    · rintro ⟨a,b⟩ hp
      obtain ⟨hp, he⟩ := mem_filter.mp hp
      obtain ⟨ha, hb⟩ := mem_product.mp hp
      dsimp [f]
      split_ifs with hab hlt
      · exact mem_disjSum.mpr (Or.inl ⟨a, ha, rfl⟩)
      · apply mem_disjSum.mpr
        right
        refine ⟨Sum.inl (a,b), ?_, rfl⟩
        apply mem_disjSum.mpr
        left
        exact ⟨(a,b), mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩, he⟩, hlt⟩, rfl⟩
      · apply mem_disjSum.mpr
        right
        refine ⟨Sum.inr (b,a), ?_, rfl⟩
        apply mem_disjSum.mpr
        right
        exact ⟨(b,a), mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hb,ha⟩, he.symm⟩,
          by omega⟩, rfl⟩
    · rintro ⟨a,b⟩ hp ⟨c,d⟩ hr he
      dsimp [f] at he
      split_ifs at he with hab hcd hlt hlt' hcd hlt' hlt' <;>
        simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
          Sum.inr_ne_inl, Prod.mk.injEq]
  simpa only [card_disjSum, Nat.card_Icc, Nat.add_sub_cancel, two_mul, add_assoc] using hc

private lemma increasingPairs_cover (q : ℕ) (hq : 0 < q) :
    increasingPairs q ⊆ (Icc 1 q).biUnion (fun k => squareDifferenceReps q (q * k)) := by
  intro p hp
  obtain ⟨hp, hlt⟩ := mem_filter.mp hp
  obtain ⟨hp, hmod⟩ := mem_filter.mp hp
  obtain ⟨ha, hb⟩ := mem_product.mp hp
  have hs : p.1 ^ 2 < p.2 ^ 2 := by nlinarith
  have hdiv : q ∣ p.2 ^ 2 - p.1 ^ 2 :=
    (Nat.modEq_iff_dvd' hs.le).mp hmod
  obtain ⟨k, hk⟩ := hdiv
  have hkpos : 0 < k := by
    have hd := Nat.sub_pos_of_lt hs
    rw [hk] at hd
    by_contra hh
    have hk0 : k = 0 := by omega
    simp [hk0] at hd
  have hkq : k ≤ q := by
    have hbq := (mem_Icc.mp hb).2
    have hb2 := Nat.pow_le_pow_left hbq 2
    have hh : q * k ≤ q * q := by nlinarith [Nat.sub_le (p.2 ^ 2) (p.1 ^ 2)]
    exact Nat.le_of_mul_le_mul_left hh hq
  apply mem_biUnion.mpr
  refine ⟨k, mem_Icc.mpr ⟨hkpos, hkq⟩, ?_⟩
  exact mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩, hlt, by omega⟩

private lemma congruentPairs_subpower (η : ℝ) (hη : 0 < η) :
    ∃ C > (0 : ℝ), ∀ q : ℕ, 0 < q →
      ((congruentPairs q).card : ℝ) ≤ C * q ^ (1 + η) := by
  obtain ⟨C, hC, hc⟩ := squareDifferenceReps_subpower (η / 2) (by linarith)
  refine ⟨1 + 2 * C, by positivity, fun q hq => ?_⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ η := Real.one_le_rpow hq1 hη.le
  have hi : ((increasingPairs q).card : ℝ) ≤ (q : ℝ) * (C * q ^ η) := by
    have hb := (card_le_card (increasingPairs_cover q hq)).trans
      (card_biUnion_le (s := Icc 1 q) (t := fun k => squareDifferenceReps q (q * k)))
    calc
      _ ≤ ∑ k ∈ Icc 1 q, ((squareDifferenceReps q (q * k)).card : ℝ) := by exact_mod_cast hb
      _ ≤ ∑ _k ∈ Icc 1 q, C * (q : ℝ) ^ η := by
        apply sum_le_sum
        intro k hk
        obtain ⟨hk1, hkq⟩ := mem_Icc.mp hk
        have hd : 0 < q * k := by positivity
        have hle : q * k ≤ q ^ 2 := by nlinarith
        simpa only [show 2 * (η / 2) = η by ring] using hc q (q * k) hd hle
      _ = _ := by simp
  have ho : ((congruentPairs q).card : ℝ) ≤ q + 2 * (increasingPairs q).card := by
    exact_mod_cast ordered_pair_count q
  rw [Real.rpow_add hqR, Real.rpow_one]
  nlinarith [mul_le_mul_of_nonneg_left hpow hqR.le]

private lemma cardinality_cauchy (q : ℕ) [NeZero q] :
    q ^ 2 ≤ (quadraticResidues q).card * (congruentPairs q).card := by
  let C := (quadraticResidues q).image ZMod.val
  have hC (a : ℕ) (ha : a ∈ Icc 1 q) : a ^ 2 % q ∈ C := by
    refine mem_image.mpr ⟨(a : ZMod q) ^ 2,
      (mem_quadraticResidues _).mpr ⟨a, rfl⟩, ?_⟩
    rw [← Nat.cast_pow, ZMod.val_natCast]
  have hsum : q = ∑ r ∈ C, ((Icc 1 q).filter (fun a => a ^ 2 % q = r)).card := by
    have hm : Set.MapsTo (fun a : ℕ => a ^ 2 % q) (Icc 1 q) C := hC
    simpa using card_eq_sum_card_fiberwise hm
  have hsum2 : (congruentPairs q).card =
      ∑ r ∈ C, ((Icc 1 q).filter (fun a => a ^ 2 % q = r)).card ^ 2 := by
    have hm : Set.MapsTo (fun p : ℕ × ℕ => p.1 ^ 2 % q) (congruentPairs q) C := by
      intro p hp
      exact hC _ (mem_product.mp (mem_filter.mp hp).1).1
    rw [card_eq_sum_card_fiberwise hm]
    apply sum_congr rfl
    intro r hr
    have he : (congruentPairs q).filter (fun p => p.1 ^ 2 % q = r) =
        ((Icc 1 q).filter (fun a => a ^ 2 % q = r)) ×ˢ
        ((Icc 1 q).filter (fun a => a ^ 2 % q = r)) := by
      ext p
      simp only [congruentPairs, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, he⟩, hr⟩
        exact ⟨⟨ha, hr⟩, ⟨hb, he.symm.trans hr⟩⟩
      · rintro ⟨⟨ha, hra⟩, ⟨hb, hrb⟩⟩
        exact ⟨⟨⟨ha, hb⟩, hra.trans hrb.symm⟩, hra⟩
    rw [he, card_product, pow_two]
  have hcard : C.card = (quadraticResidues q).card :=
    card_image_iff.mpr (fun _ _ _ _ he => ZMod.val_injective q he)
  rw [← hcard, hsum2]
  conv_lhs => rw [hsum]
  exact sq_sum_le_card_mul_sum_sq

/-- The quadratic-residue density is bounded below by a subpower, uniformly
    over all positive moduli. -/
lemma density_subpower_global (η : ℝ) (hη : 0 < η) :
    ∃ C > (0 : ℝ), ∀ q : ℕ, 0 < q →
      1 ≤ C * quadraticResidueDensity q * (q : ℝ) ^ η := by
  obtain ⟨C, hC, hc⟩ := congruentPairs_subpower η hη
  refine ⟨C, hC, fun q hq => ?_⟩
  letI : NeZero q := ⟨hq.ne'⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo : (q : ℝ) ^ 2 ≤ (quadraticResidues q).card * (congruentPairs q).card := by
    exact_mod_cast cardinality_cauchy q
  have hhi := mul_le_mul_of_nonneg_left (hc q hq)
    (show (0 : ℝ) ≤ (quadraticResidues q).card by positivity)
  have hh := hlo.trans hhi
  rw [Real.rpow_add hqR, Real.rpow_one] at hh
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hqR)).mp
  rw [quadraticResidueDensity_eq]
  convert hh using 1 <;> field_simp

/-- On polynomially bounded moduli, the lower bound is uniform in the ambient
    scale, with no multiplicative constant. -/
lemma density_uniform_polynomial (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, 0 < q → (q : ℝ) ≤ (N : ℝ) ^ K →
      (N : ℝ) ^ (-ε) ≤ quadraticResidueDensity q := by
  obtain ⟨C, hC, hc⟩ := density_subpower_global (ε / (2 * K)) (by positivity)
  have hbound : ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ (ε / 2) :=
    tendsto_atTop.mp ((tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp
      tendsto_natCast_atTop_atTop) C
  filter_upwards [hbound, eventually_ge_atTop 1] with N hCN hN q hq hqN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqpow : (q : ℝ) ^ (ε / (2 * K)) ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ ≤ ((N : ℝ) ^ K) ^ (ε / (2 * K)) :=
        Real.rpow_le_rpow (by positivity) hqN (by positivity)
      _ = _ := by rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
  have hprod : C * (q : ℝ) ^ (ε / (2 * K)) ≤ (N : ℝ) ^ ε := by
    calc
      _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
        mul_le_mul hCN hqpow (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hh : 1 ≤ quadraticResidueDensity q * (N : ℝ) ^ ε := by
    calc
      _ ≤ quadraticResidueDensity q * (C * (q : ℝ) ^ (ε / (2 * K))) := by
        simpa only [mul_left_comm, mul_comm, mul_assoc] using hc q hq
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (quadraticResidueDensity_nonneg q)
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hN0 ε)).mp
  simpa only [← Real.rpow_add hN0, neg_add_cancel, add_neg_cancel, Real.rpow_zero, mul_comm] using hh

/-- If the modulus exceeds every square in the interval, those squares already
    give distinct quadratic residues. -/
lemma card_residues_large_modulus (N q : ℕ) [NeZero q] (h : N ^ 2 < q) :
    N ≤ (quadraticResidues q).card := by
  have hm : Set.MapsTo (fun n : ℕ => (n : ZMod q) ^ 2) (Icc 1 N)
      (quadraticResidues q) := fun n hn => (mem_quadraticResidues _).mpr ⟨n, rfl⟩
  have hi : Set.InjOn (fun n : ℕ => (n : ZMod q) ^ 2) (Icc 1 N) := by
    intro a ha b hb he
    have ha' : a ^ 2 < q := (Nat.pow_le_pow_left (mem_Icc.mp ha).2 2).trans_lt h
    have hb' : b ^ 2 < q := (Nat.pow_le_pow_left (mem_Icc.mp hb).2 2).trans_lt h
    have hv := congrArg ZMod.val he
    simp only [← Nat.cast_pow, ZMod.val_natCast, Nat.mod_eq_of_lt ha',
      Nat.mod_eq_of_lt hb'] at hv
    nlinarith
  simpa using Finset.card_le_card_of_injOn _ hm hi

/-- The entire family of the basic modular cardinality inequalities is consistent
    with a hypothetical near-linear cardinality. This is NOT a Sidon construction
    or a lower bound on the actual maximum. -/
lemma modular_inequalities_compatible (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, ∀ hq : 0 < q,
      letI : NeZero q := ⟨hq.ne'⟩
      let x := (N : ℝ) ^ (1 - ε)
      x ^ 2 ≤ (quadraticResidues q).card * (x + 2 * (N ^ 2 / q : ℕ) + 1) := by
  filter_upwards [density_uniform_polynomial 2 ε (by norm_num) hε,
    eventually_ge_atTop 1] with N hden hN q hq
  letI : NeZero q := ⟨hq.ne'⟩
  dsimp only
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 ≤ (N : ℝ) ^ (1 - ε) := Real.rpow_nonneg hN0.le _
  have hxN : (N : ℝ) ^ (1 - ε) ≤ N := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - ε ≤ 1 by linarith)
  by_cases hsmall : q ≤ N ^ 2
  · have hden' := hden q hq (by exact_mod_cast hsmall)
    have hquot : N ^ 2 ≤ 2 * q * (N ^ 2 / q) := by
      have hdiv := Nat.div_add_mod (N ^ 2) q
      have hrem := Nat.mod_lt (N ^ 2) hq
      have hone : 1 ≤ N ^ 2 / q := (Nat.le_div_iff_mul_le hq).mpr (by simpa)
      nlinarith
    have hquotR : (N : ℝ) ^ 2 ≤ 2 * q * (N ^ 2 / q : ℕ) := by exact_mod_cast hquot
    calc
      ((N : ℝ) ^ (1 - ε)) ^ 2 = (N : ℝ) ^ (2 - 2 * ε) := by
        rw [← Real.rpow_mul_natCast hN0.le]; congr 1; norm_num; ring
      _ ≤ (N : ℝ) ^ (2 - ε) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = (N : ℝ) ^ (-ε) * (N : ℝ) ^ 2 := by
        rw [← Real.rpow_two, ← Real.rpow_add hN0]; congr 1; ring
      _ ≤ quadraticResidueDensity q * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hden' (sq_nonneg _)
      _ ≤ quadraticResidueDensity q * (2 * q * (N ^ 2 / q : ℕ)) :=
        mul_le_mul_of_nonneg_left hquotR (quadraticResidueDensity_nonneg q)
      _ = (quadraticResidues q).card * (2 * (N ^ 2 / q : ℕ)) := by
        rw [quadraticResidueDensity_eq]; field_simp
      _ ≤ _ := by gcongr; linarith
  · have hcard : (N : ℝ) ≤ (quadraticResidues q).card := by
      exact_mod_cast card_residues_large_modulus N q (by omega)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (quadraticResidues q).card by positivity)
      (show (0 : ℝ) ≤ (N ^ 2 / q : ℕ) by positivity)]

#print axioms density_subpower_global
#print axioms density_uniform_polynomial
#print axioms modular_inequalities_compatible
end Erdos773.ResidueDensityLower
