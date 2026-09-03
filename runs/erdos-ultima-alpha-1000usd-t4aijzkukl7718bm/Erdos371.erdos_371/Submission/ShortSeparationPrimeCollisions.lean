import Submission.DyadicHarmonicSignedCollisions

/-! Unconditional control of the unsigned critical harmonic collision mass
at sublinear index separations. Macroscopic separations are not estimated. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma primeLoser_dvd_endpoint (n : ℕ) :
    primeLoser n ∣ n ∨ primeLoser n ∣ n+1 := by
  rcases min_cases (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) with h|h
  · left
    simpa only [primeLoser,h.1] using (Nat.maxPrimeFac_dvd (n := n))
  · right
    simpa only [primeLoser,h.1] using (Nat.maxPrimeFac_dvd (n := n+1))

lemma common_endpoint_divisor_offset (p n d : ℕ)
    (hn : p ∣ n ∨ p ∣ n+1) (hm : p ∣ n+d ∨ p ∣ n+d+1) :
    p ∣ d-1 ∨ p ∣ d ∨ p ∣ d+1 := by
  rcases hn with hn|hn <;> rcases hm with hm|hm
  · right; left
    convert Nat.dvd_sub hm hn using 1; omega
  · right; right
    convert Nat.dvd_sub hm hn using 1; omega
  · left
    convert Nat.dvd_sub hm hn using 1; omega
  · right; left
    convert Nat.dvd_sub hm hn using 1; omega

lemma positive_divisor_image_card_bound (S : Finset ℕ) (f : ℕ → ℕ) (D p : ℕ)
    (hf : ∀ d∈S, 0<f d ∧ f d≤D+1) (hinj : Set.InjOn f S) :
    (S.filter (fun d => p ∣ f d)).card≤(D+1)/p := by
  let T := (range (D+2)).filter fun v => v≠0 ∧ p ∣ v
  have h := card_le_card_of_injOn f
    (s := S.filter (fun d => p ∣ f d)) (t := T) (by
      intro d hd
      obtain ⟨hd,hpd⟩ := mem_filter.mp hd
      have hb := hf d hd
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,hpd⟩)
    (fun d hd e he hde => hinj (mem_filter.mp hd).1 (mem_filter.mp he).1 hde)
  simpa only [T,show D+2=(D+1)+1 by omega,Nat.card_multiples'] using h

lemma neighboring_divisor_offsets_card_bound (p D : ℕ) :
    ((Icc 2 D).filter (fun d => p ∣ d-1 ∨ p ∣ d ∨ p ∣ d+1)).card ≤
      3*((D+1)/p) := by
  let S := Icc 2 D
  let A := S.filter (fun d => p ∣ d-1)
  let B := S.filter (fun d => p ∣ d)
  let C := S.filter (fun d => p ∣ d+1)
  have hA : A.card≤(D+1)/p := positive_divisor_image_card_bound S (fun d => d-1) D p
    (by intro d hd; have := mem_Icc.mp hd; dsimp; omega)
    (by intro d hd e he hde; have := mem_Icc.mp (show d∈Icc 2 D from hd); have := mem_Icc.mp (show e∈Icc 2 D from he); dsimp at hde; omega)
  have hB : B.card≤(D+1)/p := positive_divisor_image_card_bound S id D p
    (by intro d hd; have := mem_Icc.mp hd; dsimp; omega)
    (by intro d hd e he hde; exact hde)
  have hC : C.card≤(D+1)/p := positive_divisor_image_card_bound S (fun d => d+1) D p
    (by intro d hd; have := mem_Icc.mp hd; dsimp; omega)
    (by intro d hd e he hde; dsimp at hde; omega)
  have hs : (Icc 2 D).filter (fun d => p ∣ d-1 ∨ p ∣ d ∨ p ∣ d+1) = A ∪ B ∪ C := by
    ext d
    simp only [A,B,C,S,mem_filter,mem_union]
    tauto
  rw [hs]
  have h1 := card_union_le A B
  have h2 := card_union_le (A ∪ B) C
  omega

noncomputable def nearLoserOffsets (D U n : ℕ) : Finset ℕ :=
  (Icc 2 D).filter fun d => n+d<U ∧ primeLoser (n+d)=primeLoser n

/-- No estimate for the signs is used. The common label must divide
one of the three positive integers d-1,d,d+1. -/
lemma nearLoserOffsets_label_card_bound (D U n : ℕ) :
    primeLoser n*(nearLoserOffsets D U n).card≤3*(D+1) := by
  have hs : nearLoserOffsets D U n ⊆
      (Icc 2 D).filter (fun d => primeLoser n ∣ d-1 ∨ primeLoser n ∣ d ∨ primeLoser n ∣ d+1) := by
    intro d hd
    obtain ⟨hd,_,he⟩ := mem_filter.mp hd
    apply mem_filter.mpr ⟨hd,?_⟩
    apply common_endpoint_divisor_offset (primeLoser n) n d (primeLoser_dvd_endpoint n)
    simpa only [← he] using primeLoser_dvd_endpoint (n+d)
  have hh := (card_le_card hs).trans (neighboring_divisor_offsets_card_bound (primeLoser n) D)
  have hm := Nat.mul_le_mul_left (primeLoser n) hh
  have hd := Nat.mul_div_le (D+1) (primeLoser n)
  nlinarith

lemma critical_pair_weight_le_diagonal (p n d : ℕ) (hn : 0<n) :
    (p : ℝ)/((n : ℝ)*(n+d : ℕ))≤(p : ℝ)/(n : ℝ)^2 := by
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg p)
    (sq_pos_of_pos (by exact_mod_cast hn))
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) d,Nat.cast_nonneg (α := ℝ) n]

lemma nearLoserOffsets_harmonic_mass_bound (D U n : ℕ) (hn : 0<n) :
    (∑ d ∈ nearLoserOffsets D U n,
      (primeLoser n : ℝ)/((n : ℝ)*(n+d : ℕ))) ≤ 3*(D+1 : ℝ)/(n : ℝ)^2 := by
  calc
    _ ≤ ∑ _d ∈ nearLoserOffsets D U n, (primeLoser n : ℝ)/(n : ℝ)^2 :=
      sum_le_sum (fun d _ => critical_pair_weight_le_diagonal (primeLoser n) n d hn)
    _ = ((primeLoser n : ℝ)*(nearLoserOffsets D U n).card)/(n : ℝ)^2 := by
      simp only [sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast nearLoserOffsets_label_card_bound D U n

noncomputable def dyadicForwardNearLoserMass (D N : ℕ) : ℝ :=
  ∑ n ∈ Ico N (2*N), ∑ d ∈ nearLoserOffsets D (2*N) n,
    (primeLoser n : ℝ)/((n : ℝ)*(n+d : ℕ))

lemma dyadicForwardNearLoserMass_nonneg (D N : ℕ) :
    0≤dyadicForwardNearLoserMass D N := by
  unfold dyadicForwardNearLoserMass
  positivity

/-- All nonadjacent forward collisions with separation at most D have
unsigned critical harmonic mass at most 3(D+1)/N. -/
theorem dyadicForwardNearLoserMass_bound (D N : ℕ) (hN : 0<N) :
    dyadicForwardNearLoserMass D N≤3*(D+1 : ℝ)/N := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hcard : (Ico N (2*N)).card=N := by rw [Nat.card_Ico]; omega
  calc
    _ ≤ ∑ n ∈ Ico N (2*N), 3*(D+1 : ℝ)/(n : ℝ)^2 := by
      apply sum_le_sum
      intro n hn
      exact nearLoserOffsets_harmonic_mass_bound D (2*N) n
        (hN.trans_le (mem_Ico.mp hn).1)
    _ ≤ ∑ _n ∈ Ico N (2*N), 3*(D+1 : ℝ)/(N : ℝ)^2 := by
      apply sum_le_sum
      intro n hn
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hNr)
      exact pow_le_pow_left₀ hNr.le (by exact_mod_cast (mem_Ico.mp hn).1) 2
    _ = 3*(D+1 : ℝ)/N := by
      rw [sum_const,hcard,nsmul_eq_mul]
      field_simp

/-- Every sublinear separation scale is negligible without cancellation
of signs. This does not cover separations comparable to N. -/
theorem dyadicForwardNearLoserMass_zero (D : ℕ → ℕ)
    (hD : Tendsto (fun N => (D N : ℝ)/N) atTop (𝓝 0)) :
    Tendsto (fun N => dyadicForwardNearLoserMass (D N) N) atTop (𝓝 0) := by
  have ht := (hD.add tendsto_one_div_atTop_nhds_zero_nat).const_mul 3
  simp only [add_zero,mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun N => dyadicForwardNearLoserMass_nonneg _ _)) _ ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  simpa only [add_div,mul_add,mul_div_assoc] using dyadicForwardNearLoserMass_bound (D N) N hN

noncomputable def dyadicAdjacentLoserMass (N : ℕ) : ℝ :=
  ∑ n ∈ (Ico N (2*N)).filter (fun n => n+1<2*N ∧ primeLoser (n+1)=primeLoser n),
    (primeLoser n : ℝ)/((n : ℝ)*(n+1 : ℕ))

lemma dyadicAdjacentLoserMass_bound (N : ℕ) (hN : 0<N) :
    dyadicAdjacentLoserMass N≤dyadicLoserWindowDiagonal N := by
  calc
    _ ≤ ∑ n ∈ (Ico N (2*N)).filter
        (fun n => n+1<2*N ∧ primeLoser (n+1)=primeLoser n), primeLoserHarmonicDiagonal n := by
      apply sum_le_sum
      intro n hn
      exact critical_pair_weight_le_diagonal (primeLoser n) n 1
        (hN.trans_le (mem_Ico.mp (mem_filter.mp hn).1).1)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun n _ _ => primeLoserHarmonicDiagonal_nonneg n)

theorem dyadicAdjacentLoserMass_zero :
    Tendsto dyadicAdjacentLoserMass atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun N => by unfold dyadicAdjacentLoserMass; positivity)) _
    dyadicLoserWindowDiagonal_zero
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact dyadicAdjacentLoserMass_bound N hN

#print axioms neighboring_divisor_offsets_card_bound
#print axioms dyadicForwardNearLoserMass_bound
#print axioms dyadicForwardNearLoserMass_zero
#print axioms dyadicAdjacentLoserMass_zero
end Erdos371
