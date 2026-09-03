import Submission.FiniteSelbergBound
import Submission.PrimeBoxCRT

/-!
A level-truncated Selberg bound for two-parameter residue conditions. The
main term is expressed in terms of the sieve mass; no asymptotic lower bound
on that mass is assumed or proved here.
-/
namespace Erdos1206.PrimeBoxSelberg
open Finset FiniteThinnedSieve FiniteSelbergWeights FiniteSelbergBound PrimeBoxCRT
open scoped Classical

noncomputable def level (P : Finset ℕ) (z : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun S => (∏ p ∈ S, p) ≤ z)

lemma level_subset (P : Finset ℕ) (z : ℕ) {S : Finset ℕ} (hS : S ∈ level P z) : S ⊆ P :=
  mem_powerset.mp (mem_filter.mp hS).1

lemma level_height (P : Finset ℕ) (z : ℕ) {S : Finset ℕ} (hS : S ∈ level P z) :
    (∏ p ∈ S, p) ≤ z := (mem_filter.mp hS).2

lemma level_downward (P : Finset ℕ) (z : ℕ) (hP : ∀ p ∈ P, p.Prime)
    {S : Finset ℕ} (hS : S ∈ level P z) (T : Finset ℕ) (hT : T ⊆ S) : T ∈ level P z := by
  have hSP := level_subset P z hS
  have hpos := prime_product_pos S (fun p hp => hP p (hSP hp))
  apply mem_filter.mpr
  exact ⟨mem_powerset.mpr (hT.trans hSP),
    (Nat.le_of_dvd hpos (prod_dvd_prod_of_subset T S id hT)).trans (level_height P z hS)⟩

lemma empty_mem_level (P : Finset ℕ) {z : ℕ} (hz : 1 ≤ z) : ∅ ∈ level P z := by
  simp only [level,mem_filter,mem_powerset,empty_subset,prod_empty,true_and]
  exact hz

lemma level_card_le (P : Finset ℕ) (z : ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (level P z).card ≤ z := by
  have hh : (level P z).card ≤ (Icc 1 z).card := by
    apply card_le_card_of_injOn (fun S => ∏ p ∈ S, p)
    · intro S hS
      change (∏ p ∈ S, p) ∈ Icc 1 z
      apply mem_Icc.mpr
      exact ⟨prime_product_pos S (fun p hp => hP p (level_subset P z hS hp)),level_height P z hS⟩
    · intro S hS T hT he
      have hs := Nat.primeFactors_prod (fun p hp => hP p (level_subset P z hS hp))
      have ht := Nat.primeFactors_prod (fun p hp => hP p (level_subset P z hT hp))
      dsimp only at he
      rw [he] at hs
      exact hs.symm.trans ht
  simpa using hh

lemma union_height (P : Finset ℕ) (z : ℕ) (hP : ∀ p ∈ P, p.Prime)
    {S T : Finset ℕ} (hS : S ∈ level P z) (hT : T ∈ level P z) :
    (∏ p ∈ S ∪ T, p) ≤ z^2 := by
  have hi : 0 < ∏ p ∈ S ∩ T, p := prime_product_pos _
    (fun p hp => hP p (level_subset P z hS ((mem_inter.mp hp).1)))
  have hh : (∏ p ∈ S ∪ T, p)*(∏ p ∈ S ∩ T, p) = (∏ p ∈ S, p)*(∏ p ∈ T, p) := prod_union_inter
  calc
    _ ≤ (∏ p ∈ S ∪ T, p)*(∏ p ∈ S ∩ T, p) := Nat.le_mul_of_pos_right _ hi
    _ = _ := hh
    _ ≤ z*z := Nat.mul_le_mul (level_height P z hS) (level_height P z hT)
    _ = _ := (pow_two z).symm

noncomputable def hits (P : Finset ℕ) (B : (p : ℕ) → Finset (ZMod p × ZMod p))
    (x : ℕ × ℕ) : Finset ℕ := P.filter (fun p => ((x.1:ZMod p),(x.2:ZMod p)) ∈ B p)

lemma hits_subset (P : Finset ℕ) (B : (p : ℕ) → Finset (ZMod p × ZMod p)) (x : ℕ × ℕ) :
    hits P B x ⊆ P := filter_subset _ _

lemma remainder_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (B : (p : ℕ) → Finset (ZMod p × ZMod p)) (N : ℕ)
    (S : Finset ℕ) (hS : S ⊆ P) :
    |remainder ((range N) ×ˢ (range N)) (hits P B) (localDensity B) ((N:ℝ)^2) S| ≤
      2*(N:ℝ)*(∏ p ∈ S, (p:ℝ))+(∏ p ∈ S, (p:ℝ))^2 := by
  have he (x : ℕ × ℕ) : S ⊆ hits P B x ↔
      ∀ p ∈ S, ((x.1:ZMod p),(x.2:ZMod p)) ∈ B p := by
    constructor
    · intro h p hp; exact (mem_filter.mp (h hp)).2
    · intro h p hp; exact mem_filter.mpr ⟨hS hp,h p hp⟩
  have hh := joint_box_discrepancy S (fun p hp => hP p (hS hp)) B N
  simpa only [remainder,jointCount,he] using hh

lemma level_coefficient_bound (P : Finset ℕ) (z : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℝ) (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1/2)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {S : Finset ℕ} (hS : S ∈ level P z) :
    (∏ p ∈ S, (1+odds (fun p => q*r p) p)) ≤ (z:ℝ) := by
  calc
    _ ≤ ∏ p ∈ S, (p:ℝ) := by
      apply prod_le_prod
      · intro p hp
        have hr0 := (hr p (level_subset P z hS hp)).1
        have hrhi : q*r p ≤ 1/2 :=
          (mul_le_of_le_one_left hr0 hq1).trans (hr p (level_subset P z hS hp)).2
        have ho : 0 ≤ odds (fun p => q*r p) p := div_nonneg (mul_nonneg hq0 hr0) (by linarith)
        linarith
      · intro p hp
        have hr0 := (hr p (level_subset P z hS hp)).1
        have hrhi : q*r p ≤ 1/2 :=
          (mul_le_of_le_one_left hr0 hq1).trans (hr p (level_subset P z hS hp)).2
        have ho : odds (fun p => q*r p) p ≤ 1 := by
          apply (div_le_one (by linarith : 0 < 1-q*r p)).mpr
          linarith
        have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hP p (level_subset P z hS hp)).two_le
        linarith
    _ ≤ _ := by
      have hh : ((∏ p ∈ S, p : ℕ):ℝ) ≤ z := by exact_mod_cast level_height P z hS
      simpa only [Nat.cast_prod] using hh

/-- A completely explicit finite upper sieve. The error is small relative
to N² for a sufficiently small power-of-N choice of the level z. -/
theorem few_hits_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (B : (p : ℕ) → Finset (ZMod p × ZMod p))
    (hB : ∀ p ∈ P, 0 < localDensity B p ∧ localDensity B p ≤ 1/2)
    (N z k : ℕ) (hz : 1 ≤ z) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (((((range N) ×ˢ (range N)).filter (fun x => (hits P B x).card ≤ k)).card:ℝ)*(1-q)^k) ≤
      (N:ℝ)^2/sieveMass (fun p => q*localDensity B p) (level P z) +
        2*(N:ℝ)*(z:ℝ)^6+(z:ℝ)^8 := by
  have hr (p : ℕ) (hp : p ∈ P) : 0 < localDensity B p ∧ localDensity B p < 1 :=
    ⟨(hB p hp).1,(hB p hp).2.trans_lt (by norm_num)⟩
  have hrem (S : Finset ℕ) (hS : S ∈ level P z) (T : Finset ℕ) (hT : T ∈ level P z) :
      |remainder ((range N) ×ˢ (range N)) (hits P B) (localDensity B) ((N:ℝ)^2) (S ∪ T)| ≤
        2*(N:ℝ)*(z:ℝ)^2+(z:ℝ)^4 := by
    have hh := remainder_bound P hP B N (S ∪ T)
      (union_subset (level_subset P z hS) (level_subset P z hT))
    have hb : (∏ p ∈ S ∪ T, (p:ℝ)) ≤ (z:ℝ)^2 := by
      have hh : ((∏ p ∈ S ∪ T, p : ℕ):ℝ) ≤ (z:ℝ)^2 := by exact_mod_cast union_height P z hP hS hT
      simpa only [Nat.cast_prod] using hh
    have hb0 : 0 ≤ ∏ p ∈ S ∪ T, (p:ℝ) := prod_nonneg (fun p _ => Nat.cast_nonneg p)
    have hbsq := pow_le_pow_left₀ hb0 hb 2
    have hmul := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ 2*N from by positivity)
    nlinarith only [hh,hbsq,hmul]
  have hh := few_hits_selberg_uniform P ((range N) ×ˢ (range N)) (hits P B)
    (localDensity B) ((N:ℝ)^2) (level P z) k hq0 hq1 hr
    (fun x _ => hits_subset P B x) (fun S hS => level_subset P z hS)
    (fun S hS T hT => level_downward P z hP hS T hT) (empty_mem_level P hz)
    (show (0:ℝ) ≤ z from Nat.cast_nonneg z)
    (show (0:ℝ) ≤ 2*(N:ℝ)*(z:ℝ)^2+(z:ℝ)^4 from by positivity)
    (fun S hS => level_coefficient_bound P z hP (localDensity B)
      (fun p hp => ⟨(hB p hp).1.le,(hB p hp).2⟩) hq0.le hq1 hS) hrem
  have hc : ((level P z).card:ℝ) ≤ (z:ℝ) := by exact_mod_cast level_card_le P z hP
  have hcsq := pow_le_pow_left₀ (Nat.cast_nonneg (level P z).card) hc 2
  have he := mul_le_mul_of_nonneg_right hcsq
    (show (0:ℝ) ≤ (z:ℝ)^2*(2*(N:ℝ)*(z:ℝ)^2+(z:ℝ)^4) from by positivity)
  nlinarith only [hh,he]

#print axioms level_card_le
#print axioms remainder_bound
#print axioms few_hits_bound
end Erdos1206.PrimeBoxSelberg
