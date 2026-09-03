import Submission.DoubleExceptionBox

/-!
# A uniform finite measure on the holes of a no-3 box family

The weighted exceptional-family criterion has no cardinality bound on the
exceptions. Its numerical weight hypothesis is still required.
-/
namespace Erdos7NoThreeHoleMeasure
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7ExceptionalLayers Erdos7DoubleExceptionHybrid
set_option maxHeartbeats 6000000

/-- A single subprobability law avoids the base boxes, retains mass>1/2,
and has simultaneous product caps for every coordinate box. -/
theorem exists_hole_weights {n : ℕ} {κ : Type*} [Fintype κ]
    (hn : 94 ≤ n)
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 94, p (Fin.castLE hn i)=Erdos7DoubleExceptionScalar.primes i)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i≠0) (heE : ∀ k i, e k i≤E i)
    (X : κ → ∀ i, Finset (A i)) (hX0 : ∀ k i, e k i=0 → X k i=Finset.univ)
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ)*((p i : ℚ)⁻¹)^(e k i))
    : ∃ ν : (∀ i, A i) → ℚ,
      (∀ x, 0 ≤ ν x) ∧ (1/2 : ℚ) < ∑ x, ν x ∧ (∑ x, ν x) ≤ 1 ∧
      (∀ k x, (∀ i, x i∈X k i) → ν x=0) ∧
      ∀ (T : Finset (Fin n)) (Y : ∀ i, Finset (A i)),
        boxMass A ν T Y ≤ ∏ i∈T, (5/4 : ℚ)*fraction (Y i) := by
  classical
  let S (k : κ) := expSupport (e k)
  have hne (k : κ) : (S k).Nonempty := by
    obtain ⟨i,hi⟩ := he0 k
    exact ⟨i,(mem_expSupport _ _).mpr hi⟩
  let σ (k : κ) := (S k).max' (hne k)
  have hσ (k : κ) : σ k∈S k := Finset.max'_mem _ _
  have hS (k : κ) (j : Fin n) (hj : j∈S k) : j≤σ k := Finset.le_max' _ _ hj
  let B := layeredBad A S X σ
  let c : Fin n → ℚ := fun _ => 5/4
  have hc (i : Fin n) : 1 ≤ c i := by norm_num [c]
  let L (i : Fin n) := ∑ x, towerWeights A B c i.val x *
    Erdos7Distortion.residual (c i) (coordinateFraction A i (B i) x)
  have hp1 (i : Fin n) : 1 < p i := by have := (hp i).2; omega
  have hpQ (i : Fin n) : (5 : ℚ) ≤ p i := by exact_mod_cast (hp i).2
  have hfrac (k : κ) (i : Fin n) : fraction (X k i) ≤ ((p i : ℚ)⁻¹)^(e k i) := by
    apply (div_le_iff₀ card_pos_rat).mpr
    simpa only [mul_comm] using hX k i
  have hraw (i : Fin n) : L i ≤ raw p i := by
    have hh := layer_raw_loss_bound A p hp1 e hei he0 X hX0 hX c
      (fun i => by norm_num [c]) σ hσ hS i
    convert hh using 1
    unfold raw Erdos7No23Sieve.charge Erdos7No23Sieve.multiplier
    dsimp only [c]
    norm_num
    ring
  have hearly (i : Fin n) (hi : i.val<94) : L i ≤
      exponentEnvelope E (fun j => powerTail (p j) (5/4) (E j))
        (fun x => Erdos7Distortion.residual (5/4) (1/(p i-1 : ℚ)*x)) i.val 1 := by
    apply layer_exponent_loss_bound A E c (fun i => 1/(p i-1 : ℚ))
      (fun i g => ((p i : ℚ)⁻¹)^g) (fun i => powerTail (p i) (c i) (E i)) hc
    · intro i; apply one_div_pos.mpr; linarith [hpQ i]
    · intros; positivity
    · intro i; exact positive_power_sum_le (p i) (hp1 i) (E i)
    · intro i; apply powerTail_zero_le_one (p i) (hp1 i) (c i); dsimp [c]; linarith [hpQ i]
    · intro i g hg; exact powerTail_decreasing (p i) (hp1 i) (c i) (by norm_num [c]) (E i) g
    · intro i; exact powerTail_terminal _ _ _
    · intro i g hg; simp only [powerTail,if_pos hg,le_refl]
    · exact hei
    · exact heE
    · exact hne
    · exact fun k i _ => hfrac k i
    · exact hσ
    · exact hS
  have hsmall := hybrid_lt_one_half hn p E hp hmono hpre L hraw hearly
  let C := Finset.univ.filter (fun x : ∀ i, A i => ¬ ∃ k, ∀ i, x i∈X k i)
  have hcov : ∀ x : ∀ i, A i, (∃ i, x∈B i) ∨ x∈C := by
    intro x
    by_cases hx : ∃ k, ∀ i, x i∈X k i
    · obtain ⟨k,hk⟩ := hx
      exact Or.inl ⟨σ k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,fun j _ => hk j⟩⟩
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
  have hb := Erdos7ExceptionalBox.coordinate_cover_with_exception A B c hc
    (layeredBad_invariant A S X σ hS) C hcov
  let μ := towerWeights A B c n
  let ν (x : ∀ i, A i) := if x∈C then μ x else 0
  have hμ : ∀ x, 0 ≤ μ x := towerWeights_nonneg A B c hc n
  have hν : ∀ x, 0 ≤ ν x := fun x => by dsimp only [ν]; split_ifs <;> [exact hμ x; rfl]
  have hle (x : ∀ i, A i) : ν x ≤ μ x := by
    dsimp only [ν]
    split_ifs <;> [rfl; exact hμ x]
  have hsum : (∑ x, ν x)=∑ x∈C, μ x := by
    simp only [ν,← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
  refine ⟨ν,hν,?_,?_,?_,?_⟩
  · rw [hsum]
    change 1 ≤ (∑ x∈C, μ x)+(∑ i, L i) at hb
    linarith
  · exact (Finset.sum_le_sum (fun x _ => hle x)).trans_eq (towerWeights_total A B c hc n)
  · intro k x hx
    have hn : x∉C := by
      intro h
      exact (Finset.mem_filter.mp h).2 ⟨k,hx⟩
    exact if_neg hn
  · intro T Y
    apply le_trans (b := boxMass A μ T Y)
    · exact Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_right (hle x) (boxIndicator_nonneg A T Y x))
    · exact towerWeights_box_bound A B c hc n le_rfl T (fun i _ => i.isLt) Y

/-- Normalize the surviving weights. The SAME probability law controls every
coordinate box, at most twice its multiplicative distortion weight. -/
theorem exists_hole_probability {n : ℕ} {κ : Type*} [Fintype κ]
    (hn : 94 ≤ n)
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 94, p (Fin.castLE hn i)=Erdos7DoubleExceptionScalar.primes i)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i≠0) (heE : ∀ k i, e k i≤E i)
    (X : κ → ∀ i, Finset (A i)) (hX0 : ∀ k i, e k i=0 → X k i=Finset.univ)
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ)*((p i : ℚ)⁻¹)^(e k i))
    : ∃ μ : (∀ i, A i) → ℚ,
      (∀ x, 0 ≤ μ x) ∧ (∑ x, μ x)=1 ∧
      (∀ k x, (∀ i, x i∈X k i) → μ x=0) ∧
      ∀ (T : Finset (Fin n)) (Y : ∀ i, Finset (A i)),
        boxMass A μ T Y ≤ 2*(∏ i∈T, (5/4 : ℚ)*fraction (Y i)) := by
  classical
  obtain ⟨ν,hν,hmass,_,hzero,hbox⟩ := exists_hole_weights hn A p E hp hmono hpre e hei he0 heE X hX0 hX
  let M := ∑ x, ν x
  have hM : (0 : ℚ)<M := by dsimp only [M]; linarith
  let μ (x : ∀ i, A i) := ν x/M
  refine ⟨μ,(fun x => div_nonneg (hν x) hM.le),?_,?_,?_⟩
  · dsimp only [μ]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hM)
  · intro k x hx
    dsimp only [μ]
    rw [hzero k x hx,zero_div]
  · intro T Y
    have he : boxMass A μ T Y=boxMass A ν T Y/M := by
      simp only [boxMass,μ,div_mul_eq_mul_div,Finset.sum_div]
    rw [he]
    apply (div_le_div_of_nonneg_right (hbox T Y) hM.le).trans
    apply (div_le_iff₀ hM).mpr
    have hw : (0 : ℚ)≤∏ i∈T, (5/4 : ℚ)*fraction (Y i) :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (by norm_num) (fraction_nonneg _))
    change (1/2 : ℚ)<M at hmass
    nlinarith

/-- Weighted union bound after a base family has been assigned zero mass. -/
lemma exceptional_box_union {ι κ J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (A : ι → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (ν : (∀ i, A i) → ℚ) (hν : ∀ x, 0 ≤ ν x)
    (X : κ → ∀ i, Finset (A i))
    (hzero : ∀ k x, (∀ i, x i∈X k i) → ν x=0)
    (T : J → Finset ι) (Y : J → ∀ i, Finset (A i))
    (hcover : ∀ x : ∀ i, A i, (∃ k, ∀ i, x i∈X k i) ∨
      (∃ j, ∀ i∈T j, x i∈Y j i)) :
    (∑ x, ν x) ≤ ∑ j, boxMass A ν (T j) (Y j) := by
  classical
  have hpoint (x : ∀ i, A i) : ν x ≤ ∑ j, ν x*boxIndicator A (T j) (Y j) x := by
    have hnon (j : J) : 0 ≤ ν x*boxIndicator A (T j) (Y j) x :=
      mul_nonneg (hν x) (boxIndicator_nonneg A _ _ _)
    rcases hcover x with ⟨k,hk⟩ | ⟨j,hj⟩
    · simp only [hzero k x hk,zero_mul,Finset.sum_const_zero,le_refl]
    · have hh := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ j)
      simpa only [boxIndicator,if_pos hj,mul_one] using hh
  have hh := Finset.sum_le_sum (fun x (_ : x∈(Finset.univ : Finset (∀ i, A i))) => hpoint x)
  rw [Finset.sum_comm] at hh
  exact hh

/-- An arbitrarily large exceptional family is excluded if its total product
weight is at most one half. No distinctness is imposed on the exceptions. -/
theorem not_cover_with_weighted_boxes {n : ℕ} {κ J : Type*} [Fintype κ] [Fintype J]
    (hn : 94 ≤ n)
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 94, p (Fin.castLE hn i)=Erdos7DoubleExceptionScalar.primes i)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i≠0) (heE : ∀ k i, e k i≤E i)
    (X : κ → ∀ i, Finset (A i)) (hX0 : ∀ k i, e k i=0 → X k i=Finset.univ)
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ)*((p i : ℚ)⁻¹)^(e k i))
    (T : J → Finset (Fin n)) (Y : J → ∀ i, Finset (A i))
    (hweight : (∑ j, ∏ i∈T j, (5/4 : ℚ)*fraction (Y j i)) ≤ 1/2) :
    ¬ (∀ x : ∀ i, A i, (∃ k, ∀ i, x i∈X k i) ∨
      (∃ j, ∀ i∈T j, x i∈Y j i)) := by
  intro hcover
  obtain ⟨ν,hν,hmass,_,hzero,hbox⟩ := exists_hole_weights hn A p E hp hmono hpre e hei he0 heE X hX0 hX
  have hlow := exceptional_box_union A ν hν X hzero T Y hcover
  have hhigh := (Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hbox (T j) (Y j))).trans hweight
  linarith

#print axioms exists_hole_weights
#print axioms exists_hole_probability
#print axioms exceptional_box_union
#print axioms not_cover_with_weighted_boxes
end Erdos7NoThreeHoleMeasure
