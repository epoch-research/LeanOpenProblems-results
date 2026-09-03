import Submission.DirectFiveRawComparison
import Submission.DirectFiveFirstLayer
import Submission.SharpNoThreeHoleMeasure

/-! A stronger hole law with prime-dependent caps. This still requires an
explicit exceptional-weight bound to exclude a near-cover. -/
namespace Erdos7DirectFiveHoleMeasure
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
open Erdos7DirectFiveLayers Erdos7DoubleExceptionHybrid
open Erdos7DirectFiveFirstLayer
open Erdos7DirectFiveScalar Erdos7DirectFiveHybrid
set_option maxHeartbeats 6000000

/-- A single subprobability law avoids the base boxes, retains mass>1/2,
and has simultaneous product caps for every coordinate box. -/
theorem exists_hole_weights {n : ℕ} {κ : Type*} [Fintype κ]
    (hn : 366 ≤ n)
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 366, p (Fin.castLE hn i)=Erdos7DirectFiveScalar.primes i)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i≠0) (heE : ∀ k i, e k i≤E i)
    (X : κ → ∀ i, Finset (A i)) (hX0 : ∀ k i, e k i=0 → X k i=Finset.univ)
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ)*((p i : ℚ)⁻¹)^(e k i))
    (Y₀ : Finset (A (Fin.castLE hn (0 : Fin 366)))) (hY₀ : fraction Y₀ ≤ 1/5)
    : ∃ ν : (∀ i, A i) → ℚ,
      (∀ x, 0 ≤ ν x) ∧ (1/2 : ℚ) < ∑ x, ν x ∧ (∑ x, ν x) ≤ 1 ∧
      (∀ k x, (∀ i, x i∈X k i) → ν x=0) ∧
      (∀ x, x (Fin.castLE hn (0 : Fin 366))∈Y₀ → ν x=0) ∧
      ∀ (T : Finset (Fin n)) (Y : ∀ i, Finset (A i)),
        boxMass A ν T Y ≤ ∏ i∈T, cap (p i)*fraction (Y i) := by
  classical
  let S (k : κ) := expSupport (e k)
  have hne (k : κ) : (S k).Nonempty := by
    obtain ⟨i,hi⟩ := he0 k
    exact ⟨i,(mem_expSupport _ _).mpr hi⟩
  let σ (k : κ) := (S k).max' (hne k)
  have hσ (k : κ) : σ k∈S k := Finset.max'_mem _ _
  have hS (k : κ) (j : Fin n) (hj : j∈S k) : j≤σ k := Finset.le_max' _ _ hj
  let j₀ : Fin n := Fin.castLE hn (0 : Fin 366)
  have hj₀ : j₀.val=0 := rfl
  have hp₀ : p j₀=5 := hpre 0
  let B₀ := layeredBad A S X σ
  let P := Finset.univ.filter (fun x : ∀ i, A i => x j₀∈Y₀)
  let B (i : Fin n) := if i=j₀ then B₀ i∪P else B₀ i
  have hB (i : Fin n) (hi : i≠j₀) : B i=B₀ i := by simp only [B,if_neg hi]
  have hBinv : ∀ i j : Fin n, j < i → ∀ x v, Function.update x i v∈B j ↔ x∈B j := by
    intro i j hji x v
    have hb := layeredBad_invariant A S X σ hS i j hji x v
    by_cases hj : j=j₀
    · subst j
      have hi : j₀≠i := ne_of_lt hji
      simpa only [B,if_pos rfl,Finset.mem_union,P,Finset.mem_filter,Finset.mem_univ,true_and,
        Function.update_of_ne hi,B₀,hb] using (or_congr hb (Iff.rfl : x j₀∈Y₀ ↔ x j₀∈Y₀))
    · simpa only [B,if_neg hj,B₀] using hb
  let c : Fin n → ℚ := fun i => cap (p i)
  have hc (i : Fin n) : 1 ≤ c i := by
    dsimp only [c]
    have := (cap_bounds (p i)).1
    linarith
  let L (i : Fin n) := ∑ x, towerWeights A B c i.val x *
    Erdos7Distortion.residual (c i) (coordinateFraction A i (B i) x)
  have hp1 (i : Fin n) : 1 < p i := by have := (hp i).2; omega
  have hpQ (i : Fin n) : (5 : ℚ) ≤ p i := by exact_mod_cast (hp i).2
  have hfrac (k : κ) (i : Fin n) : fraction (X k i) ≤ ((p i : ℚ)⁻¹)^(e k i) := by
    apply (div_le_iff₀ card_pos_rat).mpr
    simpa only [mul_comm] using hX k i
  have hraw (i : Fin n) (hi : 366 ≤ i.val) : L i ≤ (88/67 : ℚ)*raw p i := by
    have hne : i≠j₀ := by intro h; subst i; change 366 ≤ 0 at hi; omega
    have hh := layer_raw_loss_bound A B p hp1 e hei he0 X hX0 hX c
      (fun i => by dsimp only [c]; have := (cap_bounds (p i)).1; linarith) σ hσ hS i
    have h5 : p (Fin.castLE hn (0 : Fin 366))=5 := hpre 0
    have h7 : p (Fin.castLE hn (1 : Fin 366))=7 := hpre 1
    have hlarge : 7 < p i := by
      rw [← h7]
      apply hmono
      change 1 < i.val
      omega
    have hfinal := hh.trans (Erdos7DirectFiveRawComparison.raw_tail_bound p
      (fun i => (hp i).2) hmono.injective (Fin.castLE hn 0) h5 i
      (by change 0 < i.val; omega) hlarge)
    simpa only [L,hB i hne,B₀,S,c] using hfinal
  have hearly (i : Fin n) (hi : i.val<366) : L i ≤
      exponentEnvelope E (fun j => powerTail (p j) (cap (p j)) (E j))
        (fun x => Erdos7Distortion.residual (cap (p i)) (1/(p i-1 : ℚ)*x+offset (p i))) i.val 1 := by
    by_cases hi0 : i=j₀
    · subst i
      have hroot (x : ∀ i, A i) : coordinateFraction A j₀ (B j₀) x ≤ 1/2 := by
        have hbase := first_layer_fraction A j₀ hj₀ 5 (E j₀) (by decide) e hei
          (fun k => heE k j₀) X (fun k => by simpa only [hp₀] using hfrac k j₀) σ hσ hS x
        have hh := coordinate_union A j₀ (B₀ j₀) P x
        have he := coordinate_pure A j₀ Y₀ x
        change coordinateFraction A j₀ P x=fraction Y₀ at he
        rw [he] at hh
        change coordinateFraction A j₀ (B₀ j₀) x ≤ 1/(5-1 : ℚ) at hbase
        change coordinateFraction A j₀ (if j₀=j₀ then B₀ j₀∪P else B₀ j₀) x ≤ 1/2
        rw [if_pos rfl]
        linarith
      have hzero (x : ∀ i, A i) : residual (c j₀) (coordinateFraction A j₀ (B j₀) x)=0 := by
        have hh := hroot x
        rw [show c j₀=2 by norm_num [c,hp₀,cap]]
        unfold Erdos7Distortion.residual
        exact max_eq_left (by linarith)
      simp only [L,hzero,mul_zero,Finset.sum_const_zero,hj₀,exponentEnvelope]
      exact le_max_left _ _
    have hpi : p i≠5 := by intro h; exact hi0 (hmono.injective (h.trans hp₀.symm))
    have hoff : offset (p i)=0 := by simp [offset,hpi]
    simp only [hoff,add_zero]
    change (∑ x, towerWeights A B c i.val x*residual (c i) (coordinateFraction A i (B i) x)) ≤ _
    rw [hB i hi0]
    apply layer_exponent_loss_bound A B E c (fun i => 1/(p i-1 : ℚ))
      (fun i g => ((p i : ℚ)⁻¹)^g) (fun i => powerTail (p i) (c i) (E i)) hc
    · intro i; apply one_div_pos.mpr; linarith [hpQ i]
    · intros; positivity
    · intro i; exact positive_power_sum_le (p i) (hp1 i) (E i)
    · intro i; apply powerTail_zero_le_one (p i) (hp1 i) (c i); exact cap_le_prime (p i) (hp i).2
    · intro i g hg; exact powerTail_decreasing (p i) (hp1 i) (c i) (by dsimp only [c]; have := (cap_bounds (p i)).1; linarith) (E i) g
    · intro i; exact powerTail_terminal _ _ _
    · intro i g hg; simp only [powerTail,if_pos hg,le_refl]
    · exact hei
    · exact heE
    · exact hne
    · exact fun k i _ => hfrac k i
    · exact hσ
    · exact hS
  have hsmall := hybrid_lt_half hn p E hp hmono hpre L hraw hearly
  let C := Finset.univ.filter (fun x : ∀ i, A i => (¬ ∃ k, ∀ i, x i∈X k i) ∧ x j₀∉Y₀)
  have hcov : ∀ x : ∀ i, A i, (∃ i, x∈B i) ∨ x∈C := by
    intro x
    by_cases hx : ∃ k, ∀ i, x i∈X k i
    · obtain ⟨k,hk⟩ := hx
      have hb : x∈B₀ (σ k) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,k,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,fun j _ => hk j⟩
      left
      refine ⟨σ k,?_⟩
      dsimp only [B]
      split_ifs <;> [exact Finset.mem_union_left _ hb; exact hb]
    · by_cases hy : x j₀∈Y₀
      · left
        refine ⟨j₀,?_⟩
        simp only [B,if_pos rfl,Finset.mem_union]
        exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,hy⟩)
  have hb := Erdos7ExceptionalBox.coordinate_cover_with_exception A B c hc hBinv C hcov
  let μ := towerWeights A B c n
  let ν (x : ∀ i, A i) := if x∈C then μ x else 0
  have hμ : ∀ x, 0 ≤ μ x := towerWeights_nonneg A B c hc n
  have hν : ∀ x, 0 ≤ ν x := fun x => by dsimp only [ν]; split_ifs <;> [exact hμ x; rfl]
  have hle (x : ∀ i, A i) : ν x ≤ μ x := by
    dsimp only [ν]
    split_ifs <;> [rfl; exact hμ x]
  have hsum : (∑ x, ν x)=∑ x∈C, μ x := by
    simp only [ν,← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
  refine ⟨ν,hν,?_,?_,?_,?_,?_⟩
  · rw [hsum]
    change 1 ≤ (∑ x∈C, μ x)+(∑ i, L i) at hb
    linarith
  · exact (Finset.sum_le_sum (fun x _ => hle x)).trans_eq (towerWeights_total A B c hc n)
  · intro k x hx
    have hn : x∉C := by
      intro h
      exact (Finset.mem_filter.mp h).2.1 ⟨k,hx⟩
    exact if_neg hn
  · intro x hx
    have hn : x∉C := by
      intro h
      exact (Finset.mem_filter.mp h).2.2 hx
    exact if_neg hn
  · intro T Y
    apply le_trans (b := boxMass A μ T Y)
    · exact Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_right (hle x) (boxIndicator_nonneg A T Y x))
    · exact towerWeights_box_bound A B c hc n le_rfl T (fun i _ => i.isLt) Y


theorem not_cover_with_weighted_boxes {n : ℕ} {κ J : Type*} [Fintype κ] [Fintype J]
    (hn : 366 ≤ n)
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 366, p (Fin.castLE hn i)=Erdos7DirectFiveScalar.primes i)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i≠0) (heE : ∀ k i, e k i≤E i)
    (X : κ → ∀ i, Finset (A i)) (hX0 : ∀ k i, e k i=0 → X k i=Finset.univ)
    (hX : ∀ k i, ((X k i).card : ℚ) ≤ (Fintype.card (A i) : ℚ)*((p i : ℚ)⁻¹)^(e k i))
    (Y₀ : Finset (A (Fin.castLE hn (0 : Fin 366)))) (hY₀ : fraction Y₀ ≤ 1/5)
    (T : J → Finset (Fin n)) (Y : J → ∀ i, Finset (A i))
    (hweight : (∑ j, ∏ i∈T j, cap (p i)*fraction (Y j i)) ≤ 1/2) :
    ¬ (∀ x : ∀ i, A i, (∃ k, ∀ i, x i∈X k i) ∨ x (Fin.castLE hn (0 : Fin 366))∈Y₀ ∨
      (∃ j, ∀ i∈T j, x i∈Y j i)) := by
  intro hcover
  classical
  obtain ⟨ν,hν,hmass,_,hzero,hpure,hbox⟩ := exists_hole_weights hn A p E hp hmono hpre e hei he0 heE X hX0 hX Y₀ hY₀
  have hpoint (x : ∀ i, A i) : ν x ≤ ∑ j, ν x*boxIndicator A (T j) (Y j) x := by
    rcases hcover x with ⟨k,hk⟩ | hy | ⟨j,hj⟩
    · simp only [hzero k x hk,zero_mul,Finset.sum_const_zero,le_refl]
    · simp only [hpure x hy,zero_mul,Finset.sum_const_zero,le_refl]
    · have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) =>
        mul_nonneg (hν x) (boxIndicator_nonneg A (T j) (Y j) x)) (Finset.mem_univ j)
      simpa only [boxIndicator,if_pos hj,mul_one] using hh
  have hlow := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => hpoint x)
  rw [Finset.sum_comm] at hlow
  change (∑ x, ν x) ≤ ∑ j, boxMass A ν (T j) (Y j) at hlow
  have hhigh := (Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hbox (T j) (Y j))).trans hweight
  linarith

#print axioms not_cover_with_weighted_boxes
#print axioms exists_hole_weights
end Erdos7DirectFiveHoleMeasure
