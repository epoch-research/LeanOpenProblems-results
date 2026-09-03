import Submission.SquarefreeConicFamily
import Submission.TotientHarmonicBound

/-! Divergent primitive collision mass survives the logarithmic loss needed
for coprime squarefree multipliers. This does not establish a density bound
for independent sets of the collision hypergraph. -/

namespace Erdos1206.SquarefreeWeightedMass
open Finset Filter SquarefreeConicFamily
open scoped Classical Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

noncomputable def multiplierModulus (x : ℕ × ℕ) : ℕ :=
  6*roots 0 x*roots 1 x*roots 2 x*roots 3 x

lemma multiplierModulus_pos (x : ℕ × ℕ) : 0 < multiplierModulus x := by
  dsimp [multiplierModulus]
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (roots_pos 0 x))
    (roots_pos 1 x)) (roots_pos 2 x)) (roots_pos 3 x)

lemma logFactor_pos (x : ℕ × ℕ) : 0<1+Real.log (multiplierModulus x) := by
  have hh := Real.log_nonneg (show (1:ℝ) ≤ multiplierModulus x by exact_mod_cast multiplierModulus_pos x)
  linarith

noncomputable def logWeight (x : ℕ × ℕ) : ℝ :=
  if Good x then 1/((roots 3 x:ℝ)*(1+Real.log (multiplierModulus x))) else 0

lemma logWeight_nonneg (x : ℕ × ℕ) : 0≤logWeight x := by
  dsimp [logWeight]
  split_ifs
  · exact (one_div_pos.mpr (mul_pos (by exact_mod_cast roots_pos 3 x) (logFactor_pos x))).le
  · rfl

private lemma summable_block_sums {f : ℕ × ℕ → ℝ} (hf : ∀ x, 0≤f x)
    (hs : Summable f) (T : ℕ → Finset (ℕ × ℕ))
    (hT : Pairwise (fun i j => Disjoint (T i) (T j))) : Summable (fun j => ∑ x ∈ T j, f x) := by
  apply summable_of_sum_le (c := ∑'x, f x) (fun j => sum_nonneg (fun x _ => hf x))
  intro S
  have hdis : (S : Set ℕ).PairwiseDisjoint T := by
    intro i hi j hj hij
    exact hT hij
  rw [← sum_biUnion hdis]
  exact Summable.sum_le_tsum _ (fun x _ => hf x) hs

noncomputable def box (N : ℕ) : Finset (ℕ × ℕ) := range N ×ˢ range N
lemma box_mono {a b : ℕ} (hab : a≤b) : box a ⊆ box b :=
  product_subset_product (range_mono hab) (range_mono hab)

lemma modulus_height (N : ℕ) (hN : 0<N) {x : ℕ × ℕ} (hx : x ∈ box N) :
    multiplierModulus x ≤ 6*(1000000*(SquarefreeConicFamily.M+1)*N)^8 := by
  let B := (1000000*(SquarefreeConicFamily.M+1)*N)^2
  have h (i : Fin 4) : roots i x ≤ B := roots_height N hN i hx
  have hprod : multiplierModulus x ≤ 6*B*B*B*B := by
    dsimp [multiplierModulus]
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 6 (h 0)) (h 1)) (h 2)) (h 3)
  calc
    _ ≤ 6*B*B*B*B := hprod
    _ = _ := by dsimp [B]; ring

/-- The logarithmic penalty still leaves divergent mass. -/
theorem logWeight_not_summable : ¬ Summable logWeight := by
  intro hs
  obtain ⟨J,hJ⟩ := eventually_atTop.mp good_eventually_large
  let H : ℕ := 1000000*(SquarefreeConicFamily.M+1)
  have hHeq : H=1000000*(SquarefreeConicFamily.M+1) := rfl
  clear_value H
  let R : ℝ := 1+Real.log 6+8*Real.log H+8*((J:ℝ)+2)*Real.log 2
  have hReq : R=1+Real.log 6+8*Real.log H+8*((J:ℝ)+2)*Real.log 2 := rfl
  clear_value R
  have hH : 0<H := by
    rw [hHeq]
    exact Nat.mul_pos (by decide) (Nat.succ_pos _)
  have hHr : (0:ℝ)<H := by exact_mod_cast hH
  have hlogH : 0≤Real.log (H:ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  have hlog6 : 0≤Real.log (6:ℝ) := Real.log_nonneg (by norm_num)
  have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hR : 0<R := by rw [hReq]; positivity
  have hRc : 8*Real.log (2:ℝ) ≤ R := by
    rw [hReq]
    have hj : (0:ℝ)≤J := Nat.cast_nonneg J
    nlinarith only [hlogH,hlog6,hlog2,hj]
  let lo (j : ℕ) := 2^(j+J)
  let hi (j : ℕ) := 2^(j+J+1)
  let T (j : ℕ) := good (hi j) \ box (lo j)
  have hhi (j : ℕ) : hi j=2*lo j := by dsimp [hi,lo]; rw [pow_succ]; omega
  have hpos (j : ℕ) : 0<hi j := by dsimp [hi]; positivity
  have hbound (j : ℕ) : J ≤ hi j := by
    exact (show J ≤ j+J+1 by omega).trans (Nat.lt_pow_self (by decide : 1<2)).le
  have hTsub (j : ℕ) : T j ⊆ box (hi j) := by
    intro x hx
    exact (mem_filter.mp (mem_sdiff.mp hx).1).1
  have hTgood (j : ℕ) {x : ℕ × ℕ} (hx : x ∈ T j) : Good x :=
    (mem_filter.mp (mem_sdiff.mp hx).1).2
  have hTdir {i j : ℕ} (hlt : i<j) : Disjoint (T i) (T j) := by
    apply disjoint_left.mpr
    intro x hxi hxj
    have hpow : hi i ≤ lo j := by
      dsimp [hi,lo]
      exact Nat.pow_le_pow_right (by decide : 0<2) (by omega)
    exact (mem_sdiff.mp hxj).2 (box_mono hpow (hTsub i hxi))
  have hTdis : Pairwise (fun i j => Disjoint (T i) (T j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hh | hh
    · exact hTdir hh
    · exact (hTdir hh).symm
  have hcard (j : ℕ) : ((hi j:ℕ):ℝ)^2/4 ≤ (T j).card := by
    have hc := hJ (hi j) (hbound j)
    have hd : (good (hi j)).card ≤ (T j).card+(box (lo j)).card :=
      card_le_card_sdiff_add_card
    have hdR : ((good (hi j)).card : ℝ) ≤ (T j).card+(lo j:ℝ)^2 := by
      simpa only [box,card_product,card_range,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,pow_two] using
        (show ((good (hi j)).card : ℝ) ≤ (T j).card+(box (lo j)).card by exact_mod_cast hd)
    have hh : (hi j:ℝ)=2*(lo j:ℝ) := by exact_mod_cast hhi j
    nlinarith only [hc,hdR,hh]
  have hlogbound (j : ℕ) {x : ℕ × ℕ} (hx : x ∈ T j) :
      1+Real.log (multiplierModulus x) ≤ R*(j+1) := by
    have hm := modulus_height (hi j) (hpos j) (hTsub j hx)
    rw [← hHeq] at hm
    have hmR : (multiplierModulus x : ℝ) ≤ 6*((H:ℝ)*(hi j:ℝ))^8 := by exact_mod_cast hm
    have hh := Real.log_le_log (by exact_mod_cast multiplierModulus_pos x) hmR
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,
      Real.log_mul hHr.ne' (by exact_mod_cast (hpos j).ne')] at hh
    have hloghi : Real.log (hi j:ℝ)=((j:ℝ)+J+1)*Real.log 2 := by
      simp only [hi,Nat.cast_pow,Real.log_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    rw [hloghi] at hh
    have hdiff := mul_nonneg (sub_nonneg.mpr hRc) (Nat.cast_nonneg j)
    rw [hReq] at hdiff ⊢
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith only [hh,hdiff,hlog2]
  have hper (j : ℕ) {x : ℕ × ℕ} (hx : x∈T j) :
      1/((H:ℝ)^2*(hi j:ℝ)^2*R*(j+1)) ≤ logWeight x := by
    have hd : (roots 3 x : ℝ) ≤ (H:ℝ)^2*(hi j:ℝ)^2 := by
      have hd := roots_height (hi j) (hpos j) 3 (hTsub j hx)
      rw [← hHeq] at hd
      simpa only [Nat.cast_pow,Nat.cast_mul,mul_pow] using (show (roots 3 x:ℝ) ≤ ((H*hi j)^2:ℕ) by exact_mod_cast hd)
    have hlog := hlogbound j hx
    have hmul := mul_le_mul hd hlog (logFactor_pos x).le (by positivity : (0:ℝ)≤(H:ℝ)^2*(hi j:ℝ)^2)
    rw [logWeight,if_pos (hTgood j hx)]
    apply one_div_le_one_div_of_le (mul_pos (by exact_mod_cast roots_pos 3 x) (logFactor_pos x))
    nlinarith only [hmul]
  have hsum (j : ℕ) :
      (1/(4*(H:ℝ)^2*R))*(1/((j:ℝ)+1)) ≤ ∑x∈T j,logWeight x := by
    have hp := sum_le_sum (fun x hx => hper j hx)
    rw [sum_const,nsmul_eq_mul] at hp
    have hc := mul_le_mul_of_nonneg_right (hcard j)
      (show (0:ℝ)≤1/((H:ℝ)^2*(hi j:ℝ)^2*R*(j+1)) by positivity)
    have hzero : (hi j:ℝ) ≠ 0 := by exact_mod_cast (hpos j).ne'
    have he : ((hi j:ℝ)^2/4)*(1/((H:ℝ)^2*(hi j:ℝ)^2*R*(j+1))) =
        (1/(4*(H:ℝ)^2*R))*(1/((j:ℝ)+1)) := by
      field_simp
    exact he ▸ hc.trans hp
  have hbs := summable_block_sums logWeight_nonneg hs T hTdis
  have hsmall := Summable.of_nonneg_of_le (fun j => by positivity) hsum hbs
  have hconst : (1/(4*(H:ℝ)^2*R)) ≠ 0 := by positivity
  have hh := (summable_mul_left_iff hconst).mp hsmall
  have hh' : Summable (fun j : ℕ => (1:ℝ)/((j+1:ℕ):ℝ)) := by simpa only [Nat.cast_add,Nat.cast_one] using hh
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hh')

abbrev Index := SquarefreeConicFamily.Index

lemma index_logWeight_not_summable :
    ¬ Summable (fun x : Index => (1:ℝ)/((roots 3 x.val:ℝ)*(1+Real.log (multiplierModulus x.val)))) := by
  intro hs
  apply logWeight_not_summable
  have hh := (summable_subtype_iff_indicator (s := {x | Good x})
    (f := fun x => (1:ℝ)/((roots 3 x:ℝ)*(1+Real.log (multiplierModulus x))))).mp hs
  simpa only [logWeight,Set.indicator,Set.mem_setOf_eq] using hh

theorem exists_large_log_weight (C : ℝ) :
    ∃ E : Finset Index, C < ∑x∈E,(1:ℝ)/((roots 3 x.val:ℝ)*(1+Real.log (multiplierModulus x.val))) := by
  by_contra hn
  push_neg at hn
  apply index_logWeight_not_summable
  exact summable_of_sum_le (fun x => by
    exact (one_div_pos.mpr (mul_pos (by exact_mod_cast roots_pos 3 x.val) (logFactor_pos x.val))).le) hn

#print axioms logWeight_not_summable
#print axioms exists_large_log_weight
end Erdos1206.SquarefreeWeightedMass
