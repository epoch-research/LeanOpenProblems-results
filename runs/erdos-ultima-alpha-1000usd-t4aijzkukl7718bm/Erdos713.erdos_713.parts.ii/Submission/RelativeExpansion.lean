import FormalConjecturesUtil
import Submission.RelativeCloneSaturation

/-! Uniform expansion from exact extremality and a relative minimum degree. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Topology
namespace Erdos713RelativeExpansion
open Erdos713Cloning Erdos713SwitchGluing
set_option maxHeartbeats 2000000

open scoped Classical in
lemma degree_cut_bound {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hFree : H.Free G) (S : Finset V) :
    (∑ v ∈ S, G.degree v) ≤ 2*extremalNumber S.card H +
      Nat.card (cross G (S : Set V)).edgeSet := by
  classical
  have hdeg (v : V) (hv : v ∈ S) :
      G.degree v = (inside G (S : Set V)).degree v + (cross G (S : Set V)).degree v := by
    have heq : G.neighborFinset v = (inside G (S : Set V)).neighborFinset v ∪
        (cross G (S : Set V)).neighborFinset v := by
      ext w
      simp only [mem_union,mem_neighborFinset,inside,cross,Finset.mem_coe]
      tauto
    have hd : Disjoint ((inside G (S : Set V)).neighborFinset v)
        ((cross G (S : Set V)).neighborFinset v) := by
      rw [Finset.disjoint_left]
      intro w hw hw'
      simp only [mem_neighborFinset,inside,cross,Finset.mem_coe] at hw hw'
      tauto
    rw [← card_neighborFinset_eq_degree,heq,card_union_of_disjoint hd,
      card_neighborFinset_eq_degree,card_neighborFinset_eq_degree]
  have hb : (cross G (S : Set V)).IsBipartiteWith (S : Set V) (Sᶜ : Finset V) := by
    refine ⟨by simpa only [coe_compl] using (show Disjoint (S : Set V) ((S : Set V)ᶜ) from disjoint_compl_right),?_⟩
    intro v w hvw
    change G.Adj v w ∧ _ at hvw
    simpa only [Finset.mem_coe,mem_compl] using hvw.2.imp id And.symm
  have hi := sum_le_sum_of_subset (f := fun v => (inside G (S : Set V)).degree v) (subset_univ S)
  rw [sum_degrees_eq_twice_card_edges] at hi
  have hcross := isBipartiteWith_sum_degrees_eq_card_edges hb
  have hEq : (∑ v ∈ S, G.degree v) =
      (∑ v ∈ S, (inside G (S : Set V)).degree v) +
      (cross G (S : Set V)).edgeFinset.card := by
    rw [← hcross,← sum_add_distrib]
    exact sum_congr rfl hdeg
  rw [hEq]
  have hin := inside_edges_le H G hFree S
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hi hin ⊢
  omega

lemma linear_error_upper (f : ℕ → ℕ) (hf0 : f 0 = 0) {α c C : ℝ}
    (hC : 0 < C) (hcC : c < C)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, (f n : ℝ) ≤ C*(n : ℝ)^α+B*n := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((Erdos713FutureRecords.ratio_limit h).eventually_lt_const hcC)
  obtain ⟨k,hk,hmax⟩ := (range (M+1)).exists_max_image f ⟨0,by simp⟩
  refine ⟨f k,Nat.cast_nonneg _,?_⟩
  intro n
  by_cases hn0 : n = 0
  · subst n; rw [hf0,Nat.cast_zero]; positivity
  have hnp : 0 < n := Nat.pos_of_ne_zero hn0
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
  by_cases hn : M ≤ n
  · have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hnr α)).mp (hM n hn)
    nlinarith [mul_nonneg (Nat.cast_nonneg (f k) : (0 : ℝ) ≤ f k) hnr.le]
  · have hh : f n ≤ f k := hmax n (mem_range.mpr (by omega))
    have hm : f n ≤ f k*n := hh.trans (Nat.le_mul_of_pos_right _ hnp)
    have hmR : (f n : ℝ) ≤ (f k : ℝ)*n := by exact_mod_cast hm
    nlinarith [mul_nonneg hC.le (Real.rpow_nonneg hnr.le α)]

lemma small_cut_bound {α c B δ n s x : ℝ} (ha : 1 < α) (hc : 0 < c)
    (hn : 0 ≤ n) (hs : 0 ≤ s) (hd : 0 ≤ δ) (hsize : s ≤ δ*n)
    (hpow : δ^(α-1) = 1/768) (hB : B ≤ c/384*n^(α-1))
    (hcut : c/48*s*n^(α-1) ≤ 4*c*s^α+2*B*s+x) :
    c/96*s*n^(α-1) ≤ x := by
  have hp := Real.rpow_le_rpow hs hsize (show 0 ≤ α-1 by linarith)
  rw [Real.mul_rpow hd hn,hpow] at hp
  have hterm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4*c*s by positivity)
  have hbterm := mul_le_mul_of_nonneg_right hB (show 0 ≤ 2*s by positivity)
  rw [rpow_factor hs ha] at hcut
  nlinarith only [hcut,hterm,hbterm]

lemma large_cut_bound {α c B δ η n s x : ℝ} (ha : 1 < α) (hc : 0 < c)
    (hn : 0 ≤ n) (hs : 0 ≤ s) (hsize : 2*s ≤ n) (hlarge : δ*n ≤ s)
    (hη : 0 ≤ η) (heq : η = c*expansionConstant α*δ/8)
    (hB : B ≤ c*expansionConstant α*δ/4*n^(α-1))
    (hcut : (c-η)*n^α ≤ (c+η)*(s^α+(n-s)^α)+B*n+x) :
    c*expansionConstant α/2*s*n^(α-1) ≤ x := by
  have hk := expansionConstant_pos ha
  have hp := power_gap hn hs hsize ha
  have hterm := mul_le_mul_of_nonneg_left hp hc.le
  have hsum : s^α+(n-s)^α ≤ n^α := by
    have hh : 0 ≤ expansionConstant α*s*n^(α-1) := by positivity
    linarith
  have herr := mul_le_mul_of_nonneg_left hsum hη
  have hlarge' := mul_le_mul_of_nonneg_right hlarge
    (show 0 ≤ c*expansionConstant α/4*n^(α-1) by positivity)
  have hbterm := mul_le_mul_of_nonneg_right hB hn
  have hfactor := rpow_factor hn ha
  have heterm : 2*η*n^α ≤ c*expansionConstant α/4*s*n^(α-1) := by
    rw [heq,hfactor]
    nlinarith only [hlarge']
  have hbterm' : B*n ≤ c*expansionConstant α/4*s*n^(α-1) := by
    nlinarith only [hlarge',hbterm]
  nlinarith only [hcut,hterm,herr,heterm,hbterm']

/-- Every sufficiently large exact optimizer with the indicated relative
minimum degree is expanding. The threshold is uniform over all hosts. -/
theorem eventually_expanding_exact {W : Type*} (H : SimpleGraph W) {α c : ℝ}
    (ha : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V = n →
        H.Free G → Nat.card G.edgeSet = extremalNumber n H →
        (∀ v, Nat.card G.edgeSet ≤ 24*n*Nat.card (G.neighborSet v)) →
        ∀ S : Finset V, 2*S.card ≤ n →
          κ*S.card*(n : ℝ)^(α-1) ≤ (Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
  classical
  let δ : ℝ := (1/768 : ℝ)^((α-1)⁻¹)
  have hd : 0 < δ := Real.rpow_pos_of_pos (by norm_num) _
  have hd1 : δ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (inv_pos.mpr (by linarith))
  have hdpow : δ^(α-1) = 1/768 := Real.rpow_inv_rpow (by norm_num) (by linarith)
  let k := expansionConstant α
  have hk : 0 < k := expansionConstant_pos ha
  have hk1 : k < 1 := by
    have hh := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2) (α-1)
    dsimp only [k,expansionConstant]
    linarith
  let η := c*k*δ/8
  have hη : 0 < η := by dsimp [η]; positivity
  have hηc : η < c/2 := by
    have hh := mul_lt_mul_of_pos_left hk1 hc
    have hh' := mul_lt_mul_of_pos_left hd1 (mul_pos hc hk)
    dsimp only [η]
    nlinarith
  obtain ⟨B,hB,hUpper⟩ := linear_error_upper (fun n => extremalNumber n H)
    (extremal_zero H) (show 0 < c+η by positivity) (by linarith) h
  let κ := min (c/96) (c*k/2)
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  let b := min (c/384) (c*k*δ/4)
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have htop : Tendsto (fun n : ℕ => b*(n : ℝ)^(α-1)) atTop atTop :=
    Tendsto.const_mul_atTop hb
      ((tendsto_rpow_atTop (by linarith : 0 < α-1)).comp tendsto_natCast_atTop_atTop)
  refine ⟨κ,hκ,?_⟩
  filter_upwards [htop.eventually_ge_atTop B,
    (Erdos713FutureRecords.ratio_limit h).eventually_const_lt (show c-η < c by linarith),
    eventually_gt_atTop (0 : ℕ)] with n hBn hLow hn
  intro V instV G hcard hFree hE hDeg S hS
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hsNat : S.card ≤ n := by omega
  have hhalf : (2 : ℝ)*S.card ≤ n := by exact_mod_cast hS
  have hp : 0 < (n : ℝ)^(α-1) := Real.rpow_pos_of_pos hnR _
  have hLow' : (c-η)*(n : ℝ)^α ≤ (extremalNumber n H : ℝ) :=
    ((lt_div_iff₀ (Real.rpow_pos_of_pos hnR α)).mp hLow).le
  have hLowHalf : c/2*(n : ℝ)^α ≤ (extremalNumber n H : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (show c/2 ≤ c-η by linarith)
      (Real.rpow_nonneg hnR.le α)
    exact hh.trans hLow'
  have hBsmall : B ≤ c/384*(n : ℝ)^(α-1) := hBn.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hp.le)
  have hBlarge : B ≤ c*k*δ/4*(n : ℝ)^(α-1) := hBn.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hp.le)
  by_cases hsmall : (S.card : ℝ) ≤ δ*n
  · have hmindeg (v : V) : c/48*(n : ℝ)^(α-1) ≤ (G.degree v : ℝ) := by
      have hh : extremalNumber n H ≤ 24*n*G.degree v := by
        simpa only [hE,Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hDeg v
      have hhR : (extremalNumber n H : ℝ) ≤ 24*(n : ℝ)*(G.degree v : ℝ) := by
        exact_mod_cast hh
      rw [rpow_factor hnR.le ha] at hLowHalf
      nlinarith
    have hSum := sum_le_sum (s := S) (fun v _ => hmindeg v)
    simp only [sum_const,nsmul_eq_mul] at hSum
    have hCut := degree_cut_bound H G hFree S
    have hCutR : (∑ v ∈ S, (G.degree v : ℝ)) ≤ 2*(extremalNumber S.card H : ℝ)+
        (Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by exact_mod_cast hCut
    have hUS : (extremalNumber S.card H : ℝ) ≤ 2*c*(S.card : ℝ)^α+B*S.card := by
      have hm := mul_le_mul_of_nonneg_right (show c+η ≤ 2*c by linarith)
        (Real.rpow_nonneg hsR α)
      exact (hUpper S.card).trans (by linarith)
    have hcut : c/48*(S.card : ℝ)*(n : ℝ)^(α-1) ≤
        4*c*(S.card : ℝ)^α+2*B*S.card+(Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
      nlinarith only [hSum,hCutR,hUS]
    have hout := small_cut_bound ha hc hnR.le hsR hd.le hsmall hdpow hBsmall hcut
    have hle := mul_le_mul_of_nonneg_right (min_le_left (c/96) (c*k/2))
      (show 0 ≤ (S.card : ℝ)*(n : ℝ)^(α-1) by positivity)
    calc
      _ = κ*((S.card : ℝ)*(n : ℝ)^(α-1)) := by ring
      _ ≤ c/96*((S.card : ℝ)*(n : ℝ)^(α-1)) := hle
      _ ≤ _ := by simpa only [mul_assoc] using hout
  · have hCut := edges_le_parts_and_cut H G hFree S
    rw [hcard,hE] at hCut
    have hCutR : (extremalNumber n H : ℝ) ≤ (extremalNumber S.card H : ℝ)+
        (extremalNumber (n-S.card) H : ℝ)+(Nat.card (cross G (S : Set V)).edgeSet : ℝ) :=
      by exact_mod_cast hCut
    have hUS := hUpper S.card
    have hUT := hUpper (n-S.card)
    rw [Nat.cast_sub hsNat] at hUT
    have hcut : (c-η)*(n : ℝ)^α ≤ (c+η)*((S.card : ℝ)^α+((n : ℝ)-S.card)^α)+
        B*n+(Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
      nlinarith only [hLow',hCutR,hUS,hUT]
    have hout := large_cut_bound ha hc hnR.le hsR hhalf (le_of_not_ge hsmall)
      hη.le (show η = c*expansionConstant α*δ/8 from rfl) hBlarge hcut
    have hle := mul_le_mul_of_nonneg_right (min_le_right (c/96) (c*k/2))
      (show 0 ≤ (S.card : ℝ)*(n : ℝ)^(α-1) by positivity)
    change c*k/2*(S.card : ℝ)*(n : ℝ)^(α-1) ≤ _ at hout
    calc
      _ = κ*((S.card : ℝ)*(n : ℝ)^(α-1)) := by ring
      _ ≤ c*k/2*((S.card : ℝ)*(n : ℝ)^(α-1)) := hle
      _ ≤ _ := by simpa only [mul_assoc] using hout

/-- All conclusions hold on the SAME exact ordinary extremal host. In
particular full clone saturation is compatible with uniform expansion. -/
theorem exact_saturated_expanders {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ a b, H.Adj a b) {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N D : ℕ,
      ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
        N ≤ Fintype.card U ∧ H.Free J ∧
        Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
        (∀ v, D ≤ Nat.card (J.neighborSet v)) ∧
        (∀ v, Nat.card J.edgeSet ≤ 24*Fintype.card U*Nat.card (J.neighborSet v)) ∧
        (∀ v, SingleFold H J v) ∧
        ∀ S : Finset U, 2*S.card ≤ Fintype.card U →
          κ*S.card*(Fintype.card U : ℝ)^(α-1) ≤
            (Nat.card (cross J (S : Set U)).edgeSet : ℝ) := by
  obtain ⟨κ,hκ,hExp⟩ := eventually_expanding_exact H ha hc h
  obtain ⟨M,hM⟩ := eventually_atTop.mp hExp
  refine ⟨κ,hκ,?_⟩
  intro N D
  obtain ⟨U,instU,J,hnu,hf,hE,hdeg,hrelative,hfold⟩ :=
    Erdos713RelativeCloneSaturation.exact_relative_saturated_cofinal H hH hEdge ha ha2 hc h
      (max N M) D
  refine ⟨U,instU,J,(le_max_left _ _).trans hnu,hf,hE,hdeg,hrelative,hfold,?_⟩
  exact hM (Fintype.card U) ((le_max_right _ _).trans hnu) U J rfl hf hE hrelative

#print axioms degree_cut_bound
#print axioms linear_error_upper
#print axioms small_cut_bound
#print axioms large_cut_bound
#print axioms eventually_expanding_exact
#print axioms exact_saturated_expanders
end Erdos713RelativeExpansion
