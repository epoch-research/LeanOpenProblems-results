import FormalConjecturesUtil
import Submission.QuantitativeExpanderPruning

/-! Nearly full-density almost-regular expanding restrictions of exact
extremal hosts. Neither exact extremality nor fold survival is claimed
for the restriction. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713NearOptimalExpanders
open Erdos713QuantitativeExpanderPruning Erdos713UniformIncidence Erdos713Cloning
open Erdos713SwitchGluing
set_option maxHeartbeats 2000000
variable {V W : Type*}

/-- Restricting further cannot increase the degree of a retained vertex. -/
lemma induce_neighbor_antitone [Fintype V] (G : SimpleGraph V) (S T : Set V)
    (hTS : T ⊆ S) (v : T) :
    Nat.card ((G.induce T).neighborSet v) ≤
      Nat.card ((G.induce S).neighborSet ⟨v.val,hTS v.property⟩) := by
  let f : (G.induce T).neighborSet v → (G.induce S).neighborSet ⟨v.val,hTS v.property⟩ :=
    fun w => ⟨⟨w.val.val,hTS w.val.property⟩,w.property⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (G.induce S).neighborSet ⟨v.val,hTS v.property⟩ => z.val.val) he
  exact Nat.card_le_card_of_injective f hf

lemma restriction_expansion [Fintype V] (G : SimpleGraph V) (U : Finset V) (h : ℝ)
    (hExp : ∀ A : Finset V, A ⊆ U → 2*A.card ≤ U.card →
      h*A.card ≤ (Nat.card (cross (inside G (U : Set V)) (A : Set V)).edgeSet : ℝ)) :
    ∀ A : Finset U, 2*A.card ≤ Fintype.card U →
      h*A.card ≤ (Nat.card (cross (G.induce (U : Set V)) (A : Set U)).edgeSet : ℝ) := by
  classical
  intro A hA
  let S := A.image Subtype.val
  have hScard : S.card = A.card := card_image_of_injective A Subtype.val_injective
  have hSsub : S ⊆ U := by
    intro v hv
    obtain ⟨w,_,rfl⟩ := mem_image.mp hv
    exact w.property
  have hShalf : 2*S.card ≤ U.card := by simpa only [hScard,Fintype.card_coe] using hA
  have hh := hExp S hSsub hShalf
  rw [cut_induce_image]
  simpa only [hScard] using hh

open scoped Classical in
/-- One upper-degree constant works for all sufficiently large H-free
expanders. The retained graph loses at most eta*n vertices and eta*n^alpha
edges, while keeping one quarter of the original expansion coefficient. -/
theorem regularize_expanders (H : SimpleGraph W) {α c κ η : ℝ}
    (ha : 1 < α) (hc : 0 < c) (hk : 0 < κ) (hη : 0 < η)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V = n → H.Free G →
        (∀ A : Finset V, 2*A.card ≤ n →
          κ*A.card*(n : ℝ)^(α-1) ≤ (Nat.card (cross G (A : Set V)).edgeSet : ℝ)) →
        ∃ T : Finset V,
          (T.card : ℝ) ≤ η*n ∧
          (Nat.card G.edgeSet : ℝ) ≤
            (Nat.card (G.induce ((Tᶜ : Finset V) : Set V)).edgeSet : ℝ)+η*(n : ℝ)^α ∧
          (∀ v : ↥(Tᶜ), (Nat.card ((G.induce ((Tᶜ : Finset V) : Set V)).neighborSet v) : ℝ)
            ≤ D*(n : ℝ)^(α-1)) ∧
          ∀ A : Finset ↥(Tᶜ), 2*A.card ≤ Fintype.card ↥(Tᶜ) →
            κ/4*A.card*(n : ℝ)^(α-1) ≤
              (Nat.card (cross (G.induce ((Tᶜ : Finset V) : Set V)) (A : Set ↥(Tᶜ))).edgeSet : ℝ) := by
  classical
  obtain ⟨δ,hδ,hMass⟩ := small_set_mass H ha hc h hη
  let δ' := min δ η
  have hd' : 0 < δ' := lt_min hδ hη
  let ε := min (κ/32) (κ*δ'/(2*(κ+2)))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεk : ε ≤ κ/32 := min_le_left _ _
  have hεδ : ε*(κ+2) ≤ κ*δ'/2 := by
    have hh := min_le_right (κ/32) (κ*δ'/(2*(κ+2)))
    have hk2 : 0 < 2*(κ+2) := by positivity
    have hz := (le_div_iff₀ hk2).mp hh
    change ε*(2*(κ+2)) ≤ κ*δ' at hz
    nlinarith
  obtain ⟨D,hD,hPrune⟩ := Erdos713NearOptimalPruning.prune_high_degrees H ha hc h hε
  refine ⟨D,hD,?_⟩
  filter_upwards [hMass,hPrune,eventually_gt_atTop (0 : ℕ)] with n hmass hprune hn
  intro V instV G hcard hf hExp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ)^(α-1) := Real.rpow_pos_of_pos hnR _
  have hFac := rpow_factor hnR.le ha
  obtain ⟨S,hScard,hSdeg,hLoss,hSF,hUpper⟩ := hprune V G hcard hf
  let h₀ := κ*(n : ℝ)^(α-1)
  have hh₀ : 0 < h₀ := by dsimp [h₀]; positivity
  have hExp' (A : Finset V) (hA : 2*A.card ≤ Fintype.card V) :
      h₀*A.card ≤ (Nat.card (cross G (A : Set V)).edgeSet : ℝ) := by
    have hh := hExp A (by simpa only [hcard] using hA)
    dsimp only [h₀]
    nlinarith only [hh]
  have hSmall : ε*(n : ℝ)^α ≤ h₀*(Fintype.card V : ℝ)/16 := by
    rw [hcard,hFac]
    have hh := mul_le_mul_of_nonneg_right hεk (show 0 ≤ (n : ℝ)*(n : ℝ)^(α-1) by positivity)
    dsimp only [h₀]
    nlinarith [mul_nonneg hk.le (mul_nonneg hnR.le hp.le)]
  obtain ⟨T,hST,hTBound,hTCuts⟩ := prune_vertex_expander G S hh₀ hExp' hLoss hSmall
  have hTsmall : (T.card : ℝ) ≤ δ'*n := by
    rw [hFac] at hTBound
    have hs := mul_le_mul_of_nonneg_left hScard hh₀.le
    have he := mul_le_mul_of_nonneg_right hεδ (show 0 ≤ (n : ℝ)*(n : ℝ)^(α-1) by positivity)
    have hpos := mul_nonneg (mul_nonneg hk.le hd'.le) (mul_nonneg hnR.le hp.le)
    have hh : h₀*T.card ≤ h₀*(δ'*n) := by
      dsimp only [h₀] at *
      nlinarith only [hTBound,hs,he,hpos]
    exact (mul_le_mul_iff_right₀ hh₀).mp hh
  have hTη : (T.card : ℝ) ≤ η*n := hTsmall.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hnR.le)
  have hTδ : (T.card : ℝ) ≤ δ*n := hTsmall.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hnR.le)
  have hmassT := hmass V G hcard hf T hTδ
  have hDel : (Nat.card G.edgeSet : ℝ) ≤
      (Nat.card (G.induce ((Tᶜ : Finset V) : Set V)).edgeSet : ℝ)+η*(n : ℝ)^α := by
    have hh : (Nat.card G.edgeSet : ℝ) ≤ (Nat.card (G.induce (T : Set V)ᶜ).edgeSet : ℝ)+
        ∑ v ∈ T, (Nat.card (G.neighborSet v) : ℝ) := by
      exact_mod_cast edges_le_induce_compl_add_degree G T
    rw [Finset.coe_compl T]
    exact hh.trans (add_le_add le_rfl hmassT)
  have hTS : ((Tᶜ : Finset V) : Set V) ⊆ (S : Set V)ᶜ := by
    intro v hv
    exact fun hvs => (mem_compl.mp hv) (hST hvs)
  refine ⟨T,hTη,hDel,?_,?_⟩
  · intro v
    exact (Nat.cast_le.mpr (induce_neighbor_antitone G _ _ hTS v)).trans
      (hUpper ⟨v.val,hTS v.property⟩)
  · have hCut := restriction_expansion G Tᶜ (h₀/4) (fun A hAT hA =>
      hTCuts A hAT (by simpa only [card_compl] using hA))
    intro A hA
    have hh := hCut A hA
    dsimp only [h₀] at hh
    nlinarith only [hh]

/-- The leading coefficient can be made arbitrarily close to the exact
extremal coefficient c while the lower degree and expansion constants
remain fixed. The upper-degree constant may depend on the accuracy. -/
theorem near_full_density {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ v w, H.Adj v w) {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ a : ℝ, 0 < a ∧ ∀ ε : ℝ, 0 < ε → ε < c →
      ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ,
        ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
          N ≤ Fintype.card U ∧ 2 ≤ Fintype.card U ∧ H.Free J ∧
          (c-ε)*(Fintype.card U : ℝ)^α ≤ (Nat.card J.edgeSet : ℝ) ∧
          (∀ v, a*(Fintype.card U : ℝ)^(α-1) ≤ (Nat.card (J.neighborSet v) : ℝ) ∧
            (Nat.card (J.neighborSet v) : ℝ) ≤ D*(Fintype.card U : ℝ)^(α-1)) ∧
          ∀ A : Finset U, 2*A.card ≤ Fintype.card U →
            a*A.card*(Fintype.card U : ℝ)^(α-1) ≤
              (Nat.card (cross J (A : Set U)).edgeSet : ℝ) := by
  classical
  obtain ⟨κ,hκ,hWitness⟩ := Erdos713RelativeExpansion.exact_saturated_expanders
    H hH hEdge ha ha2 hc h
  refine ⟨κ/4,by positivity,?_⟩
  intro ε hε hεc
  let η := min (ε/4) (1/4 : ℝ)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε/4 := min_le_left _ _
  have hη1 : η ≤ 1/4 := min_le_right _ _
  obtain ⟨D,hD,hReg⟩ := regularize_expanders H ha hc hκ hη h
  obtain ⟨M,hM⟩ := eventually_atTop.mp hReg
  have hLow : ∀ᶠ n : ℕ in atTop, (c-ε/2)*(n : ℝ)^α ≤ (extremalNumber n H : ℝ) := by
    filter_upwards [(Erdos713FutureRecords.ratio_limit h).eventually_const_lt (show c-ε/2 < c by linarith),
      eventually_gt_atTop (0 : ℕ)] with n hn hnp
    exact ((lt_div_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hnp : (0 : ℝ) < n) α)).mp hn).le
  obtain ⟨L,hL⟩ := eventually_atTop.mp hLow
  refine ⟨D*(2 : ℝ)^(α-1),by positivity,?_⟩
  intro N
  obtain ⟨V,instV,G,hLarge,hFree,hE,hDeg,hRel,hFold,hExp⟩ :=
    hWitness (max (max (2*N) 4) (max M L)) 0
  let n := Fintype.card V
  have hnN : 2*N ≤ n := by dsimp [n]; omega
  have hn4 : 4 ≤ n := by dsimp [n]; omega
  have hnM : M ≤ n := by dsimp [n]; omega
  have hnL : L ≤ n := by dsimp [n]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨T,hTsmall,hLoss,hMax,hCuts⟩ := hM n hnM V G rfl hFree hExp
  let U := (Tᶜ : Finset V)
  let J := G.induce (U : Set V)
  have hCard : Fintype.card U = n-T.card := by simp only [U,Fintype.card_coe,card_compl]; rfl
  have hTquarter : (T.card : ℝ) ≤ (n : ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right hη1 hnR.le
    nlinarith
  have hTnat : 4*T.card ≤ n := by exact_mod_cast (show (4 : ℝ)*T.card ≤ n by linarith)
  have hmN : N ≤ Fintype.card U := by rw [hCard]; omega
  have hmtwo : 2 ≤ Fintype.card U := by rw [hCard]; omega
  have hmle : Fintype.card U ≤ n := by rw [hCard]; omega
  have hnle : n ≤ 2*Fintype.card U := by rw [hCard]; omega
  have hmR : (0 : ℝ) < Fintype.card U := by exact_mod_cast (by omega : 0 < Fintype.card U)
  have hPow : (Fintype.card U : ℝ)^(α-1) ≤ (n : ℝ)^(α-1) :=
    Real.rpow_le_rpow hmR.le (by exact_mod_cast hmle) (by linarith)
  have hPow' : (n : ℝ)^(α-1) ≤ (2 : ℝ)^(α-1)*(Fintype.card U : ℝ)^(α-1) := by
    have hh := Real.rpow_le_rpow hnR.le (show (n : ℝ) ≤ 2*Fintype.card U by exact_mod_cast hnle)
      (show 0 ≤ α-1 by linarith)
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hmR.le] at hh
  have hDenseOld : (c-ε)*(n : ℝ)^α ≤ (Nat.card J.edgeSet : ℝ) := by
    have hlow := hL n hnL
    change (Nat.card G.edgeSet : ℝ) ≤ (Nat.card J.edgeSet : ℝ)+η*(n : ℝ)^α at hLoss
    rw [hE] at hLoss
    change (extremalNumber n H : ℝ) ≤ (Nat.card J.edgeSet : ℝ)+η*(n : ℝ)^α at hLoss
    have herr := mul_le_mul_of_nonneg_right hηε (Real.rpow_nonneg hnR.le α)
    nlinarith only [hlow,hLoss,herr,mul_nonneg hε.le (Real.rpow_nonneg hnR.le α)]
  have hDense : (c-ε)*(Fintype.card U : ℝ)^α ≤ (Nat.card J.edgeSet : ℝ) :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hmR.le (by exact_mod_cast hmle) (by linarith : 0 ≤ α))
      (by linarith : 0 ≤ c-ε)).trans hDenseOld
  have hJFree : H.Free J := fun hQ => hFree (hQ.trans ⟨Copy.induce G _⟩)
  have hCut (A : Finset U) (hA : 2*A.card ≤ Fintype.card U) :
      κ/4*A.card*(Fintype.card U : ℝ)^(α-1) ≤
        (Nat.card (cross J (A : Set U)).edgeSet : ℝ) := by
    have hh := hCuts A hA
    have hm := mul_le_mul_of_nonneg_left hPow (show 0 ≤ κ/4*A.card by positivity)
    exact hm.trans hh
  refine ⟨U,inferInstance,J,hmN,hmtwo,hJFree,hDense,?_,hCut⟩
  intro v
  constructor
  · have hh := hCut {v} (by simpa only [card_singleton] using hmtwo)
    simpa only [card_singleton,Nat.cast_one,mul_one,coe_singleton,cross_singleton_card] using hh
  · have hh := hMax v
    have hm := mul_le_mul_of_nonneg_left hPow' hD.le
    change (Nat.card (J.neighborSet v) : ℝ) ≤ _ at hh
    calc
      _ ≤ D*(n : ℝ)^(α-1) := hh
      _ ≤ D*((2 : ℝ)^(α-1)*(Fintype.card U : ℝ)^(α-1)) := hm
      _ = _ := by ring

#print axioms induce_neighbor_antitone
#print axioms restriction_expansion
#print axioms regularize_expanders
#print axioms near_full_density
end Erdos713NearOptimalExpanders
