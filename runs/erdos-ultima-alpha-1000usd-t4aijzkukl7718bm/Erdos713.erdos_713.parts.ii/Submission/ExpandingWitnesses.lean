import FormalConjecturesUtil
import Submission.UpToSharpDegree

/-! Expanding extremal witnesses from record maxima. -/

open Filter SimpleGraph Asymptotics Finset
namespace Erdos713Expansion
open Erdos713SwitchGluing

open scoped Classical in
lemma inside_edges_le {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hFree : H.Free G) (S : Finset V) :
    Nat.card (inside G (S : Set V)).edgeSet ≤ extremalNumber S.card H := by
  classical
  have heq : inside G (S : Set V) = (G.induce (S : Set V)).spanningCoe := by
    ext u v
    exact (Erdos713Regularization.restrict_adj G (S : Set V) u v).symm
  rw [heq]
  have hmap := card_edgeFinset_map (Function.Embedding.subtype (fun v => v ∈ (S : Set V)))
    (G.induce (S : Set V))
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hmap
  rw [hmap]
  have hf : H.Free (G.induce (S : Set V)) := fun h => hFree (h.trans ⟨Copy.induce G _⟩)
  have hc : Nat.card (S : Set V) = S.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe S
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card,hc] using
    card_edgeFinset_le_extremalNumber hf

lemma edges_le_parts_and_cut {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hFree : H.Free G) (S : Finset V) :
    Nat.card G.edgeSet ≤ extremalNumber S.card H + extremalNumber (Fintype.card V-S.card) H +
      Nat.card (cross G (S : Set V)).edgeSet := by
  classical
  have hRest : Erdos713Gluing.rest G (S : Set V) = inside G ((Sᶜ : Finset V) : Set V) := by
    ext u v
    simp [Erdos713Gluing.rest,inside]
  have hA := inside_edges_le H G hFree S
  have hB := inside_edges_le H G hFree Sᶜ
  rw [card_compl] at hB
  have hsplit := edge_split G (S : Set V)
  rw [hRest] at hsplit
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hsplit
  omega

lemma rpow_factor {x r : ℝ} (hx : 0 ≤ x) (hr : 1 < r) : x^r = x*x^(r-1) := by
  by_cases hx0 : x = 0
  · simp [hx0,Real.zero_rpow (by linarith : r ≠ 0)]
  · rw [Real.rpow_sub_one hx0]
    field_simp

noncomputable abbrev expansionConstant (r : ℝ) : ℝ := 1 - (1/2 : ℝ)^(r-1)

lemma expansionConstant_pos {r : ℝ} (hr : 1 < r) : 0 < expansionConstant r := by
  exact sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith))

lemma power_gap {n s r : ℝ} (hn : 0 ≤ n) (hs : 0 ≤ s) (hS : 2*s ≤ n) (hr : 1 < r) :
    expansionConstant r * s * n^(r-1) ≤ n^r-s^r-(n-s)^r := by
  have hns : 0 ≤ n-s := by linarith
  have hb := Real.rpow_le_rpow hns (show n-s ≤ n by linarith) (by linarith : 0 ≤ r-1)
  have ha := Real.rpow_le_rpow hs (show s ≤ (1/2 : ℝ)*n by linarith) (by linarith : 0 ≤ r-1)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1/2) hn] at ha
  have hA := mul_le_mul_of_nonneg_left ha hs
  have hB := mul_le_mul_of_nonneg_left hb hns
  rw [rpow_factor hn hr,rpow_factor hs hr,rpow_factor hns hr]
  dsimp only [expansionConstant]
  nlinarith

lemma record_cut_bound {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hFree : H.Free G) {r C : ℝ} (hr : 1 < r) (hC : 0 ≤ C)
    (hEdges : (Nat.card G.edgeSet : ℝ) = C*(Fintype.card V : ℝ)^r)
    (hUpper : ∀ j : ℕ, j ≤ Fintype.card V → (extremalNumber j H : ℝ) ≤ C*(j : ℝ)^r)
    (S : Finset V) (hS : 2*S.card ≤ Fintype.card V) :
    expansionConstant r * C * S.card * (Fintype.card V : ℝ)^(r-1) ≤
      (Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
  classical
  have hs : S.card ≤ Fintype.card V := card_le_univ S
  have he : (Nat.card G.edgeSet : ℝ) ≤ (extremalNumber S.card H : ℝ) +
      (extremalNumber (Fintype.card V-S.card) H : ℝ) +
        (Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
    exact_mod_cast edges_le_parts_and_cut H G hFree S
  have hA := hUpper S.card hs
  have hB := hUpper (Fintype.card V-S.card) (Nat.sub_le _ _)
  rw [Nat.cast_sub hs] at hB
  have hp := mul_le_mul_of_nonneg_left
    (power_gap (Nat.cast_nonneg (Fintype.card V)) (Nat.cast_nonneg S.card)
      (by exact_mod_cast hS) hr) hC
  rw [hEdges] at he
  nlinarith

lemma exists_record_expanders {W : Type*} (H : SimpleGraph W) {r : ℝ} (hr : 1 < r)
    (hLarge : ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      C * (n : ℝ)^r < (extremalNumber n H : ℝ)) :
    ∀ A : ℝ, 0 < A → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ C : ℝ, A < C ∧
      ∃ G : SimpleGraph (Fin n), H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H ∧
        (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r ∧
        ∀ S : Finset (Fin n), 2*S.card ≤ n →
          expansionConstant r * C * S.card * (n : ℝ)^(r-1) ≤
            (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ) := by
  intro A hA N
  obtain ⟨n,hn,hnpos,C,hC,hRecord,hUpper⟩ :=
    Erdos713RateRegularization.exists_record H (by linarith) hLarge N A hA
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hCpos : 0 < C := hA.trans hC
  have hepos : 0 < extremalNumber n H := by
    have hh : (0 : ℝ) < extremalNumber n H := by rw [hRecord]; positivity
    exact_mod_cast hh
  obtain ⟨G,hFree,hE⟩ := Erdos713SharpDegree.exists_extremal_of_pos H n hepos
  refine ⟨n,hn,hnpos,C,hC,G,hFree,hE,by rwa [hE],?_⟩
  intro S hS
  simpa only [Fintype.card_fin] using record_cut_bound H G hFree hr hCpos.le
    (by simpa only [Fintype.card_fin,hE] using hRecord)
    (by simpa only [Fintype.card_fin] using hUpper) S
    (by simpa only [Fintype.card_fin] using hS)

lemma of_rate {W : Type*} (H : SimpleGraph W) {α r : ℝ}
    (h : Erdos713Rate.HasRate H α) (hr : 1 < r) (hrα : r < α) :
    ∀ A : ℝ, 0 < A → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ C : ℝ, A < C ∧
      ∃ G : SimpleGraph (Fin n), H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H ∧
        (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r ∧
        ∀ S : Finset (Fin n), 2*S.card ≤ n →
          expansionConstant r * C * S.card * (n : ℝ)^(r-1) ≤
            (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ) :=
  exists_record_expanders H hr
    (Erdos713PowerCritical.exists_lower_above_smaller_power h hr.le hrα)


lemma linear_error_upper {W : Type*} (H : SimpleGraph W) {r c C : ℝ}
    (hC : 0 < C) (hcC : c < C)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c*(n : ℝ)^r)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, (extremalNumber n H : ℝ) ≤ C*(n : ℝ)^r + B*n := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((Erdos713SharpDegree.ratio_limit h).eventually_lt_const hcC)
  refine ⟨M, Nat.cast_nonneg _,?_⟩
  intro n
  by_cases hn : M ≤ n
  · by_cases hn0 : n = 0
    · subst n
      have he := Erdos713RateRegularization.extremal_sq_bound H 0
      have he0 : extremalNumber 0 H = 0 := by norm_num at he; exact he
      rw [he0,Nat.cast_zero]
      positivity
    have hnreal : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hnreal r)).mp (hM n hn)
    nlinarith [mul_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) hnreal.le]
  · have hnM : (n : ℝ) ≤ M := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hn))
    have he : (extremalNumber n H : ℝ) ≤ (n : ℝ)^2 := by
      exact_mod_cast Erdos713RateRegularization.extremal_sq_bound H n
    have hm := mul_le_mul_of_nonneg_right hnM (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith [mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg n) r)]

lemma rpow_increment_real {x y r : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hr : 1 ≤ r) :
    r*y^(r-1)*(x-y) ≤ x^r-y^r := by
  rcases hyx.eq_or_lt with h | h
  · rw [← h]
    simp
  · have hh := (convexOn_rpow hr).le_slope_of_hasDerivAt hy (hy.trans hyx) h
      (Real.hasDerivAt_rpow_const (Or.inr hr))
    simp only [slope_def_field] at hh
    exact (le_div_iff₀ (sub_pos.mpr h)).mp hh

lemma potential_record_cut_bound {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hFree : H.Free G) {r t C B : ℝ} (hr : 1 < r) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hEdges : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    (hRecord : ∀ j : ℕ, j ≤ Fintype.card V → (extremalNumber j H : ℝ)-t*(j : ℝ)^r ≤
      (extremalNumber (Fintype.card V) H : ℝ)-t*(Fintype.card V : ℝ)^r)
    (hUpper : ∀ j : ℕ, (extremalNumber j H : ℝ) ≤ C*(j : ℝ)^r+B*j)
    (S : Finset V) (hS : 2*S.card ≤ Fintype.card V) :
    (r*t-C)*(1/2 : ℝ)^(r-1)*S.card*(Fintype.card V : ℝ)^(r-1) - B*S.card ≤
      (Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
  have hs : S.card ≤ Fintype.card V := card_le_univ S
  have hnreal : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hsreal : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hsHalf : (S.card : ℝ) ≤ (1/2 : ℝ)*Fintype.card V := by
    have hh : (2 : ℝ)*S.card ≤ Fintype.card V := by exact_mod_cast hS
    linarith
  have hns : (0 : ℝ) ≤ (Fintype.card V : ℝ)-(S.card : ℝ) :=
    sub_nonneg.mpr (Nat.cast_le.mpr hs)
  have he : (Nat.card G.edgeSet : ℝ) ≤ (extremalNumber S.card H : ℝ) +
      (extremalNumber (Fintype.card V-S.card) H : ℝ) +
        (Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
    exact_mod_cast edges_le_parts_and_cut H G hFree S
  rw [hEdges] at he
  have hRec := hRecord (Fintype.card V-S.card) (Nat.sub_le _ _)
  rw [Nat.cast_sub hs] at hRec
  have hU := hUpper S.card
  have hInc := rpow_increment_real hns
    (show (Fintype.card V : ℝ)-S.card ≤ Fintype.card V by linarith) hr.le
  simp only [sub_sub_cancel] at hInc
  have hBase := Real.rpow_le_rpow (show (0 : ℝ) ≤ (1/2 : ℝ)*Fintype.card V by positivity)
    (show (1/2 : ℝ)*Fintype.card V ≤ (Fintype.card V : ℝ)-S.card by linarith)
    (show 0 ≤ r-1 by linarith)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1/2) hnreal] at hBase
  have hIncLower := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBase
    (show 0 ≤ r by linarith)) hsreal
  have hIncT := mul_le_mul_of_nonneg_left (hIncLower.trans hInc) ht
  have hSmall := Real.rpow_le_rpow hsreal hsHalf (show 0 ≤ r-1 by linarith)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1/2) hnreal] at hSmall
  have hSmallC := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSmall hsreal) hC
  rw [← rpow_factor hsreal hr] at hSmallC
  nlinarith

lemma exists_exact_expanders {W : Type*} (H : SimpleGraph W) {r c : ℝ}
    (hr : 1 < r) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c*(n : ℝ)^r)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
      ∃ G : SimpleGraph (Fin n), H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H ∧
        ∀ S : Finset (Fin n), 2*S.card ≤ n →
          κ * S.card * (n : ℝ)^(r-1) ≤
            (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ) := by
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hcr : c/r < c := (div_lt_self hc hr)
  obtain ⟨t,hct,htc⟩ := exists_between hcr
  have ht : 0 < t := (div_pos hc hrpos).trans hct
  have hctr : c < r*t := by have hh := (div_lt_iff₀ hrpos).mp hct; nlinarith
  obtain ⟨C,hcC,hCtr⟩ := exists_between hctr
  have hC : 0 < C := hc.trans hcC
  obtain ⟨B,hB,hUpper⟩ := linear_error_upper H hC hcC h
  let κ : ℝ := (r*t-C)*(1/2 : ℝ)^(r-1)/2
  have hκ : 0 < κ := div_pos (mul_pos (sub_pos.mpr hCtr)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2) _)) (by norm_num)
  have hTop : Tendsto (fun n : ℕ => κ*(n : ℝ)^(r-1)) atTop atTop :=
    Tendsto.const_mul_atTop hκ ((tendsto_rpow_atTop (by linarith : 0 < r-1)).comp
      tendsto_natCast_atTop_atTop)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hTop.eventually_ge_atTop B)
  refine ⟨κ,hκ,?_⟩
  intro N
  obtain ⟨n,hn,hnpos,hLow,hRecord⟩ :=
    Erdos713SharpDegree.exists_potential_record H hrpos ht htc h (max N M)
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_right _ _).trans hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hepos : 0 < extremalNumber n H := by
    have hh : (0 : ℝ) < extremalNumber n H :=
      (mul_pos ht (Real.rpow_pos_of_pos hnr r)).trans hLow
    exact_mod_cast hh
  obtain ⟨G,hFree,hE⟩ := Erdos713SharpDegree.exists_extremal_of_pos H n hepos
  refine ⟨n,hnN,hnpos,G,hFree,hE,?_⟩
  intro S hS
  have hh := potential_record_cut_bound H G hFree hr ht.le hC.le
    (by simpa only [Fintype.card_fin] using hE)
    (by simpa only [Fintype.card_fin] using hRecord) hUpper S
    (by simpa only [Fintype.card_fin] using hS)
  simp only [Fintype.card_fin] at hh
  have hErr := mul_le_mul_of_nonneg_right (hM n hnM) (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  dsimp only [κ] at hErr ⊢
  nlinarith


lemma exists_bipartite_all_cuts {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ B : SimpleGraph V, B ≤ G ∧ B.IsBipartite ∧
      Nat.card G.edgeSet ≤ 2*Nat.card B.edgeSet ∧
      ∀ S : Finset V, Nat.card (cross G (S : Set V)).edgeSet ≤
        2*Nat.card (cross B (S : Set V)).edgeSet := by
  classical
  obtain ⟨χ,_,hMax⟩ := exists_max_image (univ : Finset (V → Bool))
    (fun χ => Nat.card (Erdos713Cut.cut G χ).edgeSet) ⟨fun _ => false,mem_univ _⟩
  let B := Erdos713Cut.cut G χ
  have hHalf : Nat.card G.edgeSet ≤ 2*Nat.card B.edgeSet := by
    obtain ⟨K,hKG,hKBip,hKHalf⟩ := Erdos713Cut.exists_bipartite_half G
    obtain ⟨χK⟩ := hKBip
    let ψ : V → Bool := fun v => if χK v = 0 then false else true
    have hle : K ≤ Erdos713Cut.cut G ψ := by
      intro u v huv
      refine ⟨hKG huv,?_⟩
      have hh := χK.valid huv
      have hcu := (χK u).isLt
      have hcv := (χK v).isLt
      simp only [ψ]
      split_ifs with hu hv <;> simp_all
      exact hh (Fin.ext (by omega))
    have he := Finset.card_le_card (edgeFinset_mono hle)
    simp only [edgeFinset_card,Fintype.card_eq_nat_card] at he hKHalf
    have hm := hMax ψ (mem_univ _)
    dsimp only [B]
    omega
  refine ⟨B,Erdos713Cut.cut_le G χ,Erdos713Cut.cut_bipartite G χ,hHalf,?_⟩
  intro S
  let ψ : V → Bool := fun v => if v ∈ S then !(χ v) else χ v
  let F := Erdos713Cut.cut G ψ
  let C := cross G (S : Set V)
  let Q := cross B (S : Set V)
  let R := cross F (S : Set V)
  have hBQ : B.edgeFinset ∩ C.edgeFinset = Q.edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | hf u v => simp [B,C,Q,cross,Erdos713Cut.cut,and_left_comm,and_assoc]
  have hFR : F.edgeFinset ∩ C.edgeFinset = R.edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | hf u v => simp [F,C,R,cross,Erdos713Cut.cut,and_left_comm,and_assoc]
  have hOutside : B.edgeFinset \ C.edgeFinset = F.edgeFinset \ C.edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | hf u v =>
      by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
        cases hcu : χ u <;> cases hcv : χ v <;>
          simp [B,C,F,ψ,cross,Erdos713Cut.cut,hu,hv,hcu,hcv]
  have hUnion : C.edgeFinset = Q.edgeFinset ∪ R.edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | hf u v =>
      by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
        cases hcu : χ u <;> cases hcv : χ v <;>
          simp [B,C,F,Q,R,ψ,cross,Erdos713Cut.cut,hu,hv,hcu,hcv]
  have hDis : Disjoint Q.edgeFinset R.edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e he he'
    induction e using Sym2.inductionOn with
    | hf u v =>
      by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
        cases hcu : χ u <;> cases hcv : χ v <;>
          simp [B,F,Q,R,ψ,cross,Erdos713Cut.cut,hu,hv,hcu,hcv] at he he'
  have hCcard : C.edgeFinset.card = Q.edgeFinset.card + R.edgeFinset.card := by
    rw [hUnion,card_union_of_disjoint hDis]
  have hBcard := card_sdiff_add_card_inter B.edgeFinset C.edgeFinset
  have hFcard := card_sdiff_add_card_inter F.edgeFinset C.edgeFinset
  rw [hBQ,hOutside] at hBcard
  rw [hFR] at hFcard
  have hM := hMax ψ (mem_univ _)
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hBcard hFcard hCcard
  change Nat.card F.edgeSet ≤ Nat.card B.edgeSet at hM
  change Nat.card C.edgeSet ≤ 2*Nat.card Q.edgeSet
  omega

#print axioms exists_exact_expanders

#print axioms of_rate
end Erdos713Expansion
