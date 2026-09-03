import FormalConjecturesUtil
import Submission.CloneMass

/-! Two-sided power records give exact extremal witnesses with minimum degree,
cut expansion, and positive cloning-obstruction mass on the same graph. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713Cloning
open Erdos713SwitchGluing

open scoped Classical in
lemma inside_edges_le {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (hFree : H.Free G) (S : Finset V) :
    Nat.card (inside G (S : Set V)).edgeSet ≤ extremalNumber S.card H := by
  classical
  have heq : inside G (S : Set V) = (G.induce (S : Set V)).spanningCoe := by
    ext u v
    constructor
    · rintro ⟨h,hu,hv⟩
      exact ⟨⟨u,hu⟩,⟨v,hv⟩,h,rfl,rfl⟩
    · rintro ⟨a,b,h,rfl,rfl⟩
      exact ⟨h,a.property,b.property⟩
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


lemma degree_lower_of_record {W : Type*} (H : SimpleGraph W) {n : ℕ}
    (G : SimpleGraph (Fin n)) (hfree : H.Free G) (he : Nat.card G.edgeSet = extremalNumber n H)
    {r C : ℝ} (hEq : (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r)
    (hUpper : ∀ j : ℕ, j ≤ n → (extremalNumber j H : ℝ) ≤ C*(j : ℝ)^r) (v : Fin n) :
    C*((n : ℝ)^r-((n-1 : ℕ) : ℝ)^r) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
  classical
  have hDel := card_edgeFinset_deleteIncidenceSet_le_extremalNumber hfree v
  rw [card_edgeFinset_deleteIncidenceSet] at hDel
  have hNat : G.edgeFinset.card ≤ extremalNumber (n-1) H + G.degree v := by
    simp only [Fintype.card_fin] at hDel
    have hh := G.degree_le_card_edgeFinset v
    omega
  simp only [edgeFinset_card,← card_neighborSet_eq_degree,Fintype.card_eq_nat_card,he] at hNat
  have hReal : (extremalNumber n H : ℝ) ≤ (extremalNumber (n-1) H : ℝ) +
      (Nat.card (G.neighborSet v) : ℝ) := by exact_mod_cast hNat
  have hh := hUpper (n-1) (Nat.sub_le _ _)
  rw [he] at hEq
  nlinarith

lemma extremal_zero {W : Type*} (H : SimpleGraph W) : extremalNumber 0 H = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  rw [← Fintype.card_fin 0,extremalNumber_le_iff]
  intro G _ _
  have hh := G.card_edgeFinset_le_card_choose_two
  simpa using hh

lemma joint_of_asymptotic {W : Type*} (H : SimpleGraph W) {α c r s : ℝ}
    (hr : 1 < r) (hra : r < α) (has : α < s) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ C : ℝ, 0 < C ∧ ∃ G : SimpleGraph (Fin n),
      H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H ∧
      (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r ∧
      (∀ j : ℕ, j ≤ n → (extremalNumber j H : ℝ) ≤ C*(j : ℝ)^r) ∧
      (∀ v, C*((n : ℝ)^r-((n-1 : ℕ) : ℝ)^r) ≤ (Nat.card (G.neighborSet v) : ℝ)) ∧
      (∀ S : Finset (Fin n), 2*S.card ≤ n →
        expansionConstant r*C*S.card*(n : ℝ)^(r-1) ≤
          (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ)) ∧
      ∃ B : Finset (Fin n), (∀ v ∈ B, SingleFold H G v) ∧
        (2-s)*(Nat.card G.edgeSet : ℝ) ≤ ∑ v ∈ B, (Nat.card (G.neighborSet v) : ℝ) := by
  obtain ⟨n,hn,hnp,hpos,hpast,hinc⟩ :=
    Erdos713FutureRecords.exists_small_increment_with_past (by linarith) hc hra has h N
  have hnpR : (0 : ℝ) < n := by exact_mod_cast hnp
  have hpos' : 0 < extremalNumber n H := by exact_mod_cast hpos
  let C : ℝ := (extremalNumber n H : ℝ)/(n : ℝ)^r
  have hC : 0 < C := div_pos hpos (Real.rpow_pos_of_pos hnpR r)
  have hEq : (extremalNumber n H : ℝ) = C*(n : ℝ)^r :=
    (div_mul_cancel₀ _ (Real.rpow_pos_of_pos hnpR r).ne').symm
  have hUpper : ∀ j : ℕ, j ≤ n → (extremalNumber j H : ℝ) ≤ C*(j : ℝ)^r := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [extremal_zero,Real.zero_rpow (by linarith : r ≠ 0)]
    · exact (div_le_iff₀ (Real.rpow_pos_of_pos (show (0 : ℝ) < j by exact_mod_cast Nat.pos_of_ne_zero hj0) r)).mp
        (hpast j (Nat.pos_of_ne_zero hj0) hj)
  obtain ⟨G,hfree,he⟩ := exists_extremal_of_pos H n hpos'
  have hEqG : (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r := by rwa [he]
  refine ⟨n,hn,hnp,C,hC,G,hfree,he,hEqG,hUpper,
    degree_lower_of_record H G hfree he hEqG hUpper,?_,
    mass_bound H G hfree he (by linarith) hinc⟩
  intro S hS
  simpa only [Fintype.card_fin] using record_cut_bound H G hfree hr hC.le
    (by simpa only [Fintype.card_fin] using hEqG)
    (by simpa only [Fintype.card_fin] using hUpper) S
    (by simpa only [Fintype.card_fin] using hS)

#print axioms joint_of_asymptotic
end Erdos713Cloning
