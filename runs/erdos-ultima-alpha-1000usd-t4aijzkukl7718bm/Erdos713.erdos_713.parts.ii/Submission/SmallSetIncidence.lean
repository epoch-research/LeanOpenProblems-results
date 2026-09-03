import FormalConjecturesUtil
import Submission.RelativeExpansion

/-! Edges incident to small sets, derived from an extremal power upper bound.
No exact extremality or clone saturation is claimed after vertex deletion. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Topology
namespace Erdos713SmallSetIncidence
open Erdos713Cloning Erdos713SwitchGluing
set_option maxHeartbeats 2000000
variable {V W : Type*}

noncomputable def label [Fintype V] (s : ℕ) (v : V) : Fin (Fintype.card V/s+1) :=
  ⟨(Fintype.equivFin V v).val/s,
    Nat.lt_succ_of_le (Nat.div_le_div_right (Fintype.equivFin V v).isLt.le)⟩

open scoped Classical in
noncomputable def block [Fintype V] (s : ℕ) (j : Fin (Fintype.card V/s+1)) : Finset V :=
  univ.filter (fun v => label s v = j)

lemma mem_block [Fintype V] (s : ℕ) (v : V) : v ∈ block s (label s v) := by
  classical
  simp [block]

lemma block_card_le [Fintype V] {s : ℕ} (hs : 0 < s) (j : Fin (Fintype.card V/s+1)) :
    (block s j).card ≤ s := by
  classical
  let f : block s j → Fin s := fun v =>
    ⟨(Fintype.equivFin V v.val).val%s,Nat.mod_lt _ hs⟩
  have hinj : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    apply (Fintype.equivFin V).injective
    apply Fin.ext
    have hmod := congrArg Fin.val he
    have hv : (Fintype.equivFin V v.val).val/s = j.val :=
      congrArg Fin.val (mem_filter.mp v.property).2
    have hw : (Fintype.equivFin V w.val).val/s = j.val :=
      congrArg Fin.val (mem_filter.mp w.property).2
    have h1 := Nat.div_add_mod (Fintype.equivFin V v.val).val s
    have h2 := Nat.div_add_mod (Fintype.equivFin V w.val).val s
    change (Fintype.equivFin V v.val).val%s = (Fintype.equivFin V w.val).val%s at hmod
    rw [hv] at h1
    rw [hw] at h2
    omega
  simpa using Fintype.card_le_of_injective f hinj

/-- The spanning subgraph of edges having at least one endpoint in S. -/
def touch (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v ∈ S ∨ w ∈ S)
  symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless v h := G.loopless v h.1

lemma degree_mass_le_touch [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    (∑ v ∈ S, Nat.card (G.neighborSet v)) ≤ 2*Nat.card (touch G (S : Set V)).edgeSet := by
  classical
  have hdeg (v : V) (hv : v ∈ S) : G.degree v = (touch G (S : Set V)).degree v := by
    apply congrArg Finset.card
    ext w
    simp [mem_neighborFinset,touch,hv]
  have hh := sum_le_sum_of_subset (f := fun v => (touch G (S : Set V)).degree v) (subset_univ S)
  rw [sum_degrees_eq_twice_card_edges] at hh
  have he : (∑ v ∈ S, G.degree v) = ∑ v ∈ S, (touch G (S : Set V)).degree v := sum_congr rfl hdeg
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  simpa only [← he,edgeFinset_card] using hh

open scoped Classical in
lemma touch_cover [Fintype V] (G : SimpleGraph V) (S : Finset V) (s : ℕ) :
    Nat.card (touch G (S : Set V)).edgeSet ≤
      ∑ j : Fin (Fintype.card V/s+1), Nat.card (inside G ((S ∪ block s j : Finset V) : Set V)).edgeSet := by
  classical
  have hsub : (touch G (S : Set V)).edgeFinset ⊆
      univ.biUnion (fun j : Fin (Fintype.card V/s+1) =>
        (inside G ((S ∪ block s j : Finset V) : Set V)).edgeFinset) := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf v w =>
      have hvw : G.Adj v w ∧ (v ∈ S ∨ w ∈ S) := by simpa [touch] using he
      rcases hvw.2 with hv | hw
      · apply mem_biUnion.mpr
        refine ⟨label s w,mem_univ _,?_⟩
        simpa only [mem_edgeFinset,inside] using
          (show G.Adj v w ∧ v ∈ S ∪ block s (label s w) ∧ w ∈ S ∪ block s (label s w) from
            ⟨hvw.1,mem_union_left _ hv,mem_union_right _ (mem_block s w)⟩)
      · apply mem_biUnion.mpr
        refine ⟨label s v,mem_univ _,?_⟩
        simpa only [mem_edgeFinset,inside] using
          (show G.Adj v w ∧ v ∈ S ∪ block s (label s v) ∧ w ∈ S ∪ block s (label s v) from
            ⟨hvw.1,mem_union_right _ (mem_block s v),mem_union_left _ hw⟩)
  have hh := (card_le_card hsub).trans card_biUnion_le
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hh

lemma touch_block_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (hFree : H.Free G)
    {α C B : ℝ} (ha : 0 ≤ α) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hU : ∀ m : ℕ, (extremalNumber m H : ℝ) ≤ C*(m : ℝ)^α+B*m)
    (S : Finset V) (hs : 0 < S.card) :
    (Nat.card (touch G (S : Set V)).edgeSet : ℝ) ≤
      (Fintype.card V/S.card+1 : ℕ)*(C*(2*(S.card : ℝ))^α+2*B*S.card) := by
  classical
  have hj (j : Fin (Fintype.card V/S.card+1)) :
      (Nat.card (inside G ((S ∪ block S.card j : Finset V) : Set V)).edgeSet : ℝ) ≤
        C*(2*(S.card : ℝ))^α+2*B*S.card := by
    have hsmall : (S ∪ block S.card j).card ≤ 2*S.card :=
      (card_union_le _ _).trans (by have hh := block_card_le hs j; omega)
    have hsmallR : ((S ∪ block S.card j).card : ℝ) ≤ 2*S.card := by exact_mod_cast hsmall
    have hp := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hsmallR ha) hC
    have hb := mul_le_mul_of_nonneg_left hsmallR hB
    have he : (Nat.card (inside G ((S ∪ block S.card j : Finset V) : Set V)).edgeSet : ℝ) ≤
        (extremalNumber (S ∪ block S.card j).card H : ℝ) :=
      by exact_mod_cast inside_edges_le H G hFree (S ∪ block S.card j)
    nlinarith only [he,hU (S ∪ block S.card j).card,hp,hb]
  have hh : (Nat.card (touch G (S : Set V)).edgeSet : ℝ) ≤
      ∑ j : Fin (Fintype.card V/S.card+1),
        (Nat.card (inside G ((S ∪ block S.card j : Finset V) : Set V)).edgeSet : ℝ) :=
    by exact_mod_cast touch_cover G S S.card
  have hb := sum_le_sum (s := (univ : Finset (Fin (Fintype.card V/S.card+1)))) (fun j _ => hj j)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  exact hh.trans hb

lemma touch_power_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (hFree : H.Free G)
    {α C B : ℝ} (ha : 1 < α) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hU : ∀ m : ℕ, (extremalNumber m H : ℝ) ≤ C*(m : ℝ)^α+B*m)
    (S : Finset V) :
    (Nat.card (touch G (S : Set V)).edgeSet : ℝ) ≤
      2*C*(2 : ℝ)^α*Fintype.card V*(S.card : ℝ)^(α-1)+4*B*Fintype.card V := by
  classical
  by_cases hs0 : S.card = 0
  · have hS : S = ∅ := card_eq_zero.mp hs0
    subst S
    have ht : touch G (∅ : Set V) = ⊥ := by ext v w; simp [touch]
    simp only [coe_empty,ht]
    have he : Nat.card ((⊥ : SimpleGraph V).edgeSet) = 0 := by simp
    rw [he,Nat.cast_zero]
    positivity
  have hs : 0 < S.card := Nat.pos_of_ne_zero hs0
  have hsR : (0 : ℝ) < S.card := by exact_mod_cast hs
  have hnum : (Fintype.card V/S.card+1)*S.card ≤ 2*Fintype.card V := by
    have h1 := Nat.div_mul_le_self (Fintype.card V) S.card
    have h2 := card_le_univ S
    nlinarith
  have hnumR : ((Fintype.card V/S.card+1 : ℕ) : ℝ)*S.card ≤ 2*Fintype.card V := by
    exact_mod_cast hnum
  have he := touch_block_bound H G hFree (zero_lt_one.trans ha).le hC hB hU S hs
  have hfac : C*(2*(S.card : ℝ))^α+2*B*S.card =
      (S.card : ℝ)*(C*(2 : ℝ)^α*(S.card : ℝ)^(α-1)+2*B) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hsR.le,rpow_factor hsR.le ha]
    ring
  rw [hfac] at he
  have hm := mul_le_mul_of_nonneg_right hnumR
    (show 0 ≤ C*(2 : ℝ)^α*(S.card : ℝ)^(α-1)+2*B by positivity)
  nlinarith only [he,hm]

lemma degree_mass_power_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (hFree : H.Free G)
    {α C B : ℝ} (ha : 1 < α) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hU : ∀ m : ℕ, (extremalNumber m H : ℝ) ≤ C*(m : ℝ)^α+B*m)
    (S : Finset V) :
    (∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ)) ≤
      4*C*(2 : ℝ)^α*Fintype.card V*(S.card : ℝ)^(α-1)+8*B*Fintype.card V := by
  have he := touch_power_bound H G hFree ha hC hB hU S
  have hs : (∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ)) ≤
      2*(Nat.card (touch G (S : Set V)).edgeSet : ℝ) := by
    exact_mod_cast degree_mass_le_touch G S
  linarith

#print axioms block_card_le
#print axioms degree_mass_le_touch
#print axioms touch_cover
#print axioms touch_power_bound
#print axioms degree_mass_power_bound
end Erdos713SmallSetIncidence
