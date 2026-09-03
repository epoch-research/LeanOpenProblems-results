import Submission.LowCountCritical
import Submission.CycleFactors

/-!
Nested edge-disjoint cycles impose an extra degree-slack condition in
count-critical graphs. This is a restricted structural consequence, not a
uniform bound for arbitrary critical graphs or a settlement of Erdős 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.CriticalNestedCycles
open CountCritical CycleNumberSubmodularity FractionalCycles FractionalEnvelope
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 1000000

lemma cycle_le_residual (C J : G.Subgraph) (hd : Disjoint C.edgeSet J.edgeSet) :
    C.spanningCoe ≤ G \ J.spanningCoe := by
  intro x y h
  exact ⟨C.adj_sub h,fun hj => Set.disjoint_left.mp hd
    (show s(x,y) ∈ C.edgeSet from h) (show s(x,y) ∈ J.edgeSet from hj)⟩

lemma cycle_degree (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) (v : V) :
    C.spanningCoe.degree v = if v ∈ C.verts then 2 else 0 := by
  rw [Subgraph.degree_spanningCoe]
  exact cycle_piece_degree G ⟨C,hc⟩ v

/-- When all vertices of C have degree four, deleting an edge-disjoint
cycle through them removes every edge leaving C. -/
lemma nested_residual_separated (C J : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hj : J.coe.Connected ∧ J.coe.IsRegularOfDegree 2)
    (hd : Disjoint C.edgeSet J.edgeSet) (hsub : C.verts ⊆ J.verts)
    (hfour : ∀ v ∈ C.verts, G.degree v = 4) :
    Disjoint C.spanningCoe.support ((G \ J.spanningCoe) \ C.spanningCoe).support := by
  apply Set.disjoint_left.mpr
  rintro v ⟨w,hw⟩ hv
  have hvC := C.edge_vert hw
  have hvJ := hsub hvC
  have hdeg := degree_sdiff_of_le (cycle_le_residual C J hd) v
  have hA := degree_sdiff_of_le J.spanningCoe_le v
  have hC := cycle_degree C hc v
  have hJ := cycle_degree J hj v
  rw [if_pos hvC] at hC
  rw [if_pos hvJ] at hJ
  have h4 := hfour v hvC
  have hp := (((G \ J.spanningCoe) \ C.spanningCoe).degree_pos_iff_mem_support v).mpr hv
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdeg hA hC hJ h4 hp
  omega

lemma residual_degree_of_outer_avoids (C J : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hj : J.coe.Connected ∧ J.coe.IsRegularOfDegree 2)
    (hd : Disjoint C.edgeSet J.edgeSet) (hsub : C.verts ⊆ J.verts)
    {v : V} (hv : v ∉ J.verts) :
    ((G \ J.spanningCoe) \ C.spanningCoe).degree v = G.degree v := by
  have hvC : v ∉ C.verts := fun h => hv (hsub h)
  have hR := degree_sdiff_of_le (cycle_le_residual C J hd) v
  have hA := degree_sdiff_of_le J.spanningCoe_le v
  have hC := cycle_degree C hc v
  have hJ := cycle_degree J hj v
  rw [if_neg hvC] at hC
  rw [if_neg hv] at hJ
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hR hA hC hJ ⊢
  omega

/-- The separate inner cycle costs one piece in addition to the degree
lower bound at any vertex missed by the outer cycle. -/
lemma degree_add_four_le_twice_count {k : ℕ} (hG : IsCountCritical k G)
    (C J : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hj : J.coe.Connected ∧ J.coe.IsRegularOfDegree 2)
    (hd : Disjoint C.edgeSet J.edgeSet) (hsub : C.verts ⊆ J.verts)
    (hfour : ∀ v ∈ C.verts, G.degree v = 4)
    {v : V} (hv : v ∉ J.verts) : G.degree v + 4 ≤ 2*k := by
  let A := G \ J.spanningCoe
  let R := A \ C.spanningCoe
  have heA : ∀ w, Even (A.degree w) := by
    intro w
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using residual_even hG.1 J hj w
  have heC : ∀ w, Even (C.spanningCoe.degree w) := by
    intro w
    have hh := cycle_degree C hc w
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
    rw [hh]
    split_ifs <;> decide
  have hCA : C.spanningCoe ≤ A := cycle_le_residual C J hd
  have heR : ∀ w, Even (R.degree w) := by
    intro w
    have hh := degree_sdiff_of_le hCA w
    have ha := heA w
    have hc := heC w
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ha hc ⊢
    change Even (Nat.card (R.neighborSet w))
    rw [hh]
    obtain ⟨a,ha⟩ := ha
    obtain ⟨b,hb⟩ := hc
    exact ⟨a-b,by omega⟩
  have hcover : C.spanningCoe.edgeSet ∪ R.edgeSet = A.edgeSet := by
    rw [show R.edgeSet = A.edgeSet \ C.spanningCoe.edgeSet from edgeSet_sdiff A C.spanningCoe]
    exact Set.union_diff_cancel (edgeSet_mono hCA)
  have hover : (C.spanningCoe.support ∩ R.support).ncard ≤ 1 := by
    rw [Set.disjoint_iff_inter_eq_empty.mp (nested_residual_separated C J hc hj hd hsub hfour)]
    simp
  have hadd := FractionalSeparated.optimum_add hcover hover (by
    intro w
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heC w) (by
    intro w
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heR w)
  have hcycle := CycleFactors.optimum_cycle (G := G) (⟨C,hc⟩ : CyclePiece G)
  rw [hcycle] at hadd
  have hdeg := degree_le_twice_optimum R (by
    intro w
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heR w) v
  have hsame : R.degree v = G.degree v := residual_degree_of_outer_avoids C J hc hj hd hsub hv
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hsame hdeg
  rw [hsame] at hdeg
  have hupper := optimum_le_number A (by
    intro w
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heA w)
  have hn : cycleNumber A + 1 = k := hG.residual_number J hj
  have hn' : (cycleNumber A : ℝ) + 1 = k := by exact_mod_cast hn
  have hh : (G.degree v : ℝ) + 4 ≤ 2*(k : ℝ) := by
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    linarith
  exact_mod_cast hh

/-- At count at most three, if all supported vertices have degree four,
the outer member of any nested edge-disjoint cycle pair is spanning on
support. -/
lemma outer_covers_support_of_count_le_three {k : ℕ}
    (hG : IsCountCritical k G) (hk : k ≤ 3)
    (hfour : ∀ v ∈ G.support, G.degree v = 4)
    (C J : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hj : J.coe.Connected ∧ J.coe.IsRegularOfDegree 2)
    (hd : Disjoint C.edgeSet J.edgeSet) (hsub : C.verts ⊆ J.verts) :
    G.support ⊆ J.verts := by
  intro v hv
  by_contra hn
  have hC : C.verts ⊆ G.support := by
    intro w hw
    apply (G.degree_pos_iff_mem_support w).mp
    have hdeg := cycle_degree C hc w
    rw [if_pos hw] at hdeg
    have hle := SimpleGraph.degree_le_of_le (v := w) C.spanningCoe_le
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hdeg hle ⊢
    omega
  have hh := degree_add_four_le_twice_count hG C J hc hj hd hsub
    (fun w hw => hfour w (hC hw)) hn
  rw [hfour v hv] at hh
  omega

/-- A nested nonspanning pair in a critical graph of count at most three
certifies existence of a degree-two vertex. -/
lemma degree_two_of_nested_nonspanning {k : ℕ}
    (hG : IsCountCritical k G) (hk : k ≤ 3)
    (C J : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hj : J.coe.Connected ∧ J.coe.IsRegularOfDegree 2)
    (hd : Disjoint C.edgeSet J.edgeSet) (hsub : C.verts ⊆ J.verts)
    (hne : ∃ v ∈ G.support, v ∉ J.verts) : ∃ v, G.degree v = 2 := by
  by_contra hno
  have hno' : ∀ v, G.degree v ≠ 2 := by simpa using hno
  obtain ⟨v,hv,hvJ⟩ := hne
  have hbot : G ≠ ⊥ := by
    intro hb
    simpa [hb] using hv
  have hfour := LowCountCritical.supported_degree_eq_four_of_count_le_three hG hk hbot hno'
  exact hvJ (outer_covers_support_of_count_le_three hG hk hfour C J hc hj hd hsub hv)

end Erdos184.CriticalNestedCycles
