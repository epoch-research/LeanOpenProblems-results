import Submission.AdjacentCertificateTransfer

/-! Normalization of independent-odd degree certificates at thresholds at least
as large as the order. This is a statement about lower certificates only. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ParityDegreeLower
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V]

/-- A single enhanced independent-odd degree certificate at integer threshold k.
The certificate does not require the hub set A to avoid the independent set B. -/
structure Certificate (G : SimpleGraph V) (k : ℕ) (A B O : Finset V) : Prop where
  positive : 1 ≤ A.card
  disjoint : Disjoint A O
  independent : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y
  oddB : ∀ x ∈ B, Odd (Nat.card (G.neighborSet x))
  oddO : ∀ x ∈ O, Odd (Nat.card (G.neighborSet x))
  bound : 2 * A.card * (k - 1) <
    (∑ x ∈ A, Nat.card (G.neighborSet x)) + (2 * A.card - 2) * B.card + O.card

lemma independent_degree_card_le (G : SimpleGraph V) (B : Finset V)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y) {x : V} (hx : x ∈ B) :
    Nat.card (G.neighborSet x) + B.card ≤ Fintype.card V := by
  have hd : Disjoint (G.neighborFinset x) B := by
    apply Finset.disjoint_left.mpr
    intro y hy hyB
    exact hB x hx y hyB ((G.mem_neighborFinset x y).mp hy)
  have hc := Finset.card_le_card (Finset.subset_univ (G.neighborFinset x ∪ B))
  rw [Finset.card_union_of_disjoint hd, Finset.card_univ,
    SimpleGraph.card_neighborFinset_eq_degree] at hc
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using hc

lemma disjoint_card_le_order {A O : Finset V} (hd : Disjoint A O) :
    A.card + O.card ≤ Fintype.card V := by
  have hc := Finset.card_le_card (Finset.subset_univ (A ∪ O))
  rwa [Finset.card_union_of_disjoint hd, Finset.card_univ] at hc

lemma Certificate.erase_overlap {G : SimpleGraph V} {k : ℕ} {A B O : Finset V}
    (h : Certificate G k A B O) (hk : Fintype.card V ≤ k)
    {x : V} (hxA : x ∈ A) (hxB : x ∈ B) :
    Certificate G k (A.erase x) B (insert x O) := by
  have hd := independent_degree_card_le G B h.independent hxB
  have hAO := disjoint_card_le_order h.disjoint
  have hbpos : 1 ≤ B.card := Finset.one_le_card.mpr ⟨x, hxB⟩
  have hxO : x ∉ O := fun hxO => Finset.disjoint_left.mp h.disjoint hxA hxO
  have hca := Finset.card_erase_add_one hxA
  have hco := Finset.card_insert_of_notMem hxO
  have hsum := Finset.sum_erase_add A (fun w => Nat.card (G.neighborSet w)) hxA
  have hapos : 2 ≤ A.card := by
    by_contra ha
    have ha1 : A.card = 1 := by have := h.positive; omega
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp ha1
    have hxy : x = y := by simpa only [hy, Finset.mem_singleton] using hxA
    have hcert := h.bound
    rw [hy, ← hxy] at hcert
    simp only [Finset.card_singleton, Finset.sum_singleton] at hcert
    omega
  have hdpos : 1 ≤ Nat.card (G.neighborSet x) := by
    have ho := (h.oddB x hxB).pos
    omega
  have hkb : Nat.card (G.neighborSet x) + 2 * B.card - 1 ≤ 2 * (k - 1) := by
    omega
  have hdis : Disjoint (A.erase x) (insert x O) := by
    apply Finset.disjoint_left.mpr
    intro y hy hyO
    rcases Finset.mem_insert.mp hyO with hyx | hyO
    · exact (Finset.mem_erase.mp hy).1 hyx
    · exact Finset.disjoint_left.mp h.disjoint (Finset.mem_of_mem_erase hy) hyO
  refine ⟨by omega, hdis, h.independent, h.oddB, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact h.oddB _ hxB
    · exact h.oddO y hy
  · have hbound := h.bound
    have ha_sub : 2 * A.card - 2 = 2 * (A.erase x).card := by omega
    have hae_sub : 2 * (A.erase x).card - 2 + 2 = 2 * (A.erase x).card := by omega
    rw [ha_sub] at hbound
    rw [hco]
    have hk1 : 1 ≤ k := by omega
    have hdk : Nat.card (G.neighborSet x) + 2 * B.card ≤ 2 * (k - 1) + 1 := by omega
    nlinarith

lemma Certificate.exists_disjoint {G : SimpleGraph V} {k : ℕ} {A B O : Finset V}
    (h : Certificate G k A B O) (hk : Fintype.card V ≤ k) :
    ∃ A' O' : Finset V, Certificate G k A' B O' ∧ Disjoint A' B := by
  let S := (Finset.univ : Finset (Finset V × Finset V)).filter
    (fun p => Certificate G k p.1 B p.2)
  have hS : S.Nonempty := ⟨(A,O), by simp [S, h]⟩
  obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image S (fun p => p.1.card) hS
  have hc : Certificate G k p.1 B p.2 := (Finset.mem_filter.mp hp).2
  refine ⟨p.1, p.2, hc, ?_⟩
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  have hn := hc.erase_overlap hk hxA hxB
  have hm := hmin (p.1.erase x, insert x p.2) (by simp [S, hn])
  have he := Finset.card_erase_add_one hxA
  change p.1.card ≤ (p.1.erase x).card at hm
  omega

end Erdos184Work.ParityDegreeLower
#print axioms Erdos184Work.ParityDegreeLower.Certificate.erase_overlap
#print axioms Erdos184Work.ParityDegreeLower.Certificate.exists_disjoint
