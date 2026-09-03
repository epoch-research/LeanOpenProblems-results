import FormalConjecturesUtil
import Submission.BipartiteCloneWitnesses

/-! A fixed smaller bipartite identification pattern persists in arbitrarily
large bipartite-extremal hosts. Containment does not transfer a growth rate
or an exact asymptotic to that pattern. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713BipExtremal
open Erdos713Cloning

lemma finite_cofinal {I : Type*} [Fintype I] {P : I → ℕ → Prop}
    (h : ∀ N : ℕ, ∃ i n, N ≤ n ∧ P i n) :
    ∃ i, ∀ N : ℕ, ∃ n, N ≤ n ∧ P i n := by
  classical
  by_contra hn
  push_neg at hn
  choose N hN using hn
  obtain ⟨i,n,hnn,hp⟩ := h ((univ : Finset I).sup N)
  exact hN i n ((Finset.le_sup (f := N) (mem_univ i)).trans hnn) hp

lemma identification_witness {W : Type*} (H : SimpleGraph W) {α c : ℝ}
    (hα : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ ∃ G : SimpleGraph (Fin n), H.Free G ∧ G.IsBipartite ∧
      Nat.card G.edgeSet = number n H ∧ extremalNumber n H ≤ 2*Nat.card G.edgeSet ∧
      ∃ a b : W, a ≠ b ∧ ∃ hnab : ¬ H.Adj a b, identified H a b hnab ⊑ G := by
  obtain ⟨r,hr,hra⟩ := exists_between hα
  obtain ⟨s,has,hs2⟩ := exists_between ha2
  obtain ⟨n,hn,hnp,C,hC,G,hfree,hB,he,hhalf,hEq,hUpper,hDeg,hCut,B,hFold,hmass⟩ :=
    joint_of_asymptotic H hr hra has hc h N
  have hEpos : (0 : ℝ) < Nat.card G.edgeSet := by
    rw [hEq]
    exact mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast hnp) r)
  have hMassPos : 0 < ∑ v ∈ B, (Nat.card (G.neighborSet v) : ℝ) :=
    (mul_pos (sub_pos.mpr hs2) hEpos).trans_le hmass
  have hBne : B.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn,sum_empty] at hMassPos
    exact lt_irrefl 0 hMassPos
  obtain ⟨v,hv⟩ := hBne
  obtain ⟨a,b,hab,hnab,f,hfv⟩ := (hFold v hv).identified_copy
  exact ⟨n,hn,hnp,G,hfree,hB,he,hhalf,a,b,hab,hnab,⟨f⟩⟩

/-- The pair being identified can be fixed before the size threshold is chosen.
No exponent or exact leading constant is asserted for the identified graph. -/
lemma fixed_identification {W : Type*} [Fintype W] (H : SimpleGraph W) {α c : ℝ}
    (hα : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ a b : W, a ≠ b ∧ ∃ hnab : ¬ H.Adj a b,
      (identified H a b hnab).IsBipartite ∧
      ∀ N : ℕ, ∃ n, N ≤ n ∧ 0 < n ∧ ∃ G : SimpleGraph (Fin n),
        H.Free G ∧ G.IsBipartite ∧ Nat.card G.edgeSet = number n H ∧
        extremalNumber n H ≤ 2*Nat.card G.edgeSet ∧ identified H a b hnab ⊑ G := by
  let P (p : W × W) (n : ℕ) : Prop := 0 < n ∧ ∃ G : SimpleGraph (Fin n),
    H.Free G ∧ G.IsBipartite ∧ Nat.card G.edgeSet = number n H ∧
    extremalNumber n H ≤ 2*Nat.card G.edgeSet ∧
    p.1 ≠ p.2 ∧ ∃ hnab : ¬ H.Adj p.1 p.2, identified H p.1 p.2 hnab ⊑ G
  have hP : ∀ N : ℕ, ∃ p n, N ≤ n ∧ P p n := by
    intro N
    obtain ⟨n,hn,hnp,G,hfree,hB,he,hhalf,a,b,hab,hnab,hJ⟩ := identification_witness H hα ha2 hc h N
    exact ⟨(a,b),n,hn,hnp,G,hfree,hB,he,hhalf,hab,hnab,hJ⟩
  obtain ⟨p,hp⟩ := finite_cofinal hP
  obtain ⟨n,hn,hnp,G,hfree,hB,he,hhalf,hab,hnab,hJ⟩ := hp 0
  have hJB : (identified H p.1 p.2 hnab).IsBipartite := hB.of_hom hJ.some.toHom
  refine ⟨p.1,p.2,hab,hnab,hJB,?_⟩
  intro N
  obtain ⟨n,hn,hnp,G,hfree,hB,he,hhalf,hab',hnab',hJ⟩ := hp N
  exact ⟨n,hn,hnp,G,hfree,hB,he,hhalf,hJ⟩

lemma card_identified_vertices {W : Type*} [Fintype W] (a : W) :
    Nat.card {w : W // w ≠ a}+1 = Nat.card W := by
  classical
  haveI : Nonempty W := ⟨a⟩
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  have hp : 0 < Fintype.card W := Fintype.card_pos
  omega

#print axioms finite_cofinal
#print axioms identification_witness
#print axioms fixed_identification
#print axioms card_identified_vertices
end Erdos713BipExtremal
