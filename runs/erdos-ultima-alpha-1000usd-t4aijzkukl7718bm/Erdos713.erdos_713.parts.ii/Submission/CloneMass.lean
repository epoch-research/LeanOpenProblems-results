import FormalConjecturesUtil
import Submission.VertexCloning
import Submission.FuturePowerRecords

/-! Along an unbounded sequence of exact extremal graphs, a positive fraction
of total degree is carried by vertices at which cloning creates the forbidden
graph. The obstructions project to single-identification patterns. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713Cloning

lemma mass_bound {W : Type*} (H : SimpleGraph W) {n : ℕ} (G : SimpleGraph (Fin n))
    (hfree : H.Free G) (he : Nat.card G.edgeSet = extremalNumber n H)
    {s : ℝ} (hs : 0 ≤ s)
    (hinc : (n : ℝ)*((extremalNumber (n+1) H : ℝ)-(extremalNumber n H : ℝ)) ≤
      s*(extremalNumber n H : ℝ)) :
    ∃ B : Finset (Fin n), (∀ v ∈ B, SingleFold H G v) ∧
      (2-s)*(Nat.card G.edgeSet : ℝ) ≤ ∑ v ∈ B, (Nat.card (G.neighborSet v) : ℝ) := by
  classical
  let D : ℝ := max ((extremalNumber (n+1) H : ℝ)-(extremalNumber n H : ℝ)) 0
  have hD : 0 ≤ D := le_max_right _ _
  have hBD : (n : ℝ)*D ≤ s*(Nat.card G.edgeSet : ℝ) := by
    rw [he]
    by_cases hd : 0 ≤ (extremalNumber (n+1) H : ℝ)-(extremalNumber n H : ℝ)
    · simpa only [D,max_eq_left hd] using hinc
    · have hd' : (extremalNumber (n+1) H : ℝ)-(extremalNumber n H : ℝ) ≤ 0 := le_of_not_ge hd
      simp only [D,max_eq_right hd',mul_zero]
      positivity
  let B : Finset (Fin n) := univ.filter (SingleFold H G)
  refine ⟨B,fun v hv => (mem_filter.mp hv).2,?_⟩
  have hlocal (v : Fin n) : (Nat.card (G.neighborSet v) : ℝ) ≤
      (if SingleFold H G v then (Nat.card (G.neighborSet v) : ℝ) else 0)+D := by
    by_cases hv : SingleFold H G v
    · simp only [if_pos hv]
      linarith
    · have hc : H.Free (clone G v) := fun hh => hv (fold_of_obstructed H G v hfree hh)
      have hh := safe_clone_bound H G v hc
      simp only [Fintype.card_fin] at hh
      have hh' : (Nat.card G.edgeSet : ℝ)+(Nat.card (G.neighborSet v) : ℝ) ≤
          (extremalNumber (n+1) H : ℝ) := by exact_mod_cast hh
      rw [he] at hh'
      have hle : (extremalNumber (n+1) H : ℝ)-(extremalNumber n H : ℝ) ≤ D := le_max_left _ _
      simp only [if_neg hv,zero_add]
      linarith
  have hsum := sum_le_sum (fun v (_ : v ∈ (univ : Finset (Fin n))) => hlocal v)
  rw [sum_add_distrib] at hsum
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hsumdeg : (∑ v : Fin n, (Nat.card (G.neighborSet v) : ℝ)) = 2*(Nat.card G.edgeSet : ℝ) := by
    have hh := G.sum_degrees_eq_twice_card_edges
    simp only [← card_neighborSet_eq_degree,edgeFinset_card,Fintype.card_eq_nat_card] at hh
    exact_mod_cast hh
  have hBsum : (∑ v : Fin n, if SingleFold H G v then (Nat.card (G.neighborSet v) : ℝ) else 0) =
      ∑ v ∈ B, (Nat.card (G.neighborSet v) : ℝ) := by simp only [B,sum_filter]
  rw [hsumdeg,hBsum] at hsum
  linarith

lemma exists_extremal_of_pos {W : Type*} (H : SimpleGraph W) (n : ℕ)
    (hn : 0 < extremalNumber n H) :
    ∃ G : SimpleGraph (Fin n), H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | H.Free G}
  have hS : S.Nonempty := by
    by_contra hs
    have he : S = ∅ := not_nonempty_iff_eq_empty.mp hs
    change 0 < S.sup (fun G => G.edgeFinset.card) at hn
    simp only [he,sup_empty,bot_eq_zero,lt_self_iff_false] at hn
  obtain ⟨G,hG,he⟩ := exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
  refine ⟨G,by simpa [S] using hG,?_⟩
  change Nat.card G.edgeSet = S.sup (fun G => G.edgeFinset.card)
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using he.symm

lemma of_asymptotic {W : Type*} (H : SimpleGraph W) {α c : ℝ}
    (hα : 1 ≤ α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (s : ℝ) (hαs : α < s) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ ∃ G : SimpleGraph (Fin n), H.Free G ∧
      Nat.card G.edgeSet = extremalNumber n H ∧ 0 < Nat.card G.edgeSet ∧
      ∃ B : Finset (Fin n), (∀ v ∈ B, SingleFold H G v) ∧
        (2-s)*(Nat.card G.edgeSet : ℝ) ≤ ∑ v ∈ B, (Nat.card (G.neighborSet v) : ℝ) := by
  obtain ⟨n,hn,hnp,hpos,hinc⟩ := Erdos713FutureRecords.exists_small_increment hα hc hαs h N
  have hpos' : 0 < extremalNumber n H := by exact_mod_cast hpos
  obtain ⟨G,hfree,he⟩ := exists_extremal_of_pos H n hpos'
  exact ⟨n,hn,hnp,G,hfree,he,he.symm ▸ hpos',
    mass_bound H G hfree he (by linarith) hinc⟩

/-- If the exponent is strictly below two, the obstruction mass is positive.
The same witnesses carry copies of a graph on one fewer forbidden vertex. -/
lemma exists_identification_witnesses {W : Type*} (H : SimpleGraph W) {α c : ℝ}
    (hα : α ∈ Set.Ico 1 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ ∃ G : SimpleGraph (Fin n), H.Free G ∧
      Nat.card G.edgeSet = extremalNumber n H ∧
      ∃ a b : W, ∃ hab : a ≠ b, ∃ hnab : ¬ H.Adj a b, identified H a b hnab ⊑ G := by
  obtain ⟨s,has,hs2⟩ := exists_between hα.2
  obtain ⟨n,hn,hnp,G,hfree,he,hpos,B,hB,hmass⟩ := of_asymptotic H hα.1 hc h s has N
  have hsumpos : 0 < ∑ v ∈ B, (Nat.card (G.neighborSet v) : ℝ) :=
    (mul_pos (sub_pos.mpr hs2) (by exact_mod_cast hpos)).trans_le hmass
  have hBne : B.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn,sum_empty] at hsumpos
    exact (lt_irrefl 0 hsumpos)
  obtain ⟨v,hv⟩ := hBne
  obtain ⟨a,b,hab,hnab,f,hfv⟩ := (hB v hv).identified_copy
  exact ⟨n,hn,hnp,G,hfree,he,a,b,hab,hnab,⟨f⟩⟩

#print axioms mass_bound
#print axioms of_asymptotic
#print axioms exists_identification_witnesses
end Erdos713Cloning
