import FormalConjecturesUtil
import Submission.CloneSupportPacking

/-! Summing partial-cloning bounds on a single bipartite extremal host. -/
open SimpleGraph Finset
namespace Erdos713PartialCloning

lemma packing_mass {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) {n : ℕ} (G : SimpleGraph (Fin n))
    (hfree : H.Free G) (hB : G.IsBipartite)
    (he : Nat.card G.edgeSet = Erdos713BipExtremal.number n H)
    {s : ℝ}
    (hinc : (n : ℝ)*((Erdos713BipExtremal.number (n+1) H : ℝ)-
      (Erdos713BipExtremal.number n H : ℝ)) ≤ s*(Erdos713BipExtremal.number n H : ℝ)) :
    ∃ F : Fin n → Finset (Finset (Fin n)),
      (∀ v, Packing H G v (F v)) ∧
      (2-s)*(Nat.card G.edgeSet : ℝ) ≤ (Fintype.card W : ℝ)*∑ v, ((F v).card : ℝ) := by
  classical
  choose F hF hlocal using fun v => exists_support_packing H hNoIso G hfree hB v
  refine ⟨F,hF,?_⟩
  have hlocalR (v : Fin n) : (Nat.card G.edgeSet : ℝ)+(Nat.card (G.neighborSet v) : ℝ) ≤
      (Erdos713BipExtremal.number (n+1) H : ℝ)+(Fintype.card W : ℝ)*((F v).card : ℝ) := by
    have hh := hlocal v
    simp only [Fintype.card_fin] at hh
    exact_mod_cast hh
  have hsum := sum_le_sum (fun v (_ : v ∈ (univ : Finset (Fin n))) => hlocalR v)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    ← mul_sum] at hsum
  have hsumdeg : (∑ v : Fin n, (Nat.card (G.neighborSet v) : ℝ)) = 2*(Nat.card G.edgeSet : ℝ) := by
    have hh := G.sum_degrees_eq_twice_card_edges
    simp only [← card_neighborSet_eq_degree,edgeFinset_card,Fintype.card_eq_nat_card] at hh
    exact_mod_cast hh
  rw [hsumdeg,he] at hsum
  rw [he]
  nlinarith

#print axioms packing_mass
end Erdos713PartialCloning
