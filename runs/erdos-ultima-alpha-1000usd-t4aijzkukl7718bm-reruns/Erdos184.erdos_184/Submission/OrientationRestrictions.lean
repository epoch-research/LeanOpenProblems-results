import Submission.OrientationComparison

/-! Every even restriction of an even graph is a disagreement graph of
balanced orientations. Thus disagreement comparison does not restrict the
class of proper even subgraphs. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.OrientationRestrictions
open BalancedOrientation OrientationComparison CycleNumberSubmodularity
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma balanced_union {H K : SimpleGraph V} {A B : V → V → ℕ}
    (hA : IsBalanced H A) (hB : IsBalanced K B) (hd : Disjoint H K) :
    IsBalanced (H ⊔ K) (fun x y => A x y + B x y) := by
  constructor
  · intro x y
    have ha := hA.1 x y
    have hb := hB.1 x y
    have hdis : ¬(H.Adj x y ∧ K.Adj x y) := by
      intro h
      have he : (H ⊓ K).Adj x y := h
      rw [disjoint_iff.mp hd] at he
      exact he
    change A x y + B x y + (A y x + B y x) = _
    simp only [sup_adj]
    by_cases hh : H.Adj x y <;> by_cases hk : K.Adj x y
    all_goals simp [hh,hk] at ha hb hdis ⊢
    all_goals omega
  · intro x
    simp only [Finset.sum_add_distrib]
    rw [hA.2,hB.2]

lemma balanced_reverse {G : SimpleGraph V} {A : V → V → ℕ}
    (hA : IsBalanced G A) : IsBalanced G (fun x y => A y x) := by
  refine ⟨fun x y => ?_,fun x => (hA.2 x).symm⟩
  simpa only [Nat.add_comm] using hA.1 x y

lemma exists_disagreement (G H : SimpleGraph V) (hHG : H ≤ G)
    (heG : ∀ v, Even (G.degree v)) (heH : ∀ v, Even (H.degree v)) :
    ∃ (A B : V → V → ℕ) (hA : IsBalanced G A) (hB : IsBalanced G B),
      disagreement hA hB = H := by
  obtain ⟨P,hP⟩ := exists_balanced H heH
  obtain ⟨Q,hQ⟩ := exists_balanced (G \ H) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      even_sdiff_of_even hHG heG heH v)
  have hd : Disjoint H (G \ H) := by
    rw [disjoint_iff]
    ext x y
    simp
  have hsup : H ⊔ (G \ H) = G := by
    ext x y
    simp only [sup_adj,sdiff_adj]
    exact ⟨fun h => h.elim (fun hh => hHG hh) And.left,
      fun h => by by_cases hh : H.Adj x y <;> tauto⟩
  let A : V → V → ℕ := fun x y => P x y + Q x y
  let B : V → V → ℕ := fun x y => P y x + Q x y
  have hA : IsBalanced G A := hsup ▸ balanced_union hP hQ hd
  have hB : IsBalanced G B := hsup ▸ balanced_union (balanced_reverse hP) hQ hd
  refine ⟨A,B,hA,hB,?_⟩
  ext x y
  change P x y + Q x y ≠ P y x + Q x y ↔ H.Adj x y
  have hp := hP.1 x y
  by_cases hh : H.Adj x y <;> simp only [hh,if_true,if_false] at hp
  · constructor
    · intro _; exact hh
    · intro _; omega
  · constructor
    · intro hn; omega
    · exact False.elim ∘ hh

lemma even_iff_disagreement (G H : SimpleGraph V)
    (heG : ∀ v, Even (G.degree v)) :
    (H ≤ G ∧ ∀ v, Even (H.degree v)) ↔
      ∃ (A B : V → V → ℕ) (hA : IsBalanced G A) (hB : IsBalanced G B),
        disagreement hA hB = H := by
  constructor
  · rintro ⟨hle,he⟩
    exact exists_disagreement G H hle heG he
  · rintro ⟨A,B,hA,hB,rfl⟩
    exact ⟨disagreement_le hA hB,disagreement_even hA hB⟩

end Erdos184.OrientationRestrictions
