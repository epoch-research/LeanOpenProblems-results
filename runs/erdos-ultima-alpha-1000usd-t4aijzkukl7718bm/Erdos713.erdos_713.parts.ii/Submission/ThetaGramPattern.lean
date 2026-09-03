import FormalConjecturesUtil
import Submission.ThetaGramPrune

/-! The counterexample applies to the precise three-by-four matrix considered
in the neighborhood argument for eight-vertex representative 23. -/
namespace Erdos713ThetaGram

def sevenPattern (i : Fin 3) (j : Fin 4) : Prop :=
  Nat.testBit ((![3,13,14] : Fin 3 → ℕ) i) j.val = true

def PatternFree {A B : Type*} (R : A → B → Prop) : Prop :=
  ∀ (a : Fin 3 → A) (b : Fin 4 → B), Function.Injective a → Function.Injective b →
    (∀ i j, sevenPattern i j → R (a i) (b j)) → False

lemma hasTheta_of_pattern {A B : Type*} (R : A → B → Prop)
    (a : Fin 3 → A) (b : Fin 4 → B) (ha : Function.Injective a) (hb : Function.Injective b)
    (h : ∀ i j, sevenPattern i j → R (a i) (b j)) : HasTheta R := by
  refine ⟨a ∘ (![1,2,0] : Fin 3 → Fin 3),b ∘ (![2,3,0,1] : Fin 4 → Fin 4),
    ha.comp (by decide),hb.comp (by decide),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact h 1 2 (by unfold sevenPattern; decide)
  · exact h 2 2 (by unfold sevenPattern; decide)
  · exact h 1 3 (by unfold sevenPattern; decide)
  · exact h 2 3 (by unfold sevenPattern; decide)
  · exact h 1 0 (by unfold sevenPattern; decide)
  · exact h 0 0 (by unfold sevenPattern; decide)
  · exact h 2 1 (by unfold sevenPattern; decide)
  · exact h 0 1 (by unfold sevenPattern; decide)

lemma patternFree_of_noTheta {A B : Type*} (R : A → B → Prop) (h : ¬ HasTheta R) : PatternFree R :=
  fun a b ha hb he => h (hasTheta_of_pattern R a b ha hb he)

lemma no_unbalanced_pattern_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      PatternFree R →
        (Nat.card {p : A × B // R p.1 p.2} : ℝ) ≤
          C*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) := by
  rintro ⟨C,hC,h⟩
  apply no_unbalanced_bound
  exact ⟨C,hC,fun A B _ _ R hR => h A B R (patternFree_of_noTheta R hR)⟩

#print axioms hasTheta_of_pattern
#print axioms no_unbalanced_pattern_bound
end Erdos713ThetaGram
