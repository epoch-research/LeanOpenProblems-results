import Submission.SecondConeRightCover

/-! The odd graph KG(7,3) has no closed five-step walk. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595OddGraphSeven

def triple : Fin 35 → Finset (Fin 7) := ![{0,1,2},
  {0,1,3},
  {0,1,4},
  {0,1,5},
  {0,1,6},
  {0,2,3},
  {0,2,4},
  {0,2,5},
  {0,2,6},
  {0,3,4},
  {0,3,5},
  {0,3,6},
  {0,4,5},
  {0,4,6},
  {0,5,6},
  {1,2,3},
  {1,2,4},
  {1,2,5},
  {1,2,6},
  {1,3,4},
  {1,3,5},
  {1,3,6},
  {1,4,5},
  {1,4,6},
  {1,5,6},
  {2,3,4},
  {2,3,5},
  {2,3,6},
  {2,4,5},
  {2,4,6},
  {2,5,6},
  {3,4,5},
  {3,4,6},
  {3,5,6},
  {4,5,6}]

lemma triple_card : ∀ i, (triple i).card = 3 := by decide +kernel

def graph : SimpleGraph (Fin 35) where
  Adj a b := Disjoint (triple a) (triple b)
  symm := fun _ _ h => h.symm
  loopless := by
    intro a h
    have hn : (triple a).Nonempty :=
      Finset.card_pos.mp (by rw [triple_card]; decide)
    obtain ⟨x, hx⟩ := hn
    exact Finset.disjoint_left.mp h hx hx

instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (Disjoint (triple a) (triple b)))

private lemma cycle_five_bound : ∀ f : Fin 5 → Bool,
    (∀ i : Fin 5, ¬(f i = true ∧ f (i+1) = true)) →
      (∑ i : Fin 5, if f i then (1 : ℕ) else 0) ≤ 2 := by decide +kernel

lemma noFive : Erdos595SecondConeRight.NoFive graph := by
  intro a b c d e hab hbc hcd hde hea
  let S : Fin 5 → Finset (Fin 7) := ![triple a,triple b,triple c,triple d,triple e]
  have hc : ∀ i, (S i).card = 3 := by
    intro i
    fin_cases i <;> exact triple_card _
  have hd : ∀ i : Fin 5, Disjoint (S i) (S (i+1)) := by
    intro i
    fin_cases i
    · exact hab
    · exact hbc
    · exact hcd
    · exact hde
    · exact hea
  have bound (x : Fin 7) : (∑ i : Fin 5, if x ∈ S i then (1 : ℕ) else 0) ≤ 2 := by
    have hh := cycle_five_bound (fun i => decide (x ∈ S i)) (by
      intro i hi
      exact Finset.disjoint_left.mp (hd i)
        (of_decide_eq_true hi.1) (of_decide_eq_true hi.2))
    simpa using hh
  have count : (∑ x : Fin 7, ∑ i : Fin 5, if x ∈ S i then (1 : ℕ) else 0) = 15 := by
    rw [Finset.sum_comm]
    simp [hc]
  have hbnd := Finset.sum_le_sum (fun (x : Fin 7) (_ : x ∈ Finset.univ) => bound x)
  rw [count] at hbnd
  norm_num at hbnd

#print axioms noFive
end Erdos595OddGraphSeven
