import FormalConjecturesUtil
import Submission.EdgeAttachments

/-! Three hexagons attached along two different old edges. -/
open SimpleGraph
namespace Erdos713EdgeAttachmentExample
open Erdos713EdgeAttachments

abbrev A := Fin 6 ⊕ Interior (0 : Fin 6) 1
abbrev V := A ⊕ Interior (0 : Fin 6) 1
abbrev first := paste Erdos713C6.C6 0 1 Erdos713C6.C6 0 1
abbrev graph : SimpleGraph V := paste Erdos713C6.C6 0 1 first (.inl 3) (.inl 4)

lemma built : Built Erdos713C6.C6 0 1 graph (.inl (.inl 0)) (.inl (.inl 1)) := by
  exact Built.step (Built.step Built.base 0 1 (cycle_base_adj 4)) (.inl 3) (.inl 4)
    (show Erdos713C6.C6.Adj 3 4 by decide)

lemma order : Nat.card V = 14 := by
  rw [Nat.card_eq_fintype_card]
  decide

lemma rate : Erdos713Rate.HasRate graph ((4 : ℝ)/3) :=
  hexagon_sandwich_rate ⟨V,graph,_,_,built,built.contains,.refl _⟩

lemma rooted_rate : Erdos713ActualBlocks.RootedRate graph :=
  hexagon_sandwich_rooted_rate ⟨V,graph,_,_,built,built.contains,.refl _⟩

#print axioms built
#print axioms order
#print axioms rooted_rate
end Erdos713EdgeAttachmentExample
