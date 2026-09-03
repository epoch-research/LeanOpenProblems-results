import Submission.BinaryAcceptingMinplusCertificates

/-! Finite powerset certificates for totality of accepting-run minima.
Totality need not come from a path that remains accepting at every prefix. -/
namespace Erdos406BinaryAcceptingMinplus
open Erdos406Tropical (Automaton Run)
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def nextSet (D : Automaton σ) (S : Finset σ) (d : ℕ) : Finset σ :=
  S.biUnion (fun s => D.next s d)

structure Coverage (D : Automaton σ) (F : σ → Prop) where
  family : Finset (Finset σ)
  start : {D.start} ∈ family
  step : ∀ S, S ∈ family → ∀ d, d < 2 → nextSet D S d ∈ family
  accepting : ∀ S, S ∈ family → ∃ t, t ∈ S ∧ F t

namespace Coverage
variable {D : Automaton σ} {F : σ → Prop} (C : Coverage D F)
include C

lemma reachable_set (n : ℕ) : ∃ S, S ∈ C.family ∧
    ∀ t, t ∈ S → ∃ v, Run D D.start (Nat.digits 2 n).reverse t v := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      refine ⟨{D.start},C.start,?_⟩
      intro t ht
      have he : t = D.start := Finset.mem_singleton.mp ht
      subst t
      exact ⟨0,by simpa using Run.nil (D:=D) D.start⟩
    have hp : 0 < n := Nat.pos_of_ne_zero hz
    obtain ⟨S,hS,hR⟩ := ih (n/2) (Nat.div_lt_self hp (by decide))
    refine ⟨nextSet D S (n%2),C.step S hS (n%2) (Nat.mod_lt _ (by decide)),?_⟩
    intro t ht
    obtain ⟨s,hs,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨v,hv⟩ := hR s hs
    refine ⟨v+D.weight s (n%2) t,?_⟩
    rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) hp,List.reverse_cons]
    exact hv.snoc ht

lemma total : Total D F := by
  intro n
  obtain ⟨S,hS,hR⟩ := C.reachable_set n
  obtain ⟨t,ht,hF⟩ := C.accepting S hS
  obtain ⟨v,hv⟩ := hR t ht
  exact ⟨t,v,hv,hF⟩
end Coverage
end Erdos406BinaryAcceptingMinplus

namespace Erdos406BinaryAcceptingCoverageControl
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
noncomputable section

def D : Automaton (Fin 4) where
  start := 0
  next s d := if s = 0 then (if d = 0 then {0} else {1})
    else if s = 1 then {2,3} else if s = 2 then {3} else {2}
  nonempty := by intro s d; split_ifs <;> simp
  weight _ _ _ := 0

def F (s : Fin 4) : Prop := s ≠ 3
instance (s : Fin 4) : Decidable (F s) := by unfold F; infer_instance

def family : Finset (Finset (Fin 4)) := {{0},{1},{2,3}}

lemma finite_checks :
    (∀ S ∈ family, ∀ d : Fin 2, nextSet D S d.val ∈ family) ∧
    (∀ S ∈ family, ∃ t, t ∈ S ∧ F t) := by decide +kernel

def coverage : Coverage D F where
  family := family
  start := by decide +kernel
  step := by intro S hS d hd; exact finite_checks.1 S hS ⟨d,hd⟩
  accepting := finite_checks.2

lemma total : Total D F := coverage.total

/-- Total acceptance here cannot be witnessed by a subset of accepting
states closed under an existential choice for each successive digit. -/
lemma no_closed_accepting_subset : ¬ ∃ S : Finset (Fin 4),
    D.start ∈ S ∧ (∀ s ∈ S, F s) ∧
    ∀ s ∈ S, ∀ d : Fin 2, ∃ t, t ∈ D.next s d.val ∧ t ∈ S := by
  decide +kernel

#print axioms Erdos406BinaryAcceptingMinplus.Coverage.total
#print axioms total
#print axioms no_closed_accepting_subset
end
end Erdos406BinaryAcceptingCoverageControl
