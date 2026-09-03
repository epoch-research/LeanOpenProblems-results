import FormalConjecturesUtil
import Submission.ApexThetaCopyOrientations
import Submission.ThetaThreePointRigidity

/-! A rigid theta-free relation has an apex-theta-free universal-row extension.
This gives a whole-host realization, but no degree balance or extremality. -/

open SimpleGraph
namespace Erdos713UniversalRowTheta
open Erdos713ThetaGram Erdos713ThetaThreePoint Erdos713GlobalTheta
open Erdos713ApexThetaOrientations Erdos713C6
set_option maxHeartbeats 2000000
variable {A B : Type*}

def extension (R : A → B → Prop) : Option A → B → Prop
  | none, _ => True
  | some a, b => R a b

lemma common_three_forces_new {R : A → B → Prop} (hR : Rigid3 R)
    {a b : Option A} (hab : a ≠ b) (f : Fin 3 → B) (hf : Function.Injective f)
    (ha : ∀ i, extension R a (f i)) (hb : ∀ i, extension R b (f i)) :
    a = none ∨ b = none := by
  cases a with
  | none => exact Or.inl rfl
  | some a =>
    cases b with
    | none => exact Or.inr rfl
    | some b => exact (hab (congrArg some (hR a b f hf ha hb))).elim

lemma no_forward {R : A → B → Prop} (hR : Rigid3 R) (hfree : ¬ HasTheta R) :
    ¬ HasApex (extension R) := by
  rintro ⟨a,b,ha,hb,hm⟩
  have hn : a none = none := by
    have hfirst := common_three_forces_new hR
      (fun h => (by decide : (none : Option (Fin 3)) ≠ some 0) (ha h))
      (fun i => b (![0,1,2] i)) (hb.comp (by decide : Function.Injective (![0,1,2] : Fin 3 → Fin 4)))
      (fun i => hm none _ (by trivial)) (fun i => hm (some 0) _ (by
        fin_cases i <;> norm_num [apexRel,thetaRel] <;> decide))
    have hsecond := common_three_forces_new hR
      (fun h => (by decide : (none : Option (Fin 3)) ≠ some 1) (ha h))
      (fun i => b (![0,1,3] i)) (hb.comp (by decide : Function.Injective (![0,1,3] : Fin 3 → Fin 4)))
      (fun i => hm none _ (by trivial)) (fun i => hm (some 1) _ (by
        fin_cases i <;> norm_num [apexRel,thetaRel] <;> decide))
    rcases hfirst with h | h
    · exact h
    rcases hsecond with h' | h'
    · exact h'
    have he := ha (h.trans h'.symm)
    contradiction
  have hold (i : Fin 3) : ∃ v : A, a (some i) = some v := by
    apply Option.ne_none_iff_exists'.mp
    intro h
    have he := ha (h.trans hn.symm)
    contradiction
  choose v hv using hold
  have hvi : Function.Injective v := by
    intro i j hij
    apply Option.some_injective
    apply ha
    rw [hv,hv,hij]
  have hinc (i : Fin 3) (j : Fin 4) (h : thetaRel i j) : R (v i) (b j) := by
    have hh := hm (some i) j h
    rw [hv] at hh
    exact hh
  apply hfree
  refine ⟨v,b,hvi,hb,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    apply hinc <;> simp only [thetaRel] <;> decide

lemma no_reverse {R : A → B → Prop} (hR : Rigid3 R) (hfree : ¬ HasTheta R) :
    ¬ HasApex (fun b a => extension R a b) := by
  rintro ⟨a,b,ha,hb,hm⟩
  have hpair : b 0 = none ∨ b 1 = none := by
    apply common_three_forces_new hR
      (fun h => (by decide : (0 : Fin 4) ≠ 1) (hb h))
      (fun i => a (![none,some 0,some 1] i))
      (ha.comp (by decide : Function.Injective (![none,some 0,some 1] : Fin 3 → Option (Fin 3))))
    · intro i
      apply hm
      fin_cases i <;> norm_num [apexRel,thetaRel]
    · intro i
      apply hm
      fin_cases i <;> norm_num [apexRel,thetaRel] <;> decide
  have finish (j : Fin 4) (hj : j = 0 ∨ j = 1)
      (hold : ∀ i : Fin 3, b (![j,2,3] i) ≠ none) : False := by
    have hidx : Function.Injective (![j,2,3] : Fin 3 → Fin 4) := by
      rcases hj with rfl | rfl <;> decide
    have hex (i : Fin 3) : ∃ v : A, b (![j,2,3] i) = some v :=
      Option.ne_none_iff_exists'.mp (hold i)
    choose v hv using hex
    have hvi : Function.Injective v := by
      intro i l hil
      apply hidx
      apply hb
      rw [hv,hv,hil]
    let c : Fin 4 → B := fun i => a (![none,some 0,some 1,some 2] i)
    have hci : Function.Injective c :=
      ha.comp (by decide : Function.Injective (![none,some 0,some 1,some 2] : Fin 4 → Option (Fin 3)))
    have hinc (i : Fin 3) (k : Fin 4) (h : thetaRel i k) : R (v i) (c k) := by
      have hp : apexRel (![none,some 0,some 1,some 2] k) (![j,2,3] i) := by
        rcases hj with rfl | rfl
        · exact (by intro i k; fin_cases i <;> fin_cases k <;> simp [thetaRel,apexRel] <;> decide : ∀ i k, thetaRel i k →
            apexRel (![none,some 0,some 1,some 2] k) (![0,2,3] i)) i k h
        · exact (by intro i k; fin_cases i <;> fin_cases k <;> simp [thetaRel,apexRel] <;> decide : ∀ i k, thetaRel i k →
            apexRel (![none,some 0,some 1,some 2] k) (![1,2,3] i)) i k h
      have hh := hm _ _ hp
      rw [hv] at hh
      exact hh
    apply hfree
    refine ⟨v,c,hvi,hci,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      apply hinc <;> simp only [thetaRel] <;> decide
  rcases hpair with h | h
  · apply finish 1 (Or.inr rfl)
    intro i hi
    have he := hb (hi.trans h.symm)
    fin_cases i <;> simp_all (config := {decide := true})
  · apply finish 0 (Or.inl rfl)
    intro i hi
    have he := hb (hi.trans h.symm)
    fin_cases i <;> simp_all (config := {decide := true})

/-- The extension avoids the actual unoriented eight-vertex graph. Both
possible orientations of a copy have been excluded. -/
theorem pattern_free {R : A → B → Prop} (hR : Rigid3 R) (hf : ¬ HasTheta R) :
    pattern.Free (bipGraph (extension R)) :=
  free_iff.mpr ⟨no_forward hR hf,no_reverse hR hf⟩

/-- Consequently all row and column links of this same host avoid theta. -/
theorem all_links_free {R : A → B → Prop} (hR : Rigid3 R) (hf : ¬ HasTheta R) :
    (∀ a, ¬ HasTheta (link (extension R) a)) ∧
    (∀ b, ¬ HasTheta (link (fun b a => extension R a b) b)) :=
  no_theta_both_links (pattern_free hR hf)

end Erdos713UniversalRowTheta
