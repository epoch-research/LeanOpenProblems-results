import Submission.ThirdTriangleFiniteEdgeSupportFailure
import Submission.FiniteExceptionUltrafilterTarget

/-!
All finite mutual towers of the new finite-edge-support counterexample
are nevertheless countably coverable. This prevents confusing the support
failure with a witness to Erdős 595.
-/

open SimpleGraph Set
open Erdos595Work Erdos595GenericUltrafilterUniversality
open Erdos595FiniteEdgeSupportFailure Erdos595ThirdTriangleFiniteEdgeSupportFailure
namespace Erdos595FiniteEdgeSupportTowerCover

abbrev Target := ((n : ℕ) × Fin (size n)) ⊕ Fin 3

def T : SimpleGraph Target where
  Adj
    | .inl x,.inl y => x.1 = y.1 ∧ x.2.val ≠ y.2.val
    | .inl _,.inr a => a ≠ 2
    | .inr a,.inl _ => a ≠ 2
    | .inr a,.inr b => a ≠ b
  symm := by
    intro x y h
    cases x <;> cases y
    · exact ⟨h.1.symm,Ne.symm h.2⟩
    · exact h
    · exact h
    · exact Ne.symm h
  loopless := by
    intro x h
    cases x
    · exact h.2 rfl
    · exact h rfl

def E : Set Target := {Sum.inr 0,Sum.inr 1}
def dummy : Target := Sum.inr 2

lemma E_finite : E.Finite := (Set.finite_singleton _).insert _

lemma dummy_adj : ∀ a ∈ E, T.Adj dummy a := by
  intro a ha
  rcases ha with rfl | rfl
  · exact (by decide : (2 : Fin 3) ≠ 0)
  · exact (by decide : (2 : Fin 3) ≠ 1)

lemma finite_neighbors : ∀ a ∉ E, (T.neighborSet a).Finite := by
  intro a ha
  cases a with
  | inl x =>
    rcases x with ⟨n,i⟩
    have hs : (Set.range (fun j : Fin (size n) => (Sum.inl (Sigma.mk n j) : Target)) ∪
        Set.range (Sum.inr : Fin 3 → Target)).Finite := (Set.finite_range _).union (Set.finite_range _)
    apply hs.subset
    intro y hy
    cases y with
    | inl x =>
      rcases x with ⟨m,j⟩
      have he : n = m := hy.1
      subst m
      exact Or.inl ⟨j,rfl⟩
    | inr j => exact Or.inr ⟨j,rfl⟩
  | inr j =>
    have hj : j = 2 := by
      fin_cases j
      · exact (ha (Or.inl rfl)).elim
      · exact (ha (Or.inr rfl)).elim
      · rfl
    subst j
    apply (Set.finite_range (Sum.inr : Fin 3 → Target)).subset
    intro y hy
    cases y with
    | inl x => exact (hy rfl).elim
    | inr j => exact ⟨j,rfl⟩

def encode : NewVertex → Target
  | .inl (.inl ⟨n,x⟩) => .inl ⟨n,x.1⟩
  | .inl (.inr _) => .inr 0
  | .inr _ => .inr 1

def initialHom : K →g T where
  toFun := encode
  map_rel' := by
    intro a b hab
    rcases a with (⟨n,x⟩ | a) | a <;> rcases b with (⟨m,y⟩ | b) | b
    · change H.Adj ⟨n,x⟩ ⟨m,y⟩ at hab
      obtain ⟨rfl,h⟩ := hab
      exact ⟨rfl,fun he => h.1.ne (Fin.ext he)⟩
    · exact (by decide : (0 : Fin 3) ≠ 2)
    · exact (by decide : (1 : Fin 3) ≠ 2)
    · exact (by decide : (0 : Fin 3) ≠ 2)
    · exact hab.elim
    · exact (by decide : (0 : Fin 3) ≠ 1)
    · exact (by decide : (1 : Fin 3) ≠ 2)
    · exact (by decide : (1 : Fin 3) ≠ 0)
    · exact hab.elim

/-- A proper countable vertex palette exists at every finite stage. -/
theorem tower_has_countable_target (n : ℕ) : Nonempty ((tower K K_cliqueFree n).val →g T) :=
  ⟨Erdos595FiniteExceptionUltrafilterTarget.towerHom T E E_finite finite_neighbors dummy dummy_adj
    K_cliqueFree initialHom n⟩

/-- The triangle-bearing finite-edge-support obstruction is STILL countably
coverable at every finite mutual-ultrafilter stage. -/
theorem every_finite_tower_cover (n : ℕ) :
    IsCountableUnionOfTriangleFree (tower K K_cliqueFree n).val :=
  Erdos595FiniteExceptionUltrafilterTarget.tower_cover T E E_finite finite_neighbors dummy dummy_adj
    K_cliqueFree initialHom n

theorem concrete_third_cover : IsCountableUnionOfTriangleFree K₃ := every_finite_tower_cover 3

#print axioms initialHom
#print axioms every_finite_tower_cover
#print axioms concrete_third_cover
end Erdos595FiniteEdgeSupportTowerCover
