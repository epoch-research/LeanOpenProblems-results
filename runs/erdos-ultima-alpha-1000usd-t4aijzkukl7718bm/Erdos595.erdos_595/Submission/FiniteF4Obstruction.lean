import Submission.FiniteTriangleRamsey
import Submission.UniformF4Obstruction
import Submission.AffineCompactnessReduction

/-!
There is a finite K4-free graph with no noncollapsed affine edge representation
over F4 in any dimension. This rules out the fixed-F4 premise of the earlier
compactness reduction, but does not settle Erdős 595.
-/
set_option autoImplicit false
set_option linter.style.existsImplication false
open SimpleGraph Set
namespace Erdos595FiniteF4Obstruction
open Erdos595FiniteTrianglePartite Erdos595AffineCompactness
universe u

lemma triangle_vec {A : Type*} (H : SimpleGraph A) (a b c : A)
    (hab : H.Adj a b) (hac : H.Adj a c) (hbc : H.Adj b c) :
    IsTriangle H ![a,b,c] := by
  intro i j hij
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  fin_cases i <;> fin_cases j <;> simp_all

lemma strict_vec {A : Type*} [Preorder A] (a b c : A) (hab : a < b) (hbc : b < c) :
    StrictMono (![a,b,c] : Fin 3 → A) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> assumption

/-- A finite K4-free obstruction uniform in the dimension of the representation. -/
theorem finite_obstruction (K : Type) [Field K] [Finite K] [CharP K 2]
    (hroot : ∀ t : K, t ≠ 0 → t ≠ 1 → t^2+t+1=0) :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ∀ (E : Type u) [AddCommGroup E] [Module K E],
        ¬∃ f : Sym2 V → E, Represents (K := K) G f := by
  classical
  let H := Erdos595UniformF4Obstruction.G
  obtain ⟨V,hV,G,hG,hRam⟩ := Erdos595FiniteTriangleRamsey.finite_triangle_ramsey
    9 K H Erdos595UniformF4Obstruction.cliqueFree
  refine ⟨V,hV,G,hG,?_⟩
  intro E _ _
  rintro ⟨F,hF⟩
  have hchoice : ∀ x : Fin 3 → V, ∃ t : K, IsTriangle G x →
      t ≠ 0 ∧ t ≠ 1 ∧
      F s(x 0,x 2) = t • F s(x 0,x 1) + (1-t) • F s(x 1,x 2) ∧
      F s(x 0,x 1) ≠ F s(x 1,x 2) := by
    intro x
    by_cases hx : IsTriangle G x
    · obtain ⟨t,ht⟩ := hF (x 0) (x 1) (x 2)
        (hx 0 1 (by decide)) (hx 0 2 (by decide)) (hx 1 2 (by decide))
      exact ⟨t,fun _ => ht⟩
    · exact ⟨0,fun h => (hx h).elim⟩
  choose col hcol using hchoice
  obtain ⟨e,z,he⟩ := hRam col
  let f : Fin 9 → Fin 9 → E := fun a b => F s(e a,e b)
  have ht (a b c : Fin 9) (hab : a < b) (hbc : b < c)
      (h₁ : H.Adj a b) (h₂ : H.Adj a c) (h₃ : H.Adj b c) :
      z ≠ 0 ∧ z ≠ 1 ∧ f a c = z • f a b + (1-z) • f b c ∧ f a b ≠ f b c := by
    let x : Fin 3 → Fin 9 := ![a,b,c]
    have hx : IsTriangle H x := triangle_vec H a b c h₁ h₂ h₃
    have hx' : IsTriangle G (e ∘ x) := fun i j hij => e.map_rel_iff.mpr (hx i j hij)
    have hz := he x (strict_vec a b c hab hbc) hx
    have hh := hcol (e ∘ x) hx'
    rw [hz] at hh
    exact hh
  have hs := ht 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hzroot := hroot z hs.1 hs.2.1
  have hcollapse : f 1 2 = f 1 3 :=
    Erdos595UniformF4Obstruction.collapse_affine z hzroot f
      (fun a b c hab hbc h₁ h₂ h₃ => (ht a b c hab hbc h₁ h₂ h₃).2.2.1)
  have heq : (1-z) • f 1 2 = (1-z) • f 2 3 := by
    have h := hs.2.2.1
    rw [← hcollapse] at h
    calc
      _ = f 1 2 - z • f 1 2 := by module
      _ = (z • f 1 2 + (1-z) • f 2 3) - z • f 1 2 := by rw [← h]
      _ = _ := by abel
  exact hs.2.2.2 (smul_right_injective E (sub_ne_zero.mpr hs.2.1.symm) heq)

lemma root_of_card_four (K : Type*) [Field K] [Fintype K]
    (hcard : Fintype.card K = 4) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    t^2+t+1=0 := by
  have hp := FiniteField.pow_card_sub_one_eq_one t ht0
  rw [hcard] at hp
  have he : (t-1)*(t^2+t+1)=0 := by linear_combination hp
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ht1)

/-- The field with four elements fails the universal finite representation premise. -/
theorem f4_obstruction :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ∀ (E : Type u) [AddCommGroup E] [Module (GaloisField 2 2) E],
        ¬∃ f : Sym2 V → E, Represents (K := GaloisField 2 2) G f := by
  classical
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  apply finite_obstruction
  apply root_of_card_four
  rw [← Nat.card_eq_fintype_card,GaloisField.card 2 2 (by decide)]
  decide

#print axioms finite_obstruction
#print axioms f4_obstruction
end Erdos595FiniteF4Obstruction
