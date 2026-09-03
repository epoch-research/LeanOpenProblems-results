import Submission.FiveDistinctExceptions

/-! Absorb all new no-three labels into the distinct base. The resulting
bounds count only genuine collisions and labels still containing three,
regardless of the total number of original exceptions. These are necessary
conditions, not a settlement of the odd covering problem. -/
namespace Erdos7ExceptionAbsorption
open Erdos7FourDistinctExceptions Erdos7FiveDistinctExceptions
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exceptions which cannot be moved into a distinct no-three base. -/
abbrev Residual {I J : Type*} (m : I → ℕ) (d : J → ℕ) (j : J) : Prop :=
  3 ∣ d j ∨ ∃ i, m i=d j

/-- Move every nonresidual exception into the base, with its residue unchanged.
No bound on the number of exceptions is used. -/
theorem absorb {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) :
    ∃ (n : I ⊕ {j // ¬ Residual m d j} → ℕ)
      (c : I ⊕ {j // ¬ Residual m d j} → ℤ),
      Function.Injective n ∧ (∀ k, 1 < n k ∧ Odd (n k)) ∧
      (∀ k, ¬ 3 ∣ n k) ∧
      ∀ x : ℤ, (∃ k, (n k : ℤ) ∣ x-c k) ∨
        ∃ j : {j // Residual m d j}, (d j : ℤ) ∣ x-b j := by
  classical
  let n : I ⊕ {j // ¬ Residual m d j} → ℕ := Sum.elim m (fun j => d j)
  let c : I ⊕ {j // ¬ Residual m d j} → ℤ := Sum.elim a (fun j => b j)
  refine ⟨n,c,?_,?_,?_,?_⟩
  · intro k l hkl
    cases k with
    | inl k =>
      cases l with
      | inl l => exact congrArg Sum.inl (hinj hkl)
      | inr l => exact False.elim (l.property (Or.inr ⟨k,hkl⟩))
    | inr k =>
      cases l with
      | inl l => exact False.elim (k.property (Or.inr ⟨l,hkl.symm⟩))
      | inr l => exact congrArg Sum.inr (Subtype.ext (hdi hkl))
  · intro k
    cases k with
    | inl k => exact hm k
    | inr k => exact hd k
  · intro k
    cases k with
    | inl k => exact h3 k
    | inr k => exact fun hh => k.property (Or.inl hh)
  · intro x
    rcases hcover x with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact Or.inl ⟨Sum.inl i,hi⟩
    · by_cases hr : Residual m d j
      · exact Or.inr ⟨⟨j,hr⟩,hj⟩
      · exact Or.inl ⟨Sum.inr ⟨j,hr⟩,hj⟩

/-- At least five exceptions must either contain three or duplicate a base
label. Arbitrarily many other exceptions do not help this bound. -/
theorem residual_card_five {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) :
    5 ≤ Fintype.card {j // Residual m d j} := by
  classical
  obtain ⟨n,c,hni,hn,hn3,hcov⟩ := absorb m a hinj hm h3 d b hdi hd hcover
  by_contra hsmall
  exact not_cover_four_distinct_odd n c hni hn hn3
    (fun j : {j // Residual m d j} => d j) (fun j => b j)
    (hdi.comp Subtype.val_injective) (fun j => hd j) (by omega) hcov

/-- With only five residual exceptions, none of the original exceptions has
three as a factor, and both five and seven occur as actual collision labels. -/
theorem residual_five_rigidity {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j)
    (hcard : Fintype.card {j // Residual m d j} ≤ 5) :
    (∀ j, ¬ 3 ∣ d j) ∧
    (∃ i j, m i=5 ∧ d j=5) ∧ (∃ i j, m i=7 ∧ d j=7) := by
  classical
  obtain ⟨n,c,hni,hn,hn3,hcov⟩ := absorb m a hinj hm h3 d b hdi hd hcover
  obtain ⟨hno,hfive,hseven⟩ := prime_constraints n c hni hn hn3
    (fun j : {j // Residual m d j} => d j) (fun j => b j)
    (hdi.comp Subtype.val_injective) (fun j => hd j) hcard hcov
  have hall (j : J) : ¬ 3 ∣ d j := by
    intro hj
    exact hno ⟨j,Or.inl hj⟩ hj
  refine ⟨hall,?_,?_⟩
  · obtain ⟨j,hj⟩ := hfive
    obtain ⟨i,hi⟩ := j.property.resolve_left (hall j)
    exact ⟨i,j,hi.trans hj,hj⟩
  · obtain ⟨j,hj⟩ := hseven
    obtain ⟨i,hi⟩ := j.property.resolve_left (hall j)
    exact ⟨i,j,hi.trans hj,hj⟩

/-- A factor-three exception forces at least six residual labels. -/
theorem residual_card_six_of_three {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j)
    (hex : ∃ j, 3 ∣ d j) :
    6 ≤ Fintype.card {j // Residual m d j} := by
  classical
  by_contra hsmall
  have hh := (residual_five_rigidity m a hinj hm h3 d b hdi hd hcover (by omega)).1
  obtain ⟨j,hj⟩ := hex
  exact hh j hj

/-- Every exception in a repair using at most five distinct labels must
already occur as a base modulus. -/
theorem five_extras_duplicate {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hdi : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (hJ : Fintype.card J ≤ 5)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) :
    ∀ j, ∃ i, m i=d j := by
  classical
  have hlow := residual_card_five m a hinj hm h3 d b hdi hd hcover
  have hno := (prime_constraints m a hinj hm h3 d b hdi hd hJ hcover).1
  intro j
  by_contra hj
  have hr : ¬ Residual m d j := by
    rintro (hthree | hdup)
    · exact hno j hthree
    · exact hj hdup
  have hlt := Fintype.card_subtype_lt (p := Residual m d) (x := j) hr
  simp only [Fintype.card_subtype] at hlow hlt
  omega

#print axioms residual_card_five
#print axioms residual_five_rigidity
#print axioms residual_card_six_of_three
#print axioms five_extras_duplicate
end Erdos7ExceptionAbsorption
