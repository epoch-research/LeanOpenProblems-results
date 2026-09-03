import Submission.SharedBranchBudget

/-! Exact compression of grouped prime-power constraints to two deepest
cylinders, with an explicit compatibility condition. This is a local signature
theorem, not an unrestricted bound on the union of all covering signatures. -/
namespace Erdos7PrimePowerCoreSignature
open scoped BigOperators
open Erdos7PresentCylinderArithmetic Erdos7IndependentPureLifts
set_option autoImplicit false
set_option maxHeartbeats 2000000

section
variable {J : Type*}

/-- One deepest representative from each nonempty group. -/
theorem exists_deepest_pair (s : Finset J) (g : J → Fin 2) (e : J → ℕ)
    (hg : ∀ r : Fin 2, ∃ j ∈ s, g j=r) :
    ∃ k : Fin 2 → J, (∀ r, k r ∈ s ∧ g (k r)=r) ∧
      ∀ j ∈ s, e j ≤ e (k (g j)) := by
  classical
  have hn (r : Fin 2) : (s.filter (fun j => g j=r)).Nonempty := by
    obtain ⟨j,hj,hgr⟩ := hg r
    exact ⟨j,Finset.mem_filter.mpr ⟨hj,hgr⟩⟩
  choose k hk hmax using fun r => Finset.exists_max_image (s.filter (fun j => g j=r)) e (hn r)
  refine ⟨k,fun r => Finset.mem_filter.mp (hk r),?_⟩
  intro j hj
  exact hmax (g j) j (Finset.mem_filter.mpr ⟨hj,rfl⟩)

def Compatible (p : ℕ) (s : Finset J) (g : J → Fin 2) (e : J → ℕ)
    (a : J → ℤ) (k : Fin 2 → J) : Prop :=
  ∀ j ∈ s, ((p^e j : ℕ) : ℤ) ∣ a (k (g j))-a j

/-- Every group intersection is either empty or exactly its deepest cylinder.
Compatibility is not presumed and is independent of the selected lifts. -/
theorem constraints_iff_deepest (p : ℕ) (s : Finset J) (g : J → Fin 2)
    (e : J → ℕ) (a : J → ℤ) (k : Fin 2 → J)
    (hk : ∀ r, k r ∈ s ∧ g (k r)=r)
    (hmax : ∀ j ∈ s, e j ≤ e (k (g j))) (z : Fin 2 → ℤ) :
    (∀ j ∈ s, ((p^e j : ℕ) : ℤ) ∣ z (g j)-a j) ↔
      Compatible p s g e a k ∧ ∀ r : Fin 2,
        ((p^e (k r) : ℕ) : ℤ) ∣ z r-a (k r) := by
  have hd (j : J) (hj : j ∈ s) : ((p^e j : ℕ) : ℤ) ∣ ((p^e (k (g j)) : ℕ) : ℤ) := by
    exact_mod_cast pow_dvd_pow p (hmax j hj)
  constructor
  · intro h
    have hdeep (r : Fin 2) := h (k r) (hk r).1
    simp only [(hk _).2] at hdeep
    refine ⟨?_,hdeep⟩
    intro j hj
    convert dvd_sub (h j hj) ((hd j hj).trans (hdeep (g j))) using 1 <;> ring
  · rintro ⟨hc,hdp⟩ j hj
    convert dvd_add ((hd j hj).trans (hdp (g j))) (hc j hj) using 1 <;> ring

lemma constraints_pair_iff (p : ℕ) (s : Finset J) (g : J → Fin 2)
    (e : J → ℕ) (a : J → ℤ) (k : Fin 2 → J)
    (hk : ∀ r, k r ∈ s ∧ g (k r)=r)
    (hmax : ∀ j ∈ s, e j ≤ e (k (g j))) (x y : ℤ) :
    (∀ j ∈ s, ((p^e j : ℕ) : ℤ) ∣ (if g j=0 then x else y)-a j) ↔
      Compatible p s g e a k ∧
      ((p^e (k 0) : ℕ) : ℤ) ∣ x-a (k 0) ∧
      ((p^e (k 1) : ℕ) : ℤ) ∣ y-a (k 1) := by
  have hh := constraints_iff_deepest p s g e a k hk hmax (fun r => if r=0 then x else y)
  simpa only [Fin.forall_fin_two,if_pos rfl,show (1 : Fin 2) ≠ 0 by decide,if_false] using hh

/-- Bound the probability of ALL constraints, not the product of their separate
probabilities. Constraints in a single branch are correlated and have already
been combined into their deepest cylinder. Incompatible groups have mass zero. -/
theorem all_constraints_fraction_le (p E : ℕ) [NeZero p] (hp : 3 ≤ p) (hE : 1 ≤ E)
    (pure : ℕ → ℤ) (b c : ℤ) (hbc : ¬ (p : ℤ) ∣ c-b)
    (s : Finset J) (g : J → Fin 2) (e : J → ℕ) (a : J → ℤ)
    (he : ∀ j ∈ s, e j ≤ E) (k : Fin 2 → J)
    (hk : ∀ r, k r ∈ s ∧ g (k r)=r)
    (hmax : ∀ j ∈ s, e j ≤ e (k (g j))) :
    letI : Decidable (Compatible p s g e a k) := Classical.propDecidable _
    let S := branchGood p E pure b
    let T := branchGood p E pure c
    let P := fun x : ZMod (p^E) × ZMod (p^E) => ∀ j ∈ s,
      ((p^e j : ℕ) : ℤ) ∣ (if g j=0 then (x.1.val : ℤ) else (x.2.val : ℤ))-a j
    letI : DecidablePred P := Classical.decPred _
    (((S ×ˢ T).filter P).card : ℚ)/(S ×ˢ T).card ≤
      if Compatible p s g e a k then
        ((p-1)/(p-2) : ℚ)*p^2*((p : ℚ)⁻¹)^(e (k 0)+e (k 1)) else 0 := by
  classical
  dsimp only
  letI : Decidable (Compatible p s g e a k) := Classical.propDecidable _
  let S := branchGood p E pure b
  let T := branchGood p E pure c
  let P := fun x : ZMod (p^E) × ZMod (p^E) => ∀ j ∈ s,
    ((p^e j : ℕ) : ℤ) ∣ (if g j=0 then (x.1.val : ℤ) else (x.2.val : ℤ))-a j
  letI : DecidablePred P := Classical.decPred _
  have hset : (S ×ˢ T).filter P = if Compatible p s g e a k then
      (S ×ˢ T).filter (fun x => x.1 ∈ cylinder p E (e (k 0)) (a (k 0)) ∧
        x.2 ∈ cylinder p E (e (k 1)) (a (k 1))) else ∅ := by
    ext x
    have hh := constraints_pair_iff p s g e a k hk hmax (x.1.val : ℤ) (x.2.val : ℤ)
    by_cases hc : Compatible p s g e a k
    · simp only [if_pos hc,Finset.mem_filter,mem_cylinder]
      exact and_congr_right (fun _ => by simpa only [hc,true_and] using hh)
    · simp only [if_neg hc,Finset.notMem_empty,Finset.mem_filter,iff_false]
      rintro ⟨_,hx⟩
      exact hc (hh.mp hx).1
  change (((S ×ˢ T).filter P).card : ℚ)/(S ×ˢ T).card ≤ _
  rw [hset]
  by_cases hc : Compatible p s g e a k
  · simp only [if_pos hc]
    exact Erdos7SharedBranchBudget.branch_pair_hit_fraction_le p E (e (k 0)) (e (k 1))
      hp hE (he _ (hk 0).1) (he _ (hk 1).1) pure b c (a (k 0)) (a (k 1)) hbc
  · simp [hc]

end
#print axioms exists_deepest_pair
#print axioms constraints_iff_deepest
#print axioms all_constraints_fraction_le
end Erdos7PrimePowerCoreSignature
