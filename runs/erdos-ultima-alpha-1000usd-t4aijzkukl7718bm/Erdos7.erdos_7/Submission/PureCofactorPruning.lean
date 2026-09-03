import FormalConjecturesUtil

/-! Arithmetic parent-slice pruning for pure cofactor classes.
These conditional facts do not exclude odd covering systems. -/
namespace Erdos7PureCofactorPruning
set_option autoImplicit false

/-- A class whose modulus divides the parent modulus covers the entire parent
slice as soon as it meets that slice. -/
theorem covers_parent_of_meets (d m : ℕ) (r a : ℤ) (hdm : d ∣ m)
    (hmeet : ∃ y : ℤ, (m : ℤ) ∣ y-a ∧ (d : ℤ) ∣ y-r) :
    ∀ x : ℤ, (m : ℤ) ∣ x-a → (d : ℤ) ∣ x-r := by
  obtain ⟨y, hym, hyr⟩ := hmeet
  have hdm' : (d : ℤ) ∣ (m : ℤ) := by exact_mod_cast hdm
  intro x hxm
  have h := dvd_add (dvd_sub (hdm'.trans hxm) (hdm'.trans hym)) hyr
  convert h using 1 <;> ring

/-- If a terminal divisor at a prime child cannot replace the parent, it
retains the full exponent of that split prime. -/
theorem quotient_coprime_of_not_covers (p m d : ℕ) (hp : Nat.Prime p)
    (hd : d ∣ m*p) (r a : ℤ)
    (hmeet : ∃ y : ℤ, (m : ℤ) ∣ y-a ∧ (d : ℤ) ∣ y-r)
    (hnot : ¬ ∀ x : ℤ, (m : ℤ) ∣ x-a → (d : ℤ) ∣ x-r) :
    p.Coprime ((m*p)/d) := by
  have hnew : ¬ d ∣ m := fun hdm =>
    hnot (covers_parent_of_meets d m r a hdm hmeet)
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  have hmul : d*p ∣ m*p := (Nat.dvd_div_iff_mul_dvd hd).mp hdiv
  exact hnew (Nat.dvd_of_mul_dvd_mul_right hp.pos hmul)

/-- Divisibility of just the cofactor is insufficient for a class with a
nontrivial core factor: the 15-class does not cover the 3-slice. -/
lemma nonpure_control : (3 : ℕ) ∣ 3 ∧
    ¬ (∀ x : ℤ, (3 : ℤ) ∣ x → (15 : ℤ) ∣ x) := by
  refine ⟨dvd_rfl, ?_⟩
  intro h
  have := h 3 dvd_rfl
  norm_num at this

#print axioms covers_parent_of_meets
#print axioms quotient_coprime_of_not_covers
#print axioms nonpure_control
end Erdos7PureCofactorPruning
