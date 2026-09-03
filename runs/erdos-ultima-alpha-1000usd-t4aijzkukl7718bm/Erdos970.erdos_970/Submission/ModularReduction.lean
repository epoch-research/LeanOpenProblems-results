import Submission.TwoSurvivorReduction

/-!
The exact modular separation condition for adjoining one new prime.
No unproved estimate is asserted here.
-/
namespace Erdos970.IncrementReduction

/-- Every choice of old classes leaves survivors in two different classes modulo `p`. -/
def PrimeSetModularBound (P : Finset ℕ) (p m : ℕ) : Prop :=
  ∀ r : ℕ → ℕ, ∃ i < m, ∃ j < m,
    (∀ q ∈ P, ¬i ≡ r q [MOD q]) ∧
    (∀ q ∈ P, ¬j ≡ r q [MOD q]) ∧ ¬i ≡ j [MOD p]

theorem primeSetModularBound_of_insert {P : Finset ℕ} {p m : ℕ}
    (hp : p ∉ P) (h : PrimeSetBound (insert p P) m) :
    PrimeSetModularBound P p m := by
  classical
  intro r
  obtain ⟨i, hi, hia⟩ := h (Function.update r p 0)
  obtain ⟨j, hj, hja⟩ := h (Function.update r p i)
  have hne (q : ℕ) (hq : q ∈ P) : q ≠ p := by
    intro hqp
    exact hp (hqp ▸ hq)
  refine ⟨i, hi, j, hj, ?_, ?_, ?_⟩
  · intro q hq
    simpa [Function.update_of_ne (hne q hq)] using
      hia q (Finset.mem_insert_of_mem hq)
  · intro q hq
    simpa [Function.update_of_ne (hne q hq)] using
      hja q (Finset.mem_insert_of_mem hq)
  · intro hij
    have hh := hja p (Finset.mem_insert_self _ _)
    apply hh
    simpa using hij.symm

theorem primeSetBound_insert_of_modular {P : Finset ℕ} {p m : ℕ}
    (h : PrimeSetModularBound P p m) : PrimeSetBound (insert p P) m := by
  intro r
  obtain ⟨i, hi, j, hj, hia, hja, hij⟩ := h r
  by_cases hip : i ≡ r p [MOD p]
  · refine ⟨j, hj, ?_⟩
    intro q hq hjq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hij (hip.trans hjq.symm)
    · exact hja q hq hjq
  · refine ⟨i, hi, ?_⟩
    intro q hq hiq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hip hiq
    · exact hia q hq hiq

/-- Unlike the two-survivor equivalence, this requires no comparison of `p` with a gap bound. -/
theorem primeSetBound_insert_iff_modular {P : Finset ℕ} {p m : ℕ}
    (hp : p ∉ P) : PrimeSetBound (insert p P) m ↔ PrimeSetModularBound P p m :=
  ⟨primeSetModularBound_of_insert hp, primeSetBound_insert_of_modular⟩

/-- The increment route is exactly a claim about modular separation of old survivors. -/
theorem largestPrimeIncrement_iff_modular : LargestPrimeIncrement ↔
    ∀ (P : Finset ℕ) (p g : ℕ), P.Nonempty → p.Prime →
      (∀ q ∈ P, q.Prime ∧ q < p) →
      PrimeSetBound P g → PrimeSetModularBound P p (g + 2 * P.card) := by
  constructor
  · intro h P p g hne hp hP hg
    have hpP : p ∉ P := fun hh => (hP p hh).2.false
    exact primeSetModularBound_of_insert hpP (h P p g hne hp hP hg)
  · intro h P p g hne hp hP hg
    exact primeSetBound_insert_of_modular (h P p g hne hp hP hg)

#print axioms primeSetBound_insert_iff_modular
#print axioms largestPrimeIncrement_iff_modular
end Erdos970.IncrementReduction
