import FormalConjecturesUtil

/-! A finite injective divisor assignment can be made divisor-closed while
only decreasing each assigned modulus. Coverage is not assumed. -/
namespace Erdos7DownwardDivisorAssignment
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Downward reassignment preserves the number of distinct resources and
makes their image closed under taking nontrivial divisors. Each source keeps
a divisor of its OWN original resource, not merely a common-period divisor. -/
theorem exists_closed {I : Type*} [Fintype I] (f : I → ℕ)
    (hinj : Function.Injective f) (h1 : ∀ i, 1 < f i) :
    ∃ g : I → ℕ, Function.Injective g ∧ (∀ i, 1 < g i ∧ g i ∣ f i) ∧
      (∑ i, g i) ≤ ∑ i, f i ∧
      ∀ i d, 1 < d → d ∣ g i → ∃ j, g j=d := by
  classical
  let P (w : ℕ) := ∃ g : I → ℕ, Function.Injective g ∧
    (∀ i, 1 < g i ∧ g i ∣ f i) ∧ ∑ i, g i=w
  have hex : ∃ w, P w := ⟨∑ i, f i,f,hinj,fun i => ⟨h1 i,dvd_refl _⟩,rfl⟩
  obtain ⟨g,hgi,hg,hsum⟩ := Nat.find_spec hex
  refine ⟨g,hgi,hg,?_,?_⟩
  · rw [hsum]
    exact Nat.find_min' hex ⟨f,hinj,fun i => ⟨h1 i,dvd_refl _⟩,rfl⟩
  · intro i d hd hdg
    by_contra! hmissing
    let g' := Function.update g i d
    have hlt : d < g i := Nat.lt_of_le_of_ne
      (Nat.le_of_dvd (by have := (hg i).1; omega) hdg) (hmissing i).symm
    have hg'i : Function.Injective g' := by
      intro j k hjk
      by_cases hji : j=i <;> by_cases hki : k=i
      · exact hji.trans hki.symm
      · subst j
        have hh : d=g k := by simpa [g',hki] using hjk
        exact (hmissing k hh.symm).elim
      · subst k
        have hh : g j=d := by simpa [g',hji] using hjk
        exact (hmissing j hh).elim
      · apply hgi
        simpa [g',hji,hki] using hjk
    have hg' (j : I) : 1 < g' j ∧ g' j ∣ f j := by
      by_cases hji : j=i
      · subst j
        simpa [g'] using And.intro hd (hdg.trans (hg i).2)
      · simpa [g',hji] using hg j
    have hslt : (∑ j, g' j) < ∑ j, g j := by
      dsimp only [g']
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      have hs := Finset.sum_erase_add (Finset.univ : Finset I) g (Finset.mem_univ i)
      have he : (Finset.univ : Finset I) \ {i}=Finset.univ.erase i := by ext j; simp
      rw [he]
      omega
    have hP : P (∑ j, g' j) := ⟨g',hg'i,hg',rfl⟩
    have hh := Nat.find_min' hex hP
    omega

/-- Consequently, if any injective assignment of nontrivial divisors to
leaf moduli exists, one with a divisor-closed image exists as well. -/
theorem closed_assignment_iff {I : Type*} [Fintype I] (m : I → ℕ) :
    (∃ f : I → ℕ, Function.Injective f ∧ ∀ i, 1 < f i ∧ f i ∣ m i) ↔
    ∃ g : I → ℕ, Function.Injective g ∧ (∀ i, 1 < g i ∧ g i ∣ m i) ∧
      ∀ i d, 1 < d → d ∣ g i → ∃ j, g j=d := by
  constructor
  · rintro ⟨f,hfi,hf⟩
    obtain ⟨g,hgi,hg,_,hclosed⟩ := exists_closed f hfi (fun i => (hf i).1)
    exact ⟨g,hgi,fun i => ⟨(hg i).1,(hg i).2.trans (hf i).2⟩,hclosed⟩
  · rintro ⟨g,hgi,hg,_⟩
    exact ⟨g,hgi,hg⟩

/-- The new congruences contain the old ones, with residues unchanged. -/
theorem enlarged_congruences {I : Type*} [Fintype I]
    (f : I → ℕ) (a : I → ℤ) (hinj : Function.Injective f) (h1 : ∀ i, 1 < f i) :
    ∃ g : I → ℕ, Function.Injective g ∧ (∀ i, 1 < g i ∧ g i ∣ f i) ∧
      (∀ i d, 1 < d → d ∣ g i → ∃ j, g j=d) ∧
      ∀ i x, (f i : ℤ) ∣ x-a i → (g i : ℤ) ∣ x-a i := by
  obtain ⟨g,hgi,hg,_,hc⟩ := exists_closed f hinj h1
  refine ⟨g,hgi,hg,hc,fun i x hx => ?_⟩
  exact (show (g i : ℤ) ∣ (f i : ℤ) by exact_mod_cast (hg i).2).trans hx

#print axioms exists_closed
#print axioms closed_assignment_iff
#print axioms enlarged_congruences
end Erdos7DownwardDivisorAssignment
