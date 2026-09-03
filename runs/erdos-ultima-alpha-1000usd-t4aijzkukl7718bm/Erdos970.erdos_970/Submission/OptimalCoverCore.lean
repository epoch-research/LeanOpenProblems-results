import Submission.Work

/-! Structural properties of a minimum-cost prime-class cover core. -/
namespace Erdos970.OptimalCoverCore

noncomputable def survivors (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun i => ∀ p ∈ P, ¬i ≡ r p [MOD p])

noncomputable def budget (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ) : ℕ :=
  P.card + (survivors m P r).card

/-- First minimize total cost, then minimize the number of retained prime classes. -/
def IsOptimal (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ) : Prop :=
  (∀ p ∈ P, p.Prime) ∧
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∀ s : ℕ → ℕ,
    budget m P r ≤ budget m Q s) ∧
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∀ s : ℕ → ℕ,
    budget m Q s = budget m P r → P.card ≤ Q.card)

theorem exists_optimal (m : ℕ) : ∃ P r, IsOptimal m P r := by
  classical
  have hex : ∃ b : ℕ, ∃ P : Finset ℕ, ∃ r : ℕ → ℕ,
      (∀ p ∈ P, p.Prime) ∧ budget m P r = b := by
    exact ⟨budget m ∅ (fun _ => 0), ∅, (fun _ => 0), by simp, rfl⟩
  obtain ⟨P₀, r₀, hP₀, hb₀⟩ := Nat.find_spec hex
  have hex' : ∃ c : ℕ, ∃ P : Finset ℕ, ∃ r : ℕ → ℕ,
      (∀ p ∈ P, p.Prime) ∧ budget m P r = Nat.find hex ∧ P.card = c :=
    ⟨P₀.card, P₀, r₀, hP₀, hb₀, rfl⟩
  obtain ⟨P, r, hP, hb, hc⟩ := Nat.find_spec hex'
  refine ⟨P, r, hP, ?_, ?_⟩
  · intro Q hQ s
    rw [hb]
    exact Nat.find_min' hex ⟨Q, s, hQ, rfl⟩
  · intro Q hQ s heq
    rw [hc]
    exact Nat.find_min' hex' ⟨Q, s, hQ, heq.trans hb, rfl⟩

theorem mem_survivors (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ) (i : ℕ) :
    i ∈ survivors m P r ↔ i < m ∧ ∀ p ∈ P, ¬i ≡ r p [MOD p] := by
  simp [survivors]

theorem optimal_budget_le_length {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) : budget m P r ≤ m := by
  simpa [budget, survivors] using h.2.1 ∅ (by simp) (fun _ => 0)

theorem survivors_insert_update (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p a : ℕ) (hp : p ∉ P) :
    survivors m (insert p P) (Function.update r p a) =
      (survivors m P r).filter (fun i => ¬i ≡ a [MOD p]) := by
  classical
  ext i
  simp only [mem_survivors, Finset.mem_filter, Finset.forall_mem_insert]
  constructor
  · rintro ⟨him, hip, hiP⟩
    refine ⟨⟨him, ?_⟩, ?_⟩
    · intro q hq
      have hqp : q ≠ p := by rintro rfl; exact hp hq
      simpa [Function.update_of_ne hqp] using hiP q hq
    · simpa using hip
  · rintro ⟨⟨him, hiP⟩, hip⟩
    refine ⟨him, by simpa using hip, ?_⟩
    intro q hq
    have hqp : q ≠ p := by rintro rfl; exact hp hq
    simpa [Function.update_of_ne hqp] using hiP q hq

/-- A new prime cannot hit two remaining positions in a minimum-cost configuration. -/
theorem unused_prime_hits_at_most_one {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (p a : ℕ) (hp : p.Prime) (hpP : p ∉ P) :
    ((survivors m P r).filter (fun i => i ≡ a [MOD p])).card ≤ 1 := by
  classical
  have hnew : ∀ q ∈ insert p P, q.Prime := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact h.1 q hq
  have hh := h.2.1 (insert p P) hnew (Function.update r p a)
  simp only [budget, Finset.card_insert_of_notMem hpP,
    survivors_insert_update m P r p a hpP] at hh
  have hpart := Finset.card_filter_add_card_filter_not
    (s := survivors m P r) (fun i => i ≡ a [MOD p])
  omega

/-- Remaining positions occupy distinct classes modulo every unused prime. -/
theorem unused_prime_injective {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (p : ℕ) (hp : p.Prime) (hpP : p ∉ P) :
    Set.InjOn (fun i => i % p) (↑(survivors m P r) : Set ℕ) := by
  classical
  intro i hi j hj hij
  have hcard := unused_prime_hits_at_most_one h p i hp hpP
  have hi' : i ∈ (survivors m P r).filter (fun x => x ≡ i [MOD p]) :=
    Finset.mem_filter.mpr ⟨hi, Nat.ModEq.refl i⟩
  have hj' : j ∈ (survivors m P r).filter (fun x => x ≡ i [MOD p]) :=
    Finset.mem_filter.mpr ⟨hj, hij.symm⟩
  exact (Finset.card_le_one.mp hcard) i hi' j hj'

/-- Every prime below the number of remaining positions is necessarily already used. -/
theorem prime_lt_survivor_card_mem {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (p : ℕ) (hp : p.Prime)
    (hps : p < (survivors m P r).card) : p ∈ P := by
  classical
  by_contra hpP
  have hc := Finset.card_le_card_of_injOn (s := survivors m P r) (t := Finset.range p)
    (fun i => i % p) (fun i hi => Finset.mem_range.mpr (Nat.mod_lt _ hp.pos))
    (unused_prime_injective h p hp hpP)
  simp only [Finset.card_range] at hc
  omega

/-- All prime divisors of a difference between two remaining positions belong to the core. -/
theorem survivor_difference_primeFactors_subset {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) {i j : ℕ}
    (hi : i ∈ survivors m P r) (hj : j ∈ survivors m P r) (hij : i < j) :
    (j - i).primeFactors ⊆ P := by
  classical
  intro p hp
  have hp' := Nat.mem_primeFactors.mp hp
  by_contra hpP
  have hmod : i ≡ j [MOD p] := (Nat.modEq_iff_dvd' hij.le).mpr hp'.2.1
  have heq := unused_prime_injective h p hp'.1 hpP hi hj hmod
  omega

noncomputable def privatePositions (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ) (p : ℕ) : Finset ℕ :=
  (survivors m (P.erase p) r).filter (fun i => i ≡ r p [MOD p])

theorem survivors_erase_partition (m : ℕ) (P : Finset ℕ) (r : ℕ → ℕ)
    (p : ℕ) (hp : p ∈ P) :
    (survivors m (P.erase p) r).card =
      (privatePositions m P r p).card + (survivors m P r).card := by
  classical
  have heq : (survivors m (P.erase p) r).filter (fun i => ¬i ≡ r p [MOD p]) =
      survivors m P r := by
    ext i
    simp only [Finset.mem_filter, mem_survivors]
    constructor
    · rintro ⟨⟨him, hiP⟩, hip⟩
      refine ⟨him, fun q hq => ?_⟩
      by_cases hqp : q = p
      · simpa [hqp] using hip
      · exact hiP q (Finset.mem_erase.mpr ⟨hqp, hq⟩)
    · rintro ⟨him, hiP⟩
      exact ⟨⟨him, fun q hq => hiP q (Finset.mem_of_mem_erase hq)⟩, hiP p hp⟩
  have hh := Finset.card_filter_add_card_filter_not
    (s := survivors m (P.erase p) r) (fun i => i ≡ r p [MOD p])
  rw [heq] at hh
  exact hh.symm

/-- Secondary minimization removes every class with fewer than two private positions. -/
theorem used_prime_private_card_ge_two {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (p : ℕ) (hp : p ∈ P) :
    2 ≤ (privatePositions m P r p).card := by
  classical
  have hP' : ∀ q ∈ P.erase p, q.Prime := fun q hq => h.1 q (Finset.mem_of_mem_erase hq)
  have hmin := h.2.1 (P.erase p) hP' r
  have hpart := survivors_erase_partition m P r p hp
  have hcard := Finset.card_erase_add_one hp
  by_contra hbad
  have heq : budget m (P.erase p) r = budget m P r := by
    unfold budget at hmin ⊢
    omega
  have hsecondary := h.2.2 (P.erase p) hP' r heq
  omega

/-- Every retained prime is smaller than the interval length; otherwise its class has at
most one private point and would have been discarded. -/
theorem used_prime_lt_length {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (p : ℕ) (hp : p ∈ P) : p < m := by
  classical
  by_contra hpm
  have hcard : (privatePositions m P r p).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    have him := ((mem_survivors m (P.erase p) r i).mp hi'.1).1
    have hjm := ((mem_survivors m (P.erase p) r j).mp hj'.1).1
    exact (hi'.2.trans hj'.2.symm).eq_of_lt_of_lt (by omega) (by omega)
  have := used_prime_private_card_ge_two h p hp
  omega

/-- The minimum cover budget is an exact inverse criterion for the Jacobsthal bound. -/
theorem isJacobsthalBound_iff_optimal_budget {m : ℕ} {P : Finset ℕ} {r : ℕ → ℕ}
    (h : IsOptimal m P r) (k : ℕ) :
    IsJacobsthalBound k m ↔ k < budget m P r := by
  classical
  constructor
  · intro hb
    have hh := (isJacobsthalBound_iff_small_prime_budget k m).mp hb P
      (fun p hp => ⟨h.1 p hp, used_prime_lt_length h p hp⟩) r
    exact hh
  · intro hk
    by_contra hb
    obtain ⟨Q, hQ, hQk, s, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hb
    have he : survivors m Q s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hi' := (mem_survivors m Q s i).mp hi
      obtain ⟨p, hp, hip⟩ := hcover i hi'.1
      exact hi'.2 p hp hip
    have hh := h.2.1 Q hQ s
    simp only [budget, he, Finset.card_empty, Nat.add_zero] at hh
    unfold budget at hk
    omega

#print axioms exists_optimal
#print axioms unused_prime_injective
#print axioms survivor_difference_primeFactors_subset
#print axioms used_prime_private_card_ge_two
#print axioms isJacobsthalBound_iff_optimal_budget

end Erdos970.OptimalCoverCore
