import FormalConjecturesUtil

/-!
A static Shearer-criterion limitation using a star of odd congruence classes.
This is an auxiliary noncoverage example, NOT a solution of Erdős Problem 7.
-/
namespace Erdos7StaticShearerBarrier
open scoped BigOperators

lemma sum_le_erase_add {I : Type*} [DecidableEq I] (s : Finset I)
    (f : I → ℝ) (i : I) (hi : 0 ≤ f i) :
    ∑ j ∈ s, f j ≤ (∑ j ∈ s.erase i, f j) + f i := by
  by_cases h : i ∈ s
  · exact (Finset.sum_erase_add s f h).ge
  · simp only [Finset.erase_eq_of_notMem h]
    linarith

lemma prime_reciprocal_sums_unbounded (B : ℝ) :
    ∃ s : Finset Nat.Primes, B < ∑ p ∈ s, (1 / (p : ℝ)) := by
  by_contra! h
  exact Nat.Primes.not_summable_one_div
    (summable_of_sum_le (fun p => by positivity) h)

lemma large_prime_reciprocal_sum :
    ∃ s : Finset Nat.Primes, (∀ p ∈ s, 3 < (p : ℕ)) ∧
      6 < ∑ p ∈ s, (1 / (p : ℝ)) := by
  classical
  obtain ⟨t, ht⟩ := prime_reciprocal_sums_unbounded 8
  let two : Nat.Primes := ⟨2, by decide⟩
  let three : Nat.Primes := ⟨3, by decide⟩
  let s := (t.erase two).erase three
  have h₂ := sum_le_erase_add t (fun p : Nat.Primes => (1 / (p : ℝ))) two (by positivity)
  have h₃ := sum_le_erase_add (t.erase two) (fun p : Nat.Primes => (1 / (p : ℝ))) three (by positivity)
  have h₂v : (1 / (two : ℝ)) = 1/2 := rfl
  have h₃v : (1 / (three : ℝ)) = 1/3 := rfl
  dsimp only at h₂ h₃
  rw [h₂v] at h₂
  rw [h₃v] at h₃
  refine ⟨s, ?_, by dsimp [s]; linarith⟩
  intro p hp
  have hp₃ : p ≠ three := (Finset.mem_erase.mp hp).1
  have hp₂ : p ≠ two := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
  have hne₂ : (p : ℕ) ≠ 2 := fun h => hp₂ (Subtype.ext h)
  have hne₃ : (p : ℕ) ≠ 3 := fun h => hp₃ (Subtype.ext h)
  have hmin := p.property.two_le
  omega

/-- An elementary finite product bound; no logarithms or numerical estimates. -/
lemma product_complement_bound {I : Type*} (s : Finset I) (w : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) :
    (1 + ∑ i ∈ s, w i) * (∏ i ∈ s, (1-w i)) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hwa := hw a (Finset.mem_insert_self _ _)
      have hws : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1 := fun i hi => hw i (Finset.mem_insert_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg (fun i hi => (hws i hi).1)
      have hprod : 0 ≤ ∏ i ∈ s, (1-w i) := Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (hws i hi).2)
      have hsquare : 0 ≤ (w a)^2 := sq_nonneg _
      have hcross : 0 ≤ w a * (∑ i ∈ s, w i) := mul_nonneg hwa.1 hsum
      have hfac : (1 + (w a + ∑ i ∈ s, w i)) * (1-w a) ≤ 1 + ∑ i ∈ s, w i := by nlinarith
      rw [Finset.sum_insert ha, Finset.prod_insert ha, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right hfac hprod).trans (ih hws)

/-- This is the weighted independence polynomial of a star: independent sets
are either an arbitrary subset of leaves, or the singleton center. -/
noncomputable def starPolynomial (s : Finset Nat.Primes) : ℝ :=
  (∑ t ∈ s.powerset, ∏ p ∈ t, -(1 / (3 * (p : ℝ)))) - 1/3

lemma starPolynomial_eq (s : Finset Nat.Primes) :
    starPolynomial s = (∏ p ∈ s, (1 - 1/(3*(p : ℝ)))) - 1/3 := by
  unfold starPolynomial
  rw [← Finset.prod_one_add]
  simp only [sub_eq_add_neg]

theorem exists_negative_star_polynomial :
    ∃ s : Finset Nat.Primes, (∀ p ∈ s, 3 < (p : ℕ)) ∧ starPolynomial s < 0 := by
  obtain ⟨s, hs, hsum⟩ := large_prime_reciprocal_sum
  let w : Nat.Primes → ℝ := fun p => 1/(3*(p : ℝ))
  have hw : ∀ p ∈ s, 0 ≤ w p ∧ w p ≤ 1 := by
    intro p hp
    have hpos : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.pos
    have hlarge : (3 : ℝ) < (p : ℕ) := by exact_mod_cast hs p hp
    dsimp [w]
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < 3*(p : ℝ))).mpr
      nlinarith
  have htotal : 2 < ∑ p ∈ s, w p := by
    have heq : (∑ p ∈ s, w p) = (∑ p ∈ s, (1/(p : ℝ))) / 3 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [w]
      ring
    rw [heq]
    linarith
  have hb := product_complement_bound s w hw
  have hnonneg : 0 ≤ ∏ p ∈ s, (1-w p) :=
    Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hw p hp).2)
  refine ⟨s, hs, ?_⟩
  rw [starPolynomial_eq]
  change (∏ p ∈ s, (1-w p)) - 1/3 < 0
  by_contra! hn
  nlinarith

/-- CRT with one ternary coordinate and finitely many larger prime coordinates. -/
lemma exists_coordinates (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 3 < (p : ℕ))
    (c : ℕ) (b : Nat.Primes → ℕ) :
    ∃ x : ℕ, Nat.ModEq 3 x c ∧ ∀ p ∈ s, Nat.ModEq (p : ℕ) x (b p) := by
  classical
  let three : Nat.Primes := ⟨3, by decide⟩
  let t := insert three s
  let a : Nat.Primes → ℕ := fun p => if p = three then c else b p
  have hcop : Set.Pairwise (t : Set Nat.Primes) (fun p q : Nat.Primes => Nat.Coprime (p : ℕ) (q : ℕ)) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes p.property q.property).mpr (fun h => hpq (Subtype.ext h))
  obtain ⟨x, hx⟩ := Nat.chineseRemainderOfFinset a (fun p : Nat.Primes => (p : ℕ)) t
    (fun p hp => p.property.ne_zero) hcop
  refine ⟨x, ?_, ?_⟩
  · simpa [a, three] using hx three (Finset.mem_insert_self _ _)
  · intro p hp
    have hpne : p ≠ three := by
      intro h
      have hh := hs p hp
      rw [h] at hh
      change 3 < 3 at hh
      omega
    simpa [a, hpne] using hx p (Finset.mem_insert_of_mem hp)

def modulus (s : Finset Nat.Primes) : Option s → ℕ
  | none => 3
  | some p => 3 * (p.val : ℕ)

def residue (s : Finset Nat.Primes) : Option s → ℕ
  | none => 0
  | some _ => 1

lemma modulus_injective (s : Finset Nat.Primes) : Function.Injective (modulus s) := by
  intro i j h
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some q =>
          have hq := q.val.property.two_le
          dsimp [modulus] at h
          omega
  | some p =>
      cases j with
      | none =>
          have hp := p.val.property.two_le
          dsimp [modulus] at h
          omega
      | some q =>
          apply congrArg some
          apply Subtype.ext
          apply Subtype.ext
          dsimp [modulus] at h
          omega

lemma odd_nontrivial (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 3 < (p : ℕ))
    (i : Option s) : Odd (modulus s i) ∧ 1 < modulus s i := by
  cases i with
  | none => change Odd (3 : ℕ) ∧ 1 < (3 : ℕ); decide
  | some p =>
      have hp := hs p.val p.property
      have ho : Odd (p.val : ℕ) := p.val.property.odd_of_ne_two (by omega)
      exact ⟨(by decide : Odd (3 : ℕ)).mul ho, by dsimp [modulus]; omega⟩

lemma nat_private (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 3 < (p : ℕ))
    (i : Option s) : ∃ x : ℕ, ∀ j, Nat.ModEq (modulus s j) x (residue s j) ↔ i=j := by
  classical
  cases i with
  | none =>
      refine ⟨0, ?_⟩
      intro j
      cases j with
      | none => simp [modulus, residue, Nat.ModEq]
      | some q =>
          have hq := q.val.property.two_le
          have hm : 1 < 3 * (q.val : ℕ) := by omega
          simp [modulus, residue, Nat.ModEq, Nat.mod_eq_of_lt hm]
  | some p =>
      obtain ⟨x, h₃, hx⟩ := exists_coordinates s hs 1 (fun q => if q=p.val then 1 else 0)
      refine ⟨x, ?_⟩
      intro j
      cases j with
      | none =>
          have hne : ¬ Nat.ModEq 3 x 0 := by
            intro h
            have hh := h₃.symm.trans h
            norm_num [Nat.ModEq] at hh
          simpa [modulus, residue] using hne
      | some q =>
          by_cases he : p=q
          · subst q
            have hp : Nat.ModEq (p.val : ℕ) x 1 := by simpa using hx p.val p.property
            have hc : Nat.Coprime 3 (p.val : ℕ) :=
              (Nat.coprime_primes (by decide) p.val.property).mpr (by have := hs p.val p.property; omega)
            have hh := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨h₃, hp⟩
            simpa [modulus, residue] using hh
          · have hv : q.val ≠ p.val := fun h => he (Subtype.ext h.symm)
            have hq : Nat.ModEq (q.val : ℕ) x 0 := by simpa [hv] using hx q.val q.property
            have hne : ¬ Nat.ModEq (3*(q.val : ℕ)) x 1 := by
              intro h
              have hh := (h.of_dvd (dvd_mul_left _ _)).symm.trans hq
              have hlt := q.val.property.one_lt
              norm_num [Nat.ModEq, Nat.mod_eq_of_lt hlt] at hh
            simpa [modulus, residue, he] using hne

lemma private_points (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 3 < (p : ℕ)) :
    ∀ i : Option s, ∃ x : ℤ, ∀ j,
      (modulus s j : ℤ) ∣ x-(residue s j : ℤ) ↔ i=j := by
  intro i
  obtain ⟨x, hx⟩ := nat_private s hs i
  refine ⟨(x : ℤ), ?_⟩
  intro j
  rw [dvd_sub_comm, ← Nat.modEq_iff_dvd]
  exact hx j

lemma two_uncovered (s : Finset Nat.Primes) :
    ∀ i : Option s, ¬ (modulus s i : ℤ) ∣ 2-(residue s i : ℤ) := by
  intro i
  cases i with
  | none => norm_num [modulus, residue]
  | some p =>
      change ¬ (3*(p.val : ℤ)) ∣ (2:ℤ)-1
      intro h
      have hh := (dvd_mul_right (3:ℤ) (p.val : ℤ)).trans h
      norm_num at hh

/-- The actual incompatibility graph is a star. Leaves all meet at integer1. -/
lemma incompatibility_star (s : Finset Nat.Primes) (i j : Option s) :
    (¬ ∃ z : ℤ, (modulus s i : ℤ) ∣ z-(residue s i : ℤ) ∧
      (modulus s j : ℤ) ∣ z-(residue s j : ℤ)) ↔
      (i=none ∧ j≠none) ∨ (j=none ∧ i≠none) := by
  cases i <;> cases j
  · apply iff_of_false ?_ (by simp)
    intro h
    exact h ⟨0, by simp [residue], by simp [residue]⟩
  · apply iff_of_true ?_ (by simp)
    rintro ⟨z, hz, hp⟩
    change (3:ℤ) ∣ z-0 at hz
    simp only [modulus, residue, Nat.cast_mul, Nat.cast_ofNat] at hp
    have hd : (3 : ℤ) ∣ z-1 := (dvd_mul_right (3:ℤ) _).trans hp
    have hh := dvd_sub hz hd
    norm_num at hh
  · apply iff_of_true ?_ (by simp)
    rintro ⟨z, hp, hz⟩
    change (3:ℤ) ∣ z-0 at hz
    simp only [modulus, residue, Nat.cast_mul, Nat.cast_ofNat] at hp
    have hd : (3 : ℤ) ∣ z-1 := (dvd_mul_right (3:ℤ) _).trans hp
    have hh := dvd_sub hz hd
    norm_num at hh
  · apply iff_of_false ?_ (by simp)
    intro h
    exact h ⟨1, by simp [residue], by simp [residue]⟩

/-- Static graph-polynomial positivity is not a universal certificate, even
for odd distinct classes having private points and a common uncovered point. -/
theorem exists_arithmetic_star_barrier :
    ∃ s : Finset Nat.Primes,
      Function.Injective (modulus s) ∧
      (∀ i, Odd (modulus s i) ∧ 1 < modulus s i) ∧
      (∀ i, ∃ x : ℤ, ∀ j, (modulus s j : ℤ) ∣ x-(residue s j : ℤ) ↔ i=j) ∧
      (∀ i, ¬ (modulus s i : ℤ) ∣ 2-(residue s i : ℤ)) ∧
      starPolynomial s < 0 := by
  obtain ⟨s, hs, hn⟩ := exists_negative_star_polynomial
  exact ⟨s, modulus_injective s, odd_nontrivial s hs, private_points s hs,
    two_uncovered s, hn⟩

#print axioms exists_arithmetic_star_barrier
#print axioms incompatibility_star


#print axioms exists_negative_star_polynomial
end Erdos7StaticShearerBarrier
