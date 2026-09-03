import Submission.PrimePowerCombFamily

/-! CRT realization and divisor-pattern tools for prime-power partial families.
These constructions retain private points and an uncovered point. -/
namespace Erdos7PrimePowerBoxRealization
open scoped BigOperators
open Finset
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p)

noncomputable def modulus (e : I → ℕ) : ℕ := ∏ i, p i ^ e i

include hp hpi

omit hpi in
lemma modulus_pos (e : I → ℕ) : 0 < modulus p e :=
  prod_pos (fun i _ => pow_pos (hp i).pos _)

lemma coprime : Pairwise (Function.onFun Nat.Coprime p) := by
  intro i j hij
  exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hpi h))

lemma factorization_at (e : I → ℕ) (i : I) : (modulus p e).factorization (p i) = e i := by
  rw [modulus, Nat.factorization_prod_apply (fun j _ => pow_ne_zero _ (hp j).ne_zero)]
  have hh : (∑ j, (p j ^ e j).factorization (p i)) = ∑ j, if j = i then e j else 0 := by
    apply sum_congr rfl
    intro j _
    rw [(hp j).factorization_pow, Finsupp.single_apply]
    simp [hpi.eq_iff]
  rw [hh]
  simp

omit hpi in
lemma factorization_outside (e : I → ℕ) (q : ℕ) (hq : ∀ i, p i ≠ q) :
    (modulus p e).factorization q = 0 := by
  rw [modulus, Nat.factorization_prod_apply (fun j _ => pow_ne_zero _ (hp j).ne_zero)]
  apply sum_eq_zero
  intro i _
  rw [(hp i).factorization_pow, Finsupp.single_apply]
  simp [hq i]

lemma modulus_injective : Function.Injective (modulus p) := by
  intro e f h
  funext i
  have hh := congrArg (fun n => n.factorization (p i)) h
  simpa only [factorization_at p hp hpi] using hh

/-- Divisors of a prime-power pattern correspond to coordinatewise smaller
patterns. This permits arbitrary finite downsets rather than rectangular caps. -/
theorem divisor_pattern (e : I → ℕ) (d : ℕ) (hd : d ∣ modulus p e) :
    ∃ f : I → ℕ, f ≤ e ∧ modulus p f = d := by
  classical
  have hm0 := (modulus_pos p hp e).ne'
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hm0 hd
  have hle := (Nat.factorization_le_iff_dvd hd0 hm0).mpr hd
  let f : I → ℕ := fun i => d.factorization (p i)
  refine ⟨f, ?_, ?_⟩
  · intro i
    simpa only [factorization_at p hp hpi] using hle (p i)
  · apply Nat.eq_of_factorization_eq (modulus_pos p hp f).ne' hd0
    intro q
    by_cases hq : ∃ i, p i = q
    · obtain ⟨i, rfl⟩ := hq
      exact factorization_at p hp hpi f i
    · have hout : ∀ i, p i ≠ q := by simpa using hq
      rw [factorization_outside p hp f q hout]
      have hh := hle q
      rw [factorization_outside p hp e q hout] at hh
      omega

lemma modulus_dvd_iff (e : I → ℕ) (x : ℤ) :
    (modulus p e : ℤ) ∣ x ↔ ∀ i, (p i : ℤ) ^ e i ∣ x := by
  constructor
  · intro h i
    have hd : p i ^ e i ∣ modulus p e := dvd_prod_of_mem _ (mem_univ i)
    exact (show (p i : ℤ) ^ e i ∣ (modulus p e : ℤ) by exact_mod_cast hd).trans h
  · intro h
    rw [modulus, Nat.cast_prod]
    simp only [Nat.cast_pow]
    apply prod_dvd_of_coprime
    · intro i _ j _ hij
      exact ((coprime p hp hpi hij).pow _ _).isCoprime
    · exact fun i _ => h i

/-- Simultaneous coordinates at arbitrary prime-power depths. -/
theorem integer_coordinates (E : I → ℕ) (x : I → ℤ) :
    ∃ z : ℤ, ∀ i, (p i : ℤ) ^ E i ∣ z - x i := by
  letI (i : I) : NeZero (p i) := ⟨(hp i).ne_zero⟩
  let z := Nat.chineseRemainderOfFinset (fun i => (x i : ZMod (p i ^ E i)).val)
    (fun i => p i ^ E i) univ (fun i _ => pow_ne_zero _ (hp i).ne_zero)
    (fun i _ j _ hij => (coprime p hp hpi hij).pow _ _)
  refine ⟨z.val, fun i => ?_⟩
  have hz : (z.val : ZMod (p i ^ E i)) = x i := by
    rw [← ZMod.natCast_zmod_val (x i : ZMod (p i ^ E i))]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (mem_univ _))
  have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (z.val : ℤ) (p i ^ E i)).mp
    (by simpa only [Int.cast_natCast] using hz.symm)
  simpa only [Nat.cast_pow] using hh

lemma realized_membership (E e : I → ℕ) (he : e ≤ E)
    (x r : I → ℤ) (z a : ℤ)
    (hz : ∀ i, (p i : ℤ) ^ E i ∣ z - x i)
    (ha : ∀ i, (p i : ℤ) ^ E i ∣ a - r i) :
    (modulus p e : ℤ) ∣ z - a ↔ ∀ i, (p i : ℤ) ^ e i ∣ x i - r i := by
  rw [modulus_dvd_iff p hp hpi]
  have hd (i : I) : (p i : ℤ) ^ e i ∣ (p i : ℤ) ^ E i := pow_dvd_pow _ (he i)
  constructor
  · intro h i
    convert dvd_add (dvd_sub (h i) ((hd i).trans (hz i))) ((hd i).trans (ha i)) using 1 <;> ring
  · intro h i
    convert dvd_sub (dvd_add (h i) ((hd i).trans (hz i))) ((hd i).trans (ha i)) using 1 <;> ring

/-- Generic realization of a finite-depth partial family, carrying its
private points and a simultaneously uncovered integer. -/
theorem realize_partial_family {J : Type*} (E : I → ℕ) (e : J → I → ℕ)
    (he : ∀ j, e j ≤ E) (r x : J → I → ℤ) (u : I → ℤ)
    (hpriv : ∀ j k, (∀ i, (p i : ℤ) ^ e k i ∣ x j i - r k i) ↔ k = j)
    (hu : ∀ k, ¬ ∀ i, (p i : ℤ) ^ e k i ∣ u i - r k i) :
    ∃ (a z : J → ℤ) (v : ℤ),
      (∀ j i, (p i : ℤ) ^ E i ∣ a j - r j i) ∧
      (∀ j k, ((modulus p (e k) : ℤ) ∣ z j - a k) ↔ k = j) ∧
      ∀ k, ¬ (modulus p (e k) : ℤ) ∣ v - a k := by
  classical
  choose a ha using fun j => integer_coordinates p hp hpi E (r j)
  choose z hz using fun j => integer_coordinates p hp hpi E (x j)
  obtain ⟨v, hv⟩ := integer_coordinates p hp hpi E u
  refine ⟨a, z, v, ha, ?_, ?_⟩
  · intro j k
    exact (realized_membership p hp hpi E (e k) (he k) (x j) (r k) (z j) (a k)
      (hz j) (ha k)).trans (hpriv j k)
  · intro k hk
    exact hu k ((realized_membership p hp hpi E (e k) (he k) u (r k) v (a k) hv (ha k)).mp hk)
end

#print axioms modulus_injective
#print axioms divisor_pattern
#print axioms realize_partial_family
end Erdos7PrimePowerBoxRealization
