import Submission.Spec

/-!
# An elementary factorial bound for Jacobsthal's function

This file only establishes a supporting bound and the nonemptiness of the set in
`Erdos970.jacobsthalFunction`. It does not address the quadratic conjecture.

For `Q = k!`, choose an integer `b` congruent to `1` modulo `Q` in the first `Q`
positions of an interval. A prime can divide at most one of the `k + 1` integers
`b, b + Q, ..., b + k * Q`. Thus at most `k` distinct prime factors cannot prevent
all these integers from being coprime to `n`.
-/

namespace Erdos970

/-- Every interval of `Q > 0` consecutive integers contains an integer congruent
    to `1` modulo `Q`. -/
lemma exists_offset_one_mod (a : ℤ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ i : ℕ, i < Q ∧ (Q : ℤ) ∣ (a + (i : ℤ)) - 1 := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hr₀ : 0 ≤ (1 - a) % (Q : ℤ) := Int.emod_nonneg _ hQ'.ne'
  have hrQ : (1 - a) % (Q : ℤ) < Q := Int.emod_lt_of_pos _ hQ'
  refine ⟨((1 - a) % (Q : ℤ)).toNat, (Int.toNat_lt hr₀).mpr hrQ, ?_⟩
  rw [Int.toNat_of_nonneg hr₀]
  refine ⟨-((1 - a) / (Q : ℤ)), ?_⟩
  rw [Int.emod_def]
  ring

/-- A prime divides at most one of `b, b + k!, ..., b + k * k!` when
    `b` is congruent to `1` modulo `k!`. -/
lemma factorial_progression_prime_dvd_unique {k p u v : ℕ} {b : ℤ}
    (hp : p.Prime) (hb : (k.factorial : ℤ) ∣ b - 1)
    (hu : u ≤ k) (hv : v ≤ k)
    (hpu : (p : ℤ) ∣ b + (u : ℤ) * (k.factorial : ℤ))
    (hpv : (p : ℤ) ∣ b + (v : ℤ) * (k.factorial : ℤ)) : u = v := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpQ : ¬ (p : ℤ) ∣ (k.factorial : ℤ) := by
    intro h
    have hpb : (p : ℤ) ∣ b := by
      simpa using dvd_sub hpu (dvd_mul_of_dvd_right h (u : ℤ))
    have hpone : (p : ℤ) ∣ 1 := by
      simpa using dvd_sub hpb (h.trans hb)
    exact hp'.not_dvd_one hpone
  have hkp : k < p := by
    apply lt_of_not_ge
    intro hpk
    exact hpQ (Int.natCast_dvd_natCast.mpr (hp.dvd_factorial.mpr hpk))
  have hpdiff : (p : ℤ) ∣ ((v : ℤ) - (u : ℤ)) * (k.factorial : ℤ) := by
    convert dvd_sub hpv hpu using 1
    ring
  have hpdiff' : (p : ℤ) ∣ (v : ℤ) - (u : ℤ) :=
    (hp'.dvd_mul.mp hpdiff).resolve_right hpQ
  have hmod : u ≡ v [MOD p] :=
    Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr hpdiff')
  exact hmod.eq_of_lt_of_lt (hu.trans_lt hkp) (hv.trans_lt hkp)

/-- An elementary uniform Jacobsthal bound, in product form. -/
theorem isJacobsthalBound_factorial_mul (k : ℕ) :
    IsJacobsthalBound k ((k + 1) * k.factorial) := by
  classical
  intro n hn hnk a
  obtain ⟨i₀, hi₀, hb⟩ := exists_offset_one_mod a (Nat.factorial_pos k)
  let b : ℤ := a + (i₀ : ℤ)
  have hgood : ∃ j : Fin (k + 1),
      (b + (j.val : ℤ) * (k.factorial : ℤ)).natAbs.Coprime n := by
    by_contra h
    have hbad : ∀ j : Fin (k + 1), ∃ p : ℕ,
        p ∈ n.primeFactors ∧ (p : ℤ) ∣ b + (j.val : ℤ) * (k.factorial : ℤ) := by
      intro j
      have hcop : ¬ (b + (j.val : ℤ) * (k.factorial : ℤ)).natAbs.Coprime n :=
        fun hc => h ⟨j, hc⟩
      obtain ⟨p, hp, hpd, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      exact ⟨p, hp.mem_primeFactors hpn hn.ne', Int.natCast_dvd.mpr hpd⟩
    choose p hp_mem hp_dvd using hbad
    let f : Fin (k + 1) → {p : ℕ // p ∈ n.primeFactors} :=
      fun j => ⟨p j, hp_mem j⟩
    have hf : Function.Injective f := by
      intro u v huv
      have hp_eq : p u = p v := congrArg Subtype.val huv
      apply Fin.ext
      apply factorial_progression_prime_dvd_unique
        (Nat.prime_of_mem_primeFactors (hp_mem u)) hb
        (Nat.le_of_lt_succ u.isLt) (Nat.le_of_lt_succ v.isLt) (hp_dvd u)
      rw [hp_eq]
      exact hp_dvd v
    have hcard : k + 1 ≤ n.primeFactors.card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using
        Fintype.card_le_of_injective f hf
    omega
  obtain ⟨j, hj⟩ := hgood
  refine ⟨i₀ + j.val * k.factorial, ?_, ?_⟩
  · calc
      i₀ + j.val * k.factorial < k.factorial + j.val * k.factorial :=
        Nat.add_lt_add_right hi₀ _
      _ ≤ k.factorial + k * k.factorial :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ j.isLt)) _
      _ = (k + 1) * k.factorial := by ring
  · simpa [b, Nat.cast_add, Nat.cast_mul, add_assoc] using hj

/-- The factorial uniform bound: every interval of `(k + 1)!` consecutive
    integers contains an integer coprime to any positive `n` with at most `k`
    distinct prime factors. -/
theorem isJacobsthalBound_factorial (k : ℕ) :
    IsJacobsthalBound k (k + 1).factorial := by
  simpa only [Nat.factorial_succ] using isJacobsthalBound_factorial_mul k

/-- In particular, the set whose infimum defines Jacobsthal's function is nonempty. -/
theorem jacobsthalBounds_nonempty (k : ℕ) :
    {m : ℕ | IsJacobsthalBound k m}.Nonempty :=
  ⟨(k + 1).factorial, isJacobsthalBound_factorial k⟩

/-- The infimum in the definition is itself a uniform bound. -/
theorem isJacobsthalBound_jacobsthalFunction (k : ℕ) :
    IsJacobsthalBound k (jacobsthalFunction k) :=
  Nat.sInf_mem (jacobsthalBounds_nonempty k)

/-- The elementary supporting estimate for Jacobsthal's function. -/
theorem jacobsthalFunction_le_factorial (k : ℕ) :
    jacobsthalFunction k ≤ (k + 1).factorial :=
  Nat.sInf_le (isJacobsthalBound_factorial k)

end Erdos970

#print axioms Erdos970.isJacobsthalBound_factorial
#print axioms Erdos970.jacobsthalBounds_nonempty
#print axioms Erdos970.isJacobsthalBound_jacobsthalFunction
#print axioms Erdos970.jacobsthalFunction_le_factorial
