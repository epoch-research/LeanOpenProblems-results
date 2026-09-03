import FormalConjecturesUtil

/-!
Checks on the quantifiers in a possible sieve argument for Erdős 972.
These results are not a proof or a disproof of the conjecture.
-/

namespace Erdos972SieveBarrier

/-- Prime inputs can have composite outputs avoiding every fixed modulus,
with infinitely many choices of input for each modulus. -/
theorem infinite_prime_inputs_square_coprime (M : ℕ) (hM : M ≠ 0) :
    {p : ℕ | p.Prime ∧ (p ^ 2).Coprime M}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hbound, hp⟩ := Nat.exists_infinite_primes (max N M + 1)
  have hNp : N < p := by omega
  have hMp : M < p := by omega
  have hc : p.Coprime M := Nat.coprime_of_lt_prime hM hMp hp
  exact ⟨p, ⟨hp, (Nat.coprime_pow_left_iff (by decide) p M).mpr hc⟩, hNp⟩

/-- None of the same outputs is prime. -/
theorem no_prime_square_outputs :
    {p : ℕ | p.Prime ∧ (p ^ 2).Prime} = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp
  rw [pow_two]
  exact Nat.not_prime_mul hp.ne_one hp.ne_one

/-- Thus the fixed-modulus statement alone cannot justify simultaneous primality. -/
theorem fixed_modulus_condition_insufficient :
    ¬ (∀ f : ℕ → ℕ,
      (∀ M : ℕ, M ≠ 0 → {p : ℕ | p.Prime ∧ (f p).Coprime M}.Infinite) →
      {p : ℕ | p.Prime ∧ (f p).Prime}.Infinite) := by
  intro h
  have hi := h (fun p => p ^ 2) infinite_prime_inputs_square_coprime
  rw [no_prime_square_outputs] at hi
  exact hi Set.finite_empty

/-- Unlike a fixed modulus, the factorial of the output's square root
sifts far enough to characterize primality exactly. -/
theorem prime_iff_coprime_sqrt_factorial (q : ℕ) :
    q.Prime ↔ 2 ≤ q ∧ q.Coprime (Nat.sqrt q).factorial := by
  constructor
  · intro hq
    exact ⟨hq.two_le, hq.coprime_factorial_of_lt (Nat.sqrt_lt_self hq.one_lt)⟩
  · rintro ⟨hq, hc⟩
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨hq, ?_⟩
    intro m hm hmq hdiv
    have he := Nat.eq_one_of_dvd_coprimes hc hdiv
      (Nat.dvd_factorial (by omega) hmq)
    omega

/-- A size bound converts a finite sieve condition into primality. -/
theorem prime_of_coprime_factorial_of_lt_square {q B : ℕ}
    (hq : 2 ≤ q) (hbound : q < (B + 1) ^ 2)
    (hc : q.Coprime B.factorial) : q.Prime := by
  apply (prime_iff_coprime_sqrt_factorial q).mpr
  refine ⟨hq, ?_⟩
  have hs : Nat.sqrt q ≤ B := by
    have := Nat.sqrt_lt'.mpr hbound
    omega
  exact hc.of_dvd_right (Nat.factorial_dvd_factorial hs)

/-- The finite set a quantitative sieve estimate would need to show is nonempty. -/
noncomputable def siftedInputs (α : ℝ) (N X B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc N X).filter fun p =>
    p.Prime ∧ (⌊α * p⌋₊).Coprime B.factorial

lemma floor_mul_two_le {α : ℝ} (hα : 1 < α) {p : ℕ} (hp : p.Prime) :
    2 ≤ ⌊α * p⌋₊ := by
  apply (Nat.le_floor_iff (show 0 ≤ α * p by positivity)).mpr
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  norm_num only [Nat.cast_ofNat]
  exact hp2.trans (le_mul_of_one_le_left (Nat.cast_nonneg p) hα.le)

/-- At a square-root cutoff, any surviving prime input has a prime output. -/
lemma prime_output_of_mem_siftedInputs {α : ℝ} (hα : 1 < α)
    {N X B p : ℕ} (hbound : ⌊α * X⌋₊ < (B + 1) ^ 2)
    (hp : p ∈ siftedInputs α N X B) :
    N < p ∧ p.Prime ∧ (⌊α * p⌋₊).Prime := by
  classical
  simp only [siftedInputs, Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨hp.1.1, hp.2.1, ?_⟩
  apply prime_of_coprime_factorial_of_lt_square
    (floor_mul_two_le hα hp.2.1) _ hp.2.2
  apply lt_of_le_of_lt (Nat.floor_le_floor ?_) hbound
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hp.1.2) (by linarith)

/-- An exact positive finite-sieve formulation of the desired infinitude.
The right side is a target estimate, not an assertion proved independently here. -/
theorem infinite_prime_pairs_iff_positive_sifted_count {α : ℝ} (hα : 1 < α) :
    {p : ℕ | p.Prime ∧ (⌊α * p⌋₊).Prime}.Infinite ↔
      ∀ N : ℕ, ∃ X B : ℕ, ⌊α * X⌋₊ < (B + 1) ^ 2 ∧
        0 < (siftedInputs α N X B).card := by
  classical
  constructor
  · intro hi N
    obtain ⟨p, hp, hNp⟩ := Set.infinite_iff_exists_gt.mp hi N
    refine ⟨p, Nat.sqrt ⌊α * p⌋₊, Nat.lt_succ_sqrt' _, ?_⟩
    apply Finset.card_pos.mpr
    refine ⟨p, ?_⟩
    simp only [siftedInputs, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hNp, le_rfl⟩, hp.1,
      hp.2.coprime_factorial_of_lt (Nat.sqrt_lt_self hp.2.one_lt)⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨X, B, hbound, hcount⟩ := h N
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hcount
    obtain ⟨hNp, hprime, houtput⟩ := prime_output_of_mem_siftedInputs hα hbound hp
    exact ⟨p, ⟨hprime, houtput⟩, hNp⟩

#print axioms fixed_modulus_condition_insufficient
#print axioms prime_iff_coprime_sqrt_factorial
#print axioms infinite_prime_pairs_iff_positive_sifted_count

end Erdos972SieveBarrier
