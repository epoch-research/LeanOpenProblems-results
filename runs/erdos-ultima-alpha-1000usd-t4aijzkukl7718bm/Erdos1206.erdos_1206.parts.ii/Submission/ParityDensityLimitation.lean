import Submission.ColoringReduction

/-!
A limitation on a proposed multiplicative-density argument, not a solution of
Erdős 1206. A positive-lower-density set can simultaneously avoid every pair
`n, p*n` with `p` prime. Thus density losses from distinct prime directions
cannot simply be multiplied.
-/

namespace Erdos1206


/-- Both fibers of a nontrivial positive-integer multiplicative Boolean character
have positive lower density. No independence assumption is needed. -/
lemma multiplicative_bool_fiber_lowerDensity_pos (c : ℕ → Bool)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b →
      c (a * b) = Bool.xor (c a) (c b))
    {p : ℕ} (hp : 0 < p) (hcp : c p = true) (i : Bool) :
    0 < ({n : ℕ | 0 < n ∧ c n = i} : Set ℕ).lowerDensity := by
  apply positive_lowerDensity_of_bounded_dilation_cover (B := p) hp
  intro n hn
  by_cases hni : c n = i
  · exact ⟨1, by decide, hp, by simpa using And.intro hn hni⟩
  · refine ⟨p, hp, le_rfl, Nat.mul_pos hp hn, ?_⟩
    rw [hmul p n hp hn, hcp]
    cases i <;> cases hcn : c n <;> simp_all

/-- Positive integers having an even number of prime factors, with multiplicity. -/
def evenOmegaRoots : Set ℕ :=
  {n | 0 < n ∧ ArithmeticFunction.cardFactors n % 2 = 0}

lemma evenOmegaRoots_lowerDensity_pos : 0 < evenOmegaRoots.lowerDensity := by
  apply positive_lowerDensity_of_bounded_dilation_cover (B := 2) (by decide)
  intro n hn
  by_cases h : ArithmeticFunction.cardFactors n % 2 = 0
  · exact ⟨1, by decide, by decide, by simpa [evenOmegaRoots] using And.intro hn h⟩
  · refine ⟨2, by decide, by decide, Nat.mul_pos (by decide) hn, ?_⟩
    rw [ArithmeticFunction.cardFactors_mul (by decide) (by omega),
      ArithmeticFunction.cardFactors_apply_prime (by decide : Nat.Prime 2)]
    omega

lemma evenOmegaRoots_avoids_prime_dilations {p n : ℕ} (hp : Nat.Prime p)
    (hn : n ∈ evenOmegaRoots) : p * n ∉ evenOmegaRoots := by
  intro hpn
  have heq := ArithmeticFunction.cardFactors_mul hp.ne_zero (Nat.ne_of_gt hn.1)
  rw [ArithmeticFunction.cardFactors_apply_prime hp] at heq
  have h₁ := hn.2
  have h₂ := hpn.2
  omega

private lemma evenOmegaRoots_mem_of_two_primes {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) : p * q ∈ evenOmegaRoots := by
  refine ⟨Nat.mul_pos hp.pos hq.pos, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul hp.ne_zero hq.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp,
    ArithmeticFunction.cardFactors_apply_prime hq]

lemma evenOmegaRoots_not_cube_sidon :
    ¬ IsSidon ((fun a : ℕ => a ^ 3) '' evenOmegaRoots) := by
  have h447 : 447 ∈ evenOmegaRoots := by
    exact evenOmegaRoots_mem_of_two_primes (p := 3) (q := 149) (by norm_num) (by norm_num)
  have h303 : 303 ∈ evenOmegaRoots := by
    exact evenOmegaRoots_mem_of_two_primes (p := 3) (q := 101) (by norm_num) (by norm_num)
  have h485 : 485 ∈ evenOmegaRoots := by
    exact evenOmegaRoots_mem_of_two_primes (p := 5) (q := 97) (by norm_num) (by norm_num)
  have h145 : 145 ∈ evenOmegaRoots := by
    exact evenOmegaRoots_mem_of_two_primes (p := 5) (q := 29) (by norm_num) (by norm_num)
  intro h
  have hh := h _ ⟨447, h447, rfl⟩ _ ⟨485, h485, rfl⟩
    _ ⟨303, h303, rfl⟩ _ ⟨145, h145, rfl⟩ (by norm_num)
  norm_num at hh

/-- Explicit counterexample to multiplying the density losses of prime-direction constraints. -/
theorem positive_density_avoids_all_prime_pairs_but_not_cube_sidon :
    ∃ A : Set ℕ, 0 < A.lowerDensity ∧
      (∀ p n : ℕ, Nat.Prime p → n ∈ A → p * n ∉ A) ∧
      ¬ IsSidon ((fun a : ℕ => a ^ 3) '' A) := by
  exact ⟨evenOmegaRoots, evenOmegaRoots_lowerDensity_pos,
    fun _ _ hp hn => evenOmegaRoots_avoids_prime_dilations hp hn,
    evenOmegaRoots_not_cube_sidon⟩

end Erdos1206
