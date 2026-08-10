import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    ((Finset.sum (range (n + 1)) fun k =>
      let N := 3 * n
      let term_val : ℚ := (N : ℚ) / (N + 2 * k : ℚ) * ((N + 2 * k).choose k : ℚ)
      term_val
    ).floor).toNat

-- The core "Lemma X" (to be proven): a(M p) ≡ a(M) mod p^{3(1+v_p M)}.
-- Here I test that Lemma X implies the conjecture.

theorem reduction
    (LemmaX : ∀ (p M : ℕ), p.Prime → 5 ≤ p → 0 < M →
      a (M * p) ≡ a M [MOD p ^ (3 * (1 + padicValNat p M))])
    (p n k : ℕ) :
    p.Prime → 5 ≤ p → 0 < n → 0 < k →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  intro hp hp5 hn hk
  set M := n * p ^ (k-1) with hM
  have hMpos : 0 < M := by positivity
  have hstep := LemmaX p M hp hp5 hMpos
  -- M * p = n * p^k
  have hMp : M * p = n * p ^ k := by
    rw [hM]; rw [mul_assoc, ← pow_succ]; congr 2; omega
  rw [hMp] at hstep
  -- 3*k ≤ 3*(1+v_p M)
  have hval : k ≤ 1 + padicValNat p M := by
    rw [hM]
    have hfact : Fact p.Prime := ⟨hp⟩
    have : padicValNat p (n * p ^ (k-1)) = padicValNat p n + (k-1) := by
      rw [padicValNat.mul (by omega) (by positivity)]
      rw [padicValNat.prime_pow]
    rw [this]; omega
  -- conclude via divisibility of moduli
  have hdvd : p ^ (3 * k) ∣ p ^ (3 * (1 + padicValNat p M)) := by
    apply pow_dvd_pow; omega
  exact hstep.of_dvd hdvd
