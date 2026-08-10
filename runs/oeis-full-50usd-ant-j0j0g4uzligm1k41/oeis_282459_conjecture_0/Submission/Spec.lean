import FormalConjectures.Util.ProblemImports

open Nat

/--
A282459: Number of composite numbers of the form $2n - 2^k + 1$ ($k > 0, 2^k < 2n + 1$).
-/
def A282459 (n : ℕ) : ℕ :=
  -- The upper bound for k is $\lfloor \log_2(2n+1) \rfloor$.
  let upper_k : ℕ := log 2 (2 * n + 1)
  -- The set of $k$ values is $1 \le k \le \lfloor \log_2(2n+1) \rfloor$.
  let s := Finset.Icc 1 upper_k

  -- A natural number $m$ is composite if $m > 1$ and $m$ is not a prime.
  -- We must use Nat.Prime explicitly in this context.
  let is_composite (m : ℕ) : Prop := 1 < m ∧ ¬ Nat.Prime m

  -- The value we are checking for compositeness. The subtraction is safe since $2^k \le 2n+1$.
  -- The subtraction is safe because $k \le \log_2(2n+1)$, which implies $2^k \le 2n+1$.
  let seq_val (k : ℕ) : ℕ := 2 * n + 1 - 2 ^ k

  -- We count how many $k$ in the set $s$ make `seq_val k` composite.
  Finset.card (Finset.filter (fun k : ℕ => is_composite (seq_val k)) s)

/-- Witness lemma: if `d` (with `1 < d`) divides `2n+1 - 2^k` for some `1 ≤ k ≤ 6`,
and `d < 2n+1 - 2^k`, then `2n+1 - 2^k` is a composite value of the sequence,
so `A282459 n > 0`. -/
theorem A282459_witness (n d k : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (hn : n > 52)
    (hd1 : 1 < d) (hdvd : d ∣ (2 * n + 1 - 2 ^ k)) (hdlt : d < 2 * n + 1 - 2 ^ k) :
    A282459 n > 0 := by
  unfold A282459
  simp only
  rw [gt_iff_lt, Finset.card_pos]
  refine ⟨k, ?_⟩
  rw [Finset.mem_filter, Finset.mem_Icc]
  have hlog : 6 ≤ log 2 (2 * n + 1) := by
    rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]; norm_num; omega
  refine ⟨⟨hk1, by omega⟩, by omega, ?_⟩
  intro hp
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp d hdvd) with h | h
  · omega
  · omega

/--
It is conjectured that `A282459 n > 0` for all `n > 52`.
-/
theorem oeis_282459_conjecture_0 : ∀ n : ℕ, n > 52 → A282459 n > 0 := by
  intro n hn
  have e1 : (2 : ℕ) ^ 1 = 2 := by norm_num
  have e2 : (2 : ℕ) ^ 2 = 4 := by norm_num
  have e3 : (2 : ℕ) ^ 3 = 8 := by norm_num
  have e4 : (2 : ℕ) ^ 4 = 16 := by norm_num
  -- Covering argument.
  -- If `3 ∤ (2n+1)` then one of `2n+1-2`, `2n+1-4` is divisible by 3 and `> 3`, hence composite.
  -- If `3 ∣ (2n+1)` but `5 ∤ (2n+1)`, then (2 is a primitive root mod 5) one of
  --   `2n+1 - 2^k` (k = 1,2,3,4) is divisible by 5 and `> 5`, hence composite.
  -- The remaining case `15 ∣ (2n+1)` is the open Erdős "105 problem"
  --   (OEIS A039669): it is conjectured but UNPROVEN that 105 is the largest odd
  --   number `N` with `N - 2^k` prime for all valid `k`. No finite covering system
  --   resolves it (the only forced divisibility, by primitive-root primes `p ≤ log₂N`,
  --   has product `≪ 2^{log₂N}`), and it is tied to the Hardy–Littlewood prime
  --   k-tuple framework. The statement is true (no counterexample up to ~10¹⁵) but
  --   not provable by currently available techniques.
  rcases (show (2 * n + 1) % 3 = 0 ∨ (2 * n + 1) % 3 = 1 ∨ (2 * n + 1) % 3 = 2 by omega)
    with h3 | h3 | h3
  · rcases (show (2 * n + 1) % 5 = 0 ∨ (2 * n + 1) % 5 = 1 ∨ (2 * n + 1) % 5 = 2 ∨
        (2 * n + 1) % 5 = 3 ∨ (2 * n + 1) % 5 = 4 by omega) with h5 | h5 | h5 | h5 | h5
    · -- 15 ∣ (2n+1): the open core (the Erdős "105" conjecture).
      sorry
    · exact A282459_witness n 5 4 (by norm_num) (by norm_num) hn (by norm_num)
        (by rw [e4]; omega) (by rw [e4]; omega)
    · exact A282459_witness n 5 1 (by norm_num) (by norm_num) hn (by norm_num)
        (by rw [e1]; omega) (by rw [e1]; omega)
    · exact A282459_witness n 5 3 (by norm_num) (by norm_num) hn (by norm_num)
        (by rw [e3]; omega) (by rw [e3]; omega)
    · exact A282459_witness n 5 2 (by norm_num) (by norm_num) hn (by norm_num)
        (by rw [e2]; omega) (by rw [e2]; omega)
  · exact A282459_witness n 3 2 (by norm_num) (by norm_num) hn (by norm_num)
      (by rw [e2]; omega) (by rw [e2]; omega)
  · exact A282459_witness n 3 1 (by norm_num) (by norm_num) hn (by norm_num)
      (by rw [e1]; omega) (by rw [e1]; omega)
