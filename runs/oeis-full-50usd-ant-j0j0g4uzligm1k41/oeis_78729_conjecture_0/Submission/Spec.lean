import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
The product $(k+1)(k+2)\cdots(k+n)$.
-/
def A078729_product (n k : ℕ) : ℕ :=
  (Finset.range n).prod (fun i ↦ k + i + 1)

/--
A078729: $a(n)$ is the least positive integer $k$ such that
$$(k+1)(k+2)\cdots(k+n) + 1$$
is prime, if such $k$ exists; otherwise, $a(n) = 0$.
-/
noncomputable def A078729 (n : ℕ) : ℕ :=
  sInf { k : ℕ | k > 0 ∧ (A078729_product n k + 1).Prime }

/--
Conjecture: $a(n) = 0$ if and only if $n=4$.
-/
theorem oeis_78729_conjecture_0 : ∀ n : ℕ, A078729 n = 0 ↔ n = 4 := by
  intro n
  constructor
  · -- Forward direction: `A078729 n = 0 → n = 4`.
    -- `A078729 n = 0` means the set `{k > 0 | ∏_{i=1}^n (k+i) + 1 is prime}` is empty,
    -- i.e. `∏_{i=1}^n (k+i) + 1` is composite for every `k ≥ 1`.
    -- The polynomial `∏_{i=1}^n (x+i) + 1` is irreducible for every `n ≠ 4` and has no
    -- fixed prime divisor, so this is exactly an instance of Bunyakovsky's conjecture (1857):
    -- proving it takes a prime value is an open problem for every univariate polynomial of
    -- degree ≥ 2 (parity barrier). This direction is therefore not provable with current
    -- mathematics / Mathlib.
    intro h
    sorry
  · -- Reverse direction: `n = 4 → A078729 n = 0`.
    rintro rfl
    have hempty : { k : ℕ | k > 0 ∧ (A078729_product 4 k + 1).Prime } = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hk hp
      have hid : A078729_product 4 k + 1 = (k ^ 2 + 5 * k + 5) ^ 2 := by
        simp [A078729_product, Finset.prod_range_succ]; ring
      rw [hid] at hp
      have h2 : 2 ≤ k ^ 2 + 5 * k + 5 := by nlinarith
      have hdvd : (k ^ 2 + 5 * k + 5) ∣ (k ^ 2 + 5 * k + 5) ^ 2 := ⟨k ^ 2 + 5 * k + 5, by ring⟩
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
      · omega
      · nlinarith [h]
    rw [A078729, hempty]
    exact Nat.sInf_empty
