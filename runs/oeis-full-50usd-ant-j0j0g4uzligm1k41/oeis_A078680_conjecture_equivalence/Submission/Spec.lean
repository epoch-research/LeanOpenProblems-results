import FormalConjectures.Util.ProblemImports
open PNat

/--
A078680: Smallest $m > 0$ such that $n \cdot 2^m + 1$ is prime, or $0$ if no such $m$ exists.
We search for the smallest element in the set of positive natural numbers ($\mathbb{N}^+$ or PNat) satisfying the primality condition.
-/
noncomputable def A078680 (n : ℕ) : ℕ :=
  -- Predicate P on PNat: n * 2^m + 1 is prime.
  let P (m : PNat) : Prop := Nat.Prime (n * 2 ^ (m : ℕ) + 1)

  -- Use classical logic to determine if a solution exists.
  match Classical.dec (∃ m : PNat, P m) with
  | isTrue h_exist => (PNat.find h_exist).val -- Find the smallest PNat m, and convert to Nat.
  | isFalse _      => 0                       -- Return 0 if no such PNat exists.

open Nat

/-- `A078680 n = 0` exactly when there is no positive `m` making `n*2^m+1` prime. -/
theorem A078680_eq_zero_iff (n : ℕ) :
    A078680 n = 0 ↔ ¬ ∃ m : PNat, Nat.Prime (n * 2 ^ (m : ℕ) + 1) := by
  unfold A078680
  dsimp only
  split
  · rename_i hex heq
    have hpos : 0 < ((PNat.find hex : ℕ)) := (PNat.find hex).2
    constructor
    · intro hz; exfalso; omega
    · intro hne; exact absurd hex hne
  · rename_i hnone heq
    exact iff_of_true rfl hnone

/-- The Fermat-number characterisation of the predicate at `n = 2^16`. -/
theorem fermat_equiv :
    (∀ m : PNat, ¬ Nat.Prime (2^16 * 2 ^ (m : ℕ) + 1)) ↔
    (∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k)) := by
  constructor
  · intro H k hk
    have h16 : (16:ℕ) ≤ 2^k := by
      calc (16:ℕ) = 2^4 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < 2^k - 16 := by
      have h32 : (32:ℕ) ≤ 2^k := by
        calc (32:ℕ) = 2^5 := by norm_num
        _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hkey := H ⟨2^k - 16, hpos⟩
    simp only [PNat.mk_coe] at hkey
    have hsum : 16 + (2^k - 16) = 2^k := by omega
    have heq : 2^16 * 2 ^ (2^k - 16) + 1 = fermatNumber k := by
      rw [fermatNumber, ← pow_add, hsum]
    rwa [heq] at hkey
  · intro H m hp
    have h2 : 2^16 * 2 ^ (m : ℕ) + 1 = 2 ^ (16 + (m:ℕ)) + 1 := by rw [pow_add]
    rw [h2] at hp
    obtain ⟨j, hj⟩ := pow_of_pow_add_prime (by norm_num : 1 < 2)
      (by positivity : 16 + (m:ℕ) ≠ 0) hp
    have hm1 : 1 ≤ (m:ℕ) := m.2
    have h17 : 17 ≤ 2^j := by omega
    have hj4 : 4 < j := by
      by_contra h
      push_neg at h
      have hle : 2^j ≤ 2^4 := Nat.pow_le_pow_right (by norm_num) h
      norm_num at hle
      omega
    apply H j hj4
    rw [fermatNumber, ← hj]
    exact hp

/-- `A078680 (2^16) = 0` is equivalent to all Fermat numbers `F_k`, `k > 4`, being composite. -/
theorem A078680_2pow16_iff :
    A078680 (2^16) = 0 ↔ (∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k)) := by
  rw [A078680_eq_zero_iff, not_exists]
  exact fermat_equiv

/--
Conjecture from OEIS A078680:
The claim that the first $n > 0$ for which $A078680(n)=0$ is $n=65536$ is equivalent to
the statement that all Fermat numbers $F_k = 2^{2^k} + 1$ for $k > 4$ are composite.

Here, $65536 = 2^{16}$.
-/
theorem oeis_A078680_conjecture_equivalence :
  (A078680 (2^16) = 0 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0))
  ↔
  (∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k)) := by
  constructor
  · rintro ⟨hC1, -⟩
    exact A078680_2pow16_iff.mp hC1
  · intro hRHS
    refine ⟨A078680_2pow16_iff.mpr hRHS, ?_⟩
    -- Remaining goal `C2`: `∀ n, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0`, i.e. every
    -- `1 ≤ n < 65536` admits a prime `n*2^m+1`.  This is equivalent to the assertion
    -- that no `n < 65536` is a Sierpiński number, an OPEN problem (e.g. `n = 21181,
    -- 22699, 24737, 55459` are unresolved Sierpiński candidates), and is not implied
    -- by `RHS`.
    sorry
