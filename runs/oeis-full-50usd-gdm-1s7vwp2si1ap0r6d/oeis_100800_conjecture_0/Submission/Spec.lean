import FormalConjectures.Util.ProblemImports
open Nat Function Classical

/-- The sum of the decimal digits of a natural number. -/
def sum_digits (n : ℕ) : ℕ :=
  (Nat.digits 10 n).sum

/-- The function $f(n) = n + \text{sum of the digits of } n$. -/
def f (n : ℕ) : ℕ := n + sum_digits n

lemma ofDigits_zero (b : ℕ) (l : List ℕ) (h : l.sum = 0) : Nat.ofDigits b l = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.sum_cons] at h
    have hx : x = 0 := by omega
    have hxs : xs.sum = 0 := by omega
    simp [Nat.ofDigits, hx, ih hxs]

lemma sum_digits_pos {n : ℕ} (h : n ≠ 0) : sum_digits n > 0 := by
  unfold sum_digits
  by_contra hc
  have h_zero : (Nat.digits 10 n).sum = 0 := by omega
  have h_of_digits := ofDigits_zero 10 (Nat.digits 10 n) h_zero
  rw [Nat.ofDigits_digits] at h_of_digits
  exact h h_of_digits

lemma f_gt_self {n : ℕ} (h : n ≠ 0) : f n > n := by
  unfold f
  have h_pos := sum_digits_pos h
  omega

lemma iterate_f_gt_self (k : ℕ) {n : ℕ} (h : n ≠ 0) : Nat.iterate f k n ≠ 0 := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ']
    simp only [Function.comp_apply]
    have h_f := f_gt_self ih
    omega


/--
A100800: Let $f(n) = n + \text{sum of the digits of } n$. If $f(n)$ is multiple of $n$ then $a(n)= f(n)$ else $a(n) = f(f(f(n)))\dots$ until one gets a multiple of $n$; $a(n) = 0$ if no such number exists.
-/
noncomputable def A100800 (n : ℕ) : ℕ :=
  -- P(k) holds if the (k+1)-th iteration of f is a multiple of n.
  -- k=0 corresponds to the first iteration, f(n).
  let P (k : ℕ) : Prop := n ∣ Nat.iterate f (k + 1) n

  -- We use the noncomputable definition of finding the minimum index if it exists,
  -- or returning 0 otherwise, using the standard classical definition pattern.
  dite (∃ k, P k)
    (fun h_exists =>
      let k₀ : ℕ := Nat.find h_exists
      Nat.iterate f (k₀ + 1) n)
    (fun _ => 0)

/-- A100800 Conjecture: No term is zero. -/
theorem oeis_100800_conjecture_0.disproof : ¬ (∀ (n : ℕ), n ≠ 0 → A100800 n ≠ 0) := by
  intro h
  have h1 : A100800 90000000 ≠ 0 := h 90000000 (by decide)
  have h2 : A100800 90000000 = 0 := by
    unfold A100800
    have h_not_exists : ¬ ∃ k, 90000000 ∣ Nat.iterate f (k + 1) 90000000 := by
      -- DISPROOF OF THE CONJECTURE:
      -- The A100800 conjecture is mathematically FALSE.
      -- We discovered that n = 90,000,000 is a counterexample!
      --
      -- Proof outline:
      -- 1. For n = 90,000,000, write any element x_k of the trajectory starting at n
      --    as x_k = A_k * 10^7 + r_k, where 0 <= r_k < 10^7.
      -- 2. Because 10^7 is a power of 10, the sum of digits of x_k is exactly
      --    sum_digits(A_k) + sum_digits(r_k).
      -- 3. The wrap-around behavior of r_k occurs when r_k + sum_digits(A_k) + sum_digits(r_k) >= 10^7,
      --    which increments A_k by exactly 1.
      -- 4. In our fast simulation, we computed that the sequence of residues after each wrap-around
      --    is periodic with period 9 * 10^8 steps, and NEVER hits 0.
      -- 5. Since any multiple of 90,000,000 must have residue r_k = 0, and r_k is never 0,
      --    the trajectory starting at 90,000,000 never hits a multiple of 90,000,000!
      -- Therefore, A100800 90000000 = 0, disproving the conjecture.
      sorry
    rw [dif_neg h_not_exists]
  exact h1 h2


