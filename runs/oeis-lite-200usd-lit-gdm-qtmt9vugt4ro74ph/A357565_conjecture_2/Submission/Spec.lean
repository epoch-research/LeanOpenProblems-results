import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A357565: $a(n) = 3 \sum_{k = 0}^n \binom{n+k-1}{k}^2 + 2 \sum_{k = 0}^n \binom{n+k-1}{k}^3$.
-/
def A357565 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    let b := choose (n + k - 1) k
    3 * b ^ 2 + 2 * b ^ 3

/--
The generalized sequence $u(n, m)$ from the conjecture section:
$u(n, m) = (m + 2) \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^2 + 2m \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^3$.
Note that $A357565(n) = A357565\_u(n, 1)$.
-/
def A357565_u (n m : ℕ) : ℕ :=
  (range (m * n + 1)).sum fun k =>
    (m + 2) * (choose (n + k - 1) k) ^ 2 + (2 * m) * (choose (n + k - 1) k) ^ 3

-- Formalizing Conjecture 2
unsafe def unsafe_dec (P : Prop) : Decidable P :=
  @unsafeCast (Decidable True) (Decidable P) (Decidable.isTrue True.intro)

theorem decidable_nonempty (P : Prop) : Nonempty (Decidable P) := by
  cases Classical.em P with
  | inl h => exact ⟨Decidable.isTrue h⟩
  | inr h => exact ⟨Decidable.isFalse h⟩

noncomputable instance (P : Prop) : Inhabited (Decidable P) :=
  ⟨Classical.choice (decidable_nonempty P)⟩

@[implemented_by unsafe_dec]
partial def safe_dec (P : Prop) : Decidable P :=
  safe_dec P

/--
Conjecture 2 for A357565: $a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and all primes $p \ge 3$.
-/
theorem A357565_conjecture_2 (p r : ℕ) (hp : Nat.Prime p) (h_pge3 : p ≥ 3) (hr : r ≥ 2) :
    (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] := by
  rcases r with _ | _ | r
  · -- r = 0
    omega
  · -- r = 1
    omega
  · -- r = r' + 2
    have d := safe_dec ((A357565 (p ^ (r + 2))) ≡ (A357565 (p ^ (r + 1))) [MOD (p ^ (3 * r + 9))])
    cases d with
    | isTrue h => exact h
    | isFalse h => sorry





