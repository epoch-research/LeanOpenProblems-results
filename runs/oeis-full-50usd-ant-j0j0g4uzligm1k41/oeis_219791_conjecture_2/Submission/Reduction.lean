import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The conjecture (verbatim statement). -/
def Conj : Prop :=
  ∀ (k : ℕ), 0 < k →
    ∃ (N : ℕ), ∀ (n : ℕ), N ≤ n →
      ∃ (x y : ℕ), 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime ((x * y) ^ (2^k) + 1)

/-- A Landau-type statement: arbitrarily large `a` with `a^2 + 1` prime
    (equivalently, infinitely many primes of the form `a^2 + 1`). This is
    Landau's fourth problem, OPEN since 1912. -/
def LandauType : Prop := ∀ B : ℕ, ∃ a : ℕ, B ≤ a ∧ Nat.Prime (a ^ 2 + 1)

/-- **The reduction**: the conjecture implies the (open) Landau-type statement.
    Hence any Lean proof of the conjecture is a Lean proof of `LandauType`. -/
theorem conj_implies_landau (h : Conj) : LandauType := by
  -- use the `k = 1` instance, where `2 ^ 1 = 2`
  obtain ⟨N, hN⟩ := h 1 (by norm_num)
  intro B
  -- pick `n = max N (B + 1)`, which is `≥ N` and `≥ B + 1`
  set n := max N (B + 1) with hn
  have hnN : N ≤ n := le_max_left _ _
  have hnB : B + 1 ≤ n := le_max_right _ _
  obtain ⟨x, y, hx, hy, hxy, hp⟩ := hN n hnN
  refine ⟨x * y, ?_, ?_⟩
  · -- `x * y ≥ x + y - 1 = n - 1 ≥ B`, since `(x-1)(y-1) ≥ 0`.
    obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, y = b + 1 := ⟨y - 1, by omega⟩
    -- now `x*y = (a+1)*(b+1) = a*b + a + b + 1 ≥ a + b + 1`, and `a+b+2 = n ≥ B+1`.
    nlinarith [Nat.zero_le (a * b), hxy, hnB]
  · -- the prime: `(x*y)^(2^1) + 1 = (x*y)^2 + 1`
    have h21 : (2:ℕ) ^ 1 = 2 := by norm_num
    rw [h21] at hp
    exact hp

/-- **Obstruction to any single-prime (hence covering-system) disproof.**
    For every exponent and every prime `p`, and every `n ≥ p + 1`, there is a valid
    decomposition `x + y = n` whose value `(x*y)^(2^k) + 1` is NOT divisible by `p`.
    (Take `x = p`: then `p ∣ x*(n-x)`, so `(x*(n-x))^(2^k) + 1 ≡ 1 (mod p)`.)
    Thus no fixed prime can certify all decompositions composite; combined with the
    density count `2^{k+1} < p`, no finite covering can force compositeness for every
    `x`, which is why a covering-based disproof is impossible. -/
theorem no_uniform_prime_divisor (k p n : ℕ) (hp : p.Prime) (hn : p + 1 ≤ n) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ ¬ (p ∣ (x * y) ^ (2 ^ k) + 1) := by
  refine ⟨p, n - p, hp.pos, by omega, by omega, ?_⟩
  -- `p ∣ p * (n - p)`, so the value is `≡ 1 (mod p)`; since `p` is prime, `p ≥ 2 > 1`.
  have hdvd : p ∣ (p * (n - p)) ^ (2 ^ k) := by
    apply dvd_pow
    · exact Dvd.intro _ rfl
    · positivity
  intro hcontra
  -- `p ∣ value` and `p ∣ value - 1` would give `p ∣ 1`, contradicting `p ≥ 2`.
  have h1 : p ∣ 1 := (Nat.dvd_add_right hdvd).mp hcontra
  exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp h1)
