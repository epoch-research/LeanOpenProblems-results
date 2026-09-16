import FormalConjectures.Util.ProblemImports
import Submission.Proofs.MainProofs

open Nat Finset

/--
A219055: Number of ways to write $n = p+q(3-(-1)^n)/2$ with $p>q$ and $p, q, p-6, q+6$ all prime.
-/
def A219055 (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun q : ℕ =>
    -- c = 1 + n % 2. The condition p > q is equivalent to (c + 1) * q < n.
    ((1 + n % 2) + 1) * q < n ∧

    -- Primality conditions for q and derived terms
    q.Prime ∧
    (q + 6).Prime ∧

    -- Primality conditions for p = n - c * q and p - 6
    (n - (1 + n % 2) * q).Prime ∧        -- p must be prime
    (n - (1 + n % 2) * q - 6).Prime      -- p - 6 must be prime
  ) (Finset.range n)

-- Formal definition of Goldbach's Conjecture
def goldbach_conjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q

-- Formal definition of Lemoine's Conjecture (or Levy's Conjecture)
def lemoine_conjecture : Prop :=
  ∀ n : ℕ, 7 ≤ n → Odd n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q

-- Formalization of the conjecture that there are infinitely many cousin primes (p, p+6)
def six_prime_gap_conjecture : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ (p + 6).Prime}

/--
The core conjecture about the sequence A219055:
a(n) > 0 for all even n > 8012 and odd n > 15727.
-/
def a219055_core_conjecture : Prop :=
  ∀ n : ℕ,
    (Even n ∧ 8012 < n) ∨ (Odd n ∧ 15727 < n)
      → A219055 n > 0

lemma a219055_implies_goldbach (h_core : a219055_core_conjecture) : goldbach_conjecture := by
  intro n h4 heven
  if h_le : n ≤ 8012 then
    exact goldbach_up_to_8012 n h4 h_le (Nat.even_iff.mp heven)
  else
    have h_gt : 8012 < n := by omega
    have h_pos : A219055 n > 0 := h_core n (Or.inl ⟨heven, h_gt⟩)
    have heq : n % 2 = 0 := Nat.even_iff.mp heven
    have h_pos2 : 0 < (filter (fun q =>
      (1 + n % 2 + 1) * q < n ∧
      q.Prime ∧ (q + 6).Prime ∧
      (n - (1 + n % 2) * q).Prime ∧
      (n - (1 + n % 2) * q - 6).Prime) (range n)).card := h_pos
    rw [card_pos] at h_pos2
    rcases h_pos2 with ⟨q, hq⟩
    rw [mem_filter] at hq
    rcases hq with ⟨_, h_cond⟩
    simp [heq] at h_cond
    rcases h_cond with ⟨hlt, hq_prime, _, hp_prime, _⟩
    use (n - q), q
    exact ⟨hp_prime, hq_prime, by omega⟩

lemma a219055_implies_lemoine (h_core : a219055_core_conjecture) : lemoine_conjecture := by
  intro n h7 hodd
  if h_le : n ≤ 15727 then
    have h_mod : n % 2 = 1 := by rcases hodd with ⟨k, rfl⟩; omega
    exact lemoine_up_to_15727 n h7 h_le h_mod
  else
    have h_gt : 15727 < n := by omega
    have h_pos : A219055 n > 0 := h_core n (Or.inr ⟨hodd, h_gt⟩)
    have heq : n % 2 = 1 := by rcases hodd with ⟨k, rfl⟩; omega
    have h_pos2 : 0 < (filter (fun q =>
      (1 + n % 2 + 1) * q < n ∧
      q.Prime ∧ (q + 6).Prime ∧
      (n - (1 + n % 2) * q).Prime ∧
      (n - (1 + n % 2) * q - 6).Prime) (range n)).card := h_pos
    rw [card_pos] at h_pos2
    rcases h_pos2 with ⟨q, hq⟩
    rw [mem_filter] at hq
    rcases hq with ⟨_, h_cond⟩
    simp [heq] at h_cond
    rcases h_cond with ⟨hlt, hq_prime, _, hp_prime, _⟩
    use (n - 2 * q), q
    exact ⟨hp_prime, hq_prime, by omega⟩

lemma a219055_implies_six_gap (h_core : a219055_core_conjecture) : six_prime_gap_conjecture := by
  intro h_fin
  have h_bdd : ∃ B, ∀ x ∈ {p : ℕ | p.Prime ∧ (p + 6).Prime}, x ≤ B := by
    rcases h_fin.bddAbove with ⟨B, hB⟩
    use B; intro x hx; exact hB hx
  rcases h_bdd with ⟨B, hB⟩
  let n := 2 * B + 8014
  have hn_even : Even n := ⟨B + 4007, by omega⟩
  have hn_gt : 8012 < n := by omega
  have h_pos : A219055 n > 0 := h_core n (Or.inl ⟨hn_even, hn_gt⟩)
  
  have heq : n % 2 = 0 := Nat.even_iff.mp hn_even
  have h_pos2 : 0 < (filter (fun q =>
    (1 + n % 2 + 1) * q < n ∧
    q.Prime ∧ (q + 6).Prime ∧
    (n - (1 + n % 2) * q).Prime ∧
    (n - (1 + n % 2) * q - 6).Prime) (range n)).card := h_pos
  rw [card_pos] at h_pos2
  rcases h_pos2 with ⟨q, hq⟩
  rw [mem_filter] at hq
  rcases hq with ⟨_, h_cond⟩
  simp [heq] at h_cond
  rcases h_cond with ⟨hlt, hq_prime, hq6_prime, hp_prime, hp6_prime⟩
  have hq_in : q ∈ {p : ℕ | p.Prime ∧ (p + 6).Prime} := ⟨hq_prime, hq6_prime⟩
  have hp_in : (n - q - 6) ∈ {p : ℕ | p.Prime ∧ (p + 6).Prime} := by
    dsimp
    use hp6_prime
    have : n - q - 6 + 6 = n - q := by omega
    rw [this]
    exact hp_prime
  have h1 := hB q hq_in
  have h2 := hB (n - q - 6) hp_in
  have hn_bound : n ≤ 2 * B + 6 := by omega
  have hn_def : n = 2 * B + 8014 := rfl
  omega

/--
A219055, Conjecture 1: The core conjecture for A219055 implies Goldbach's conjecture,
Lemoine's conjecture and the conjecture that there are infinitely many primes p with p+6 also prime.
-/
theorem oeis_219055_conjecture_1 :
    a219055_core_conjecture → goldbach_conjecture ∧ lemoine_conjecture ∧ six_prime_gap_conjecture :=
  fun h_core => ⟨a219055_implies_goldbach h_core, a219055_implies_lemoine h_core, a219055_implies_six_gap h_core⟩

theorem oeis_219055_conjecture_1.disproof : ¬ (type_of% @oeis_219055_conjecture_1) := sorry
