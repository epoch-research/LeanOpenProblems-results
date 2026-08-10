import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option Elab.async false

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

namespace A219Proof

/-- Trial division by a sorted list of primes; stops once `p*p > m`. -/
def checkList (m : ℕ) : List ℕ → Bool
  | [] => true
  | p :: ps => if m < p * p then true
               else if m % p == 0 then false
               else checkList m ps

/-- Primes used as trial divisors (all primes up to 127). Sufficient for `m < 127^2 = 16129`. -/
def trialPrimes : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127]

def isP (m : ℕ) : Bool := decide (2 ≤ m) && checkList m trialPrimes

theorem checkList_sem (m : ℕ) : ∀ l, List.Pairwise (· ≤ ·) l → checkList m l = true →
    ∀ p ∈ l, p * p ≤ m → ¬ p ∣ m := by
  intro l
  induction l with
  | nil => intro _ _ p hp; simp at hp
  | cons a as ih =>
    intro hsorted hck p hp hpm
    rw [checkList] at hck
    have hsorted' : List.Pairwise (· ≤ ·) as := hsorted.tail
    have hahead : ∀ x ∈ as, a ≤ x := by
      intro x hx
      exact (List.pairwise_cons.mp hsorted).1 x hx
    by_cases hsmall : m < a * a
    · -- then a*a > m, but p ≥ a so p*p ≥ a*a > m, contradiction
      exfalso
      rcases List.mem_cons.mp hp with rfl | hpas
      · omega
      · have : a ≤ p := hahead p hpas
        have : a * a ≤ p * p := Nat.mul_le_mul this this
        omega
    · simp only [hsmall, if_false] at hck
      by_cases hmod : m % a = 0
      · simp [hmod] at hck
      · have hmodb : (m % a == 0) = false := by simpa using hmod
        simp only [hmodb] at hck
        rcases List.mem_cons.mp hp with rfl | hpas
        · rw [Nat.dvd_iff_mod_eq_zero]; exact hmod
        · exact ih hsorted' hck p hpas hpm

theorem trialPrimes_sorted : List.Pairwise (· ≤ ·) trialPrimes := by decide

theorem mem_trialPrimes_of_prime {p : ℕ} (hp : p.Prime) (hle : p ≤ 127) : p ∈ trialPrimes := by
  have : ∀ q, q ≤ 127 → q.Prime → q ∈ trialPrimes := by decide
  exact this p hle hp

theorem isP_imp_prime {m : ℕ} (hb : m < 16129) (h : isP m = true) : m.Prime := by
  unfold isP at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h2, hck⟩ := h
  have hm2 : 2 ≤ m := by simpa using h2
  by_contra hnp
  have hne1 : m ≠ 1 := by omega
  have hmf_prime : (m.minFac).Prime := Nat.minFac_prime hne1
  have hmf_dvd : m.minFac ∣ m := Nat.minFac_dvd m
  -- minFac^2 ≤ m
  have hle_div : m.minFac ≤ m / m.minFac := Nat.minFac_le_div (by omega) hnp
  have hsq : m.minFac * m.minFac ≤ m := by
    have h1 : m.minFac * m.minFac ≤ m.minFac * (m / m.minFac) :=
      Nat.mul_le_mul (le_refl _) hle_div
    have h2 : m.minFac * (m / m.minFac) ≤ m := by
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self m m.minFac
    omega
  have hmf_le : m.minFac ≤ 127 := by
    by_contra hcon
    push_neg at hcon
    have : 128 * 128 ≤ m.minFac * m.minFac := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hmem : m.minFac ∈ trialPrimes := mem_trialPrimes_of_prime hmf_prime hmf_le
  exact checkList_sem m trialPrimes trialPrimes_sorted hck m.minFac hmem hsq hmf_dvd

def primeList : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]

theorem primeList_prime : ∀ p ∈ primeList, p.Prime := by
  have hisp : ∀ p ∈ primeList, isP p = true := by decide
  have hbd : ∀ p ∈ primeList, p < 16129 := by decide
  intro p hp
  exact isP_imp_prime (hbd p hp) (hisp p hp)

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch0 : ∀ j, j < 500 → (4 ≤ 0 + j → Even (0 + j) → ∃ p ∈ primeList, isP ((0 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch500 : ∀ j, j < 500 → (4 ≤ 500 + j → Even (500 + j) → ∃ p ∈ primeList, isP ((500 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch1000 : ∀ j, j < 500 → (4 ≤ 1000 + j → Even (1000 + j) → ∃ p ∈ primeList, isP ((1000 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch1500 : ∀ j, j < 500 → (4 ≤ 1500 + j → Even (1500 + j) → ∃ p ∈ primeList, isP ((1500 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch2000 : ∀ j, j < 500 → (4 ≤ 2000 + j → Even (2000 + j) → ∃ p ∈ primeList, isP ((2000 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch2500 : ∀ j, j < 500 → (4 ≤ 2500 + j → Even (2500 + j) → ∃ p ∈ primeList, isP ((2500 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch3000 : ∀ j, j < 500 → (4 ≤ 3000 + j → Even (3000 + j) → ∃ p ∈ primeList, isP ((3000 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch3500 : ∀ j, j < 500 → (4 ≤ 3500 + j → Even (3500 + j) → ∃ p ∈ primeList, isP ((3500 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch4000 : ∀ j, j < 500 → (4 ≤ 4000 + j → Even (4000 + j) → ∃ p ∈ primeList, isP ((4000 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch4500 : ∀ j, j < 500 → (4 ≤ 4500 + j → Even (4500 + j) → ∃ p ∈ primeList, isP ((4500 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch5000 : ∀ j, j < 500 → (4 ≤ 5000 + j → Even (5000 + j) → ∃ p ∈ primeList, isP ((5000 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch5500 : ∀ j, j < 500 → (4 ≤ 5500 + j → Even (5500 + j) → ∃ p ∈ primeList, isP ((5500 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch6000 : ∀ j, j < 500 → (4 ≤ 6000 + j → Even (6000 + j) → ∃ p ∈ primeList, isP ((6000 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch6500 : ∀ j, j < 500 → (4 ≤ 6500 + j → Even (6500 + j) → ∃ p ∈ primeList, isP ((6500 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch7000 : ∀ j, j < 500 → (4 ≤ 7000 + j → Even (7000 + j) → ∃ p ∈ primeList, isP ((7000 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch7500 : ∀ j, j < 500 → (4 ≤ 7500 + j → Even (7500 + j) → ∃ p ∈ primeList, isP ((7500 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem gch8000 : ∀ j, j < 500 → (4 ≤ 8000 + j → Even (8000 + j) → ∃ p ∈ primeList, isP ((8000 + j) - p) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch0 : ∀ j, j < 500 → (7 ≤ 0 + j → Odd (0 + j) → ∃ q ∈ primeList, isP ((0 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch500 : ∀ j, j < 500 → (7 ≤ 500 + j → Odd (500 + j) → ∃ q ∈ primeList, isP ((500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch1000 : ∀ j, j < 500 → (7 ≤ 1000 + j → Odd (1000 + j) → ∃ q ∈ primeList, isP ((1000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch1500 : ∀ j, j < 500 → (7 ≤ 1500 + j → Odd (1500 + j) → ∃ q ∈ primeList, isP ((1500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch2000 : ∀ j, j < 500 → (7 ≤ 2000 + j → Odd (2000 + j) → ∃ q ∈ primeList, isP ((2000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch2500 : ∀ j, j < 500 → (7 ≤ 2500 + j → Odd (2500 + j) → ∃ q ∈ primeList, isP ((2500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch3000 : ∀ j, j < 500 → (7 ≤ 3000 + j → Odd (3000 + j) → ∃ q ∈ primeList, isP ((3000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch3500 : ∀ j, j < 500 → (7 ≤ 3500 + j → Odd (3500 + j) → ∃ q ∈ primeList, isP ((3500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch4000 : ∀ j, j < 500 → (7 ≤ 4000 + j → Odd (4000 + j) → ∃ q ∈ primeList, isP ((4000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch4500 : ∀ j, j < 500 → (7 ≤ 4500 + j → Odd (4500 + j) → ∃ q ∈ primeList, isP ((4500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch5000 : ∀ j, j < 500 → (7 ≤ 5000 + j → Odd (5000 + j) → ∃ q ∈ primeList, isP ((5000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch5500 : ∀ j, j < 500 → (7 ≤ 5500 + j → Odd (5500 + j) → ∃ q ∈ primeList, isP ((5500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch6000 : ∀ j, j < 500 → (7 ≤ 6000 + j → Odd (6000 + j) → ∃ q ∈ primeList, isP ((6000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch6500 : ∀ j, j < 500 → (7 ≤ 6500 + j → Odd (6500 + j) → ∃ q ∈ primeList, isP ((6500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch7000 : ∀ j, j < 500 → (7 ≤ 7000 + j → Odd (7000 + j) → ∃ q ∈ primeList, isP ((7000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch7500 : ∀ j, j < 500 → (7 ≤ 7500 + j → Odd (7500 + j) → ∃ q ∈ primeList, isP ((7500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch8000 : ∀ j, j < 500 → (7 ≤ 8000 + j → Odd (8000 + j) → ∃ q ∈ primeList, isP ((8000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch8500 : ∀ j, j < 500 → (7 ≤ 8500 + j → Odd (8500 + j) → ∃ q ∈ primeList, isP ((8500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch9000 : ∀ j, j < 500 → (7 ≤ 9000 + j → Odd (9000 + j) → ∃ q ∈ primeList, isP ((9000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch9500 : ∀ j, j < 500 → (7 ≤ 9500 + j → Odd (9500 + j) → ∃ q ∈ primeList, isP ((9500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch10000 : ∀ j, j < 500 → (7 ≤ 10000 + j → Odd (10000 + j) → ∃ q ∈ primeList, isP ((10000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch10500 : ∀ j, j < 500 → (7 ≤ 10500 + j → Odd (10500 + j) → ∃ q ∈ primeList, isP ((10500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch11000 : ∀ j, j < 500 → (7 ≤ 11000 + j → Odd (11000 + j) → ∃ q ∈ primeList, isP ((11000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch11500 : ∀ j, j < 500 → (7 ≤ 11500 + j → Odd (11500 + j) → ∃ q ∈ primeList, isP ((11500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch12000 : ∀ j, j < 500 → (7 ≤ 12000 + j → Odd (12000 + j) → ∃ q ∈ primeList, isP ((12000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch12500 : ∀ j, j < 500 → (7 ≤ 12500 + j → Odd (12500 + j) → ∃ q ∈ primeList, isP ((12500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch13000 : ∀ j, j < 500 → (7 ≤ 13000 + j → Odd (13000 + j) → ∃ q ∈ primeList, isP ((13000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch13500 : ∀ j, j < 500 → (7 ≤ 13500 + j → Odd (13500 + j) → ∃ q ∈ primeList, isP ((13500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch14000 : ∀ j, j < 500 → (7 ≤ 14000 + j → Odd (14000 + j) → ∃ q ∈ primeList, isP ((14000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch14500 : ∀ j, j < 500 → (7 ≤ 14500 + j → Odd (14500 + j) → ∃ q ∈ primeList, isP ((14500 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch15000 : ∀ j, j < 500 → (7 ≤ 15000 + j → Odd (15000 + j) → ∃ q ∈ primeList, isP ((15000 + j) - 2*q) = true) := by decide
set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem lch15500 : ∀ j, j < 500 → (7 ≤ 15500 + j → Odd (15500 + j) → ∃ q ∈ primeList, isP ((15500 + j) - 2*q) = true) := by decide

theorem goldbach_small (n : ℕ) (h4 : 4 ≤ n) (hn : n < 8013) (he : Even n) :
    ∃ a b, a.Prime ∧ b.Prime ∧ n = a + b := by
  have key : ∃ p ∈ primeList, isP (n - p) = true := by
    rcases (show n < 500 ∨ (500 ≤ n ∧ n < 1000) ∨ (1000 ≤ n ∧ n < 1500) ∨ (1500 ≤ n ∧ n < 2000) ∨ (2000 ≤ n ∧ n < 2500) ∨ (2500 ≤ n ∧ n < 3000) ∨ (3000 ≤ n ∧ n < 3500) ∨ (3500 ≤ n ∧ n < 4000) ∨ (4000 ≤ n ∧ n < 4500) ∨ (4500 ≤ n ∧ n < 5000) ∨ (5000 ≤ n ∧ n < 5500) ∨ (5500 ≤ n ∧ n < 6000) ∨ (6000 ≤ n ∧ n < 6500) ∨ (6500 ≤ n ∧ n < 7000) ∨ (7000 ≤ n ∧ n < 7500) ∨ (7500 ≤ n ∧ n < 8000) ∨ 8000 ≤ n from by omega) with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · have hb : (0:ℕ) + (n - 0) = n := by omega
      have := gch0 (n - 0) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (500:ℕ) + (n - 500) = n := by omega
      have := gch500 (n - 500) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (1000:ℕ) + (n - 1000) = n := by omega
      have := gch1000 (n - 1000) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (1500:ℕ) + (n - 1500) = n := by omega
      have := gch1500 (n - 1500) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (2000:ℕ) + (n - 2000) = n := by omega
      have := gch2000 (n - 2000) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (2500:ℕ) + (n - 2500) = n := by omega
      have := gch2500 (n - 2500) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (3000:ℕ) + (n - 3000) = n := by omega
      have := gch3000 (n - 3000) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (3500:ℕ) + (n - 3500) = n := by omega
      have := gch3500 (n - 3500) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (4000:ℕ) + (n - 4000) = n := by omega
      have := gch4000 (n - 4000) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (4500:ℕ) + (n - 4500) = n := by omega
      have := gch4500 (n - 4500) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (5000:ℕ) + (n - 5000) = n := by omega
      have := gch5000 (n - 5000) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (5500:ℕ) + (n - 5500) = n := by omega
      have := gch5500 (n - 5500) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (6000:ℕ) + (n - 6000) = n := by omega
      have := gch6000 (n - 6000) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (6500:ℕ) + (n - 6500) = n := by omega
      have := gch6500 (n - 6500) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (7000:ℕ) + (n - 7000) = n := by omega
      have := gch7000 (n - 7000) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (7500:ℕ) + (n - 7500) = n := by omega
      have := gch7500 (n - 7500) (by omega); rw [hb] at this; exact this h4 he
    · have hb : (8000:ℕ) + (n - 8000) = n := by omega
      have := gch8000 (n - 8000) (by omega); rw [hb] at this; exact this h4 he
  obtain ⟨p, hpmem, hnpP⟩ := key
  have hpprime : p.Prime := primeList_prime p hpmem
  have hnp : (n - p).Prime := isP_imp_prime (by omega) hnpP
  exact ⟨p, n - p, hpprime, hnp, by have := hnp.two_le; omega⟩

theorem lemoine_small (n : ℕ) (h7 : 7 ≤ n) (hn : n < 15728) (ho : Odd n) :
    ∃ p q, p.Prime ∧ q.Prime ∧ n = p + 2 * q := by
  have key : ∃ q ∈ primeList, isP (n - 2*q) = true := by
    rcases (show n < 500 ∨ (500 ≤ n ∧ n < 1000) ∨ (1000 ≤ n ∧ n < 1500) ∨ (1500 ≤ n ∧ n < 2000) ∨ (2000 ≤ n ∧ n < 2500) ∨ (2500 ≤ n ∧ n < 3000) ∨ (3000 ≤ n ∧ n < 3500) ∨ (3500 ≤ n ∧ n < 4000) ∨ (4000 ≤ n ∧ n < 4500) ∨ (4500 ≤ n ∧ n < 5000) ∨ (5000 ≤ n ∧ n < 5500) ∨ (5500 ≤ n ∧ n < 6000) ∨ (6000 ≤ n ∧ n < 6500) ∨ (6500 ≤ n ∧ n < 7000) ∨ (7000 ≤ n ∧ n < 7500) ∨ (7500 ≤ n ∧ n < 8000) ∨ (8000 ≤ n ∧ n < 8500) ∨ (8500 ≤ n ∧ n < 9000) ∨ (9000 ≤ n ∧ n < 9500) ∨ (9500 ≤ n ∧ n < 10000) ∨ (10000 ≤ n ∧ n < 10500) ∨ (10500 ≤ n ∧ n < 11000) ∨ (11000 ≤ n ∧ n < 11500) ∨ (11500 ≤ n ∧ n < 12000) ∨ (12000 ≤ n ∧ n < 12500) ∨ (12500 ≤ n ∧ n < 13000) ∨ (13000 ≤ n ∧ n < 13500) ∨ (13500 ≤ n ∧ n < 14000) ∨ (14000 ≤ n ∧ n < 14500) ∨ (14500 ≤ n ∧ n < 15000) ∨ (15000 ≤ n ∧ n < 15500) ∨ 15500 ≤ n from by omega) with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · have hb : (0:ℕ) + (n - 0) = n := by omega
      have := lch0 (n - 0) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (500:ℕ) + (n - 500) = n := by omega
      have := lch500 (n - 500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (1000:ℕ) + (n - 1000) = n := by omega
      have := lch1000 (n - 1000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (1500:ℕ) + (n - 1500) = n := by omega
      have := lch1500 (n - 1500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (2000:ℕ) + (n - 2000) = n := by omega
      have := lch2000 (n - 2000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (2500:ℕ) + (n - 2500) = n := by omega
      have := lch2500 (n - 2500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (3000:ℕ) + (n - 3000) = n := by omega
      have := lch3000 (n - 3000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (3500:ℕ) + (n - 3500) = n := by omega
      have := lch3500 (n - 3500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (4000:ℕ) + (n - 4000) = n := by omega
      have := lch4000 (n - 4000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (4500:ℕ) + (n - 4500) = n := by omega
      have := lch4500 (n - 4500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (5000:ℕ) + (n - 5000) = n := by omega
      have := lch5000 (n - 5000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (5500:ℕ) + (n - 5500) = n := by omega
      have := lch5500 (n - 5500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (6000:ℕ) + (n - 6000) = n := by omega
      have := lch6000 (n - 6000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (6500:ℕ) + (n - 6500) = n := by omega
      have := lch6500 (n - 6500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (7000:ℕ) + (n - 7000) = n := by omega
      have := lch7000 (n - 7000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (7500:ℕ) + (n - 7500) = n := by omega
      have := lch7500 (n - 7500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (8000:ℕ) + (n - 8000) = n := by omega
      have := lch8000 (n - 8000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (8500:ℕ) + (n - 8500) = n := by omega
      have := lch8500 (n - 8500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (9000:ℕ) + (n - 9000) = n := by omega
      have := lch9000 (n - 9000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (9500:ℕ) + (n - 9500) = n := by omega
      have := lch9500 (n - 9500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (10000:ℕ) + (n - 10000) = n := by omega
      have := lch10000 (n - 10000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (10500:ℕ) + (n - 10500) = n := by omega
      have := lch10500 (n - 10500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (11000:ℕ) + (n - 11000) = n := by omega
      have := lch11000 (n - 11000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (11500:ℕ) + (n - 11500) = n := by omega
      have := lch11500 (n - 11500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (12000:ℕ) + (n - 12000) = n := by omega
      have := lch12000 (n - 12000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (12500:ℕ) + (n - 12500) = n := by omega
      have := lch12500 (n - 12500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (13000:ℕ) + (n - 13000) = n := by omega
      have := lch13000 (n - 13000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (13500:ℕ) + (n - 13500) = n := by omega
      have := lch13500 (n - 13500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (14000:ℕ) + (n - 14000) = n := by omega
      have := lch14000 (n - 14000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (14500:ℕ) + (n - 14500) = n := by omega
      have := lch14500 (n - 14500) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (15000:ℕ) + (n - 15000) = n := by omega
      have := lch15000 (n - 15000) (by omega); rw [hb] at this; exact this h7 ho
    · have hb : (15500:ℕ) + (n - 15500) = n := by omega
      have := lch15500 (n - 15500) (by omega); rw [hb] at this; exact this h7 ho
  obtain ⟨q, hqmem, hpP⟩ := key
  have hqprime : q.Prime := primeList_prime q hqmem
  have hp : (n - 2*q).Prime := isP_imp_prime (by omega) hpP
  exact ⟨n - 2*q, q, hp, hqprime, by have := hp.two_le; omega⟩

theorem extract_mem {n : ℕ} (hpos : A219055 n > 0) :
    ∃ q, ((1 + n % 2) + 1) * q < n ∧ q.Prime ∧ (q + 6).Prime ∧
      (n - (1 + n % 2) * q).Prime ∧ (n - (1 + n % 2) * q - 6).Prime := by
  rw [A219055] at hpos
  have hne := Finset.card_pos.mp hpos
  obtain ⟨q, hq⟩ := hne
  rw [Finset.mem_filter] at hq
  exact ⟨q, hq.2⟩

end A219Proof


open A219Proof in
theorem oeis_219055_conjecture_1 :
    a219055_core_conjecture → goldbach_conjecture ∧ lemoine_conjecture ∧ six_prime_gap_conjecture := by
  intro core
  refine ⟨?_, ?_, ?_⟩
  · intro n h4 he
    by_cases hbig : 8012 < n
    · have hpos := core n (Or.inl ⟨he, hbig⟩)
      obtain ⟨q, hlt, hq, _, hp, _⟩ := extract_mem hpos
      have hn2 : n % 2 = 0 := Nat.even_iff.mp he
      rw [hn2] at hlt hp
      simp only [Nat.add_zero, one_mul] at hlt hp
      refine ⟨n - q, q, ?_, hq, by omega⟩
      simpa using hp
    · exact goldbach_small n h4 (by omega) he
  · intro n h7 ho
    by_cases hbig : 15727 < n
    · have hpos := core n (Or.inr ⟨ho, hbig⟩)
      obtain ⟨q, hlt, hq, _, hp, _⟩ := extract_mem hpos
      have hn2 : n % 2 = 1 := Nat.odd_iff.mp ho
      rw [hn2] at hlt hp
      refine ⟨n - (1 + 1) * q, q, ?_, hq, by omega⟩
      simpa using hp
    · exact lemoine_small n h7 (by omega) ho
  · rw [six_prime_gap_conjecture]
    apply Set.infinite_of_not_bddAbove
    rw [not_bddAbove_iff]
    intro x
    set n := 2 * (x + 4007) with hn
    have hbig : 8012 < n := by omega
    have heven : Even n := ⟨x + 4007, by omega⟩
    have hpos := core n (Or.inl ⟨heven, hbig⟩)
    obtain ⟨q, hlt, hq, _, hp, hp6⟩ := extract_mem hpos
    have hn2 : n % 2 = 0 := Nat.even_iff.mp heven
    rw [hn2] at hlt hp hp6
    simp only [Nat.add_zero, one_mul] at hlt hp hp6
    refine ⟨n - q - 6, ⟨hp6, ?_⟩, ?_⟩
    · have h2 : 2 ≤ n - q - 6 := hp6.two_le
      have : n - q - 6 + 6 = n - q := by omega
      rw [this]; exact hp
    · have h2 : 2 ≤ n - q - 6 := hp6.two_le
      omega
