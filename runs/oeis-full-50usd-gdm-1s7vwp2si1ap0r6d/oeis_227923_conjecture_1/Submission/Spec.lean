import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A227923: Number of ways to write $n = x + y$ ($x, y > 0$) such that $6x-1$ is a Sophie Germain prime and $\{6y-1, 6y+1\}$ is a twin prime pair.
-/
def A227923 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun x =>
    let y : ℕ := n - x
    -- The condition for the sum. The term (12 * x - 1).Prime checks if 2 * (6 * x - 1) + 1 is prime,
    -- which is the definition of a Sophie Germain prime when 6x-1 is prime.
    if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime then 1 else 0

/--
The set of all Sophie Germain primes. A prime $p$ is a Sophie Germain prime if $p \ge 2$ and $2p+1$ is also prime.
-/
def SophieGermainPrimes : Set ℕ :=
  {p : ℕ | p.Prime ∧ (2 * p + 1).Prime}

/--
The set of all twin primes. A prime $p$ is a twin prime if $p+2$ is also prime.
We choose the smaller prime in the pair to represent the set.
-/
def TwinPrimes : Set ℕ :=
  {p : ℕ | p.Prime ∧ (p + 2).Prime}

lemma sum_pos_iff_exists_pos {α : Type*} (s : Finset α) (f : α → ℕ) :
  0 < s.sum f ↔ ∃ x ∈ s, 0 < f x := by
  exact sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)

lemma if_pos_of_gt_zero {P : Prop} [Decidable P] (h : 0 < (if P then 1 else 0)) : P := by
  by_contra hp
  rw [if_neg hp] at h
  exact Nat.lt_irrefl 0 h

lemma sg_arith (x : ℕ) (hx : x ≥ 1) : 12 * x - 1 = 2 * (6 * x - 1) + 1 := by
  omega

lemma twin_arith (y : ℕ) (hy : 1 ≤ y) : (6 * y - 1) + 2 = 6 * y + 1 := by
  omega

lemma factorial_five_le (M : ℕ) (hM : 5 ≤ M) : 120 ≤ Nat.factorial M := by
  have h1 : Nat.factorial 5 ≤ Nat.factorial M := Nat.factorial_le hM
  have h2 : Nat.factorial 5 = 120 := rfl
  rw [h2] at h1
  exact h1

lemma sg_composite_arith (x y : ℕ) (_hy : 1 ≤ y) (h : 6 * y + 1 = 6 * x - 1) : 12 * x - 1 = 3 * (4 * y + 1) := by
  omega

lemma composite_contradiction (x y : ℕ) (h_eq : 12 * x - 1 = 3 * (4 * y + 1)) (hp : Nat.Prime (12 * x - 1)) : False := by
  have h_dvd : 3 ∣ 12 * x - 1 := by
    rw [h_eq]
    exact ⟨4 * y + 1, rfl⟩
  cases hp.eq_one_or_self_of_dvd 3 h_dvd with
  | inl h => omega
  | inr h =>
    rw [h_eq] at h
    omega

lemma exists_gt_of_contradiction {s : Set ℕ} (a : ℕ) (h_not : ¬ ∃ b ∈ s, a < b) : ∀ b ∈ s, b ≤ a := by
  intro b hb
  by_contra h_gt
  have h_lt : a < b := by omega
  exact h_not ⟨b, hb, h_lt⟩

lemma sg_infinite (h_premise : ∀ (n : ℕ), 1 < n → A227923 n > 0) : Set.Infinite SophieGermainPrimes := by
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  by_contra h_not
  have h_bound : ∀ b ∈ SophieGermainPrimes, b ≤ N := exists_gt_of_contradiction N h_not
  let M := N + 6
  have hM : 5 ≤ M := by omega
  have h_div : 6 ∣ Nat.factorial M := Nat.dvd_factorial (by omega) (by omega)
  let n := Nat.factorial M / 6
  have h_fact_eq : 6 * n = Nat.factorial M := Nat.mul_div_cancel' h_div
  have h_fact_ge : 120 ≤ Nat.factorial M := factorial_five_le M hM
  have hn : 1 < n := by omega
  have h_a227923 : 0 < A227923 n := h_premise n hn
  rw [A227923] at h_a227923
  rw [sum_pos_iff_exists_pos] at h_a227923
  rcases h_a227923 with ⟨x, hx_ico, h_if⟩
  rw [mem_Ico] at hx_ico
  let y := n - x
  have h_P : (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime := if_pos_of_gt_zero h_if
  rcases h_P with ⟨h1, h2, h3, h4⟩
  have h_sg : 6 * x - 1 ∈ SophieGermainPrimes := by
    simp only [SophieGermainPrimes, Set.mem_setOf_eq]
    refine ⟨h1, ?_⟩
    rw [← sg_arith x (by omega)]
    exact h2
  have h_le_N : 6 * x - 1 ≤ N := h_bound (6 * x - 1) h_sg
  have h_lt_M : 6 * x - 1 < M := by omega
  have h_ge_5 : 6 * x - 1 ≥ 5 := by omega
  have h_dvd_fact : 6 * x - 1 ∣ Nat.factorial M := Nat.dvd_factorial (by omega) (by omega)
  have h_xy : x + y = n := by omega
  have h_sum : 6 * x + 6 * y = Nat.factorial M := by omega
  have h_sum2 : (6 * x - 1) + (6 * y + 1) = Nat.factorial M := by omega
  have h_eq : 6 * y + 1 = Nat.factorial M - (6 * x - 1) := by omega
  have h_dvd_twin : 6 * x - 1 ∣ 6 * y + 1 := by
    rw [h_eq]
    exact Nat.dvd_sub h_dvd_fact dvd_rfl
  cases h4.eq_one_or_self_of_dvd (6 * x - 1) h_dvd_twin with
  | inl h_one => omega
  | inr h_self =>
    have h_self' : 6 * y + 1 = 6 * x - 1 := by omega
    have h_comp : 12 * x - 1 = 3 * (4 * y + 1) := sg_composite_arith x y (by omega) h_self'
    exact composite_contradiction x y h_comp h2

lemma twin_infinite (h_premise : ∀ (n : ℕ), 1 < n → A227923 n > 0) : Set.Infinite TwinPrimes := by
  apply Set.infinite_iff_exists_gt.mpr
  intro N
  by_contra h_not
  have h_bound : ∀ b ∈ TwinPrimes, b ≤ N := exists_gt_of_contradiction N h_not
  let M := N + 6
  have hM : 5 ≤ M := by omega
  have h_div : 6 ∣ Nat.factorial M := Nat.dvd_factorial (by omega) (by omega)
  let n := Nat.factorial M / 6
  have h_fact_eq : 6 * n = Nat.factorial M := Nat.mul_div_cancel' h_div
  have h_fact_ge : 120 ≤ Nat.factorial M := factorial_five_le M hM
  have hn : 1 < n := by omega
  have h_a227923 : 0 < A227923 n := h_premise n hn
  rw [A227923] at h_a227923
  rw [sum_pos_iff_exists_pos] at h_a227923
  rcases h_a227923 with ⟨x, hx_ico, h_if⟩
  rw [mem_Ico] at hx_ico
  let y := n - x
  have h_P : (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime := if_pos_of_gt_zero h_if
  rcases h_P with ⟨h1, h2, h3, h4⟩
  have h_tw : 6 * y - 1 ∈ TwinPrimes := by
    simp only [TwinPrimes, Set.mem_setOf_eq]
    refine ⟨h3, ?_⟩
    rw [twin_arith y (by omega)]
    exact h4
  have h_le_N : 6 * y - 1 ≤ N := h_bound (6 * y - 1) h_tw
  have h_lt_M : 6 * y + 1 < M := by omega
  have h_ge_5 : 6 * y + 1 ≥ 5 := by omega
  have h_dvd_fact : 6 * y + 1 ∣ Nat.factorial M := Nat.dvd_factorial (by omega) (by omega)
  have h_xy : x + y = n := by omega
  have h_sum : 6 * x + 6 * y = Nat.factorial M := by omega
  have h_sum2 : (6 * x - 1) + (6 * y + 1) = Nat.factorial M := by omega
  have h_eq : 6 * x - 1 = Nat.factorial M - (6 * y + 1) := by omega
  have h_dvd_sg : 6 * y + 1 ∣ 6 * x - 1 := by
    rw [h_eq]
    exact Nat.dvd_sub h_dvd_fact dvd_rfl
  cases h1.eq_one_or_self_of_dvd (6 * y + 1) h_dvd_sg with
  | inl h_one => omega
  | inr h_self =>
    have h_comp : 12 * x - 1 = 3 * (4 * y + 1) := sg_composite_arith x y (by omega) h_self
    exact composite_contradiction x y h_comp h2

/--
oeis_227923_conjecture_1: Part (i) of the conjecture implies that there are
infinitely many Sophie Germain primes, and also infinitely many twin prime pairs.
For example, if all twin primes does not exceed an integer N > 2, and (N+1)!/6 = x + y
with 6*x-1 a Sophie Germain prime and {6*y-1, 6*y+1} a twin prime pair, then
(N+1)! = (6*x-1) + (6*y+1) with 1 < 6*y+1 < N+1, hence we get a contradiction since
(N+1)! - k is composite for every k = 2..N.
-/
theorem oeis_227923_conjecture_1 :
  (∀ (n : ℕ), 1 < n → A227923 n > 0) →
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) :=
by
  intro h_premise
  exact ⟨sg_infinite h_premise, twin_infinite h_premise⟩
