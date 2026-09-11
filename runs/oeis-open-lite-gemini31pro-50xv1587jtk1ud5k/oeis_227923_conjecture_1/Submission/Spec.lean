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

lemma A227923_pos_implies {n : ℕ} (h : A227923 n > 0) :
  ∃ x y : ℕ, 1 ≤ x ∧ x < n ∧ y = n - x ∧
  (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime := by
  dsimp [A227923] at h
  have h1 : ∃ x ∈ Ico 1 n, (fun x => let y := n - x; if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime then 1 else 0) x > 0 := by
    by_contra! h2
    have h3 : (Ico 1 n).sum (fun x => let y := n - x; if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime then (1 : ℕ) else 0) = 0 :=
      sum_eq_zero (fun x hx => Nat.le_antisymm (h2 x hx) (Nat.zero_le _))
    rw [h3] at h
    omega
  rcases h1 with ⟨x, hx, hx2⟩
  rw [mem_Ico] at hx
  use x, n - x
  refine ⟨hx.1, hx.2, rfl, ?_⟩
  dsimp at hx2
  split at hx2
  next h_cond => exact h_cond
  next => omega

lemma factorial_dvd_six (N : ℕ) (h : 6 ≤ N) : 6 ∣ N.factorial := by
  apply Nat.dvd_factorial <;> omega

lemma div_six_mul_six (N : ℕ) (h : 6 ≤ N) : 6 * (N.factorial / 6) = N.factorial := by
  exact Nat.mul_div_cancel' (factorial_dvd_six N h)

lemma factorial_div_six_gt_one (N : ℕ) (h : 7 ≤ N) : 1 < N.factorial / 6 := by
  have h1 : 6 * 1 < 6 * (N.factorial / 6) := by
    rw [div_six_mul_six N (by omega)]
    have h2 : 6 < Nat.factorial 7 := by decide
    have h3 : Nat.factorial 7 ≤ N.factorial := Nat.factorial_le (by omega)
    omega
  omega

lemma finite_bdd (S : Set ℕ) (h : S.Finite) : ∃ M, ∀ x ∈ S, x ≤ M := by
  have := h.bddAbove
  rcases this with ⟨M, hM⟩
  use M
  intro x hx
  exact hM hx

lemma div_prime {P K : ℕ} (hP : P.Prime) (hK : K > 1) (hdvd : K ∣ P) : K = P := by
  rcases hP.eq_one_or_self_of_dvd K hdvd with h | h
  · linarith
  · exact h

lemma sophie_germain_primes_infinite (h_conj : ∀ (n : ℕ), 1 < n → A227923 n > 0) : Set.Infinite SophieGermainPrimes := by
  intro h_fin
  rcases finite_bdd SophieGermainPrimes h_fin with ⟨M, hM⟩
  let N := M + 7
  have hN : 7 ≤ N := by omega
  let n := N.factorial / 6
  have hn_gt1 : 1 < n := factorial_div_six_gt_one N hN
  have h_A227923 := h_conj n hn_gt1
  rcases A227923_pos_implies h_A227923 with ⟨x, y, hx_ge1, hx_lt, hy_eq, h6xm1_pr, h12xm1_pr, h6ym1_pr, h6yp1_pr⟩
  have hy_ge1 : 1 ≤ y := by omega
  have h_sg : 6 * x - 1 ∈ SophieGermainPrimes := by
    dsimp [SophieGermainPrimes]
    refine ⟨h6xm1_pr, ?_⟩
    have h_eq : 2 * (6 * x - 1) + 1 = 12 * x - 1 := by omega
    rw [h_eq]
    exact h12xm1_pr
  have h6xm1_le_M : 6 * x - 1 ≤ M := hM (6 * x - 1) h_sg
  have h6xp1_le_N : 6 * x + 1 ≤ N := by omega
  have h6xp1_ge7 : 7 ≤ 6 * x + 1 := by omega
  have h6xp1_dvd_N_fact : 6 * x + 1 ∣ N.factorial := by
    apply Nat.dvd_factorial <;> omega
  have h_sum_mul6 : 6 * x + 6 * y = N.factorial := by
    have h_n_sum : x + y = n := by omega
    have h_sum_mul6_1 : 6 * (x + y) = 6 * n := by omega
    rw [mul_add] at h_sum_mul6_1
    have h_6n_eq_N_fact : 6 * n = N.factorial := div_six_mul_six N (by omega)
    omega
  have h6xp1_dvd_6ym1 : 6 * x + 1 ∣ 6 * y - 1 := by
    have h_eq : 6 * y - 1 = N.factorial - (6 * x + 1) := by omega
    rw [h_eq]
    apply Nat.dvd_sub
    · exact h6xp1_dvd_N_fact
    · exact dvd_rfl
  have h_eq2 : 6 * x + 1 = 6 * y - 1 := div_prime h6ym1_pr (by omega) h6xp1_dvd_6ym1
  omega

lemma twin_primes_infinite (h_conj : ∀ (n : ℕ), 1 < n → A227923 n > 0) : Set.Infinite TwinPrimes := by
  intro h_fin
  rcases finite_bdd TwinPrimes h_fin with ⟨M, hM⟩
  let N := M + 7
  have hN : 7 ≤ N := by omega
  let n := N.factorial / 6
  have hn_gt1 : 1 < n := factorial_div_six_gt_one N hN
  have h_A227923 := h_conj n hn_gt1
  rcases A227923_pos_implies h_A227923 with ⟨x, y, hx_ge1, hx_lt, hy_eq, h6xm1_pr, h12xm1_pr, h6ym1_pr, h6yp1_pr⟩
  have hy_ge1 : 1 ≤ y := by omega
  have h_twin : 6 * y - 1 ∈ TwinPrimes := by
    dsimp [TwinPrimes]
    refine ⟨h6ym1_pr, ?_⟩
    have h_eq : (6 * y - 1) + 2 = 6 * y + 1 := by omega
    rw [h_eq]
    exact h6yp1_pr
  have h6ym1_le_M : 6 * y - 1 ≤ M := hM (6 * y - 1) h_twin
  have h6yp1_le_N : 6 * y + 1 ≤ N := by omega
  have h6yp1_ge7 : 7 ≤ 6 * y + 1 := by omega
  have h6yp1_dvd_N_fact : 6 * y + 1 ∣ N.factorial := by
    apply Nat.dvd_factorial <;> omega
  have h_sum_mul6 : 6 * x + 6 * y = N.factorial := by
    have h_n_sum : x + y = n := by omega
    have h_sum_mul6_1 : 6 * (x + y) = 6 * n := by omega
    rw [mul_add] at h_sum_mul6_1
    have h_6n_eq_N_fact : 6 * n = N.factorial := div_six_mul_six N (by omega)
    omega
  have h6yp1_dvd_6xm1 : 6 * y + 1 ∣ 6 * x - 1 := by
    have h_eq : 6 * x - 1 = N.factorial - (6 * y + 1) := by omega
    rw [h_eq]
    apply Nat.dvd_sub
    · exact h6yp1_dvd_N_fact
    · exact dvd_rfl
  have h_eq2 : 6 * y + 1 = 6 * x - 1 := div_prime h6xm1_pr (by omega) h6yp1_dvd_6xm1
  omega

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
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) := by
  intro h_conj
  exact ⟨sophie_germain_primes_infinite h_conj, twin_primes_infinite h_conj⟩

theorem oeis_227923_conjecture_1.disproof : ¬ (type_of% @oeis_227923_conjecture_1) := sorry
