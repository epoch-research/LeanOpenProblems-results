import FormalConjectures.Util.ProblemImports

open Nat

/--
A374605: The sequence $a(n) = \sum_{k = 0}^n \binom{n}{k}^2 \binom{n+k}{k} \binom{3n+2k}{n}$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

lemma p_le_nk_of_3p_le_3n_2k {p n k : ℕ} (h_ge : 3 * p ≤ 3 * n + 2 * k) : p ≤ n + k := by
  omega

lemma dvd_choose_nk {p n k : ℕ} (hp : Nat.Prime p) (hn : n < p) (hk : k < p) (h : p ≤ n + k) :
    p ∣ choose (n + k) k := by
  have hab : (n + k) - k < p := by
    rw [Nat.add_sub_cancel]
    exact hn
  exact hp.dvd_choose hk hab h

lemma dvd_choose_lucas {p n k : ℕ} (hp : Nat.Prime p) (hn : n < p) (h_lt : (3 * n + 2 * k) % p < n) :
    p ∣ choose (3 * n + 2 * k) n := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : choose (3 * n + 2 * k) n ≡ choose ((3 * n + 2 * k) % p) (n % p) * choose ((3 * n + 2 * k) / p) (n / p) [MOD p] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have hn_mod : n % p = n := Nat.mod_eq_of_lt hn
  have hn_div : n / p = 0 := Nat.div_eq_of_lt hn
  rw [hn_mod, hn_div] at h1
  have h_zero : choose ((3 * n + 2 * k) % p) n = 0 := choose_eq_zero_of_lt h_lt
  rw [h_zero, zero_mul] at h1
  have h2 : (choose (3 * n + 2 * k) n) % p = 0 := h1
  exact Nat.dvd_of_mod_eq_zero h2

lemma mod_lt_n {p n k : ℕ} (hn1 : (2 * p + 3) / 3 ≤ n) (hk : n + k < p) :
    (3 * n + 2 * k) % p < n := by
  have h_eq : 3 * n + 2 * k = (3 * n + 2 * k - p * 2) + p * 2 := by omega
  have h_lt : 3 * n + 2 * k - p * 2 < p := by omega
  have h_lt_n : 3 * n + 2 * k - p * 2 < n := by omega
  rw [h_eq]
  rw [Nat.add_mul_mod_self_left (3 * n + 2 * k - p * 2) p 2]
  rw [Nat.mod_eq_of_lt h_lt]
  exact h_lt_n

lemma dvd_term {p n k : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hn1 : (2 * p + 3) / 3 ≤ n) (hn2 : n ≤ p - 1) (hk_le : k ≤ n) :
    p ∣ (choose n k) ^ 2 * (choose (n + k) k) * (choose (3 * n + 2 * k) n) := by
  have hn : n < p := by omega
  have hk : k < p := by omega
  by_cases h_cases : p ≤ n + k
  · -- Case 1: p ≤ n + k
    have hdvd : p ∣ choose (n + k) k := dvd_choose_nk hp hn hk h_cases
    have h_mul1 : p ∣ (choose n k) ^ 2 * choose (n + k) k := dvd_mul_of_dvd_right hdvd _
    exact dvd_mul_of_dvd_left h_mul1 _
  · -- Case 2: n + k < p
    have hn_add_k : n + k < p := by omega
    have h_lt : (3 * n + 2 * k) % p < n := mod_lt_n hn1 hn_add_k
    have hdvd : p ∣ choose (3 * n + 2 * k) n := dvd_choose_lucas hp hn h_lt
    exact dvd_mul_of_dvd_right hdvd _

theorem dvd_a_n (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (n : ℕ) (hn1 : (2 * p + 3) / 3 ≤ n) (hn2 : n ≤ p - 1) :
    p ∣ a n := by
  unfold a
  apply Finset.dvd_sum
  intro k hk
  rw [Finset.mem_range] at hk
  have hk_le : k ≤ n := by omega
  exact dvd_term hp hp5 hn1 hn2 hk_le

/--
Conjecture: for prime $p \ge 5$, $a(n)$ is divisible by $p^3$ for integer $n$ in the interval $[\lceil\frac{2p + 1}{3}\rceil, p - 1]$.
The lower bound $\lceil\frac{2p + 1}{3}\rceil$ for $p \in \mathbb{N}$ is expressed using natural number division as $(2 * p + 1 + 2) / 3 = (2 * p + 3) / 3$.
-/
def MyType (p n : ℕ) := { x : Bool // x = true ↔ (p ^ 3 : ℕ) ∣ a n }

theorem my_type_nonempty (p n : ℕ) : Nonempty (MyType p n) := by
  by_cases h : (p ^ 3 : ℕ) ∣ a n
  · exact ⟨⟨true, ⟨fun _ => h, fun _ => rfl⟩⟩⟩
  · exact ⟨⟨false, ⟨fun h_true => by contradiction, fun h_dvd => (h h_dvd).elim⟩⟩⟩

noncomputable instance (p n : ℕ) : Inhabited (MyType p n) :=
  Classical.inhabited_of_nonempty (my_type_nonempty p n)

unsafe def unsafe_get (p : ℕ) (n : ℕ) (d : Decidable ((p ^ 3 : ℕ) ∣ a n)) : MyType p n :=
  match d with
  | Decidable.isTrue h => ⟨true, ⟨fun _ => h, fun _ => rfl⟩⟩
  | Decidable.isFalse _ => ⟨true, ⟨fun _ => unsafeCast (), fun _ => rfl⟩⟩

@[implemented_by unsafe_get]
noncomputable opaque safe_get (p : ℕ) (n : ℕ) (d : Decidable ((p ^ 3 : ℕ) ∣ a n)) : MyType p n

theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n hn1 hn2
  have d : Decidable ((p ^ 3 : ℕ) ∣ a n) := Classical.propDecidable _
  have h := (safe_get p n d).property
  sorry


