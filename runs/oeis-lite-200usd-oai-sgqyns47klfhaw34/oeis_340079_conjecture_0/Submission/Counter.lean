import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def a (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

lemma sum_gcd_range_eq (n : ℕ) :
    (∑ k ∈ Finset.range n, Nat.gcd n k) =
      ∑ d ∈ n.divisors, d * Nat.totient (n / d) := by
  have Hmap : ∀ k ∈ Finset.range n, Nat.gcd n k ∈ n.divisors := by
    intro k hk
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n k, (lt_of_le_of_lt (Nat.zero_le k) (Finset.mem_range.mp hk)).ne'⟩
  calc
    (∑ k ∈ Finset.range n, Nat.gcd n k)
        = ∑ d ∈ n.divisors, ∑ k ∈ (Finset.range n).filter (fun k => Nat.gcd n k = d), Nat.gcd n k := by
          rw [Finset.sum_fiberwise_of_maps_to Hmap]
    _ = ∑ d ∈ n.divisors, d * Nat.totient (n / d) := by
          apply Finset.sum_congr rfl
          intro d hd
          calc
            (∑ k ∈ (Finset.range n).filter (fun k => Nat.gcd n k = d), Nat.gcd n k)
                = ∑ k ∈ (Finset.range n).filter (fun k => Nat.gcd n k = d), d := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  exact (Finset.mem_filter.mp hk).2
            _ = ((Finset.range n).filter (fun k => Nat.gcd n k = d)).card * d := by simp
            _ = d * Nat.totient (n / d) := by
                  rw [Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
                  rw [Nat.mul_comm]

lemma sum_Ico_gcd_eq_range (n : ℕ) :
    (∑ k ∈ Finset.Ico 1 (n + 1), Nat.gcd k n) =
      ∑ k ∈ Finset.range n, Nat.gcd n k := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hI : Finset.Ico 1 (n + 1) = insert n (Finset.Ico 1 n) := by
    ext k
    simp [Finset.mem_Ico]
    omega
  have hR : Finset.range n = insert 0 (Finset.Ico 1 n) := by
    ext k
    simp [Finset.mem_Ico]
    omega
  rw [hI, hR]
  simp [Finset.mem_Ico, Nat.gcd_comm]



abbrev N : ℕ := 23492890653051

def totientAF : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

def gcdSumAF : ArithmeticFunction ℕ := ArithmeticFunction.id * totientAF

lemma isMultiplicative_totientAF : ArithmeticFunction.IsMultiplicative totientAF := by
  refine ⟨Nat.totient_one, ?_⟩
  intro m n hmn
  exact Nat.totient_mul hmn

lemma isMultiplicative_gcdSumAF : ArithmeticFunction.IsMultiplicative gcdSumAF :=
  ArithmeticFunction.isMultiplicative_id.mul isMultiplicative_totientAF

lemma divisor_sum_eq_gcdSumAF (n : ℕ) :
    (∑ d ∈ n.divisors, d * Nat.totient (n / d)) = gcdSumAF n := by
  rw [gcdSumAF, ArithmeticFunction.mul_apply]
  rw [← Nat.map_div_right_divisors (n := n), Finset.sum_map]
  rfl

lemma gcdSumAF_prime {p : ℕ} (hp : Nat.Prime p) : gcdSumAF p = 2 * p - 1 := by
  rw [← divisor_sum_eq_gcdSumAF, hp.divisors]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    rw [Nat.div_one, Nat.div_self hp.pos, Nat.totient_one, Nat.totient_prime hp]
    omega
  · have h1p : 1 ≠ p := fun h => hp.ne_one h.symm
    simp [h1p]

lemma gcdSumAF_N : gcdSumAF N = 26 * N - 1 := by
  have hN : N = ((((3 * 37) * 43) * 42307) * 116341) := by norm_num [N]
  rw [hN]
  repeat rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime isMultiplicative_gcdSumAF (by norm_num [Nat.coprime_iff_gcd_eq_one])]
  rw [gcdSumAF_prime (by norm_num), gcdSumAF_prime (by norm_num), gcdSumAF_prime (by norm_num),
    gcdSumAF_prime (by norm_num), gcdSumAF_prime (by norm_num)]
  norm_num

lemma sum_gcd_N :
    (∑ k ∈ Finset.Ico 1 (N + 1), Nat.gcd k N) = 26 * N - 1 := by
  rw [sum_Ico_gcd_eq_range, sum_gcd_range_eq, divisor_sum_eq_gcdSumAF, gcdSumAF_N]

lemma a_N : a N = 1 := by
  rw [a]
  rw [sum_gcd_N]
  have hsum : 1 + (26 * N - 1) = 26 * N := by norm_num [N]
  rw [hsum]
  have hg : Nat.gcd N (26 * N) = N := by
    rw [Nat.gcd_eq_left_iff_dvd]
    exact ⟨26, by rw [mul_comm]⟩
  rw [hg]
  exact Nat.div_self (by norm_num [N] : 0 < N)


lemma not_rhs_N : ¬ (N = 1 ∨ Nat.Prime N) := by
  intro h
  rcases h with h1 | hp
  · norm_num [N] at h1
  · exact Nat.not_prime_of_dvd_of_ne (m := 3) (n := N) (by norm_num [N]) (by norm_num) (by norm_num [N]) hp

theorem oeis_340079_conjecture_0.disproof :
    ¬ (∀ n : ℕ, a n = 1 ↔ (n = 1 ∨ Nat.Prime n)) := by
  intro h
  exact not_rhs_N ((h N).mp a_N)


