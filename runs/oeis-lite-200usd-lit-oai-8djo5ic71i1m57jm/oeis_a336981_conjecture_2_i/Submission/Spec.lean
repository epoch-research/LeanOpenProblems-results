import FormalConjectures.Util.ProblemImports



open Nat Finset
open scoped BigOperators

/--
The coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
$$ T_k(b, c) = \sum_{i=0}^{\lfloor k/2 \rfloor} \binom{k}{i} \binom{k-i}{i} b^{k-2i} c^i $$
-/
def T_k (k : ℕ) (b c : ℤ) : ℚ :=
  Finset.sum (range (k / 2 + 1)) (fun i : ℕ =>
    -- The multinomial coefficient $\binom{k}{i, i, k-2i}$
    ((k.choose i * (k - i).choose i : ℕ) : ℚ) *
    -- Powers of b and c
    ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i))

/--
A336981: $$a(n) = \frac{\sum_{k=0}^{n-1} (4290k + 367) \cdot 3136^{n-1-k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)}{n \cdot \binom{2n-1}{n-1}}$$
where $T_k(b, c)$ denotes the coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
The sequence is defined as a function $\mathbb{N} \to \mathbb{Q}$.
-/
noncomputable def a (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    let numerator_sum : ℚ :=
      Finset.sum (range n) (fun k : ℕ =>
        let T1k : ℚ := T_k k 14 1
        let T2k : ℚ := T_k k 17 16

        let k_q : ℚ := k
        -- We use casting for the exponent subtraction to ensure it stays non-negative when k <= n-1
        let n_prime : ℕ := n - 1 - k

        let term_factor : ℚ := 4290 * k_q + 367
        let power_factor : ℚ := (3136 : ℚ) ^ n_prime
        let central_binomial : ℚ := (Nat.choose (2 * k) k : ℚ)

        term_factor * power_factor * central_binomial * T1k * T2k)

    let divisor : ℚ := (n : ℚ) * (Nat.choose (2 * n - 1) (n - 1) : ℚ)

    numerator_sum / divisor

-- Definition for t(k) for the infinite sum
/--
$$t(k) = \frac{4290k+367}{3136^k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)$$
-/
noncomputable def t (k : ℕ) : ℝ :=
  let T1k : ℝ := T_k k 14 1
  let T2k : ℝ := T_k k 17 16
  let k_r : ℝ := k
  let central_binomial : ℝ := (Nat.choose (2 * k) k : ℝ)

  let term_factor : ℝ := 4290 * k_r + 367
  let power_factor : ℝ := (3136 : ℝ) ^ k

  term_factor / power_factor * central_binomial * T1k * T2k



/--
Conjecture 2 (i): We have $\sum_{k \ge 0} t(k) = 5390/\pi$.

Denote (4290k+367)/3136^k*C(2k,k)*T_k(14,1)*T_k(17,16) by t(k).
(i) We have Sum_{k>=0}t(k) = 5390/Pi.
-/

noncomputable def Aseq (n : ℕ) : ℝ :=
  (n:ℝ) * (Nat.choose (2*n) n : ℝ)^2 / (16:ℝ)^n

lemma central_choose_succ (n : ℕ) :
    (Nat.choose (2*(n+1)) (n+1) : ℝ) =
      (2:ℝ) * (2*n+1) * (Nat.choose (2*n) n : ℝ) / (n+1) := by
  have h1 : Nat.choose (2*(n+1)) (n+1) = 2 * Nat.choose (2*n+1) n := by
    calc
      Nat.choose (2*(n+1)) (n+1) = Nat.choose (2*n+2) (n+1) := by ring_nf
      _ = Nat.choose (2*n+1) n + Nat.choose (2*n+1) (n+1) := by
        rw [show 2*n+2 = (2*n+1).succ by omega, show n+1 = n.succ by omega, Nat.choose_succ_succ]
      _ = Nat.choose (2*n+1) n + Nat.choose (2*n+1) n := by
        have hh := Nat.choose_succ_right_eq (2*n+1) n
        have hsub : 2*n+1 - n = n+1 := by omega
        rw [hsub] at hh
        exact congrArg (fun z => Nat.choose (2*n+1) n + z)
          (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n) (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hh))
      _ = 2 * Nat.choose (2*n+1) n := by omega
  have h2 := Nat.choose_mul_succ_eq (2*n) n
  have hsub : 2*n+1 - n = n+1 := by omega
  rw [hsub] at h2
  rw [h1]
  norm_num
  have hn1 : ((n:ℝ)+1) ≠ 0 := by positivity
  have h2r : (Nat.choose (2*n+1) n : ℝ) * ((n:ℝ)+1) = (Nat.choose (2*n) n : ℝ) * ((2:ℝ)*n+1) := by exact_mod_cast h2.symm
  rw [show (2:ℝ) * (2 * ↑n + 1) * ↑((2 * n).choose n) / (↑n + 1) = 2 * (↑((2 * n + 1).choose n) * (↑n + 1)) / (↑n + 1) by rw [h2r]; ring]
  field_simp [hn1]

lemma Aseq_succ (n : ℕ) (hn : 0 < n) :
    Aseq (n+1) = Aseq n * ((2*n+1:ℝ)^2 / (4*n*(n+1))) := by
  unfold Aseq
  rw [central_choose_succ n]
  field_simp [show (16:ℝ) ≠ 0 by norm_num, show ((n:ℝ)+1) ≠ 0 by positivity]
  rw [Nat.cast_add, Nat.cast_one, pow_succ]
  norm_num
  ring

lemma Aseq_step (n : ℕ) (hn : 0 < n) :
    Aseq (n+1) - Aseq n = Aseq n / (4*n*(n+1)) := by
  rw [Aseq_succ n hn]
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnR, show ((n:ℝ)+1) ≠ 0 by positivity]
  ring


lemma T_k_pos (k:ℕ) {b c:ℤ} (hb:0 < (b:ℚ)) (hc:0 < (c:ℚ)) : 0 < T_k k b c := by
  unfold T_k
  have h0mem : 0 ∈ Finset.range (k/2+1) := by simp
  refine Finset.sum_pos' ?hnonneg ?hpos
  · intro i hi
    exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hb.le _) (pow_nonneg hc.le _))
  · refine ⟨0,h0mem,?_⟩
    simp
    exact pow_pos hb k

lemma t_ne_zero (k:ℕ) : t k ≠ 0 := by
  have h1q : 0 < T_k k 14 1 := T_k_pos k (by norm_num) (by norm_num)
  have h2q : 0 < T_k k 17 16 := T_k_pos k (by norm_num) (by norm_num)
  have h1 : 0 < (T_k k 14 1 : ℝ) := by exact_mod_cast h1q
  have h2 : 0 < (T_k k 17 16 : ℝ) := by exact_mod_cast h2q
  have hcbin : 0 < (Nat.choose (2*k) k : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ 2*k)
  unfold t
  positivity

lemma t_support_infinite : ¬ (Function.support t).Finite := by
  have hsup : Function.support t = (Set.univ : Set ℕ) := by
    ext k
    simp [Function.mem_support, t_ne_zero k]
  intro hfin
  have : (Set.univ : Set ℕ).Finite := by simpa [hsup] using hfin
  exact Set.infinite_univ.not_finite this


theorem oeis_a336981_conjecture_2_i :
  (∑' (k : ℕ), t k) = 5390 / Real.pi := by
  sorry
