import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A005187: Sum of $\lfloor n / 2^k \rfloor$ for $k \ge 0$.
This is $\sum_{k=0}^\infty \lfloor n / 2^k \rfloor$.
-/
noncomputable def A005187 (e : ℕ) : ℕ :=
  Finset.sum (Finset.range (e + 1)) fun k ↦ e / (2^k)

/--
A046644: Multiplicative function defined on prime powers $p^e$ as $2^{\text{A005187}(e)}$.
-/
noncomputable def A046644 (n : ℕ) : ℚ :=
  if n = 0 then 0
  else n.factorization.prod fun _ e ↦ (2 : ℚ) ^ (A005187 e)

/--
The sequence $f(n) \in \mathbb{Q}$ such that $f * f = \text{A046644}$.
Defined by well-founded recursion on $\mathbb{N}$ w.r.t. $<$.
-/
noncomputable def A317940_f : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    if n = 0 then 0
    else if n = 1 then 1
    else
      let A_n : ℚ := A046644 n

      let sum_of_products : ℚ := Finset.sum (divisors n) fun d ↦
        if h_prop : d > 1 ∧ d < n then
          -- Proofs that recursive arguments are smaller than n:
          have d_lt_n : d < n := h_prop.2
          let q := n / d
          have q_lt_n : q < n := Nat.div_lt_self (Nat.pos_of_ne_zero (by omega)) h_prop.1

          IH d d_lt_n * IH q q_lt_n
        else 0
      (A_n - sum_of_products) / 2

/--
A317940: Numerators of sequence whose Dirichlet convolution with itself yields A046644.
$a(n) = \text{numerator}(f(n))$, where $f*f = \text{A046644}$.
-/
noncomputable def A317940 (n : ℕ) : ℕ :=
  (A317940_f n).num.natAbs

/--
A317940 No negative terms among the first 2^20 terms. Is the sequence nonnegative?
Conjecture: The sequence of rational numbers $A317940\_f(n)$ is nonnegative for all $n \ge 1$.
-/

-- developed lemmas
lemma shifted_sum_eq_digits (n : ℕ) :
    (∑ i ∈ Finset.range n, n / 2 ^ (i+1)) = n - (Nat.digits 2 n).sum := by
  by_cases hn : n = 0
  · simp [hn]
  · have hleg := Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits (p := 2) n
    simp only [Nat.reduceSub, one_mul] at hleg
    rw [← hleg]
    symm
    apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      have hloglt : Nat.log 2 n < n := Nat.log_lt_self 2 hn
      omega
    · intro x hxlog hxn
      rw [Finset.mem_range] at hxlog hxn
      simp at hxlog hxn
      have hxgt : Nat.log 2 n < x := by omega
      have hlt : n < 2 ^ x := Nat.lt_pow_of_log_lt (by norm_num : 1 < 2) hxgt
      exact Nat.div_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num : 2 > 0) (Nat.le_succ x)))

lemma A005187_eq_two_mul_sub_digits (n : ℕ) : A005187 n = 2*n - (Nat.digits 2 n).sum := by
  rw [A005187, Finset.sum_range_succ']
  rw [shifted_sum_eq_digits]
  simp only [pow_zero, Nat.div_one]
  have hle : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  omega

lemma digits_two_mul_sum (n : ℕ) : (Nat.digits 2 (2*n)).sum = (Nat.digits 2 n).sum := by
  by_cases hn : n = 0
  · simp [hn]
  · have h := Nat.digits_add 2 (by norm_num : 1 < 2) 0 n (by norm_num : 0 < 2) (Or.inr hn)
    simpa using congrArg List.sum h

lemma digits_two_mul_add_one_sum (n : ℕ) : (Nat.digits 2 (2*n+1)).sum = (Nat.digits 2 n).sum + 1 := by
  have h := Nat.digits_add 2 (by norm_num : 1 < 2) 1 n (by norm_num : 1 < 2) (Or.inl (by norm_num : 1 ≠ 0))
  have hs := congrArg List.sum h
  simpa [add_comm, add_left_comm, add_assoc] using hs

lemma A005187_two_mul (n : ℕ) : A005187 (2*n) = 2*n + A005187 n := by
  rw [A005187_eq_two_mul_sub_digits, A005187_eq_two_mul_sub_digits, digits_two_mul_sum]
  have hle : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  omega

lemma A005187_two_mul_add_one (n : ℕ) : A005187 (2*n+1) = (2*n+1) + A005187 n := by
  rw [A005187_eq_two_mul_sub_digits, A005187_eq_two_mul_sub_digits, digits_two_mul_add_one_sum]
  have hle : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  omega

noncomputable def localB (n : ℕ) : ℚ := (2:ℚ) ^ A005187 n

lemma localB_even (n : ℕ) : localB (2*n) = (4:ℚ)^n * localB n := by
  unfold localB
  rw [A005187_two_mul, pow_add]
  have hpow : (2:ℚ) ^ (2*n) = (4:ℚ)^n := by
    change (2:ℚ) ^ (2*n) = ((2:ℚ)^2)^n
    rw [pow_mul]
  rw [hpow]

lemma localB_odd (n : ℕ) : localB (2*n+1) = 2 * (4:ℚ)^n * localB n := by
  unfold localB
  rw [A005187_two_mul_add_one, pow_add]
  have hpow : (2:ℚ) ^ (2*n+1) = 2 * (4:ℚ)^n := by
    rw [show 2*n+1 = 1 + 2*n by omega, pow_add]
    have h2 : (2:ℚ) ^ (2*n) = (4:ℚ)^n := by
      change (2:ℚ) ^ (2*n) = ((2:ℚ)^2)^n
      rw [pow_mul]
    rw [h2]
    norm_num [mul_comm]
  rw [hpow]

noncomputable def Mcoeff : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    if h0 : n = 0 then 0 else
    if hodd : Odd n then (2:ℚ)^n else (2:ℚ)^(n+1) * IH (n/2) (by
      have hn : 1 < n := by
        have heven : Even n := Nat.not_odd_iff_even.mp hodd
        rcases heven with ⟨k, hk⟩
        subst n
        cases k <;> omega
      exact Nat.div_lt_self (by omega) (by norm_num)) - (2:ℚ)^n

noncomputable def Dcoeff (k : ℕ) : ℚ := Mcoeff (k+1)

lemma Mcoeff_ge_one (n : ℕ) (hn : 0 < n) : 1 ≤ Mcoeff n := by
  classical
  refine Nat.strong_induction_on n ?_ hn
  intro n IH hnpos
  rw [Mcoeff, WellFounded.fix_eq]
  split_ifs with h0 hodd
  · omega
  · exact one_le_pow₀ (by norm_num : (1:ℚ) ≤ 2)
  · have hn : 1 < n := by
      have heven : Even n := Nat.not_odd_iff_even.mp hodd
      rcases heven with ⟨k, hk⟩
      subst n
      cases k <;> omega
    have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
    have hpos2 : 0 < n/2 := Nat.div_pos hn (by norm_num)
    have hrec : 1 ≤ Mcoeff (n/2) := IH (n/2) hlt hpos2
    have hpown : 0 < (2:ℚ)^n := pow_pos (by norm_num) _
    have hpowge : 1 ≤ (2:ℚ)^n := one_le_pow₀ (by norm_num : (1:ℚ) ≤ 2)
    calc
      1 ≤ (2:ℚ)^n := hpowge
      _ ≤ (2:ℚ)^(n+1) * Mcoeff (n/2) - (2:ℚ)^n := by
        rw [pow_succ' (2:ℚ) n]
        nlinarith

lemma Mcoeff_nonneg (n : ℕ) : 0 ≤ Mcoeff n := by
  by_cases h : n = 0
  · rw [h, Mcoeff, WellFounded.fix_eq]; simp
  · exact (Mcoeff_ge_one n (Nat.pos_of_ne_zero h)).trans' zero_le_one

lemma Dcoeff_even (j : ℕ) : Dcoeff (2*j) = 2 * (4:ℚ)^j := by
  unfold Dcoeff
  rw [show 2*j+1 = 2*j + 1 by rfl]
  rw [Mcoeff, WellFounded.fix_eq]
  simp [Odd]
  -- hodd branch should be true
  have hpow : (2:ℚ) ^ (2*j+1) = 2 * (4:ℚ)^j := by
    rw [show 2*j+1 = 1 + 2*j by omega, pow_add]
    have h2 : (2:ℚ) ^ (2*j) = (4:ℚ)^j := by
      change (2:ℚ) ^ (2*j) = ((2:ℚ)^2)^j
      rw [pow_mul]
    rw [h2]
    norm_num [mul_comm]
  exact hpow

lemma Dcoeff_odd (j : ℕ) : Dcoeff (2*j+1) = 8 * (4:ℚ)^j * Dcoeff j - 4 * (4:ℚ)^j := by
  unfold Dcoeff
  rw [show 2*j+1+1 = 2*(j+1) by omega]
  rw [Mcoeff, WellFounded.fix_eq]
  have hnot0 : ¬ 2 * (j + 1) = 0 := by omega
  have hnotodd : ¬ Odd (2 * (j+1)) := by
    intro ho
    rcases ho with ⟨m, hm⟩
    omega
  simp [hnot0, hnotodd]
  have hdiv : (2 * (j+1))/2 = j+1 := by simp
  rw [hdiv]
  have hpow1 : (2:ℚ) ^ (2 * (j+1) + 1) = 8 * (4:ℚ)^j := by
    have : 2 * (j+1) + 1 = 3 + 2*j := by omega
    rw [this, pow_add]
    have h2 : (2:ℚ) ^ (2*j) = (4:ℚ)^j := by
      change (2:ℚ) ^ (2*j) = ((2:ℚ)^2)^j
      rw [pow_mul]
    rw [h2]
    norm_num
  have hpow2 : (2:ℚ) ^ (2 * (j+1)) = 4 * (4:ℚ)^j := by
    have : 2 * (j+1) = 2 + 2*j := by omega
    rw [this, pow_add]
    have h2 : (2:ℚ) ^ (2*j) = (4:ℚ)^j := by
      change (2:ℚ) ^ (2*j) = ((2:ℚ)^2)^j
      rw [pow_mul]
    rw [h2]
    norm_num
  rw [hpow1, hpow2]

lemma sum_range_two_mul {α} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∑ k ∈ range (2*n), f k = (∑ j ∈ range n, f (2*j)) + (∑ j ∈ range n, f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, sum_range_succ]
    rw [show 2*n+1 = 2*n + 1 by omega, sum_range_succ]
    rw [sum_range_succ, sum_range_succ, ih]
    abel

lemma sum_range_two_mul_add_one {α} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∑ k ∈ range (2*n+1), f k = (∑ j ∈ range (n+1), f (2*j)) + (∑ j ∈ range n, f (2*j+1)) := by
  rw [show 2*n+1 = 2*n + 1 by omega, sum_range_succ, sum_range_two_mul]
  rw [sum_range_succ]
  abel

lemma localB_logderiv_rec (N : ℕ) :
    (N:ℚ) * localB N = ∑ k ∈ range N, Dcoeff k * localB (N - 1 - k) := by
  classical
  refine Nat.strong_induction_on N ?_
  intro N IH
  by_cases hN0 : N = 0
  · simp [hN0]
  by_cases hOdd : Odd N
  · rcases hOdd with ⟨n, rfl⟩
    rw [sum_range_two_mul_add_one]
    have hEvenSum :
        (∑ j ∈ range (n + 1), Dcoeff (2 * j) * localB (2 * n + 1 - 1 - 2 * j)) =
          2 * (4:ℚ)^n * (∑ j ∈ range (n+1), localB (n - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < n + 1 := by simpa using hj
      have hjle : j ≤ n := by omega
      have hidx : 2 * n + 1 - 1 - 2 * j = 2 * (n - j) := by omega
      rw [Dcoeff_even, hidx, localB_even]
      calc
        2 * (4:ℚ)^j * ((4:ℚ)^(n-j) * localB (n-j))
            = 2 * ((4:ℚ)^j * (4:ℚ)^(n-j)) * localB (n-j) := by ring
        _ = 2 * (4:ℚ)^n * localB (n-j) := by rw [pow_mul_pow_sub (4:ℚ) hjle]
    have hOddSum :
        (∑ j ∈ range n, Dcoeff (2 * j + 1) * localB (2 * n + 1 - 1 - (2 * j + 1))) =
          4^(n+1) * (∑ j ∈ range n, Dcoeff j * localB (n - 1 - j))
          - 2 * (4:ℚ)^n * (∑ j ∈ range n, localB (n - 1 - j)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < n := by simpa using hj
      have hjle : j ≤ n-1 := by omega
      have hidx : 2 * n + 1 - 1 - (2 * j + 1) = 2 * (n - 1 - j) + 1 := by omega
      rw [Dcoeff_odd, hidx, localB_odd]
      have hp : (4:ℚ)^j * (4:ℚ)^(n - 1 - j) = (4:ℚ)^(n-1) := by
        simpa using pow_mul_pow_sub (4:ℚ) hjle
      calc
        (8 * (4:ℚ)^j * Dcoeff j - 4 * (4:ℚ)^j) * (2 * (4:ℚ)^(n - 1 - j) * localB (n - 1 - j))
            = (16 * ((4:ℚ)^j * (4:ℚ)^(n-1-j)) * Dcoeff j - 8 * ((4:ℚ)^j * (4:ℚ)^(n-1-j))) * localB (n-1-j) := by ring
        _ = (16 * (4:ℚ)^(n-1) * Dcoeff j - 8 * (4:ℚ)^(n-1)) * localB (n-1-j) := by rw [hp]
        _ = (4:ℚ)^(n+1) * (Dcoeff j * localB (n - 1 - j)) - 2 * (4:ℚ)^n * localB (n - 1 - j) := by
          have hnpos : 0 < n := by omega
          have hp1 : (4:ℚ)^(n+1) = 16 * (4:ℚ)^(n-1) := by
            calc
              (4:ℚ)^(n+1) = (4:ℚ)^((n-1)+2) := by congr 1; omega
              _ = (4:ℚ)^(n-1) * (4:ℚ)^2 := by rw [pow_add]
              _ = 16 * (4:ℚ)^(n-1) := by ring
          have hp2 : (4:ℚ)^n = 4 * (4:ℚ)^(n-1) := by
            calc
              (4:ℚ)^n = (4:ℚ)^((n-1)+1) := by congr 1; omega
              _ = (4:ℚ)^(n-1) * (4:ℚ)^1 := by rw [pow_add]
              _ = 4 * (4:ℚ)^(n-1) := by ring
          rw [hp1, hp2]
          ring_nf
    rw [hEvenSum, hOddSum]
    rw [Finset.sum_range_succ']
    have hIHn := IH n (by omega)
    rw [← hIHn]
    rw [localB_odd]
    simp
    have hsumEq : (∑ x ∈ range n, localB (n - (x + 1))) = (∑ x ∈ range n, localB (n - 1 - x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      omega
    rw [hsumEq]
    ring
  · have hEven : Even N := Nat.not_odd_iff_even.mp hOdd
    rcases hEven with ⟨n, rfl⟩
    cases n with
    | zero => omega
    | succ n =>
      rw [show n + 1 + (n + 1) = 2*(n+1) by omega]
      rw [sum_range_two_mul]
      have hEvenSum :
          (∑ j ∈ range (n+1), Dcoeff (2*j) * localB (2*(n+1) - 1 - 2*j)) =
            (4:ℚ)^(n+1) * (∑ j ∈ range (n+1), localB (n - j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < n+1 := by simpa using hj
        have hjle : j ≤ n := by omega
        have hidx : 2*(n+1) - 1 - 2*j = 2*(n-j)+1 := by omega
        rw [Dcoeff_even, hidx, localB_odd]
        calc
          2 * (4:ℚ)^j * (2 * (4:ℚ)^(n-j) * localB (n-j))
              = 4 * ((4:ℚ)^j * (4:ℚ)^(n-j)) * localB (n-j) := by ring
          _ = (4:ℚ)^(n+1) * localB (n-j) := by
            rw [pow_mul_pow_sub (4:ℚ) hjle]
            rw [pow_succ' (4:ℚ) n]
      have hOddSum :
          (∑ j ∈ range (n+1), Dcoeff (2*j+1) * localB (2*(n+1) - 1 - (2*j+1))) =
            2 * (4:ℚ)^(n+1) * (∑ j ∈ range (n+1), Dcoeff j * localB (n-j))
            - (4:ℚ)^(n+1) * (∑ j ∈ range (n+1), localB (n-j)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < n+1 := by simpa using hj
        have hjle : j ≤ n := by omega
        have hidx : 2*(n+1) - 1 - (2*j+1) = 2*(n-j) := by omega
        rw [Dcoeff_odd, hidx, localB_even]
        have hp : (4:ℚ)^j * (4:ℚ)^(n-j) = (4:ℚ)^n := by
          simpa using pow_mul_pow_sub (4:ℚ) hjle
        calc
          (8 * (4:ℚ)^j * Dcoeff j - 4 * (4:ℚ)^j) * ((4:ℚ)^(n-j) * localB (n-j))
              = (8 * ((4:ℚ)^j * (4:ℚ)^(n-j)) * Dcoeff j - 4 * ((4:ℚ)^j * (4:ℚ)^(n-j))) * localB (n-j) := by ring
          _ = (8 * (4:ℚ)^n * Dcoeff j - 4 * (4:ℚ)^n) * localB (n-j) := by rw [hp]
          _ = 2 * (4:ℚ)^(n+1) * (Dcoeff j * localB (n-j)) - (4:ℚ)^(n+1) * localB (n-j) := by
            rw [pow_succ' (4:ℚ) n]
            ring
      rw [hEvenSum, hOddSum]
      have hIH := IH (n+1) (by omega)
      have hsumD : (∑ k ∈ range (n+1), Dcoeff k * localB (n + 1 - 1 - k)) =
          (∑ k ∈ range (n+1), Dcoeff k * localB (n - k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show n + 1 - 1 - k = n - k by omega]
      have hIH' : ((n+1:ℕ):ℚ) * localB (n+1) = (∑ k ∈ range (n+1), Dcoeff k * localB (n-k)) := by
        rw [hIH, hsumD]
      rw [← hIH']
      rw [localB_even]
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring

noncomputable def Cpos : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    if h0 : n = 0 then 1 else
      (∑ k ∈ Finset.range n, Dcoeff k * IH (n-1-k) (by
        exact lt_of_le_of_lt (Nat.sub_le (n - 1) k) (Nat.pred_lt h0))) / (2 * (n:ℚ))

lemma Cpos_zero : Cpos 0 = 1 := by
  rw [Cpos, WellFounded.fix_eq]
  simp

lemma Cpos_succ (n : ℕ) :
    Cpos (n+1) = (∑ k ∈ range (n+1), Dcoeff k * Cpos (n-k)) / (2 * ((n+1:ℕ):ℚ)) := by
  rw [Cpos, WellFounded.fix_eq]
  simp

lemma Cpos_nonneg (n : ℕ) : 0 ≤ Cpos n := by
  classical
  refine Nat.strong_induction_on n ?_
  intro n IH
  rw [Cpos, WellFounded.fix_eq]
  split_ifs with h0
  · norm_num
  · apply div_nonneg
    · apply Finset.sum_nonneg
      intro k hk
      have hklt : k < n := by simpa using hk
      apply mul_nonneg
      · exact Mcoeff_nonneg (k+1)
      · exact IH (n - 1 - k) (lt_of_le_of_lt (Nat.sub_le (n - 1) k) (Nat.pred_lt h0))
    · positivity

open PowerSeries
noncomputable def Bseries : ℚ⟦X⟧ := PowerSeries.mk localB
noncomputable def Cseries : ℚ⟦X⟧ := PowerSeries.mk Cpos
noncomputable def Dseries : ℚ⟦X⟧ := PowerSeries.mk Dcoeff

lemma coeff_mul_mk_sum (a b : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b : ℚ⟦X⟧) =
      ∑ k ∈ range (n+1), a k * b (n-k) := by
  rw [PowerSeries.coeff_mul]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [PowerSeries.coeff_mk]

lemma Cseries_ode : Dseries * Cseries = (2:ℚ) • (d⁄dX ℚ Cseries) := by
  ext n
  unfold Dseries Cseries
  rw [coeff_mul_mk_sum]
  rw [PowerSeries.coeff_smul, PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
  rw [Cpos_succ n]
  rw [smul_eq_mul]
  field_simp [show ((n+1:ℕ):ℚ) ≠ 0 by positivity]
  norm_num [Nat.cast_add]

lemma Bseries_ode : Dseries * Bseries = d⁄dX ℚ Bseries := by
  ext n
  unfold Dseries Bseries
  rw [coeff_mul_mk_sum]
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
  simpa [Dcoeff, mul_comm] using (localB_logderiv_rec (n+1)).symm


lemma Hseries_ode : Dseries * (Cseries*Cseries - Bseries) = d⁄dX ℚ (Cseries*Cseries - Bseries) := by
  calc
    Dseries * (Cseries*Cseries - Bseries)
        = (Dseries*Cseries)*Cseries - Dseries*Bseries := by ring
    _ = ((2:ℚ) • (d⁄dX ℚ Cseries))*Cseries - d⁄dX ℚ Bseries := by rw [Cseries_ode, Bseries_ode]
    _ = d⁄dX ℚ (Cseries*Cseries - Bseries) := by
      rw [map_sub]
      have hprod : d⁄dX ℚ (Cseries*Cseries) = Cseries * (d⁄dX ℚ Cseries) + Cseries * (d⁄dX ℚ Cseries) := by
        simpa [Algebra.smul_def, mul_comm] using (PowerSeries.derivativeFun_mul (R := ℚ) Cseries Cseries)
      rw [hprod]
      rw [two_smul]
      ring

lemma ode_zero_of_constant_zero {H D : ℚ⟦X⟧} (hode : D * H = d⁄dX ℚ H)
    (h0 : PowerSeries.coeff 0 H = 0) : H = 0 := by
  apply PowerSeries.ext
  intro n
  refine Nat.strong_induction_on n ?_ 
  intro n IH
  cases n with
  | zero => simpa using h0
  | succ n =>
    have hcoeff := congrArg (PowerSeries.coeff n) hode
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_derivative] at hcoeff
    have hsumzero : (∑ x ∈ Finset.antidiagonal n, PowerSeries.coeff x.1 D * PowerSeries.coeff x.2 H) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxsum : x.1 + x.2 = n := (Finset.mem_antidiagonal.mp hx)
      have hx2lt : x.2 < n+1 := by omega
      have hx2zero : PowerSeries.coeff x.2 H = 0 := IH x.2 hx2lt
      simp [hx2zero]
    rw [hsumzero] at hcoeff
    have hnz : ((n:ℚ) + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hcoeff.symm).resolve_right hnz

lemma Cseries_sq_eq_Bseries : Cseries*Cseries = Bseries := by
  have hH0 : PowerSeries.coeff 0 (Cseries*Cseries - Bseries) = 0 := by
    unfold Cseries Bseries
    rw [map_sub, PowerSeries.coeff_mul]
    simp [PowerSeries.coeff_mk, Cpos_zero, localB, A005187]
  have hz := ode_zero_of_constant_zero Hseries_ode hH0
  exact sub_eq_zero.mp hz

lemma localC_square_coeff (n : ℕ) :
    (∑ k ∈ range (n+1), Cpos k * Cpos (n-k)) = localB n := by
  have h := congrArg (PowerSeries.coeff n) Cseries_sq_eq_Bseries
  unfold Cseries Bseries at h
  rw [coeff_mul_mk_sum, PowerSeries.coeff_mk] at h
  exact h

noncomputable def Gfun (n : ℕ) : ℚ := if n = 0 then 0 else n.factorization.prod fun _ e => Cpos e
noncomputable def Garith : ArithmeticFunction ℚ where
  toFun := Gfun
  map_zero' := by simp [Gfun]

lemma Gfun_one : Gfun 1 = 1 := by simp [Gfun]

lemma Gfun_prime_pow {p e : ℕ} (hp : Nat.Prime p) : Gfun (p^e) = Cpos e := by
  by_cases he : e = 0
  · simp [he, Gfun, Cpos_zero]
  · have hp0 : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
    rw [Gfun, if_neg hp0, hp.factorization_pow]
    simp [Finsupp.prod_single_index, Cpos_zero]

lemma Garith_multiplicative : Garith.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · exact Gfun_one
  · intro m n hm0 hn0 hcop
    simp only [Garith]
    simp [Gfun, hm0, hn0, mul_ne_zero hm0 hn0]
    exact Finsupp.prod_add_index_of_disjoint (hcop.disjoint_primeFactors) (fun _ e => Cpos e)

noncomputable def Bfun (n : ℕ) : ℚ := if n = 0 then 0 else n.factorization.prod fun _ e => localB e
noncomputable def Barith : ArithmeticFunction ℚ where
  toFun := Bfun
  map_zero' := by simp [Bfun]

lemma Bfun_one : Bfun 1 = 1 := by simp [Bfun, localB, A005187]
lemma Bfun_prime_pow {p e : ℕ} (hp : Nat.Prime p) : Bfun (p^e) = localB e := by
  by_cases he : e = 0
  · simp [he, Bfun, localB, A005187]
  · have hp0 : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
    rw [Bfun, if_neg hp0, hp.factorization_pow]
    simp [Finsupp.prod_single_index, localB, A005187]

lemma Barith_multiplicative : Barith.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · exact Bfun_one
  · intro m n hm0 hn0 hcop
    simp only [Barith]
    simp [Bfun, hm0, hn0, mul_ne_zero hm0 hn0]
    exact Finsupp.prod_add_index_of_disjoint (hcop.disjoint_primeFactors) (fun _ e => localB e)

lemma Garith_mul_prime_pow {p e : ℕ} (hp : Nat.Prime p) : (Garith*Garith) (p^e) = localB e := by
  rw [ArithmeticFunction.mul_apply]
  rw [← Nat.map_div_right_divisors (n := p^e), Finset.sum_map]
  rw [Nat.divisors_prime_pow hp e, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hs : (∑ x ∈ range (e + 1),
      Garith (p ^ x) * Garith (p ^ e / p ^ x)) =
      (∑ x ∈ range (e + 1), Cpos x * Cpos (e-x)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxle : x ≤ e := by simpa using hx
    rw [Nat.pow_div hxle hp.pos]
    simp [Garith, Gfun_prime_pow hp]
  rw [hs, localC_square_coeff]


lemma Garith_sq_eq_Barith : Garith * Garith = Barith := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers (Garith*Garith) (Garith_multiplicative.mul Garith_multiplicative) Barith Barith_multiplicative).mpr
  intro p e hp
  rw [Garith_mul_prime_pow hp]
  change localB e = Bfun (p^e)
  rw [Bfun_prime_pow hp]


lemma divisors_sum_endpoints_proper {n : ℕ} (hn : 1 < n) (F : ℕ → ℚ) :
    (∑ d ∈ divisors n, F d) = F 1 + F n + ∑ d ∈ divisors n, (if d > 1 ∧ d < n then F d else 0) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have h1mem : 1 ∈ divisors n := by simp [hn0]
  have hnmem : n ∈ divisors n := by simp [hn0]
  calc
    (∑ d ∈ divisors n, F d)
        = ∑ d ∈ divisors n, ((if d = 1 then F d else 0) + (if d = n then F d else 0) + (if d > 1 ∧ d < n then F d else 0)) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
          have hdle : d ≤ n := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hd).1
          by_cases h1 : d = 1
          · simp [h1, show ¬(1:ℕ) = n by omega]
          · by_cases hn' : d = n
            · simp [hn', hn.ne']
            · have hp : d > 1 ∧ d < n := by omega
              simp [h1, hn', hp]
    _ = (∑ d ∈ divisors n, if d = 1 then F d else 0) + (∑ d ∈ divisors n, if d = n then F d else 0) +
          ∑ d ∈ divisors n, (if d > 1 ∧ d < n then F d else 0) := by
          simp [Finset.sum_add_distrib, add_assoc]
    _ = F 1 + F n + ∑ d ∈ divisors n, (if d > 1 ∧ d < n then F d else 0) := by
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp [h1mem, hnmem]
lemma Barith_apply_eq_A046644 (n : ℕ) : Barith n = A046644 n := by
  simp [Barith, Bfun, A046644, localB]

lemma Garith_conv_divisors (n : ℕ) :
    (Garith*Garith) n = ∑ d ∈ divisors n, Gfun d * Gfun (n/d) := by
  rw [ArithmeticFunction.mul_apply]
  rw [← Nat.map_div_right_divisors (n := n), Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rfl

lemma Gfun_rec (n : ℕ) (hn : 1 < n) :
    Gfun n = (A046644 n - ∑ d ∈ divisors n, (if d > 1 ∧ d < n then Gfun d * Gfun (n/d) else 0)) / 2 := by
  have hsq := congrArg (fun f : ArithmeticFunction ℚ => f n) Garith_sq_eq_Barith
  change (Garith*Garith) n = Barith n at hsq
  rw [Garith_conv_divisors, Barith_apply_eq_A046644] at hsq
  have hsplit := divisors_sum_endpoints_proper hn (fun d => Gfun d * Gfun (n/d))
  rw [hsplit] at hsq
  have hn0 : n ≠ 0 := by omega
  have hG1 : Gfun 1 = 1 := Gfun_one
  have hGn1 : Gfun (n / n) = 1 := by rw [Nat.div_self (by omega : 0 < n)]; exact Gfun_one
  have hndiv1 : n / 1 = n := by simp
  rw [hG1, hndiv1, hGn1] at hsq
  ring_nf at hsq ⊢
  linarith

lemma A317940_f_eq_Gfun (n : ℕ) : A317940_f n = Gfun n := by
  classical
  refine Nat.strong_induction_on n ?_
  intro n IH
  rw [A317940_f, WellFounded.fix_eq]
  split_ifs with h0 h1
  · simp [Gfun, h0]
  · simp [Gfun, h1]
  · have hn : 1 < n := by omega
    rw [Gfun_rec n hn]
    dsimp
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hp : d > 1 ∧ d < n
    · simp [hp]
      change A317940_f d * A317940_f (n / d) = Gfun d * Gfun (n / d)
      rw [IH d hp.2]
      have hq_lt : n / d < n := Nat.div_lt_self (Nat.pos_of_ne_zero (by omega)) hp.1
      rw [IH (n/d) hq_lt]
    · simp [hp]


theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) : A317940_f n ≥ 0 := by
  rw [A317940_f_eq_Gfun]
  unfold Gfun
  split_ifs with h0
  · omega
  · unfold Finsupp.prod
    apply Finset.prod_nonneg
    intro p hp
    exact Cpos_nonneg (n.factorization p)
