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

namespace Dev
/-- a(0)=1, a(2m)=4^m a(m), a(2m+1)=2·4^m a(m). -/
noncomputable def a : ℕ → ℚ
  | 0 => 1
  | (e+1) =>
      if (e+1) % 2 = 0 then (4:ℚ)^((e+1)/2) * a ((e+1)/2)
      else 2 * (4:ℚ)^((e+1)/2) * a ((e+1)/2)
  decreasing_by
    · exact Nat.div_lt_self (Nat.succ_pos e) (by norm_num)
    · exact Nat.div_lt_self (Nat.succ_pos e) (by norm_num)

/-- μ(0)=0, μ(odd e)=2^e, μ(even e≥2)=4^{e/2}(2 μ(e/2) - 1). -/
noncomputable def mu : ℕ → ℚ
  | 0 => 0
  | (e+1) =>
      if (e+1) % 2 = 1 then (2:ℚ)^(e+1)
      else (4:ℚ)^((e+1)/2) * (2 * mu ((e+1)/2) - 1)
  decreasing_by
    exact Nat.div_lt_self (Nat.succ_pos e) (by norm_num)

lemma a_zero : a 0 = 1 := by rw [a]

lemma a_succ (e : ℕ) : a (e+1) =
    if (e+1) % 2 = 0 then (4:ℚ)^((e+1)/2) * a ((e+1)/2)
    else 2 * (4:ℚ)^((e+1)/2) * a ((e+1)/2) := by rw [a]

lemma mu_succ (e : ℕ) : mu (e+1) =
    if (e+1) % 2 = 1 then (2:ℚ)^(e+1)
    else (4:ℚ)^((e+1)/2) * (2 * mu ((e+1)/2) - 1) := by rw [mu]

lemma a_even (m : ℕ) : a (2 * m) = (4:ℚ)^m * a m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [a_zero]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k+1 := ⟨m-1, by omega⟩
    have : 2 * (k+1) = (2*k+1) + 1 := by ring
    rw [this, a_succ, if_pos (by omega : ((2*k+1)+1) % 2 = 0)]
    have h2 : ((2*k+1)+1) / 2 = k+1 := by omega
    rw [h2]

lemma a_odd (m : ℕ) : a (2 * m + 1) = 2 * (4:ℚ)^m * a m := by
  rw [a_succ, if_neg (by omega : ¬ (2*m+1) % 2 = 0)]
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [h2]

lemma mu_zero : mu 0 = 0 := by rw [mu]

lemma mu_odd (m : ℕ) : mu (2 * m + 1) = (2:ℚ)^(2*m+1) := by
  rw [mu_succ, if_pos (by omega : (2*m+1) % 2 = 1)]

lemma mu_even (m : ℕ) (hm : 1 ≤ m) : mu (2 * m) = (4:ℚ)^m * (2 * mu m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k+1 := ⟨m-1, by omega⟩
  have : 2 * (k+1) = (2*k+1) + 1 := by ring
  rw [this, mu_succ, if_neg (by omega : ¬ ((2*k+1)+1) % 2 = 1)]
  have h2 : ((2*k+1)+1) / 2 = k+1 := by omega
  rw [h2]

/-- mu is nonnegative, and at least 1 for e ≥ 1. -/
lemma mu_ge_one : ∀ e : ℕ, 1 ≤ e → (1:ℚ) ≤ mu e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e IH =>
    intro he
    rcases Nat.even_or_odd e with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · -- e = m + m = 2*m
      have hm : 1 ≤ m := by omega
      have : m + m = 2 * m := by ring
      rw [this, mu_even m hm]
      have hmu : (1:ℚ) ≤ mu m := IH m (by omega) hm
      have h4 : (1:ℚ) ≤ (4:ℚ)^m := one_le_pow₀ (by norm_num)
      nlinarith [h4, hmu]
    · -- e = 2*m+1
      rw [mu_odd m]
      exact one_le_pow₀ (by norm_num)

lemma mu_nonneg (e : ℕ) : 0 ≤ mu e := by
  rcases Nat.eq_zero_or_pos e with h | h
  · subst h; rw [mu_zero]
  · exact le_trans (by norm_num) (mu_ge_one e h)

/-- Splitting a `range` sum by parity (even-ending case). -/
lemma split_even (f : ℕ → ℚ) (N : ℕ) :
    ∑ j ∈ range (2*N+1), f j
      = (∑ i ∈ range (N+1), f (2*i)) + (∑ i ∈ range N, f (2*i+1)) := by
  induction N with
  | zero => simp
  | succ N IH =>
    have e1 : 2*(N+1)+1 = (2*N+1) + 1 + 1 := by ring
    rw [e1, Finset.sum_range_succ, Finset.sum_range_succ, IH]
    rw [Finset.sum_range_succ (fun i => f (2*i)) (N+1)]
    rw [Finset.sum_range_succ (fun i => f (2*i+1)) N]
    have c1 : f (2*(N+1)) = f (2*N+2) := by congr 1
    have c2 : f (2*N+1+1) = f (2*N+2) := by congr 1
    rw [c1, c2]
    ring

/-- Splitting a `range` sum by parity (odd-ending case). -/
lemma split_odd (f : ℕ → ℚ) (N : ℕ) :
    ∑ j ∈ range (2*N+2), f j
      = (∑ i ∈ range (N+1), f (2*i)) + (∑ i ∈ range (N+1), f (2*i+1)) := by
  rw [show 2*N+2 = (2*N+1)+1 from rfl, Finset.sum_range_succ, split_even f N]
  rw [Finset.sum_range_succ (fun i => f (2*i+1)) N]
  have : 2*N+1 = 2*N+1 := rfl
  ring

/-- The convolution `(mu * a)` at `e`. -/
noncomputable def T (e : ℕ) : ℚ := ∑ j ∈ range (e+1), mu j * a (e - j)

/-- Key termwise identity for the even doubling. -/
lemma term_even (N i : ℕ) (hi : i < N) :
    mu (2*(i+1)) * a (2*N - 2*(i+1)) + mu (2*i+1) * a (2*N - (2*i+1))
      = 2 * 4^N * (mu (i+1) * a (N - (i+1))) := by
  set k := N - (i+1) with hk
  have hik : i + 1 + k = N := by omega
  -- rewrite the `a` arguments
  have ha1 : 2*N - 2*(i+1) = 2 * k := by omega
  have ha2 : 2*N - (2*i+1) = 2 * k + 1 := by omega
  rw [ha1, ha2, a_even k, a_odd k, mu_even (i+1) (by omega), mu_odd i]
  -- power facts
  have hpa : (4:ℚ)^(i+1) * 4^k = 4^N := by rw [← pow_add, hik]
  have hpb : (2:ℚ)^(2*i+1) * 2 = 4^(i+1) := by
    rw [← pow_succ, show 2*i+1+1 = 2*(i+1) from by ring, pow_mul]; norm_num
  linear_combination (4^k * a k) * hpb + (2 * mu (i+1) * a k) * hpa

/-- Key termwise identity for the odd doubling. -/
lemma term_odd (N i : ℕ) (hi : i < N) :
    mu (2*(i+1)) * a (2*N+1 - 2*(i+1)) + mu (2*(i+1)+1) * a (2*N+1 - (2*(i+1)+1))
      = 4 * 4^N * (mu (i+1) * a (N - (i+1))) := by
  set k := N - (i+1) with hk
  have hik : i + 1 + k = N := by omega
  have ha1 : 2*N+1 - 2*(i+1) = 2 * k + 1 := by omega
  have ha2 : 2*N+1 - (2*(i+1)+1) = 2 * k := by omega
  rw [ha1, ha2, a_even k, a_odd k, mu_even (i+1) (by omega), mu_odd (i+1)]
  have hpa : (4:ℚ)^(i+1) * 4^k = 4^N := by rw [← pow_add, hik]
  have hpc : (2:ℚ)^(2*(i+1)+1) = 2 * 4^(i+1) := by
    rw [pow_succ, pow_mul]; norm_num; ring
  linear_combination (4^k * a k) * hpc + (4 * a k * mu (i+1)) * hpa

lemma T_peel (N : ℕ) : T N = ∑ i ∈ range N, mu (i+1) * a (N - (i+1)) := by
  unfold T
  rw [Finset.sum_range_succ' (fun j => mu j * a (N - j)) N]
  simp [mu_zero]

lemma T_even (N : ℕ) : T (2*N) = 2 * 4^N * T N := by
  rw [T_peel N]
  show (∑ j ∈ range (2*N+1), mu j * a (2*N - j)) = _
  rw [split_even (fun j => mu j * a (2*N - j)) N]
  rw [Finset.sum_range_succ' (fun i => mu (2*i) * a (2*N - 2*i)) N]
  simp only [Nat.mul_zero, mu_zero, zero_mul, add_zero]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact term_even N i (Finset.mem_range.mp hi)

lemma T_odd (N : ℕ) : T (2*N+1) = 2 * 4^N * a N + 4^(N+1) * T N := by
  rw [T_peel N]
  show (∑ j ∈ range (2*N+1+1), mu j * a (2*N+1 - j)) = _
  rw [show 2*N+1+1 = 2*N+2 from rfl, split_odd (fun j => mu j * a (2*N+1 - j)) N]
  rw [Finset.sum_range_succ' (fun i => mu (2*i) * a (2*N+1 - 2*i)) N]
  rw [Finset.sum_range_succ' (fun i => mu (2*i+1) * a (2*N+1 - (2*i+1))) N]
  have hE0 : mu (2*0) * a (2*N+1 - 2*0) = 0 := by norm_num [mu_zero]
  have hO0 : mu (2*0+1) * a (2*N+1 - (2*0+1)) = 2 * 4^N * a N := by
    rw [show 2*N+1 - (2*0+1) = 2*N from by omega, a_even N, mu_odd 0]
    norm_num; ring
  rw [hE0, hO0, add_zero]
  rw [Finset.mul_sum]
  -- LHS: (∑ EVEN') + (∑ ODD' + 2*4^N*a N) ; RHS: 2*4^N*a N + ∑ 4^(N+1)*(...)
  rw [show (∑ i ∈ range N, mu (2*(i+1)) * a (2*N+1 - 2*(i+1)))
        + ((∑ i ∈ range N, mu (2*(i+1)+1) * a (2*N+1 - (2*(i+1)+1))) + 2 * 4^N * a N)
      = (∑ i ∈ range N, (mu (2*(i+1)) * a (2*N+1 - 2*(i+1))
          + mu (2*(i+1)+1) * a (2*N+1 - (2*(i+1)+1)))) + 2 * 4^N * a N from by
        rw [Finset.sum_add_distrib]; ring]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [term_odd N i (Finset.mem_range.mp hi)]
  rw [show (N+1) = N+1 from rfl, pow_succ]
  ring

/-- The logarithmic-derivative identity: `e · a(e) = (mu * a)(e)`. -/
lemma star : ∀ e : ℕ, (e:ℚ) * a e = T e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e IH =>
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp [T, mu_zero, a_zero]
    · rcases Nat.even_or_odd e with ⟨N, hN⟩ | ⟨N, hN⟩
      · have hN2 : e = 2 * N := by omega
        subst hN2
        rw [T_even N, ← IH N (by omega), a_even N]
        push_cast; ring
      · subst hN
        rw [T_odd N, ← IH N (by omega), a_odd N, pow_succ]
        push_cast; ring

/-- `c` is the "exp-recursion" sequence: `2 e · c(e) = (mu * c)(e)`, with `c 0 = 1`. -/
noncomputable def c (n : ℕ) : ℚ :=
  Nat.strongRecOn' n (fun n IH =>
    if n = 0 then 1
    else (1/(2*(n:ℚ))) *
      ∑ j ∈ (Finset.range n).attach, mu (n - j.1) * IH j.1 (Finset.mem_range.mp j.2))

lemma c_eq (n : ℕ) : c n =
    if n = 0 then 1
    else (1/(2*(n:ℚ))) * ∑ j ∈ (Finset.range n).attach, mu (n - j.1) * c j.1 := by
  rw [c, Nat.strongRecOn'_beta]
  rfl

lemma c_zero : c 0 = 1 := by rw [c_eq]; simp

lemma c_succ (n : ℕ) (hn : 1 ≤ n) :
    c n = (1/(2*(n:ℚ))) * ∑ j ∈ Finset.range n, mu (n - j) * c j := by
  rw [c_eq, if_neg (by omega)]
  congr 1
  rw [← Finset.sum_attach (Finset.range n) (fun j => mu (n - j) * c j)]

lemma c_nonneg : ∀ n, 0 ≤ c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [c_zero]; norm_num
    · rw [c_succ n h]
      apply mul_nonneg
      · positivity
      · apply Finset.sum_nonneg
        intro j hj
        exact mul_nonneg (mu_nonneg _) (IH j (Finset.mem_range.mp hj))

/-- The exp-recursion identity: `(mu * c)(n) = 2 n · c(n)`. -/
lemma MC_eq (n : ℕ) : ∑ j ∈ range (n+1), mu j * c (n-j) = 2 * (n:ℚ) * c n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [mu_zero]
  · have hrefl : ∑ j ∈ range (n+1), mu j * c (n-j)
        = ∑ i ∈ range (n+1), mu (n-i) * c i := by
      rw [← Finset.sum_range_reflect (fun i => mu (n-i) * c i) (n+1)]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ n := by have := Finset.mem_range.mp hj; omega
      rw [show (n+1)-1-j = n-j from by omega, show n-(n-j) = j from by omega]
    rw [hrefl, Finset.sum_range_succ,
      show mu (n-n) * c n = 0 from by rw [Nat.sub_self, mu_zero]; ring, add_zero,
      c_succ n h]
    have hn0 : (n:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp

open PowerSeries

noncomputable def Aps : ℚ⟦X⟧ := PowerSeries.mk a
noncomputable def Mps : ℚ⟦X⟧ := PowerSeries.mk mu
noncomputable def Cps : ℚ⟦X⟧ := PowerSeries.mk c

lemma coeff_mul_rangeP (p q : ℚ⟦X⟧) (e : ℕ) :
    PowerSeries.coeff e (p * q)
      = ∑ j ∈ range (e+1), PowerSeries.coeff j p * PowerSeries.coeff (e-j) q := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- `e · a(e) = (mu * a)(e)` in power-series form. -/
lemma key_a (e : ℕ) : (e:ℚ) * PowerSeries.coeff e Aps = PowerSeries.coeff e (Mps * Aps) := by
  rw [coeff_mul_rangeP]
  simp only [Aps, Mps, PowerSeries.coeff_mk]
  exact star e

/-- `(mu * c)(e) = 2 e · c(e)` in power-series form. -/
lemma key_c (e : ℕ) : PowerSeries.coeff e (Mps * Cps) = 2 * (e:ℚ) * PowerSeries.coeff e Cps := by
  rw [coeff_mul_rangeP]
  simp only [Mps, Cps, PowerSeries.coeff_mk]
  exact MC_eq e

/-- Symmetry of the convolution against the "index" weight. -/
lemma conv_symm (e : ℕ) :
    ∑ j ∈ range (e+1), (e:ℚ) * (c j * c (e-j))
      = 2 * ∑ j ∈ range (e+1), (j:ℚ) * (c j * c (e-j)) := by
  have hsplit : ∑ j ∈ range (e+1), (e:ℚ) * (c j * c (e-j))
      = (∑ j ∈ range (e+1), (j:ℚ) * (c j * c (e-j)))
        + ∑ j ∈ range (e+1), ((e-j:ℕ):ℚ) * (c j * c (e-j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ e := by have := Finset.mem_range.mp hj; omega
    rw [Nat.cast_sub hj']
    ring
  have hrev : ∑ j ∈ range (e+1), ((e-j:ℕ):ℚ) * (c j * c (e-j))
      = ∑ j ∈ range (e+1), (j:ℚ) * (c j * c (e-j)) := by
    rw [← Finset.sum_range_reflect (fun j => (j:ℚ) * (c j * c (e-j))) (e+1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ e := by have := Finset.mem_range.mp hj; omega
    rw [show (e+1)-1-j = e-j from by omega, show e-(e-j) = j from by omega]
    ring
  rw [hsplit, hrev]; ring

/-- `e · (c*c)(e) = (mu * (c*c))(e)`. -/
lemma key_q (e : ℕ) :
    (e:ℚ) * PowerSeries.coeff e (Cps^2) = PowerSeries.coeff e (Mps * Cps^2) := by
  have hcc : Cps^2 = Cps * Cps := sq Cps
  have hL : (e:ℚ) * PowerSeries.coeff e (Cps^2)
      = ∑ j ∈ range (e+1), (e:ℚ) * (c j * c (e-j)) := by
    rw [hcc, coeff_mul_rangeP, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Cps, PowerSeries.coeff_mk]
  have hM : (e:ℚ) * PowerSeries.coeff e (Cps^2)
      = ∑ j ∈ range (e+1), PowerSeries.coeff j (Mps * Cps) * c (e-j) := by
    rw [hL, conv_symm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [key_c j]
    simp only [Cps, PowerSeries.coeff_mk]
    ring
  rw [hM, show Mps * Cps^2 = (Mps * Cps) * Cps from by rw [hcc]; ring, coeff_mul_rangeP]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Cps, PowerSeries.coeff_mk]

lemma uniq : Cps^2 = Aps := by
  ext e
  induction e using Nat.strong_induction_on with
  | _ e IH =>
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      rw [sq, coeff_mul_rangeP]
      simp [Cps, Aps, PowerSeries.coeff_mk, c_zero, a_zero]
    · have hsum : PowerSeries.coeff e (Mps * Cps^2) = PowerSeries.coeff e (Mps * Aps) := by
        rw [coeff_mul_rangeP, coeff_mul_rangeP]
        apply Finset.sum_congr rfl
        intro j hj
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0; simp [Mps, PowerSeries.coeff_mk, mu_zero]
        · have : e - j < e := by have := Finset.mem_range.mp hj; omega
          rw [IH (e-j) this]
      have hkq := key_q e
      have hka := key_a e
      have he0 : (e:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have heq : (e:ℚ) * PowerSeries.coeff e (Cps^2) = (e:ℚ) * PowerSeries.coeff e Aps := by
        rw [hkq, hsum, ← hka]
      exact mul_left_cancel₀ he0 heq

/-- The key convolution identity: `(c * c)(e) = a(e)`. -/
lemma conv_cc (e : ℕ) : ∑ j ∈ range (e+1), c j * c (e-j) = a e := by
  have h1 : PowerSeries.coeff e (Cps^2) = PowerSeries.coeff e Aps := by rw [uniq]
  rw [sq, coeff_mul_rangeP] at h1
  simp only [Cps, Aps, PowerSeries.coeff_mk] at h1
  exact h1


lemma floor_div_two_pow_zero (m j : ℕ) (h : m ≤ j) : m / 2^j = 0 := by
  apply Nat.div_eq_of_lt
  calc m < 2^m := Nat.lt_two_pow_self
    _ ≤ 2^j := Nat.pow_le_pow_right (by norm_num) h

lemma sum_floor_eq (m U : ℕ) (h : m < U) : ∑ k ∈ range U, m / 2^k = A005187 m := by
  unfold A005187
  symm
  apply Finset.sum_subset
  · exact Finset.range_subset_range.mpr (by omega)
  · intro k _ hk'
    simp only [Finset.mem_range, not_lt] at hk'
    exact floor_div_two_pow_zero m k (by omega)

lemma A005187_even (m : ℕ) (hm : 1 ≤ m) : A005187 (2*m) = 2*m + A005187 m := by
  have hterm : ∀ k, (2*m)/2^(k+1) = m/2^k := by
    intro k
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    congr 1
    exact Nat.mul_div_cancel_left m (by norm_num)
  have e1 : A005187 (2*m) = (∑ k ∈ range (2*m), (2*m)/2^(k+1)) + (2*m)/2^0 := by
    rw [A005187, Finset.sum_range_succ' (fun k => (2*m)/2^k) (2*m)]
  rw [e1, Finset.sum_congr rfl (fun k _ => hterm k), sum_floor_eq m (2*m) (by omega),
    pow_zero, Nat.div_one]
  omega

lemma A005187_odd (m : ℕ) : A005187 (2*m+1) = 2*m+1 + A005187 m := by
  have hterm : ∀ k, (2*m+1)/2^(k+1) = m/2^k := by
    intro k
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    congr 1
    omega
  have e1 : A005187 (2*m+1) = (∑ k ∈ range (2*m+1), (2*m+1)/2^(k+1)) + (2*m+1)/2^0 := by
    rw [A005187, Finset.sum_range_succ' (fun k => (2*m+1)/2^k) (2*m+1)]
  rw [e1, Finset.sum_congr rfl (fun k _ => hterm k), sum_floor_eq m (2*m+1) (by omega),
    pow_zero, Nat.div_one]
  omega

lemma a_eq_pow : ∀ e, a e = (2:ℚ)^(A005187 e) := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e IH =>
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; rw [a_zero]; norm_num [A005187]
    · have h4 : (4:ℚ)^(e/2) = 2^(2*(e/2)) := by
        rw [show (4:ℚ) = 2^2 from by norm_num, ← pow_mul]
      rcases Nat.even_or_odd e with ⟨m,hm⟩ | ⟨m,hm⟩
      · have hm2 : e = 2*m := by omega
        subst hm2
        have hmpos : 1 ≤ m := by omega
        have h4' : (4:ℚ)^m = 2^(2*m) := by
          rw [show (4:ℚ) = 2^2 from by norm_num, ← pow_mul]
        rw [a_even m, IH m (by omega), A005187_even m hmpos, h4', ← pow_add]
      · subst hm
        have h4' : (4:ℚ)^m = 2^(2*m) := by
          rw [show (4:ℚ) = 2^2 from by norm_num, ← pow_mul]
        rw [a_odd m, IH m (by omega), A005187_odd m, h4', pow_add, pow_add, pow_one]
        ring

lemma A005187_zero : A005187 0 = 0 := by simp [A005187]

open ArithmeticFunction

/-- Build a multiplicative arithmetic function from prime-power values `phi`. -/
noncomputable def mkMult (phi : ℕ → ℚ) : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod (fun _ e => phi e), by simp⟩

lemma mkMult_apply (phi : ℕ → ℚ) {n : ℕ} (hn : n ≠ 0) :
    mkMult phi n = n.factorization.prod (fun _ e => phi e) := by
  simp only [mkMult, ArithmeticFunction.coe_mk, hn, if_false]

lemma mkMult_prime_pow (phi : ℕ → ℚ) (h0 : phi 0 = 1) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    mkMult phi (p^i) = phi i := by
  rw [mkMult_apply phi (pow_ne_zero i hp.pos.ne'), Nat.Prime.factorization_pow hp,
    Finsupp.prod_single_index h0]

lemma mkMult_mult (phi : ℕ → ℚ) : (mkMult phi).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [mkMult_apply phi one_ne_zero, Nat.factorization_one, Finsupp.prod_zero_index]
  · intro m n hm hn hcop
    rw [mkMult_apply phi (Nat.mul_ne_zero hm hn), mkMult_apply phi hm, mkMult_apply phi hn,
      Nat.factorization_mul hm hn, Finsupp.prod_add_index_of_disjoint]
    rw [Nat.support_factorization, Nat.support_factorization]
    exact (Nat.disjoint_primeFactors hm hn).mpr hcop

noncomputable def Ff : ArithmeticFunction ℚ := mkMult c
noncomputable def Af : ArithmeticFunction ℚ := mkMult (fun e => (2:ℚ)^(A005187 e))

lemma Ff_mult : Ff.IsMultiplicative := mkMult_mult c
lemma Af_mult : Af.IsMultiplicative := mkMult_mult _

lemma Ff_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) : Ff (p^i) = c i :=
  mkMult_prime_pow c c_zero hp i

lemma FfFf_eq_Af : Ff * Ff = Af := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers (Ff * Ff)
    (Ff_mult.mul Ff_mult) Af Af_mult]
  intro p i hp
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun x y => Ff x * Ff y),
    Nat.sum_divisors_prime_pow hp]
  rw [show Af (p^i) = mkMult (fun e => (2:ℚ)^(A005187 e)) (p^i) from rfl,
    mkMult_prime_pow _ (by rw [A005187_zero]; norm_num) hp i,
    ← a_eq_pow i, ← conv_cc i]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≤ i := by have := Finset.mem_range.mp hj; omega
  rw [Ff_prime_pow hp, Nat.pow_div hji hp.pos, Ff_prime_pow hp]



lemma A046644_eq_Af (n : ℕ) : A046644 n = Af n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [A046644, Af, mkMult]
  · rw [A046644, if_neg (by omega), Af, mkMult_apply _ (by omega)]

lemma Ff_one : Ff 1 = 1 := Ff_mult.map_one

lemma A317940_f_eq (n : ℕ) (hn : 2 ≤ n) :
    A317940_f n =
      (A046644 n - ∑ d ∈ n.divisors,
        (if 1 < d ∧ d < n then A317940_f d * A317940_f (n / d) else 0)) / 2 := by
  conv_lhs => rw [A317940_f, WellFounded.fix_eq]
  rw [if_neg (by omega), if_neg (by omega)]
  congr 2

lemma A317940_f_zero : A317940_f 0 = 0 := by
  conv_lhs => rw [A317940_f, WellFounded.fix_eq]
  rw [if_pos rfl]

lemma A317940_f_one : A317940_f 1 = 1 := by
  conv_lhs => rw [A317940_f, WellFounded.fix_eq]
  rw [if_neg one_ne_zero, if_pos rfl]

lemma conv_split (n : ℕ) (hn : 2 ≤ n) :
    (Ff * Ff) n = 2 * Ff n + ∑ d ∈ n.divisors,
      (if 1 < d ∧ d < n then Ff d * Ff (n/d) else 0) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (f := fun x y => Ff x * Ff y),
    ← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => 1 < d ∧ d < n)
        (fun d => Ff d * Ff (n/d)), add_comm]
  congr 1
  · have hfil : n.divisors.filter (fun d => ¬(1 < d ∧ d < n)) = {1, n} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hdvd, _⟩, hnp⟩
        have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
        omega
      · rintro (rfl | rfl)
        · exact ⟨⟨one_dvd _, by omega⟩, by omega⟩
        · exact ⟨⟨dvd_refl _, by omega⟩, by omega⟩
    rw [hfil, Finset.sum_pair (by omega : (1:ℕ) ≠ n),
      show n/1 = n from Nat.div_one n, show n/n = 1 from Nat.div_self (by omega), Ff_one]
    ring
  · rw [Finset.sum_filter]

lemma Ff_eq_f : ∀ n, Ff n = A317940_f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · rw [A317940_f_zero, ArithmeticFunction.map_zero]
      · rw [A317940_f_one, Ff_one]
    · have hconv : (Ff * Ff) n = A046644 n := by rw [FfFf_eq_Af, ← A046644_eq_Af]
      rw [conv_split n hge] at hconv
      rw [A317940_f_eq n hge]
      have hSS : (∑ d ∈ n.divisors, (if 1 < d ∧ d < n then Ff d * Ff (n/d) else 0))
          = ∑ d ∈ n.divisors, (if 1 < d ∧ d < n then A317940_f d * A317940_f (n/d) else 0) := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hp : 1 < d ∧ d < n
        · rw [if_pos hp, if_pos hp, IH d hp.2, IH (n/d) (Nat.div_lt_self (by omega) hp.1)]
        · rw [if_neg hp, if_neg hp]
      rw [← hSS]
      linarith [hconv]

lemma Ff_nonneg (n : ℕ) : 0 ≤ Ff n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; rw [ArithmeticFunction.map_zero]
  · rw [show Ff = mkMult c from rfl, mkMult_apply c (by omega)]
    exact Finset.prod_nonneg (fun p _ => c_nonneg _)
end Dev

/--
A317940 No negative terms among the first 2^20 terms. Is the sequence nonnegative?
Conjecture: The sequence of rational numbers $A317940\_f(n)$ is nonnegative for all $n \ge 1$.
-/
theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) : A317940_f n ≥ 0 := by
  rw [← Dev.Ff_eq_f n]
  exact Dev.Ff_nonneg n
