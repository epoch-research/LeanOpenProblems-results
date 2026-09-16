import FormalConjectures.Util.ProblemImports

open Nat
open scoped BigOperators

def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum
def delta (x : ℕ) : ℤ := Int.sign ((S (5 * x) : ℤ) - (S x : ℤ))

lemma S_zero : S 0 = 0 := by
  unfold S
  rw [Nat.digits_zero]
  rfl

lemma S_eq (a b : ℕ) (hb : b < 10) : S (10 * a + b) = b + S a := by
  by_cases h : 10 * a + b = 0
  · have h1 : a = 0 := by omega
    have h2 : b = 0 := by omega
    subst h1 h2
    simp [S_zero]
  · have h10 : 1 < 10 := by decide
    have H : (10 * a + b) % 10 = b := by omega
    have H2 : (10 * a + b) / 10 = a := by omega
    unfold S
    rw [Nat.digits_def' h10 (by omega)]
    simp [H, H2]

lemma S_5q_c (q c : ℕ) (hc : c ≤ 4) : S (5 * q + c) = S (5 * q) + c := by
  by_cases hq : q % 2 = 0
  · have H1 : 5 * q % 10 = 0 := by omega
    have H2 : 10 * (5 * q / 10) + 0 = 5 * q := by omega
    have H3 : 5 * q + c = 10 * (5 * q / 10) + c := by omega
    have H4 : S (10 * (5 * q / 10) + c) = c + S (5 * q / 10) := S_eq _ c (by omega)
    have H5 : S (10 * (5 * q / 10) + 0) = 0 + S (5 * q / 10) := S_eq _ 0 (by omega)
    calc S (5 * q + c)
      _ = S (10 * (5 * q / 10) + c) := by rw [H3]
      _ = c + S (5 * q / 10) := H4
      _ = (0 + S (5 * q / 10)) + c := by omega
      _ = S (10 * (5 * q / 10) + 0) + c := by rw [H5]
      _ = S (5 * q) + c := by rw [H2]
  · have H1 : 5 * q % 10 = 5 := by omega
    have H2 : 10 * (5 * q / 10) + 5 = 5 * q := by omega
    have H3 : 5 * q + c = 10 * (5 * q / 10) + (5 + c) := by omega
    have H4 : S (10 * (5 * q / 10) + (5 + c)) = (5 + c) + S (5 * q / 10) := S_eq _ (5 + c) (by omega)
    have H5 : S (10 * (5 * q / 10) + 5) = 5 + S (5 * q / 10) := S_eq _ 5 (by omega)
    calc S (5 * q + c)
      _ = S (10 * (5 * q / 10) + (5 + c)) := by rw [H3]
      _ = (5 + c) + S (5 * q / 10) := H4
      _ = (5 + S (5 * q / 10)) + c := by omega
      _ = S (10 * (5 * q / 10) + 5) + c := by rw [H5]
      _ = S (5 * q) + c := by rw [H2]

lemma S_5x_add (k : ℕ) : ∀ x < 10^k, S (5 * x) + S (5 * (10^k - 1 - x)) = 9 * k := by
  induction k with
  | zero =>
    intro x hx
    have : x = 0 := by omega
    subst this
    have : 10^0 - 1 - 0 = 0 := by rfl
    rw [this]
    simp [S_zero]
  | succ k ih =>
    intro x hx
    have hk10 : 10^(k+1) = 10 * 10^k := by ring
    have hq : x / 10 < 10^k := by omega
    set q := x / 10
    set r := x % 10
    set q' := 10^k - 1 - q
    set r' := 9 - r
    have hx_eq : x = 10 * q + r := by omega
    have h10k_pos : 0 < 10^k := by positivity
    have hy_eq : 10^(k+1) - 1 - x = 10 * q' + r' := by omega
    have h5x : 5 * x = 10 * (5 * q + r / 2) + 5 * (r % 2) := by omega
    have h5y : 5 * (10^(k+1) - 1 - x) = 10 * (5 * q' + r' / 2) + 5 * (r' % 2) := by omega
    have Hx : S (5 * x) = 5 * (r % 2) + S (5 * q + r / 2) := by
      rw [h5x]
      apply S_eq
      omega
    have Hy : S (5 * (10^(k+1) - 1 - x)) = 5 * (r' % 2) + S (5 * q' + r' / 2) := by
      rw [h5y]
      apply S_eq
      omega
    rw [Hx, Hy]
    have Hc : S (5 * q + r / 2) = S (5 * q) + r / 2 := S_5q_c q (r / 2) (by omega)
    have Hc' : S (5 * q' + r' / 2) = S (5 * q') + r' / 2 := S_5q_c q' (r' / 2) (by omega)
    rw [Hc, Hc']
    have Hih : S (5 * q) + S (5 * q') = 9 * k := ih q hq
    omega

lemma S_x_add (k : ℕ) : ∀ x < 10^k, S x + S (10^k - 1 - x) = 9 * k := by
  induction k with
  | zero =>
    intro x hx
    have : x = 0 := by omega
    subst this
    have : 10^0 - 1 - 0 = 0 := by rfl
    rw [this]
    simp [S_zero]
  | succ k ih =>
    intro x hx
    have hk10 : 10^(k+1) = 10 * 10^k := by ring
    have hq : x / 10 < 10^k := by omega
    set q := x / 10
    set r := x % 10
    set q' := 10^k - 1 - q
    set r' := 9 - r
    have hx_eq : x = 10 * q + r := by omega
    have h10k_pos : 0 < 10^k := by positivity
    have hy_eq : 10^(k+1) - 1 - x = 10 * q' + r' := by omega
    have Hx : S x = r + S q := by
      nth_rw 1 [hx_eq]
      apply S_eq
      omega
    have Hy : S (10^(k+1) - 1 - x) = r' + S q' := by
      rw [hy_eq]
      apply S_eq
      omega
    rw [Hx, Hy]
    have Hih : S q + S q' = 9 * k := ih q hq
    omega

lemma sum_pair_zero (i start : ℕ) (f : ℕ → ℤ)
  (h_symm : ∀ d < i, f (start + d) + f (start + 2 * i - 1 - d) = 0) :
  (Finset.Ico start (start + 2 * i)).sum f = 0 := by
  induction i generalizing start with
  | zero => simp
  | succ i ih =>
    have heq : start + 2 * (i + 1) = start + 2 * i + 2 := by ring
    rw [heq]
    have h1 : start < start + 2 * i + 2 := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot h1]
    have h2 : start + 1 ≤ start + 2 * i + 1 := by omega
    rw [Finset.sum_Ico_succ_top h2]
    have H : (Finset.Ico (start + 1) (start + 2 * i + 1)).sum f = 0 := by
      have H2 : start + 2 * i + 1 = start + 1 + 2 * i := by omega
      rw [H2]
      apply ih (start + 1)
      intro d hd
      have := h_symm (d + 1) (by omega)
      have eq1 : start + 1 + d = start + (d + 1) := by ring
      have eq2 : start + 1 + 2 * i - 1 - d = start + 2 * (i + 1) - 1 - (d + 1) := by omega
      rw [eq1, eq2]
      exact this
    have eq3 : start + 2 * (i + 1) - 1 - 0 = start + 2 * i + 1 := by omega
    have := h_symm 0 (by omega)
    have eq4 : start + 0 = start := by ring
    rw [eq4, eq3] at this
    rw [H]
    linarith

lemma delta_symm (k x y : ℕ)
    (H1 : S (5 * x) + S (5 * y) = 9 * k)
    (H2 : S x + S y = 9 * k) : delta x + delta y = 0 := by
  unfold delta
  have h1 : (S (5 * x) : ℤ) + (S (5 * y) : ℤ) = (9 * k : ℤ) := by omega
  have h2 : (S x : ℤ) + (S y : ℤ) = (9 * k : ℤ) := by omega
  have h3 : (S (5 * x) : ℤ) - (S x : ℤ) = - ((S (5 * y) : ℤ) - (S y : ℤ)) := by omega
  rw [h3, Int.sign_neg]
  omega

lemma pow_ten_even (k : ℕ) (hk : 0 < k) : 10^k = 2 * (10^k / 2) := by
  cases k with
  | zero => omega
  | succ k =>
    have : 10^(k+1) = 2 * (5 * 10^k) := by
      calc 10^(k+1) = 10 * 10^k := by ring
        _ = (2 * 5) * 10^k := by rfl
        _ = 2 * (5 * 10^k) := by ring
    rw [this]
    have : 2 * (5 * 10^k) / 2 = 5 * 10^k := Nat.mul_div_cancel_left _ (by decide)
    rw [this]

/--
A289411: $\mathrm{a}(n) = \sum_{k=0}^n \mathrm{sign}(\mathrm{A007953}(5k) - \mathrm{A007953}(k))$.
$\mathrm{A007953}(n)$ is the digital sum of $n$ in base 10.
The sequence is non-negative, so the sum over $\mathbb{Z}$ is converted to $\mathbb{N}$.
-/
def A289411 (n : ℕ) : ℕ :=
  let digital_sum_ten (m : ℕ) : ℕ := (Nat.digits 10 m).sum
  (Finset.range (n + 1)).sum (fun k =>
    Int.sign ((digital_sum_ten (5 * k) : ℤ) - (digital_sum_ten k : ℤ)))
  |>.toNat

lemma A289411_eq (n : ℕ) : A289411 n = ((Finset.range (n + 1)).sum delta).toNat := by
  rfl

/--
this relation is conjectured to hold for any k > 0, where $m_k = 10^k/2 - 1$.
The relation is $a(m_k - i) = a(m_k + i)$ for $i = 0 \dots m_k$.
-/
theorem oeis_289411_conjecture_0 (k : ℕ) (hk : 0 < k) :
  let m_k : ℕ := (10 ^ k) / 2 - 1
  ∀ i : ℕ, i ≤ m_k → A289411 (m_k - i) = A289411 (m_k + i) := by
  intro m_k i hi
  rw [A289411_eq, A289411_eq]
  congr 1
  change (Finset.range (m_k - i + 1)).sum delta = (Finset.range (m_k + i + 1)).sum delta
  have h_even : 10^k = 2 * (10^k / 2) := pow_ten_even k hk
  have h10_pos : 0 < 10^k := by positivity
  have h_start_le : m_k - i + 1 ≤ m_k + i + 1 := by omega
  have H_split : (Finset.range (m_k + i + 1)).sum delta =
    (Finset.range (m_k - i + 1)).sum delta + (Finset.Ico (m_k - i + 1) (m_k + i + 1)).sum delta := by
    rw [Finset.sum_range_add_sum_Ico delta h_start_le]
  have H_end : m_k - i + 1 + 2 * i = m_k + i + 1 := by omega
  have H_sum0 : (Finset.Ico (m_k - i + 1) (m_k + i + 1)).sum delta = 0 := by
    rw [← H_end]
    apply sum_pair_zero
    intro d hd
    have H_sum_args : (m_k - i + 1 + d) + (m_k - i + 1 + 2 * i - 1 - d) = 10^k - 1 := by omega
    set x := m_k - i + 1 + d
    set y := m_k - i + 1 + 2 * i - 1 - d
    have Hx_lt : x < 10^k := by omega
    have Hx_y : y = 10^k - 1 - x := by omega
    have H1 : S (5 * x) + S (5 * y) = 9 * k := by
      rw [Hx_y]
      exact S_5x_add k x Hx_lt
    have H2 : S x + S y = 9 * k := by
      rw [Hx_y]
      exact S_x_add k x Hx_lt
    exact delta_symm k x y H1 H2
  rw [H_sum0] at H_split
  omega

theorem oeis_289411_conjecture_0.disproof : ¬ (type_of% @oeis_289411_conjecture_0) := sorry
