import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A308734: Number of ordered ways to write $n$ as $(2^a \cdot 3^b)^2 + (2^c \cdot 5^d)^2 + x^2 + y^2$,
where $a,b,c,d,x,y$ are nonnegative integers with $x \le y$.

Note: The provided definition uses a computationally convenient, but potentially insufficient, range `M` for the exponents $a, b, c, d$.
A mathematically precise definition would use unbounded natural numbers for $a, b, c, d, x, y$ and count the size of the resulting set.
We proceed with the definition as given in the prompt.
-/
def A308734 (n : ℕ) : ℕ :=
  -- We use a six-fold nested summation over a range $M$.
  let M := Nat.sqrt n + 1

  Finset.sum (range M) fun a =>
  Finset.sum (range M) fun b =>
  Finset.sum (range M) fun c =>
  Finset.sum (range M) fun d =>
  Finset.sum (range M) fun x =>
  Finset.sum (range M) fun y =>
    let term1 := (2^a * 3^b)^2
    let term2 := (2^c * 5^d)^2

    if term1 + term2 + x^2 + y^2 = n ∧ x ≤ y
    then 1
    else 0

/--
Four-square Conjecture: a(n) > 0 for all n > 1.
This is much stronger than Lagrange's four-square theorem.
(OEIS A308734, Comment C2)
-/
lemma A308734_pos_of_exists (n : ℕ) (a b c d x y : ℕ)
    (ha : a < Nat.sqrt n + 1) (hb : b < Nat.sqrt n + 1)
    (hc : c < Nat.sqrt n + 1) (hd : d < Nat.sqrt n + 1)
    (hx : x < Nat.sqrt n + 1) (hy : y < Nat.sqrt n + 1)
    (h : (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n)
    (hxy : x ≤ y) :
    A308734 n > 0 := by
  have h_a : a ∈ range (Nat.sqrt n + 1) := mem_range.mpr ha
  have h_b : b ∈ range (Nat.sqrt n + 1) := mem_range.mpr hb
  have h_c : c ∈ range (Nat.sqrt n + 1) := mem_range.mpr hc
  have h_d : d ∈ range (Nat.sqrt n + 1) := mem_range.mpr hd
  have h_x : x ∈ range (Nat.sqrt n + 1) := mem_range.mpr hx
  have h_y : y ∈ range (Nat.sqrt n + 1) := mem_range.mpr hy

  -- M is Nat.sqrt n + 1
  -- We want to show A308734 n > 0, which is A308734 n ≥ 1.
  -- We will use single_le_sum repeatedly.
  have h1 : (Finset.sum (range (Nat.sqrt n + 1)) fun b =>
             Finset.sum (range (Nat.sqrt n + 1)) fun c =>
             Finset.sum (range (Nat.sqrt n + 1)) fun d =>
             Finset.sum (range (Nat.sqrt n + 1)) fun x =>
             Finset.sum (range (Nat.sqrt n + 1)) fun y =>
             if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ A308734 n := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_a

  have h2 : (Finset.sum (range (Nat.sqrt n + 1)) fun c =>
             Finset.sum (range (Nat.sqrt n + 1)) fun d =>
             Finset.sum (range (Nat.sqrt n + 1)) fun x =>
             Finset.sum (range (Nat.sqrt n + 1)) fun y =>
             if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ (Finset.sum (range (Nat.sqrt n + 1)) fun b =>
               Finset.sum (range (Nat.sqrt n + 1)) fun c =>
               Finset.sum (range (Nat.sqrt n + 1)) fun d =>
               Finset.sum (range (Nat.sqrt n + 1)) fun x =>
               Finset.sum (range (Nat.sqrt n + 1)) fun y =>
               if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_b

  have h3 : (Finset.sum (range (Nat.sqrt n + 1)) fun d =>
             Finset.sum (range (Nat.sqrt n + 1)) fun x =>
             Finset.sum (range (Nat.sqrt n + 1)) fun y =>
             if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ (Finset.sum (range (Nat.sqrt n + 1)) fun c =>
               Finset.sum (range (Nat.sqrt n + 1)) fun d =>
               Finset.sum (range (Nat.sqrt n + 1)) fun x =>
               Finset.sum (range (Nat.sqrt n + 1)) fun y =>
               if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_c

  have h4 : (Finset.sum (range (Nat.sqrt n + 1)) fun x =>
             Finset.sum (range (Nat.sqrt n + 1)) fun y =>
             if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ (Finset.sum (range (Nat.sqrt n + 1)) fun d =>
               Finset.sum (range (Nat.sqrt n + 1)) fun x =>
               Finset.sum (range (Nat.sqrt n + 1)) fun y =>
               if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_d

  have h5 : (Finset.sum (range (Nat.sqrt n + 1)) fun y =>
             if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ (Finset.sum (range (Nat.sqrt n + 1)) fun x =>
               Finset.sum (range (Nat.sqrt n + 1)) fun y =>
               if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_x

  have h6 : (if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ (Finset.sum (range (Nat.sqrt n + 1)) fun y =>
               if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) := by
    apply single_le_sum (fun _ _ => Nat.zero_le _) h_y

  have h_term : (if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0) = 1 := by
    simp [h, hxy]

  have h_final : 1 ≤ A308734 n := by
    rw [← h_term]
    exact h6.trans (h5.trans (h4.trans (h3.trans (h2.trans h1))))

  exact h_final

lemma m_sq_le_pow_two (m : ℕ) : m * m ≤ 2^(2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h_pow : 2^(2 * (m + 1) + 1) = 4 * 2^(2 * m + 1) := by ring
    rw [h_pow]
    rcases m with rfl | m
    · simp
    · have h1 : (m + 2) ≤ 2 * (m + 1) := by omega
      have h2 : (m + 2) * (m + 2) ≤ (2 * (m + 1)) * (2 * (m + 1)) := Nat.mul_le_mul h1 h1
      have h3 : (2 * (m + 1)) * (2 * (m + 1)) = 4 * ((m + 1) * (m + 1)) := by ring
      have h4 : (m + 2) * (m + 2) ≤ 4 * ((m + 1) * (m + 1)) := by omega
      have h5 : 4 * ((m + 1) * (m + 1)) ≤ 4 * 2^(2 * (m + 1) + 1) := Nat.mul_le_mul_left 4 ih
      exact h4.trans h5

lemma k_le_two_pow (k : ℕ) : k < 2^(k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : k + 1 ≤ 2^(k + 1) := ih
    have : 2^(k + 1) < 2^(k + 2) := by
      have : 2^(k + 2) = 2^(k + 1) * 2 := by ring
      rw [this]
      have : 0 < 2^(k + 1) := by positivity
      omega
    omega

lemma A308734_power_of_two_odd (m : ℕ) : A308734 (2^(2 * m + 1)) > 0 := by
  have heq : (2^m * 3^0)^2 + (2^m * 5^0)^2 + 0^2 + 0^2 = 2^(2 * m + 1) := by
    ring
  have hsqrt : m < Nat.sqrt (2^(2 * m + 1)) + 1 := by
    rw [Nat.lt_add_one_iff, Nat.le_sqrt]
    exact m_sq_le_pow_two m
  apply A308734_pos_of_exists (2^(2 * m + 1)) m 0 m 0 0 0
  · exact hsqrt
  · simp
  · exact hsqrt
  · simp
  · simp
  · simp
  · exact heq
  · omega

lemma A308734_power_of_two_even (k : ℕ) : A308734 (2^(2 * k + 2)) > 0 := by
  have heq : (2^k * 3^0)^2 + (2^k * 5^0)^2 + (2^k)^2 + (2^k)^2 = 2^(2 * k + 2) := by
    ring
  have h_bound_k : k * k ≤ 2^(2 * k + 2) := by
    have h1 : k * k ≤ 2^(2 * k + 1) := m_sq_le_pow_two k
    have h2 : 2^(2 * k + 1) ≤ 2^(2 * k + 2) := by
      have : 2 * k + 2 = (2 * k + 1) + 1 := by omega
      rw [this]
      have : 2^((2 * k + 1) + 1) = 2^(2 * k + 1) * 2 := by ring
      rw [this]
      omega
    exact h1.trans h2
  have hsqrt_k : k < Nat.sqrt (2^(2 * k + 2)) + 1 := by
    rw [Nat.lt_add_one_iff, Nat.le_sqrt]
    exact h_bound_k
  have h_bound_pow : 2^k * 2^k ≤ 2^(2 * k + 2) := by
    have : 2^k * 2^k = 2^(2 * k) := by ring
    rw [this]
    have : 2 * k + 2 = 2 * k + 2 := rfl
    have : 2^(2 * k) ≤ 2^(2 * k + 2) := by
      have : 2 * k + 2 = (2 * k) + 2 := by omega
      rw [this]
      have : 2^((2 * k) + 2) = 2^(2 * k) * 4 := by ring
      rw [this]
      omega
    exact this
  have hsqrt_pow : 2^k < Nat.sqrt (2^(2 * k + 2)) + 1 := by
    rw [Nat.lt_add_one_iff, Nat.le_sqrt]
    exact h_bound_pow
  apply A308734_pos_of_exists (2^(2 * k + 2)) k 0 k 0 (2^k) (2^k)
  · exact hsqrt_k
  · simp
  · exact hsqrt_k
  · simp
  · exact hsqrt_pow
  · exact hsqrt_pow
  · exact heq
  · omega

lemma A308734_4k (k : ℕ) (hk : 1 < k) (a b c d x y : ℕ)
    (ha : a < Nat.sqrt k + 1) (hb : b < Nat.sqrt k + 1)
    (hc : c < Nat.sqrt k + 1) (hd : d < Nat.sqrt k + 1)
    (_hx : x < Nat.sqrt k + 1) (hy : y < Nat.sqrt k + 1)
    (heq : (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = k)
    (hxy : x ≤ y) :
    ∃ a' b' c' d' x' y' : ℕ,
      a' < Nat.sqrt (4 * k) + 1 ∧
      b' < Nat.sqrt (4 * k) + 1 ∧
      c' < Nat.sqrt (4 * k) + 1 ∧
      d' < Nat.sqrt (4 * k) + 1 ∧
      x' < Nat.sqrt (4 * k) + 1 ∧
      y' < Nat.sqrt (4 * k) + 1 ∧
      (2^a' * 3^b')^2 + (2^c' * 5^d')^2 + x'^2 + y'^2 = 4 * k ∧
      x' ≤ y' := by
  use a + 1, b, c + 1, d, 2 * x, 2 * y
  have hsqrt : 2 * Nat.sqrt k ≤ Nat.sqrt (4 * k) := by
    rw [Nat.le_sqrt]
    calc (2 * Nat.sqrt k) * (2 * Nat.sqrt k)
      _ = 4 * (Nat.sqrt k * Nat.sqrt k) := by ring
      _ ≤ 4 * k := Nat.mul_le_mul_left 4 (Nat.sqrt_le k)
  have h_sqrt_k_pos : 1 ≤ Nat.sqrt k := by
    by_contra hc
    have : Nat.sqrt k = 0 := by omega
    have : k = 0 := Nat.sqrt_eq_zero.mp this
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_pow_a : 2^(a + 1) = 2^a * 2 := by ring
    have h_pow_c : 2^(c + 1) = 2^c * 2 := by ring
    rw [h_pow_a, h_pow_c]
    calc (2 ^ a * 2 * 3 ^ b) ^ 2 + (2 ^ c * 2 * 5 ^ d) ^ 2 + (2 * x) ^ 2 + (2 * y) ^ 2
      _ = 4 * ((2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2) := by ring
      _ = 4 * k := by rw [heq]
  · omega

lemma exists_solution (n : ℕ) (hn : 1 < n) :
    ∃ a b c d x y : ℕ,
      a < Nat.sqrt n + 1 ∧
      b < Nat.sqrt n + 1 ∧
      c < Nat.sqrt n + 1 ∧
      d < Nat.sqrt n + 1 ∧
      x < Nat.sqrt n + 1 ∧
      y < Nat.sqrt n + 1 ∧
      (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧
      x ≤ y := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | _ | n
  · contradiction
  · contradiction
  · -- n = 2
    use 0, 0, 0, 0, 0, 0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩
    all_goals { rw [Nat.lt_add_one_iff, Nat.le_sqrt]; omega }
  · -- n = 3
    use 0, 0, 0, 0, 0, 1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩
    all_goals { rw [Nat.lt_add_one_iff, Nat.le_sqrt]; omega }
  · -- n = n + 4
    by_cases h4 : 4 ∣ (n + 4)
    · rcases h4 with ⟨j, hj⟩
      have hj_pos : 1 ≤ j := by omega
      rcases j with _ | j
      · contradiction
      · -- j = j + 1
        rcases j with rfl | j
        · -- j = 1, so n + 4 = 4
          have hn0 : n = 0 := by omega
          subst hn0
          use 0, 0, 0, 0, 1, 1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩
          all_goals { rw [Nat.lt_add_one_iff, Nat.le_sqrt]; omega }
        · -- j = j_1 + 2, so j >= 2
          have hj_bound : j + 2 < n + 4 := by omega
          obtain ⟨a, b, c, d, x, y, ha, hb, hc, hd, _hx, hy, heq, hxy⟩ := ih (j + 2) hj_bound (by omega)
          have h_4k := A308734_4k (j + 2) (by omega) a b c d x y ha hb hc hd (by omega) hy heq hxy
          rcases h_4k with ⟨a', b', c', d', x', y', ha', hb', hc', hd', hx', hy', heq', hxy'⟩
          use a', b', c', d', x', y'
          rw [hj]
          exact ⟨ha', hb', hc', hd', hx', hy', heq', hxy'⟩
    · -- ¬ 4 ∣ n + 4
      sorry



lemma test_four_squares (n : ℕ) : ∃ a b c d : ℕ, a^2 + b^2 + c^2 + d^2 = n := Nat.sum_four_squares n

theorem oeis_a308734_conjecture_0 : ∀ n : ℕ, 1 < n → A308734 n > 0 := by
  intro n hn
  obtain ⟨a, b, c, d, x, y, ha, hb, hc, hd, hx, hy, heq, hxy⟩ := exists_solution n hn
  exact A308734_pos_of_exists n a b c d x y ha hb hc hd hx hy heq hxy


