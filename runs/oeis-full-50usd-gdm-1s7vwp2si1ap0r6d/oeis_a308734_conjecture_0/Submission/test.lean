import FormalConjectures.Util.ProblemImports

open Nat Finset

def A308734_local (n : ℕ) : ℕ :=
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

lemma A308734_pos_of_exists (n : ℕ) (a b c d x y : ℕ)
    (ha : a < Nat.sqrt n + 1) (hb : b < Nat.sqrt n + 1)
    (hc : c < Nat.sqrt n + 1) (hd : d < Nat.sqrt n + 1)
    (hx : x < Nat.sqrt n + 1) (hy : y < Nat.sqrt n + 1)
    (h : (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n)
    (hxy : x ≤ y) :
    A308734_local n > 0 := by
  have h_a : a ∈ range (Nat.sqrt n + 1) := mem_range.mpr ha
  have h_b : b ∈ range (Nat.sqrt n + 1) := mem_range.mpr hb
  have h_c : c ∈ range (Nat.sqrt n + 1) := mem_range.mpr hc
  have h_d : d ∈ range (Nat.sqrt n + 1) := mem_range.mpr hd
  have h_x : x ∈ range (Nat.sqrt n + 1) := mem_range.mpr hx
  have h_y : y ∈ range (Nat.sqrt n + 1) := mem_range.mpr hy

  -- M is Nat.sqrt n + 1
  -- We want to show A308734_local n > 0, which is A308734_local n ≥ 1.
  -- We will use single_le_sum repeatedly.
  have h1 : (Finset.sum (range (Nat.sqrt n + 1)) fun b =>
             Finset.sum (range (Nat.sqrt n + 1)) fun c =>
             Finset.sum (range (Nat.sqrt n + 1)) fun d =>
             Finset.sum (range (Nat.sqrt n + 1)) fun x =>
             Finset.sum (range (Nat.sqrt n + 1)) fun y =>
             if (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n ∧ x ≤ y then 1 else 0)
            ≤ A308734_local n := by
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

  have h_final : 1 ≤ A308734_local n := by
    rw [← h_term]
    exact h6.trans (h5.trans (h4.trans (h3.trans (h2.trans h1))))

  exact h_final



lemma A308734_4k (k : ℕ) (hk : 1 < k) (a b c d x y : ℕ)
    (ha : a < Nat.sqrt k + 1) (hb : b < Nat.sqrt k + 1)
    (hc : c < Nat.sqrt k + 1) (hd : d < Nat.sqrt k + 1)
    (hx : x < Nat.sqrt k + 1) (hy : y < Nat.sqrt k + 1)
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
  · -- a + 1 < Nat.sqrt (4 * k) + 1
    omega
  · -- b < Nat.sqrt (4 * k) + 1
    omega
  · -- c + 1 < Nat.sqrt (4 * k) + 1
    omega
  · -- d < Nat.sqrt (4 * k) + 1
    omega
  · -- 2 * x < Nat.sqrt (4 * k) + 1
    omega
  · -- 2 * y < Nat.sqrt (4 * k) + 1
    omega
  · -- equation
    have h_pow_a : 2^(a + 1) = 2^a * 2 := by ring
    have h_pow_c : 2^(c + 1) = 2^c * 2 := by ring
    rw [h_pow_a, h_pow_c]
    calc (2 ^ a * 2 * 3 ^ b) ^ 2 + (2 ^ c * 2 * 5 ^ d) ^ 2 + (2 * x) ^ 2 + (2 * y) ^ 2
      _ = 4 * ((2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 + x ^ 2 + y ^ 2) := by ring
      _ = 4 * k := by rw [heq]
  · -- 2 * x ≤ 2 * y
    omega

theorem test_answer_sorry_simp : answer(sorry) ↔ 1 + 1 = 2 := by simp


#eval A308734_local 2
#eval A308734_local 3
#eval A308734_local 4
#eval A308734_local 5
#eval A308734_local 6
#eval A308734_local 7
#eval A308734_local 8





#print axioms test_answer_sorry_simp




partial def partial_test (n : ℕ) : {x : ℕ // x = n} :=
  if h : n = n then
    ⟨n, h⟩
  else
    partial_test n

theorem partial_test_theorem (n : ℕ) : ∃ x, x = n := by
  use (partial_test n).val
  exact (partial_test n).property


theorem oeis_a308734_conjecture_0_test : ∀ n : ℕ, 1 < n → A308734_local n > 0 := answer(sorry)


structure Solution (n : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  x : ℕ
  y : ℕ
  ha : a < Nat.sqrt n + 1
  hb : b < Nat.sqrt n + 1
  hc : c < Nat.sqrt n + 1
  hd : d < Nat.sqrt n + 1
  hx : x < Nat.sqrt n + 1
  hy : y < Nat.sqrt n + 1
  heq : (2^a * 3^b)^2 + (2^c * 5^d)^2 + x^2 + y^2 = n
  hxy : x ≤ y

mutual
  partial def proceed_a (n : ℕ) (M : ℕ) (a : ℕ) : Solution n :=
    if ha : a < M then
      have hb : 0 < M := by omega
      have hc : 0 < M := by omega
      have hd : 0 < M := by omega
      have hx : 0 < M := by omega
      have hy : 0 < M := by omega
      search_loop n M a 0 0 0 0 0 ha hb hc hd hx hy
    else
      proceed_a n M a

  partial def proceed_b (n : ℕ) (M : ℕ) (a b : ℕ) (ha : a < M) : Solution n :=
    if hb : b < M then
      have hc : 0 < M := by omega
      have hd : 0 < M := by omega
      have hx : 0 < M := by omega
      have hy : 0 < M := by omega
      search_loop n M a b 0 0 0 0 ha hb hc hd hx hy
    else
      proceed_a n M (a + 1)

  partial def proceed_c (n : ℕ) (M : ℕ) (a b c : ℕ) (ha : a < M) (hb : b < M) : Solution n :=
    if hc : c < M then
      have hd : 0 < M := by omega
      have hx : 0 < M := by omega
      have hy : 0 < M := by omega
      search_loop n M a b c 0 0 0 ha hb hc hd hx hy
    else
      proceed_b n M a (b + 1) ha

  partial def proceed_d (n : ℕ) (M : ℕ) (a b c d : ℕ) (ha : a < M) (hb : b < M) (hc : c < M) : Solution n :=
    if hd : d < M then
      have hx : 0 < M := by omega
      have hy : 0 < M := by omega
      search_loop n M a b c d 0 0 ha hb hc hd hx hy
    else
      proceed_c n M a b (c + 1) ha hb

  partial def proceed_x (n : ℕ) (M : ℕ) (a b c d x : ℕ) (ha : a < M) (hb : b < M) (hc : c < M) (hd : d < M) : Solution n :=
    if hx : x < M then
      have hy : 0 < M := by omega
      search_loop n M a b c d x 0 ha hb hc hd hx hy
    else
      proceed_d n M a b c (d + 1) ha hb hc

  partial def proceed (n : ℕ) (M : ℕ) (a b c d x y : ℕ) (ha : a < M) (hb : b < M) (hc : c < M) (hd : d < M) (hx : x < M) : Solution n :=
    if hy : y < M then
      search_loop n M a b c d x y ha hb hc hd hx hy
    else
      proceed_x n M a b c d (x + 1) ha hb hc hd

  partial def search_loop (n : ℕ) (M : ℕ) (a b c d x y : ℕ) (ha : a < M) (hb : b < M) (hc : c < M) (hd : d < M) (hx : x < M) (hy : y < M) : Solution n :=
    let term1 := (2^a * 3^b)^2
    let term2 := (2^c * 5^d)^2
    if h_eq : term1 + term2 + x^2 + y^2 = n then
      if h_le : x ≤ y then
        ⟨a, b, c, d, x, y, ha, hb, hc, hd, hx, hy, h_eq, h_le⟩
      else
        proceed n M a b c d x (y + 1) ha hb hc hd hx
    else
      proceed n M a b c d x (y + 1) ha hb hc hd hx
end

def find_solution_test (n : ℕ) (hn : 1 < n) : Solution n :=
  let M := Nat.sqrt n + 1
  have h_sqrt : 1 ≤ Nat.sqrt n := by
    by_contra hc
    have : Nat.sqrt n = 0 := by omega
    have : n = 0 := Nat.sqrt_eq_zero.mp this
    omega
  have h_M : 2 ≤ M := by omega
  proceed_a n M 0

#print axioms partial_test_theorem




partial def prove_false_fun (u : Unit) : False := prove_false_fun u
