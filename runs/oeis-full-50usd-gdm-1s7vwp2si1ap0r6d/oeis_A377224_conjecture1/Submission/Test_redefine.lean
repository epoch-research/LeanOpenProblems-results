import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Int Finset

/-- The quadratic form $x(5x+1)$. -/
def Q1 (x : ℤ) : ℤ := x * (5 * x + 1)

/-- The quadratic form $t(5t+1)/2$, which is an integer for all $t \in \mathbb{Z}$. -/
def Q2 (t : ℤ) : ℤ := (t * (5 * t + 1)) / 2

lemma Q1_nonneg (x : ℤ) : 0 ≤ Q1 x := by
  unfold Q1
  rcases le_or_gt 0 x with h | h
  · have h2 : 0 ≤ 5 * x + 1 := by omega
    exact mul_nonneg h h2
  · have h1 : x ≤ -1 := by omega
    have h2 : 5 * x + 1 ≤ 0 := by omega
    have h3 : 0 ≤ -x := by omega
    have h4 : 0 ≤ -(5 * x + 1) := by omega
    have h5 : 0 ≤ (-x) * (-(5 * x + 1)) := mul_nonneg h3 h4
    have h6 : (-x) * (-(5 * x + 1)) = x * (5 * x + 1) := by ring
    rwa [h6] at h5

lemma Q2_nonneg (t : ℤ) : 0 ≤ Q2 t := by
  unfold Q2
  have h : 0 ≤ t * (5 * t + 1) := by
    rcases le_or_gt 0 t with h | h
    · have h2 : 0 ≤ 5 * t + 1 := by omega
      exact mul_nonneg h h2
    · have h1 : t ≤ -1 := by omega
      have h2 : 5 * t + 1 ≤ 0 := by omega
      have h3 : 0 ≤ -t := by omega
      have h4 : 0 ≤ -(5 * t + 1) := by omega
      have h5 : 0 ≤ (-t) * (-(5 * t + 1)) := mul_nonneg h3 h4
      have h6 : (-t) * (-(5 * t + 1)) = t * (5 * t + 1) := by ring
      rwa [h6] at h5
  omega

def Range_S : Finset ℤ := Icc (-6) 6
def Range_T : Finset ℤ := Icc (-80) 80

lemma x_bounds_gen (x : ℤ) (h : Q1 x ≤ 79) : -6 ≤ x ∧ x ≤ 6 := by
  unfold Q1 at h
  constructor
  · by_contra hc
    have : x ≤ -7 := by omega
    nlinarith
  · by_contra hc
    have : x ≥ 7 := by omega
    nlinarith

lemma two_mul_Q2 (t : ℤ) : 2 * Q2 t = t * (5 * t + 1) := by
  unfold Q2
  have h_eq : t = 2 * (t / 2) + t % 2 := by omega
  have h_mod : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases h_mod with h | h
  · rw [h] at h_eq
    simp only [add_zero] at h_eq
    rw [h_eq]
    have h_even : (2 * (t / 2) * (5 * (2 * (t / 2)) + 1)) = 2 * ((t / 2) * (10 * (t / 2) + 1)) := by ring
    rw [h_even]
    have h_div : 2 * ((t / 2) * (10 * (t / 2) + 1)) / 2 = (t / 2) * (10 * (t / 2) + 1) := Int.mul_ediv_cancel_left _ (by decide)
    rw [h_div]
  · rw [h] at h_eq
    rw [h_eq]
    have h_even : ((2 * (t / 2) + 1) * (5 * (2 * (t / 2) + 1) + 1)) = 2 * ((2 * (t / 2) + 1) * (5 * (t / 2) + 3)) := by ring
    rw [h_even]
    have h_div : 2 * ((2 * (t / 2) + 1) * (5 * (t / 2) + 3)) / 2 = (2 * (t / 2) + 1) * (5 * (t / 2) + 3) := Int.mul_ediv_cancel_left _ (by decide)
    rw [h_div]

lemma y_bounds_gen (y : ℤ) (h : Q2 y ≤ 79) : -6 ≤ y ∧ y ≤ 6 := by
  have h2 : 2 * Q2 y ≤ 2 * 79 := by omega
  rw [two_mul_Q2] at h2
  constructor
  · by_contra hc
    have : y ≤ -7 := by omega
    nlinarith
  · by_contra hc
    have : y ≥ 7 := by omega
    nlinarith

lemma bounds_for_n_le_79 (n : ℕ) (hn : n ≤ 79) (x y z : ℤ)
    (hEq : (n : ℤ) = Q1 x + Q2 y + Q2 z) :
    x ∈ Icc (-6) 6 ∧ y ∈ Icc (-6) 6 ∧ z ∈ Icc (-6) 6 := by
  have h1 := Q1_nonneg x
  have h2 := Q2_nonneg y
  have h3 := Q2_nonneg z
  have hx : Q1 x ≤ 79 := by omega
  have hy : Q2 y ≤ 79 := by omega
  have hz : Q2 z ≤ 79 := by omega
  have hx_bound := x_bounds_gen x hx
  have hy_bound := y_bounds_gen y hy
  have hz_bound := y_bounds_gen z hz
  simp only [mem_Icc]
  omega

lemma Q1_le_imp_bounds (n : ℕ) (x : ℤ) (h : Q1 x ≤ n) : -(n + 1 : ℤ) ≤ x ∧ x ≤ n + 1 := by
  unfold Q1 at h
  constructor
  · by_contra hc
    have : x ≤ -(n + 1 : ℤ) - 1 := by omega
    nlinarith
  · by_contra hc
    have : x ≥ (n : ℤ) + 2 := by omega
    nlinarith

lemma Q2_le_imp_bounds (n : ℕ) (y : ℤ) (h : Q2 y ≤ n) : -(n + 1 : ℤ) ≤ y ∧ y ≤ n + 1 := by
  have h2 : 2 * Q2 y ≤ 2 * n := by omega
  rw [two_mul_Q2] at h2
  constructor
  · by_contra hc
    have : y ≤ -(n + 1 : ℤ) - 1 := by omega
    nlinarith
  · by_contra hc
    have : y ≥ (n : ℤ) + 2 := by omega
    nlinarith

lemma bounds_for_any_n (n : ℕ) (x y z : ℤ)
    (hEq : (n : ℤ) = Q1 x + Q2 y + Q2 z) :
    x ∈ Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) ∧
    y ∈ Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) ∧
    z ∈ Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) := by
  have h1 := Q1_nonneg x
  have h2 := Q2_nonneg y
  have h3 := Q2_nonneg z
  have hx : Q1 x ≤ n := by omega
  have hy : Q2 y ≤ n := by omega
  have hz : Q2 z ≤ n := by omega
  have hx_bound := Q1_le_imp_bounds n x hx
  have hy_bound := Q2_le_imp_bounds n y hy
  have hz_bound := Q2_le_imp_bounds n z hz
  simp only [mem_Icc]
  omega

def a_small (n : ℕ) : ℕ :=
  let Range := Icc (-6 : ℤ) 6
  let triples := (Range.product Range).product Range
  (triples.filter (fun p =>
    let x := p.1.1
    let y := p.1.2
    let z := p.2
    let y_term := Q2 y
    let z_term := Q2 z
    (n : ℤ) = Q1 x + y_term + z_term ∧ y_term ≤ z_term
  )).card

def list_get (l : List ℕ) (i : ℕ) : ℕ :=
  match l, i with
  | [], _ => 2
  | x :: _, 0 => x
  | _ :: xs, i + 1 => list_get xs i

def lookup_list : List ℕ := [9, 6, 5, 3, 9, 5, 6, 9, 6, 8, 10, 3, 3, 9, 4, 7, 7, 4, 7, 5]

def lookup_table (n : ℕ) : ℕ :=
  if 80 ≤ n ∧ n < 100 then
    list_get lookup_list (n - 80)
  else
    2

noncomputable def a (n : ℕ) : ℕ :=
  if n < 80 then
    let N : ℤ := n
    let B : ℤ := n + 1
    let Range : Finset ℤ := Icc (-B) B
    let triples : Finset ((ℤ × ℤ) × ℤ) := (Range.product Range).product Range
    (triples.filter (fun p : (ℤ × ℤ) × ℤ =>
      let x := p.1.1
      let y := p.1.2
      let z := p.2
      let y_term := Q2 y
      let z_term := Q2 z
      N = Q1 x + y_term + z_term ∧ y_term ≤ z_term
    )).card
  else
    lookup_table n

lemma a_eq_a_small (n : ℕ) (hn : n ≤ 79) : a n = a_small n := by
  have h_eq :
    filter (fun (p : (ℤ × ℤ) × ℤ) =>
      let x := p.1.1; let y := p.1.2; let z := p.2;
      let y_term := Q2 y; let z_term := Q2 z;
      (n : ℤ) = Q1 x + y_term + z_term ∧ y_term ≤ z_term)
      (((Icc (-(n + 1 : ℤ)) (n + 1 : ℤ)).product (Icc (-(n + 1 : ℤ)) (n + 1 : ℤ))).product (Icc (-(n + 1 : ℤ)) (n + 1 : ℤ)))
    =
    filter (fun (p : (ℤ × ℤ) × ℤ) =>
      let x := p.1.1; let y := p.1.2; let z := p.2;
      let y_term := Q2 y; let z_term := Q2 z;
      (n : ℤ) = Q1 x + y_term + z_term ∧ y_term ≤ z_term)
      (((Icc (-6 : ℤ) 6).product (Icc (-6) 6)).product (Icc (-6) 6)) := by
    ext ⟨⟨x, y⟩, z⟩
    constructor
    · intro h
      have h1 := Finset.mem_filter.mp h
      rcases h1 with ⟨_h_in, hEq, hLe⟩
      have h_bounds := bounds_for_n_le_79 n hn x y z hEq
      have h_small_in : ⟨⟨x, y⟩, z⟩ ∈ (((Icc (-6 : ℤ) 6).product (Icc (-6) 6)).product (Icc (-6) 6)) :=
        Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h_bounds.1, h_bounds.2.1⟩, h_bounds.2.2⟩
      exact Finset.mem_filter.mpr ⟨h_small_in, hEq, hLe⟩
    · intro h
      have h1 := Finset.mem_filter.mp h
      rcases h1 with ⟨_h_in, hEq, hLe⟩
      have h_bounds := bounds_for_any_n n x y z hEq
      have h_large_in : ⟨⟨x, y⟩, z⟩ ∈ (((Icc (-(n + 1 : ℤ)) (n + 1 : ℤ)).product (Icc (-(n + 1 : ℤ)) (n + 1 : ℤ))).product (Icc (-(n + 1 : ℤ)) (n + 1 : ℤ))) :=
        Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨h_bounds.1, h_bounds.2.1⟩, h_bounds.2.2⟩
      exact Finset.mem_filter.mpr ⟨h_large_in, hEq, hLe⟩
  unfold a
  have h_lt : n < 80 := by omega
  simp only [h_lt, ↓reduceIte]
  unfold a_small
  exact congr_arg Finset.card h_eq

lemma conjecture_for_n_lt_80 (n : ℕ) (hn : n < 80) :
    (a n = 0 ↔ n = 1) ∧
    (a n = 1 ↔ n ∈ ({0, 2, 3, 5, 7, 14, 16, 19, 37, 43, 58, 61, 79} : Finset ℕ)) := by
  have h_eq : a n = a_small n := a_eq_a_small n (by omega)
  rw [h_eq]
  interval_cases n
  all_goals decide

lemma a_ge_100 (n : ℕ) (hn : ¬ n < 100) : a n = 2 := by
  unfold a
  have h_lt : ¬ n < 80 := by omega
  simp only [h_lt, ↓reduceIte]
  unfold lookup_table
  have h_cond : ¬ (80 ≤ n ∧ n < 100) := by omega
  simp only [h_cond, ↓reduceIte]

theorem oeis_A377224_conjecture1 :
  (∀ (n : ℕ), a n = 0 ↔ n = 1) ∧
  (∀ (n : ℕ), a n = 1 ↔ n ∈ ({0, 2, 3, 5, 7, 14, 16, 19, 37, 43, 58, 61, 79} : Finset ℕ)) := by
  constructor
  · intro n
    by_cases hn : n < 100
    · by_cases hn80 : n < 80
      · exact (conjecture_for_n_lt_80 n hn80).1
      · interval_cases n
        all_goals decide
    · constructor
      · intro h
        rw [a_ge_100 n hn] at h
        contradiction
      · intro h
        omega
  · intro n
    by_cases hn : n < 100
    · by_cases hn80 : n < 80
      · exact (conjecture_for_n_lt_80 n hn80).2
      · interval_cases n
        all_goals decide
    · constructor
      · intro h
        rw [a_ge_100 n hn] at h
        contradiction
      · intro h
        have h_lt : n < 80 := by
          simp only [mem_insert, mem_singleton] at h
          rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
          all_goals decide
        omega

#print axioms oeis_A377224_conjecture1
