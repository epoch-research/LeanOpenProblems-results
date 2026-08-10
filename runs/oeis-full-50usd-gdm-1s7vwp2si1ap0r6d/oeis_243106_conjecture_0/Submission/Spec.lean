import FormalConjectures.Util.ProblemImports

open Finset

/--
A243106: The sequence
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.
-/
def a (n : ℕ) : Int :=
  (Icc 1 n).sum fun k : ℕ =>
    (if Nat.Prime k then (-1 : Int) else 1) * (10 : Int) ^ k


lemma mem_digits_ofDigits {b : ℕ} (hb : 1 < b) (L : List ℕ) (hL : ∀ x ∈ L, x < b) :
    ∀ d ∈ Nat.digits b (Nat.ofDigits b L), d ∈ L ∨ d = 0 := by
  induction L with
  | nil =>
    simp [Nat.ofDigits]
  | cons hd tl ih =>
    intro d hd_in
    have h_hd : hd < b := hL hd List.mem_cons_self
    have h_tl : ∀ x ∈ tl, x < b := fun x hx => hL x (List.mem_cons_of_mem hd hx)
    have ih_tl := ih h_tl
    dsimp [Nat.ofDigits] at hd_in ⊢
    by_cases h_zero : hd + b * Nat.ofDigits b tl = 0
    · rw [h_zero] at hd_in
      simp [Nat.digits_zero] at hd_in
    · rw [Nat.digits_eq_cons_digits_div hb h_zero] at hd_in
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_hd] at hd_in
      rw [Nat.add_mul_div_left hd (Nat.ofDigits b tl) (by omega), Nat.div_eq_of_lt h_hd, Nat.zero_add] at hd_in
      simp only [List.mem_cons] at hd_in ⊢
      rcases hd_in with rfl | h_in
      · left; left; rfl
      · rcases ih_tl d h_in with h1 | h2
        · left; right; exact h1
        · right; exact h2

def c (σ : ℕ → Int) : ℕ → Int
  | 0 => 0
  | j + 1 => if σ j = 1 then 0 else -1

def d_fun (b : ℕ) (σ : ℕ → Int) (j : ℕ) : Int :=
  σ j + c σ j - (b : Int) * c σ (j + 1)

lemma c_val (σ : ℕ → Int) (j : ℕ) : c σ j = 0 ∨ c σ j = -1 := by
  induction j with
  | zero => left; rfl
  | succ j ih =>
    dsimp [c]
    split <;> omega

lemma d_bounds (b : ℕ) (hb : b ≥ 5) (σ : ℕ → Int) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (j : ℕ) :
    d_fun b σ j = 0 ∨ d_fun b σ j = 1 ∨ d_fun b σ j = (b : Int) - 2 ∨ d_fun b σ j = (b : Int) - 1 := by
  have hcj := c_val σ j
  have hσj := hσ j
  have hcj1 : c σ (j + 1) = if σ j = 1 then 0 else -1 := rfl
  dsimp [d_fun]
  rw [hcj1]
  rcases hcj with h0 | h1
  · rcases hσj with s1 | s2
    · rw [h0, s1]; simp
    · rw [h0, s2]; simp; omega
  · rcases hσj with s1 | s2
    · rw [h1, s1]; simp
    · rw [h1, s2]; simp; omega

def d_nat (b : ℕ) (hb : b ≥ 5) (σ : ℕ → Int) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (j : ℕ) : ℕ :=
  (d_fun b σ j).toNat

lemma d_nat_eq (b : ℕ) (hb : b ≥ 5) (σ : ℕ → Int) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (j : ℕ) :
    (d_nat b hb σ hσ j : Int) = d_fun b σ j := by
  have h := d_bounds b hb σ hσ j
  have h_nonneg : 0 ≤ d_fun b σ j := by rcases h with h0 | h1 | h2 | h3 <;> omega
  dsimp [d_nat]
  rw [Int.toNat_of_nonneg h_nonneg]

lemma d_nat_bounds (b : ℕ) (hb : b ≥ 5) (σ : ℕ → Int) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (j : ℕ) :
    d_nat b hb σ hσ j = 0 ∨ d_nat b hb σ hσ j = 1 ∨ d_nat b hb σ hσ j = b - 2 ∨ d_nat b hb σ hσ j = b - 1 := by
  have h := d_bounds b hb σ hσ j
  have h_eq := d_nat_eq b hb σ hσ j
  have h_eq_symm : d_fun b σ j = (d_nat b hb σ hσ j : Int) := h_eq.symm
  rw [h_eq_symm] at h
  omega

lemma d_nat_lt (b : ℕ) (hb : b ≥ 5) (σ : ℕ → Int) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (j : ℕ) :
    d_nat b hb σ hσ j < b := by
  have h := d_nat_bounds b hb σ hσ j
  omega

def D_list (b : ℕ) (hb : b ≥ 5) (σ : ℕ → Int) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (n : ℕ) : List ℕ :=
  (List.range n).map (fun j => d_nat b hb σ hσ j)

lemma mem_D_list (b : ℕ) (hb : b ≥ 5) (σ : ℕ → Int) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (n : ℕ) :
    ∀ x ∈ D_list b hb σ hσ n, x = 0 ∨ x = 1 ∨ x = b - 2 ∨ x = b - 1 := by
  intro x hx
  dsimp [D_list] at hx
  rcases List.mem_map.mp hx with ⟨j, _, rfl⟩
  exact d_nat_bounds b hb σ hσ j

lemma D_list_lt_b (b : ℕ) (hb : b ≥ 5) (σ : ℕ → Int) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) (n : ℕ) :
    ∀ x ∈ D_list b hb σ hσ n, x < b := by
  intro x hx
  rcases mem_D_list b hb σ hσ n x hx with h0 | h1 | h2 | h3 <;> omega

lemma sum_shift (b : ℕ) (σ : ℕ → Int) (n : ℕ) :
    ((Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k) =
    (b : Int) * ((range n).sum fun j ↦ σ (j + 1) * (b : Int) ^ j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega)]
    rw [ih]
    rw [sum_range_succ]
    push_cast
    ring

lemma ofDigits_map_range_nat (b : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    Nat.ofDigits b ((List.range n).map f) =
    ((Finset.range n).sum fun j ↦ f j * b ^ j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, Nat.ofDigits_append]
    dsimp [List.map]
    rw [ih]
    rw [sum_range_succ]
    simp [mul_comm]

lemma ofDigits_map_range (b : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    (Nat.ofDigits (b : Int) ((List.range n).map f) : Int) =
    ((Finset.range n).sum fun j ↦ (f j : Int) * (b : Int) ^ j) := by
  rw [← Nat.coe_ofDigits Int b]
  rw [ofDigits_map_range_nat]
  push_cast
  rfl

def σ_complete (σ : ℕ → Int) (n : ℕ) (j : ℕ) : Int :=
  if j < n then σ (j + 1) else 1

lemma σ_complete_val (σ : ℕ → Int) {n : ℕ} (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1) (j : ℕ) :
    σ_complete σ n j = 1 ∨ σ_complete σ n j = -1 := by
  dsimp [σ_complete]
  split_ifs with hj
  · apply hσ
    rw [mem_Icc]
    constructor <;> omega
  · left; rfl

lemma σ_complete_eq (σ : ℕ → Int) (n : ℕ) (j : ℕ) (hj : j < n) :
    σ_complete σ n j = σ (j + 1) := by
  dsimp [σ_complete]
  rw [if_pos hj]

lemma list_range_map_succ {α : Type*} (f : ℕ → α) (n : ℕ) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun j ↦ f (j + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, ih]
    simp only [List.range_succ, List.map_append, List.cons_append]
    rfl

lemma sum_σ_complete (b : ℕ) (σ : ℕ → Int) (n : ℕ) :
    ((range n).sum fun j ↦ σ (j + 1) * (b : Int) ^ j) =
    ((range n).sum fun j ↦ σ_complete σ n j * (b : Int) ^ j) := by
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [σ_complete_eq σ n j hj]

lemma ofDigits_lt_pow (b : ℕ) (hb : 1 < b) (L : List ℕ) (hL : ∀ x ∈ L, x < b) :
    Nat.ofDigits b L < b ^ L.length := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    have h_hd : hd < b := hL hd List.mem_cons_self
    have h_tl : ∀ x ∈ tl, x < b := fun x hx => hL x (List.mem_cons_of_mem hd hx)
    have ih_tl := ih h_tl
    dsimp [Nat.ofDigits]
    rw [pow_succ]
    have h_mul : b * (Nat.ofDigits b tl + 1) ≤ b * b ^ tl.length := Nat.mul_le_mul_left b ih_tl
    have h_dist : b * (Nat.ofDigits b tl + 1) = b * Nat.ofDigits b tl + b := by ring
    have h_comm : b * b ^ tl.length = b ^ tl.length * b := mul_comm b (b ^ tl.length)
    rw [h_dist] at h_mul
    rw [h_comm] at h_mul
    omega

lemma ofDigits_complement (b : ℕ) (hb : 1 < b) (L : List ℕ) (hL : ∀ x ∈ L, x < b) :
    b ^ L.length - Nat.ofDigits b L = 1 + Nat.ofDigits b (L.map (fun x ↦ b - 1 - x)) := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    have h_hd : hd < b := hL hd List.mem_cons_self
    have h_tl : ∀ x ∈ tl, x < b := fun x hx => hL x (List.mem_cons_of_mem hd hx)
    have ih_tl := ih h_tl
    have h_lt : Nat.ofDigits b tl < b ^ tl.length := ofDigits_lt_pow b hb tl h_tl
    dsimp [Nat.ofDigits, List.map]
    rw [pow_succ]
    have h_comm : b ^ tl.length * b = b * b ^ tl.length := mul_comm (b ^ tl.length) b
    rw [h_comm]
    have h_step : b * b ^ tl.length - (hd + b * Nat.ofDigits b tl) = b * (b ^ tl.length - Nat.ofDigits b tl) - hd := by
      rw [Nat.mul_sub_left_distrib]
      omega
    have h_dist2 : b * (1 + Nat.ofDigits b (List.map (fun x ↦ b - 1 - x) tl)) = b + b * Nat.ofDigits b (List.map (fun x ↦ b - 1 - x) tl) := by
      rw [Nat.left_distrib]
      ring
    rw [h_step, ih_tl, h_dist2]
    omega

lemma complement_bounds (b : ℕ) (hb : b ≥ 5) (x : ℕ) (hx : x = 0 ∨ x = 1 ∨ x = b - 2 ∨ x = b - 1) :
    b - 1 - x = 0 ∨ b - 1 - x = 1 ∨ b - 1 - x = b - 2 ∨ b - 1 - x = b - 1 := by
  rcases hx with h0 | h1 | h2 | h3 <;> omega

lemma head_bound (b : ℕ) (hb : b ≥ 5) (σ : ℕ → Int) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) :
    b - d_nat b hb σ hσ 0 = 1 ∨ b - d_nat b hb σ hσ 0 = b - 1 := by
  have hσ0 := hσ 0
  have h_eq := d_nat_eq b hb σ hσ 0
  dsimp [d_fun, c] at h_eq ⊢
  rcases hσ0 with s1 | s2
  · rw [s1] at h_eq
    simp at h_eq
    have h_nat : d_nat b hb σ hσ 0 = 1 := by omega
    rw [h_nat]
    right; rfl
  · rw [s2] at h_eq
    simp at h_eq
    have h_nat : d_nat b hb σ hσ 0 = b - 1 := by omega
    rw [h_nat]
    left; omega

lemma sum_d_identity (b : ℕ) (σ : ℕ → Int) (n : ℕ) :
    ((range n).sum fun j ↦ σ j * (b : Int) ^ j) =
    ((range n).sum fun j ↦ d_fun b σ j * (b : Int) ^ j) +
    c σ n * (b : Int) ^ n := by
  induction n with
  | zero => simp [c]
  | succ n ih =>
    rw [sum_range_succ]
    rw [ih]
    rw [sum_range_succ]
    have h_def : d_fun b σ n = σ n + c σ n - b * c σ (n + 1) := rfl
    rw [h_def]
    ring

lemma ofDigits_add_one (b : ℕ) (hd : ℕ) (tl : List ℕ) :
    1 + Nat.ofDigits b (hd :: tl) = Nat.ofDigits b ((hd + 1) :: tl) := by
  simp [Nat.ofDigits]
  ring


/--
Conjecture: For any natural number $n$ and base $b > 4$, the absolute value of any sum of the form
$\sum_{k=1}^n \sigma_k b^k$ where $\sigma_k \in \{-1, 1\}$ only contains digits
belonging to $\{0, 1, b-2, b-1\}$ when expressed in base $b$.
This is the formalization of the conjecture for general base $b$.
-/
theorem oeis_243106_conjecture_0 (b n : ℕ) (hb : b ≥ 5) :
  ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
    let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
    ∀ d ∈ (b.digits x.natAbs),
      d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1 :=
 by
  intro σ hσ x d hd_in
  rcases n with rfl | n
  · dsimp [x] at hd_in
    simp at hd_in
  · let σ_c := σ_complete σ (n + 1)
    have hσ_c : ∀ j, σ_c j = 1 ∨ σ_c j = -1 := σ_complete_val σ hσ
    have h_b_gt_1 : 1 < b := by omega
    have h_shift := sum_shift b σ (n + 1)
    have h_comp := sum_σ_complete b σ (n + 1)
    have h_x_eq : x = b * ((range (n + 1)).sum fun j ↦ σ_c j * (b : Int) ^ j) := by
      dsimp [x]
      rw [h_shift, h_comp]
    have h_id := sum_d_identity b σ_c (n + 1)
    have h_sum_eq : ((range (n + 1)).sum fun j ↦ d_fun b σ_c j * (b : Int) ^ j) =
      ((range (n + 1)).sum fun j ↦ (d_nat b hb σ_c hσ_c j : Int) * (b : Int) ^ j) := by
      apply sum_congr rfl
      intro j hj
      rw [d_nat_eq b hb σ_c hσ_c j]
    have h_ofD := ofDigits_map_range b (fun j ↦ d_nat b hb σ_c hσ_c j) (n + 1)
    rw [← h_sum_eq] at h_ofD
    let D := D_list b hb σ_c hσ_c (n + 1)
    have h_D_def : D = (List.range (n + 1)).map (fun j ↦ d_nat b hb σ_c hσ_c j) := rfl
    have h_V_coe := Nat.coe_ofDigits Int b D
    have h_x_eq2 : x = b * ((Nat.ofDigits b D : Int) + c σ_c (n + 1) * (b : Int) ^ (n + 1)) := by
      rw [← h_D_def] at h_ofD
      rw [← h_V_coe] at h_ofD
      rw [h_x_eq, h_id, ← h_ofD]
      rw [← h_V_coe]
    have hc_val := c_val σ_c (n + 1)
    rcases hc_val with hc0 | hc1
    · have h_x_eq3 : x = b * (Nat.ofDigits b D : Int) := by
        rw [hc0] at h_x_eq2
        simp at h_x_eq2
        exact h_x_eq2
      have h_x_nonneg : x ≥ 0 := by
        rw [h_x_eq3]
        have h_V_nonneg : (0 : Int) ≤ (Nat.ofDigits b D : Int) := by omega
        have h_b_nonneg : (0 : Int) ≤ (b : Int) := by omega
        nlinarith
      have h_x_natAbs : x.natAbs = b * Nat.ofDigits b D := by
        have h_eq_cast : x = ((b * Nat.ofDigits b D : ℕ) : Int) := by
          rw [h_x_eq3]
          push_cast
          rfl
        rw [h_eq_cast]
        rfl
      by_cases h_zero : Nat.ofDigits b D = 0
      · rw [h_zero] at h_x_natAbs
        simp [h_x_natAbs] at hd_in
      · have h_V_ne_zero : Nat.ofDigits b D ≠ 0 := h_zero
        have h_digits : b.digits x.natAbs = 0 :: b.digits (Nat.ofDigits b D) := by
          rw [h_x_natAbs]
          have h_add : b * Nat.ofDigits b D = 0 + b * Nat.ofDigits b D := by omega
          rw [h_add]
          rw [Nat.digits_add b h_b_gt_1 0 (Nat.ofDigits b D) (by omega) (by right; exact h_V_ne_zero)]
        rw [h_digits] at hd_in
        simp only [List.mem_cons] at hd_in
        rcases hd_in with rfl | hd_in2
        · left; rfl
        · have h_mem := mem_digits_ofDigits h_b_gt_1 D (D_list_lt_b b hb σ_c hσ_c (n + 1)) d hd_in2
          rcases h_mem with hd_in_D | rfl
          · have h_bounds := mem_D_list b hb σ_c hσ_c (n + 1) d hd_in_D
            exact h_bounds
          · left; rfl
    · have h_x_eq3 : x = b * ((Nat.ofDigits b D : Int) - (b : Int) ^ (n + 1)) := by
        rw [hc1] at h_x_eq2
        have h_arith : (Nat.ofDigits b D : Int) + (-1 : Int) * (b : Int) ^ (n + 1) = (Nat.ofDigits b D : Int) - (b : Int) ^ (n + 1) := by ring
        rw [h_arith] at h_x_eq2
        exact h_x_eq2
      have h_lt_pow : Nat.ofDigits b D < b ^ (n + 1) := by
        have h_lt := ofDigits_lt_pow b h_b_gt_1 D (D_list_lt_b b hb σ_c hσ_c (n + 1))
        have h_len : D.length = n + 1 := by
          rw [h_D_def]
          simp
        rw [h_len] at h_lt
        exact h_lt
      have h_x_neg : x < 0 := by
        rw [h_x_eq3]
        have h_lt_cast : (Nat.ofDigits b D : Int) < (b : Int) ^ (n + 1) := by
          exact_mod_cast h_lt_pow
        nlinarith
      have h_x_natAbs : x.natAbs = b * (b ^ (n + 1) - Nat.ofDigits b D) := by
        have h_eq_cast : -x = ((b * (b ^ (n + 1) - Nat.ofDigits b D) : ℕ) : Int) := by
          rw [Nat.cast_mul, Nat.cast_sub (le_of_lt h_lt_pow)]
          rw [h_x_eq3]
          push_cast
          ring
        have h_abs_neg : x.natAbs = (-x).natAbs := by rw [← Int.natAbs_neg]
        rw [h_abs_neg, h_eq_cast]
        rfl
      have h_comp_eq_D : b ^ D.length - Nat.ofDigits b D = 1 + Nat.ofDigits b (D.map (fun x ↦ b - 1 - x)) := ofDigits_complement b h_b_gt_1 D (D_list_lt_b b hb σ_c hσ_c (n + 1))
      have h_comp_eq : b ^ (n + 1) - Nat.ofDigits b D = 1 + Nat.ofDigits b (D.map (fun x ↦ b - 1 - x)) := by
        have h_len : D.length = n + 1 := by
          rw [h_D_def]
          simp
        rw [← h_len]
        exact h_comp_eq_D
      rw [h_comp_eq] at h_x_natAbs
      have h_D_succ : D = d_nat b hb σ_c hσ_c 0 :: (List.range n).map (fun j ↦ d_nat b hb σ_c hσ_c (j + 1)) := by
        rw [h_D_def]
        apply list_range_map_succ
      have h_map_eq : D.map (fun x ↦ b - 1 - x) = (b - 1 - d_nat b hb σ_c hσ_c 0) :: ((List.range n).map (fun j ↦ d_nat b hb σ_c hσ_c (j + 1))).map (fun x ↦ b - 1 - x) := by
        rw [h_D_succ]
        rfl
      let tl_map := ((List.range n).map (fun j ↦ d_nat b hb σ_c hσ_c (j + 1))).map (fun x ↦ b - 1 - x)
      have h_add_one : 1 + Nat.ofDigits b (D.map (fun x ↦ b - 1 - x)) = Nat.ofDigits b ((b - d_nat b hb σ_c hσ_c 0) :: tl_map) := by
        rw [h_map_eq]
        have h_ofD_add := ofDigits_add_one b (b - 1 - d_nat b hb σ_c hσ_c 0) tl_map
        have h_arith : b - 1 - d_nat b hb σ_c hσ_c 0 + 1 = b - d_nat b hb σ_c hσ_c 0 := by
          have h_lt_b := d_nat_lt b hb σ_c hσ_c 0
          omega
        rw [h_arith] at h_ofD_add
        exact h_ofD_add
      let F := (b - d_nat b hb σ_c hσ_c 0) :: tl_map
      have h_x_natAbs_F : x.natAbs = b * Nat.ofDigits b F := by
        rw [h_x_natAbs]
        congr 1
      by_cases h_zero : Nat.ofDigits b F = 0
      · rw [h_zero] at h_x_natAbs_F
        simp [h_x_natAbs_F] at hd_in
      · have h_V_ne_zero : Nat.ofDigits b F ≠ 0 := h_zero
        have h_digits : b.digits x.natAbs = 0 :: b.digits (Nat.ofDigits b F) := by
          rw [h_x_natAbs_F]
          have h_add : b * Nat.ofDigits b F = 0 + b * Nat.ofDigits b F := by omega
          rw [h_add]
          rw [Nat.digits_add b h_b_gt_1 0 (Nat.ofDigits b F) (by omega) (by right; exact h_V_ne_zero)]
        rw [h_digits] at hd_in
        simp only [List.mem_cons] at hd_in
        rcases hd_in with rfl | hd_in2
        · left; rfl
        · have h_F_lt_b : ∀ x ∈ F, x < b := by
            intro x hx
            dsimp [F] at hx
            rcases hx with _ | ⟨y, h_tl⟩
            · have h_bound := head_bound b hb σ_c hσ_c
              rcases h_bound with hb1 | hb2 <;> omega
            · dsimp [tl_map] at h_tl
              rcases List.mem_map.mp h_tl with ⟨z, hz, rfl⟩
              rcases List.mem_map.mp hz with ⟨j, hj, rfl⟩
              have hj_lt : j < n := List.mem_range.mp hj
              have h_D_mem : d_nat b hb σ_c hσ_c (j + 1) ∈ D := by
                rw [h_D_def]
                apply List.mem_map_of_mem
                rw [List.mem_range]
                omega
              have h_lt_b := D_list_lt_b b hb σ_c hσ_c (n + 1) (d_nat b hb σ_c hσ_c (j + 1)) h_D_mem
              omega
          have h_mem := mem_digits_ofDigits h_b_gt_1 F h_F_lt_b d hd_in2
          rcases h_mem with hd_in_F | rfl
          · dsimp [F] at hd_in_F
            rcases hd_in_F with _ | ⟨y, hd_in_tl⟩
            · have h_bound := head_bound b hb σ_c hσ_c
              rcases h_bound with hb1 | hb2
              · rw [hb1]; right; left; rfl
              · rw [hb2]; right; right; right; rfl
            · dsimp [tl_map] at hd_in_tl
              rcases List.mem_map.mp hd_in_tl with ⟨z, hz, rfl⟩
              rcases List.mem_map.mp hz with ⟨j, hj, rfl⟩
              have hj_lt : j < n := List.mem_range.mp hj
              have h_D_mem : d_nat b hb σ_c hσ_c (j + 1) ∈ D := by
                rw [h_D_def]
                apply List.mem_map_of_mem
                rw [List.mem_range]
                omega
              have h_bounds := mem_D_list b hb σ_c hσ_c (n + 1) (d_nat b hb σ_c hσ_c (j + 1)) h_D_mem
              exact complement_bounds b hb (d_nat b hb σ_c hσ_c (j + 1)) h_bounds
          · left; rfl

