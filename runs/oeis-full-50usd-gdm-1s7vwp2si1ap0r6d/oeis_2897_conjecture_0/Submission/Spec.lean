import FormalConjectures.Util.ProblemImports

open Nat MvPolynomial BigOperators

/--
The sequence $a(n)$ is defined by $a(n) = \binom{2n}{n}^3$.
We use `Nat.choose (2 * n) n` for the central binomial coefficient.
-/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3

-- Define the set of variables {x, y, z}
abbrev Vars := Fin 3

/--
The finsupp corresponding to the monomial $x^n y^n z^n$.
This is the map $\lambda i. n$. Since `Fin 3` is finite, this function is finitely supported.
We mark it noncomputable as it builds a mathematical object defined in terms of finite support.
-/
noncomputable def xyz_pow_n (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)

-- The polynomial ring over ℤ with 3 variables
local notation "P" => MvPolynomial Vars ℤ

/--
The polynomial $P_n(X, Y, Z) = (1 + X + Y + Z)^{2n} (1 + X + Y - Z)^n (1 + X - Y + Z)^n$.
We identify $X_0, X_1, X_2$ with $X, Y, Z$.
We mark it noncomputable due to dependencies in the polynomial ring structure.
-/
noncomputable def P_n (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n

noncomputable def U : P := 1 + X 0
noncomputable def V : P := X 1 + X 2
noncomputable def W : P := X 1 - X 2

theorem P_n_decomp (n : ℕ) :
  P_n n = (U + V) ^ (2 * n) * (U ^ 2 - W ^ 2) ^ n := by
  dsimp [P_n, U, V, W]
  have hb : (1 + X 0 + X 1 + X 2 : P) = (1 + X 0 + (X 1 + X 2) : P) := by ring
  rw [hb]
  have h1 : ((1 + X 0 + (X 1 + X 2) : P) ^ (2 * n)) = (((1 + X 0 + (X 1 + X 2) : P) ^ 2) ^ n) := by
    rw [← pow_mul]
  rw [h1]
  rw [mul_assoc, ← mul_pow, ← mul_pow]
  rw [← mul_pow]
  congr 1
  ring

theorem P_n_expand (n : ℕ) :
  P_n n = ∑ k ∈ Finset.range (2 * n + 1), ∑ j ∈ Finset.range (n + 1),
    (U ^ (2 * n - k + (2 * n - 2 * j)) * V ^ k * W ^ (2 * j) * (C ((-1)^j * ((2*n).choose k * n.choose j : ℤ)))) := by
  rw [P_n_decomp]
  have h1 : (U + V) ^ (2 * n) = ∑ k ∈ Finset.range (2 * n + 1), U ^ (2 * n - k) * V ^ k * ↑((2 * n).choose k) := by
    rw [add_comm U V]
    rw [add_pow V U (2 * n)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have h_neg : ∀ j, (- (W ^ 2)) ^ j = C ((-1 : ℤ)^j) * W ^ (2 * j) := by
    intro j
    rw [neg_pow (W ^ 2) j]
    rw [← pow_mul]
    simp
  have h2 : (U ^ 2 - W ^ 2) ^ n = ∑ j ∈ Finset.range (n + 1), U ^ (2 * n - 2 * j) * W ^ (2 * j) * C ((-1)^j * (n.choose j : ℤ)) := by
    have h_add : U ^ 2 - W ^ 2 = - (W ^ 2) + U ^ 2 := by ring
    rw [h_add]
    rw [add_pow (- (W ^ 2)) (U ^ 2) n]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [h_neg j]
    have h_pow_mul : (U ^ 2) ^ (n - j) = U ^ (2 * (n - j)) := by
      rw [← pow_mul]
    rw [h_pow_mul]
    have hj_le : j ≤ n := Finset.mem_range_succ_iff.mp hj
    have h_sub : 2 * (n - j) = 2 * n - 2 * j := by
      omega
    rw [h_sub]
    have hc : (n.choose j : P) = C (n.choose j : ℤ) := by
      simp
    rw [hc]
    rw [map_mul]
    ring
  rw [h1, h2]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h_ck : (↑((2 * n).choose k) : P) = C ((2 * n).choose k : ℤ) := by simp
  rw [h_ck]
  rw [map_mul, map_mul, map_mul]
  ring

def is_var0 (p : P) : Prop :=
  ∀ m ∈ p.support, m 1 = 0 ∧ m 2 = 0

def is_var12 (p : P) : Prop :=
  ∀ m ∈ p.support, m 0 = 0

theorem coeff_mul_disjoint {p q : P} (hp : is_var0 p) (hq : is_var12 q) (n : ℕ) :
  coeff (xyz_pow_n n) (p * q) = coeff (Finsupp.single 0 n) p * coeff (Finsupp.single 1 n + Finsupp.single 2 n) q := by
  rw [coeff_mul]
  have h_sum : Finsupp.single 0 n + (Finsupp.single 1 n + Finsupp.single 2 n) = xyz_pow_n n := by
    ext i
    fin_cases i <;> simp [xyz_pow_n, Finsupp.ofSupportFinite_coe]
  have h_uniq : ∀ x ∈ Finset.antidiagonal (xyz_pow_n n), coeff x.1 p * coeff x.2 q ≠ 0 → x = (Finsupp.single 0 n, Finsupp.single 1 n + Finsupp.single 2 n) := by
    rintro ⟨x1, x2⟩ h_mem h_ne
    rw [Finset.mem_antidiagonal] at h_mem
    have h_ne1 : coeff x1 p ≠ 0 := fun h => h_ne (by simp [h])
    have h_ne2 : coeff x2 q ≠ 0 := fun h => h_ne (by simp [h])
    have h1 : x1 ∈ p.support := mem_support_iff.mpr h_ne1
    have h2 : x2 ∈ q.support := mem_support_iff.mpr h_ne2
    have hp1 := hp x1 h1
    have hq1 := hq x2 h2
    have hx1 : x1 = Finsupp.single 0 n := by
      ext i
      fin_cases i
      · have h_eq := congr_arg (fun f : Vars →₀ ℕ => f 0) h_mem
        simp [xyz_pow_n, Finsupp.ofSupportFinite_coe, Finsupp.coe_add] at *
        have h_x2_0 : x2 0 = 0 := hq1
        rw [h_x2_0] at h_eq
        omega
      · simp [hp1.1]
      · simp [hp1.2]
    have hx2 : x2 = Finsupp.single 1 n + Finsupp.single 2 n := by
      ext i
      fin_cases i
      · simp [hq1, Finsupp.coe_add]
      · have h_eq := congr_arg (fun f : Vars →₀ ℕ => f 1) h_mem
        simp [xyz_pow_n, Finsupp.ofSupportFinite_coe, Finsupp.coe_add] at *
        rw [hx1] at h_eq
        simp at h_eq
        omega
      · have h_eq := congr_arg (fun f : Vars →₀ ℕ => f 2) h_mem
        simp [xyz_pow_n, Finsupp.ofSupportFinite_coe, Finsupp.coe_add] at *
        rw [hx1] at h_eq
        simp at h_eq
        omega
    rw [hx1, hx2]
  have hi0 : (Finsupp.single 0 n, Finsupp.single 1 n + Finsupp.single 2 n) ∈ Finset.antidiagonal (xyz_pow_n n) := by
    rw [Finset.mem_antidiagonal]
    exact h_sum
  rw [Finset.sum_eq_single (Finsupp.single 0 n, Finsupp.single 1 n + Finsupp.single 2 n)]
  · rintro x h_mem h_ne
    by_contra h_ne_zero
    have h_eq : x = (Finsupp.single 0 n, Finsupp.single 1 n + Finsupp.single 2 n) := h_uniq x h_mem h_ne_zero
    exact h_ne h_eq
  · intro h_not_mem
    exact False.elim (h_not_mem hi0)


theorem is_var0_C (c : ℤ) : is_var0 (C c) := by
  intro m hm
  rw [MvPolynomial.support_C] at hm
  split_ifs at hm with h
  · simp at hm
  · simp at hm
    subst hm
    simp

theorem is_var0_X0 : is_var0 (X 0 : P) := by
  intro m hm
  rw [MvPolynomial.support_X] at hm
  simp at hm
  subst hm
  simp

theorem is_var0_add {p q : P} (hp : is_var0 p) (hq : is_var0 q) : is_var0 (p + q) := by
  intro m hm
  have h_sup : (p + q).support ⊆ p.support ∪ q.support := MvPolynomial.support_add
  have hm' := h_sup hm
  rw [Finset.mem_union] at hm'
  cases hm' with
  | inl h => exact hp m h
  | inr h => exact hq m h

theorem is_var0_mul {p q : P} (hp : is_var0 p) (hq : is_var0 q) : is_var0 (p * q) := by
  intro m hm
  have h_sup := MvPolynomial.support_mul p q
  have hm' := h_sup hm
  rw [Finset.mem_add] at hm'
  rcases hm' with ⟨y, hy, z, hz, rfl⟩
  have hpy := hp y hy
  have hqz := hq z hz
  simp [hpy, hqz]

theorem is_var0_pow {p : P} (hp : is_var0 p) (n : ℕ) : is_var0 (p ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact is_var0_C 1
  | succ n ih =>
    rw [pow_succ]
    exact is_var0_mul ih hp

theorem is_var12_C (c : ℤ) : is_var12 (C c) := by
  intro m hm
  rw [MvPolynomial.support_C] at hm
  split_ifs at hm with h
  · simp at hm
  · simp at hm
    subst hm
    simp

theorem is_var12_X (i : Vars) (hi : i ≠ 0) : is_var12 (X i : P) := by
  intro m hm
  rw [MvPolynomial.support_X] at hm
  simp at hm
  subst hm
  simp [hi]

theorem is_var12_add {p q : P} (hp : is_var12 p) (hq : is_var12 q) : is_var12 (p + q) := by
  intro m hm
  have h_sup : (p + q).support ⊆ p.support ∪ q.support := MvPolynomial.support_add
  have hm' := h_sup hm
  rw [Finset.mem_union] at hm'
  cases hm' with
  | inl h => exact hp m h
  | inr h => exact hq m h

theorem is_var12_mul {p q : P} (hp : is_var12 p) (hq : is_var12 q) : is_var12 (p * q) := by
  intro m hm
  have h_sup := MvPolynomial.support_mul p q
  have hm' := h_sup hm
  rw [Finset.mem_add] at hm'
  rcases hm' with ⟨y, hy, z, hz, rfl⟩
  have hpy := hp y hy
  have hqz := hq z hz
  simp [hpy, hqz]

theorem is_var12_pow {p : P} (hp : is_var12 p) (n : ℕ) : is_var12 (p ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact is_var12_C 1
  | succ n ih =>
    rw [pow_succ]
    exact is_var12_mul ih hp

theorem is_var12_neg {p : P} (hp : is_var12 p) : is_var12 (-p) := by
  intro m hm
  rw [MvPolynomial.support_neg] at hm
  exact hp m hm

theorem is_var12_sub {p q : P} (hp : is_var12 p) (hq : is_var12 q) : is_var12 (p - q) := by
  rw [sub_eq_add_neg]
  exact is_var12_add hp (is_var12_neg hq)

theorem is_var12_V : is_var12 V := by
  dsimp [V]
  apply is_var12_add
  · apply is_var12_X; decide
  · apply is_var12_X; decide

theorem is_var12_W : is_var12 W := by
  dsimp [W]
  apply is_var12_sub
  · apply is_var12_X; decide
  · apply is_var12_X; decide

theorem IsHomogeneous.neg {p : P} {n : ℕ} (hp : IsHomogeneous p n) : IsHomogeneous (-p) n := by
  have h_neg : -p = C (-1) * p := by
    rw [map_neg, map_one, neg_mul, one_mul]
  rw [h_neg]
  have h_mul := IsHomogeneous.mul (isHomogeneous_C _ (-1)) hp
  rw [zero_add] at h_mul
  exact h_mul

theorem IsHomogeneous.sub {p q : P} {n : ℕ} (hp : IsHomogeneous p n) (hq : IsHomogeneous q n) : IsHomogeneous (p - q) n := by
  rw [sub_eq_add_neg]
  exact IsHomogeneous.add hp (IsHomogeneous.neg hq)

theorem isHomogeneous_V : IsHomogeneous (V : P) 1 := by
  dsimp [V]
  apply IsHomogeneous.add
  · apply isHomogeneous_X
  · apply isHomogeneous_X

theorem isHomogeneous_W : IsHomogeneous (W : P) 1 := by
  dsimp [W]
  apply IsHomogeneous.sub
  · apply isHomogeneous_X
  · apply isHomogeneous_X

theorem isHomogeneous_VW (k j : ℕ) : IsHomogeneous (V ^ k * W ^ (2 * j) : P) (k + 2 * j) := by
  apply IsHomogeneous.mul
  · have h_pow := IsHomogeneous.pow isHomogeneous_V k
    rw [one_mul] at h_pow
    exact h_pow
  · have h_pow := IsHomogeneous.pow isHomogeneous_W (2 * j)
    rw [one_mul] at h_pow
    exact h_pow

theorem degree_single_sum (n : ℕ) :
  Finsupp.degree (Finsupp.single (1 : Vars) n + Finsupp.single (2 : Vars) n) = 2 * n := by
  rw [map_add]
  rw [Finsupp.degree_single, Finsupp.degree_single]
  omega

theorem coeff_VW_eq_zero (n k j : ℕ) (h : k + 2 * j ≠ 2 * n) :
  coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ k * W ^ (2 * j) : P) = 0 := by
  apply IsHomogeneous.coeff_eq_zero (isHomogeneous_VW k j)
  rw [degree_single_sum]
  exact Ne.symm h

theorem is_var0_U : is_var0 U := by
  dsimp [U]
  apply is_var0_add
  · apply is_var0_C
  · apply is_var0_X0

theorem coeff_U_pow (A n : ℕ) (h : n ≤ A) :
  coeff (Finsupp.single (0 : Vars) n) (U ^ A) = A.choose n := by
  dsimp [U]
  rw [add_comm]
  rw [add_pow (X 0) 1 A]
  have h_one : ∀ i, (1 : P) ^ (A - i) = 1 := fun i => one_pow (A - i)
  have h_sum : (∑ i ∈ Finset.range (A + 1), X 0 ^ i * 1 ^ (A - i) * (A.choose i : P)) =
               ∑ i ∈ Finset.range (A + 1), C (A.choose i : ℤ) * X 0 ^ i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_one i, mul_one]
    have hc : (A.choose i : P) = C (A.choose i : ℤ) := by simp
    rw [hc]
    ring
  rw [h_sum]
  rw [coeff_sum]
  have hn_mem : n ∈ Finset.range (A + 1) := by
    rw [Finset.mem_range]
    omega
  rw [Finset.sum_eq_single n]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro i hi hi_ne
    rw [coeff_C_mul, coeff_X_pow]
    split_ifs with h_eq
    · have h_eq_i : i = n := by
        have h_eval := congr_arg (fun f : Vars →₀ ℕ => f 0) h_eq
        simp at h_eval
        exact h_eval
      exact False.elim (hi_ne h_eq_i)
    · rw [mul_zero]
  · intro hn_not
    exact False.elim (hn_not hn_mem)


theorem term_eq_zero (n j k : ℕ) (hk : k ≠ 2 * n - 2 * j) :
  coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ k * W ^ (2 * j) * C ((-1)^j * ((2*n).choose k * n.choose j : ℤ))) = 0 := by
  have h_comm : V ^ k * W ^ (2 * j) * C ((-1)^j * ((2*n).choose k * n.choose j : ℤ)) =
                C ((-1)^j * ((2*n).choose k * n.choose j : ℤ)) * (V ^ k * W ^ (2 * j)) := by ring
  rw [h_comm]
  rw [coeff_C_mul]
  have h_vw : coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ k * W ^ (2 * j) : P) = 0 := by
    apply coeff_VW_eq_zero
    intro hc
    apply hk
    omega
  rw [h_vw, mul_zero]

theorem coeff_P_n_eq_sum (n : ℕ) :
  coeff (xyz_pow_n n) (P_n n) =
    ∑ j ∈ Finset.range (n + 1),
      ((2 * n).choose n : ℤ) * coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * j) * W ^ (2 * j)) *
        ((-1)^j * ((2*n).choose (2 * n - 2 * j) * n.choose j : ℤ)) := by
  rw [P_n_expand]
  simp_rw [coeff_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj_le : j ≤ n := Finset.mem_range_succ_iff.mp hj
  have hk_eq : 2 * n - 2 * j ∈ Finset.range (2 * n + 1) := by
    rw [Finset.mem_range]
    omega
  rw [Finset.sum_eq_single (2 * n - 2 * j)]
  · have h_assoc : (U ^ (2 * n - (2 * n - 2 * j) + (2 * n - 2 * j)) * V ^ (2 * n - 2 * j) * W ^ (2 * j) * C ((-1)^j * ((2*n).choose (2 * n - 2 * j) * n.choose j : ℤ))) =
                    (U ^ (2 * n - (2 * n - 2 * j) + (2 * n - 2 * j))) * (V ^ (2 * n - 2 * j) * W ^ (2 * j) * C ((-1)^j * ((2*n).choose (2 * n - 2 * j) * n.choose j : ℤ))) := by ring
    rw [h_assoc]
    have hp_var : is_var0 (U ^ (2 * n - (2 * n - 2 * j) + (2 * n - 2 * j))) := by
      apply is_var0_pow is_var0_U
    have hq_var : is_var12 (V ^ (2 * n - 2 * j) * W ^ (2 * j) * C ((-1)^j * ((2*n).choose (2 * n - 2 * j) * n.choose j : ℤ))) := by
      apply is_var12_mul
      · apply is_var12_mul
        · apply is_var12_pow is_var12_V
        · apply is_var12_pow is_var12_W
      · apply is_var12_C
    rw [coeff_mul_disjoint hp_var hq_var]
    have h_exp : 2 * n - (2 * n - 2 * j) + (2 * n - 2 * j) = 2 * n := by omega
    rw [h_exp]
    rw [coeff_U_pow (2 * n) n (by omega)]
    have h_comm : V ^ (2 * n - 2 * j) * W ^ (2 * j) * C ((-1)^j * ((2*n).choose (2 * n - 2 * j) * n.choose j : ℤ)) =
                  C ((-1)^j * ((2*n).choose (2 * n - 2 * j) * n.choose j : ℤ)) * (V ^ (2 * n - 2 * j) * W ^ (2 * j)) := by ring
    rw [h_comm]
    rw [coeff_C_mul]
    ring
  · intro k hk hk_ne
    have h_assoc : (U ^ (2 * n - k + (2 * n - 2 * j)) * V ^ k * W ^ (2 * j) * C ((-1)^j * ((2*n).choose k * n.choose j : ℤ))) =
                    (U ^ (2 * n - k + (2 * n - 2 * j))) * (V ^ k * W ^ (2 * j) * C ((-1)^j * ((2*n).choose k * n.choose j : ℤ))) := by ring
    rw [h_assoc]
    have hp_var : is_var0 (U ^ (2 * n - k + (2 * n - 2 * j))) := by
      apply is_var0_pow is_var0_U
    have hq_var : is_var12 (V ^ k * W ^ (2 * j) * C ((-1)^j * ((2*n).choose k * n.choose j : ℤ))) := by
      apply is_var12_mul
      · apply is_var12_mul
        · apply is_var12_pow is_var12_V
        · apply is_var12_pow is_var12_W
      · apply is_var12_C
    rw [coeff_mul_disjoint hp_var hq_var]
    have h_zero : coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ k * W ^ (2 * j) * C ((-1)^j * ((2*n).choose k * n.choose j : ℤ))) = 0 := by
      apply term_eq_zero; exact hk_ne
    rw [h_zero, mul_zero]
  · intro hk_not
    exact False.elim (hk_not hk_eq)



theorem W_sq_eq : (W : P) ^ 2 = (V : P) ^ 2 - 4 * X 1 * X 2 := by
  dsimp [V, W]
  ring

theorem W_pow_eq (j : ℕ) :
  (W : P) ^ (2 * j) = ∑ i ∈ Finset.range (j + 1),
    (- 4 * X 1 * X 2 : P) ^ i * (V ^ 2) ^ (j - i) * C (j.choose i : ℤ) := by
  rw [pow_mul]
  rw [W_sq_eq]
  have h_add : (V : P) ^ 2 - 4 * X 1 * X 2 = (- 4 * X 1 * X 2) + V ^ 2 := by ring
  rw [h_add]
  rw [add_pow (- 4 * X 1 * X 2) (V ^ 2) j]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp

theorem coeff_X_pow_mul (s : Vars) (k : ℕ) (m : Finsupp Vars ℕ) (p : P) :
  coeff (Finsupp.single s k + m) (X s ^ k * p) = coeff m p := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h_pow : X s ^ (k + 1) * p = X s * (X s ^ k * p) := by
      rw [pow_succ]
      ring
    have h_single : Finsupp.single s (k + 1) + m = Finsupp.single s 1 + (Finsupp.single s k + m) := by
      ext i
      by_cases h : i = s
      · subst h
        simp [Finsupp.coe_add, Finsupp.single_eq_same]
        omega
      · simp [Finsupp.coe_add, Finsupp.single_eq_of_ne h]
    rw [h_pow, h_single]
    rw [coeff_X_mul]
    exact ih

theorem coeff_X12_pow_mul (i : ℕ) (m : Finsupp Vars ℕ) (p : P) :
  coeff (Finsupp.single 1 i + Finsupp.single 2 i + m) ((X 1 * X 2 : P) ^ i * p) = coeff m p := by
  have h_pow : (X 1 * X 2 : P) ^ i * p = X 1 ^ i * (X 2 ^ i * p) := by
    rw [mul_pow]
    ring
  have h_add : Finsupp.single 1 i + Finsupp.single 2 i + m = Finsupp.single 1 i + (Finsupp.single 2 i + m) := by
    rw [add_assoc]
  rw [h_pow, h_add]
  rw [coeff_X_pow_mul 1 i]
  rw [coeff_X_pow_mul 2 i]

theorem single_add_single_sub (i n : ℕ) (hi : i ≤ n) :
  Finsupp.single (1:Vars) i + Finsupp.single (2:Vars) i + (Finsupp.single (1:Vars) (n - i) + Finsupp.single (2:Vars) (n - i)) =
  Finsupp.single (1:Vars) n + Finsupp.single (2:Vars) n := by
  ext v
  fin_cases v <;> simp [Finsupp.coe_add] <;> omega

theorem coeff_X12_pow_mul_eq (i n : ℕ) (hi : i ≤ n) (p : P) :
  coeff (Finsupp.single (1:Vars) n + Finsupp.single (2:Vars) n) ((X 1 * X 2 : P) ^ i * p) =
  coeff (Finsupp.single (1:Vars) (n - i) + Finsupp.single (2:Vars) (n - i)) p := by
  have h_add := single_add_single_sub i n hi
  rw [← h_add]
  exact coeff_X12_pow_mul i _ _

theorem monomial_eq (i j : ℕ) (c : ℤ) :
  (X 1 ^ i * X 2 ^ j * C c : P) = monomial (Finsupp.single 1 i + Finsupp.single 2 j) c := by
  have h1 : (X 1 : P) ^ i = monomial (Finsupp.single 1 i) 1 := by
    rw [X, monomial_pow]
    simp
  have h2 : (X 2 : P) ^ j = monomial (Finsupp.single 2 j) 1 := by
    rw [X, monomial_pow]
    simp
  have h3 : (C c : P) = monomial 0 c := rfl
  rw [h1, h2, h3]
  rw [monomial_mul, monomial_mul]
  simp

theorem single12_eq_iff (i j m : ℕ) :
  Finsupp.single (1:Vars) i + Finsupp.single (2:Vars) j = Finsupp.single (1:Vars) m + Finsupp.single (2:Vars) m ↔ i = m ∧ j = m := by
  constructor
  · intro h
    have h1 := congr_arg (fun f : Vars →₀ ℕ => f 1) h
    have h2 := congr_arg (fun f : Vars →₀ ℕ => f 2) h
    simp [Finsupp.coe_add] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem coeff_X12_pow_C (i j m : ℕ) (c : ℤ) :
  coeff (Finsupp.single (1:Vars) m + Finsupp.single (2:Vars) m) (X 1 ^ i * X 2 ^ j * C c : P) =
  if i = m ∧ j = m then c else 0 := by
  rw [monomial_eq]
  rw [coeff_monomial]
  by_cases h : i = m ∧ j = m
  · have h_eq : (Finsupp.single (1:Vars) i + Finsupp.single (2:Vars) j = Finsupp.single (1:Vars) m + Finsupp.single (2:Vars) m) := by
      rw [single12_eq_iff]
      exact h
    rw [if_pos h_eq, if_pos h]
  · have h_neq : ¬(Finsupp.single (1:Vars) i + Finsupp.single (2:Vars) j = Finsupp.single (1:Vars) m + Finsupp.single (2:Vars) m) := by
      rw [single12_eq_iff]
      exact h
    rw [if_neg h_neq, if_neg h]

theorem coeff_V_pow (m : ℕ) :
  coeff (Finsupp.single (1:Vars) m + Finsupp.single (2:Vars) m) ((V : P) ^ (2 * m)) = (2 * m).choose m := by
  dsimp [V]
  rw [add_pow (X 1) (X 2) (2 * m)]
  simp_rw [coeff_sum]
  have hm_mem : m ∈ Finset.range (2 * m + 1) := by
    rw [Finset.mem_range]
    omega
  rw [Finset.sum_eq_single m]
  · have h_sub : 2 * m - m = m := by omega
    rw [h_sub]
    have hc : (X 1 ^ m * X 2 ^ m * ((2 * m).choose m : P)) = X 1 ^ m * X 2 ^ m * C ((2 * m).choose m : ℤ) := by simp
    rw [hc]
    rw [coeff_X12_pow_C]
    simp
  · intro i hi hi_ne
    have hc : (X 1 ^ i * X 2 ^ (2 * m - i) * ((2 * m).choose i : P)) = X 1 ^ i * X 2 ^ (2 * m - i) * C ((2 * m).choose i : ℤ) := by simp
    rw [hc]
    rw [coeff_X12_pow_C]
    split_ifs with h_and
    · omega
    · rfl
  · intro hm_not
    exact False.elim (hm_not hm_mem)

theorem coeff_term_eq (n j : ℕ) (hj : j ≤ n) :
  coeff (Finsupp.single (1:Vars) n + Finsupp.single (2:Vars) n) (V ^ (2 * n - 2 * j) * W ^ (2 * j) : P) =
  ∑ i ∈ Finset.range (j + 1), (-4)^i * (j.choose i : ℤ) * (2 * n - 2 * i).choose (n - i) := by
  rw [W_pow_eq]
  rw [Finset.mul_sum]
  rw [coeff_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi_le : i ≤ j := Finset.mem_range_succ_iff.mp hi
  have hi_le_n : i ≤ n := by omega
  have h_neg4 : (- 4 * X 1 * X 2 : P) ^ i = C ((-4 : ℤ)^i) * (X 1 * X 2 : P) ^ i := by
    have h_eq : (- 4 * X 1 * X 2 : P) = C (-4 : ℤ) * (X 1 * X 2 : P) := by
      simp
      ring
    rw [h_eq, mul_pow, ← map_pow]
  have h_term : (V : P) ^ (2 * n - 2 * j) * ((- 4 * X 1 * X 2 : P) ^ i * (V ^ 2) ^ (j - i) * C (j.choose i : ℤ)) =
                C ((-4 : ℤ)^i * (j.choose i : ℤ)) * ((X 1 * X 2 : P) ^ i * V ^ (2 * n - 2 * i)) := by
    rw [h_neg4]
    have h_V_pow : (V : P) ^ (2 * n - 2 * j) * (V ^ 2) ^ (j - i) = (V : P) ^ (2 * n - 2 * i) := by
      rw [← pow_mul]
      have h_exp : 2 * n - 2 * j + 2 * (j - i) = 2 * n - 2 * i := by omega
      rw [← pow_add]
      rw [h_exp]
    have h_rearrange : (V : P) ^ (2 * n - 2 * j) * (C ((-4 : ℤ)^i) * (X 1 * X 2 : P) ^ i * (V ^ 2) ^ (j - i) * C (j.choose i : ℤ)) =
                       (C ((-4 : ℤ)^i) * C (j.choose i : ℤ)) * (X 1 * X 2 : P) ^ i * ((V : P) ^ (2 * n - 2 * j) * (V ^ 2) ^ (j - i)) := by ring
    rw [h_rearrange, h_V_pow]
    rw [map_mul]
    ring
  rw [h_term, coeff_C_mul, coeff_X12_pow_mul_eq i n hi_le_n]
  have h_exp_V : 2 * n - 2 * i = 2 * (n - i) := by omega
  rw [h_exp_V]
  rw [coeff_V_pow]

open Polynomial hiding X coeff coeff_sub coeff_one coeff_mul

lemma coeff_one_sub_X_pow (n : ℕ) (k : ℕ) :
  ((1 - Polynomial.X : Polynomial ℤ) ^ n).coeff k = (-1)^k * n.choose k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ m =>
      rw [pow_zero]
      rw [Polynomial.coeff_one, if_neg (by omega)]
      simp
  | succ n ih =>
    cases k with
    | zero =>
      have h1 : (1 - Polynomial.X : Polynomial ℤ) ^ (n + 1) = (1 - Polynomial.X) ^ n * (1 - Polynomial.X) := by ring
      rw [h1]
      have h2 : (1 - Polynomial.X : Polynomial ℤ) ^ n * (1 - Polynomial.X) = (1 - Polynomial.X) ^ n - (1 - Polynomial.X) ^ n * Polynomial.X := by ring
      rw [h2]
      rw [Polynomial.coeff_sub, Polynomial.coeff_mul_X_zero, sub_zero]
      rw [ih 0]
      simp
    | succ m =>
      have h1 : (1 - Polynomial.X : Polynomial ℤ) ^ (n + 1) = (1 - Polynomial.X) ^ n * (1 - Polynomial.X) := by ring
      rw [h1]
      have h2 : (1 - Polynomial.X : Polynomial ℤ) ^ n * (1 - Polynomial.X) = (1 - Polynomial.X) ^ n - (1 - Polynomial.X) ^ n * Polynomial.X := by ring
      rw [h2]
      rw [Polynomial.coeff_sub, Polynomial.coeff_mul_X]
      rw [ih (m + 1), ih m]
      rw [choose_succ_succ' n m]
      push_cast
      ring

lemma coeff_one_sub_X_sq_pow (n : ℕ) (j : ℕ) :
  ((1 - Polynomial.X^2 : Polynomial ℤ) ^ n).coeff (2 * j) = (-1)^j * n.choose j := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => simp
    | succ m =>
      rw [pow_zero]
      rw [Polynomial.coeff_one, if_neg (by omega)]
      simp
  | succ n ih =>
    cases j with
    | zero =>
      have h1 : (1 - Polynomial.X^2 : Polynomial ℤ) ^ (n + 1) = (1 - Polynomial.X^2) ^ n * (1 - Polynomial.X^2) := by ring
      rw [h1]
      have h2 : (1 - Polynomial.X^2 : Polynomial ℤ) ^ n * (1 - Polynomial.X^2) = (1 - Polynomial.X^2) ^ n - (1 - Polynomial.X^2) ^ n * Polynomial.X^2 := by ring
      rw [h2]
      rw [Polynomial.coeff_sub]
      have h_zero : ((1 - Polynomial.X^2 : Polynomial ℤ) ^ n * Polynomial.X^2).coeff 0 = 0 := by
        have h_eq : (1 - Polynomial.X^2 : Polynomial ℤ) ^ n * Polynomial.X^2 = ((1 - Polynomial.X^2) ^ n * Polynomial.X) * Polynomial.X := by ring
        rw [h_eq]
        exact Polynomial.coeff_mul_X_zero ((1 - Polynomial.X^2) ^ n * Polynomial.X)
      rw [h_zero, sub_zero]
      rw [ih 0]
      simp
    | succ m =>
      have h1 : (1 - Polynomial.X^2 : Polynomial ℤ) ^ (n + 1) = (1 - Polynomial.X^2) ^ n * (1 - Polynomial.X^2) := by ring
      rw [h1]
      have h2 : (1 - Polynomial.X^2 : Polynomial ℤ) ^ n * (1 - Polynomial.X^2) = (1 - Polynomial.X^2) ^ n - (1 - Polynomial.X^2) ^ n * Polynomial.X^2 := by ring
      rw [h2]
      rw [Polynomial.coeff_sub]
      have h_mul : ((1 - Polynomial.X^2 : Polynomial ℤ) ^ n * Polynomial.X^2).coeff (2 * (m + 1)) = ((1 - Polynomial.X^2 : Polynomial ℤ) ^ n).coeff (2 * m) := by
        have h_eq : 2 * (m + 1) = 2 * m + 2 := by ring
        rw [h_eq]
        exact Polynomial.coeff_mul_X_pow ((1 - Polynomial.X^2 : Polynomial ℤ) ^ n) 2 (2 * m)
      rw [h_mul]
      have h_eq_succ : 2 * (m + 1) = 2 * m + 2 := by ring
      rw [ih (m + 1), ih m]
      rw [choose_succ_succ' n m]
      push_cast
      ring

lemma one_sub_X_mul_one_add_X_pow (n : ℕ) :
  (1 - Polynomial.X : Polynomial ℤ) ^ n * (1 + Polynomial.X) ^ n = (1 - Polynomial.X^2) ^ n := by
  rw [← mul_pow]
  congr 1
  ring

lemma sum_choose_mul_choose_eq (n j : ℕ) :
  ∑ k ∈ Finset.range (2 * j + 1), (-1 : ℤ)^k * n.choose k * n.choose (2 * j - k) = (-1 : ℤ)^j * n.choose j := by
  have h_mul : ((1 - Polynomial.X : Polynomial ℤ) ^ n * (1 + Polynomial.X) ^ n).coeff (2 * j) = ((1 - Polynomial.X^2 : Polynomial ℤ) ^ n).coeff (2 * j) := by
    rw [one_sub_X_mul_one_add_X_pow]
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => ((1 - Polynomial.X : Polynomial ℤ) ^ n).coeff a * ((1 + Polynomial.X : Polynomial ℤ) ^ n).coeff b)] at h_mul
  rw [coeff_one_sub_X_sq_pow] at h_mul
  have h_congr : (∑ k ∈ Finset.range (2 * j + 1), ((1 - Polynomial.X : Polynomial ℤ) ^ n).coeff k * ((1 + Polynomial.X : Polynomial ℤ) ^ n).coeff (2 * j - k)) =
                 ∑ k ∈ Finset.range (2 * j + 1), (-1 : ℤ)^k * n.choose k * n.choose (2 * j - k) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [coeff_one_sub_X_pow]
    have hc : ((1 + Polynomial.X : Polynomial ℤ) ^ n).coeff (2 * j - k) = n.choose (2 * j - k) := by
      exact coeff_one_add_X_pow ℤ n (2 * j - k)
    rw [hc]
  rw [h_congr] at h_mul
  exact h_mul

lemma sum_choose_sq (n : ℕ) :
  (∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) ^ 2) = ((2 * n).choose n : ℤ) := by
  have h_v : ((2 * n).choose n : ℤ) = ∑ ij ∈ Finset.antidiagonal n, (n.choose ij.1 * n.choose ij.2 : ℤ) := by
    have h_v' := Nat.add_choose_eq n n n
    have h_add : n + n = 2 * n := by ring
    rw [h_add] at h_v'
    exact_mod_cast h_v'
  rw [h_v]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => (n.choose a : ℤ) * (n.choose b : ℤ))]
  have h_congr : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * (n.choose (n - k) : ℤ)) =
                 ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) ^ 2 := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk_le : k ≤ n := Finset.mem_range_succ_iff.mp hk
    rw [Nat.choose_symm hk_le]
    ring
  rw [h_congr]

theorem C_recurrence (n : ℕ) (j : ℕ) (hj : j + 1 ≤ n) :
  coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * (j + 1)) * W ^ (2 * (j + 1)) : P) =
  coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * j) * W ^ (2 * j) : P) -
  4 * coeff (Finsupp.single 1 (n - 1) + Finsupp.single 2 (n - 1)) (V ^ (2 * (n - 1) - 2 * j) * W ^ (2 * j) : P) := by
  have h_poly : (V ^ (2 * n - 2 * (j + 1)) * W ^ (2 * (j + 1)) : P) =
                V ^ (2 * n - 2 * j) * W ^ (2 * j) - MvPolynomial.C 4 * X 1 * X 2 * V ^ (2 * n - 2 * j - 2) * W ^ (2 * j) := by
    have h_pow_V : (V ^ (2 * n - 2 * (j + 1)) : P) = V ^ (2 * n - 2 * j - 2) := by
      congr 1
    have h_pow_W : (W ^ (2 * (j + 1)) : P) = W ^ (2 * j) * W ^ 2 := by
      have h_eq : 2 * (j + 1) = 2 * j + 2 := by ring
      rw [h_eq, pow_add]
    rw [h_pow_V, h_pow_W]
    rw [W_sq_eq]
    have h_ring : V ^ (2 * n - 2 * j - 2) * (W ^ (2 * j) * (V ^ 2 - 4 * X 1 * X 2)) =
                  (V ^ 2 * V ^ (2 * n - 2 * j - 2)) * W ^ (2 * j) - 4 * X 1 * X 2 * V ^ (2 * n - 2 * j - 2) * W ^ (2 * j) := by ring
    rw [h_ring]
    have h_V_add : (V ^ 2 : P) * V ^ (2 * n - 2 * j - 2) = V ^ (2 * n - 2 * j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h_V_add]
    simp
  rw [h_poly]
  rw [coeff_sub]
  congr 1
  have h_mul : (MvPolynomial.C 4 * X 1 * X 2 * V ^ (2 * n - 2 * j - 2) * W ^ (2 * j) : P) =
               MvPolynomial.C 4 * (X 1 * X 2 * (V ^ (2 * n - 2 * j - 2) * W ^ (2 * j))) := by ring
  rw [h_mul, MvPolynomial.coeff_C_mul]
  have h_coeff : coeff (Finsupp.single 1 n + Finsupp.single 2 n) (X 1 * X 2 * (V ^ (2 * n - 2 * j - 2) * W ^ (2 * j)) : P) =
                 coeff (Finsupp.single 1 (n - 1) + Finsupp.single 2 (n - 1)) (V ^ (2 * (n - 1) - 2 * j) * W ^ (2 * j) : P) := by
    have h_single : (X 1 * X 2 : P) = (X 1 * X 2 : P) ^ 1 := by ring
    rw [h_single]
    rw [coeff_X12_pow_mul_eq 1 n (by omega)]
    have h_exp : 2 * (n - 1) - 2 * j = 2 * n - 2 * j - 2 := by omega
    rw [h_exp]
  rw [h_coeff]


lemma choose_ident1 (n j : ℕ) (hj : j + 1 ≤ n) :
  (2 * j + 2) * (2 * j + 1) * (2 * n).choose (2 * j + 2) = (2 * n - 2 * j) * (2 * n - 2 * j - 1) * (2 * n).choose (2 * j) := by
  have h1 : (2 * n).choose (2 * j + 2) * (2 * j + 2) = (2 * n).choose (2 * j + 1) * (2 * n - (2 * j + 1)) := by
    apply Nat.choose_succ_right_eq (2 * n) (2 * j + 1)
  have h2 : (2 * n).choose (2 * j + 1) * (2 * j + 1) = (2 * n).choose (2 * j) * (2 * n - 2 * j) := by
    apply Nat.choose_succ_right_eq (2 * n) (2 * j)
  have h3 : 2 * n - (2 * j + 1) = 2 * n - 2 * j - 1 := by omega
  have h_lhs : (2 * j + 2) * (2 * j + 1) * (2 * n).choose (2 * j + 2) =
               (2 * j + 1) * ((2 * n).choose (2 * j + 2) * (2 * j + 2)) := by ring
  rw [h_lhs, h1, h3]
  have h_mid : (2 * j + 1) * ((2 * n).choose (2 * j + 1) * (2 * n - 2 * j - 1)) =
               (2 * n - 2 * j - 1) * ((2 * n).choose (2 * j + 1) * (2 * j + 1)) := by ring
  rw [h_mid, h2]
  ring


lemma choose_ident2 (n j : ℕ) (hj : j + 1 ≤ n) :
  (2 * j + 2) * (2 * j + 1) * (2 * n).choose (2 * j + 2) = 2 * n * (2 * n - 1) * (2 * n - 2).choose (2 * j) := by
  have h1 : (2 * n) * (2 * n - 1).choose (2 * j + 1) = (2 * n).choose (2 * j + 2) * (2 * j + 2) := by
    have h_succ : Nat.succ (2 * n - 1) = 2 * n := by omega
    have h_j : Nat.succ (2 * j + 1) = 2 * j + 2 := by omega
    have h_eq := Nat.succ_mul_choose_eq (2 * n - 1) (2 * j + 1)
    rw [h_succ, h_j] at h_eq
    exact h_eq
  have h2 : (2 * n - 1) * (2 * n - 2).choose (2 * j) = (2 * n - 1).choose (2 * j + 1) * (2 * j + 1) := by
    have h_succ : Nat.succ (2 * n - 2) = 2 * n - 1 := by omega
    have h_j : Nat.succ (2 * j) = 2 * j + 1 := by omega
    have h_eq := Nat.succ_mul_choose_eq (2 * n - 2) (2 * j)
    rw [h_succ, h_j] at h_eq
    exact h_eq
  have h_lhs : (2 * j + 2) * (2 * j + 1) * (2 * n).choose (2 * j + 2) =
               (2 * j + 1) * ((2 * n).choose (2 * j + 2) * (2 * j + 2)) := by ring
  rw [h_lhs, ← h1]
  have h_mid : (2 * j + 1) * (2 * n * (2 * n - 1).choose (2 * j + 1)) =
               2 * n * ((2 * n - 1).choose (2 * j + 1) * (2 * j + 1)) := by ring
  rw [h_mid, ← h2]
  ring


lemma choose_ident3 (n : ℕ) (hn : 1 ≤ n) :
  n * (2 * n).choose n = 2 * (2 * n - 1) * (2 * n - 2).choose (n - 1) := by
  have h1 : (2 * n) * (2 * n - 1).choose (n - 1) = (2 * n).choose n * n := by
    have h_succ : Nat.succ (2 * n - 1) = 2 * n := by omega
    have h_n : Nat.succ (n - 1) = n := by omega
    have h_eq := Nat.succ_mul_choose_eq (2 * n - 1) (n - 1)
    rw [h_succ, h_n] at h_eq
    exact h_eq
  have h2 : (2 * n - 1).choose (n - 1) = (2 * n - 1).choose n := by
    have h_symm : (2 * n - 1).choose ((2 * n - 1) - (n - 1)) = (2 * n - 1).choose (n - 1) := by
      apply Nat.choose_symm
      omega
    have h_sub : (2 * n - 1) - (n - 1) = n := by omega
    rw [h_sub] at h_symm
    rw [h_symm]
  have h3 : (2 * n - 1) * (2 * n - 2).choose (n - 1) = (2 * n - 1).choose n * n := by
    have h_succ : Nat.succ (2 * n - 2) = 2 * n - 1 := by omega
    have h_n : Nat.succ (n - 1) = n := by omega
    have h_eq := Nat.succ_mul_choose_eq (2 * n - 2) (n - 1)
    rw [h_succ, h_n] at h_eq
    exact h_eq
  have h_lhs : n * (2 * n).choose n = (2 * n).choose n * n := by ring
  rw [h_lhs, ← h1, h2]
  have h_mid : 2 * n * (2 * n - 1).choose n = 2 * ((2 * n - 1).choose n * n) := by ring
  rw [h_mid, ← h3]
  ring


lemma choose_ident5 (n j : ℕ) (hn : 1 ≤ n) :
  n.choose (j + 1) * (j + 1) = n * (n - 1).choose j := by
  have h_succ : Nat.succ (n - 1) = n := by omega
  have h_eq := Nat.succ_mul_choose_eq (n - 1) j
  rw [h_succ] at h_eq
  exact h_eq.symm


lemma choose_identity_main (n j : ℕ) (hj : j + 1 ≤ n) :
  ((2 * n).choose (2 * j) : ℤ) * ((2 * n - 2).choose (2 * j) : ℤ) * (- ((2 * n).choose n : ℤ) * n.choose (j + 1)) =
  ((2 * n - 2).choose (2 * j) : ℤ) * ((2 * n).choose (2 * j + 2) : ℤ) * (((2 * n).choose n : ℤ) * n.choose j) -
  4 * ((2 * n).choose (2 * j) : ℤ) * ((2 * n).choose (2 * j + 2) : ℤ) * (((2 * n - 2).choose (n - 1) : ℤ) * (n - 1).choose j) := by
  let nZ : ℤ := n
  let jZ : ℤ := j
  let A : ℤ := (2 * n).choose (2 * j)
  let B : ℤ := (2 * n).choose (2 * j + 2)
  let D : ℤ := (2 * n - 2).choose (2 * j)
  let H1 : ℤ := (2 * n - 2).choose (n - 1)
  let H2 : ℤ := (2 * n).choose n
  let C1 : ℤ := n.choose (j + 1)
  let C2 : ℤ := n.choose j
  let C3 : ℤ := (n - 1).choose j
  let denom_A : ℤ := (2 * nZ - 2 * jZ) * (2 * nZ - 2 * jZ - 1)

  have hn : 1 ≤ n := by omega

  have h_eq1_nat : (2 * n - 2 * j) * (2 * n - 2 * j - 1) * (2 * n).choose (2 * j) = (2 * j + 2) * (2 * j + 1) * (2 * n).choose (2 * j + 2) := by
    have h := choose_ident1 n j hj
    exact h.symm

  have h_eq2_nat : 2 * n * (2 * n - 1) * (2 * n - 2).choose (2 * j) = (2 * j + 2) * (2 * j + 1) * (2 * n).choose (2 * j + 2) := by
    have h := choose_ident2 n j hj
    exact h.symm

  have h_eq3_nat : n * (2 * n).choose n = 2 * (2 * n - 1) * (2 * n - 2).choose (n - 1) := by
    have h := choose_ident3 n hn
    exact h

  have h_eq4_nat : (n - j) * n.choose j = (j + 1) * n.choose (j + 1) := by
    have h := Nat.choose_succ_right_eq n j
    rw [mul_comm, ← h, mul_comm]

  have h_eq5_nat : n * (n - 1).choose j = (j + 1) * n.choose (j + 1) := by
    have h := choose_ident5 n j hn
    rw [← h, mul_comm]

  have h_sub1 : ((2 * n - 1 : ℕ) : ℤ) = 2 * nZ - 1 := by dsimp [nZ]; omega
  have h_sub_j1 : ((2 * n - 2 * j - 1 : ℕ) : ℤ) = 2 * nZ - 2 * jZ - 1 := by dsimp [nZ, jZ]; omega
  have h_sub_j2 : ((2 * n - 2 * j : ℕ) : ℤ) = 2 * nZ - 2 * jZ := by dsimp [nZ, jZ]; omega
  have h_sub_nj : ((n - j : ℕ) : ℤ) = nZ - jZ := by dsimp [nZ, jZ]; omega

  let eq2 : ℤ := 2 * nZ * (2 * nZ - 1) * D - (2 * jZ + 2) * (2 * jZ + 1) * B
  let eq3 : ℤ := nZ * H2 - 2 * (2 * nZ - 1) * H1
  let eq4 : ℤ := (nZ - jZ) * C2 - (jZ + 1) * C1
  let eq5 : ℤ := nZ * C3 - (jZ + 1) * C1

  have h_eq2_0 : eq2 = 0 := by
    dsimp [eq2, nZ, jZ, D, B]
    have h_cast : (((2 * n * (2 * n - 1) * (2 * n - 2).choose (2 * j) : ℕ) : ℤ)) = (((2 * j + 2) * (2 * j + 1) * (2 * n).choose (2 * j + 2) : ℕ) : ℤ) := by rw [h_eq2_nat]
    push_cast at h_cast
    rw [h_sub1] at h_cast
    linarith
  have h_eq3_0 : eq3 = 0 := by
    dsimp [eq3, nZ, H2, H1]
    have h_cast : (((n * (2 * n).choose n : ℕ) : ℤ)) = (((2 * (2 * n - 1) * (2 * n - 2).choose (n - 1) : ℕ) : ℤ)) := by rw [h_eq3_nat]
    push_cast at h_cast
    rw [h_sub1] at h_cast
    linarith
  have h_eq4_0 : eq4 = 0 := by
    dsimp [eq4, nZ, jZ, C2, C1]
    have h_cast : ((((n - j) * n.choose j : ℕ) : ℤ)) = ((((j + 1) * n.choose (j + 1) : ℕ) : ℤ)) := by rw [h_eq4_nat]
    push_cast at h_cast
    rw [h_sub_nj] at h_cast
    linarith
  have h_eq5_0 : eq5 = 0 := by
    dsimp [eq5, nZ, jZ, C3, C1]
    have h_cast : (((n * (n - 1).choose j : ℕ) : ℤ)) = ((((j + 1) * n.choose (j + 1) : ℕ) : ℤ)) := by rw [h_eq5_nat]
    push_cast at h_cast
    linarith

  let target : ℤ := 4 * A * B * H1 * C3 - A * D * H2 * C1 - D * B * H2 * C2
  let bracket : ℤ := 4 * nZ * A * B * (jZ + 1) * (nZ - jZ) - (2 * jZ + 2) * (2 * jZ + 1) * B * (A * (nZ - jZ) + B * (jZ + 1))

  have h_id : 2 * nZ * (2 * nZ - 1) * (nZ - jZ) * target = H2 * C1 * bracket + 4 * A * B * (nZ - jZ) * (nZ * H2 * eq5 - (jZ + 1) * C1 * eq3 - eq3 * eq5) - A * H2 * C1 * (nZ - jZ) * eq2 - B * H2 * (2 * jZ + 2) * (2 * jZ + 1) * B * eq4 - B * H2 * (jZ + 1) * C1 * eq2 - B * H2 * eq2 * eq4 := by ring

  rw [h_eq2_0, h_eq3_0, h_eq4_0, h_eq5_0] at h_id
  have h_id_simped : 2 * nZ * (2 * nZ - 1) * (nZ - jZ) * target = H2 * C1 * bracket := by
    omega

  have h_eq1_0 : denom_A * A - (2 * jZ + 2) * (2 * jZ + 1) * B = 0 := by
    dsimp [denom_A, nZ, jZ, A, B]
    have h_cast : (((2 * n - 2 * j) * (2 * n - 2 * j - 1) * (2 * n).choose (2 * j) : ℕ) : ℤ) = (((2 * j + 2) * (2 * j + 1) * (2 * n).choose (2 * j + 2) : ℕ) : ℤ) := by rw [h_eq1_nat]
    push_cast at h_cast
    rw [h_sub_j1, h_sub_j2] at h_cast
    linarith

  have h_denom_bracket : denom_A * bracket = (4 * nZ * B * (jZ + 1) * (nZ - jZ) - (2 * jZ + 2) * (2 * jZ + 1) * B * (nZ - jZ)) * (denom_A * A - (2 * jZ + 2) * (2 * jZ + 1) * B) := by ring

  rw [h_eq1_0, mul_zero] at h_denom_bracket

  have h_denom_pos : 0 < denom_A := by
    dsimp [denom_A, nZ, jZ]
    have h1 : 0 < 2 * (n : ℤ) - 2 * (j : ℤ) := by omega
    have h2 : 0 < 2 * (n : ℤ) - 2 * (j : ℤ) - 1 := by omega
    exact mul_pos h1 h2
  have h_denom_ne : denom_A ≠ 0 := by omega

  have h_bracket_zero : bracket = 0 := by
    have h_or := mul_eq_zero.mp h_denom_bracket
    cases h_or with
    | inl h_denom =>
      exact False.elim (h_denom_ne h_denom)
    | inr h_br =>
      exact h_br

  have h_coeff_pos : 0 < 2 * nZ * (2 * nZ - 1) * (nZ - jZ) := by
    dsimp [nZ, jZ]
    have h1 : 0 < 2 * (n : ℤ) := by omega
    have h2 : 0 < 2 * (n : ℤ) - 1 := by omega
    have h3 : 0 < (n : ℤ) - j := by omega
    apply mul_pos
    · apply mul_pos <;> omega
    · omega
  have h_coeff_ne : 2 * nZ * (2 * nZ - 1) * (nZ - jZ) ≠ 0 := by omega

  have h_target_zero : target = 0 := by
    rw [h_bracket_zero, mul_zero] at h_id_simped
    have h_or := mul_eq_zero.mp h_id_simped
    cases h_or with
    | inl h_cf =>
      exact False.elim (h_coeff_ne h_cf)
    | inr h_tg =>
      exact h_tg

  have h_diff : A * D * (- H2 * C1) - (D * B * (H2 * C2) - 4 * A * B * (H1 * C3)) = target := by ring
  rw [h_target_zero] at h_diff
  dsimp [A, B, D, H1, H2, C1, C2, C3] at h_diff
  exact sub_eq_zero.mp h_diff


/--
**oeis_2897_conjecture_0**:
Conjecture: The g.f. is also the diagonal of the rational function 1/(1 - (x + y)*(1 - 4*z*t) - z - t) = 1/det(I - M*diag(x, y, z, t)), I the 4 x 4 unit matrix and M the 4 x 4 matrix [1, 1, 1, 1; 1, 1, 1, 1; 1, 1, 1, -1; 1 , 1, -1, 1]. If true, then a(n) = [(x*y*z)^n] (1 + x + y + z)^(2*n)*(1 + x + y - z)^n*(1 + x - y + z)^n. - _Peter Bala_, Apr 10 2022
-/
lemma coeff_V_W_eq_strong (n : ℕ) (j : ℕ) (hj : j ≤ n) :
  ((2 * n).choose (2 * j) : ℤ) * coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * j) * W ^ (2 * j) : P) =
  (-1)^j * (2 * n).choose n * n.choose j := by
  induction n using Nat.strong_induction_on generalizing j with
  | h n ih =>
    induction j with
    | zero =>
      simp
      rw [coeff_V_pow]
    | succ j ih_j =>
      have hj_le : j + 1 ≤ n := hj
      have hn1 : n - 1 < n := by omega
      have h_ih_n1 : ((2 * (n - 1)).choose (2 * j) : ℤ) * coeff (Finsupp.single 1 (n - 1) + Finsupp.single 2 (n - 1)) (V ^ (2 * (n - 1) - 2 * j) * W ^ (2 * j) : P) =
                      (-1)^j * (2 * (n - 1)).choose (n - 1) * (n - 1).choose j := by
        apply ih (n - 1) hn1 j
        omega
      have h_ih_j : ((2 * n).choose (2 * j) : ℤ) * coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * j) * W ^ (2 * j) : P) =
                    (-1)^j * (2 * n).choose n * n.choose j := by
        apply ih_j
        omega
      let c_next := coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * (j + 1)) * W ^ (2 * (j + 1)) : P)
      let c_curr := coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * j) * W ^ (2 * j) : P)
      let c_prev := coeff (Finsupp.single 1 (n - 1) + Finsupp.single 2 (n - 1)) (V ^ (2 * (n - 1) - 2 * j) * W ^ (2 * j) : P)

      have h_rec := C_recurrence n j hj_le
      let A : ℤ := (2 * n).choose (2 * j)
      let D : ℤ := (2 * (n - 1)).choose (2 * j)
      let B : ℤ := (2 * n).choose (2 * j + 2)

      have h_mult : A * D * B * c_next = D * B * (A * c_curr) - 4 * A * B * (D * c_prev) := by
        dsimp [c_next, c_curr, c_prev]
        rw [h_rec]
        dsimp [A, B, D]
        ring

      rw [h_ih_j, h_ih_n1] at h_mult

      have h_factor : D * B * ((-1)^j * (2 * n).choose n * n.choose j) - 4 * A * B * ((-1)^j * (2 * (n - 1)).choose (n - 1) * (n - 1).choose j) =
                      (-1)^j * (D * B * (((2 * n).choose n : ℤ) * n.choose j) - 4 * A * B * (((2 * (n - 1)).choose (n - 1) : ℤ) * (n - 1).choose j)) := by ring
      rw [h_factor] at h_mult

      have h_main := choose_identity_main n j hj_le
      have h_sub_eq : 2 * n - 2 = 2 * (n - 1) := by omega
      rw [h_sub_eq] at h_main

      have h_main_mult : (-1)^j * (A * D * (- ((2 * n).choose n : ℤ) * n.choose (j + 1))) =
                         (-1)^j * (D * B * (((2 * n).choose n : ℤ) * n.choose j) - 4 * A * B * (((2 * (n - 1)).choose (n - 1) : ℤ) * (n - 1).choose j)) := by
        dsimp [A, B, D]
        rw [h_main]

      have h_neg_pow : (-1)^j * (A * D * (- ((2 * n).choose n : ℤ) * n.choose (j + 1))) =
                       A * D * ((-1)^(j + 1) * (2 * n).choose n * n.choose (j + 1)) := by
        have h_pow : (-1 : ℤ)^(j + 1) = - (-1)^j := by
          rw [pow_succ]
          ring
        rw [h_pow]
        ring

      rw [h_neg_pow] at h_main_mult
      rw [← h_main_mult] at h_mult

      have h_A_pos : 0 < A := by
        dsimp [A]
        exact_mod_cast Nat.choose_pos (by omega)
      have h_D_pos : 0 < D := by
        dsimp [D]
        exact_mod_cast Nat.choose_pos (by omega)
      have h_AD_ne : A * D ≠ 0 := by
        have h_pos : 0 < A * D := mul_pos h_A_pos h_D_pos
        omega

      have h_cancel : B * c_next = (-1)^(j + 1) * (2 * n).choose n * n.choose (j + 1) := by
        have h_ring_lhs : A * D * B * c_next = A * D * (B * c_next) := by ring
        rw [h_ring_lhs] at h_mult
        exact mul_left_cancel₀ h_AD_ne h_mult

      exact h_cancel

lemma T_eq (n : ℕ) (j : ℕ) (hj : j ≤ n) :
  coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * j) * W ^ (2 * j) : P) *
    ((-1)^j * ((2*n).choose (2 * n - 2 * j) * n.choose j : ℤ)) = ((2 * n).choose n : ℤ) * (n.choose j : ℤ) ^ 2 := by
  have h_symm : (2 * n).choose (2 * n - 2 * j) = (2 * n).choose (2 * j) := by
    rw [Nat.choose_symm (by omega)]
  have h_comm : coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * j) * W ^ (2 * j) : P) * ((-1)^j * ((2*n).choose (2 * n - 2 * j) * n.choose j : ℤ)) =
                ((-1)^j * n.choose j : ℤ) * (((2 * n).choose (2 * j) : ℤ) * coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * j) * W ^ (2 * j) : P)) := by
    rw [h_symm]
    push_cast
    ring
  rw [h_comm]
  rw [coeff_V_W_eq_strong n j hj]
  have h_neg : (-1 : ℤ) ^ j * (-1 : ℤ) ^ j = 1 := by
    rw [← mul_pow]
    simp
  have h_calc : ((-1 : ℤ) ^ j * n.choose j) * ((-1 : ℤ) ^ j * (2 * n).choose n * n.choose j) =
                ((-1 : ℤ) ^ j * (-1 : ℤ) ^ j) * ((2 * n).choose n * (n.choose j : ℤ) ^ 2) := by ring
  rw [h_calc, h_neg, one_mul]

theorem sum_identity (n : ℕ) :
  ∑ j ∈ Finset.range (n + 1),
    coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * j) * W ^ (2 * j) : P) *
      ((-1)^j * ((2*n).choose (2 * n - 2 * j) * n.choose j : ℤ)) = ((2 * n).choose n : ℤ) ^ 2 := by
  have h_sum : (∑ j ∈ Finset.range (n + 1), coeff (Finsupp.single 1 n + Finsupp.single 2 n) (V ^ (2 * n - 2 * j) * W ^ (2 * j) : P) * ((-1)^j * ((2*n).choose (2 * n - 2 * j) * n.choose j : ℤ))) =
               ∑ j ∈ Finset.range (n + 1), ((2 * n).choose n : ℤ) * (n.choose j : ℤ) ^ 2 := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj_le : j ≤ n := Finset.mem_range_succ_iff.mp hj
    exact T_eq n j hj_le
  rw [h_sum]
  rw [← Finset.mul_sum]
  rw [sum_choose_sq]
  ring

theorem oeis_2897_conjecture_0 (n : ℕ) :
  (a n : ℤ) = MvPolynomial.coeff (xyz_pow_n n) (P_n n) := by
  rw [coeff_P_n_eq_sum]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [sum_identity]
  dsimp [a]
  ring


#print axioms oeis_2897_conjecture_0

