import FormalConjectures.Util.ProblemImports

open Polynomial Nat Finset

noncomputable def A185895 (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  let Px : Polynomial ℚ := (Icc 1 n).prod (fun k : ℕ =>
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)
  let coeff_n : ℚ := Polynomial.coeff Px n
  let a_n_q : ℚ := coeff_n * n.factorial.cast
  a_n_q.floor

def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

namespace A185895Pf

/-! ### Triangular numbers and block positions -/

def T (m : ℕ) : ℕ := m * (m+1) / 2

lemma two_T (m : ℕ) : 2 * T m = m * (m+1) := by
  have h : 2 ∣ m * (m+1) := (Nat.even_mul_succ_self m).two_dvd
  unfold T
  omega

lemma T_succ (m : ℕ) : T (m+1) = T m + (m+1) := by
  have h1 := two_T m
  have h2 : 2 * T (m+1) = m*(m+1) + 2*(m+1) := by rw [two_T]; ring
  omega

lemma T_mono : Monotone T := by
  refine monotone_nat_of_le_succ ?_
  intro m; rw [T_succ]; omega

def blk (n : ℕ) : ℕ := (Nat.sqrt (8*n+1) - 1) / 2

lemma blk_spec (n : ℕ) : T (blk n) ≤ n ∧ n < T (blk n + 1) := by
  have hs : Nat.sqrt (8*n+1) ^ 2 ≤ 8*n+1 := Nat.sqrt_le' (8*n+1)
  have hs2 : 8*n+1 < (Nat.sqrt (8*n+1) + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' (8*n+1)
    simpa [Nat.succ_eq_add_one] using this
  have hs1 : 1 ≤ Nat.sqrt (8*n+1) := by
    by_contra h
    push_neg at h
    have h0 : Nat.sqrt (8*n+1) = 0 := by omega
    rw [h0] at hs2
    norm_num at hs2
  have hb : blk n = (Nat.sqrt (8*n+1) - 1) / 2 := rfl
  set s := Nat.sqrt (8*n+1)
  set m := blk n
  have hm2 : 2*m+1 ≤ s ∧ s ≤ 2*m+2 := by omega
  have e1 : (2*m+1)^2 ≤ 8*n+1 := le_trans (Nat.pow_le_pow_left hm2.1 2) hs
  have e2 : 8*n+1 < (2*m+3)^2 :=
    lt_of_lt_of_le hs2 (Nat.pow_le_pow_left (by omega) 2)
  have h3 : (2*m+1)^2 = 4*(m*(m+1))+1 := by ring
  have h4 : (2*m+3)^2 = 4*((m+1)*((m+1)+1))+1 := by ring
  rw [h3] at e1
  rw [h4] at e2
  have t1 := two_T m
  have t2 := two_T (m+1)
  omega

lemma T_blk_le (n : ℕ) : T (blk n) ≤ n := (blk_spec n).1
lemma lt_T_blk_succ (n : ℕ) : n < T (blk n + 1) := (blk_spec n).2

/-- blk is characterized by the bracketing. -/
lemma blk_eq_of (n m : ℕ) (h1 : T m ≤ n) (h2 : n < T (m+1)) : blk n = m := by
  have b1 := T_blk_le n
  have b2 := lt_T_blk_succ n
  by_contra h
  rcases Nat.lt_or_ge (blk n) m with hlt | hge
  · have : blk n + 1 ≤ m := hlt
    have := T_mono this
    omega
  · have : m + 1 ≤ blk n := by omega
    have := T_mono this
    omega

lemma blk_T (m : ℕ) : blk (T m) = m :=
  blk_eq_of _ _ (le_refl _) (by rw [T_succ]; omega)

def nuu (n : ℕ) : ℕ := n - T (blk n)

def K0 (n : ℕ) : ℕ := if nuu n = 0 then blk n else blk n + 1

def rq (n : ℕ) : ℕ := T (K0 n) - n

lemma nuu_le (n : ℕ) : nuu n ≤ blk n := by
  have h1 := T_blk_le n
  have h2 := lt_T_blk_succ n
  have h3 := T_succ (blk n)
  unfold nuu
  omega

lemma n_le_T_K0 (n : ℕ) : n ≤ T (K0 n) := by
  unfold K0
  split
  · have h1 := T_blk_le n
    unfold nuu at *
    omega
  · exact le_of_lt (lt_T_blk_succ n)

lemma rq_eq (n : ℕ) (h : nuu n ≠ 0) : rq n = blk n + 1 - nuu n := by
  have h1 := T_blk_le n
  have h3 := T_succ (blk n)
  unfold rq K0 nuu at *
  split
  · omega
  · omega

lemma rq_zero (n : ℕ) (h : nuu n = 0) : rq n = 0 := by
  have h1 := T_blk_le n
  unfold rq K0 nuu at *
  simp [h]
  omega

/-! ### The coefficient sequence -/

def fq : ℕ → ℕ → ℚ
  | 0, n => if n = 0 then 1 else 0
  | (K+1), n => fq K n - (if K+1 ≤ n then fq K (n-(K+1)) / ((K+1)! : ℚ) else 0)

lemma fq_zero_eval (n : ℕ) : fq 0 n = if n = 0 then 1 else 0 := rfl

lemma fq_succ (K n : ℕ) :
    fq (K+1) n = fq K n - (if K+1 ≤ n then fq K (n-(K+1)) / ((K+1)! : ℚ) else 0) := rfl

lemma fq_at_zero (K : ℕ) : fq K 0 = 1 := by
  induction K with
  | zero => rfl
  | succ K ih => simp [fq_succ, ih]

/-- Bridge to the polynomial product coefficient. -/
lemma fq_eq_coeff (K n : ℕ) :
    fq K n = (((Icc 1 K).prod (fun k : ℕ =>
      (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)).coeff n) := by
  induction K generalizing n with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega : ¬(1:ℕ) ≤ 0), Finset.prod_empty]
    rw [Polynomial.coeff_one, fq_zero_eval]
  | succ K ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ K + 1)]
    rw [mul_sub, mul_one]
    rw [Polynomial.coeff_sub]
    have : ((Icc 1 K).prod (fun k : ℕ =>
        (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k) *
        (C ((1 : ℚ) / (K+1).factorial.cast) * X ^ (K+1))) =
        C ((1 : ℚ) / (K+1).factorial.cast) *
        ((Icc 1 K).prod (fun k : ℕ =>
        (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k) * X ^ (K+1)) := by
      ring
    rw [this, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    rw [fq_succ]
    simp only [ih]
    split
    · ring
    · ring

/-- Degree bound: coefficient vanishes beyond the triangular number. -/
lemma fq_eq_zero (K n : ℕ) (h : T K < n) : fq K n = 0 := by
  induction K generalizing n with
  | zero =>
    have : n ≠ 0 := by unfold T at h; omega
    simp [fq_zero_eval, this]
  | succ K ih =>
    have hT := T_succ K
    rw [fq_succ]
    rw [ih n (by omega)]
    by_cases h2 : K + 1 ≤ n
    · rw [if_pos h2, ih (n - (K+1)) (by omega)]
      ring
    · rw [if_neg h2]
      ring

/-- Integrality: n! * fq K n is an integer. -/
lemma fq_int (K : ℕ) : ∀ n : ℕ, ∃ z : ℤ, (n ! : ℚ) * fq K n = z := by
  induction K with
  | zero =>
    intro n
    by_cases h : n = 0
    · exact ⟨1, by simp [h, fq_zero_eval]⟩
    · exact ⟨0, by simp [fq_zero_eval, h]⟩
  | succ K ih =>
    intro n
    obtain ⟨z1, hz1⟩ := ih n
    by_cases h : K + 1 ≤ n
    · obtain ⟨z2, hz2⟩ := ih (n - (K+1))
      refine ⟨z1 - (n.choose (K+1) : ℤ) * z2, ?_⟩
      rw [fq_succ, if_pos h, mul_sub, hz1]
      have hfact : (n.choose (K+1)) * (K+1)! * (n - (K+1))! = n ! :=
        Nat.choose_mul_factorial_mul_factorial h
      have hne : ((K+1)! : ℚ) ≠ 0 := by positivity
      push_cast
      rw [sub_right_inj]
      rw [div_eq_mul_inv]
      have : (n ! : ℚ) = (n.choose (K+1) : ℚ) * ((K+1)! : ℚ) * ((n - (K+1))! : ℚ) := by
        rw [← hfact]; push_cast; ring
      rw [this]
      field_simp
      rw [← hz2]
      ring
    · exact ⟨z1, by rw [fq_succ, if_neg h]; simpa using hz1⟩

lemma A185895_eq_floor (n : ℕ) (h : n ≠ 0) :
    A185895 n = (fq n n * (n ! : ℚ)).floor := by
  unfold A185895
  rw [if_neg h]
  dsimp only
  rw [← fq_eq_coeff]

/-- The OEIS sequence value equals n! * fq n n (as a rational). -/
lemma A185895_eq (n : ℕ) (h : 0 < n) : ((A185895 n : ℤ) : ℚ) = (n ! : ℚ) * fq n n := by
  obtain ⟨z, hz⟩ := fq_int n n
  rw [A185895_eq_floor n (by omega)]
  have h2 : fq n n * (n ! : ℚ) = (z:ℚ) := by rw [← hz]; ring
  rw [h2, Rat.floor_intCast, ← hz]
  try ring

end A185895Pf
