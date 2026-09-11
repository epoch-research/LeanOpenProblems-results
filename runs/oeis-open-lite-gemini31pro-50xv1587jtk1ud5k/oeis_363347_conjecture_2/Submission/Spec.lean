import FormalConjectures.Util.ProblemImports
/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    if 2 ≤ k ∧ k ≤ n - 1 then
      if k = n - 1 then
        (k : ℚ) + (n : ℚ) / 4
      else
        let R_next := continued_fraction_denominator n (k + 1)
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs

open Rat Nat

def P_rev (n : ℕ) : ℕ → ℤ
| 0 => 4
| 1 => 5 * (n : ℤ) - 4
| i + 2 =>
  let k := (n : ℤ) - (i + 2)
  k * P_rev n (i + 1) - (k + 1) * P_rev n i

def P (n k : ℕ) : ℤ := P_rev n (n - k)

def D (n k : ℕ) : ℤ := (k - 1 : ℤ) * P n k - (k : ℤ) * (k - 2 : ℤ) * P n (k + 1)
lemma P_step (n k : ℕ) (hk : k + 2 ≤ n) :
  P n k = (k : ℤ) * P n (k + 1) - (k + 1 : ℤ) * P n (k + 2) := by
  unfold P
  have h1 : n - k = (n - k - 2) + 2 := by omega
  rw [h1, P_rev]
  have eq1 : ((n : ℤ) - ((n - k - 2 : ℕ) + 2 : ℤ)) = (k : ℤ) := by omega
  have eq3 : (n - k - 2) + 1 = n - (k + 1) := by omega
  have eq4 : n - k - 2 = n - (k + 2) := by omega
  rw [eq1, eq3, eq4]

lemma D_step (n k : ℕ) (hk : k + 2 ≤ n) :
  D n k = D n (k + 1) := by
  unfold D
  have : P n k = (k : ℤ) * P n (k + 1) - (k + 1 : ℤ) * P n (k + 2) := P_step n k hk
  rw [this]
  have h1 : ((k + 1 : ℕ) - 1 : ℤ) = (k : ℤ) := by omega
  have h2 : ((k + 1 : ℕ) - 2 : ℤ) = (k - 1 : ℤ) := by omega
  have h3 : k + 1 + 1 = k + 2 := by omega
  rw [h1, h2, h3]
  have hk1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
  rw [hk1]
  generalize P n (k + 1) = P1
  generalize P n (k + 2) = P2
  ring

lemma D_eq_d (n d k : ℕ) (hk : k + d = n - 2) : D n k = D n (n - 2) := by
  induction' d with d ih generalizing k
  · have : k = n - 2 := by omega
    rw [this]
  · have h1 : k + 2 ≤ n := by omega
    have h2 : (k + 1) + d = n - 2 := by omega
    have step := D_step n k h1
    rw [step]
    exact ih (k + 1) h2

lemma D_eq (n k : ℕ) (hk : k ≤ n - 2) : D n k = D n (n - 2) :=
  D_eq_d n (n - 2 - k) k (by omega)

lemma D_val (n : ℕ) (hn : 3 ≤ n) : D n (n - 2) = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := by
  unfold D
  have hn1 : n - (n - 2) = 2 := by omega
  have hn2 : n - (n - 2 + 1) = 1 := by omega
  have eq1 : P n (n - 2) = P_rev n 2 := by unfold P; rw [hn1]
  have eq2 : P n (n - 2 + 1) = P_rev n 1 := by unfold P; rw [hn2]
  rw [eq1, eq2]
  have hrev1 : P_rev n 1 = 5 * (n : ℤ) - 4 := by rfl
  have hrev2 : P_rev n 2 = (n - 2 : ℤ) * P_rev n 1 - ((n - 2 : ℤ) + 1) * P_rev n 0 := by rfl
  have hrev0 : P_rev n 0 = 4 := by rfl
  rw [hrev2, hrev1, hrev0]
  have hk1 : ((n - 2 : ℕ) - 1 : ℤ) = (n : ℤ) - 3 := by omega
  have hk2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  rw [hk1, hk2]
  ring




def fact : ℕ → ℤ
| 0 => 1
| n + 1 => (n + 1 : ℤ) * fact n

lemma fact_eq (n : ℕ) : fact n = (n.factorial : ℤ) := by
  induction' n with n ih
  · rfl
  · unfold fact; rw [ih]; rfl


lemma D_eq_all (n j : ℕ) (hn : 3 ≤ n) (hj2 : j ≤ n - 1) :
  D n j = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := by
  have H1 : j ≤ n - 2 ∨ j = n - 1 := by omega
  cases H1 with
  | inl hj =>
    rw [D_eq n j hj, D_val n hn]
  | inr hj =>
    rw [hj]
    have step := D_step n (n - 2) (by omega)
    have eq : n - 2 + 1 = n - 1 := by omega
    rw [eq] at step
    rw [← step, D_val n hn]

def fact_sum : ℕ → ℤ
| 0 => 0
| n + 1 => fact_sum n + fact n

def C (k : ℕ) : ℤ :=
  if k < 3 then 0 else ((k : ℤ) - 2) * fact_sum (k - 3)

lemma fact_sum_step (n : ℕ) : fact_sum (n + 1) = fact_sum n + fact n := rfl

lemma fact_step (n : ℕ) : fact (n + 1) = (n + 1 : ℤ) * fact n := rfl

lemma C_step (k : ℕ) (hk : 3 ≤ k) :
  (k - 1 : ℤ) * C k + fact (k - 1) = (k - 2 : ℤ) * C (k + 1) := by
  unfold C
  have hk1 : ¬(k < 3) := by omega
  have hk2 : ¬(k + 1 < 3) := by omega
  simp [hk1, hk2]
  have h1 : k - 2 = k - 3 + 1 := by omega
  rw [h1, fact_sum_step]
  have h2 : ((k : ℤ) + 1 - 2) = (k : ℤ) - 1 := by omega
  rw [h2]
  have hk3 : k - 1 = k - 3 + 1 + 1 := by omega
  have hk4 : k - 2 = k - 3 + 1 := by omega
  rw [hk3, fact_step, fact_step]
  have eq1 : ((k - 3 + 1 : ℕ) + 1 : ℤ) = (k : ℤ) - 1 := by omega
  have eq2 : ((k - 3 : ℕ) + 1 : ℤ) = (k : ℤ) - 2 := by omega
  rw [eq1, eq2]
  ring

lemma Ek_step (n k : ℕ) (hk1 : 3 ≤ k)
  (hD : (k - 1 : ℤ) * P n k - (k : ℤ) * (k - 2 : ℤ) * P n (k + 1) = (n : ℤ)^2 + 2 * (n : ℤ) - 4)
  (ih : 2 * (k - 2 : ℤ) * P n 3 - fact (k - 1) * P n k = C k * ((n : ℤ)^2 + 2 * (n : ℤ) - 4)) :
  2 * (k - 1 : ℤ) * P n 3 - fact k * P n (k + 1) = C (k + 1) * ((n : ℤ)^2 + 2 * (n : ℤ) - 4) := by
  have hc : (k - 2 : ℤ) * C (k + 1) = (k - 1 : ℤ) * C k + fact (k - 1) := by
    have := C_step k hk1
    omega
  have eq : fact k = (k : ℤ) * fact (k - 1) := by
    have h : k = k - 1 + 1 := by omega
    nth_rw 1 [h]
    rw [fact_step]
    have : ((k - 1 : ℕ) + 1 : ℤ) = (k : ℤ) := by omega
    rw [this]
  have mul_target : (k - 2 : ℤ) * (2 * (k - 1 : ℤ) * P n 3 - fact k * P n (k + 1)) = (k - 2 : ℤ) * C (k + 1) * ((n : ℤ)^2 + 2 * (n : ℤ) - 4) := by
    rw [hc, eq]
    linear_combination (k - 1 : ℤ) * ih + fact (k - 1) * hD
  have mul_target2 : (k - 2 : ℤ) * (2 * (k - 1 : ℤ) * P n 3 - fact k * P n (k + 1)) = (k - 2 : ℤ) * (C (k + 1) * ((n : ℤ)^2 + 2 * (n : ℤ) - 4)) := by
    rw [mul_target]
    ring
  have h_k_ne : (k - 2 : ℤ) ≠ 0 := by omega
  exact mul_left_cancel₀ h_k_ne mul_target2

lemma Ek_eq_d (n d k : ℕ) (hn : 3 ≤ n) (hk : k = 3 + d) (hkn : k ≤ n) :
  2 * (k - 2 : ℤ) * P n 3 - fact (k - 1) * P n k = C k * ((n : ℤ)^2 + 2 * (n : ℤ) - 4) := by
  induction' d with d ih generalizing k
  · have : k = 3 := by omega
    rw [this]
    have hc3 : C 3 = 0 := by
      unfold C
      simp
      rfl
    rw [hc3]
    have hf2 : fact (3 - 1) = 2 := by rfl
    rw [hf2]
    ring
  · have hk1 : k - 1 = 3 + d := by omega
    have hk1_ge : 3 ≤ k - 1 := by omega
    have hk1_le : k - 1 ≤ n - 1 := by omega
    have ih_val := ih (k - 1) hk1 (by omega)
    have hd_eq := D_eq_all n (k - 1) hn hk1_le
    unfold D at hd_eq
    have step := Ek_step n (k - 1) hk1_ge hd_eq ih_val
    have h_eq : (k - 1) + 1 = k := by omega
    have h_eq3 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    rw [h_eq] at step
    rw [h_eq3] at step
    have hr : (k : ℤ) - 1 - 1 = (k : ℤ) - 2 := by omega
    rw [hr] at step
    exact step


lemma Ek_eq (n : ℕ) (hn : 3 ≤ n) :
  2 * (n - 2 : ℤ) * P n 3 - fact (n - 1) * P n n = C n * ((n : ℤ)^2 + 2 * (n : ℤ) - 4) := by
  have hk : n = 3 + (n - 3) := by omega
  have hkn : n ≤ n := by omega
  exact Ek_eq_d n (n - 3) n hn hk hkn


lemma P2_eq (n : ℕ) (hn : 3 ≤ n) : P n 2 = (n : ℤ)^2 + 2 * (n : ℤ) - 4 := by
  have hd := D_eq_all n 2 hn (by omega)
  unfold D at hd
  have h_eq : ((2 : ℕ) - 1 : ℤ) = 1 := by omega
  have h_eq2 : ((2 : ℕ) - 2 : ℤ) = 0 := by omega
  have h_eq3 : ((2 : ℕ) : ℤ) = 2 := by omega
  rw [h_eq, h_eq2, h_eq3] at hd
  have : 1 * P n 2 - 2 * 0 * P n (2 + 1) = P n 2 := by ring
  rw [this] at hd
  exact hd



lemma P_pos (n d k : ℕ) (hn : 3 ≤ n) (hk : k + d = n) (hk2 : 2 ≤ k) :
  0 < P n k := by
  induction' d with d ih generalizing k
  · have : k = n := by omega
    rw [this]
    unfold P
    have : n - n = 0 := by omega
    rw [this]
    have h : P_rev n 0 = 4 := rfl
    rw [h]
    omega
  · have hk1_le : k + 1 + d = n := by omega
    have hk1_ge : 2 ≤ k + 1 := by omega
    have step := ih (k + 1) hk1_le hk1_ge
    have hd_eq := D_eq_all n k hn (by omega)
    unfold D at hd_eq
    have h_pos : 0 < (n : ℤ)^2 + 2 * (n : ℤ) - 4 := by
      have : 3 ≤ (n : ℤ) := by exact_mod_cast hn
      nlinarith
    have h_k_ge : 0 ≤ (k : ℤ) * (k - 2 : ℤ) := by
      have : 2 ≤ (k : ℤ) := by exact_mod_cast hk2
      nlinarith
    have h_k1_pos : 0 < P n (k + 1) := step
    have : 0 < (k - 1 : ℤ) * P n k := by
      calc 0 < (n : ℤ)^2 + 2 * (n : ℤ) - 4 := h_pos
           _ = (k - 1 : ℤ) * P n k - (k : ℤ) * (k - 2 : ℤ) * P n (k + 1) := hd_eq.symm
           _ ≤ (k - 1 : ℤ) * P n k := by
             have H : 0 ≤ (k : ℤ) * (k - 2 : ℤ) * P n (k + 1) := mul_nonneg h_k_ge (le_of_lt h_k1_pos)
             linarith
    have hk_gt : 0 < (k - 1 : ℤ) := by
      have : 2 ≤ (k : ℤ) := by exact_mod_cast hk2
      omega
    exact pos_of_mul_pos_right this (le_of_lt hk_gt)

lemma continued_fraction_denominator_eq_d (n d k : ℕ) (hn : 3 ≤ n) (hk : k + d = n - 1) (hk2 : 2 ≤ k) :
  continued_fraction_denominator n k = (P n k : ℚ) / (P n (k + 1) : ℚ) := by
  induction' d with d ih generalizing k
  · have : k = n - 1 := by omega
    rw [this]
    unfold continued_fraction_denominator
    have hn2 : ¬ (n ≤ 2) := by omega
    have hkn1 : 2 ≤ n - 1 ∧ n - 1 ≤ n - 1 := by omega
    have hkn2 : n - 1 = n - 1 := rfl
    simp [hn2, hkn1]
    have eq1 : P n (n - 1) = P_rev n 1 := by
      unfold P
      have h : n - (n - 1) = 1 := by omega
      rw [h]
    have eq2 : P n (n - 1 + 1) = P_rev n 0 := by
      unfold P
      have h : n - (n - 1 + 1) = 0 := by omega
      rw [h]
    rw [eq1, eq2]
    have hrev1 : P_rev n 1 = 5 * (n : ℤ) - 4 := rfl
    have hrev0 : P_rev n 0 = 4 := rfl
    rw [hrev1, hrev0]
    have hn_sub : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by exact Nat.cast_sub (by omega)
    rw [hn_sub]
    push_cast
    ring
  · have hk1_le : k + 1 ≤ n - 1 := by omega
    have hk1_ge : 2 ≤ k + 1 := by omega
    have step := ih (k + 1) (by omega) hk1_ge
    unfold continued_fraction_denominator
    have hn2 : ¬ (n ≤ 2) := by omega
    have hkn1 : 2 ≤ k ∧ k ≤ n - 1 := by omega
    have hkn2 : k ≠ n - 1 := by omega
    simp [hn2, hkn1, hkn2]
    rw [step]
    have hp_step : P n k = (k : ℤ) * P n (k + 1) - (k + 1 : ℤ) * P n (k + 2) := P_step n k (by omega)
    have hp_step_q : (P n k : ℚ) = (k : ℚ) * (P n (k + 1) : ℚ) - (k + 1 : ℚ) * (P n (k + 2) : ℚ) := by
      exact_mod_cast hp_step
    rw [hp_step_q]
    have hP_pos : 0 < P n (k + 1) := P_pos n (n - (k + 1)) (k + 1) hn (by omega) hk1_ge
    have hP_nz : (P n (k + 1) : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hP_pos
    have hP2_pos : 0 < P n (k + 2) := P_pos n (n - (k + 2)) (k + 2) hn (by omega) (by omega)
    have hP2_nz : (P n (k + 2) : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hP2_pos
    rw [div_div_eq_mul_div]
    have h_sub : (k : ℚ) - (k + 1 : ℚ) * (P n (k + 2) : ℚ) / (P n (k + 1) : ℚ) = ((k : ℚ) * (P n (k + 1) : ℚ) - (k + 1 : ℚ) * (P n (k + 2) : ℚ)) / (P n (k + 1) : ℚ) := by
      calc (k : ℚ) - (k + 1 : ℚ) * (P n (k + 2) : ℚ) / (P n (k + 1) : ℚ)
        _ = (k : ℚ) * (P n (k + 1) : ℚ) / (P n (k + 1) : ℚ) - (k + 1 : ℚ) * (P n (k + 2) : ℚ) / (P n (k + 1) : ℚ) := by
          rw [mul_div_cancel_right₀ _ hP_nz]
        _ = ((k : ℚ) * (P n (k + 1) : ℚ) - (k + 1 : ℚ) * (P n (k + 2) : ℚ)) / (P n (k + 1) : ℚ) := by
          rw [sub_div]
    rw [h_sub]

lemma continued_fraction_denominator_eq (n k : ℕ) (hn : 3 ≤ n) (hk1 : 2 ≤ k) (hk2 : k ≤ n - 1) :
  continued_fraction_denominator n k = (P n k : ℚ) / (P n (k + 1) : ℚ) :=
  continued_fraction_denominator_eq_d n (n - 1 - k) k hn (by omega) hk1


lemma num_div (A B : ℤ) (hB : 0 < B) : ((A : ℚ) / (B : ℚ)).num = A / (A.gcd B : ℤ) := by
  rw [← Rat.divInt_eq_div]
  rw [Rat.num_divInt]
  have hb : B.sign = 1 := Int.sign_eq_one_of_pos hB
  rw [hb]
  have hgcd : (B.gcd A : ℤ) = (A.gcd B : ℤ) := by rw [Int.gcd_comm]
  rw [hgcd]
  rw [one_mul]

lemma A363347_eq (n : ℕ) (hn : 3 ≤ n) :
  (A363347 n : ℤ) = P n 2 / (P n 2).gcd (P n 3) := by
  unfold A363347
  have hn2 : ¬ (n ≤ 2) := by omega
  simp [hn2]
  have r2_eq := continued_fraction_denominator_eq n 2 hn (by omega) (by omega)
  rw [r2_eq]
  have hP3_pos : 0 < P n 3 := P_pos n (n - 3) 3 hn (by omega) (by omega)
  have hP2_pos : 0 < P n 2 := P_pos n (n - 2) 2 hn (by omega) (by omega)
  have eq_num := num_div (P n 2) (P n 3) hP3_pos
  rw [eq_num]
  have h_gcd : 0 < ((P n 2).gcd (P n 3) : ℤ) := by
    have h1 : (P n 2).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hP2_pos)
    have : 0 < (P n 2).gcd (P n 3) := Nat.gcd_pos_of_pos_left (P n 3).natAbs (Nat.pos_of_ne_zero h1)
    exact_mod_cast this
  apply abs_of_nonneg
  exact Int.ediv_nonneg (le_of_lt hP2_pos) (le_of_lt h_gcd)



lemma qr (p : ℕ) [Fact p.Prime] (hp : p % 10 = 1 ∨ p % 10 = 9) :
  ∃ x : ZMod p, x^2 = 5 := by
  have hp2 : p ≠ 2 := by rintro rfl; revert hp; decide
  have hp5 : p ≠ 5 := by rintro rfl; revert hp; decide
  have hq2 : 5 ≠ 2 := by decide
  have h_fact5 : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h_recip := legendreSym.quadratic_reciprocity (p := p) (q := 5) hp2 hq2 hp5
  have h_pow : (-1 : ℤ) ^ (p / 2 * (5 / 2)) = 1 := by
    have : 5 / 2 = 2 := by rfl
    rw [this]
    have eq_mul : p / 2 * 2 = 2 * (p / 2) := by ring
    rw [eq_mul]
    have h_pow2 : (-1 : ℤ) ^ (2 * (p / 2)) = ((-1 : ℤ) ^ 2) ^ (p / 2) := by exact pow_mul (-1) 2 (p / 2)
    rw [h_pow2]
    norm_num
  rw [h_pow] at h_recip
  have h_leg5_p : legendreSym 5 (p : ℤ) = 1 := by
    have hp5_mod : (p : ℤ) % 5 = 1 ∨ (p : ℤ) % 5 = 4 := by
      have h1 : (p : ℤ) % 10 = 1 ∨ (p : ℤ) % 10 = 9 := by exact_mod_cast hp
      omega
    rw [legendreSym.mod 5 p]
    change legendreSym 5 ((p : ℤ) % 5) = 1
    cases hp5_mod with
    | inl h => rw [h]; rfl
    | inr h => rw [h]; rfl
  have h_leg_p_5 : legendreSym p 5 = 1 := by
    rw [h_leg5_p, one_mul] at h_recip
    exact h_recip
  have h_nz : ((5 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have : (p : ℤ) ∣ 5 := (ZMod.intCast_zmod_eq_zero_iff_dvd 5 p).mp h
    have : p ∣ 5 := by exact_mod_cast this
    have hle : p ≤ 5 := Nat.le_of_dvd (by decide) this
    have hp_pos : p > 0 := Nat.Prime.pos Fact.out
    have hp_not_1 : p ≠ 1 := Nat.Prime.ne_one Fact.out
    revert hle
    cases hp with
    | inl h1 =>
      have : p % 10 = 1 := h1
      have eq : p = 10 * (p / 10) + p % 10 := (Nat.div_add_mod p 10).symm
      rw [this] at eq
      have : p / 10 > 0 := by
        by_contra hc
        have : p / 10 = 0 := by omega
        rw [this] at eq
        have : p = 1 := by omega
        exact hp_not_1 this
      omega
    | inr h9 =>
      have : p % 10 = 9 := h9
      have eq : p = 10 * (p / 10) + p % 10 := (Nat.div_add_mod p 10).symm
      rw [this] at eq
      omega
  have h_eq_one_iff := legendreSym.eq_one_iff p h_nz
  rw [h_eq_one_iff] at h_leg_p_5
  rcases h_leg_p_5 with ⟨y, hy⟩
  use y
  have h_5 : ((5 : ℤ) : ZMod p) = 5 := by exact Int.cast_ofNat 5
  rw [h_5] at hy
  have : y ^ 2 = y * y := by exact sq y
  rw [this]
  exact hy.symm

lemma p_ge_11 (p : ℕ) [Fact p.Prime] (hp : p % 10 = 1 ∨ p % 10 = 9) : 11 ≤ p := by
  have : p ≠ 1 := Nat.Prime.ne_one Fact.out
  have hp_prime : p.Prime := Fact.out
  have : p ≠ 9 := by rintro rfl; revert hp_prime; decide
  have eq : 10 * (p / 10) + p % 10 = p := Nat.div_add_mod p 10
  cases hp with
  | inl h => omega
  | inr h => omega

lemma mod_sum (p n1 n2 : ℕ) [Fact p.Prime] (y : ZMod p)
  (hn1 : n1 = (y - 1).val) (hn2 : n2 = (- (y - 1) - 2).val) :
  (n1 + n2) % p = p - 2 := by
  have hp_ge : 2 ≤ p := Nat.Prime.two_le Fact.out
  have h_val : ((n1 + n2 : ℕ) : ZMod p) = -2 := by
    push_cast
    rw [hn1, hn2]
    have eq1 : (((y - 1).val : ℕ) : ZMod p) = y - 1 := ZMod.natCast_zmod_val (y - 1)
    have eq2 : (((-(y - 1) - 2).val : ℕ) : ZMod p) = -(y - 1) - 2 := ZMod.natCast_zmod_val (-(y - 1) - 2)
    rw [eq1, eq2]
    ring
  have h_eq : (((n1 + n2) % p : ℕ) : ZMod p) = ((p - 2 : ℕ) : ZMod p) := by
    have h1 : (((n1 + n2) % p : ℕ) : ZMod p) = ((n1 + n2 : ℕ) : ZMod p) := by
      exact ZMod.natCast_mod (n1 + n2) p
    rw [h1, h_val]
    have eqp2 : ((p - 2 : ℕ) : ℤ) = (p : ℤ) - 2 := by omega
    have h2 : (((p - 2 : ℕ) : ZMod p)) = (((p - 2 : ℕ) : ℤ) : ZMod p) := by exact_mod_cast rfl
    rw [h2, eqp2]
    push_cast
    have : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
    rw [this]
    ring
  have h_val_eq : (((n1 + n2) % p : ℕ) : ZMod p).val = ((p - 2 : ℕ) : ZMod p).val := by rw [h_eq]
  have h1 : (((n1 + n2) % p : ℕ) : ZMod p).val = (n1 + n2) % p % p := ZMod.val_natCast p ((n1 + n2) % p)
  have h2 : ((p - 2 : ℕ) : ZMod p).val = (p - 2) % p := ZMod.val_natCast p (p - 2)
  rw [h1, h2] at h_val_eq
  have h3 : (n1 + n2) % p % p = (n1 + n2) % p := Nat.mod_mod _ _
  have h4 : (p - 2) % p = p - 2 := Nat.mod_eq_of_lt (by omega)
  rw [h3, h4] at h_val_eq
  exact h_val_eq

lemma root_exists_small (p : ℕ) [Fact p.Prime] (hp : p % 10 = 1 ∨ p % 10 = 9) :
  ∃ n : ℕ, n ≤ p / 2 ∧ ((n : ℤ)^2 + 2*(n : ℤ) - 4) % p = 0 := by
  have ⟨y, hy⟩ := qr p hp
  have h_root1 : (y - 1)^2 + 2*(y - 1) - 4 = 0 := by
    calc (y - 1)^2 + 2*(y - 1) - 4
      _ = y^2 - 2*y + 1 + 2*y - 2 - 4 := by ring
      _ = y^2 - 5 := by ring
      _ = 5 - 5 := by rw [hy]
      _ = 0 := by ring
  have h_root2 : (- (y - 1) - 2)^2 + 2*(- (y - 1) - 2) - 4 = 0 := by
    calc (- (y - 1) - 2)^2 + 2*(- (y - 1) - 2) - 4
      _ = (y - 1)^2 + 4*(y - 1) + 4 - 2*(y - 1) - 4 - 4 := by ring
      _ = (y - 1)^2 + 2*(y - 1) - 4 := by ring
      _ = 0 := h_root1
  let n1 := (y - 1).val
  let n2 := (- (y - 1) - 2).val
  have hn1_eq : (n1 : ZMod p) = y - 1 := ZMod.natCast_zmod_val _
  have hn2_eq : (n2 : ZMod p) = - (y - 1) - 2 := ZMod.natCast_zmod_val _
  have hn1_lt : n1 < p := ZMod.val_lt _
  have hn2_lt : n2 < p := ZMod.val_lt _
  have hp_ge : 11 ≤ p := p_ge_11 p hp
  have eq_mod : (n1 + n2) % p = p - 2 := mod_sum p n1 n2 y rfl rfl
  have h_sum_val : n1 + n2 = p - 2 ∨ n1 + n2 = 2 * p - 2 := by
    have h1 : n1 + n2 < 2 * p := by omega
    have div_eq : p * ((n1 + n2) / p) + p - 2 = n1 + n2 := by
      have h3 := Nat.div_add_mod (n1 + n2) p
      rw [eq_mod] at h3
      omega
    have h_lt2 : (n1 + n2) / p < 2 := by
      by_contra hc
      have h4 : (n1 + n2) / p ≥ 2 := by omega
      have h5 : p * 2 ≤ p * ((n1 + n2) / p) := Nat.mul_le_mul_left p h4
      have h7 : p * 2 + p - 2 ≤ n1 + n2 := by
        calc p * 2 + p - 2 ≤ p * ((n1 + n2) / p) + p - 2 := by omega
             _ = n1 + n2 := div_eq
      omega
    match h : (n1 + n2) / p with
    | 0 => left; rw [h] at div_eq; omega
    | 1 => right; rw [h] at div_eq; omega
    | x + 2 => exfalso; omega
  have h_sum_not_2p : n1 + n2 ≠ 2 * p - 2 := by
    intro h
    have hn1 : n1 = p - 1 := by omega
    have hn1_z : (n1 : ZMod p) = -1 := by
      have eqp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
      have eqp2 : ((n1 : ℕ) : ZMod p) = (((p - 1 : ℕ) : ℤ) : ZMod p) := by
        rw [hn1]
        exact_mod_cast rfl
      rw [eqp2, eqp1]
      push_cast
      have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
      rw [hp0]
      ring
    rw [hn1_z] at hn1_eq
    have hy0 : y = 0 := by
      calc y = y - 1 + 1 := by ring
           _ = -1 + 1 := by rw [← hn1_eq]
           _ = 0 := by ring
    have hy0_sq : y^2 = 0 := by rw [hy0]; ring
    rw [hy] at hy0_sq
    have h5 : ((5 : ℤ) : ZMod p) = 0 := by exact_mod_cast hy0_sq
    have hdvd : (p : ℤ) ∣ 5 := (ZMod.intCast_zmod_eq_zero_iff_dvd 5 p).mp h5
    have hp5 : p ∣ 5 := by exact_mod_cast hdvd
    have hle : p ≤ 5 := Nat.le_of_dvd (by decide) hp5
    omega
  have h_sum_fin : n1 + n2 = p - 2 := by
    cases h_sum_val with
    | inl h => exact h
    | inr h => exfalso; exact h_sum_not_2p h
  let n := min n1 n2
  use n
  have hn_le : n ≤ p / 2 := by
    have : 2 * n ≤ n1 + n2 := by
      calc 2 * n = n + n := by ring
           _ ≤ n1 + n2 := by exact Nat.add_le_add (Nat.min_le_left n1 n2) (Nat.min_le_right n1 n2)
    rw [h_sum_fin] at this
    omega
  have h_root : ((n : ℤ)^2 + 2*(n : ℤ) - 4) % p = 0 := by
    have hn_cases : n = n1 ∨ n = n2 := by
      if h : n1 ≤ n2 then
        have h_min : min n1 n2 = n1 := Nat.min_eq_left h
        exact Or.inl h_min
      else
        have h2 : n2 ≤ n1 := by omega
        have h_min : min n1 n2 = n2 := Nat.min_eq_right h2
        exact Or.inr h_min
    cases hn_cases with
    | inl h1 =>
      have h_eq : (n : ZMod p)^2 + 2*(n : ZMod p) - 4 = 0 := by
        rw [h1, hn1_eq]
        exact h_root1
      have h_eq3 : (((n : ℤ)^2 + 2*(n : ℤ) - 4 : ℤ) : ZMod p) = 0 := by
        push_cast
        exact h_eq
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ)^2 + 2*(n : ℤ) - 4) p).mp h_eq3 |> Int.dvd_iff_emod_eq_zero.mp
    | inr h2 =>
      have h_eq : (n : ZMod p)^2 + 2*(n : ZMod p) - 4 = 0 := by
        rw [h2, hn2_eq]
        exact h_root2
      have h_eq3 : (((n : ℤ)^2 + 2*(n : ℤ) - 4 : ℤ) : ZMod p) = 0 := by
        push_cast
        exact h_eq
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ)^2 + 2*(n : ℤ) - 4) p).mp h_eq3 |> Int.dvd_iff_emod_eq_zero.mp
  exact ⟨hn_le, h_root⟩


lemma p2_nat (n : ℕ) (hn : 3 ≤ n) : ((n : ℤ)^2 + 2*(n : ℤ) - 4) = ((n^2 + 2*n - 4 : ℕ) : ℤ) := by
  have h4 : 4 ≤ n^2 + 2*n := by nlinarith
  have h_eq : ((n : ℤ)^2 + 2*(n : ℤ)) = ((n^2 + 2*n : ℕ) : ℤ) := by push_cast; rfl
  rw [h_eq]
  generalize n^2 + 2*n = K at h4 ⊢
  omega

lemma m_exists (p n : ℕ) (hn : 3 ≤ n) (h_root : ((n : ℤ)^2 + 2*(n : ℤ) - 4) % p = 0) :
  ∃ m : ℕ, n^2 + 2*n = p * m + 4 := by
  have hp2 := p2_nat n hn
  have h_mod : ((n^2 + 2*n - 4 : ℕ) : ℤ) % (p : ℤ) = 0 := by
    rw [← hp2]
    exact h_root
  have h_dvd : (p : ℤ) ∣ ((n^2 + 2*n - 4 : ℕ) : ℤ) := Int.dvd_of_emod_eq_zero h_mod
  have h_dvd_nat : p ∣ (n^2 + 2*n - 4) := by exact_mod_cast h_dvd
  rcases h_dvd_nat with ⟨m, hm⟩
  use m
  have h4 : 4 ≤ n^2 + 2*n := by nlinarith
  generalize n^2 + 2*n = K at h4 hm ⊢
  have h_eq : K - 4 = p * m := hm
  omega

lemma m_lt_n (p n m : ℕ) (hn_le : n ≤ p / 2) (hm : n^2 + 2*n = p * m + 4) :
  m < n := by
  by_contra hc
  have h_m_ge : m ≥ n := by omega
  have h1 : p * m ≥ p * n := Nat.mul_le_mul_left p h_m_ge
  have h2 : n^2 + 2*n ≥ p * n + 4 := by omega
  have h3 : p * n ≥ 2 * n * n := by
    have : 2 * n ≤ p := by omega
    have h_mul : 2 * n * n ≤ p * n := Nat.mul_le_mul_right n this
    omega
  have h4 : n^2 + 2*n ≥ 2 * n^2 + 4 := by
    calc n^2 + 2*n ≥ p * n + 4 := h2
         _ ≥ 2 * n * n + 4 := by omega
         _ = 2 * n^2 + 4 := by ring
  nlinarith

lemma Pnn_eq (n : ℕ) : P n n = 4 := by
  unfold P
  have : n - n = 0 := by omega
  rw [this]
  rfl




lemma gcd_m (p m P2 P3 : ℕ) (hp_prime : p.Prime) (hP2 : P2 = p * m)
  (h_not_dvd : ¬ ((p : ℤ) ∣ (P3 : ℤ))) (h_m_dvd : m ∣ P3) :
  P2.gcd P3 = m := by
  have hdvd1 : m ∣ P2 := by rw [hP2]; exact dvd_mul_left m p
  have hdvd2 : m ∣ P3 := h_m_dvd
  have h_m_div_gcd : m ∣ P2.gcd P3 := Nat.dvd_gcd hdvd1 hdvd2
  have h_gcd_div_P2 : P2.gcd P3 ∣ p * m := by
    have h1 : P2.gcd P3 ∣ P2 := Nat.gcd_dvd_left P2 P3
    rw [hP2] at h1 ⊢
    exact h1
  have h_gcd_coprime : (P2.gcd P3).Coprime p := by
    have hdvd_p : (P2.gcd P3).gcd p ∣ p := Nat.gcd_dvd_right _ _
    have h_prime_dvd := Nat.Prime.eq_one_or_self_of_dvd hp_prime _ hdvd_p
    rcases h_prime_dvd with h1 | hp_eq
    · exact h1
    · exfalso
      have h_p_dvd_gcd : p ∣ P2.gcd P3 := by
        have : (P2.gcd P3).gcd p = p := hp_eq
        exact this ▸ Nat.gcd_dvd_left _ _
      have h_p_dvd_P3 : p ∣ P3 := Nat.dvd_trans h_p_dvd_gcd (Nat.gcd_dvd_right P2 P3)
      have : (p : ℤ) ∣ (P3 : ℤ) := by exact_mod_cast h_p_dvd_P3
      exact h_not_dvd this
  have h_gcd_div_P2_comm : P2.gcd P3 ∣ m * p := by
    have eq : p * m = m * p := mul_comm p m
    rw [← eq]
    exact h_gcd_div_P2
  have h_gcd_div_m : P2.gcd P3 ∣ m := by
    exact Nat.Coprime.dvd_of_dvd_mul_right h_gcd_coprime h_gcd_div_P2_comm
  exact Nat.dvd_antisymm h_gcd_div_m h_m_div_gcd

lemma my_A363347_eq (n p m P_n_3 P_n_2 : ℕ) (hn : 3 ≤ n) (hp_prime : p.Prime)
  (hm : n^2 + 2*n = p * m + 4)
  (h_not_dvd : ¬ ((p : ℤ) ∣ P_n_3)) (hm_dvd : m ∣ P_n_3) (h_P2 : P_n_2 = p * m) :
  P_n_2 / P_n_2.gcd P_n_3 = p := by
  have h_gcd := gcd_m p m P_n_2 P_n_3 hp_prime h_P2 h_not_dvd hm_dvd
  rw [h_gcd]
  rw [h_P2]
  have h_m_pos : m > 0 := by
    by_contra hc
    have h_m0 : m = 0 := by omega
    rw [h_m0] at hm
    have h4 : p * 0 + 4 = 4 := by ring
    rw [h4] at hm
    have : n < 2 := by nlinarith
    omega
  exact Nat.mul_div_cancel p h_m_pos





lemma P_rev_step (n i : ℕ) : P_rev n (i + 2) = ((n : ℤ) - ↑(i + 2)) * P_rev n (i + 1) - (((n : ℤ) - ↑(i + 2)) + 1) * P_rev n i := rfl

lemma P_rev_2 (n : ℕ) : P_rev n 2 = ((n : ℤ) - 2) * (5 * (n : ℤ) - 4) - (((n : ℤ) - 2) + 1) * 4 := by
  have h_eq : 2 = 0 + 2 := rfl
  rw [h_eq, P_rev_step]
  have h_rev0 : P_rev n 0 = 4 := rfl
  have h_rev1 : P_rev n 1 = 5 * (n : ℤ) - 4 := rfl
  rw [h_rev0, h_rev1]
  push_cast
  ring

lemma P_rev_3 (n : ℕ) : P_rev n 3 = ((n : ℤ) - 3) * P_rev n 2 - (((n : ℤ) - 3) + 1) * (5 * (n : ℤ) - 4) := by
  have h_eq : 3 = 1 + 2 := rfl
  rw [h_eq, P_rev_step]
  have h_rev1 : P_rev n 1 = 5 * (n : ℤ) - 4 := rfl
  have h_rev2 : P_rev n 2 = P_rev n (0 + 2) := rfl
  rw [h_rev1]
  push_cast
  ring

lemma P_rev_mult_4 (n : ℕ) (x : ℤ) (hn : (n : ℤ) = 2 * x) :
  ∀ i, i ≠ 1 → ∃ c : ℤ, P_rev n i = 4 * c := by
  intro i
  induction' i using Nat.strong_induction_on with i ih
  intro h_not_1
  rcases i with _ | _ | _ | _ | j
  · use 1; rfl
  · contradiction
  · use 5*x^2 - 9*x + 3
    rw [P_rev_2, hn]
    ring
  · use 10*x^3 - 38*x^2 + 40*x - 11
    rw [P_rev_3, P_rev_2, hn]
    ring
  · have hi1 : j + 3 < j + 4 := Nat.lt_succ_self _
    have hi2 : j + 2 < j + 4 := Nat.lt_trans (Nat.lt_succ_self _) hi1
    have hn1 : j + 3 ≠ 1 := by omega
    have hn2 : j + 2 ≠ 1 := by omega
    have h1 := ih (j+3) hi1 hn1
    have h2 := ih (j+2) hi2 hn2
    rcases h1 with ⟨c1, hc1⟩
    rcases h2 with ⟨c2, hc2⟩
    have h_eq_j : j + 1 + 1 + 1 + 1 = j + 4 := by omega
    rw [h_eq_j]
    have h_step : P_rev n (j + 4) = ((n : ℤ) - (j + 4)) * P_rev n (j + 3) - (((n : ℤ) - (j + 4)) + 1) * P_rev n (j + 2) := by
      have h : j + 4 = (j + 2) + 2 := by omega
      rw [h, P_rev_step]
      push_cast
      ring
    rw [h_step, hc1, hc2]
    use ((n : ℤ) - (j + 4)) * c1 - (((n : ℤ) - (j + 4)) + 1) * c2
    ring

lemma P3_mult_4 (n : ℕ) (x : ℤ) (hn : (n : ℤ) = 2 * x) (hn_ge : 3 ≤ n) :
  ∃ c : ℤ, P n 3 = 4 * c := by
  unfold P
  by_cases h : n - 3 = 1
  · have hn4 : n = 4 := by omega
    use 4
    have h_prev : P_rev n (n - 3) = P_rev 4 1 := by rw [h, hn4]
    rw [h_prev]
    rfl
  · apply P_rev_mult_4 n x hn
    exact h


lemma p_not_div_p3 (n p m : ℕ) (hp : p.Prime) (hp_ge : 11 ≤ p)
  (hn_ge : 3 ≤ n) (hn_le : n ≤ p / 2)
  (P3 : ℤ)
  (C_n : ℤ)
  (h_eq : 2 * (n - 2 : ℤ) * P3 - 4 * ((n - 1).factorial : ℤ) = C_n * m * p) :
  ¬ ((p : ℤ) ∣ P3) := by
  intro h
  rcases h with ⟨k, hk⟩
  have : (p : ℤ) ∣ 4 * (n - 1).factorial := by
    have h1 : 4 * ((n - 1).factorial : ℤ) = p * (2 * (n - 2 : ℤ) * k - C_n * m) := by
      have h_eq2 : 4 * ((n - 1).factorial : ℤ) = 2 * (n - 2 : ℤ) * P3 - C_n * m * p := by linarith
      rw [h_eq2, hk]
      ring
    exact ⟨2 * (n - 2 : ℤ) * k - C_n * m, h1⟩
  have hdvd : p ∣ 4 * (n - 1).factorial := by exact_mod_cast this
  have h_prime_dvd := (Nat.Prime.dvd_mul hp).mp hdvd
  rcases h_prime_dvd with h4 | hfact
  · have : p ≤ 4 := Nat.le_of_dvd (by decide) h4
    omega
  · have h_le : p ≤ n - 1 := (Nat.Prime.dvd_factorial hp).mp hfact
    omega


lemma odd_x_sq_x_minus_1 (x : ℤ) : ¬ 2 ∣ x^2 + x - 1 := by
  intro h
  have h1 : 2 ∣ x * (x + 1) := by
    by_cases hx : 2 ∣ x
    · rcases hx with ⟨k, hk⟩; use k * (x + 1); rw [hk]; ring
    · have hx2 : 2 ∣ x + 1 := by omega
      rcases hx2 with ⟨k, hk⟩; use x * k; rw [hk]; ring
  have h2 : 2 ∣ (x^2 + x) := by
    have : x^2 + x = x * (x + 1) := by ring
    rw [this]; exact h1
  have h3 : 2 ∣ (x^2 + x) - (x^2 + x - 1) := dvd_sub h2 h
  have : (x^2 + x) - (x^2 + x - 1) = 1 := by ring
  rw [this] at h3
  revert h3
  omega

lemma m_mprime (m p x : ℤ) (hp : ¬ 2 ∣ p)
  (h : m * p = 4 * (x^2 + x - 1)) :
  ∃ m' : ℤ, m = 4 * m' ∧ ¬ 2 ∣ m' := by
  have hdvd4 : 4 ∣ p * m := by
    have : p * m = 4 * (x^2 + x - 1) := by linarith
    exact ⟨x^2 + x - 1, this⟩
  have h_p_coprime : IsCoprime 4 p := by
    have h_mod4 : p % 4 = 1 ∨ p % 4 = 3 ∨ p % 4 = -1 ∨ p % 4 = -3 := by omega
    rcases h_mod4 with h4 | h4 | h4 | h4
    · use -(p / 4), 1; omega
    · use -(3 * (p / 4) + 2), 3; omega
    · use -(p / 4), -1; omega
    · use -(3 * (p / 4) - 2), -3; omega
  have hdvd_m : 4 ∣ m := IsCoprime.dvd_of_dvd_mul_left h_p_coprime hdvd4
  rcases hdvd_m with ⟨m', hm'⟩
  use m'
  constructor
  · exact hm'
  · intro h2
    have : 8 ∣ m := by
      rcases h2 with ⟨k, hk⟩
      use k
      rw [hm', hk]
      ring
    rcases this with ⟨k, hk⟩
    have h_sub : 8 * k * p = 4 * (x^2 + x - 1) := by
      calc
        8 * k * p = m * p := by rw [hk]
        _ = 4 * (x^2 + x - 1) := h
    have h_div : 2 * k * p = x^2 + x - 1 := by linarith
    have h_even : 2 ∣ x^2 + x - 1 := by use k * p; linarith
    exact odd_x_sq_x_minus_1 x h_even

lemma m_div_8p3 (n m : ℕ) (P3 : ℤ)
  (h_m_P2 : (m : ℤ) ∣ (n : ℤ)^2 + 2*(n : ℤ) - 4)
  (h_m_2P3 : (m : ℤ) ∣ 2 * ((n : ℤ) - 2) * P3) :
  (m : ℤ) ∣ 8 * P3 := by
  have h1 : 8 * P3 = 2 * P3 * ((n : ℤ)^2 + 2*(n : ℤ) - 4) - (n + 4 : ℤ) * (2 * ((n : ℤ) - 2) * P3) := by
    ring
  rw [h1]
  apply _root_.dvd_sub
  · exact dvd_mul_of_dvd_right h_m_P2 _
  · exact dvd_mul_of_dvd_right h_m_2P3 _

lemma m_div_p3_even (m P3 c m' : ℤ)
  (h1 : m = 4 * m')
  (h2 : P3 = 4 * c)
  (h3 : ¬ 2 ∣ m')
  (h4 : m ∣ 8 * P3) :
  m ∣ P3 := by
  have hdvd : m' ∣ 8 * c := by
    rcases h4 with ⟨k, hk⟩
    rw [h1, h2] at hk
    have : 4 * (m' * k) = 4 * (8 * c) := by linarith
    have h_cancel : m' * k = 8 * c := by linarith
    use k
    rw [h_cancel]
  have h_coprime : IsCoprime m' 8 := by
    have h_mod : m' % 8 = 1 ∨ m' % 8 = 3 ∨ m' % 8 = 5 ∨ m' % 8 = 7 := by
      have : m' % 2 ≠ 0 := by intro hc; apply h3; exact ⟨m' / 2, by omega⟩
      omega
    rcases h_mod with h | h | h | h
    · use 1, -(m' / 8); omega
    · use 3, -(3 * (m' / 8) + 1); omega
    · use 5, -(5 * (m' / 8) + 3); omega
    · use 7, -(7 * (m' / 8) + 6); omega
  have hdvd2 : m' ∣ c := by
    exact IsCoprime.dvd_of_dvd_mul_left h_coprime hdvd
  rcases hdvd2 with ⟨k, hk⟩
  use k
  rw [h1, h2, hk]
  ring

lemma m_div_p3_odd (m P3 : ℤ)
  (h3 : ¬ 2 ∣ m)
  (h4 : m ∣ 8 * P3) :
  m ∣ P3 := by
  have h_coprime : IsCoprime m 8 := by
    have h_mod : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by
      have : m % 2 ≠ 0 := by intro hc; apply h3; exact ⟨m / 2, by omega⟩
      omega
    rcases h_mod with h | h | h | h
    · use 1, -(m / 8); omega
    · use 3, -(3 * (m / 8) + 1); omega
    · use 5, -(5 * (m / 8) + 3); omega
    · use 7, -(7 * (m / 8) + 6); omega
  exact IsCoprime.dvd_of_dvd_mul_left h_coprime h4

lemma m_div_p3_main (n m p : ℕ) (P3 : ℤ) (hp : ¬ 2 ∣ (p : ℤ))
  (hm_eq : (n : ℤ)^2 + 2*(n : ℤ) - 4 = (m : ℤ) * p)
  (h_m_2P3 : (m : ℤ) ∣ 2 * ((n : ℤ) - 2) * P3)
  (h_P3_even : 2 ∣ (n : ℤ) → ∃ c, P3 = 4 * c) :
  (m : ℤ) ∣ P3 := by
  have h_m_P2 : (m : ℤ) ∣ (n : ℤ)^2 + 2*(n : ℤ) - 4 := ⟨p, hm_eq⟩
  have h_m_8P3 : (m : ℤ) ∣ 8 * P3 := m_div_8p3 n m P3 h_m_P2 h_m_2P3
  by_cases hn_even : 2 ∣ (n : ℤ)
  · rcases hn_even with ⟨x, hx⟩
    have hm_eq2 : (m : ℤ) * p = 4 * (x^2 + x - 1) := by
      calc
        (m : ℤ) * p = (n : ℤ)^2 + 2*(n : ℤ) - 4 := hm_eq.symm
        _ = (2 * x)^2 + 2*(2 * x) - 4 := by rw [hx]
        _ = 4 * (x^2 + x - 1) := by ring
    have h_mprime := m_mprime (m : ℤ) (p : ℤ) x hp hm_eq2
    rcases h_mprime with ⟨m', hm1, hm2⟩
    have h_c := h_P3_even ⟨x, hx⟩
    rcases h_c with ⟨c, hc⟩
    exact m_div_p3_even m P3 c m' hm1 hc hm2 h_m_8P3
  · have hm_odd : ¬ 2 ∣ (m : ℤ) := by
      intro h2
      have : 2 ∣ (m : ℤ) * p := by rcases h2 with ⟨k, hk⟩; use k * p; rw [hk]; ring
      have h_eq2 : (m : ℤ) * p = (n : ℤ)^2 + 2*(n : ℤ) - 4 := hm_eq.symm
      rw [h_eq2] at this
      have h_odd : ∃ k, (n : ℤ) = 2 * k + 1 := by
        have h_mod : (n : ℤ) % 2 = 1 ∨ (n : ℤ) % 2 = -1 := by omega
        rcases h_mod with h_mod | h_mod
        · use n / 2; omega
        · use (n / 2) - 1; omega
      rcases h_odd with ⟨k, hk⟩
      have : (n : ℤ)^2 + 2*(n : ℤ) - 4 = 2 * (2 * k^2 + 4 * k - 1) + 1 := by
        calc
          (n : ℤ)^2 + 2*(n : ℤ) - 4 = (2 * k + 1)^2 + 2*(2 * k + 1) - 4 := by rw [hk]
          _ = 2 * (2 * k^2 + 4 * k - 1) + 1 := by ring
      have h_even_n2 : 2 ∣ (n : ℤ)^2 + 2*(n : ℤ) - 4 := this ▸ ‹2 ∣ (n : ℤ)^2 + 2*(n : ℤ) - 4›
      revert h_even_n2
      omega
    exact m_div_p3_odd m P3 hm_odd h_m_8P3



/-- The conjecture. -/
@[AMS 11, category research solved]
theorem oeis_363347_conjecture_2
  (p : ℕ) (hp : Nat.Prime p)
  (h_mod : p % 10 = 1 ∨ p % 10 = 9) :
  ∃ n : ℕ, A363347 n = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_ge : 11 ≤ p := p_ge_11 p h_mod
  have h_root := root_exists_small p h_mod
  let n := Classical.choose h_root
  have h_root_props := Classical.choose_spec h_root
  have hn_le : n ≤ p / 2 := h_root_props.1
  have h_mod_0 : ((n : ℤ)^2 + 2*(n : ℤ) - 4) % p = 0 := h_root_props.2
  have hn_ge_3 : 3 ≤ n := by
    by_contra hc
    have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases this with h0 | h1 | h2
    · rw [h0] at h_mod_0; norm_num at h_mod_0
      have h4 : (p : ℤ) ≤ 4 := Int.le_of_dvd (by decide) h_mod_0
      omega
    · rw [h1] at h_mod_0; norm_num at h_mod_0
      have h1 : (p : ℤ) ≤ 1 := Int.le_of_dvd (by decide) h_mod_0
      omega
    · rw [h2] at h_mod_0; norm_num at h_mod_0
      have h4 : (p : ℤ) ≤ 4 := Int.le_of_dvd (by decide) h_mod_0
      omega
  have hm := m_exists p n hn_ge_3 h_mod_0
  rcases hm with ⟨m, hm_eq⟩
  use n
  have h_m_lt_n : m < n := m_lt_n p n m hn_le hm_eq
  have hn_ge_3' : 3 ≤ n := hn_ge_3
  have hm_eq_z : (n : ℤ)^2 + 2*(n : ℤ) - 4 = (m : ℤ) * p := by
    have h1 : (n^2 + 2*n : ℤ) = (p * m + 4 : ℤ) := by exact_mod_cast hm_eq
    linarith
  have h_ek_base := Ek_eq n hn_ge_3'
  have h_ek : 2 * (n - 2 : ℤ) * P n 3 - 4 * ((n - 1).factorial : ℤ) = (C n : ℤ) * m * p := by
    have h_pnn : P n n = 4 := Pnn_eq n
    have h_fact2 : fact (n - 1) = ((n - 1).factorial : ℤ) := fact_eq (n - 1)
    have h1 : 2 * (n - 2 : ℤ) * P n 3 - fact (n - 1) * P n n = (C n : ℤ) * ((n : ℤ)^2 + 2*(n : ℤ) - 4) := by exact_mod_cast h_ek_base
    rw [h_pnn, h_fact2] at h1
    have h1' : 2 * (n - 2 : ℤ) * P n 3 - 4 * ((n - 1).factorial : ℤ) = (C n : ℤ) * ((n : ℤ)^2 + 2*(n : ℤ) - 4) := by linarith
    rw [h1', hm_eq_z]
    ring
  have h_not_dvd := p_not_div_p3 n p m hp hp_ge hn_ge_3' hn_le (P n 3) (C n) h_ek
  have h_not_dvd_abs : ¬ ((p : ℤ) ∣ (P n 3).natAbs) := by
    intro h
    apply h_not_dvd
    have : ((P n 3).natAbs : ℤ) = P n 3 ∨ ((P n 3).natAbs : ℤ) = - P n 3 := by omega
    rcases this with h1 | h2
    · rw [← h1]; exact h
    · have h_neg : (p : ℤ) ∣ - P n 3 := by rw [← h2]; exact h
      rcases h_neg with ⟨k_neg, hk_neg⟩
      use -k_neg
      linarith
  have h_m_div := m_div_p3_main n m p (P n 3) (by
    intro h2
    have h_p2 : 2 ∣ p := by exact_mod_cast h2
    have h_p_odd : p % 2 = 1 := by omega
    have : p % 2 = 0 := Nat.mod_eq_zero_of_dvd h_p2
    omega
  ) hm_eq_z (by
    have : 2 * (n - 2 : ℤ) * P n 3 = 4 * ((n - 1).factorial : ℤ) + (C n : ℤ) * m * p := by linarith
    rw [this]
    apply _root_.dvd_add
    · have h_m_le : m ≤ n - 1 := by omega
      have h_m_pos : 0 < m := by
        by_contra h0
        have : m = 0 := by omega
        rw [this] at hm_eq
        have : n^2 + 2*n = 4 := by omega
        omega
      have h_dvd : m ∣ (n - 1).factorial := Nat.dvd_factorial h_m_pos h_m_le
      have h_dvd_z : (m : ℤ) ∣ ((n - 1).factorial : ℤ) := by exact_mod_cast h_dvd
      exact dvd_mul_of_dvd_right h_dvd_z 4
    · use (C n : ℤ) * p
      ring
  ) (by
    intro hn_even
    have hn_even_nat : 2 ∣ n := by exact_mod_cast hn_even
    rcases hn_even_nat with ⟨x, hx⟩
    have h_c := P3_mult_4 n x (by exact_mod_cast hx) hn_ge_3'
    exact h_c
  )
  have h_m_div_nat : m ∣ (P n 3).natAbs := by
    have ⟨k, hk⟩ := h_m_div
    use k.natAbs
    have : (P n 3).natAbs = (↑m * k).natAbs := by rw [hk]
    have h_abs : ((m : ℤ) * k).natAbs = (m : ℤ).natAbs * k.natAbs := Int.natAbs_mul (m : ℤ) k
    have h_m_abs : (m : ℤ).natAbs = m := rfl
    rw [h_m_abs] at h_abs
    rw [h_abs] at this
    exact this
  have hP2 : (P n 2).natAbs = p * m := by
    have : P n 2 = ((p * m : ℕ) : ℤ) := by
      have h_P2 : P n 2 = (n : ℤ)^2 + 2*(n : ℤ) - 4 := P2_eq n hn_ge_3'
      rw [h_P2, hm_eq_z]
      push_cast
      ring
    rw [this]
    rfl
  have hm_eq_nat : (P n 2).natAbs = p * m := hP2
  have h_P2_pos : 0 < (P n 2).natAbs := by omega
  have h_gcd := my_A363347_eq n p m ((P n 3).natAbs) ((P n 2).natAbs) hn_ge_3' hp hm_eq h_not_dvd_abs h_m_div_nat hm_eq_nat
  have h_A_int := A363347_eq n hn_ge_3'
  have h_P2_pos' : 0 ≤ P n 2 := by
    have : P n 2 = ((p * m : ℕ) : ℤ) := by
      have h_z : P n 2 = (n : ℤ)^2 + 2*(n : ℤ) - 4 := P2_eq n hn_ge_3'
      rw [h_z, hm_eq_z]
      push_cast
      ring
    rw [this]
    exact Int.natCast_nonneg _
  have h_gcd_eq : (P n 2).gcd (P n 3) = (P n 2).natAbs.gcd (P n 3).natAbs := rfl
  have h_div_eq : P n 2 / ((P n 2).gcd (P n 3) : ℤ) = ((P n 2).natAbs / (P n 2).natAbs.gcd (P n 3).natAbs : ℕ) := by
    rw [h_gcd_eq]
    have : P n 2 = (((P n 2).natAbs : ℕ) : ℤ) := by exact Int.natAbs_of_nonneg h_P2_pos' |>.symm
    rw [this]
    exact Int.ofNat_ediv_ofNat.symm
  rw [h_div_eq] at h_A_int
  rw [h_gcd] at h_A_int
  exact_mod_cast h_A_int

/-- The disproof. -/
@[AMS 11, category research solved]
theorem oeis_363347_conjecture_2.disproof
  (p : ℕ) (hp : Nat.Prime p)
  (h_mod : p % 10 = 1 ∨ p % 10 = 9) :
  ¬ ∃ n : ℕ, A363347 n = p := sorry
