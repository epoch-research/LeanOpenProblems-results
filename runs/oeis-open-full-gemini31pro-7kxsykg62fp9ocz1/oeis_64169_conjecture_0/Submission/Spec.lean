import FormalConjectures.Util.ProblemImports
open Rat

def A064169 (n : ℕ) : ℕ :=
  let hn := harmonic n
  Int.natAbs (hn.num - hn.den)

theorem oeis_64169_conjecture_0 (n : ℕ) (hn : n > 2) :
  (n ∣ A064169 (n - 2)) ↔ n.Prime :=
by sorry

def p : ℕ := 16843
def N : ℕ := p * p
def Good (q : ℚ) : Prop := ¬ (p ∣ q.den)
def DivByN (q : ℚ) : Prop := (N : ℤ) ∣ q.num ∧ Good q

lemma prime_p : Nat.Prime p := by unfold p; norm_num

lemma p_not_dvd_of_N_coprime {G : ℕ} (h_not : ¬ (p ∣ G)) : (N.gcd G) = 1 := by
  have h1 : (N.gcd G) ∣ N := Nat.gcd_dvd_left N G
  have h2 : (N.gcd G) ∣ G := Nat.gcd_dvd_right N G
  by_contra h3
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd h3
  have hq_dvd_N : q ∣ N := Nat.dvd_trans hq_dvd h1
  have hq_dvd_p : q ∣ p ∨ q ∣ p := (Nat.Prime.dvd_mul hq_prime).mp hq_dvd_N
  cases hq_dvd_p with
  | inl h => 
    have hpq : q = p := (Nat.Prime.eq_one_or_self_of_dvd prime_p q h).resolve_left hq_prime.ne_one
    subst hpq; exact h_not (Nat.dvd_trans hq_dvd h2)
  | inr h =>
    have hpq : q = p := (Nat.Prime.eq_one_or_self_of_dvd prime_p q h).resolve_left hq_prime.ne_one
    subst hpq; exact h_not (Nat.dvd_trans hq_dvd h2)

lemma Int_dvd_div_of_coprime {A B G : ℤ} (h1 : (N:ℤ) ∣ A) (h2 : A = G * B) (h3 : (N : ℤ).gcd (G.natAbs) = 1) : (N:ℤ) ∣ B := by
  have h4 : (N:ℤ) ∣ B * G := by rw [mul_comm]; rw [←h2]; exact h1
  exact Int.dvd_of_dvd_mul_left_of_gcd_one h4 h3

lemma div_by_N_mul_good (x y : ℚ) (hx : (N:ℤ) ∣ x.num) (hx_good : ¬ (p ∣ x.den)) (hy_good : ¬ (p ∣ y.den)) : (N:ℤ) ∣ (x * y).num := by
  have h_mul := Rat.mul_def x y
  have h_num := congrArg Rat.num h_mul
  set A := x.num * y.num
  set B : ℕ := x.den * y.den
  have h_nz : B ≠ 0 := mul_ne_zero x.den_pos.ne' y.den_pos.ne'
  rw [Rat.num_normalize h_nz] at h_num
  set G : ℤ := ↑(A.natAbs.gcd B)
  have h_mul2 : A = G * (x * y).num := by
    have h_div : A / G = (x * y).num := h_num.symm
    have h_dvd : G ∣ A := Int.natAbs_dvd_natAbs.mp (Nat.gcd_dvd_left A.natAbs B)
    have h_cancel := Int.ediv_mul_cancel h_dvd
    rw [h_div] at h_cancel
    rw [mul_comm] at h_cancel
    exact h_cancel.symm
  have hA : (N:ℤ) ∣ A := dvd_mul_of_dvd_left hx (y.num)
  have h_not : ¬ (p ∣ G.natAbs) := by
    have hG_def : G.natAbs = A.natAbs.gcd B := by rfl
    have hG_dvd_B : G.natAbs ∣ B := by rw [hG_def]; exact Nat.gcd_dvd_right A.natAbs B
    intro h
    have h_p_dvd_B : p ∣ B := Nat.dvd_trans h hG_dvd_B
    have h_p_dvd_xy : p ∣ x.den ∨ p ∣ y.den := (Nat.Prime.dvd_mul prime_p).mp h_p_dvd_B
    cases h_p_dvd_xy with
    | inl hx_p => exact hx_good hx_p
    | inr hy_p => exact hy_good hy_p
  have h_coprime : (N : ℤ).gcd G.natAbs = 1 := p_not_dvd_of_N_coprime h_not
  exact Int_dvd_div_of_coprime hA h_mul2 h_coprime

lemma good_mul (x y : ℚ) (hx : Good x) (hy : Good y) : Good (x * y) := by
  unfold Good at *; intro h; have h1 : (x * y).den ∣ x.den * y.den := Rat.mul_den_dvd x y
  have h2 : p ∣ x.den * y.den := Nat.dvd_trans h h1
  have h3 : p ∣ x.den ∨ p ∣ y.den := (Nat.Prime.dvd_mul prime_p).mp h2
  cases h3 with | inl h3 => exact hx h3 | inr h3 => exact hy h3

lemma div_by_N_mul_good_div (x y : ℚ) (hx : DivByN x) (hy : Good y) : DivByN (x * y) := by
  rcases hx with ⟨hx_num, hx_good⟩
  exact ⟨div_by_N_mul_good x y hx_num hx_good hy, good_mul x y hx_good hy⟩

lemma den_one_half : (1 / 2 : ℚ).den = 2 := by
  have h_eq : (1 / 2 : ℚ).den == 2 := rfl
  exact eq_of_beq h_eq

lemma div_by_N_two_mul (X : ℚ) (h : DivByN (2 * X)) : DivByN X := by
  have h_eq : X = (2 * X) * (1 / 2) := by ring
  rw [h_eq]
  apply div_by_N_mul_good_div (2 * X) (1 / 2) h
  unfold Good
  rw [den_one_half]
  intro hp
  have hp2 : p = 16843 := by rfl
  have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) hp
  omega

lemma good_zero : Good 0 := by
  unfold Good; intro h; rw [Rat.den_zero] at h; exact Nat.Prime.not_dvd_one prime_p h

lemma div_by_N_zero : DivByN 0 := by
  unfold DivByN
  refine ⟨?_, good_zero⟩
  rw [Rat.num_zero]
  exact dvd_zero (N : ℤ)

lemma good_add (x y : ℚ) (hx : Good x) (hy : Good y) : Good (x + y) := by
  unfold Good at *; intro h; have h1 : (x + y).den ∣ x.den * y.den := Rat.add_den_dvd x y
  have h2 : p ∣ x.den * y.den := Nat.dvd_trans h h1
  have h3 : p ∣ x.den ∨ p ∣ y.den := (Nat.Prime.dvd_mul prime_p).mp h2
  cases h3 with | inl h3 => exact hx h3 | inr h3 => exact hy h3

lemma div_by_N_add_helper (x y : ℚ) (hx_num : (N:ℤ) ∣ x.num) (hy_num : (N:ℤ) ∣ y.num) 
  (hx_good : ¬ (p ∣ x.den)) (hy_good : ¬ (p ∣ y.den)) : (N:ℤ) ∣ (x + y).num := by
  have h_add := Rat.add_num_den x y
  have h_num := congrArg Rat.num h_add
  rw [Rat.num_divInt] at h_num
  set A := x.num * ↑y.den + ↑x.den * y.num
  set B : ℤ := ↑x.den * ↑y.den
  have hA : (N:ℤ) ∣ A := by
    apply dvd_add
    · exact dvd_mul_of_dvd_left hx_num (y.den : ℤ)
    · exact dvd_mul_of_dvd_right hy_num (x.den : ℤ)
  set G : ℤ := ↑(B.gcd A)
  have h_sign : B.sign = 1 := by
    have hx_pos : (0 : ℤ) < ↑x.den := Int.natCast_pos.mpr x.den_pos
    have hy_pos : (0 : ℤ) < ↑y.den := Int.natCast_pos.mpr y.den_pos
    exact Int.sign_eq_one_of_pos (mul_pos hx_pos hy_pos)
  rw [h_sign, one_mul] at h_num
  have h_mul : A = G * (x + y).num := by
    have h_div : A / G = (x + y).num := h_num.symm
    have h_dvd : G ∣ A := Int.gcd_dvd_right B A
    have h_cancel := Int.ediv_mul_cancel h_dvd
    rw [h_div] at h_cancel
    rw [mul_comm] at h_cancel
    exact h_cancel.symm
  have h_not : ¬ (p ∣ G.natAbs) := by
    have hG_def : G.natAbs = B.gcd A := by rfl
    have hG_dvd_B : G.natAbs ∣ B.natAbs := by
      rw [hG_def]
      have h1 : B.gcd A = B.natAbs.gcd A.natAbs := by rfl
      rw [h1]
      exact Nat.gcd_dvd_left B.natAbs A.natAbs
    intro h
    have h_p_dvd_B : p ∣ B.natAbs := Nat.dvd_trans h hG_dvd_B
    have hB_nat : B.natAbs = x.den * y.den := by
      change (x.den * y.den : ℤ).natAbs = x.den * y.den
      exact Int.natAbs_natCast (x.den * y.den)
    rw [hB_nat] at h_p_dvd_B
    have h_p_dvd_xy : p ∣ x.den ∨ p ∣ y.den := (Nat.Prime.dvd_mul prime_p).mp h_p_dvd_B
    cases h_p_dvd_xy with
    | inl hx => exact hx_good hx
    | inr hy => exact hy_good hy
  have h_coprime : (N : ℤ).gcd G.natAbs = 1 := p_not_dvd_of_N_coprime h_not
  exact Int_dvd_div_of_coprime hA h_mul h_coprime

lemma div_by_N_add (x y : ℚ) (hx : DivByN x) (hy : DivByN y) : DivByN (x + y) := by
  rcases hx with ⟨hx_num, hx_good⟩
  rcases hy with ⟨hy_num, hy_good⟩
  exact ⟨div_by_N_add_helper x y hx_num hy_num hx_good hy_good, good_add x y hx_good hy_good⟩

lemma div_by_N_sum (s : Finset ℕ) (f : ℕ → ℚ) (hf : ∀ x ∈ s, DivByN (f x)) : DivByN (s.sum f) := by
  induction s using Finset.induction_on with
  | empty => exact div_by_N_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    apply div_by_N_add
    · apply hf a; exact Finset.mem_insert_self a s
    · apply ih; intro x hx; apply hf x; exact Finset.mem_insert_of_mem hx

lemma div_by_N_N_div (X : ℕ) (hXp : ¬ (p ∣ X)) : DivByN (N / (X : ℚ)) := by
  by_cases hX0 : X = 0
  · subst hX0; rw [Nat.cast_zero, div_zero]; unfold DivByN Good; rw [Rat.num_zero, Rat.den_zero]
    exact ⟨dvd_zero _, Nat.Prime.not_dvd_one prime_p⟩
  have h_eq : (N : ℚ) / X = (N : ℚ) * (X : ℚ)⁻¹ := rfl
  rw [h_eq]
  have hN_div : DivByN (N : ℚ) := by
    unfold DivByN Good; rw [Rat.num_natCast, Rat.den_natCast]
    exact ⟨dvd_rfl, Nat.Prime.not_dvd_one prime_p⟩
  have hX_inv : Good (X : ℚ)⁻¹ := by
    unfold Good; rw [Rat.den_inv, Rat.num_natCast]
    split
    · intro h; exact Nat.Prime.not_dvd_one prime_p h
    · rw [Int.natAbs_natCast]; exact hXp
  exact div_by_N_mul_good_div (N : ℚ) (X : ℚ)⁻¹ hN_div hX_inv

lemma div_by_N_pair (k : ℕ) (hk0 : k ≠ 0) (hkN : k < N) (hkp : ¬ (p ∣ k)) : 
  DivByN (1 / (k : ℚ) + 1 / ((N - k : ℕ) : ℚ)) := by
  have hk_neq : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
  have hkN_neq : ((N - k : ℕ) : ℚ) ≠ 0 := by
    have h1 : N - k ≠ 0 := by omega
    exact Nat.cast_ne_zero.mpr h1
  have h_add := one_div_add_one_div hk_neq hkN_neq
  have h_sum : (k : ℚ) + ((N - k : ℕ) : ℚ) = (N : ℚ) := by
    have hk_le : k ≤ N := by omega
    rw [Nat.cast_sub hk_le]
    ring
  have h_prod : (k : ℚ) * ((N - k : ℕ) : ℚ) = ((k * (N - k) : ℕ) : ℚ) := by
    rw [Nat.cast_mul]
  rw [h_sum, h_prod] at h_add
  rw [h_add]
  apply div_by_N_N_div
  intro h
  have h_dvd_mul : p ∣ k * (N - k) := h
  have h_dvd_k_or : p ∣ k ∨ p ∣ N - k := (Nat.Prime.dvd_mul prime_p).mp h_dvd_mul
  cases h_dvd_k_or with
  | inl h => exact hkp h
  | inr h =>
    have h_p_dvd_N : p ∣ N := by exact dvd_mul_right p p
    have h_p_dvd_k : p ∣ k := by
      have h1 : k = N - (N - k) := by omega
      rw [h1]
      exact Nat.dvd_sub h_p_dvd_N h
    exact hkp h_p_dvd_k

lemma div_by_N_S_sum : DivByN (((Finset.Icc 1 (N-1)).filter (fun k => ¬ (p ∣ k))).sum (fun k => 1 / (k : ℚ))) := by
  set S := (Finset.Icc 1 (N-1)).filter (fun k => ¬ (p ∣ k))
  have h_sum1 : S.sum (fun k => 1 / (k : ℚ)) = S.sum (fun k => 1 / ((N - k : ℕ) : ℚ)) := by
    apply Finset.sum_bij (fun k _ => N - k)
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_Icc] at ha
      rcases ha with ⟨⟨ha1, ha2⟩, hap⟩
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro hp
      have h_p_dvd_N : p ∣ N := dvd_mul_right p p
      have h_p_dvd_a : p ∣ a := by
        have h1 : a = N - (N - a) := by omega
        rw [h1]
        exact Nat.dvd_sub h_p_dvd_N hp
      exact hap h_p_dvd_a
    · intro a1 ha1 a2 ha2 h_eq
      rw [Finset.mem_filter, Finset.mem_Icc] at ha1 ha2
      omega
    · intro b hb
      use N - b
      rw [Finset.mem_filter, Finset.mem_Icc] at hb
      have hb_in_S : (N - b) ∈ S := by
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        intro hp
        have h_p_dvd_N : p ∣ N := dvd_mul_right p p
        have h_p_dvd_b : p ∣ b := by
          have h1 : b = N - (N - b) := by omega
          rw [h1]
          exact Nat.dvd_sub h_p_dvd_N hp
        exact hb.2 h_p_dvd_b
      refine ⟨hb_in_S, by omega⟩
    · intro a ha
      have h_eq : N - (N - a) = a := by
        rw [Finset.mem_filter, Finset.mem_Icc] at ha
        omega
      rw [h_eq]
  have h_sum2 : 2 * S.sum (fun k => 1 / (k : ℚ)) = S.sum (fun k => 1 / (k : ℚ) + 1 / ((N - k : ℕ) : ℚ)) := by
    rw [two_mul]
    nth_rw 2 [h_sum1]
    rw [←Finset.sum_add_distrib]
  apply div_by_N_two_mul
  rw [h_sum2]
  apply div_by_N_sum
  intro k hk
  rw [Finset.mem_filter, Finset.mem_Icc] at hk
  rcases hk with ⟨⟨hk1, hk2⟩, hkp⟩
  have hk0 : k ≠ 0 := by omega
  have hkN : k < N := by omega
  exact div_by_N_pair k hk0 hkN hkp

def h_p_1 : ℚ := harmonic 16842

def T_sum : ℚ := ((Finset.Icc 1 (N-1)).filter (fun k => p ∣ k)).sum (fun k => 1 / (k : ℚ))
lemma T_sum_eq : T_sum = h_p_1 / p := by native_decide
lemma div_by_N_T_sum_num : (N : ℤ) ∣ (h_p_1 / p).num := by native_decide
lemma div_by_N_T_sum_den : ¬ (p ∣ (h_p_1 / p).den) := by native_decide

lemma div_by_N_T_sum : DivByN T_sum := by
  rw [T_sum_eq]
  unfold DivByN Good
  exact ⟨div_by_N_T_sum_num, div_by_N_T_sum_den⟩

lemma harmonic_N_minus_1 : 
  harmonic (N - 1) = 
  ((Finset.Icc 1 (N-1)).filter (fun k => ¬ (p ∣ k))).sum (fun k => 1 / (k : ℚ)) + 
  T_sum := by
  have h_part : ((Finset.Icc 1 (N-1)).filter (fun k => p ∣ k)).sum (fun k => 1 / (k : ℚ)) +
                ((Finset.Icc 1 (N-1)).filter (fun k => ¬ (p ∣ k))).sum (fun k => 1 / (k : ℚ)) = 
                (Finset.Icc 1 (N-1)).sum (fun k => 1 / (k : ℚ)) := by
    exact Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (N - 1)) (fun k => p ∣ k) (fun k => 1 / (k : ℚ))
  have h_range : harmonic (N - 1) = (Finset.Icc 1 (N-1)).sum (fun k => 1 / (k : ℚ)) := by
    unfold harmonic
    have h1 : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
      ext x; rw [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [h1]
    have h2 := Finset.sum_Ico_eq_sum_range (fun k => 1 / (k : ℚ)) 1 N
    rw [h2]
    apply Finset.sum_congr rfl
    intro x _
    push_cast
    rw [one_div]
    have h4 : (x : ℚ) + 1 = 1 + (x : ℚ) := by ring
    rw [h4]
  have h_T_sum : T_sum = ((Finset.Icc 1 (N-1)).filter (fun k => p ∣ k)).sum (fun k => 1 / (k : ℚ)) := rfl
  rw [h_range, ←h_part, h_T_sum, add_comm]

lemma b_num : (1 / ((N - 1 : ℕ) : ℚ)).num = 1 := by unfold N p; norm_num
lemma b_den : (1 / ((N - 1 : ℕ) : ℚ)).den = N - 1 := by unfold N p; norm_num
lemma p_not_dvd_N_minus_1 : ¬ (p ∣ N - 1) := by unfold N p; decide
lemma N_ge_1 : 1 ≤ N := by unfold N p; decide

lemma H_N_2_dvd (H_N_1 : ℚ) (h_num : (N : ℤ) ∣ H_N_1.num) (h_good : ¬ (p ∣ H_N_1.den)) : (N : ℤ) ∣ (H_N_1 - 1 / ((N - 1 : ℕ) : ℚ)).num - (H_N_1 - 1 / ((N - 1 : ℕ) : ℚ)).den := by
  set b := 1 / ((N - 1 : ℕ) : ℚ)
  have h_sub := Rat.sub_def H_N_1 b
  have h_num_sub := congrArg Rat.num h_sub
  have h_den_sub := congrArg Rat.den h_sub
  set A := H_N_1.num * ↑b.den - b.num * ↑H_N_1.den
  set B : ℕ := H_N_1.den * b.den
  have h_nz : B ≠ 0 := mul_ne_zero H_N_1.den_pos.ne' b.den_pos.ne'
  rw [Rat.num_normalize h_nz] at h_num_sub
  rw [Rat.den_normalize h_nz] at h_den_sub
  set G_N : ℕ := A.natAbs.gcd B
  set G : ℤ := ↑G_N
  set H_N_2 := H_N_1 - b
  have h_mul1 : A = G * H_N_2.num := by
    have h_div : A / G = H_N_2.num := h_num_sub.symm
    have h_dvd : G ∣ A := Int.natAbs_dvd_natAbs.mp (Nat.gcd_dvd_left A.natAbs B)
    have h_cancel := Int.ediv_mul_cancel h_dvd
    rw [h_div] at h_cancel
    rw [mul_comm] at h_cancel
    exact h_cancel.symm
  have h_mul2 : (B : ℤ) = G * H_N_2.den := by
    have h_div : B / G_N = H_N_2.den := h_den_sub.symm
    have h_dvd : G_N ∣ B := Nat.gcd_dvd_right A.natAbs B
    have h_cancel := Nat.div_mul_cancel h_dvd
    rw [h_div] at h_cancel
    have h_cast : ((H_N_2.den * G_N : ℕ) : ℤ) = ((B : ℕ) : ℤ) := congrArg Nat.cast h_cancel
    push_cast at h_cast
    rw [mul_comm] at h_cast
    exact h_cast.symm
  have h_sub_val : A - (B : ℤ) = G * (H_N_2.num - H_N_2.den) := by
    rw [h_mul1, h_mul2, mul_sub]
  have hA_sub_B : (N : ℤ) ∣ A - (B : ℤ) := by
    have hb_val_num : b.num = 1 := b_num
    have hb_val_den : b.den = N - 1 := b_den
    have hA_val : A = H_N_1.num * ↑(N - 1) - 1 * ↑H_N_1.den := by
      change H_N_1.num * ↑b.den - b.num * ↑H_N_1.den = _
      rw [hb_val_num, hb_val_den]
    have hB_val : (B : ℤ) = H_N_1.den * ↑(N - 1) := by
      have h1 : B = H_N_1.den * b.den := rfl
      rw [h1, hb_val_den]
      push_cast
      rfl
    rw [hA_val, hB_val]
    have hN1 : (↑(N - 1) : ℤ) = (N : ℤ) - 1 := Nat.cast_sub N_ge_1
    rw [hN1]
    have h_eq : H_N_1.num * (↑N - 1) - 1 * ↑H_N_1.den - ↑H_N_1.den * (↑N - 1) = H_N_1.num * (↑N - 1) - ↑H_N_1.den * ↑N := by ring
    rw [h_eq]
    apply dvd_sub
    · exact dvd_mul_of_dvd_left h_num (N - 1)
    · exact dvd_mul_of_dvd_left dvd_rfl ↑H_N_1.den |>.trans (by rw [mul_comm])
  have h_not : ¬ (p ∣ G_N) := by
    have hG_dvd_B : G_N ∣ B := Nat.gcd_dvd_right A.natAbs B
    intro h
    have h_p_dvd_B : p ∣ B := Nat.dvd_trans h hG_dvd_B
    have h_p_dvd_xy : p ∣ H_N_1.den ∨ p ∣ b.den := (Nat.Prime.dvd_mul prime_p).mp h_p_dvd_B
    cases h_p_dvd_xy with
    | inl hx => exact h_good hx
    | inr hy =>
      have hy_val : b.den = N - 1 := b_den
      rw [hy_val] at hy
      exact p_not_dvd_N_minus_1 hy
  have h_coprime : (N : ℤ).gcd G_N = 1 := p_not_dvd_of_N_coprime h_not
  exact Int_dvd_div_of_coprime hA_sub_B h_sub_val h_coprime

lemma N_gt_2 : N > 2 := by unfold N p; decide
lemma not_prime_N : ¬ Nat.Prime N := by
  intro hp
  have h_dvd : p ∣ N := dvd_mul_right p p
  have h_p_pos : p ≠ 1 := by unfold p; decide
  have h_p_lt_N : p ≠ N := by unfold p N; decide
  have h_p_dvd := hp.eq_one_or_self_of_dvd p h_dvd
  cases h_p_dvd with
  | inl h_eq => exact h_p_pos h_eq
  | inr h_eq => exact h_p_lt_N h_eq

lemma harmonic_N_2_eq : harmonic (N - 2) = harmonic (N - 1) - 1 / ((N - 1 : ℕ) : ℚ) := by
  have h1 : N - 1 = N - 2 + 1 := by omega
  have h2 : harmonic (N - 1) = harmonic (N - 2 + 1) := by rw [h1]
  rw [h2]
  have h3 : harmonic (N - 2 + 1) = harmonic (N - 2) + 1 / ((N - 2 + 1 : ℕ) : ℚ) := by
    unfold harmonic
    rw [Finset.sum_range_succ]
    rw [one_div]
  rw [h3]
  have h5 : ((N - 2 + 1 : ℕ) : ℚ) = ((N - 1 : ℕ) : ℚ) := by
    have h6 : N - 2 + 1 = N - 1 := by omega
    rw [h6]
  rw [h5]
  ring

theorem oeis_64169_conjecture_0.disproof : ¬ (type_of% @oeis_64169_conjecture_0) := by
  intro h
  have h_counter : (N ∣ A064169 (N - 2)) := by
    unfold A064169
    have h_eq : harmonic (N - 2) = harmonic (N - 1) - 1 / ((N - 1 : ℕ) : ℚ) := harmonic_N_2_eq
    rw [h_eq]
    have h1 : DivByN (harmonic (N - 1)) := by
      rw [harmonic_N_minus_1]
      apply div_by_N_add
      · exact div_by_N_S_sum
      · exact div_by_N_T_sum
    have h2 := H_N_2_dvd (harmonic (N - 1)) h1.1 h1.2
    exact Int.natCast_dvd.mp h2
  have h_prime := (h N N_gt_2).mp h_counter
  exact not_prime_N h_prime
