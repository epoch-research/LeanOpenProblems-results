import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators


lemma term_eq_helper (a y : ℕ) (f : ℕ → R) [CommRing R] (hne : y ≠ a) :
    ((if a < y then f a * f y else 0) + (if y < a then f a * f y else 0)) = f a * f y := by
  rcases lt_or_gt_of_ne hne.symm with h | h
  · have h1 : ¬ y < a := by omega
    simp [h, h1]
  · have h1 : ¬ a < y := by omega
    simp [h, h1]

lemma prod_one_add_t_mul {R : Type*} [CommRing R]
    (t : R) (ht3 : t^3 = 0) (s : Finset ℕ) (f : ℕ → R) :
    ∏ x ∈ s, (1 + t * f x) = 1 + t * (∑ x ∈ s, f x) + t^2 * (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [prod_insert ha, ih, sum_insert ha]
    have h_double : ∑ x ∈ insert a s, ∑ y ∈ insert a s, (if x < y then f x * f y else 0) =
        (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) + f a * (∑ x ∈ s, f x) := by
      rw [sum_insert ha]
      simp only [sum_insert ha, lt_self_iff_false, if_false, zero_add]
      rw [sum_add_distrib]
      have h_term : ∑ y ∈ s, (if a < y then f a * f y else 0) + ∑ x ∈ s, (if x < a then f x * f a else 0) =
          f a * ∑ x ∈ s, f x := by
        rw [← sum_add_distrib]
        rw [mul_sum]
        apply sum_congr rfl
        intro x hx
        have hne : x ≠ a := by
          intro h_eq
          subst h_eq
          exact ha hx
        have h_comm : f x * f a = f a * f x := mul_comm (f x) (f a)
        rw [h_comm]
        exact term_eq_helper a x f hne
      calc ∑ y ∈ s, (if a < y then f a * f y else 0) + ((∑ x ∈ s, if x < a then f x * f a else 0) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0)
        _ = (∑ y ∈ s, (if a < y then f a * f y else 0) + ∑ x ∈ s, if x < a then f x * f a else 0) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0 := by ring
        _ = f a * (∑ x ∈ s, f x) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0 := by rw [h_term]
        _ = (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) + f a * (∑ x ∈ s, f x) := by ring
    rw [h_double]
    set sum_s := ∑ x ∈ s, f x
    set sum_pair := ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0
    have h_ring : (1 + t * f a) * (1 + t * sum_s + t^2 * sum_pair) =
        1 + t * (f a + sum_s) + t^2 * (sum_pair + f a * sum_s) + t^3 * (f a * sum_pair) := by ring
    rw [h_ring, ht3]
    ring


lemma sum_pairs_identity {R : Type*} [CommRing R] (s : Finset ℕ) (f : ℕ → R) :
    2 * (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) = (∑ x ∈ s, f x)^2 - ∑ x ∈ s, (f x)^2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h_double : ∑ x ∈ insert a s, ∑ y ∈ insert a s, (if x < y then f x * f y else 0) =
        (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) + f a * (∑ x ∈ s, f x) := by
      rw [sum_insert ha]
      simp only [sum_insert ha, lt_self_iff_false, if_false, zero_add]
      rw [sum_add_distrib]
      have h_term : ∑ y ∈ s, (if a < y then f a * f y else 0) + ∑ x ∈ s, (if x < a then f x * f a else 0) =
          f a * ∑ x ∈ s, f x := by
        rw [← sum_add_distrib]
        rw [mul_sum]
        apply sum_congr rfl
        intro x hx
        have hne : x ≠ a := by
          intro h_eq
          subst h_eq
          exact ha hx
        have h_comm : f x * f a = f a * f x := mul_comm (f x) (f a)
        rw [h_comm]
        exact term_eq_helper a x f hne
      calc ∑ y ∈ s, (if a < y then f a * f y else 0) + ((∑ x ∈ s, if x < a then f x * f a else 0) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0)
        _ = (∑ y ∈ s, (if a < y then f a * f y else 0) + ∑ x ∈ s, if x < a then f x * f a else 0) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0 := by ring
        _ = f a * (∑ x ∈ s, f x) + ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0 := by rw [h_term]
        _ = (∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0) + f a * (∑ x ∈ s, f x) := by ring
    rw [h_double]
    rw [sum_insert ha, sum_insert ha]
    set sum_s := ∑ x ∈ s, f x
    set sum_pair := ∑ x ∈ s, ∑ y ∈ s, if x < y then f x * f y else 0
    set sum_sq := ∑ x ∈ s, (f x)^2
    calc 2 * (sum_pair + f a * sum_s)
      _ = 2 * sum_pair + 2 * f a * sum_s := by ring
      _ = (sum_s^2 - sum_sq) + 2 * f a * sum_s := by rw [ih]
      _ = (f a + sum_s)^2 - ((f a)^2 + sum_sq) := by ring

lemma prod_Ico_reflect {α : Type*} [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∏ j ∈ Ico 1 n, f (n - j) = ∏ j ∈ Ico 1 n, f j := by
  apply prod_nbij' (fun j => n - j) (fun j => n - j)
  · intro a ha
    rw [mem_Ico] at ha ⊢
    omega
  · intro a ha
    rw [mem_Ico] at ha ⊢
    omega
  · intro a ha
    rw [mem_Ico] at ha
    omega
  · intro a ha
    rw [mem_Ico] at ha
    omega
  · intro a ha
    rfl

lemma choose_mul_factorial_helper (n : ℕ) (hn : n ≥ 1) :
    (3 * n - 1).choose (n - 1) * (n - 1)! * (2 * n)! = (3 * n - 1)! := by
  have h_sub : (3 * n - 1) - (n - 1) = 2 * n := by omega
  have h_le : n - 1 ≤ 3 * n - 1 := by omega
  rw [← Nat.choose_mul_factorial_mul_factorial h_le, h_sub]


lemma prod_range_succ (n : ℕ) : ∏ j ∈ range n, (j + 1) = (n)! := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, mul_comm, Nat.factorial_succ]


lemma prod_Ico_id_eq_factorial (n : ℕ) (hn : n ≥ 1) :
    ∏ j ∈ Ico 1 n, j = (n - 1)! := by
  have h_eq : ∏ j ∈ Ico 1 n, j = ∏ j ∈ range (n - 1), (j + 1) := by
    apply prod_nbij' (fun j => j - 1) (fun j => j + 1)
    · intro a ha
      rw [mem_Ico] at ha
      rw [mem_range]
      omega
    · intro a ha
      rw [mem_range] at ha
      rw [mem_Ico]
      omega
    · intro a ha
      rw [mem_Ico] at ha
      omega
    · intro a ha
      rw [mem_range] at ha
      omega
    · intro a ha
      rw [mem_Ico] at ha
      omega
  rw [h_eq]
  exact prod_range_succ (n - 1)


lemma prod_add_eq_Ico (n : ℕ) :
    ∏ j ∈ Ico 1 n, (2 * n + j) = ∏ j ∈ Ico (2 * n + 1) (3 * n), j := by
  have h := Finset.prod_Ico_add (fun j => j) 1 n (2 * n)
  have h1 : 1 + 2 * n = 2 * n + 1 := by omega
  have h2 : n + 2 * n = 3 * n := by omega
  rw [h1, h2] at h
  exact h


lemma prod_add_mul_factorial (n : ℕ) (hn : n ≥ 1) :
    (2 * n)! * ∏ j ∈ Ico 1 n, (2 * n + j) = (3 * n - 1)! := by
  have h_shift := prod_add_eq_Ico n
  rw [h_shift]
  have h_fac1 := prod_Ico_id_eq_factorial (2 * n + 1) (by omega)
  have h_sub : 2 * n + 1 - 1 = 2 * n := by omega
  rw [h_sub] at h_fac1
  rw [← h_fac1]
  have h_consec := Finset.prod_Ico_consecutive (fun j => j) (by omega : 1 ≤ 2 * n + 1) (by omega : 2 * n + 1 ≤ 3 * n)
  rw [h_consec]
  have h_fac2 := prod_Ico_id_eq_factorial (3 * n) (by omega)
  rw [h_fac2]


lemma choose_mul_factorial_eq_prod (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (3 * p - 1).choose (p - 1) * (p - 1)! = ∏ j ∈ Ico 1 p, (2 * p + j) := by
  have h1 : (3 * p - 1).choose (p - 1) * (p - 1)! * (2 * p)! = (∏ j ∈ Ico 1 p, (2 * p + j)) * (2 * p)! := by
    rw [choose_mul_factorial_helper p (by omega)]
    rw [mul_comm (∏ j ∈ Ico 1 p, (2 * p + j))]
    exact (prod_add_mul_factorial p (by omega)).symm
  have h_pos : (2 * p)! > 0 := Nat.factorial_pos _
  exact Nat.eq_of_mul_eq_mul_right h_pos h1



lemma j_coprime_p_cub (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    Nat.Coprime j (p^3) := by
  have h1 : ¬ p ∣ j := by
    intro hdvd
    have : p ≤ j := Nat.le_of_dvd (by omega) hdvd
    omega
  have h2 : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
  exact Nat.Coprime.pow_right 3 h2

lemma j_inv_mul_cub (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    (j : ZMod (p^3)) * (j : ZMod (p^3))⁻¹ = 1 := by
  exact ZMod.coe_mul_inv_eq_one j (j_coprime_p_cub p hp j hj1 hjp)


lemma element_factorization (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    ((2 * p + j : ℕ) : ZMod (p^3)) = (j : ZMod (p^3)) * (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹) := by
  have h_j_inv : (j : ZMod (p^3)) * (j : ZMod (p^3))⁻¹ = 1 := j_inv_mul_cub p hp j hj1 hjp
  calc ((2 * p + j : ℕ) : ZMod (p^3))
    _ = 2 * (p : ZMod (p^3)) + (j : ZMod (p^3)) := by push_cast; rfl
    _ = (j : ZMod (p^3)) * (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹) := by
      rw [mul_add, mul_one, ← mul_assoc, mul_comm (j : ZMod (p^3)), mul_assoc, h_j_inv]
      ring


lemma prod_factorization (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ∏ j ∈ Ico 1 p, ((2 * p + j : ℕ) : ZMod (p^3)) =
    (∏ j ∈ Ico 1 p, (j : ZMod (p^3))) * ∏ j ∈ Ico 1 p, (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹) := by
  have h_eq : ∏ j ∈ Ico 1 p, ((2 * p + j : ℕ) : ZMod (p^3)) =
      ∏ j ∈ Ico 1 p, ((j : ZMod (p^3)) * (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹)) := by
    apply prod_congr rfl
    intro j hj
    rw [mem_Ico] at hj
    exact element_factorization p hp j hj.1 hj.2
  rw [h_eq]
  exact prod_mul_distrib


lemma prod_id_zmod_cub (p : ℕ) (hp : p.Prime) :
    ∏ j ∈ Ico 1 p, (j : ZMod (p^3)) = ((p - 1)! : ZMod (p^3)) := by
  have h := prod_Ico_id_eq_factorial p (by have := hp.two_le; omega)
  have h_cast : ((∏ j ∈ Ico 1 p, j : ℕ) : ZMod (p^3)) = (((p - 1)! : ℕ) : ZMod (p^3)) := by rw [h]
  push_cast at h_cast
  exact h_cast



lemma coprime_factorial_p_cub (p : ℕ) (hp : p.Prime) :
    Nat.Coprime ((p - 1)!) (p^3) := by
  have h_pos : p > 0 := hp.pos
  have h_cop : Nat.Coprime p ((p - 1)!) := Nat.Prime.coprime_factorial_of_lt hp (by omega)
  have h_cop2 : Nat.Coprime ((p - 1)!) p := h_cop.symm
  exact Nat.Coprime.pow_right 3 h_cop2


lemma choose_mod_p_cubed (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ((3 * p - 1).choose (p - 1) : ZMod (p^3)) = ∏ j ∈ Ico 1 p, (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹) := by
  have h_cop := coprime_factorial_p_cub p hp
  have h_eq1 := choose_mul_factorial_eq_prod p hp hp5
  have h_cast : (((3 * p - 1).choose (p - 1) * (p - 1)! : ℕ) : ZMod (p^3)) = (((∏ j ∈ Ico 1 p, (2 * p + j) : ℕ) : ZMod (p^3))) := by rw [h_eq1]
  push_cast at h_cast
  have h_fac := prod_factorization p hp hp5
  push_cast at h_fac
  have h_id_zmod := prod_id_zmod_cub p hp
  rw [h_fac, h_id_zmod] at h_cast
  have h_inv := ZMod.coe_mul_inv_eq_one ((p - 1)!) h_cop
  set B : ZMod (p^3) := ((p - 1)! : ZMod (p^3))
  set A : ZMod (p^3) := ((3 * p - 1).choose (p - 1) : ZMod (p^3))
  set C : ZMod (p^3) := ∏ j ∈ Ico 1 p, (1 + 2 * (p : ZMod (p^3)) * (j : ZMod (p^3))⁻¹)
  change A * B = B * C at h_cast
  have h_comm : B * C = C * B := mul_comm B C
  rw [h_comm] at h_cast
  have h_cancel : A = C := by
    calc A
      _ = A * 1 := by ring
      _ = A * (B * B⁻¹) := by rw [h_inv]
      _ = (A * B) * B⁻¹ := by ring
      _ = (C * B) * B⁻¹ := by rw [h_cast]
      _ = C * (B * B⁻¹) := by ring
      _ = C * 1 := by rw [h_inv]
      _ = C := by ring
  exact h_cancel


lemma p_cub_eq_zero (p : ℕ) : ((p : ZMod (p^3)) ^ 3) = 0 := by
  have : (p : ZMod (p^3)) ^ 3 = (((p^3 : ℕ) : ZMod (p^3))) := by push_cast; rfl
  rw [this, ZMod.natCast_self]


lemma p_mul_eq_zero_of_val_divisible_cubed (p : ℕ) (hp : p.Prime) (x : ZMod (p^3)) (h : (x.val : ZMod (p^2)) = 0) :
    (p : ZMod (p^3)) * x = 0 := by
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  have hdvd : p^2 ∣ x.val := by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact h
  obtain ⟨k, hk⟩ := hdvd
  have h_val : x = (x.val : ZMod (p^3)) := by rw [ZMod.natCast_zmod_val]
  rw [h_val, hk]
  have h_eq : p * (p^2 * k) = p^3 * k := by ring
  have h_mul : (p : ZMod (p^3)) * ((p^2 * k : ℕ) : ZMod (p^3)) = ((p * (p^2 * k) : ℕ) : ZMod (p^3)) := by push_cast; rfl
  rw [h_mul, h_eq]
  push_cast
  rw [← Nat.cast_pow]
  have h_zero : ((p^3 : ℕ) : ZMod (p^3)) = 0 := ZMod.natCast_self (p^3)
  rw [h_zero, zero_mul]


lemma mod_p_cub_cast (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ((n % p^3 : ℕ) : ZMod (p^2)) = (n : ZMod (p^2)) := by
  haveI : NeZero (p^2) := ⟨by have := hp.pos; positivity⟩
  have h_eq : (n % p^3) + p^3 * (n / p^3) = n := Nat.mod_add_div n (p^3)
  have h_cast : (n : ZMod (p^2)) = ((n % p^3 : ℕ) : ZMod (p^2)) + ((p^3 * (n / p^3) : ℕ) : ZMod (p^2)) := by
    rw [← Nat.cast_add, h_eq]
  rw [h_cast]
  have h_zero : ((p^3 * (n / p^3) : ℕ) : ZMod (p^2)) = 0 := by
    have h_eq2 : p^3 * (n / p^3) = p^2 * (p * (n / p^3)) := by ring
    rw [h_eq2]
    push_cast
    rw [← Nat.cast_pow]
    rw [ZMod.natCast_self (p^2)]
    ring
  rw [h_zero, add_zero]

lemma val_add_cast_cub (p : ℕ) (hp : p.Prime) (A B : ZMod (p^3)) :
    (((A + B).val : ℕ) : ZMod (p^2)) = (A.val : ZMod (p^2)) + (B.val : ZMod (p^2)) := by
  haveI : NeZero (p^2) := ⟨by have := hp.pos; positivity⟩
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  have h_val := ZMod.val_add A B
  rw [h_val]
  rw [mod_p_cub_cast p hp]
  push_cast
  rfl

lemma sum_val_cast_cub (p : ℕ) (hp : p.Prime) (s : Finset ℕ) (x : ℕ → ZMod (p^3)) :
    (((∑ i ∈ s, x i).val : ℕ) : ZMod (p^2)) = ∑ i ∈ s, (((x i).val : ZMod (p^2))) := by
  haveI : NeZero (p^2) := ⟨by have := hp.pos; positivity⟩
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    rw [val_add_cast_cub p hp]
    rw [ih]

lemma val_mul_cast_cub (p : ℕ) (hp : p.Prime) (A B : ZMod (p^3)) :
    (((A * B).val : ℕ) : ZMod (p^2)) = (A.val : ZMod (p^2)) * (B.val : ZMod (p^2)) := by
  haveI : NeZero (p^2) := ⟨by have := hp.pos; positivity⟩
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  have h_val := ZMod.val_mul A B
  rw [h_val]
  rw [mod_p_cub_cast p hp]
  push_cast
  rfl

lemma inv_val_cast_cub (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    (((j : ZMod (p^3))⁻¹).val : ZMod (p^2)) = (j : ZMod (p^2))⁻¹ := by
  haveI : NeZero (p^2) := ⟨by have := hp.pos; positivity⟩
  haveI : NeZero (p^3) := ⟨by have := hp.pos; positivity⟩
  set X : ZMod (p^2) := (j : ZMod (p^2))
  set Y : ZMod (p^2) := (((j : ZMod (p^3))⁻¹).val : ZMod (p^2))
  set Z : ZMod (p^2) := (j : ZMod (p^2))⁻¹
  have h_cop_p2 : Nat.Coprime j (p^2) := by
    have h1 : ¬ p ∣ j := by
      intro hdvd
      have : p ≤ j := Nat.le_of_dvd (by omega) hdvd
      omega
    have h2 : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
    exact Nat.Coprime.pow_right 2 h2
  have h_XZ : X * Z = 1 := ZMod.coe_mul_inv_eq_one j h_cop_p2
  have h_j_inv : (j : ZMod (p^3)) * (j : ZMod (p^3))⁻¹ = 1 := by
    exact ZMod.coe_mul_inv_eq_one j (j_coprime_p_cub p hp j hj1 hjp)
  have h_cast : (((j : ZMod (p^3)) * (j : ZMod (p^3))⁻¹).val : ZMod (p^2)) = 1 := by
    rw [h_j_inv]
    have hp2 := hp.two_le
    have h_le1 : p ≤ p * p := by nlinarith [hp2]
    have h_le2 : p * p ≤ p * p * p := by nlinarith [hp2]
    have h_le3 : p ≤ p * p * p := by omega
    have h_ring : p^3 = p * p * p := by ring
    have h_le4 : p ≤ p^3 := by rw [h_ring]; exact h_le3
    have h_p1 : 1 < p := by omega
    have h_p3_gt : 1 < p^3 := by omega
    haveI : Fact (1 < p^3) := ⟨h_p3_gt⟩
    have h_one : (1 : ZMod (p^3)).val = 1 := ZMod.val_one (p^3)
    rw [h_one]
    push_cast; rfl
  have h_mul_cast := val_mul_cast_cub p hp (j : ZMod (p^3)) ((j : ZMod (p^3))⁻¹)
  rw [h_cast] at h_mul_cast
  have h_val_j : ((j : ZMod (p^3)).val : ZMod (p^2)) = X := by
    have h_lt : j < p^3 := by
      have hp2 := hp.two_le
      have h_le1 : p ≤ p * p := by nlinarith [hp2]
      have h_le2 : p * p ≤ p * p * p := by nlinarith [hp2]
      have h_le3 : p ≤ p * p * p := by omega
      have h_ring : p^3 = p * p * p := by ring
      have h_le4 : p ≤ p^3 := by rw [h_ring]; exact h_le3
      omega
    rw [ZMod.val_natCast_of_lt h_lt]
  rw [h_val_j] at h_mul_cast
  have h_XY : X * Y = 1 := h_mul_cast.symm
  calc Y
    _ = 1 * Y := by ring
    _ = (Z * X) * Y := by rw [mul_comm Z X, h_XZ]
    _ = Z * (X * Y) := by ring
    _ = Z * 1 := by rw [h_XY]
    _ = Z := by ring


lemma prod_expansion (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ∏ j ∈ Ico 1 p, (1 + (p : ZMod (p^3)) * (2 * (j : ZMod (p^3))⁻¹)) =
    1 + (p : ZMod (p^3)) * (∑ j ∈ Ico 1 p, 2 * (j : ZMod (p^3))⁻¹) +
    (p : ZMod (p^3))^2 * (∑ x ∈ Ico 1 p, ∑ y ∈ Ico 1 p, if x < y then (2 * (x : ZMod (p^3))⁻¹) * (2 * (y : ZMod (p^3))⁻¹) else 0) := by
  have ht3 : (p : ZMod (p^3))^3 = 0 := p_cub_eq_zero p
  exact prod_one_add_t_mul (p : ZMod (p^3)) ht3 (Ico 1 p) (fun j => 2 * (j : ZMod (p^3))⁻¹)




