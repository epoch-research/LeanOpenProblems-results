import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

lemma j_coprime_p_sq (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    Nat.Coprime j (p^2) := by
  have h1 : ¬ p ∣ j := by
    intro hdvd
    have : p ≤ j := Nat.le_of_dvd (by omega) hdvd
    omega
  have h2 : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
  exact Nat.Coprime.pow_right 2 h2

lemma j_inv_mul (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    (j : ZMod (p^2)) * (j : ZMod (p^2))⁻¹ = 1 := by
  exact ZMod.coe_mul_inv_eq_one j (j_coprime_p_sq p hp j hj1 hjp)

lemma sum_inv_eq_sum_inv_p_sub (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹) = ∑ j ∈ Ico 1 p, (((p - j : ℕ) : ZMod (p^2))⁻¹) := by
  apply Finset.sum_nbij' (fun j => p - j) (fun j => p - j)
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
    rw [mem_Ico] at ha
    have : p - (p - a) = a := by omega
    rw [this]

lemma p_sub_j_inv (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    ((p - j : ℕ) : ZMod (p^2))⁻¹ = - (j : ZMod (p^2))⁻¹ - (p : ZMod (p^2)) * ((j : ZMod (p^2))⁻¹ ^ 2) := by
  set A : ZMod (p^2) := ((p - j : ℕ) : ZMod (p^2))
  set Y : ZMod (p^2) := (j : ZMod (p^2))⁻¹
  set p_cast : ZMod (p^2) := (p : ZMod (p^2))
  have h_cop : Nat.Coprime (p - j) (p^2) := by
    have h_pos : 1 ≤ p - j := by omega
    have h_lt : p - j < p := by omega
    exact j_coprime_p_sq p hp (p - j) h_pos h_lt
  have h_inv_mul := ZMod.coe_mul_inv_eq_one (p - j) h_cop
  have h_jY : (j : ZMod (p^2)) * Y = 1 := j_inv_mul p hp j hj1 hjp
  have h_p2 : p_cast^2 = 0 := by
    have : p_cast^2 = (((p^2 : ℕ) : ZMod (p^2))) := by push_cast; rfl
    rw [this]
    rw [ZMod.natCast_self]
  have h_A : A = p_cast - (j : ZMod (p^2)) := by
    have : p - j + j = p := by omega
    have h_eq : A + (j : ZMod (p^2)) = p_cast := by
      change ((p - j : ℕ) : ZMod (p^2)) + (j : ZMod (p^2)) = (p : ZMod (p^2))
      rw [← Nat.cast_add, this]
    rw [← h_eq]
    ring
  have h_mul : A * (- Y - p_cast * Y^2) = 1 := by
    rw [h_A]
    calc (p_cast - (j : ZMod (p^2))) * (- Y - p_cast * Y^2)
      _ = - (p_cast * Y) - p_cast^2 * Y^2 + (j : ZMod (p^2)) * Y + p_cast * ((j : ZMod (p^2)) * Y) * Y := by ring
      _ = - (p_cast * Y) - 0 * Y^2 + 1 + p_cast * 1 * Y := by rw [h_p2, h_jY]
      _ = 1 := by ring
  have h_cancel : A⁻¹ = - Y - p_cast * Y^2 := by
    calc A⁻¹
      _ = 1 * A⁻¹ := by ring
      _ = (A * (- Y - p_cast * Y^2)) * A⁻¹ := by rw [h_mul]
      _ = (A * A⁻¹) * (- Y - p_cast * Y^2) := by ring
      _ = 1 * (- Y - p_cast * Y^2) := by rw [h_inv_mul]
      _ = - Y - p_cast * Y^2 := by ring
  exact h_cancel

lemma p_mul_eq_zero_of_val_divisible (p : ℕ) (hp : p.Prime) (x : ZMod (p^2)) (h : (x.val : ZMod p) = 0) :
    (p : ZMod (p^2)) * x = 0 := by
  have h_p_pos : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  have hdvd : p ∣ x.val := by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact h
  obtain ⟨k, hk⟩ := hdvd
  have h_val : x = (x.val : ZMod (p^2)) := by rw [ZMod.natCast_zmod_val]
  rw [h_val, hk]
  have : p * (p * k) = p^2 * k := by ring
  have h_mul : (p : ZMod (p^2)) * ((p * k : ℕ) : ZMod (p^2)) = ((p * (p * k) : ℕ) : ZMod (p^2)) := by push_cast; rfl
  rw [h_mul, this]
  push_cast
  have h_p2 : (p : ZMod (p^2))^2 = 0 := by
    have h_eq : (p : ZMod (p^2))^2 = ((p^2 : ℕ) : ZMod (p^2)) := by push_cast; rfl
    rw [h_eq, ZMod.natCast_self]
  rw [h_p2, zero_mul]

lemma mod_p_sq_cast (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ((n % p^2 : ℕ) : ZMod p) = (n : ZMod p) := by
  have h_eq : (n % p^2) + p^2 * (n / p^2) = n := Nat.mod_add_div n (p^2)
  have h_cast : (n : ZMod p) = ((n % p^2 : ℕ) : ZMod p) + ((p^2 * (n / p^2) : ℕ) : ZMod p) := by
    rw [← Nat.cast_add, h_eq]
  rw [h_cast]
  have h_zero : ((p^2 * (n / p^2) : ℕ) : ZMod p) = 0 := by
    push_cast
    have : (p : ZMod p) = 0 := ZMod.natCast_self p
    rw [this]
    ring
  rw [h_zero, add_zero]

lemma val_add_cast (p : ℕ) (hp : p.Prime) (A B : ZMod (p^2)) :
    (((A + B).val : ℕ) : ZMod p) = (A.val : ZMod p) + (B.val : ZMod p) := by
  have : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  have h_val := ZMod.val_add A B
  rw [h_val]
  rw [mod_p_sq_cast p hp]
  push_cast
  rfl

lemma sum_val_cast (p : ℕ) (hp : p.Prime) (s : Finset ℕ) (x : ℕ → ZMod (p^2)) :
    (((∑ i ∈ s, x i).val : ℕ) : ZMod p) = ∑ i ∈ s, (((x i).val : ZMod p)) := by
  have : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    rw [val_add_cast p hp]
    rw [ih]

lemma val_mul_cast (p : ℕ) (hp : p.Prime) (A B : ZMod (p^2)) :
    (((A * B).val : ℕ) : ZMod p) = (A.val : ZMod p) * (B.val : ZMod p) := by
  have : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  have h_val := ZMod.val_mul A B
  rw [h_val]
  rw [mod_p_sq_cast p hp]
  push_cast
  rfl

lemma inv_val_cast (p : ℕ) (hp : p.Prime) (j : ℕ) (hj1 : 1 ≤ j) (hjp : j < p) :
    (((j : ZMod (p^2))⁻¹).val : ZMod p) = (j : ZMod p)⁻¹ := by
  have : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  set X : ZMod p := (j : ZMod p)
  set Y : ZMod p := (((j : ZMod (p^2))⁻¹).val : ZMod p)
  set Z : ZMod p := (j : ZMod p)⁻¹
  have h_cop_p : Nat.Coprime j p := by
    have h1 : ¬ p ∣ j := by
      intro hdvd
      have : p ≤ j := Nat.le_of_dvd (by omega) hdvd
      omega
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
  have h_XZ : X * Z = 1 := ZMod.coe_mul_inv_eq_one j h_cop_p
  have h_j_inv : (j : ZMod (p^2)) * (j : ZMod (p^2))⁻¹ = 1 := j_inv_mul p hp j hj1 hjp
  have h_cast : (((j : ZMod (p^2)) * (j : ZMod (p^2))⁻¹).val : ZMod p) = 1 := by
    rw [h_j_inv]
    have hp2 : p ≥ 2 := hp.two_le
    haveI : Fact (1 < p^2) := ⟨by nlinarith⟩
    have : (1 : ZMod (p^2)).val = 1 := ZMod.val_one _
    rw [this]
    push_cast; rfl
  have h_mul_cast := val_mul_cast p hp (j : ZMod (p^2)) ((j : ZMod (p^2))⁻¹)
  rw [h_cast] at h_mul_cast
  have h_val_j : ((j : ZMod (p^2)).val : ZMod p) = X := by
    have h_lt : j < p^2 := by
      calc j < p := hjp
      _ ≤ p^2 := by nlinarith
    rw [ZMod.val_natCast_of_lt h_lt]
  rw [h_val_j] at h_mul_cast
  have h_XY : X * Y = 1 := h_mul_cast.symm
  calc Y
    _ = 1 * Y := by ring
    _ = (Z * X) * Y := by rw [mul_comm Z X, h_XZ]
    _ = Z * (X * Y) := by ring
    _ = Z * 1 := by rw [h_XY]
    _ = Z := by ring

lemma sum_inv_eq_zero_mod_p_sq (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹) = 0 := by
  have : p > 0 := hp.pos
  haveI : NeZero (p^2) := ⟨by nlinarith⟩
  set S : ZMod (p^2) := ∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹)
  have h_p_sub : S = ∑ j ∈ Ico 1 p, (((p - j : ℕ) : ZMod (p^2))⁻¹) := sum_inv_eq_sum_inv_p_sub p hp hp5
  have h_congr : ∑ j ∈ Ico 1 p, (((p - j : ℕ) : ZMod (p^2))⁻¹) = ∑ j ∈ Ico 1 p, (- (j : ZMod (p^2))⁻¹ - (p : ZMod (p^2)) * ((j : ZMod (p^2))⁻¹ ^ 2)) := by
    apply sum_congr rfl
    intro j hj
    rw [mem_Ico] at hj
    exact p_sub_j_inv p hp j hj.1 hj.2
  rw [← h_p_sub] at h_congr
  have h_split : ∑ j ∈ Ico 1 p, (- (j : ZMod (p^2))⁻¹ - (p : ZMod (p^2)) * ((j : ZMod (p^2))⁻¹ ^ 2)) =
      - S - (p : ZMod (p^2)) * (∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹ ^ 2)) := by
    rw [sum_sub_distrib, sum_neg_distrib, ← mul_sum]
  rw [h_split] at h_congr
  have h_p_sum : (p : ZMod (p^2)) * (∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹ ^ 2)) = 0 := by
    apply p_mul_eq_zero_of_val_divisible p hp
    rw [sum_val_cast p hp]
    have h_pow_cast : ∀ j ∈ Ico 1 p, ((((j : ZMod (p^2))⁻¹ ^ 2).val : ℕ) : ZMod p) = (j : ZMod p)⁻¹ ^ 2 := by
      intro j hj
      rw [mem_Ico] at hj
      have h_sq : (j : ZMod (p^2))⁻¹ ^ 2 = (j : ZMod (p^2))⁻¹ * (j : ZMod (p^2))⁻¹ := by ring
      rw [h_sq]
      rw [val_mul_cast p hp]
      rw [inv_val_cast p hp j hj.1 hj.2]
      ring
    have h_congr2 : ∑ j ∈ Ico 1 p, ((((j : ZMod (p^2))⁻¹ ^ 2).val : ℕ) : ZMod p) = ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹ ^ 2) := by
      apply sum_congr rfl
      intro j hj
      exact h_pow_cast j hj
    rw [h_congr2]
    sorry
  have h_two_S : (2 : ZMod (p^2)) * S = 0 := by
    calc (2 : ZMod (p^2)) * S
      _ = S + S := by ring
      _ = S + (-S - (p : ZMod (p^2)) * (∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹ ^ 2))) := by nth_rw 2 [h_congr]
      _ = - ((p : ZMod (p^2)) * (∑ j ∈ Ico 1 p, ((j : ZMod (p^2))⁻¹ ^ 2))) := by ring
      _ = - 0 := by rw [h_p_sum]
      _ = 0 := by ring
  have h_cop_two : Nat.Coprime 2 (p^2) := by
    have h1 : ¬ p ∣ 2 := by
      intro hdvd
      have : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
      omega
    have h2 : Nat.Coprime 2 p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
    exact Nat.Coprime.pow_right 2 h2
  have h_inv_two := ZMod.coe_mul_inv_eq_one 2 h_cop_two
  have h_one : (2 : ZMod (p^2))⁻¹ * 2 = 1 := by
    rw [mul_comm]
    exact h_inv_two
  calc S
    _ = 1 * S := by ring
    _ = ((2 : ZMod (p^2))⁻¹ * 2) * S := by rw [h_one]
    _ = (2 : ZMod (p^2))⁻¹ * (2 * S) := by ring
    _ = (2 : ZMod (p^2))⁻¹ * 0 := by rw [h_two_S]
    _ = 0 := by ring











