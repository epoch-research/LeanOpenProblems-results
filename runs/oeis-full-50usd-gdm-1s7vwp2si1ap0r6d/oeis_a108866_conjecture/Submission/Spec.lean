import FormalConjectures.Util.ProblemImports

/--
A108866: Numerator of $\sum_{k=1}^n \frac{2^k}{k}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Finset.range n) fun i : ℕ => (2 : Rat) ^ (i + 1) / ((i + 1) : Rat)).num.natAbs

/--
The rational number inside the numerator function in the conjecture.
$$ -\frac{2}{n} + \sum_{k=1}^n \frac{2^k}{k} $$
-/
noncomputable def rat_expression (n : ℕ) : Rat :=
  if h : n > 0 then
    (-2 : Rat) / (n : Rat) + Finset.sum (Finset.range n) fun i : ℕ => (2 : Rat) ^ (i + 1) / ((i + 1) : Rat)
  else
    0

lemma rat_expression_split (n : ℕ) (hn : n > 0) :
    rat_expression n = Finset.sum (Finset.range (n - 1)) (fun i : ℕ => (2 : Rat) ^ (i + 1) / ((i + 1) : Rat)) + ((2 : Rat)^n - 2) / (n : Rat) := by
  unfold rat_expression
  rw [dif_pos hn]
  have h_eq : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
  generalize h_m : n - 1 = m
  have hn_eq : n = m + 1 := by omega
  rw [hn_eq]
  rw [Finset.sum_range_succ]
  generalize h_sum : Finset.sum (Finset.range m) (fun i => (2 : Rat) ^ (i + 1) / ((i + 1) : Rat)) = S
  push_cast
  ring

def rat_to_zmod (m : ℕ) (x : ℚ) : ZMod m :=
  (x.num : ZMod m) * (x.den : ZMod m)⁻¹

theorem rat_eq_zero_iff (m : ℕ) (x : ℚ) (h : Nat.Coprime x.den m) :
    rat_to_zmod m x = 0 ↔ (x.num : ZMod m) = 0 := by
  unfold rat_to_zmod
  constructor
  · intro h_eq
    have h_unit : IsUnit (x.den : ZMod m) := by
      rwa [ZMod.isUnit_iff_coprime]
    have h_mul : ((x.num : ZMod m) * (x.den : ZMod m)⁻¹) * (x.den : ZMod m) = 0 * (x.den : ZMod m) := by
      rw [h_eq]
    rw [zero_mul] at h_mul
    rw [mul_assoc] at h_mul
    rw [ZMod.inv_mul_of_unit (x.den : ZMod m) h_unit] at h_mul
    rw [mul_one] at h_mul
    exact h_mul
  · intro h_eq
    rw [h_eq, zero_mul]

theorem zmod_zero_iff (m : ℕ) (a : ℤ) :
    (a : ZMod m) = 0 ↔ a ≡ 0 [ZMOD m] := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Iff.symm (Int.modEq_zero_iff_dvd)

theorem rat_modeq_zero_iff (m : ℕ) (x : ℚ) (h : Nat.Coprime x.den m) :
    x.num ≡ 0 [ZMOD m] ↔ rat_to_zmod m x = 0 := by
  rw [← zmod_zero_iff]
  exact Iff.symm (rat_eq_zero_iff m x h)

theorem rat_to_zmod_add (m : ℕ) (x y : ℚ) (hx : Nat.Coprime x.den m) (hy : Nat.Coprime y.den m) :
    rat_to_zmod m (x + y) = rat_to_zmod m x + rat_to_zmod m y := by
  unfold rat_to_zmod
  have h_prod : Nat.Coprime (x.den * y.den) m := Nat.Coprime.mul_left hx hy
  have h_sum_den : (x + y).den ∣ x.den * y.den := Rat.add_den_dvd x y
  have hxy_coprime : Nat.Coprime (x + y).den m := Nat.Coprime.of_dvd_left h_sum_den h_prod
  have h_unit_x : IsUnit (x.den : ZMod m) := by rwa [ZMod.isUnit_iff_coprime]
  have h_unit_y : IsUnit (y.den : ZMod m) := by rwa [ZMod.isUnit_iff_coprime]
  have h_unit_xy : IsUnit ((x + y).den : ZMod m) := by rwa [ZMod.isUnit_iff_coprime]
  have h_id : (((x + y).num : ZMod m) * (x.den : ZMod m) * (y.den : ZMod m)) =
      ((x.num : ZMod m) * (y.den : ZMod m) + (y.num : ZMod m) * (x.den : ZMod m)) * ((x + y).den : ZMod m) := by
    have h_cast := congrArg (fun (a : ℤ) => (a : ZMod m)) (Rat.add_num_den' x y)
    push_cast at h_cast
    exact h_cast
  have h_goal_eq : ((x + y).num : ZMod m) * (((x + y).den : ZMod m))⁻¹ = (x.num : ZMod m) * ((x.den : ZMod m))⁻¹ + (y.num : ZMod m) * ((y.den : ZMod m))⁻¹ := by
    apply (IsUnit.mul_right_inj h_unit_xy).mp
    rw [mul_comm, mul_assoc, ZMod.inv_mul_of_unit ((x + y).den : ZMod m) h_unit_xy, mul_one]
    apply (IsUnit.mul_right_inj h_unit_x).mp
    apply (IsUnit.mul_right_inj h_unit_y).mp
    have h_u_x : ((x.den : ZMod m))⁻¹ * (x.den : ZMod m) = 1 := ZMod.inv_mul_of_unit (x.den : ZMod m) h_unit_x
    have h_u_y : ((y.den : ZMod m))⁻¹ * (y.den : ZMod m) = 1 := ZMod.inv_mul_of_unit (y.den : ZMod m) h_unit_y
    have h_rhs : (y.den : ZMod m) * ((x.den : ZMod m) * (((x + y).den : ZMod m) * ((x.num : ZMod m) * ((x.den : ZMod m))⁻¹ + (y.num : ZMod m) * ((y.den : ZMod m))⁻¹))) =
        ((x.num : ZMod m) * (y.den : ZMod m) + (y.num : ZMod m) * (x.den : ZMod m)) * ((x + y).den : ZMod m) := by
      calc (y.den : ZMod m) * ((x.den : ZMod m) * (((x + y).den : ZMod m) * ((x.num : ZMod m) * ((x.den : ZMod m))⁻¹ + (y.num : ZMod m) * ((y.den : ZMod m))⁻¹)))
        _ = ((x.num : ZMod m) * (((x.den : ZMod m))⁻¹ * (x.den : ZMod m)) * (y.den : ZMod m) + (y.num : ZMod m) * (((y.den : ZMod m))⁻¹ * (y.den : ZMod m)) * (x.den : ZMod m)) * ((x + y).den : ZMod m) := by ring
        _ = ((x.num : ZMod m) * 1 * (y.den : ZMod m) + (y.num : ZMod m) * 1 * (x.den : ZMod m)) * ((x + y).den : ZMod m) := by rw [h_u_x, h_u_y]
        _ = ((x.num : ZMod m) * (y.den : ZMod m) + (y.num : ZMod m) * (x.den : ZMod m)) * ((x + y).den : ZMod m) := by ring
    have h_lhs : (y.den : ZMod m) * ((x.den : ZMod m) * ((x + y).num : ZMod m)) =
        ((x + y).num : ZMod m) * (x.den : ZMod m) * (y.den : ZMod m) := by ring
    rw [h_lhs, h_id, h_rhs]
  exact h_goal_eq

theorem coprime_sum_den (m : ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, Nat.Coprime (f i).den m) :
    Nat.Coprime (s.sum f).den m := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : ℚ).den = 1 := rfl
    rw [h0]
    exact Nat.coprime_one_left m
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h_fi : Nat.Coprime (f a).den m := hf a (Finset.mem_insert_self a s)
    have h_sum' : ∀ i ∈ s, Nat.Coprime (f i).den m := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h_ih := ih h_sum'
    have h_prod : Nat.Coprime ((f a).den * (Finset.sum s f).den) m := Nat.Coprime.mul_left h_fi h_ih
    have h_dvd := Rat.add_den_dvd (f a) (Finset.sum s f)
    exact Nat.Coprime.of_dvd_left h_dvd h_prod

theorem rat_to_zmod_sum (m : ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, Nat.Coprime (f i).den m) :
    rat_to_zmod m (s.sum f) = s.sum (fun i => rat_to_zmod m (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold rat_to_zmod
    have h0 : (0 : ℚ).num = 0 := rfl
    have h1 : (0 : ℚ).den = 1 := rfl
    rw [h0, h1]
    push_cast
    rw [zero_mul]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h_fi : Nat.Coprime (f a).den m := hf a (Finset.mem_insert_self a s)
    have h_sum' : ∀ i ∈ s, Nat.Coprime (f i).den m := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h_ih := ih h_sum'
    have h_cop : Nat.Coprime (Finset.sum s f).den m := coprime_sum_den m s f h_sum'
    rw [rat_to_zmod_add m (f a) (Finset.sum s f) h_fi h_cop]
    rw [h_ih]



theorem rat_pow_sub_eq_cast_sub {p : ℕ} (hp : p.Prime) : ((2 : Rat)^p - 2) = (((2^p - 2 : ℕ) : Rat)) := by
  have hp_pos : p > 0 := hp.pos
  have hp1 : 2^p ≥ 2 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp_pos)
    rw [hk]
    have h2k : 2^k ≥ 1 := Nat.one_le_pow k 2 (by decide)
    omega
  have h_sub : (((2^p - 2 : ℕ) : Rat)) = ((2^p : ℕ) : Rat) - 2 := Nat.cast_sub hp1
  push_cast at h_sub
  exact h_sub.symm

theorem rat_div_p {p : ℕ} (hp : p.Prime) :
    (((2^p - 2 : ℕ) : Rat)) / (p : Rat) = ((( (2^p - 2) / p : ℕ) : ℤ) : Rat) := by
  have hp_pos : p > 0 := hp.pos
  have h_dvd : p ∣ 2^p - 2 := by
    have h_dvd_int : (p : ℤ) ∣ (2 : ℤ)^p - 2 := Int.prime_dvd_pow_self_sub hp 2
    have h_eq_int : ((2^p - 2 : ℕ) : ℤ) = (2 : ℤ)^p - 2 := by
      have hp1 : 2^p ≥ 2 := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp_pos)
        rw [hk]
        have h2k : 2^k ≥ 1 := Nat.one_le_pow k 2 (by decide)
        omega
      exact Nat.cast_sub hp1
    rw [← h_eq_int] at h_dvd_int
    exact_mod_cast h_dvd_int
  have h_eq : (((2^p - 2 : ℕ) : Rat)) = (p : Rat) * (((2^p - 2) / p : ℕ) : Rat) := by
    have h_eq_nat : 2^p - 2 = p * ((2^p - 2) / p) := (Nat.mul_div_cancel' h_dvd).symm
    exact_mod_cast h_eq_nat
  rw [h_eq]
  have hp_ne_zero : (p : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hp_pos
  rw [mul_div_cancel_left₀ _ hp_ne_zero]
  push_cast
  rfl

theorem rat_to_zmod_cast (m : ℕ) (a : ℤ) : rat_to_zmod m (a : ℚ) = (a : ZMod m) := by
  unfold rat_to_zmod
  simp


theorem rat_to_zmod_mul (m : ℕ) (x y : ℚ) (hx : Nat.Coprime x.den m) (hy : Nat.Coprime y.den m) :
    rat_to_zmod m (x * y) = rat_to_zmod m x * rat_to_zmod m y := by
  unfold rat_to_zmod
  have h_prod : Nat.Coprime (x.den * y.den) m := Nat.Coprime.mul_left hx hy
  have h_xy_den : (x * y).den ∣ x.den * y.den := Rat.mul_den_dvd x y
  have hxy_coprime : Nat.Coprime (x * y).den m := Nat.Coprime.of_dvd_left h_xy_den h_prod
  have h_unit_x : IsUnit (x.den : ZMod m) := by rwa [ZMod.isUnit_iff_coprime]
  have h_unit_y : IsUnit (y.den : ZMod m) := by rwa [ZMod.isUnit_iff_coprime]
  have h_unit_xy : IsUnit ((x * y).den : ZMod m) := by rwa [ZMod.isUnit_iff_coprime]
  have h_id : (((x * y).num : ZMod m) * (x.den : ZMod m) * (y.den : ZMod m)) =
      ((x.num : ZMod m) * (y.num : ZMod m)) * ((x * y).den : ZMod m) := by
    have h_cast := congrArg (fun (a : ℤ) => (a : ZMod m)) (Rat.mul_num_den' x y)
    push_cast at h_cast
    exact h_cast
  have h_goal_eq : ((x * y).num : ZMod m) * (((x * y).den : ZMod m))⁻¹ = (x.num : ZMod m) * ((x.den : ZMod m))⁻¹ * ((y.num : ZMod m) * ((y.den : ZMod m))⁻¹) := by
    apply (IsUnit.mul_right_inj h_unit_xy).mp
    rw [mul_comm, mul_assoc, ZMod.inv_mul_of_unit ((x * y).den : ZMod m) h_unit_xy, mul_one]
    apply (IsUnit.mul_right_inj h_unit_x).mp
    apply (IsUnit.mul_right_inj h_unit_y).mp
    have h_u_x : ((x.den : ZMod m))⁻¹ * (x.den : ZMod m) = 1 := ZMod.inv_mul_of_unit (x.den : ZMod m) h_unit_x
    have h_u_y : ((y.den : ZMod m))⁻¹ * (y.den : ZMod m) = 1 := ZMod.inv_mul_of_unit (y.den : ZMod m) h_unit_y
    have h_rhs : (y.den : ZMod m) * ((x.den : ZMod m) * (((x * y).den : ZMod m) * ((x.num : ZMod m) * ((x.den : ZMod m))⁻¹ * ((y.num : ZMod m) * ((y.den : ZMod m))⁻¹)))) =
        ((x.num : ZMod m) * (y.num : ZMod m)) * ((x * y).den : ZMod m) := by
      calc (y.den : ZMod m) * ((x.den : ZMod m) * (((x * y).den : ZMod m) * ((x.num : ZMod m) * ((x.den : ZMod m))⁻¹ * ((y.num : ZMod m) * ((y.den : ZMod m))⁻¹))))
        _ = (((x.num : ZMod m) * (y.num : ZMod m)) * (((x.den : ZMod m))⁻¹ * (x.den : ZMod m)) * (((y.den : ZMod m))⁻¹ * (y.den : ZMod m))) * ((x * y).den : ZMod m) := by ring
        _ = (((x.num : ZMod m) * (y.num : ZMod m)) * 1 * 1) * ((x * y).den : ZMod m) := by rw [h_u_x, h_u_y]
        _ = ((x.num : ZMod m) * (y.num : ZMod m)) * ((x * y).den : ZMod m) := by ring
    have h_lhs : (y.den : ZMod m) * ((x.den : ZMod m) * ((x * y).num : ZMod m)) =
        ((x * y).num : ZMod m) * (x.den : ZMod m) * (y.den : ZMod m) := by ring
    rw [h_lhs, h_id, h_rhs]
  exact h_goal_eq

theorem rat_div_den_dvd (a : ℤ) (b : ℕ) (hb0 : b ≠ 0) :
    ((a : ℚ) / (b : ℚ)).den ∣ b := by
  have h_div_mul : ((a : ℚ) / (b : ℚ)) = (a : ℚ) * (b : ℚ)⁻¹ := rfl
  rw [h_div_mul]
  have h_den_dvd := Rat.mul_den_dvd (a : ℚ) (b : ℚ)⁻¹
  have h_a_den : (a : ℚ).den = 1 := rfl
  rw [h_a_den, one_mul] at h_den_dvd
  have h_b_inv : ((b : ℚ)⁻¹).den = b := by
    exact Rat.inv_natCast_den_of_pos (Nat.pos_of_ne_zero hb0)
  rw [h_b_inv] at h_den_dvd
  exact h_den_dvd

theorem rat_to_zmod_div_of_ne_zero (m : ℕ) (a : ℤ) (b : ℕ) (hb : Nat.Coprime b m) (hb0 : b ≠ 0) :
    rat_to_zmod m ((a : ℚ) / (b : ℚ)) = (a : ZMod m) * (b : ZMod m)⁻¹ := by
  have h_div_eq : ((a : ℚ) / (b : ℚ)) * (b : ℚ) = (a : ℚ) := by
    apply div_mul_cancel₀
    exact_mod_cast hb0
  have h_div_den := rat_div_den_dvd a b hb0

  have hxy_coprime : Nat.Coprime ((a : ℚ) / (b : ℚ)).den m := Nat.Coprime.of_dvd_left h_div_den hb
  have h_cop_b : Nat.Coprime (b : ℚ).den m := by
    have h_den : (b : ℚ).den = 1 := rfl
    rw [h_den]
    exact Nat.coprime_one_left m
  have h_mul := rat_to_zmod_mul m ((a : ℚ) / (b : ℚ)) (b : ℚ) hxy_coprime h_cop_b
  rw [h_div_eq] at h_mul
  rw [rat_to_zmod_cast] at h_mul
  have h_b_cast : rat_to_zmod m (b : ℚ) = (b : ZMod m) := by
    unfold rat_to_zmod
    simp
  rw [h_b_cast] at h_mul
  have h_unit_b : IsUnit (b : ZMod m) := by rwa [ZMod.isUnit_iff_coprime]
  have h_goal : rat_to_zmod m ((a : ℚ) / (b : ℚ)) = (a : ZMod m) * (b : ZMod m)⁻¹ := by
    rw [h_mul, mul_assoc, ZMod.mul_inv_of_unit (b : ZMod m) h_unit_b, mul_one]
  exact h_goal

theorem prime_coprime_pow {p : ℕ} (hp : p.Prime) {a : ℕ} (ha_pos : a > 0) (ha_lt : a < p) :
    Nat.Coprime a (p^2) := by
  have hp_cop : Nat.Coprime a p := Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha_pos ha_lt))
  exact Nat.Coprime.pow_right 2 hp_cop

theorem choose_div_succ (n k : ℕ) :
    ((Nat.choose n k : ℚ) / (k + 1 : ℚ)) = (Nat.choose (n + 1) (k + 1) : ℚ) / (n + 1 : ℚ) := by
  have h_eq_nat := Nat.add_one_mul_choose_eq n k
  have h_eq_rat : (( (n + 1) * Nat.choose n k : ℕ) : ℚ) = ((Nat.choose (n + 1) (k + 1) * (k + 1) : ℕ) : ℚ) := by
    congr 1
  push_cast at h_eq_rat
  have hn_ne : (n + 1 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hk_ne : (k + 1 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  have h_goal : (Nat.choose n k : ℚ) / (k + 1 : ℚ) = (Nat.choose (n + 1) (k + 1) : ℚ) / (n + 1 : ℚ) := by
    field_simp [hn_ne, hk_ne]
    rw [mul_comm (Nat.choose n k : ℚ) (n + 1 : ℚ), h_eq_rat]
    ring
  exact h_goal

theorem choose_div_succ_sum (m : ℕ) :
    Finset.sum (Finset.range m) (fun i => (Nat.choose m i : ℚ) / (i + 1 : ℚ)) =
    ((2 : ℚ)^(m + 1) - 2) / (m + 1 : ℚ) := by
  have h_term : ∀ i ∈ Finset.range m, (Nat.choose m i : ℚ) / (i + 1 : ℚ) = (Nat.choose (m + 1) (i + 1) : ℚ) / (m + 1 : ℚ) := by
    intro i _
    exact choose_div_succ m i
  rw [Finset.sum_congr rfl h_term]
  rw [← Finset.sum_div]
  have h_split : Finset.sum (Finset.range (m + 2)) (fun j => (Nat.choose (m + 1) j : ℚ)) =
      (Nat.choose (m + 1) 0 : ℚ) + Finset.sum (Finset.range m) (fun i => (Nat.choose (m + 1) (i + 1) : ℚ)) + (Nat.choose (m + 1) (m + 1) : ℚ) := by
    rw [Finset.sum_range_succ']
    rw [Finset.sum_range_succ]
    ring
  have h_sum_choose : Finset.sum (Finset.range (m + 2)) (fun j => (Nat.choose (m + 1) j : ℚ)) = (2 : ℚ)^(m + 1) := by
    have h_nat := Nat.sum_range_choose (m + 1)
    exact_mod_cast h_nat
  have h_choose_0 : (Nat.choose (m + 1) 0 : ℚ) = 1 := by simp
  have h_choose_self : (Nat.choose (m + 1) (m + 1) : ℚ) = 1 := by simp
  rw [h_choose_0, h_choose_self] at h_split
  have h_sum_eq : Finset.sum (Finset.range m) (fun i => (Nat.choose (m + 1) (i + 1) : ℚ)) = (2 : ℚ)^(m + 1) - 2 := by
    rw [← h_sum_choose, h_split]
    ring
  rw [h_sum_eq]


theorem rat_expression_eq_sum {p : ℕ} (hp : p.Prime) (hp3 : p > 3) :
    rat_expression p = Finset.sum (Finset.range (p - 1)) (fun i => ((2 : ℚ)^(i + 1) + (Nat.choose (p - 1) i : ℚ)) / (i + 1 : ℚ)) := by
  have hp_pos : p > 0 := hp.pos
  rw [rat_expression_split p hp_pos]
  rw [rat_pow_sub_eq_cast_sub hp]
  rw [rat_div_p hp]
  have h_cast_eq : ((( (2^p - 2) / p : ℕ) : ℤ) : Rat) = ((2 : ℚ)^p - 2) / (p : ℚ) := by
    rw [← rat_div_p hp, rat_pow_sub_eq_cast_sub hp]
  rw [h_cast_eq]
  have hp_eq : p - 1 + 1 = p := Nat.sub_add_cancel hp_pos
  have h_choose_sum := choose_div_succ_sum (p - 1)
  have h_choose_sum_eq : ((2 : ℚ)^(p - 1 + 1) - 2) / (↑(p - 1) + 1 : ℚ) = ((2 : ℚ)^p - 2) / (p : ℚ) := by
    congr 2
    · rw [hp_eq]
    · have h_nat : (p - 1) + 1 = p := hp_eq
      exact_mod_cast h_nat
  rw [h_choose_sum_eq] at h_choose_sum
  rw [← h_choose_sum]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext i
  ring

theorem rat_expression_den_coprime {p : ℕ} (hp : p.Prime) (hp3 : p > 3) :
    Nat.Coprime (rat_expression p).den (p^2) := by
  rw [rat_expression_eq_sum hp hp3]
  apply coprime_sum_den
  intro i hi
  simp only [Finset.mem_range] at hi
  have h_eq_cast : ((2 : ℚ) ^ (i + 1) + ↑((p - 1).choose i)) / (i + 1 : ℚ) = ((( (2^(i + 1) : ℕ) + (p - 1).choose i : ℤ) : ℚ)) / (((i + 1 : ℕ) : ℚ)) := by
    push_cast
    rfl
  rw [h_eq_cast]
  have h_div_den := rat_div_den_dvd (((2^(i + 1) : ℕ) + (p - 1).choose i : ℤ)) (i + 1) (Nat.succ_ne_zero i)
  have h_cop : Nat.Coprime (i + 1) (p^2) := by
    apply prime_coprime_pow hp (Nat.succ_pos i)
    omega
  exact Nat.Coprime.of_dvd_left h_div_den h_cop

theorem rat_expression_prime_to_zmod {p : ℕ} (hp : p.Prime) (hp3 : p > 3) :
    rat_to_zmod (p^2) (rat_expression p) = Finset.sum (Finset.range (p - 1)) (fun i =>
      (((2^(i + 1) : ℕ) + (p - 1).choose i : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹) := by
  have hp_pos : p > 0 := hp.pos
  rw [rat_expression_eq_sum hp hp3]
  have h_cop_sum : ∀ i ∈ Finset.range (p - 1), Nat.Coprime (((2 : ℚ)^(i + 1) + (Nat.choose (p - 1) i : ℚ)) / (i + 1 : ℚ)).den (p^2) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have h_eq_cast : ((2 : ℚ) ^ (i + 1) + ↑((p - 1).choose i)) / (i + 1 : ℚ) = ((( (2^(i + 1) : ℕ) + (p - 1).choose i : ℤ) : ℚ)) / (((i + 1 : ℕ) : ℚ)) := by
      push_cast
      rfl
    rw [h_eq_cast]
    have h_div_den := rat_div_den_dvd (((2^(i + 1) : ℕ) + (p - 1).choose i : ℤ)) (i + 1) (Nat.succ_ne_zero i)
    have h_cop_i : Nat.Coprime (i + 1) (p^2) := by
      apply prime_coprime_pow hp (Nat.succ_pos i)
      omega
    exact Nat.Coprime.of_dvd_left h_div_den h_cop_i
  rw [rat_to_zmod_sum (p^2) (Finset.range (p - 1)) _ h_cop_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have h_eq_cast : ((2 : ℚ) ^ (i + 1) + ↑((p - 1).choose i)) / (i + 1 : ℚ) = ((( (2^(i + 1) : ℕ) + (p - 1).choose i : ℤ) : ℚ)) / (((i + 1 : ℕ) : ℚ)) := by
    push_cast
    rfl
  rw [h_eq_cast]
  have h_cop_i : Nat.Coprime (i + 1) (p^2) := by
    apply prime_coprime_pow hp (Nat.succ_pos i)
    omega
  rw [rat_to_zmod_div_of_ne_zero (p^2) (((2^(i + 1) : ℕ) + (p - 1).choose i : ℤ)) (i + 1) h_cop_i (Nat.succ_ne_zero i)]
  push_cast
  rfl




lemma choose_p_sub_one_mod_p {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p) :
    ((p - 1).choose i : ZMod p) = (-1 : ZMod p)^i := by
  induction i with
  | zero =>
    simp
  | succ i ih =>
    have hi_succ : i + 1 < p := hi
    have hi_lt : i < p := by omega
    have h_ih := ih hi_lt
    have h_mul := Nat.choose_succ_right_eq (p - 1) i
    have h_cast : (((p - 1).choose (i + 1) * (i + 1) : ℕ) : ZMod p) = (((p - 1).choose i * (p - 1 - i) : ℕ) : ZMod p) := by
      congr 1
    push_cast at h_cast
    have h_sub : ((p - 1 - i : ℕ) : ZMod p) = - (i + 1 : ZMod p) := by
      have hp_pos : p > 0 := hp.pos
      have h_nat : p - 1 - i + (i + 1) = p := by omega
      have h_eq_cast : (((p - 1 - i + (i + 1) : ℕ) : ZMod p)) = ((p : ℕ) : ZMod p) := by
        congr 1
      have h_sum_cast : (((p - 1 - i) + (i + 1) : ℕ) : ZMod p) = ((p - 1 - i : ℕ) : ZMod p) + ((i + 1 : ℕ) : ZMod p) := by
        push_cast
        rfl
      rw [h_sum_cast] at h_eq_cast
      have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
      rw [hp0] at h_eq_cast
      have h_eq_cast_nf : ((p - 1 - i : ℕ) : ZMod p) + (i + 1 : ZMod p) = 0 := by
        have : ((i + 1 : ℕ) : ZMod p) = (i + 1 : ZMod p) := by push_cast; rfl
        rw [this] at h_eq_cast
        exact h_eq_cast
      calc ((p - 1 - i : ℕ) : ZMod p) = ((p - 1 - i : ℕ) : ZMod p) + (i + 1 : ZMod p) - (i + 1 : ZMod p) := by ring
      _ = 0 - (i + 1 : ZMod p) := by rw [h_eq_cast_nf]
      _ = - (i + 1 : ZMod p) := by ring
    rw [h_sub, h_ih] at h_cast
    have h_unit : IsUnit ((i + 1 : ℕ) : ZMod p) := by
      rw [ZMod.isUnit_iff_coprime]
      exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hi_succ))
    have h_rhs_eq : (-1 : ZMod p)^i * - (i + 1 : ZMod p) = (i + 1 : ZMod p) * (-1 : ZMod p)^(i + 1) := by ring
    rw [h_rhs_eq] at h_cast
    have h_lhs : ((p - 1).choose (i + 1) : ZMod p) * (i + 1 : ZMod p) = (i + 1 : ZMod p) * ((p - 1).choose (i + 1) : ZMod p) := by ring
    rw [h_lhs] at h_cast
    have h_unit_cast : IsUnit (i + 1 : ZMod p) := by
      have : (i + 1 : ZMod p) = ((i + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [this]
      exact h_unit
    exact (IsUnit.mul_right_inj h_unit_cast).mp h_cast

lemma p_mul_choose_sub_one {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p) :
    (p : ZMod (p^2)) * ((-1 : ZMod (p^2))^i * ((p - 1).choose i : ZMod (p^2))) = (p : ZMod (p^2)) := by
  have h_eq := choose_p_sub_one_mod_p hp i hi
  have h_eq_zmod : ((( ((p - 1).choose i : ℤ) - (-1 : ℤ)^i : ℤ) : ZMod p)) = 0 := by
    push_cast
    rw [sub_eq_zero]
    exact h_eq
  rw [zmod_zero_iff p (((p - 1).choose i : ℤ) - (-1 : ℤ)^i)] at h_eq_zmod
  have h_dvd : (p : ℤ) ∣ ((p - 1).choose i : ℤ) - (-1 : ℤ)^i := by
    rw [← Int.modEq_zero_iff_dvd]
    exact h_eq_zmod
  rcases h_dvd with ⟨k, hk⟩
  have hk_eq : ((p - 1).choose i : ℤ) = (-1 : ℤ)^i + p * k := by omega
  have h_cast := congrArg (fun (x : ℤ) => (x : ZMod (p^2))) hk_eq
  push_cast at h_cast
  have h_mul : (-1 : ZMod (p^2))^i * ((p - 1).choose i : ZMod (p^2)) = 1 + (p : ZMod (p^2)) * ((-1 : ZMod (p^2))^i * (k : ZMod (p^2))) := by
    have h_pow : (-1 : ZMod (p^2))^(i * 2) = 1 := by
      rw [mul_comm]
      rw [pow_mul (-1 : ZMod (p^2)) 2 i]
      simp
    calc (-1 : ZMod (p^2))^i * ((p - 1).choose i : ZMod (p^2))
      _ = (-1 : ZMod (p^2))^i * ((-1 : ZMod (p^2))^i + (p : ZMod (p^2)) * (k : ZMod (p^2))) := by rw [h_cast]
      _ = (-1 : ZMod (p^2))^(i * 2) + (p : ZMod (p^2)) * ((-1 : ZMod (p^2))^i * (k : ZMod (p^2))) := by ring
      _ = 1 + (p : ZMod (p^2)) * ((-1 : ZMod (p^2))^i * (k : ZMod (p^2))) := by rw [h_pow]
  have h_mul_p : (p : ZMod (p^2)) * ((-1 : ZMod (p^2))^i * ((p - 1).choose i : ZMod (p^2))) = (p : ZMod (p^2)) := by
    calc (p : ZMod (p^2)) * ((-1 : ZMod (p^2))^i * ((p - 1).choose i : ZMod (p^2)))
      _ = (p : ZMod (p^2)) * (1 + (p : ZMod (p^2)) * ((-1 : ZMod (p^2))^i * (k : ZMod (p^2)))) := by rw [h_mul]
      _ = (p : ZMod (p^2)) + (p : ZMod (p^2))^2 * ((-1 : ZMod (p^2))^i * (k : ZMod (p^2))) := by ring
      _ = (p : ZMod (p^2)) := by
        have hp2_eq : (p : ZMod (p^2))^2 = ((p^2 : ℕ) : ZMod (p^2)) := by push_cast; rfl
        have hp2 : ((p^2 : ℕ) : ZMod (p^2)) = 0 := ZMod.natCast_self (p^2)
        rw [hp2_eq, hp2, zero_mul, add_zero]
  exact h_mul_p

lemma p_mul_choose_eq_p_mul_pow {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p) :
    (p : ZMod (p^2)) * ((p - 1).choose i : ZMod (p^2)) = (p : ZMod (p^2)) * (-1 : ZMod (p^2))^i := by
  have h1 := p_mul_choose_sub_one hp i hi
  have h2 : (p : ZMod (p^2)) * ((-1 : ZMod (p^2))^i * ((p - 1).choose i : ZMod (p^2))) * (-1 : ZMod (p^2))^i = (p : ZMod (p^2)) * (-1 : ZMod (p^2))^i := by rw [h1]
  have h_lhs : (p : ZMod (p^2)) * ((-1 : ZMod (p^2))^i * ((p - 1).choose i : ZMod (p^2))) * (-1 : ZMod (p^2))^i =
      (p : ZMod (p^2)) * ((p - 1).choose i : ZMod (p^2)) * (-1 : ZMod (p^2))^(2 * i) := by ring
  rw [h_lhs] at h2
  have h_pow : (-1 : ZMod (p^2))^(2 * i) = 1 := by
    rw [pow_mul]
    simp
  rw [h_pow, mul_one] at h2
  exact h2

lemma p_mul_choose_div_succ {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p - 1) :
    (p : ZMod (p^2)) * ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ = (p.choose (i + 1) : ZMod (p^2)) := by
  have h_nat := Nat.add_one_mul_choose_eq (p - 1) i
  have hp_eq : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
  rw [hp_eq] at h_nat
  have h_cast : (((p * (p - 1).choose i : ℕ) : ZMod (p^2))) = (((p.choose (i + 1) * (i + 1) : ℕ) : ZMod (p^2))) := by
    congr 1
  push_cast at h_cast
  have h_mul : (p : ZMod (p^2)) * ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ =
      (p.choose (i + 1) : ZMod (p^2)) * ((i + 1 : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹) := by
    calc (p : ZMod (p^2)) * ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹
      _ = (p.choose (i + 1) : ZMod (p^2)) * (i + 1 : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ := by rw [h_cast]
      _ = (p.choose (i + 1) : ZMod (p^2)) * ((i + 1 : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹) := by ring
  have h_unit : IsUnit ((i + 1 : ℕ) : ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    apply prime_coprime_pow hp (Nat.succ_pos i)
    omega
  have h_unit_cast : IsUnit (i + 1 : ZMod (p^2)) := by
    have : (i + 1 : ZMod (p^2)) = ((i + 1 : ℕ) : ZMod (p^2)) := by push_cast; rfl
    rw [this]
    exact h_unit
  rw [ZMod.mul_inv_of_unit (i + 1 : ZMod (p^2)) h_unit_cast] at h_mul
  rw [mul_one] at h_mul
  exact h_mul

lemma p_mul_inv_eq_choose {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p - 1) :
    (p : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ = (-1 : ZMod (p^2))^i * (p.choose (i + 1) : ZMod (p^2)) := by
  have h1 := p_mul_choose_sub_one hp i (by omega)
  have h2 : (p : ZMod (p^2)) * ((-1 : ZMod (p^2))^i * ((p - 1).choose i : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹ = (p : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ := by rw [h1]
  have h_lhs : (p : ZMod (p^2)) * ((-1 : ZMod (p^2))^i * ((p - 1).choose i : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹ =
      (-1 : ZMod (p^2))^i * ((p : ZMod (p^2)) * ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹) := by ring
  rw [h_lhs] at h2
  have h3 := p_mul_choose_div_succ hp i hi
  rw [h3] at h2
  exact h2.symm

lemma choose_add_one_inv_eq_inv_add_p {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p - 1) :
    ((p.choose (i + 1) : ZMod (p^2)) + 1) * (i + 1 : ZMod (p^2))⁻¹ =
    (p : ZMod (p^2)) * (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2))⁻¹^2 + (i + 1 : ZMod (p^2))⁻¹ := by
  calc ((p.choose (i + 1) : ZMod (p^2)) + 1) * (i + 1 : ZMod (p^2))⁻¹
    _ = (p.choose (i + 1) : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ + (i + 1 : ZMod (p^2))⁻¹ := by ring
    _ = (p : ZMod (p^2)) * ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ * (i + 1 : ZMod (p^2))⁻¹ + (i + 1 : ZMod (p^2))⁻¹ := by
      rw [← p_mul_choose_div_succ hp i hi]
    _ = (p : ZMod (p^2)) * ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹^2 + (i + 1 : ZMod (p^2))⁻¹ := by ring
    _ = (p : ZMod (p^2)) * (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2))⁻¹^2 + (i + 1 : ZMod (p^2))⁻¹ := by
      rw [p_mul_choose_eq_p_mul_pow hp i (by omega)]

lemma choose_p_sub_one_eq_harmonic {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p) :
    ((p - 1).choose i : ZMod (p^2)) = (-1 : ZMod (p^2))^i * (1 - (p : ZMod (p^2)) * Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹)) := by
  induction i with
  | zero =>
    simp
  | succ i ih =>
    have hi_succ : i + 1 < p := hi
    have hi_lt : i < p := by omega
    have h_ih := ih hi_lt
    have h_mul := Nat.choose_succ_right_eq (p - 1) i
    have h_cast : (((p - 1).choose (i + 1) * (i + 1) : ℕ) : ZMod (p^2)) = (((p - 1).choose i * (p - 1 - i) : ℕ) : ZMod (p^2)) := by
      congr 1
    push_cast at h_cast
    have h_sub : ((p - 1 - i : ℕ) : ZMod (p^2)) = (p : ZMod (p^2)) - (i + 1 : ZMod (p^2)) := by
      have hp_pos : p > 0 := hp.pos
      have h_nat : p - 1 - i + (i + 1) = p := by omega
      have h_eq_cast : (((p - 1 - i + (i + 1) : ℕ) : ZMod (p^2))) = ((p : ℕ) : ZMod (p^2)) := by
        congr 1
      have h_sum_cast : (((p - 1 - i) + (i + 1) : ℕ) : ZMod (p^2)) = ((p - 1 - i : ℕ) : ZMod (p^2)) + ((i + 1 : ℕ) : ZMod (p^2)) := by
        push_cast
        rfl
      rw [h_sum_cast] at h_eq_cast
      have : ((i + 1 : ℕ) : ZMod (p^2)) = (i + 1 : ZMod (p^2)) := by push_cast; rfl
      rw [this] at h_eq_cast
      calc ((p - 1 - i : ℕ) : ZMod (p^2)) = ((p - 1 - i : ℕ) : ZMod (p^2)) + (i + 1 : ZMod (p^2)) - (i + 1 : ZMod (p^2)) := by ring
      _ = (p : ZMod (p^2)) - (i + 1 : ZMod (p^2)) := by rw [h_eq_cast]
    rw [h_sub, h_ih] at h_cast
    have h_unit : IsUnit ((i + 1 : ℕ) : ZMod (p^2)) := by
      rw [ZMod.isUnit_iff_coprime]
      apply prime_coprime_pow hp (Nat.succ_pos i)
      omega
    have h_unit_cast : IsUnit (i + 1 : ZMod (p^2)) := by
      have : (i + 1 : ZMod (p^2)) = ((i + 1 : ℕ) : ZMod (p^2)) := by push_cast; rfl
      rw [this]
      exact h_unit
    generalize h_X : Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹) = X
    rw [h_X] at h_cast
    have h_sum_succ : Finset.sum (Finset.range (i + 1)) (fun j => (j + 1 : ZMod (p^2))⁻¹) = X + (i + 1 : ZMod (p^2))⁻¹ := by
      rw [Finset.sum_range_succ, h_X]
    rw [h_sum_succ]
    have h_cancel : (i + 1 : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ = 1 := by
      rw [ZMod.mul_inv_of_unit (i + 1 : ZMod (p^2)) h_unit_cast]
    have hp2_eq : (p : ZMod (p^2))^2 = ((p^2 : ℕ) : ZMod (p^2)) := by push_cast; rfl
    have hp2_zero : ((p^2 : ℕ) : ZMod (p^2)) = 0 := ZMod.natCast_self (p^2)
    have hp2 : (p : ZMod (p^2))^2 = 0 := by rw [hp2_eq, hp2_zero]
    have h_eq : (-1 : ZMod (p^2))^i * (1 - (p : ZMod (p^2)) * X) * ((p : ZMod (p^2)) - (i + 1 : ZMod (p^2))) =
        (i + 1 : ZMod (p^2)) * ((-1 : ZMod (p^2))^(i + 1) * (1 - (p : ZMod (p^2)) * (X + (i + 1 : ZMod (p^2))⁻¹))) := by
      calc (-1 : ZMod (p^2))^i * (1 - (p : ZMod (p^2)) * X) * ((p : ZMod (p^2)) - (i + 1 : ZMod (p^2)))
        _ = (-1 : ZMod (p^2))^i * (p : ZMod (p^2)) - (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2)) - (p : ZMod (p^2))^2 * (-1 : ZMod (p^2))^i * X + (p : ZMod (p^2)) * (i + 1 : ZMod (p^2)) * (-1 : ZMod (p^2))^i * X := by ring
        _ = (-1 : ZMod (p^2))^i * (p : ZMod (p^2)) - (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2)) - 0 * (-1 : ZMod (p^2))^i * X + (p : ZMod (p^2)) * (i + 1 : ZMod (p^2)) * (-1 : ZMod (p^2))^i * X := by rw [hp2]
        _ = (-1 : ZMod (p^2))^i * (p : ZMod (p^2)) - (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2)) + (p : ZMod (p^2)) * (i + 1 : ZMod (p^2)) * (-1 : ZMod (p^2))^i * X := by ring
        _ = (i + 1 : ZMod (p^2)) * (-1 : ZMod (p^2))^(i + 1) - (p : ZMod (p^2)) * (i + 1 : ZMod (p^2)) * (-1 : ZMod (p^2))^(i + 1) * X - (p : ZMod (p^2)) * (-1 : ZMod (p^2))^(i + 1) * ((i + 1 : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹) := by
          rw [h_cancel]
          ring
        _ = (i + 1 : ZMod (p^2)) * ((-1 : ZMod (p^2))^(i + 1) * (1 - (p : ZMod (p^2)) * (X + (i + 1 : ZMod (p^2))⁻¹))) := by ring
    rw [h_eq] at h_cast
    have h_lhs : ((p - 1).choose (i + 1) : ZMod (p^2)) * (i + 1 : ZMod (p^2)) = (i + 1 : ZMod (p^2)) * ((p - 1).choose (i + 1) : ZMod (p^2)) := by ring
    rw [h_lhs] at h_cast
    exact (IsUnit.mul_right_inj h_unit_cast).mp h_cast

lemma term_eq_harmonic {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p - 1) :
    (((2^(i + 1) : ℕ) + (p - 1).choose i : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹ =
    (((2^(i + 1) : ℕ) + (-1 : ZMod (p^2))^i : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹ -
    (p : ZMod (p^2)) * (-1 : ZMod (p^2))^i * Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹) * (i + 1 : ZMod (p^2))⁻¹ := by
  have h_choose := choose_p_sub_one_eq_harmonic hp i (by omega)
  calc (((2^(i + 1) : ℕ) + (p - 1).choose i : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹
    _ = ((2^(i + 1) : ZMod (p^2)) + ((-1 : ZMod (p^2))^i * (1 - (p : ZMod (p^2)) * Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹)))) * (i + 1 : ZMod (p^2))⁻¹ := by
      push_cast
      rw [h_choose]
    _ = (((2^(i + 1) : ℕ) + (-1 : ZMod (p^2))^i : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹ -
    (p : ZMod (p^2)) * (-1 : ZMod (p^2))^i * Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹) * (i + 1 : ZMod (p^2))⁻¹ := by
      push_cast
      ring


lemma p_mul_eq_zero_of_val_mod_p_eq_zero {p : ℕ} (hp : p.Prime) (x : ZMod (p^2)) (h : (x.val : ZMod p) = 0) :
    (p : ZMod (p^2)) * x = 0 := by
  haveI : NeZero (p^2) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h_dvd : p ∣ x.val := by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact h
  rcases h_dvd with ⟨k, hk⟩
  have h_val_eq : (x.val : ZMod (p^2)) = (p * k : ZMod (p^2)) := by
    rw [hk, Nat.cast_mul]
  have h_x_eq : x = (x.val : ZMod (p^2)) := (ZMod.natCast_zmod_val x).symm
  rw [h_x_eq, h_val_eq]
  have hp2_eq : (p : ZMod (p^2))^2 = ((p^2 : ℕ) : ZMod (p^2)) := by push_cast; rfl
  have hp2_zero : ((p^2 : ℕ) : ZMod (p^2)) = 0 := ZMod.natCast_self (p^2)
  have hp2 : (p : ZMod (p^2))^2 = 0 := by rw [hp2_eq, hp2_zero]
  calc (p : ZMod (p^2)) * ((p : ZMod (p^2)) * (k : ZMod (p^2)))
    _ = (p : ZMod (p^2))^2 * (k : ZMod (p^2)) := by ring
    _ = 0 := by rw [hp2, zero_mul]


lemma p_choose_div_eq_p_mul_inv_sq {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p - 1) :
    (p.choose (i + 1) : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ =
    (p : ZMod (p^2)) * (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2))⁻¹^2 := by
  have h := choose_add_one_inv_eq_inv_add_p hp i hi
  calc (p.choose (i + 1) : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹
    _ = ((p.choose (i + 1) : ZMod (p^2)) + 1) * (i + 1 : ZMod (p^2))⁻¹ - (i + 1 : ZMod (p^2))⁻¹ := by ring
    _ = (p : ZMod (p^2)) * (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2))⁻¹^2 + (i + 1 : ZMod (p^2))⁻¹ - (i + 1 : ZMod (p^2))⁻¹ := by rw [h]
    _ = (p : ZMod (p^2)) * (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2))⁻¹^2 := by ring


lemma term_sum_eq_harmonic_sum {p : ℕ} (hp : p.Prime) (hp3 : p > 3) :
    Finset.sum (Finset.range (p - 1)) (fun i => (((2^(i + 1) : ℕ) + (p - 1).choose i : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹) =
    Finset.sum (Finset.range (p - 1)) (fun i => (((2^(i + 1) : ℕ) + (-1 : ZMod (p^2))^i : ZMod (p^2))) * (i + 1 : ZMod (p^2))⁻¹) -
    (p : ZMod (p^2)) * Finset.sum (Finset.range (p - 1)) (fun i => (-1 : ZMod (p^2))^i * Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹) * (i + 1 : ZMod (p^2))⁻¹) := by
  haveI : NeZero (p^2) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have h := term_eq_harmonic hp i hi
  rw [h]
  ring


lemma term_harmonic_sub_eq_choose {p : ℕ} (hp : p.Prime) (i : ℕ) (hi : i < p - 1) :
    (-1 : ZMod (p^2))^i * (p : ZMod (p^2)) * Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹) * (i + 1 : ZMod (p^2))⁻¹ =
    (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2))⁻¹ - ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ := by
  have h_choose := choose_p_sub_one_eq_harmonic hp i (by omega)
  have h_mul : ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹ = (-1 : ZMod (p^2))^i * (1 - (p : ZMod (p^2)) * Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹)) * (i + 1 : ZMod (p^2))⁻¹ := by
    rw [h_choose]
  rw [h_mul]
  ring

lemma sum_two_pow_sub_one_div (n : ℕ) :
    Finset.sum (Finset.range n) (fun i => ((2 : ℚ)^(i + 1) - 1) / (i + 1 : ℚ)) =
    Finset.sum (Finset.range n) (fun i => (Nat.choose n (i + 1) : ℚ) / (i + 1 : ℚ)) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [ih]
    have h_choose : ∀ i ∈ Finset.range n, (Nat.choose (n + 1) (i + 1) : ℚ) / (i + 1 : ℚ) =
        (Nat.choose n (i + 1) : ℚ) / (i + 1 : ℚ) + (Nat.choose n i : ℚ) / (i + 1 : ℚ) := by
      intro i _
      have h_pascal : Nat.choose (n + 1) (i + 1) = Nat.choose n (i + 1) + Nat.choose n i := by
        have h_eq := Nat.choose_succ_succ n i
        rw [h_eq]
        rw [add_comm]
      have h_cast : ((Nat.choose (n + 1) (i + 1) : ℕ) : ℚ) = ((Nat.choose n (i + 1) + Nat.choose n i : ℕ) : ℚ) := by
        congr 1
      push_cast at h_cast
      rw [h_cast]
      ring
    rw [Finset.sum_congr rfl h_choose]
    rw [Finset.sum_add_distrib]
    have h_choose_sum := choose_div_succ_sum n
    have h_last : (Nat.choose (n + 1) (n + 1) : ℚ) / (n + 1 : ℚ) = 1 / (n + 1 : ℚ) := by
      simp
    rw [h_last]
    rw [h_choose_sum]
    ring

lemma rat_expression_eq_sum_choose_add_one (n : ℕ) (hn : n > 1) :
    rat_expression n = Finset.sum (Finset.range (n - 1)) (fun i => ((Nat.choose n (i + 1) : ℚ) + 1) / (i + 1 : ℚ)) := by
  have hn_pos : n > 0 := by omega
  rw [rat_expression_split n hn_pos]
  generalize h_m : n - 1 = m
  have hn_eq : n = m + 1 := by omega
  rw [hn_eq]
  push_cast
  rw [← choose_div_succ_sum m]
  rw [← Finset.sum_add_distrib]
  have h_id : Finset.sum (Finset.range m) (fun i => (2 : ℚ)^(i + 1) / (i + 1 : ℚ) + (Nat.choose m i : ℚ) / (i + 1 : ℚ)) =
      Finset.sum (Finset.range m) (fun i => ((Nat.choose (m + 1) (i + 1) : ℚ) + 1) / (i + 1 : ℚ)) := by
    have h_diff : Finset.sum (Finset.range m) (fun i => (2 : ℚ)^(i + 1) / (i + 1 : ℚ) + (Nat.choose m i : ℚ) / (i + 1 : ℚ) - ((Nat.choose (m + 1) (i + 1) : ℚ) + 1) / (i + 1 : ℚ)) = 0 := by
      have h_term : ∀ i ∈ Finset.range m, (2 : ℚ)^(i + 1) / (i + 1 : ℚ) + (Nat.choose m i : ℚ) / (i + 1 : ℚ) - ((Nat.choose (m + 1) (i + 1) : ℚ) + 1) / (i + 1 : ℚ) =
          (((2 : ℚ)^(i + 1) - 1) / (i + 1 : ℚ)) - (Nat.choose m (i + 1) : ℚ) / (i + 1 : ℚ) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        have h_pascal : Nat.choose (m + 1) (i + 1) = Nat.choose m (i + 1) + Nat.choose m i := by
          have h_eq := Nat.choose_succ_succ m i
          rw [h_eq, add_comm]
        have h_cast : ((Nat.choose (m + 1) (i + 1) : ℕ) : ℚ) = ((Nat.choose m (i + 1) + Nat.choose m i : ℕ) : ℚ) := by congr 1
        push_cast at h_cast
        rw [h_cast]
        ring
      rw [Finset.sum_congr rfl h_term]
      rw [Finset.sum_sub_distrib]
      rw [sum_two_pow_sub_one_div m]
      ring
    have h_eq_sum : Finset.sum (Finset.range m) (fun i => (2 : ℚ)^(i + 1) / (i + 1 : ℚ) + (Nat.choose m i : ℚ) / (i + 1 : ℚ)) -
        Finset.sum (Finset.range m) (fun i => ((Nat.choose (m + 1) (i + 1) : ℚ) + 1) / (i + 1 : ℚ)) = 0 := by
      rw [← Finset.sum_sub_distrib]
      exact h_diff
    exact sub_eq_zero.mp h_eq_sum
  push_cast
  rw [h_id]


lemma p_mul_S2_eq_sub {p : ℕ} (hp : p.Prime) (hp3 : p > 3) :
    (p : ZMod (p^2)) * Finset.sum (Finset.range (p - 1)) (fun i => (-1 : ZMod (p^2))^i * Finset.sum (Finset.range i) (fun j => (j + 1 : ZMod (p^2))⁻¹) * (i + 1 : ZMod (p^2))⁻¹) =
    Finset.sum (Finset.range (p - 1)) (fun i => (-1 : ZMod (p^2))^i * (i + 1 : ZMod (p^2))⁻¹) -
    Finset.sum (Finset.range (p - 1)) (fun i => ((p - 1).choose i : ZMod (p^2)) * (i + 1 : ZMod (p^2))⁻¹) := by
  haveI : NeZero (p^2) := ⟨Nat.ne_of_gt (Nat.pow_pos hp.pos)⟩
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have h := term_harmonic_sub_eq_choose hp i hi
  rw [← h]
  ring


lemma sum_inv_sq_eq_sum_sq {p : ℕ} (hp : p.Prime) :
    Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod p)⁻¹^2) =
    Finset.sum (Finset.range (p - 1)) (fun i => (i + 1 : ZMod p)^2) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp_gt : p > 1 := hp.one_lt
  refine @Finset.sum_bij ℕ ℕ (ZMod p) _ (Finset.range (p - 1)) (Finset.range (p - 1))
    (fun i => (i + 1 : ZMod p)⁻¹^2) (fun i => (i + 1 : ZMod p)^2)
    (fun i _ => (i + 1 : ZMod p)⁻¹.val - 1) ?subgoal1 ?subgoal2 ?subgoal3 ?subgoal4
  case subgoal1 =>
    intro i hi
    simp only [Finset.mem_range] at hi
    have h_lt : i + 1 < p := by omega
    have h_pos : i + 1 > 0 := by omega
    have h_unit : IsUnit (i + 1 : ZMod p) := by
      have h_eq : (i + 1 : ZMod p) = ((i + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.isUnit_iff_coprime]
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h_pos h_lt)).symm
    have h_val_lt : (i + 1 : ZMod p)⁻¹.val < p := ZMod.val_lt (i + 1 : ZMod p)⁻¹
    have h_val_pos : (i + 1 : ZMod p)⁻¹.val > 0 := by
      have h_zero : (i + 1 : ZMod p)⁻¹.val ≠ 0 := by
        intro h_z
        rw [ZMod.val_eq_zero] at h_z
        exact IsUnit.ne_zero (IsUnit.inv h_unit) h_z
      omega
    simp only [Finset.mem_range]
    omega
  case subgoal2 =>
    intro i hi j hj h_eq
    simp only [Finset.mem_range] at hi hj
    dsimp only at h_eq
    have h_lt_i : i + 1 < p := by omega
    have h_pos_i : i + 1 > 0 := by omega
    have h_lt_j : j + 1 < p := by omega
    have h_pos_j : j + 1 > 0 := by omega
    have h_unit_i : IsUnit (i + 1 : ZMod p) := by
      have h_eq : (i + 1 : ZMod p) = ((i + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.isUnit_iff_coprime]
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h_pos_i h_lt_i)).symm
    have h_unit_j : IsUnit (j + 1 : ZMod p) := by
      have h_eq : (j + 1 : ZMod p) = ((j + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.isUnit_iff_coprime]
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h_pos_j h_lt_j)).symm
    have h_val_pos_i : (i + 1 : ZMod p)⁻¹.val > 0 := by
      have h_zero : (i + 1 : ZMod p)⁻¹.val ≠ 0 := by
        intro h_z
        rw [ZMod.val_eq_zero] at h_z
        exact IsUnit.ne_zero (IsUnit.inv h_unit_i) h_z
      omega
    have h_val_pos_j : (j + 1 : ZMod p)⁻¹.val > 0 := by
      have h_zero : (j + 1 : ZMod p)⁻¹.val ≠ 0 := by
        intro h_z
        rw [ZMod.val_eq_zero] at h_z
        exact IsUnit.ne_zero (IsUnit.inv h_unit_j) h_z
      omega
    have h_eq_add : (i + 1 : ZMod p)⁻¹.val = (j + 1 : ZMod p)⁻¹.val := by omega
    have h_eq_zmod : (i + 1 : ZMod p)⁻¹ = (j + 1 : ZMod p)⁻¹ := by
      have h1 : ( (i + 1 : ZMod p)⁻¹.val : ZMod p ) = (i + 1 : ZMod p)⁻¹ := ZMod.natCast_zmod_val _
      have h2 : ( (j + 1 : ZMod p)⁻¹.val : ZMod p ) = (j + 1 : ZMod p)⁻¹ := ZMod.natCast_zmod_val _
      rw [← h1, ← h2, h_eq_add]
    have h_eq_inv : (i + 1 : ZMod p)⁻¹⁻¹ = (j + 1 : ZMod p)⁻¹⁻¹ := by rw [h_eq_zmod]
    rw [inv_inv, inv_inv] at h_eq_inv
    have h_val_i : (i + 1 : ZMod p).val = i + 1 := by
      have h_eq : (i + 1 : ZMod p) = ((i + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt h_lt_i]
    have h_val_j : (j + 1 : ZMod p).val = j + 1 := by
      have h_eq : (j + 1 : ZMod p) = ((j + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt h_lt_j]
    have h_eq_val : (i + 1 : ZMod p).val = (j + 1 : ZMod p).val := congrArg ZMod.val h_eq_inv
    rw [h_val_i, h_val_j] at h_eq_val
    omega
  case subgoal3 =>
    intro b hb
    simp only [Finset.mem_range] at hb
    have h_lt_b : b + 1 < p := by omega
    have h_pos_b : b + 1 > 0 := by omega
    have h_unit_b : IsUnit (b + 1 : ZMod p) := by
      have h_eq : (b + 1 : ZMod p) = ((b + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.isUnit_iff_coprime]
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h_pos_b h_lt_b)).symm
    have h_val_pos_b : (b + 1 : ZMod p)⁻¹.val > 0 := by
      have h_zero : (b + 1 : ZMod p)⁻¹.val ≠ 0 := by
        intro h_z
        rw [ZMod.val_eq_zero] at h_z
        exact IsUnit.ne_zero (IsUnit.inv h_unit_b) h_z
      omega
    use (b + 1 : ZMod p)⁻¹.val - 1
    have h_mem : (b + 1 : ZMod p)⁻¹.val - 1 ∈ Finset.range (p - 1) := by
      simp only [Finset.mem_range]
      have h_val_lt : (b + 1 : ZMod p)⁻¹.val < p := ZMod.val_lt _
      omega
    refine ⟨h_mem, ?_⟩
    dsimp only
    have h_eq_cast : (((b + 1 : ZMod p)⁻¹.val - 1 : ℕ) : ZMod p) + 1 = (b + 1 : ZMod p)⁻¹ := by
      have : (((b + 1 : ZMod p)⁻¹.val - 1 : ℕ) : ZMod p) + 1 = (((b + 1 : ZMod p)⁻¹.val - 1 + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [this]
      rw [Nat.sub_add_cancel h_val_pos_b]
      exact ZMod.natCast_zmod_val (b + 1 : ZMod p)⁻¹
    have h_eq_cast_inv : ((((b + 1 : ZMod p)⁻¹.val - 1 : ℕ) : ZMod p) + 1)⁻¹ = b + 1 := by
      rw [h_eq_cast, inv_inv]
    rw [h_eq_cast_inv]
    have h_val : (b + 1 : ZMod p).val = b + 1 := by
      have h_eq : (b + 1 : ZMod p) = ((b + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt h_lt_b]
    rw [h_val]
    omega
  case subgoal4 =>
    intro i hi
    simp only [Finset.mem_range] at hi
    dsimp only
    congr 1
    have h_lt : i + 1 < p := by omega
    have h_pos : i + 1 > 0 := by omega
    have h_unit : IsUnit (i + 1 : ZMod p) := by
      have h_eq : (i + 1 : ZMod p) = ((i + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [h_eq]
      rw [ZMod.isUnit_iff_coprime]
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt h_pos h_lt)).symm
    have h_val_pos : (i + 1 : ZMod p)⁻¹.val > 0 := by
      have h_zero : (i + 1 : ZMod p)⁻¹.val ≠ 0 := by
        intro h_z
        rw [ZMod.val_eq_zero] at h_z
        exact IsUnit.ne_zero (IsUnit.inv h_unit) h_z
      omega
    have h_val_lt : (i + 1 : ZMod p)⁻¹.val < p := ZMod.val_lt (i + 1 : ZMod p)⁻¹
    have h_eq_cast : (((i + 1 : ZMod p)⁻¹.val - 1 : ℕ) : ZMod p) + 1 = (i + 1 : ZMod p)⁻¹ := by
      have : (((i + 1 : ZMod p)⁻¹.val - 1 : ℕ) : ZMod p) + 1 = (((i + 1 : ZMod p)⁻¹.val - 1 + 1 : ℕ) : ZMod p) := by push_cast; rfl
      rw [this]
      rw [Nat.sub_add_cancel h_val_pos]
      exact ZMod.natCast_zmod_val (i + 1 : ZMod p)⁻¹
    exact h_eq_cast.symm


lemma sum_inv_sq_cancelled {p : ℕ} (hp : p.Prime) (hp3 : p > 3) :
    Finset.sum (Finset.range (p - 1)) (fun i => (-1 : ZMod p)^i * (i + 1 : ZMod p)⁻¹^2) = 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h_odd : Odd (p - 2) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp.pos)
    have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
    rcases hp_odd with ⟨m, rfl⟩
    use m - 1
    omega
  have h_pow_odd : (-1 : ZMod p)^(p - 2) = -1 := by
    rcases h_odd with ⟨k, hk⟩
    rw [hk, pow_succ, pow_mul]
    have : (-1 : ZMod p)^2 = 1 := by ring
    rw [this, one_pow, one_mul]
  have h_parity : ∀ i < p - 1, (-1 : ZMod p)^(p - 2 - i) = - (-1 : ZMod p)^i := by
    intro i hi
    have hi_le : i ≤ p - 2 := by omega
    have h_eq : (p - 2 - i) + i = p - 2 := Nat.sub_add_cancel hi_le
    have h_pow : (-1 : ZMod p)^(p - 2 - i) * (-1 : ZMod p)^i = (-1 : ZMod p)^(p - 2) := by
      rw [← pow_add, h_eq]
    rw [h_pow_odd] at h_pow
    have h_mul : (-1 : ZMod p)^(p - 2 - i) * (-1 : ZMod p)^i * (-1 : ZMod p)^i = - (-1 : ZMod p)^i := by
      rw [h_pow]
      ring
    have h_pow2 : (-1 : ZMod p)^i * (-1 : ZMod p)^i = 1 := by
      rw [← pow_add]
      have : i + i = 2 * i := by omega
      rw [this, pow_mul]
      have : (-1 : ZMod p)^2 = 1 := by ring
      rw [this, one_pow]
    rw [mul_assoc, h_pow2, mul_one] at h_mul
    exact h_mul
  generalize hS : Finset.sum (Finset.range (p - 1)) (fun i => (-1 : ZMod p)^i * (i + 1 : ZMod p)⁻¹^2) = S
  have h_sum := Finset.sum_range_reflect (fun i => (-1 : ZMod p)^i * (i + 1 : ZMod p)⁻¹^2) (p - 1)
  have h_sub_eq : p - 1 - 1 = p - 2 := by omega
  rw [h_sub_eq] at h_sum
  have h_sum_congr : Finset.sum (Finset.range (p - 1)) (fun i => (-1 : ZMod p)^(p - 2 - i) * ( (p - 2 - i + 1 : ℕ) : ZMod p )⁻¹^2) = - S := by
    rw [← hS]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    have h_p : (-1 : ZMod p)^(p - 2 - i) = - (-1 : ZMod p)^i := h_parity i hi
    have h_denom : ( (p - 2 - i + 1 : ℕ) : ZMod p ) = - (i + 1 : ZMod p) := by
      have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
      have h_nat1 : p - 2 - i + 1 = p - 1 - i := by omega
      have h_cast1 : ( (p - 2 - i + 1 : ℕ) : ZMod p ) = ( (p - 1 - i : ℕ) : ZMod p ) := by congr 1
      have h_nat2 : p - 1 - i + (i + 1) = p := by omega
      have h_cast2 : ( (p - 1 - i : ℕ) : ZMod p ) + (i + 1 : ZMod p) = (p : ZMod p) := by
        have h_cast_eq : ( (p - 1 - i + (i + 1) : ℕ) : ZMod p ) = (p : ZMod p) := by congr 1
        push_cast at h_cast_eq
        exact h_cast_eq
      calc ( (p - 2 - i + 1 : ℕ) : ZMod p )
        _ = ( (p - 1 - i : ℕ) : ZMod p ) := h_cast1
        _ = ( (p - 1 - i : ℕ) : ZMod p ) + (i + 1 : ZMod p) - (i + 1 : ZMod p) := by ring
        _ = (p : ZMod p) - (i + 1 : ZMod p) := by rw [h_cast2]
        _ = - (i + 1 : ZMod p) := by rw [hp0, zero_sub]
    rw [h_p, h_denom]
    have h_inv : (- (i + 1 : ZMod p))⁻¹ = - (i + 1 : ZMod p)⁻¹ := by rw [inv_neg]
    rw [h_inv]
    ring
  push_cast at h_sum
  push_cast at h_sum_congr
  rw [h_sum_congr] at h_sum
  rw [hS] at h_sum
  have h_S_eq : - S = S := h_sum
  have h_two : 2 * S = 0 := by
    calc 2 * S = S + S := by ring
    _ = S - (-S) := by ring
    _ = S - S := by rw [h_S_eq]
    _ = 0 := by ring
  have h_unit : IsUnit ((2 : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    have h_not_dvd : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr h_not_dvd)
  have h_unit_cast : IsUnit (2 : ZMod p) := by
    have : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by push_cast; rfl
    rw [this]
    exact h_unit
  exact (IsUnit.mul_right_inj h_unit_cast).mp (by rw [mul_zero, h_two])



/--
A108866 Conjecture: for n > 3, numerator(-2/n + Sum_{k=1..n} 2^k/k) == 0 (mod n^2) if and only if n is prime.
-/
theorem oeis_a108866_conjecture {n : ℕ} (hn : n > 3) :
    (rat_expression n).num ≡ 0 [ZMOD (n^2 : ℤ)] ↔ Nat.Prime n := by
  constructor
  · intro h
    sorry
  · intro hp
    have hn_pos : n > 0 := by omega
    have h_split := rat_expression_split n hn_pos
    sorry

