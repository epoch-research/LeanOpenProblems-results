import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat

lemma rat_div_eq (a b : ℕ) : (a : ℚ) / (b : ℚ) = (a : ℤ) /. (b : ℤ) := by
  have h1 : (a : ℚ).num = a := by rfl
  have h2 : (a : ℚ).den = 1 := by rfl
  have h3 : (b : ℚ).num = b := by rfl
  have h4 : (b : ℚ).den = 1 := by rfl
  rw [Rat.div_def', h1, h2, h3, h4]
  simp

lemma rat_num_den (a b : ℕ) (hb : 0 < b) :
  ((a : ℚ) / (b : ℚ)).num = a / Nat.gcd a b := by
  rw [rat_div_eq]
  rw [Rat.num_divInt]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  have h_sign : Int.sign (n.succ : ℤ) = 1 := rfl
  have h_gcd : Int.gcd (n.succ : ℤ) (a : ℤ) = Nat.gcd a n.succ := by
    rw [Int.gcd_comm]
    rfl
  rw [h_sign, h_gcd]
  simp


lemma rat_den_den (a b : ℕ) (hb : 0 < b) :
  ((a : ℚ) / (b : ℚ)).den = b / Nat.gcd a b := by
  rw [rat_div_eq]
  rw [Rat.den_divInt]
  have hb_nz : ¬ (b : ℤ) = 0 := by
    exact Int.ofNat_ne_zero.mpr hb.ne'
  simp only [hb_nz, ↓reduceIte]
  have h_nat : Int.natAbs (b : ℤ) = b := rfl
  have h_gcd : Int.gcd (b : ℤ) (a : ℤ) = Nat.gcd a b := by
    rw [Int.gcd_comm]
    rfl
  rw [h_nat, h_gcd]

def sigma_computable (n : ℕ) : ℕ :=
  (Finset.filter (· ∣ n) (Finset.Ico 1 (n + 1))).sum (fun x => x)

lemma sigma_computable_eq_sigma_one (i : ℕ) : sigma_computable i = sigma 1 i := by
  rw [sigma_apply]
  simp only [pow_one]
  dsimp [sigma_computable]
  rfl

def A243473_val_computable (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let s := sigma_computable i
    let g := Nat.gcd s i
    (s - i) / g

def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    (r.num - (r.den : ℤ)).toNat

lemma Nat_sub_div {a b c : ℕ} (ha : c ∣ a) (hb : c ∣ b) : (a - b) / c = a / c - b / c := by
  by_cases hc : c = 0
  · subst hc
    simp
  · have hc_pos : 0 < c := Nat.pos_of_ne_zero hc
    have ha_eq : a = (a / c) * c := by
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod a c).symm.trans (by rw [Nat.mod_eq_zero_of_dvd ha, add_zero])
    have hb_eq : b = (b / c) * c := by
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod b c).symm.trans (by rw [Nat.mod_eq_zero_of_dvd hb, add_zero])
    have h_sub_mul : (a / c - b / c) * c = a - b := by
      rw [Nat.sub_mul, ← ha_eq, ← hb_eq]
    rw [← h_sub_mul]
    exact Nat.mul_div_cancel _ hc_pos

lemma A243473_val_computable_eq (i : ℕ) (hi : 0 < i) : A243473_val_computable i = A243473_val i := by
  dsimp [A243473_val, A243473_val_computable]
  simp only [hi.ne', ↓reduceIte]
  rw [sigma_computable_eq_sigma_one]
  have h_num := rat_num_den (sigma 1 i) i hi
  have h_den := rat_den_den (sigma 1 i) i hi
  rw [h_num, h_den]
  have h_gcd_dvd_sigma : (sigma 1 i).gcd i ∣ sigma 1 i := Nat.gcd_dvd_left (sigma 1 i) i
  have h_gcd_dvd_i : (sigma 1 i).gcd i ∣ i := Nat.gcd_dvd_right (sigma 1 i) i
  have h_le : i <= sigma 1 i := by
    rw [sigma_apply]
    simp only [pow_one]
    exact Finset.single_le_sum (fun x _ => Nat.zero_le x) (Nat.mem_divisors.mpr ⟨dvd_rfl, hi.ne'⟩)
  have h_sub : (sigma 1 i / (sigma 1 i).gcd i : ℕ) - (i / (sigma 1 i).gcd i : ℕ) = (sigma 1 i - i) / (sigma 1 i).gcd i := by
    rw [Nat_sub_div h_gcd_dvd_sigma h_gcd_dvd_i]
  have h_div_cast : (↑((sigma 1 i) / (sigma 1 i).gcd i) : ℤ) = ↑(sigma 1 i) / ↑((sigma 1 i).gcd i) := by
    rw [Int.ofNat_tdiv]
    have h_dvd : ((sigma 1 i).gcd i : ℤ) ∣ sigma 1 i := Int.ofNat_dvd.mpr h_gcd_dvd_sigma
    rw [Int.tdiv_eq_ediv_of_dvd h_dvd]
  rw [← h_div_cast]
  rw [← Int.ofNat_sub]
  · rw [h_sub]
    rfl
  · exact Nat.div_le_div_right h_le

















