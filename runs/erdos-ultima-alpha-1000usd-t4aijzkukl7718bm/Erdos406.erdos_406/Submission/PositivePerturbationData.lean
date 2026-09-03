import Submission.PatternObstruction

/-! A base-nine leading-prefix lemma and exact arithmetic data for positive
perturbations. These are auxiliary constructions, not a settlement of Erdős 406. -/
namespace Erdos406Perturbation
open scoped Topology
open Erdos406Work

lemma leading_prefix_base_nine_in_four_progression (A E s M : ℕ) (hA : 0 < A) (hs : 0 < s) :
    ∃ j L : ℕ, M ≤ j ∧ 4 ^ (E + s * j) / 9 ^ L = A := by
  let D := Nat.log 9 A
  let α : ℝ := (s : ℕ) * (Real.log 2 / Real.log 3)
  let β : ℝ := (E : ℕ) * (Real.log 2 / Real.log 3)
  let a : ℝ := (Real.log A - (D : ℝ) * Real.log 9) / Real.log 9
  let b : ℝ := (Real.log (A + 1) - (D : ℝ) * Real.log 9) / Real.log 9
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hαpos : 0 < α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hi : Irrational α := irrational_log_two_div_log_three.natCast_mul (by omega)
  have hlowNat : 9 ^ D ≤ A := Nat.pow_log_le_self 9 (ne_of_gt hA)
  have hhighNat : A + 1 ≤ 9 ^ (D + 1) :=
    Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 9) A)
  have hlow : (D : ℝ) * Real.log 9 ≤ Real.log A := by
    have hh : (9 : ℝ) ^ D ≤ A := by exact_mod_cast hlowNat
    have hl := Real.log_le_log (by positivity : 0 < (9 : ℝ) ^ D) hh
    simpa only [Real.log_pow] using hl
  have hhigh : Real.log (A + 1) ≤ ((D : ℝ) + 1) * Real.log 9 := by
    have hh : (A : ℝ) + 1 ≤ (9 : ℝ) ^ (D + 1) := by exact_mod_cast hhighNat
    have hl := Real.log_le_log (by positivity : 0 < (A : ℝ) + 1) hh
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using hl
  have ha : 0 ≤ a := by dsimp [a]; exact div_nonneg (sub_nonneg.mpr hlow) (le_of_lt h9)
  have hab : a < b := by
    dsimp [a, b]
    apply (div_lt_div_iff_of_pos_right h9).mpr
    have hh := Real.log_lt_log hAr (show (A : ℝ) < A + 1 by linarith)
    linarith
  have hb : b ≤ 1 := by
    dsimp [b]
    rw [div_le_iff₀ h9]
    nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((D : ℝ) / α)
  obtain ⟨j, hj, hja, hjb⟩ := fract_affine_interval_arbitrarily_late hi β ha hab hb (M + N)
  have hx : (D : ℝ) < (j : ℝ) * α + β := by
    have hNj : (N : ℝ) ≤ j := by exact_mod_cast (show N ≤ j by omega)
    have hN' := (div_lt_iff₀ hαpos).mp hN
    nlinarith
  have hx0 : 0 ≤ (j : ℝ) * α + β := by positivity
  let F := Nat.floor ((j : ℝ) * α + β)
  have hDF : D ≤ F := (Nat.le_floor_iff hx0).mpr (le_of_lt hx)
  have hfract : Int.fract ((j : ℝ) * α + β) = j * α + β - F := by
    rw [Int.fract]
    have hh := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_floor_eq_floor hx0)
    simpa only [Int.cast_natCast] using congrArg (fun y : ℝ => j * α + β - y) hh.symm
  rw [hfract] at hja hjb
  have hja' := mul_lt_mul_of_pos_right hja h9
  have hjb' := mul_lt_mul_of_pos_right hjb h9
  dsimp [a] at hja'
  dsimp [b] at hjb'
  rw [div_mul_cancel₀ _ (ne_of_gt h9)] at hja' hjb'
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog : Real.log ((4 : ℝ) ^ (E + s * j)) = (j * α + β) * Real.log 9 := by
    rw [Real.log_pow, hlog4, hlog9]
    dsimp [α, β]
    push_cast
    field_simp
    ring
  have hFD : ((F - D : ℕ) : ℝ) + D = F := by
    exact_mod_cast Nat.sub_add_cancel hDF
  have hloR : (A : ℝ) * (9 : ℝ) ^ (F - D) < (4 : ℝ) ^ (E + s * j) := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (ne_of_gt hAr) (by positivity), hlog, Real.log_pow]
    nlinarith
  have hhiR : (4 : ℝ) ^ (E + s * j) < ((A : ℝ) + 1) * (9 : ℝ) ^ (F - D) := by
    apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_mul (by positivity : (A : ℝ) + 1 ≠ 0) (by positivity), hlog, Real.log_pow]
    nlinarith
  have hloN : A * 9 ^ (F - D) ≤ 4 ^ (E + s * j) := by exact_mod_cast le_of_lt hloR
  have hhiN : 4 ^ (E + s * j) < (A + 1) * 9 ^ (F - D) := by exact_mod_cast hhiR
  exact ⟨j, F - D, by omega, Nat.div_eq_of_lt_le hloN hhiN⟩


/-- Exact arithmetic parameters for arbitrarily large positive perturbations.
The odd leading exponent is enforced by working in base nine. -/
theorem positive_perturbation_data (G N : ℕ) :
    ∃ m D t : ℕ, 0 < m ∧ N + 3 * G + 3 ≤ D ∧ Odd D ∧
      4 ^ m = 1 + 3 ^ D + 4 * (3 ^ G * t) ∧
      3 ^ G * t < 3 ^ (D - (2 * G + 1)) := by
  obtain ⟨j, L, hj, hlead⟩ := leading_prefix_base_nine_in_four_progression
    (3 ^ (2 * G + 1)) 0 (3 ^ G) (N + 3 * G + 3) (by positivity) (by positivity)
  simp only [zero_add] at hlead
  let m := 3 ^ G * j
  let D := 2 * G + 1 + 2 * L
  have h3G : 1 ≤ 3 ^ G := Nat.one_le_pow _ _ (by decide)
  have hjm : j ≤ m := by dsimp [m]; nlinarith
  have hm : 0 < m := by omega
  have hbase : 3 ^ (2 * G + 1) * 9 ^ L = 3 ^ D := by
    dsimp [D]
    rw [show (9 : ℕ) = 3 ^ 2 by decide, ← pow_mul, ← pow_add]
  have hlo : 3 ^ D ≤ 4 ^ m := by
    have hh := (Nat.div_eq_iff (by positivity : 0 < 9 ^ L)).mp hlead
    have hhlo := hh.1
    rw [hbase] at hhlo
    exact hhlo
  have hhi : 4 ^ m < 3 ^ D + 9 ^ L := by
    have hh := (Nat.div_eq_iff (by positivity : 0 < 9 ^ L)).mp hlead
    have hhhi := hh.2
    rw [hbase] at hhhi
    change 4 ^ m ≤ 3 ^ D + 9 ^ L - 1 at hhhi
    have hp : 0 < 9 ^ L := by positivity
    omega
  have hDL : 2 * L ≤ D := by dsimp [D]; omega
  have h9 : 9 ^ L ≤ 3 ^ D := by
    calc
      9 ^ L = 3 ^ (2 * L) := by rw [pow_mul]; norm_num
      _ ≤ 3 ^ D := Nat.pow_le_pow_right (by decide) hDL
  have hmD : m ≤ D := by
    have hh : 3 ^ m < 3 ^ (D + 1) := by
      calc
        3 ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by decide) _
        _ < 3 ^ D + 9 ^ L := hhi
        _ ≤ 3 ^ (D + 1) := by rw [pow_succ]; omega
    have hh' := (Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp hh
    omega
  have hD : N + 3 * G + 3 ≤ D := by omega
  have hodd : Odd D := ⟨G + L, by dsimp [D]; omega⟩
  have hn3 : 4 ^ m % 3 = 1 := by norm_num [Nat.pow_mod]
  have hb3 : 3 ^ D % 3 = 0 := by
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))
  have hlo' : 3 ^ D + 1 ≤ 4 ^ m := by omega
  let x := 4 ^ m - (3 ^ D + 1)
  have hx : 4 ^ m = 3 ^ D + 1 + x := by dsimp [x]; omega
  have hn4 : 4 ^ m % 4 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 4 (by omega))
  have hb4 : 3 ^ D % 4 = 3 := by
    obtain ⟨v, hv⟩ := hodd
    rw [hv, pow_add, pow_mul]
    norm_num [Nat.pow_mod, Nat.mul_mod]
  have hx4 : 4 ∣ x := Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨r, hr⟩ := hx4
  have hnG : Nat.ModEq (3 ^ G) (4 ^ m) 1 := by
    apply ((four_pow_mod_eq_one_iff G m).mpr (dvd_mul_right _ _)).of_dvd
    exact pow_dvd_pow 3 (by omega)
  have hbG : 3 ^ G ∣ 3 ^ D := pow_dvd_pow 3 (by omega)
  have hxG : 3 ^ G ∣ x := by
    have hh : Nat.ModEq (3 ^ G) (3 ^ D + 1 + x) (3 ^ D + 1) := by
      rw [← hx]
      have hh0 : Nat.ModEq (3 ^ G) (3 ^ D + 1) 1 := by
        simpa using (Nat.modEq_zero_iff_dvd.mpr hbG).add_right 1
      exact hnG.trans hh0.symm
    have hh' : Nat.ModEq (3 ^ G) x 0 :=
      Nat.ModEq.add_left_cancel' (3 ^ D + 1) (by simpa using hh)
    exact Nat.modEq_zero_iff_dvd.mp hh' 
  have hrG : 3 ^ G ∣ r := by
    have hcop : Nat.Coprime (3 ^ G) 4 := (by decide : Nat.Coprime 3 4).pow_left G
    exact hcop.dvd_of_dvd_mul_left (hr ▸ hxG)
  obtain ⟨t, ht⟩ := hrG
  refine ⟨m, D, t, hm, hD, hodd, ?_, ?_⟩
  · rw [hr, ht] at hx
    omega
  · have hpow : 3 ^ (D - (2 * G + 1)) = 9 ^ L := by
      have he : D - (2 * G + 1) = 2 * L := by dsimp [D]; omega
      rw [he, pow_mul]
      norm_num
    rw [hpow]
    rw [hr, ht] at hx
    omega

#print axioms leading_prefix_base_nine_in_four_progression
#print axioms positive_perturbation_data
end Erdos406Perturbation
