import Submission.CubicRootObstruction
import Submission.CubicBlockRigidity

/-! Finite boundary-digit tests cannot certify pure-power cube descent.
These theorems do not assert goodness of the entire cube, and do not settle
Erdős 406. -/

namespace Erdos406Work

lemma unit_power_residue (r A : ℕ) (hA : A % 3 = 1) :
    ∃ e : ℕ, e < 3 ^ r ∧ Nat.ModEq (3 ^ (r + 1)) (4 ^ e) A := by
  let f : Fin (3 ^ r) → Fin (3 ^ r) := fun e =>
    ⟨(4 ^ e.val % 3 ^ (r + 1)) / 3, by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr
      simpa only [pow_succ] using Nat.mod_lt (4 ^ e.val) (by positivity : 0 < 3 ^ (r + 1))⟩
  have hrem (n : ℕ) : (n % 3 ^ (r + 1)) % 3 = n % 3 := by
    exact Nat.mod_mod_of_dvd n (dvd_pow_self 3 (by omega : r + 1 ≠ 0))
  have hunit (e : ℕ) : (4 ^ e % 3 ^ (r + 1)) % 3 = 1 := by
    rw [hrem]
    norm_num [Nat.pow_mod]
  have hinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    apply four_pow_mod_injective a.isLt b.isLt
    have heq := congrArg Fin.val hab
    dsimp only [f] at heq
    have ha := hunit a.val
    have hb := hunit b.val
    omega
  have hsurj := Finite.surjective_of_injective hinj
  let t : Fin (3 ^ r) := ⟨(A % 3 ^ (r + 1)) / 3, by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr
    simpa only [pow_succ] using Nat.mod_lt A (by positivity : 0 < 3 ^ (r + 1))⟩
  obtain ⟨e, he⟩ := hsurj t
  refine ⟨e.val, e.isLt, ?_⟩
  have heq := congrArg Fin.val he
  dsimp only [f, t] at heq
  have hu := hunit e.val
  have hAr : A % 3 ^ (r + 1) % 3 = 1 := (hrem A).trans hA
  change 4 ^ e.val % 3 ^ (r + 1) = A % 3 ^ (r + 1)
  omega

/-- Arbitrarily late pure powers can have any prescribed positive leading
block and any prescribed trailing residue congruent to one modulo three. -/
lemma residue_prefix_in_four_powers (r A B M : ℕ) (hA : A % 3 = 1) (hB : 0 < B) :
    ∃ m L : ℕ, M ≤ m ∧ Nat.ModEq (3 ^ (r + 1)) (4 ^ m) A ∧
      4 ^ m / 3 ^ L = B := by
  obtain ⟨e, he, hres⟩ := unit_power_residue r A hA
  obtain ⟨j, L, hj, hlead⟩ := leading_prefix_in_four_progression B e (3 ^ r) M hB (by positivity)
  refine ⟨e + 3 ^ r * j, L, ?_, ?_, hlead⟩
  · have hp : 1 ≤ 3 ^ r := Nat.one_le_pow _ _ (by decide)
    nlinarith
  · have hh : Nat.ModEq (3 ^ (r + 1)) (4 ^ (3 ^ r * j)) 1 :=
      (four_pow_mod_eq_one_iff r _).mpr (dvd_mul_right _ _)
    simpa only [← pow_add, mul_one] using hres.mul hh

/-- Even with roots restricted to arbitrarily large pure powers of four,
any fixed number of good LOW cube digits is compatible with a bad root.
The whole cube is not claimed to be good. -/
lemma pure_power_cube_tail_no_descent (R M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ Nat.digits 3 (4 ^ (3 * m) % 3 ^ R) ⊆ [0, 1] ∧
      ¬ Nat.digits 3 (4 ^ m) ⊆ [0, 1] := by
  obtain ⟨m, L, hm, hres, hlead⟩ := residue_prefix_in_four_powers R 562 562 M (by decide) (by decide)
  have hcube : Nat.ModEq (3 ^ R) (4 ^ (3 * m)) (562 ^ 3) := by
    have hh := (hres.pow 3).of_dvd (pow_dvd_pow 3 (by omega : R ≤ R + 1))
    simpa only [← pow_mul, Nat.mul_comm m 3] using hh
  refine ⟨m, hm, ?_, ?_⟩
  · rw [hcube]
    exact good_mod_three_pow plain_cube_descent_counterexample.1 R
  · intro hg
    have hh := good_div_three_pow hg L
    rw [hlead] at hh
    exact plain_cube_descent_counterexample.2.1 hh

set_option maxHeartbeats 2000000 in
lemma cube_prefix_from_near_562 {n L R : ℕ}
    (hn : n / 3 ^ L = 562 * 3 ^ (R + 13)) :
    n ^ 3 / 3 ^ (3 * L + 2 * R + 39) = 562 ^ 3 * 3 ^ R := by
  let p := 3 ^ (R + 13)
  let q := 3 ^ L
  have hp : 1 ≤ p := Nat.one_le_pow _ _ (by decide)
  have hq : 0 < q := by dsimp [q]; positivity
  have hbounds := (Nat.div_eq_iff hq).mp hn
  change 562 * p * q ≤ n ∧ n ≤ 562 * p * q + q - 1 at hbounds
  have hhigh : n < (562 * p + 1) * q := by
    rw [add_mul, one_mul]
    omega
  have herr : (562 * p + 1) ^ 3 ≤ (562 * p) ^ 3 + p ^ 2 * 3 ^ 13 := by
    have hpp : p ≤ p ^ 2 := by nlinarith
    norm_num
    nlinarith
  have hden : 3 ^ (3 * L + 2 * R + 39) = q ^ 3 * p ^ 2 * 3 ^ 13 := by
    dsimp only [p, q]
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  have hpId : p = 3 ^ R * 3 ^ 13 := by dsimp only [p]; exact pow_add 3 R 13
  have hlo : (562 ^ 3 * 3 ^ R) * 3 ^ (3 * L + 2 * R + 39) ≤ n ^ 3 := by
    have he : (562 ^ 3 * 3 ^ R) * 3 ^ (3 * L + 2 * R + 39) = (562 * p * q) ^ 3 := by
      rw [hden, hpId]
      ring
    rw [he]
    exact Nat.pow_le_pow_left hbounds.1 3
  have hhi : n ^ 3 < (562 ^ 3 * 3 ^ R + 1) * 3 ^ (3 * L + 2 * R + 39) := by
    calc
      n ^ 3 < ((562 * p + 1) * q) ^ 3 := Nat.pow_lt_pow_left hhigh (by decide)
      _ = (562 * p + 1) ^ 3 * q ^ 3 := mul_pow _ _ _
      _ ≤ ((562 * p) ^ 3 + p ^ 2 * 3 ^ 13) * q ^ 3 := Nat.mul_le_mul_right _ herr
      _ = _ := by rw [hden, hpId]; ring
  exact Nat.div_eq_of_lt_le hlo hhi

/-- A pure power can have a bad root while its cube has an arbitrarily long
prescribed good leading block and an arbitrarily long good trailing block.
No assertion is made about the cube's intervening digits. -/
theorem pure_power_cube_good_boundaries_bad_root (R M : ℕ) :
    ∃ m L : ℕ, M ≤ m ∧
      ¬ Nat.digits 3 (4 ^ m) ⊆ [0, 1] ∧
      Nat.digits 3 (4 ^ (3 * m) % 3 ^ R) ⊆ [0, 1] ∧
      4 ^ (3 * m) / 3 ^ L = 562 ^ 3 * 3 ^ R ∧
      (Nat.digits 3 (4 ^ (3 * m))).reverse.take R ⊆ [0, 1] := by
  obtain ⟨m, L, hm, hres, hlead⟩ :=
    residue_prefix_in_four_powers R 562 (562 * 3 ^ (R + 13)) M (by decide) (by positivity)
  have hcube : Nat.ModEq (3 ^ R) (4 ^ (3 * m)) (562 ^ 3) := by
    have hh := (hres.pow 3).of_dvd (pow_dvd_pow 3 (by omega : R ≤ R + 1))
    simpa only [← pow_mul, Nat.mul_comm m 3] using hh
  have hrootbad : ¬ Nat.digits 3 (4 ^ m) ⊆ [0, 1] := by
    intro hg
    have hh := good_div_three_pow hg L
    rw [hlead, mul_comm, good_mul_three_pow_iff] at hh
    exact plain_cube_descent_counterexample.2.1 hh
  have hprefix : 4 ^ (3 * m) / 3 ^ (3 * L + 2 * R + 39) = 562 ^ 3 * 3 ^ R := by
    simpa only [← pow_mul, Nat.mul_comm m 3] using cube_prefix_from_near_562 hlead
  refine ⟨m, 3 * L + 2 * R + 39, hm, hrootbad, ?_, hprefix, ?_⟩
  · rw [hcube]
    exact good_mod_three_pow plain_cube_descent_counterexample.1 R
  · have hg : Nat.digits 3 (562 ^ 3 * 3 ^ R) ⊆ [0, 1] := by
      rw [mul_comm, good_mul_three_pow_iff]
      exact plain_cube_descent_counterexample.1
    have hlen : R ≤ (Nat.digits 3 (562 ^ 3 * 3 ^ R)).length := by
      have hge : 3 ^ R ≤ 562 ^ 3 * 3 ^ R := Nat.le_mul_of_pos_left _ (by decide)
      have hlt := Nat.lt_base_pow_length_digits (b := 3) (m := 562 ^ 3 * 3 ^ R) (by decide)
      have he : 3 ^ R < 3 ^ (Nat.digits 3 (562 ^ 3 * 3 ^ R)).length := lt_of_le_of_lt hge hlt
      exact Nat.le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 3)).mp he)
    rw [fixed_leading_digits_of_quotient hprefix hlen]
    exact fun d hd => hg (List.mem_reverse.mp (List.mem_of_mem_take hd))

/-- In fact, the leading cube block is arbitrary, and the cube's trailing
residue may be any residue arising from a root congruent to one modulo three.
An extra root digit beyond the tested tail can be forced to be two. -/
theorem arbitrary_cube_boundary_bad_root (R M A B : ℕ)
    (hA : A % 3 = 1) (hB : 0 < B) :
    ∃ m L : ℕ, M ≤ m ∧ ¬ Nat.digits 3 (4 ^ m) ⊆ [0, 1] ∧
      Nat.ModEq (3 ^ R) (4 ^ (3 * m)) (A ^ 3) ∧ 4 ^ (3 * m) / 3 ^ L = B := by
  let T := R + 1
  let Q := 3 ^ T
  let a := A % Q + 2 * Q
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have h3Q : 3 ∣ Q := dvd_pow_self 3 (by dsimp [T]; omega)
  have ha3 : a % 3 = 1 := by
    dsimp [a]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd A h3Q, Nat.mul_mod, Nat.mod_eq_zero_of_dvd h3Q]
    simpa using hA
  have haBound : a < 3 ^ (T + 1) := by
    rw [pow_succ]
    change A % Q + 2 * Q < Q * 3
    have hmod := Nat.mod_lt A hQ
    omega
  obtain ⟨e, he, hres⟩ := unit_power_residue T a ha3
  obtain ⟨j, L, hj, hlead⟩ := leading_prefix_in_four_progression B (3 * e) (3 * Q) M hB (by positivity)
  let m := e + Q * j
  have hm : M ≤ m := by
    have hQ1 : 1 ≤ Q := by omega
    dsimp [m]
    nlinarith
  have hroot : Nat.ModEq (3 ^ (T + 1)) (4 ^ m) a := by
    have hh : Nat.ModEq (3 ^ (T + 1)) (4 ^ (Q * j)) 1 :=
      (four_pow_mod_eq_one_iff T _).mpr (dvd_mul_right _ _)
    simpa only [← pow_add, mul_one] using hres.mul hh
  have hrootbad : ¬ Nat.digits 3 (4 ^ m) ⊆ [0, 1] := by
    intro hg
    have hga := good_mod_three_pow hg (T + 1)
    rw [hroot, Nat.mod_eq_of_lt haBound] at hga
    have hh := good_div_three_pow hga T
    have heq : a / 3 ^ T = 2 := by
      dsimp only [a, Q]
      rw [mul_comm 2, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt (Nat.mod_lt A (by positivity)), zero_add]
    rw [heq] at hh
    norm_num [Nat.digits_of_two_le_of_pos] at hh
  have hdiv : 3 ^ R ∣ Q := pow_dvd_pow 3 (by dsimp [T]; omega)
  have halow : Nat.ModEq (3 ^ R) a A := by
    change a % 3 ^ R = A % 3 ^ R
    dsimp only [a]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd A hdiv, Nat.mul_mod,
      Nat.mod_eq_zero_of_dvd hdiv]
    simp
  have hrootlow := (hroot.of_dvd (pow_dvd_pow 3 (by dsimp [T]; omega : R ≤ T + 1))).trans halow
  refine ⟨m, L, hm, hrootbad, ?_, ?_⟩
  · simpa only [← pow_mul, Nat.mul_comm m 3] using hrootlow.pow 3
  · have heq : 3 * e + 3 * Q * j = 3 * m := by dsimp [m]; ring
    simpa only [heq] using hlead

/-- A finite test of good leading and trailing cube digits, even with an
arbitrarily late threshold and a pure-power root, cannot replace the premise
that the WHOLE cube is good. -/
theorem no_finite_boundary_cubic_descent :
    ¬ (∃ R M : ℕ, ∀ m : ℕ, M ≤ m →
      Nat.digits 3 (4 ^ m % 3 ^ R) ⊆ [0, 1] →
      (Nat.digits 3 (4 ^ m)).reverse.take R ⊆ [0, 1] →
      Nat.digits 3 (4 ^ (m / 3)) ⊆ [0, 1]) := by
  rintro ⟨R, M, h⟩
  obtain ⟨m, L, hm, hbad, htail, hprefix, hhead⟩ :=
    pure_power_cube_good_boundaries_bad_root R M
  have hh := h (3 * m) (by omega) htail hhead
  have he : 3 * m / 3 = m := by omega
  rw [he] at hh
  exact hbad hh

#print axioms arbitrary_cube_boundary_bad_root
#print axioms no_finite_boundary_cubic_descent

#print axioms cube_prefix_from_near_562
#print axioms pure_power_cube_good_boundaries_bad_root

#print axioms unit_power_residue
#print axioms residue_prefix_in_four_powers
#print axioms pure_power_cube_tail_no_descent
end Erdos406Work
