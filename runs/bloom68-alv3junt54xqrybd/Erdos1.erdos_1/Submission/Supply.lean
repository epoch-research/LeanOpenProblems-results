import Submission.Kernel

/-!
# Choosing an efficient cyclic code from an adjustable kernel

The supply of adjustable kernels is an explicit hypothesis.  A sufficiently
large even charge leaves room to adjust the period to one modulo any positive
odd modulus without losing the required efficiency.
-/

namespace ErdosDSS

/-- A coprime step reaches one modulo `P` in fewer than `P` steps.
The congruence formulation includes the case `P = 1`. -/
private lemma exists_adjustment {P step : ℕ} (hP : 0 < P)
    (hcop : Nat.Coprime step P) (B : ℕ) :
    ∃ u < P, Nat.ModEq P (B + u * step) 1 := by
  obtain ⟨u, hu, hmod⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (P + 1 - B % P) hcop hP.ne'
  have htarget : Nat.ModEq P (B + (P + 1 - B % P)) 1 := by
    unfold Nat.ModEq
    rw [← Nat.mod_add_mod, Nat.add_sub_of_le (by have := Nat.mod_lt B hP; omega)]
    simp
  refine ⟨u, hu, ?_⟩
  have h : Nat.ModEq P (step * u) (P + 1 - B % P) := hmod
  simpa only [mul_comm] using (h.add_left B).trans htarget

/-- Adjustable kernels at all even charges supply efficient cyclic codes
at arbitrarily large charges and with any prescribed positive odd modulus. -/
theorem treeSupply_codeSupply (hs : TreeSupply) : CodeSupply := by
  intro P hP hodd K
  let q := 2 * (48 * P + K + 1)
  have hq_even : Even q := by
    refine ⟨48 * P + K + 1, ?_⟩
    dsimp [q]
    omega
  have hq_two : 2 ≤ q := by dsimp [q]; omega
  have hq_large : K < q := by dsimp [q]; omega
  have hq_pow : 48 * P ≤ 2 ^ q := by
    calc
      48 * P ≤ q := by dsimp [q]; omega
      _ ≤ 2 ^ q := Nat.le_of_lt Nat.lt_two_pow_self
  obtain ⟨a⟩ := hs q hq_even hq_two
  have hcop : Nat.Coprime (2 ^ (a.m - a.h)) P :=
    hodd.coprime_two_left.pow_left _
  obtain ⟨u, hu, hres⟩ := exists_adjustment hP hcop a.B
  have hu_bound : 48 * u ≤ 2 ^ a.h := by
    calc
      48 * u ≤ 48 * P := Nat.mul_le_mul_left 48 (Nat.le_of_lt hu)
      _ ≤ 2 ^ q := hq_pow
      _ ≤ 2 ^ a.h := Nat.pow_le_pow_right (by decide) a.height
  have hpow : 2 ^ a.h * 2 ^ (a.m - a.h) = 2 ^ a.m := by
    rw [← pow_add, Nat.add_sub_of_le a.h_le_m]
  have hadjust : 48 * (u * 2 ^ (a.m - a.h)) ≤ 2 ^ a.m := by
    calc
      48 * (u * 2 ^ (a.m - a.h)) = (48 * u) * 2 ^ (a.m - a.h) :=
        (mul_assoc _ _ _).symm
      _ ≤ 2 ^ a.h * 2 ^ (a.m - a.h) := Nat.mul_le_mul_right _ hu_bound
      _ = 2 ^ a.m := hpow
  have heff : 48 * (a.B + u * 2 ^ (a.m - a.h)) ≤ 35 * 2 ^ a.m := by
    have hbase := a.efficiency
    rw [mul_add]
    omega
  let d := a.data u
  refine ⟨q, hq_large, ⟨{
    m := a.m
    B := a.B + u * 2 ^ (a.m - a.h)
    b := d.b
    q_pos := d.q_pos
    B_pos := d.B_pos
    B_odd := d.B_odd
    small := d.small
    kernel := d.kernel
    efficiency := heff
    residue := hres
  }⟩⟩

end ErdosDSS
