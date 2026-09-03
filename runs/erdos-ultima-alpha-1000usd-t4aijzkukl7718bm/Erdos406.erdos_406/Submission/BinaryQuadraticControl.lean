import Submission.BinaryQuadraticCriterion
import Submission.BinaryWeightedControl

/-! A kernel-checked quadratic control at rate5/8. Its strict rate condition
is false, so this is explicitly not a proof of the original conjecture. -/
namespace Erdos406BinaryQuadraticControl
open Erdos406BinaryWeighted Erdos406BinaryWeightedControl Erdos406GroupedCertificate
noncomputable section

private def upper : Fin 6 → ℤ
  | 0 => 0 | 1 => 3 | 2 => -4 | 3 => -2 | 4 => -3 | _ => -1
private def lower : Fin 6 → ℤ
  | 0 => 0 | 1 => 3 | 2 => -4 | 3 => -5 | 4 => -3 | _ => -5

private lemma edge_checks : ∀ (s : Fin 6) (d : Fin 2), s ≠ 0 ∨ d.val ≠ 0 →
    upper s + W s d.val ≤ 5 + upper (D.step s d.val) ∧
    5 + lower (D.step s d.val) ≤ lower s + W s d.val := by decide +kernel

private lemma endpoint_checks : ∀ s : Fin 6, upper s ≤ 3 ∧ -5 ≤ lower s := by
  decide +kernel

private lemma state_ne_zero (n : ℕ) (hn : 0 < n) : evalNat 2 D n ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [evalNat_pos 2 D (by decide) hn]
    by_cases hq : n/2 = 0
    · have hd : n%2 = 1 := by omega
      norm_num [hq, hd, evalNat_zero, D]
    · have hh := ih (n/2) (Nat.div_lt_self hn (by decide)) (Nat.pos_of_ne_zero hq)
      have hc : ∀ (s : Fin 6) (d : Fin 2), s ≠ 0 → D.step s d.val ≠ 0 := by decide +kernel
      exact hc _ ⟨n%2, Nat.mod_lt _ (by decide)⟩ hh

private lemma weighted_bounds (n : ℕ) :
    (5/8:ℝ)*(Nat.digits 2 n).length + (lower (evalNat 2 D n):ℝ)/8 ≤ weightNat D w n ∧
    weightNat D w n ≤ (5/8:ℝ)*(Nat.digits 2 n).length + (upper (evalNat 2 D n):ℝ)/8 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      norm_num [weightNat_zero, evalNat_zero, D, lower, upper]
    have hp : 0 < n := Nat.pos_of_ne_zero hz
    have hq := ih (n/2) (Nat.div_lt_self hp (by decide))
    have hd : n%2 < 2 := Nat.mod_lt _ (by decide)
    have hstate : evalNat 2 D (n/2) ≠ 0 ∨ n%2 ≠ 0 := by
      by_cases hq : n/2 = 0
      · right; omega
      · exact Or.inl (state_ne_zero _ (Nat.pos_of_ne_zero hq))
    have hh := edge_checks (evalNat 2 D (n/2)) ⟨n%2,hd⟩ hstate
    have hhu : (upper (evalNat 2 D (n/2)):ℝ) + W (evalNat 2 D (n/2)) (n%2) ≤
        5 + upper (D.step (evalNat 2 D (n/2)) (n%2)) := by exact_mod_cast hh.1
    have hhl : (5:ℝ) + lower (D.step (evalNat 2 D (n/2)) (n%2)) ≤
        lower (evalNat 2 D (n/2)) + W (evalNat 2 D (n/2)) (n%2) := by exact_mod_cast hh.2
    rw [weightNat_pos D w hp, evalNat_pos 2 D (by decide) hp,
      Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) hp]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, w]
    constructor <;> linarith [hq.1,hq.2]

lemma weight_nonnegative (n : ℕ) : 0 ≤ weightNat D w n := by
  by_cases hz : n = 0
  · simp [hz, weightNat_zero]
  have hh := (weighted_bounds n).1
  have he : (-5:ℝ) ≤ lower (evalNat 2 D n) := by
    exact_mod_cast (endpoint_checks (evalNat 2 D n)).2
  have hlen : 1 ≤ (Nat.digits 2 n).length := by
    have hpow := Nat.lt_base_pow_length_digits (m:=n) (by decide : 1 < 2)
    by_contra h
    have hl : (Nat.digits 2 n).length = 0 := by omega
    rw [hl] at hpow
    norm_num at hpow
    omega
  have hlenR : (1:ℝ) ≤ (Nat.digits 2 n).length := by exact_mod_cast hlen
  linarith

lemma weight_upper (n : ℕ) :
    weightNat D w n ≤ (5/8:ℝ)*(Nat.digits 2 n).length + 3/8 := by
  have hh := (weighted_bounds n).2
  have he : (upper (evalNat 2 D n):ℝ) ≤ 3 := by
    exact_mod_cast (endpoint_checks (evalNat 2 D n)).1
  linarith

def potential (n : ℕ) : ℝ := (8/5:ℝ)*(weightNat D w n)^2

lemma control_construction_bound (n d : ℕ) (hd : d < 2) :
    potential (3*n+d) ≤ potential n + 2*(Nat.digits 2 n).length + 14/5 := by
  have hs := Erdos406BinaryWeightedControl.control_construction_bound n d hd
  have h0 := weight_nonnegative n
  have h1 := weight_nonnegative (3*n+d)
  have hu := weight_upper n
  have hh : (weightNat D w (3*n+d))^2 ≤ (weightNat D w n+1)^2 := by nlinarith
  unfold potential
  nlinarith

lemma control_power_bound (k : ℕ) : (5/8:ℝ)*(k:ℝ)^2 ≤ potential (2^k) := by
  have hh := Erdos406BinaryWeightedControl.control_power_bound k
  have hp : (0:ℝ) ≤ k := by positivity
  have h0 := weight_nonnegative (2^k)
  unfold potential
  nlinarith

lemma control_not_supercritical : ¬ Real.log 2 < (5/8:ℝ)*Real.log 3 :=
  Erdos406BinaryWeightedControl.control_not_supercritical

#print axioms weight_nonnegative
#print axioms weight_upper
#print axioms control_construction_bound
#print axioms control_power_bound
#print axioms control_not_supercritical
end
end Erdos406BinaryQuadraticControl
