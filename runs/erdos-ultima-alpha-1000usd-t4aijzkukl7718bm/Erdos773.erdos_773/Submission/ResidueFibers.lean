import FormalConjecturesUtil

/-!
Exact within-fiber Sidon control for a unit arithmetic progression. Auxiliary
work on residue lifting; this is not a proof of Erdős 773.
-/
namespace Erdos773.ResidueFibers
open Finset
set_option maxHeartbeats 1000000

lemma sum_gap_forces_square_sum_gap (q a b c d : ℕ)
    (hq : 0 < q) (hc : c ≤ q) (hd : d ≤ q)
    (hgap : c + d + q ≤ a + b) : c ^ 2 + d ^ 2 < a ^ 2 + b ^ 2 := by
  have hc2 := Nat.mul_le_mul_left c hc
  have hd2 := Nat.mul_le_mul_left d hd
  have hsq := Nat.pow_le_pow_left hgap 2
  have hab : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
    have h := sq_nonneg ((a : ℤ) - b)
    have h' : (2 : ℤ) * a * b ≤ a ^ 2 + b ^ 2 := by nlinarith
    exact_mod_cast h'
  nlinarith

lemma unit_progression_collision (q r a b c d : ℕ) (hq : 0 < q)
    (hcop : q.Coprime (2 * r))
    (ha : a ≤ q) (hb : b ≤ q) (hc : c ≤ q) (hd : d ≤ q)
    (he : (q * a + r) ^ 2 + (q * b + r) ^ 2 =
      (q * c + r) ^ 2 + (q * d + r) ^ 2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hr : q * (a ^ 2 + b ^ 2) + 2 * r * (a + b) =
      q * (c ^ 2 + d ^ 2) + 2 * r * (c + d) := by
    apply Nat.eq_of_mul_eq_mul_left hq
    nlinarith only [he]
  have hm : 2 * r * (a + b) ≡ 2 * r * (c + d) [MOD q] := by
    have h := congrArg (fun x : ℕ => x % q) hr
    simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod] using h
  have hsumMod : a + b ≡ c + d [MOD q] := hm.cancel_left_of_coprime hcop
  have hsum : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with h | h | h
    · have hg := hsumMod.add_le_of_lt h
      have hs := sum_gap_forces_square_sum_gap q c d a b hq ha hb hg
      have hmul := Nat.mul_lt_mul_of_pos_left hs hq
      have hlin := Nat.mul_le_mul_left (2 * r) h.le
      omega
    · exact h
    · have hg := hsumMod.symm.add_le_of_lt h
      have hs := sum_gap_forces_square_sum_gap q a b c d hq hc hd hg
      have hmul := Nat.mul_lt_mul_of_pos_left hs hq
      have hlin := Nat.mul_le_mul_left (2 * r) h.le
      omega
  have hsq : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by
    rw [hsum] at hr
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel hr)
  have hsum' : (a : ℤ) + b = c + d := by exact_mod_cast hsum
  have hsq' : (a : ℤ) ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by exact_mod_cast hsq
  have hf : ((a : ℤ) - c) * (a - d) = 0 := by
    have hb' : (b : ℤ) = c + d - a := by omega
    rw [hb'] at hsq'
    nlinarith only [hsq']
  rcases mul_eq_zero.mp hf with h | h
  · left
    have hh : a = c := by exact_mod_cast sub_eq_zero.mp h
    exact ⟨hh, by omega⟩
  · right
    have hh : a = d := by exact_mod_cast sub_eq_zero.mp h
    exact ⟨hh, by omega⟩

lemma unit_progression_squares_sidon (q r : ℕ) (hq : 0 < q)
    (hcop : q.Coprime (2 * r)) :
    IsSidon (((Icc 0 q).image (fun a => (q * a + r) ^ 2)) : Set ℕ) := by
  intro a ha c hc b hb d hd he
  simp only [mem_coe, mem_image, mem_Icc] at ha hc hb hd
  obtain ⟨a, ⟨_, ha⟩, rfl⟩ := ha
  obtain ⟨c, ⟨_, hc⟩, rfl⟩ := hc
  obtain ⟨b, ⟨_, hb⟩, rfl⟩ := hb
  obtain ⟨d, ⟨_, hd⟩, rfl⟩ := hd
  rcases unit_progression_collision q r a b c d hq hcop ha hb hc hd he with h | h
  · left; simp [h.1, h.2]
  · right; simp [h.1, h.2]

lemma cross_fiber_identity (q : ℤ) :
    (5 * q - 1) ^ 2 + (5 * q - 2) ^ 2 =
      (q - 1) ^ 2 + (7 * q - 2) ^ 2 := by
  ring

/-- Individual fibers and the two coarse square residues can all be Sidon,
while their union is not. This is only a check of the proposed lifting rule. -/
lemma separate_fiber_conditions_do_not_suffice :
    IsSidon (((Icc 0 11).image (fun a : ℕ => (11 * a + 10) ^ 2)) : Set ℕ) ∧
    IsSidon (((Icc 0 11).image (fun a : ℕ => (11 * a + 9) ^ 2)) : Set ℕ) ∧
    IsSidon ({(10 : ZMod 11) ^ 2, (9 : ZMod 11) ^ 2} : Set (ZMod 11)) ∧
    ¬ IsSidon ((((Icc 0 11).image (fun a : ℕ => (11 * a + 10) ^ 2)) ∪
      ((Icc 0 11).image (fun a : ℕ => (11 * a + 9) ^ 2))) : Set ℕ) := by
  refine ⟨unit_progression_squares_sidon 11 10 (by decide) (by decide),
    unit_progression_squares_sidon 11 9 (by decide) (by decide), by norm_num [IsSidon]; decide, ?_⟩
  intro hs
  have hh := hs (54 ^ 2) (by decide) (10 ^ 2) (by decide)
    (53 ^ 2) (by decide) (75 ^ 2) (by decide) (by norm_num)
  norm_num at hh

#print axioms unit_progression_squares_sidon
#print axioms separate_fiber_conditions_do_not_suffice
end Erdos773.ResidueFibers
