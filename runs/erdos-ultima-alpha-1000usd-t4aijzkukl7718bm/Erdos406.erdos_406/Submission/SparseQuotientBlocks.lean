import Submission.SparseTriple

/-! A sharp short-quotient lemma for a sparse two-one multiplier. The size
hypothesis is essential for arbitrary multipliers. No global bound on a
power-of-two exponent, or solution of Erdős406, is asserted. -/
namespace Erdos406SparseQuotient
open Erdos406SparseTriple Erdos406AffineCertificate

lemma good_block_bound {L n : ℕ} (hg : Good n) (hn : n < 3 ^ L) :
    2 * n < 3 ^ L := by
  induction L generalizing n with
  | zero => simp only [pow_zero] at hn ⊢; omega
  | succ L ih =>
    have hq : n / 3 < 3 ^ L := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr
      simpa only [pow_succ] using hn
    have hh := ih (good_div_three hg) hq
    have hr : n % 3 < 2 := by
      simpa using lowGood_of_good hg 1 ⟨0, by decide⟩
    rw [pow_succ]
    omega

lemma three_block_middle (B a b c n : ℕ)
    (ha : 2 * a < B) (hb : 2 * b < B) (hc : 2 * c < B)
    (hn : n = a + B * b + B ^ 2 * c) (hd : B + 1 ∣ n) : b = a + c := by
  obtain ⟨t, ht⟩ := hd
  have he : (B + 1) * (t + c) + b = (B + 1) * (b + B * c) + (a + c) := by
    calc
      _ = n + (B + 1) * c + b := by rw [ht]; ring
      _ = _ := by rw [hn]; ring
  have hm := congrArg (fun x : ℕ => x % (B + 1)) he
  have hb' : b < B + 1 := by omega
  have hac : a + c < B + 1 := by omega
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt hac] using hm

/-- If a good integer divisible by `3^L+1` fits in three length-L blocks,
then its quotient is good. -/
theorem short_quotient_good (L m : ℕ)
    (hg : Good ((3 ^ L + 1) * m))
    (hsize : (3 ^ L + 1) * m < (3 ^ L) ^ 3) : Good m := by
  let B := 3 ^ L
  let n := (B + 1) * m
  let a := n % B
  let b := n / B % B
  let c := n / B / B
  have hB : 0 < B := by dsimp [B]; positivity
  have ha : a < B := Nat.mod_lt _ hB
  have hb : b < B := Nat.mod_lt _ hB
  have hq : n / B < B ^ 2 := by
    apply (Nat.div_lt_iff_lt_mul hB).mpr
    change (3 ^ L + 1) * m < (3 ^ L) ^ 2 * 3 ^ L
    simpa only [pow_succ] using hsize
  have hc : c < B := by
    apply (Nat.div_lt_iff_lt_mul hB).mpr
    simpa only [pow_two] using hq
  have hga : Good a := good_mod_pow hg L
  have hgb : Good b := good_mod_pow (good_div_pow hg L) L
  have hgc : Good c := good_div_pow (good_div_pow hg L) L
  have hn : n = a + B * b + B ^ 2 * c := by
    have hq' : n / B = b + B * c := (Nat.mod_add_div (n / B) B).symm
    calc
      n = a + B * (n / B) := (Nat.mod_add_div n B).symm
      _ = _ := by rw [hq']; ring
  have hm := three_block_middle B a b c n
    (good_block_bound hga ha) (good_block_bound hgb hb) (good_block_bound hgc hc)
    hn (dvd_mul_right _ _)
  have he : (B + 1) * m = (B + 1) * (a + B * c) := by
    change n = _
    rw [hn, hm]
    ring
  have hquot : m = a + B * c := Nat.eq_of_mul_eq_mul_left (by omega) he
  rw [hquot, Nat.add_comm]
  exact good_prefix hgc hga ha

lemma boundary_identity (B : ℕ) (hB : 1 ≤ B) :
    (B + 1) * (B * (B - 1) + 1) = B ^ 3 + 1 := by
  have h := Nat.sub_add_cancel hB
  have h₁ := congrArg (fun x : ℕ => B * x) h
  have h₂ := congrArg (fun x : ℕ => B ^ 2 * x) h
  nlinarith only [h₁, h₂]

/-- At the next possible leading block the implication fails for general
multipliers. The multiplier here is odd and greater than one, not a power
of two, so this is not a counterexample to Erdős406. -/
theorem sharp_boundary (L : ℕ) (hL : 0 < L) :
    let B := 3 ^ L
    let m := B * (B - 1) + 1
    (B + 1) * m = B ^ 3 + 1 ∧ Good ((B + 1) * m) ∧
      ¬ Good m ∧ ¬ m.isPowerOfTwo := by
  dsimp only
  let B := 3 ^ L
  let m := B * (B - 1) + 1
  have hB : 3 ≤ B := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 1 ≤ L)
    simpa [B] using hh
  have hid : (B + 1) * m = B ^ 3 + 1 := boundary_identity B (by omega)
  have hgood1 : Good 1 := by norm_num [Good, Nat.digits_of_two_le_of_pos]
  have hpow : 1 < 3 ^ (L * 3) := one_lt_pow₀ (by decide) (by omega)
  have hgood : Good ((B + 1) * m) := by
    rw [hid]
    simpa only [pow_mul, mul_one, B] using good_prefix (k := L * 3) hgood1 hgood1 hpow
  have hq : m / B = B - 1 := by
    dsimp only [m]
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega : 0 < B),
      Nat.div_eq_of_lt (by omega : 1 < B), zero_add]
  have hB3 : B % 3 = 0 := by
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega : L ≠ 0))
  have hbad : ¬ Good m := by
    intro hg
    have hh : m / 3 ^ L % 3 < 2 := by
      simpa using lowGood_of_good (good_div_pow hg L) 1 ⟨0, by decide⟩
    change m / B % 3 < 2 at hh
    rw [hq] at hh
    omega
  have hB2 : B % 2 = 1 := by dsimp [B]; simp [Nat.pow_mod]
  have hp2 : (B - 1) % 2 = 0 := by omega
  have hm2 : m % 2 = 1 := by
    dsimp [m]
    simp [Nat.add_mod, Nat.mul_mod, hp2]
  have hm1 : 1 < m := by
    have hp : 0 < B * (B - 1) := Nat.mul_pos (by omega) (by omega)
    dsimp only [m]
    omega
  have hnopow : ¬ m.isPowerOfTwo := by
    rintro ⟨k, hk⟩
    cases k with
    | zero => simp at hk; omega
    | succ k => rw [hk, pow_succ] at hm2; omega
  exact ⟨hid, hgood, hbad, hnopow⟩

#print axioms short_quotient_good
#print axioms sharp_boundary
end Erdos406SparseQuotient
