import Submission.RegularPredecessorFamilies

/-! Soundness of automatic zero-block insertion into a certified good
multiple. This supplies necessary regular rejections, not an invariant. -/
namespace Erdos406PumpedNegative
open Erdos406RegularPredecessor Erdos406Work

lemma tail_length (v w : List ℕ) (L R : ℕ)
    (hv : v.length = L) (hw : w.length = R) (t : ℕ) :
    (tailWord v w t).length = R + L * t := by
  induction t with
  | zero => simpa [tailWord] using hw
  | succ t ih => rw [tailWord, List.length_append, hv, ih]; ring

lemma identity (K L R b : ℕ) (v w : List ℕ)
    (hv : v.length = L) (hw : w.length = R)
    (hloop : K * wordValue v + 1 = 3 ^ L)
    (htail : K * wordValue w = 3 ^ R + b) (t : ℕ) :
    K * wordValue (tailWord v w t) = 3 ^ (R + L * t) + b := by
  induction t with
  | zero => simpa [tailWord] using htail
  | succ t ih =>
    rw [tailWord, wordValue_append, tail_length v w L R hv hw]
    have he : 3 ^ (R + L * (t + 1)) = 3 ^ (R + L * t) * 3 ^ L := by
      rw [show R + L * (t + 1) = (R + L * t) + L by ring, pow_add]
    rw [he]
    have hh := congrArg (fun n : ℕ => 3 ^ (R + L * t) * n) hloop
    nlinarith

lemma output_good (K L R b : ℕ) (v w : List ℕ)
    (hv : v.length = L) (hw : w.length = R)
    (hloop : K * wordValue v + 1 = 3 ^ L)
    (htail : K * wordValue w = 3 ^ R + b)
    (hb : b < 3 ^ R) (hg : Nat.digits 3 b ⊆ [0, 1]) (t : ℕ) :
    Nat.digits 3 (K * wordValue (tailWord v w t)) ⊆ [0, 1] := by
  rw [identity K L R b v w hv hw hloop htail t, Nat.add_comm]
  have hp : b < 3 ^ (R + L * t) := hb.trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  simpa only [mul_one] using good_add_shifted hp hg
    (by decide +kernel : Nat.digits 3 1 ⊆ [0, 1])

lemma output_length (K L R b : ℕ) (v w : List ℕ)
    (hv : v.length = L) (hw : w.length = R)
    (hloop : K * wordValue v + 1 = 3 ^ L)
    (htail : K * wordValue w = 3 ^ R + b)
    (hb : b < 3 ^ R) (t : ℕ) :
    (Nat.digits 3 (K * wordValue (tailWord v w t))).length = R + L * t + 1 := by
  rw [identity K L R b v w hv hw hloop htail t]
  have hp : b < 3 ^ (R + L * t) := hb.trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hlo := (Nat.lt_digits_length_iff (b := 3) (k := R + L * t) (by decide)
    (3 ^ (R + L * t) + b)).mpr (by omega)
  have hhi := (Nat.digits_length_le_iff (b := 3) (k := R + L * t + 1) (by decide)
    (3 ^ (R + L * t) + b)).mpr (by rw [pow_succ]; omega)
  omega

lemma input_residue (K L R b m : ℕ) (hK : K ≠ 0) (v w : List ℕ)
    (hv : v.length = L) (hw : w.length = R)
    (hloop : K * wordValue v + 1 = 3 ^ L)
    (htail : K * wordValue w = 3 ^ R + b)
    (hperiod : Nat.ModEq (K * m) (3 ^ L) 1) (t : ℕ) :
    Nat.ModEq m (wordValue (tailWord v w t)) (wordValue w) := by
  have hh := (hperiod.pow t).mul_left (3 ^ R) |>.add_right b
  simp only [one_pow, mul_one] at hh
  rw [← pow_mul, ← pow_add, ← identity K L R b v w hv hw hloop htail t, ← htail] at hh
  exact Nat.ModEq.mul_left_cancel' hK hh

lemma input_mod_three (j L R b : ℕ) (hR : 0 < R) (v w : List ℕ)
    (hv : v.length = L) (hw : w.length = R)
    (hloop : 4 ^ j * wordValue v + 1 = 3 ^ L)
    (htail : 4 ^ j * wordValue w = 3 ^ R + b) (t : ℕ) :
    Nat.ModEq 3 (wordValue (tailWord v w t)) (wordValue w) := by
  have hK : 4 ^ j % 3 = 1 := by simp [Nat.pow_mod]
  have hp : 3 ^ R % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega : R ≠ 0))
  have hpt : 3 ^ (R + L * t) % 3 = 0 := by rw [pow_add, Nat.mul_mod, hp]; simp
  have h0 := congrArg (fun n : ℕ => n % 3) htail
  have h1 := congrArg (fun n : ℕ => n % 3) (identity _ _ _ _ _ _ hv hw hloop htail t)
  have h0' : wordValue w % 3 = b % 3 := by simpa [Nat.add_mod, Nat.mul_mod, hK, hp] using h0
  have h1' : wordValue (tailWord v w t) % 3 = b % 3 := by
    simpa [Nat.add_mod, Nat.mul_mod, hK, hpt] using h1
  exact h1'.trans h0'.symm

structure Data where
  j : ℕ
  L : ℕ
  R : ℕ
  b : ℕ
  m : ℕ
  v : List ℕ
  w : List ℕ
  residues : Finset ℕ
  hR : 0 < R
  coprime : Nat.Coprime 3 m
  hv : v.length = L
  hw : w.length = R
  hloop : 4 ^ j * wordValue v + 1 = 3 ^ L
  htail : 4 ^ j * wordValue w = 3 ^ R + b
  hb : b < 3 ^ R
  good_b : Nat.digits 3 b ⊆ [0, 1]
  period : Nat.ModEq (4 ^ j * m) (3 ^ L) 1
  seed_guard : wordValue w % (3 * m) ∈ residues
  guard_closed : ∀ a ∈ residues, (4 * a) % (3 * m) ∈ residues

namespace Data
variable (D : Data)
def input (t : ℕ) := wordValue (tailWord D.v D.w t)

lemma guard (t : ℕ) : D.input t % (3 * D.m) ∈ D.residues := by
  have h3 := input_mod_three D.j D.L D.R D.b D.hR D.v D.w D.hv D.hw D.hloop D.htail t
  have hm := input_residue (4 ^ D.j) D.L D.R D.b D.m (by positivity)
    D.v D.w D.hv D.hw D.hloop D.htail D.period t
  have hh := (Nat.modEq_and_modEq_iff_modEq_mul D.coprime).mp ⟨h3, hm⟩
  change D.input t % (3 * D.m) = wordValue D.w % (3 * D.m) at hh
  rw [hh]
  exact D.seed_guard

/-- The automatically generalized language is a sound necessary rejection
for every invariant satisfying the specified guard and good-length bound. -/
theorem rejected (P : ℕ → Prop) (H : ℕ) (hH : H ≤ D.R + 1)
    (hP : ∀ n, n % (3 * D.m) ∈ D.residues → P n → P (4 * n))
    (hbound : ∀ n, P n → Nat.digits 3 n ⊆ [0, 1] → (Nat.digits 3 n).length < H)
    (t : ℕ) : ¬ P (D.input t) := by
  intro hp
  have hG : ∀ n, n % (3 * D.m) ∈ D.residues → (4 * n) % (3 * D.m) ∈ D.residues := by
    intro n hn
    have hh := D.guard_closed _ hn
    simpa [Nat.mul_mod] using hh
  have hp' := (guarded_iterates P (fun n => n % (3 * D.m) ∈ D.residues)
    hG hP (D.guard t) hp D.j).2
  have hg := output_good (4 ^ D.j) D.L D.R D.b D.v D.w D.hv D.hw D.hloop D.htail D.hb D.good_b t
  have hh := hbound _ hp' hg
  change (Nat.digits 3 (4 ^ D.j * wordValue (tailWord D.v D.w t))).length < H at hh
  rw [output_length (4 ^ D.j) D.L D.R D.b D.v D.w D.hv D.hw D.hloop D.htail D.hb t] at hh
  omega
end Data

/-- Soundness of the complete first-layer exclusion when accepted inputs
have final ternary digit one. Divisibility by four then gives the full guard. -/
theorem full_one_step_rejected (P : ℕ → Prop) (H : ℕ)
    (hlast : ∀ n, P n → n % 3 = 1)
    (hstep : ∀ n, n % 12 = 4 → P n → P (4 * n))
    (hbound : ∀ n, P n → Nat.digits 3 n ⊆ [0, 1] → (Nat.digits 3 n).length < H)
    (n : ℕ) (hdiv : n % 4 = 0)
    (hg : Nat.digits 3 (4 * n) ⊆ [0, 1])
    (hl : H ≤ (Nat.digits 3 (4 * n)).length) : ¬ P n := by
  intro hp
  have hm := hlast n hp
  have hguard : n % 12 = 4 := by omega
  have hh := hbound _ (hstep n hguard hp) hg
  omega

#print axioms full_one_step_rejected
#print axioms identity
#print axioms Data.rejected
end Erdos406PumpedNegative
