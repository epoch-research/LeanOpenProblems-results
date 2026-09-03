import Submission.AlternatingPredecessorFamily

/-! Uniform arithmetic identities behind the regular negative families used
in certificate searches. No multiplication-closed invariant is supplied. -/
namespace Erdos406RegularPredecessor
open Erdos406Work

def wordValue (w : List ℕ) : ℕ := Nat.ofDigits 3 w.reverse

def tailWord (v w : List ℕ) : ℕ → List ℕ
  | 0 => w
  | t + 1 => v ++ tailWord v w t

lemma wordValue_append (u v : List ℕ) :
    wordValue (u ++ v) = wordValue v + 3 ^ v.length * wordValue u := by
  simp [wordValue, List.reverse_append, Nat.ofDigits_append]

lemma tailWord_length (v w : List ℕ) (L : ℕ)
    (hv : v.length = L) (hw : w.length = L) (t : ℕ) :
    (tailWord v w t).length = (t + 1) * L := by
  induction t with
  | zero => simpa [tailWord] using hw
  | succ t ih => rw [tailWord, List.length_append, hv, ih]; ring

lemma block_power (L t : ℕ) : 3 ^ ((t + 1) * L) = (3 ^ L) ^ (t + 1) := by
  rw [Nat.mul_comm (t + 1) L, pow_mul]

/-- The loop and terminal block equations imply the identity for every
number of repetitions, not merely the tested sample words. -/
lemma scaled_tail_identity (K C L : ℕ) (v w : List ℕ)
    (hv : v.length = L) (hw : w.length = L)
    (hloop : K * wordValue v + C = C * 3 ^ L)
    (htail : K * wordValue w = C * 3 ^ L + 13) (t : ℕ) :
    K * wordValue (tailWord v w t) = C * (3 ^ L) ^ (t + 1) + 13 := by
  induction t with
  | zero => simpa [tailWord] using htail
  | succ t ih =>
    rw [tailWord, wordValue_append, tailWord_length v w L hv hw, block_power]
    rw [show (3 ^ L) ^ (t + 1 + 1) = (3 ^ L) ^ (t + 1) * 3 ^ L from pow_succ _ _]
    have hh := congrArg (fun n : ℕ => (3 ^ L) ^ (t + 1) * n) hloop
    nlinarith

lemma scaled_word_identity (K C L : ℕ) (u v w : List ℕ)
    (hv : v.length = L) (hw : w.length = L)
    (hprefix : K * wordValue u + C = 243)
    (hloop : K * wordValue v + C = C * 3 ^ L)
    (htail : K * wordValue w = C * 3 ^ L + 13) (t : ℕ) :
    K * wordValue (u ++ tailWord v w t) = 243 * (3 ^ L) ^ (t + 1) + 13 := by
  rw [wordValue_append, tailWord_length v w L hv hw, block_power]
  have hs := scaled_tail_identity K C L v w hv hw hloop htail t
  have hp := congrArg (fun n : ℕ => (3 ^ L) ^ (t + 1) * n) hprefix
  nlinarith

lemma scaled_word_identity_three (K C L : ℕ) (u v w : List ℕ)
    (hv : v.length = L) (hw : w.length = L)
    (hprefix : K * wordValue u + C = 243)
    (hloop : K * wordValue v + C = C * 3 ^ L)
    (htail : K * wordValue w = C * 3 ^ L + 13) (t : ℕ) :
    K * wordValue (u ++ tailWord v w t) = 3 ^ (L * (t + 1) + 5) + 13 := by
  have he : 3 ^ (L * (t + 1) + 5) = 243 * (3 ^ L) ^ (t + 1) := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  rw [scaled_word_identity K C L u v w hv hw hprefix hloop htail t, he]

lemma scaled_word_good (K C L : ℕ) (u v w : List ℕ)
    (hv : v.length = L) (hw : w.length = L)
    (hprefix : K * wordValue u + C = 243)
    (hloop : K * wordValue v + C = C * 3 ^ L)
    (htail : K * wordValue w = C * 3 ^ L + 13) (t : ℕ) :
    Nat.digits 3 (K * wordValue (u ++ tailWord v w t)) ⊆ [0, 1] := by
  rw [scaled_word_identity_three K C L u v w hv hw hprefix hloop htail t]
  apply good_add_top_power (by decide +kernel : Nat.digits 3 13 ⊆ [0, 1])
  have hh : (Nat.digits 3 13).length = 3 := by decide +kernel
  rw [hh]
  omega

lemma scaled_word_length (K C L : ℕ) (u v w : List ℕ)
    (hv : v.length = L) (hw : w.length = L)
    (hprefix : K * wordValue u + C = 243)
    (hloop : K * wordValue v + C = C * 3 ^ L)
    (htail : K * wordValue w = C * 3 ^ L + 13) (t : ℕ) :
    (Nat.digits 3 (K * wordValue (u ++ tailWord v w t))).length = L * (t + 1) + 6 := by
  rw [scaled_word_identity_three K C L u v w hv hw hprefix hloop htail t,
    four_digit_formula (by omega : 3 ≤ L * (t + 1) + 5)]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

lemma scaled_word_mod_three (K C L : ℕ) (u v w : List ℕ)
    (hv : v.length = L) (hw : w.length = L)
    (hprefix : K * wordValue u + C = 243)
    (hloop : K * wordValue v + C = C * 3 ^ L)
    (htail : K * wordValue w = C * 3 ^ L + 13)
    (hK : K % 3 = 1) (t : ℕ) :
    wordValue (u ++ tailWord v w t) % 3 = 1 := by
  have hh := congrArg (fun n : ℕ => n % 3)
    (scaled_word_identity K C L u v w hv hw hprefix hloop htail t)
  simpa [Nat.add_mod, Nat.mul_mod, hK] using hh

lemma scaled_word_residue (K C L m r : ℕ) (hK : K ≠ 0)
    (u v w : List ℕ) (hv : v.length = L) (hw : w.length = L)
    (hprefix : K * wordValue u + C = 243)
    (hloop : K * wordValue v + C = C * 3 ^ L)
    (htail : K * wordValue w = C * 3 ^ L + 13)
    (hbase : K * r = 256) (hperiod : Nat.ModEq (K * m) (3 ^ L) 1) (t : ℕ) :
    Nat.ModEq m (wordValue (u ++ tailWord v w t)) r := by
  have hh := (hperiod.pow (t + 1)).mul_left 243 |>.add_right 13
  simp only [one_pow, mul_one] at hh
  rw [← scaled_word_identity K C L u v w hv hw hprefix hloop htail t] at hh
  norm_num at hh
  rw [← hbase] at hh
  exact Nat.ModEq.mul_left_cancel' hK hh

/-- Guarded closure propagates through any fixed number of fourfold steps. -/
lemma guarded_iterates (P G : ℕ → Prop)
    (hG : ∀ n, G n → G (4 * n))
    (hP : ∀ n, G n → P n → P (4 * n))
    {n : ℕ} (hg : G n) (hp : P n) (j : ℕ) : G (4 ^ j * n) ∧ P (4 ^ j * n) := by
  induction j with
  | zero => simpa using And.intro hg hp
  | succ j ih =>
    have hh := And.intro (hG _ ih.1) (hP _ ih.1 ih.2)
    simpa only [pow_succ', mul_assoc] using hh

/-- The regular family is necessarily rejected by any invariant with the
stated bound and guard assumptions. All assumptions remain explicit. -/
theorem family_rejected (j C L H : ℕ) (u v w : List ℕ)
    (hv : v.length = L) (hw : w.length = L)
    (hprefix : 4 ^ j * wordValue u + C = 243)
    (hloop : 4 ^ j * wordValue v + C = C * 3 ^ L)
    (htail : 4 ^ j * wordValue w = C * 3 ^ L + 13)
    (P G : ℕ → Prop) (hG : ∀ n, G n → G (4 * n))
    (hP : ∀ n, G n → P n → P (4 * n))
    (hbound : ∀ n, P n → Nat.digits 3 n ⊆ [0, 1] → (Nat.digits 3 n).length < H)
    (t : ℕ) (hg : G (wordValue (u ++ tailWord v w t)))
    (hlong : H ≤ L * (t + 1) + 6) : ¬ P (wordValue (u ++ tailWord v w t)) := by
  intro hp
  have hp' := (guarded_iterates P G hG hP hg hp j).2
  have hh := hbound _ hp' (scaled_word_good (4 ^ j) C L u v w hv hw hprefix hloop htail t)
  rw [scaled_word_length (4 ^ j) C L u v w hv hw hprefix hloop htail t] at hh
  omega

#print axioms scaled_word_identity
#print axioms scaled_word_residue
#print axioms family_rejected
end Erdos406RegularPredecessor
