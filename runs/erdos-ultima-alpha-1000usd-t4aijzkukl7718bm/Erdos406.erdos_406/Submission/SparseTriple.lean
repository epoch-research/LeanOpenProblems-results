import Submission.AffineCertificates

/-! A structural characterization of integers n for which n, 4n and 256n
all have ternary digits zero or one. This does not settle Erdős 406. -/

namespace Erdos406SparseTriple
open Erdos406AffineCertificate

abbrev Good (n : ℕ) : Prop := Nat.digits 3 n ⊆ [0, 1]
def Triple (n : ℕ) : Prop := Good n ∧ Good (4 * n) ∧ Good (256 * n)

inductive SixSpaced : ℕ → Prop
  | zero : SixSpaced 0
  | shift {n : ℕ} : SixSpaced n → SixSpaced (3 * n)
  | one {n : ℕ} : SixSpaced n → SixSpaced (729 * n + 1)

lemma good_ofDigits {w : List ℕ} (hw : w ⊆ [0, 1]) : Good (Nat.ofDigits 3 w) := by
  induction w with
  | nil => simp [Nat.ofDigits]
  | cons d w ih =>
    have hd := hw (List.mem_cons_self ..)
    have ht : w ⊆ [0, 1] := fun a ha => hw (List.mem_cons_of_mem _ ha)
    have h := good_three_mul_add (ih ht) hd
    simpa only [Nat.ofDigits_cons, Nat.add_comm] using h

lemma good_mod_pow {n : ℕ} (h : Good n) (k : ℕ) : Good (n % 3 ^ k) := by
  rw [Nat.self_mod_pow_eq_ofDigits_take k n (by decide : 2 ≤ 3)]
  exact good_ofDigits (fun a ha => h (List.mem_of_mem_take ha))

lemma good_div_pow {n : ℕ} (h : Good n) (k : ℕ) : Good (n / 3 ^ k) := by
  induction k with
  | zero => simpa using h
  | succ k ih => simpa only [Nat.div_div_eq_div_mul, ← pow_succ] using good_div_three ih

lemma good_prefix {k n a : ℕ} (hn : Good n) (ha : Good a) (hlt : a < 3 ^ k) :
    Good (3 ^ k * n + a) := by
  induction k generalizing a with
  | zero =>
    have : a = 0 := by simpa using hlt
    simpa [this] using hn
  | succ k ih =>
    have hq : a / 3 < 3 ^ k := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr
      simpa only [pow_succ] using hlt
    have hd : a % 3 ∈ ([0, 1] : List ℕ) := by
      by_cases hz : a = 0
      · simp [hz]
      · exact (by simpa using good_unit_mod_three (by omega) ha)
    have hp := good_three_mul_add (ih (good_div_three ha) hq) hd
    have he : 3 ^ (k + 1) * n + a = 3 * (3 ^ k * n + a / 3) + a % 3 := by
      rw [pow_succ]
      calc
        _ = 3 * (3 ^ k * n) + a := by ring
        _ = _ := by omega
    rw [he]
    exact hp

abbrev LowGood (k n : ℕ) : Prop := ∀ i : Fin k, n / 3 ^ i.val % 3 < 2

lemma lowGood_of_good {n : ℕ} (hn : Good n) (k : ℕ) : LowGood k n := by
  intro i
  have hh := good_div_pow hn i.val
  by_cases hz : n / 3 ^ i.val = 0
  · simp [hz]
  · have hu := good_unit_mod_three (Nat.pos_of_ne_zero hz) hh
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unit_triple_prefix_check :
    ∀ r : Fin 2187, r.val % 3 = 1 →
      LowGood 7 r.val → LowGood 7 (4 * r.val % 2187) → LowGood 7 (256 * r.val % 2187) →
      r.val % 729 = 1 := by decide

lemma unit_triple_prefix {n : ℕ} (hn : Triple n) (hu : n % 3 = 1) : n % 729 = 1 := by
  obtain ⟨h0, h4, h256⟩ := hn
  have h0' := good_mod_pow h0 7
  have h4' := good_mod_pow h4 7
  have h256' := good_mod_pow h256 7
  have hu' : n % 2187 % 3 = 1 := by omega
  have hc := unit_triple_prefix_check ⟨n % 2187, Nat.mod_lt _ (by decide)⟩ hu'
    (lowGood_of_good (by simpa using h0') 7)
    (lowGood_of_good (by simpa only [Nat.mul_mod, Nat.mod_mod, Nat.reducePow] using h4') 7)
    (lowGood_of_good (by simpa only [Nat.mul_mod, Nat.mod_mod, Nat.reducePow] using h256') 7)
  dsimp only at hc
  omega

lemma triple_div_three {n : ℕ} (hn : Triple n) (hm : n % 3 = 0) : Triple (n / 3) := by
  obtain ⟨h0, h4, h256⟩ := hn
  have he4 : 4 * n / 3 = 4 * (n / 3) := by omega
  have he256 : 256 * n / 3 = 256 * (n / 3) := by omega
  exact ⟨good_div_three h0, by simpa only [he4] using good_div_three h4,
    by simpa only [he256] using good_div_three h256⟩

lemma triple_div_729 {n : ℕ} (hn : Triple n) (hm : n % 729 = 1) : Triple (n / 729) := by
  obtain ⟨h0, h4, h256⟩ := hn
  have he4 : 4 * n / 729 = 4 * (n / 729) := by omega
  have he256 : 256 * n / 729 = 256 * (n / 729) := by omega
  exact ⟨good_div_pow h0 6, by simpa only [Nat.reducePow, he4] using good_div_pow h4 6,
    by simpa only [Nat.reducePow, he256] using good_div_pow h256 6⟩

lemma triple_implies_sixSpaced {n : ℕ} (hn : Triple n) : SixSpaced n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n; exact SixSpaced.zero
    rcases good_unit_mod_three (by omega) hn.1 with h0 | h1
    · have hh := ih (n / 3) (Nat.div_lt_self (by omega) (by decide)) (triple_div_three hn h0)
      have he : 3 * (n / 3) = n := by omega
      simpa only [he] using SixSpaced.shift hh
    · have hm := unit_triple_prefix hn h1
      have hh := ih (n / 729) (Nat.div_lt_self (by omega) (by decide)) (triple_div_729 hn hm)
      have he : 729 * (n / 729) + 1 = n := by omega
      simpa only [he] using SixSpaced.one hh

lemma sixSpaced_implies_triple {n : ℕ} (hn : SixSpaced n) : Triple n := by
  induction hn with
  | zero => simp [Triple]
  | @shift n hn ih =>
    obtain ⟨h0, h4, h256⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · simpa using good_three_mul_add h0 (by simp : 0 ∈ ([0, 1] : List ℕ))
    · simpa only [add_zero, mul_left_comm] using
        good_three_mul_add h4 (by simp : 0 ∈ ([0, 1] : List ℕ))
    · simpa only [add_zero, mul_left_comm] using
        good_three_mul_add h256 (by simp : 0 ∈ ([0, 1] : List ℕ))
  | @one n hn ih =>
    obtain ⟨h0, h4, h256⟩ := ih
    have hh0 := good_prefix (k := 6) h0 (by norm_num [Good, Nat.digits_of_two_le_of_pos] : Good 1) (by decide)
    have hh4 := good_prefix (k := 6) h4 (by norm_num [Good, Nat.digits_of_two_le_of_pos] : Good 4) (by decide)
    have hh256 := good_prefix (k := 6) h256 (by norm_num [Good, Nat.digits_of_two_le_of_pos] : Good 256) (by decide)
    refine ⟨hh0, ?_, ?_⟩
    · rw [show 4 * (729 * n + 1) = 3 ^ 6 * (4 * n) + 4 by norm_num; ring]
      exact hh4
    · rw [show 256 * (729 * n + 1) = 3 ^ 6 * (256 * n) + 256 by norm_num; ring]
      exact hh256

theorem triple_iff_sixSpaced (n : ℕ) : Triple n ↔ SixSpaced n :=
  ⟨triple_implies_sixSpaced, sixSpaced_implies_triple⟩

#print axioms triple_iff_sixSpaced
end Erdos406SparseTriple
