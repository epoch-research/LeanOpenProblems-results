import Submission.SquareRootObstruction

/-! Actual square inputs do not make ternary goodness backward-closed under
multiplication by64, even above arbitrary cutoffs and divisibility thresholds.
The examples have odd divisor5; this does not disprove Erdős406. -/
namespace Erdos406SquareBackward
open Erdos406Work

lemma good_affine_square (a b j : ℕ)
    (ha : Nat.digits 3 (a^2) ⊆ [0,1])
    (hab : Nat.digits 3 (2*a*b) ⊆ [0,1])
    (hb : Nat.digits 3 (b^2) ⊆ [0,1])
    (haB : a^2 < 3^18) (habB : 2*a*b < 3^18) (hj : 9 ≤ j) :
    Nat.digits 3 ((a+b*9^j)^2) ⊆ [0,1] := by
  have hp : (3 : ℕ)^18 ≤ 3^(2*j) := Nat.pow_le_pow_right (by decide) (by omega)
  have hg := good_add_shifted (haB.trans_le hp) ha
    (good_add_shifted (habB.trans_le hp) hab hb)
  have he : (a+b*9^j)^2 = a^2+3^(2*j)*(2*a*b+3^(2*j)*b^2) := by
    rw [show (9 : ℕ) = 3^2 by decide, pow_mul]
    ring
  rwa [he]

lemma quotient_mod (a b j r v x : ℕ) (hr : r ≤ 2*j)
    (hx : a+b*9^j = 8*x) (hv : Nat.ModEq (3^r) a (8*v)) :
    Nat.ModEq (3^r) x v := by
  have hd : 3^r ∣ 9^j := by
    rw [show (9 : ℕ) = 3^2 by decide, ← pow_mul]
    exact pow_dvd_pow 3 hr
  have hm : Nat.ModEq (3^r) (8*x) a := by
    rw [← hx]
    exact Nat.add_modEq_left_iff.mpr (dvd_mul_of_dvd_right hd b)
  exact Nat.ModEq.cancel_left_of_coprime
    ((by decide : Nat.Coprime 3 8).pow_left r) (hm.trans hv)

/-- A concrete block certificate supplies unbounded square-input failures.
Its hypotheses are all finite facts about a,b,r,v, not the conjecture. -/
lemma failures_of_blocks (a b r v : ℕ)
    (haPos : 0 < a) (hbPos : 0 < b) (hbOdd : Odd b) (h8 : 8 ∣ a+b)
    (ha5 : 5 ∣ a) (hb5 : 5 ∣ b)
    (ha : Nat.digits 3 (a^2) ⊆ [0,1])
    (hab : Nat.digits 3 (2*a*b) ⊆ [0,1])
    (hb : Nat.digits 3 (b^2) ⊆ [0,1])
    (haB : a^2 < 3^18) (habB : 2*a*b < 3^18)
    (hr : 2 ≤ r ∧ r ≤ 18)
    (hv : Nat.ModEq (3^r) a (8*v))
    (hbad : 3^r ≤ 2*(v^2 % 3^r)) (K B : ℕ) :
    ∃ x : ℕ, B < x^2 ∧ 2^K ∣ x ∧ x^2 % 9 = v^2 % 9 ∧
      Nat.digits 3 (64*x^2) ⊆ [0,1] ∧
      ¬ Nat.digits 3 (x^2) ⊆ [0,1] ∧ 5 ∣ x ∧ ¬ (x^2).isPowerOfTwo := by
  obtain ⟨j, hj, hd⟩ := affine_nine_pow_divisible a b (8*B+9) K hbOdd h8
  have hj9 : 9 ≤ j := by omega
  have h8n : 8 ∣ a+b*9^j := by
    apply dvd_trans (pow_dvd_pow 2 (by omega : 3 ≤ K+3)) hd
  obtain ⟨x, hx⟩ := h8n
  have hxK : 2^K ∣ x := by
    have he : (2 : ℕ)^(K+3) = 8*2^K := by rw [pow_add]; ring
    rw [hx, he] at hd
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < (8 : ℕ)) hd
  have hxB : B < x := by
    have hp : j < 9^j := Nat.lt_pow_self (by decide)
    have hmul : 9^j ≤ b*9^j := Nat.le_mul_of_pos_left _ hbPos
    omega
  have hxSqB : B < x^2 := by nlinarith
  have hm := quotient_mod a b j r v x (by omega) hx hv
  have hmSq := hm.pow 2
  have hm9 : x^2 % 9 = v^2 % 9 := by
    exact hmSq.of_dvd (pow_dvd_pow 3 hr.1)
  have hg : Nat.digits 3 (64*x^2) ⊆ [0,1] := by
    have hh := good_affine_square a b j ha hab hb haB habB hj9
    rw [hx] at hh
    have he : (8*x)^2 = 64*x^2 := by ring
    rwa [he] at hh
  have hng : ¬ Nat.digits 3 (x^2) ⊆ [0,1] := by
    intro hgx
    have hh := (digits_iff_no_carries (x^2)).mp hgx r
    change x^2 % 3^r = v^2 % 3^r at hmSq
    rw [hmSq] at hh
    omega
  have h5 : 5 ∣ x := by
    have hh : 5 ∣ 8*x := by rw [← hx]; exact dvd_add ha5 (dvd_mul_of_dvd_left hb5 _)
    exact (Nat.prime_five.dvd_mul.mp hh).resolve_left (by decide)
  have hnp : ¬ (x^2).isPowerOfTwo := by
    rintro ⟨e, he⟩
    have hd5 : 5 ∣ (2 : ℕ)^e := by rw [← he]; exact h5.trans (dvd_pow_self x (by decide))
    have hh := Nat.prime_five.dvd_of_dvd_pow hd5
    norm_num at hh
  exact ⟨x, hxSqB, hxK, hm9, hg, hng, h5, hnp⟩

/-- Failures occur in the residue1 class modulo9. -/
theorem residue_one_failures (K B : ℕ) :
    ∃ x : ℕ, B < x^2 ∧ 2^K ∣ x ∧ x^2 % 9 = 1 ∧
      Nat.digits 3 (64*x^2) ⊆ [0,1] ∧
      ¬ Nat.digits 3 (x^2) ⊆ [0,1] ∧ 5 ∣ x ∧ ¬ (x^2).isPowerOfTwo := by
  have hh := failures_of_blocks 11645 8035 4 28
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by decide) (by decide) K B
  simpa only [Nat.reducePow, Nat.reduceMod] using hh

/-- Failures also occur in the residue4 class modulo9. -/
theorem residue_four_failures (K B : ℕ) :
    ∃ x : ℕ, B < x^2 ∧ 2^K ∣ x ∧ x^2 % 9 = 4 ∧
      Nat.digits 3 (64*x^2) ⊆ [0,1] ∧
      ¬ Nat.digits 3 (x^2) ⊆ [0,1] ∧ 5 ∣ x ∧ ¬ (x^2).isPowerOfTwo := by
  have hh := failures_of_blocks 8035 11645 9 18227
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide) (by decide)
    (by decide) (by decide) K B
  simpa only [Nat.reducePow, Nat.reduceMod] using hh

/-- Both difficult modulo-nine classes admit actual square counterexamples
above every cutoff, with every prescribed power-of-four divisibility. -/
theorem arbitrarily_late_square_failures (r K B : ℕ) (hr : r = 1 ∨ r = 4) :
    ∃ n : ℕ, B < n ∧ IsSquare n ∧ 4^K ∣ n ∧ n % 9 = r ∧
      Nat.digits 3 (64*n) ⊆ [0,1] ∧ ¬ Nat.digits 3 n ⊆ [0,1] ∧
      5 ∣ n ∧ ¬ n.isPowerOfTwo ∧ ¬ (64*n).isPowerOfTwo := by
  have hx : ∃ x : ℕ, B < x^2 ∧ 2^K ∣ x ∧ x^2 % 9 = r ∧
      Nat.digits 3 (64*x^2) ⊆ [0,1] ∧
      ¬ Nat.digits 3 (x^2) ⊆ [0,1] ∧ 5 ∣ x ∧ ¬ (x^2).isPowerOfTwo := by
    rcases hr with rfl | rfl
    · exact residue_one_failures K B
    · exact residue_four_failures K B
  obtain ⟨x, hB, hK, hx9, hg, hng, h5, hnp⟩ := hx
  have h4 : 4^K ∣ x^2 := by
    have hh := pow_dvd_pow_of_dvd hK 2
    have he : ((2 : ℕ)^K)^2 = 4^K := by
      rw [← pow_mul, Nat.mul_comm K 2, pow_mul]
      rfl
    rwa [he] at hh
  have hn5 : 5 ∣ x^2 := h5.trans (dvd_pow_self _ (by decide))
  have hnp64 : ¬ (64*x^2).isPowerOfTwo := by
    rintro ⟨e, he⟩
    have hh : 5 ∣ (2 : ℕ)^e := by rw [← he]; exact dvd_mul_of_dvd_right hn5 _
    have h2 := Nat.prime_five.dvd_of_dvd_pow hh
    norm_num at h2
  exact ⟨x^2, hB, ⟨x, pow_two x⟩, h4, hx9, hg, hng, hn5, hnp, hnp64⟩

/-- This negates only a proposed square-guarded descent, not Erdős406. -/
theorem square_guarded_backward_goodness_false (r K B : ℕ)
    (hr : r = 1 ∨ r = 4) :
    ¬ (∀ n : ℕ, B ≤ n → IsSquare n → 4^K ∣ n → n % 9 = r →
      Nat.digits 3 (64*n) ⊆ [0,1] → Nat.digits 3 n ⊆ [0,1]) := by
  intro h
  obtain ⟨n, hB, hs, hd, hm, hg, hng, _, _, _⟩ :=
    arbitrarily_late_square_failures r K B hr
  exact hng (h n hB.le hs hd hm hg)

#print axioms residue_one_failures
#print axioms residue_four_failures
#print axioms arbitrarily_late_square_failures
#print axioms square_guarded_backward_goodness_false
end Erdos406SquareBackward
