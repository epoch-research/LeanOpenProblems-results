import Submission.NewmanFactorBridge

/-! Restrictions from evaluation at minus one. These bound the number of
factors, not their degrees, and do not settle Erdős 406. -/
namespace Erdos406MinusOne
open Polynomial Erdos406Cyclotomic Erdos406FactorParity Erdos406FactorCount
  Erdos406FactorBridge

lemma candidate_factor_eval_neg_one_four_dvd (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hdeg : 0 < Q.natDegree) :
    (4 : ℤ) ∣ Q.eval (-1) := by
  obtain ⟨t, ht, _, hval⟩ := candidate_factor_four_exponent_positive k hg Q hQ hd hdeg
  have hthree : (4 : ℤ) ∣ Q.eval 3 := by
    rw [hval]
    exact dvd_pow_self 4 (by omega)
  have hdiff : (4 : ℤ) ∣ Q.eval 3 - Q.eval (-1) := by
    simpa using sub_dvd_eval_sub (3 : ℤ) (-1) Q
  have hh := dvd_sub hthree hdiff
  convert hh using 1
  ring

lemma list_eval_neg_one_four_dvd (L : List ℤ[X])
    (hL : ∀ Q ∈ L, (4 : ℤ) ∣ Q.eval (-1)) :
    (4 : ℤ) ^ L.length ∣ L.prod.eval (-1) := by
  induction L with
  | nil => simp
  | cons Q L ih =>
    simp only [List.length_cons, List.prod_cons, eval_mul, pow_succ']
    exact mul_dvd_mul (hL Q (by simp)) (ih (fun R hR => hL R (by simp [hR])))

lemma digitPoly_eval_neg_one_abs_le_sum (w : List ℕ) :
    |(digitPoly w).eval (-1)| ≤ (w.sum : ℤ) := by
  induction w with
  | nil => simp [digitPoly, Nat.ofDigits]
  | cons d w ih =>
    have he : (digitPoly (d :: w)).eval (-1) = (d : ℤ) - (digitPoly w).eval (-1) := by
      simp [digitPoly, Nat.ofDigits]; ring
    rw [he, List.sum_cons, Nat.cast_add]
    calc
      _ ≤ |(d : ℤ)| + |(digitPoly w).eval (-1)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (d : ℤ) (-((digitPoly w).eval (-1)))
      _ ≤ _ := by simpa using add_le_add_left ih (d : ℤ)

/-- If there is no zero at minus one, every nonconstant factor consumes
at least two powers of two in the alternating digit sum. -/
theorem candidate_factor_count_neg_one (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (L : List ℤ[X])
    (hL : ∀ Q ∈ L, Q.Monic ∧ 0 < Q.natDegree)
    (hprod : L.prod = digitPoly (Nat.digits 3 (2 ^ k)))
    (hn : (digitPoly (Nat.digits 3 (2 ^ k))).eval (-1) ≠ 0) :
    4 ^ L.length ≤ (Nat.digits 3 (2 ^ k)).sum := by
  have hd : (4 : ℤ) ^ L.length ∣ (digitPoly (Nat.digits 3 (2 ^ k))).eval (-1) := by
    rw [← hprod]
    apply list_eval_neg_one_four_dvd L
    intro Q hQ
    exact candidate_factor_eval_neg_one_four_dvd k hg Q (hL Q hQ).1
      (by rw [← hprod]; exact List.dvd_prod hQ) (hL Q hQ).2
  have habs : (4 : ℤ) ^ L.length ≤ |(digitPoly (Nat.digits 3 (2 ^ k))).eval (-1)| := by
    exact Int.le_abs_of_dvd hn hd
  have hh := habs.trans (digitPoly_eval_neg_one_abs_le_sum _)
  exact_mod_cast hh

/-- A candidate with positive exponent and digit sum not divisible by four
has an irreducible digit polynomial. This leaves its degree unbounded. -/
theorem candidate_irreducible_of_digit_sum_not_four_dvd (k : ℕ) (hk : 0 < k)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1])
    (hfour : ¬ 4 ∣ (Nat.digits 3 (2 ^ k)).sum) :
    Irreducible (digitPoly (Nat.digits 3 (2 ^ k))) := by
  let P := digitPoly (Nat.digits 3 (2 ^ k))
  change Irreducible P
  have hP : P.Monic := (candidate_digitPoly_isMonicOfDegree k hg).monic
  have hP1 : P ≠ 1 := by
    intro hp
    have hv : P.eval 3 = (2 : ℤ) ^ k := by
      dsimp [P]
      rw [digitPoly_eval_three]
      norm_cast
    rw [hp, eval_one] at hv
    have hgt : 1 < (2 : ℤ) ^ k := one_lt_pow₀ (by norm_num) (by omega)
    omega
  apply (irreducible_of_monic hP hP1).mpr
  intro A B hA hB he
  by_cases hA1 : A = 1
  · exact Or.inl hA1
  by_cases hB1 : B = 1
  · exact Or.inr hB1
  have hAd : 0 < A.natDegree := hA.natDegree_pos_of_not_isUnit (by simpa [hA.isUnit_iff])
  have hBd : 0 < B.natDegree := hB.natDegree_pos_of_not_isUnit (by simpa [hB.isUnit_iff])
  have hAa : A ∣ P := by rw [← he]; exact dvd_mul_right _ _
  have hBb : B ∣ P := by rw [← he]; exact dvd_mul_left _ _
  have h2A := (candidate_factor_eval_one_even k hg A hA hAa hAd).1
  have h2B := (candidate_factor_eval_one_even k hg B hB hBb hBd).1
  have hfourZ : (4 : ℤ) ∣ P.eval 1 := by
    rw [← he, eval_mul]
    exact mul_dvd_mul h2A h2B
  have hs : P.eval 1 = ((Nat.digits 3 (2 ^ k)).sum : ℤ) :=
    Erdos406Newman.eval_one_digitPoly _
  rw [hs] at hfourZ
  exact (hfour (by exact_mod_cast hfourZ)).elim

/-- A six-one candidate, if one exists, is a genuinely high-degree
irreducible case; its alternating digit sum is plus or minus four. -/
theorem six_ones_candidate_constraints (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1])
    (hs : (Nat.digits 3 (2 ^ k)).sum = 6) :
    Irreducible (digitPoly (Nat.digits 3 (2 ^ k))) ∧
      5 ≤ (digitPoly (Nat.digits 3 (2 ^ k))).natDegree ∧
      ((digitPoly (Nat.digits 3 (2 ^ k))).eval (-1) = 4 ∨
        (digitPoly (Nat.digits 3 (2 ^ k))).eval (-1) = -4) := by
  have hk : 0 < k := by
    by_contra hh
    have hz : k = 0 := by omega
    simp [hz] at hs
  have hI := candidate_irreducible_of_digit_sum_not_four_dvd k hk hg (by rw [hs]; decide)
  have hP := candidate_digitPoly_isMonicOfDegree k hg
  have hlen := Erdos406Newman.sum_le_length hg
  rw [hs] at hlen
  have hd : 5 ≤ (digitPoly (Nat.digits 3 (2 ^ k))).natDegree := by
    rw [hP.natDegree_eq]
    omega
  have hn : (digitPoly (Nat.digits 3 (2 ^ k))).eval (-1) ≠ 0 :=
    hI.not_isRoot_of_natDegree_ne_one (by omega)
  have hfour := candidate_factor_eval_neg_one_four_dvd k hg _ hP.monic
    (dvd_refl _) (by omega)
  have hb := digitPoly_eval_neg_one_abs_le_sum (Nat.digits 3 (2 ^ k))
  rw [hs] at hb
  norm_num only [Nat.cast_ofNat] at hb
  have hh := abs_le.mp hb
  obtain ⟨t, ht⟩ := hfour
  exact ⟨hI, hd, by omega⟩

#print axioms candidate_factor_eval_neg_one_four_dvd
#print axioms candidate_factor_count_neg_one
#print axioms candidate_irreducible_of_digit_sum_not_four_dvd
#print axioms six_ones_candidate_constraints
end Erdos406MinusOne
