import Submission.NewmanTotallyReal

/-! An explicit reduction of large good powers to irreducible factors with
large value at three. The factor bound used in the converse is a hypothesis,
not a result proved here, so this file does not settle Erdős 406. -/
namespace Erdos406FactorBridge
open Polynomial Erdos406Cyclotomic Erdos406FactorParity Erdos406FactorCount

lemma digitPoly_isMonicOfDegree (w : List ℕ) (hne : w ≠ [])
    (hlast : w.getLast hne = 1) : (digitPoly w).IsMonicOfDegree (w.length - 1) := by
  induction w with
  | nil => contradiction
  | cons a w ih =>
    cases w with
    | nil =>
      simp only [List.getLast_singleton] at hlast
      subst a
      simpa [digitPoly, Nat.ofDigits] using (isMonicOfDegree_one (R := ℤ))
    | cons b w =>
      have hh := ih (by simp) (by simpa only [List.getLast_cons] using hlast)
      have hm := (isMonicOfDegree_X ℤ).mul hh
      have ha : (C (a : ℤ)).natDegree < 1 + (b :: w).length - 1 := by simp
      have hm' : (X * digitPoly (b :: w)).IsMonicOfDegree
          (1 + (b :: w).length - 1) := by simpa only [List.length_cons] using hm
      have hfinal := IsMonicOfDegree.add_left ha hm'
      simpa [digitPoly, Nat.ofDigits] using hfinal

lemma candidate_digitPoly_isMonicOfDegree (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) :
    (digitPoly (Nat.digits 3 (2 ^ k))).IsMonicOfDegree
      ((Nat.digits 3 (2 ^ k)).length - 1) := by
  have hn : 2 ^ k ≠ 0 := by positivity
  have hne : Nat.digits 3 (2 ^ k) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  apply digitPoly_isMonicOfDegree _ hne
  have hh := hg (List.getLast_mem hne)
  have hlast := Nat.getLast_digit_ne_zero 3 hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  exact hh.resolve_left hlast

/-- Monic polynomials over the integers have an exact list factorization into
monic irreducibles, with no residual unit. -/
lemma monic_irreducible_list (P : ℤ[X]) (hP : P.Monic) :
    ∃ L : List ℤ[X], (∀ Q ∈ L, Q.Monic ∧ Irreducible Q) ∧ L.prod = P := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases h1 : P = 1
    · exact ⟨[], by simp, by simpa using h1.symm⟩
    by_cases hI : Irreducible P
    · exact ⟨[P], by simpa using And.intro hP hI, by simp⟩
    have hh := mt (irreducible_of_monic hP h1).mpr hI
    push_neg at hh
    obtain ⟨A, B, hA, hB, he, hA1, hB1⟩ := hh
    have hda : 0 < A.natDegree := hA.natDegree_pos_of_not_isUnit (by simpa [hA.isUnit_iff])
    have hdb : 0 < B.natDegree := hB.natDegree_pos_of_not_isUnit (by simpa [hB.isUnit_iff])
    have hd : A.natDegree + B.natDegree = n := by rw [← hA.natDegree_mul hB, he, hn]
    obtain ⟨LA, hLA, heA⟩ := ih A.natDegree (by omega) A hA rfl
    obtain ⟨LB, hLB, heB⟩ := ih B.natDegree (by omega) B hB rfl
    refine ⟨LA ++ LB, ?_, ?_⟩
    · intro Q hQ
      rcases List.mem_append.mp hQ with ha | hb
      · exact hLA Q ha
      · exact hLB Q hb
    · rw [List.prod_append, heA, heB, he]

lemma list_eval_square_bound (L : List ℤ[X])
    (hL : ∀ Q ∈ L, (Q.eval 3) ^ 2 ≤ 2 * (8 : ℤ) ^ Q.natDegree) :
    (L.prod.eval 3) ^ 2 ≤ (2 : ℤ) ^ L.length * 8 ^ (L.map natDegree).sum := by
  induction L with
  | nil => simp
  | cons Q L ih =>
    have hq := hL Q (by simp)
    have ht := ih (fun A hA => hL A (by simp [hA]))
    simp only [List.prod_cons, eval_mul, mul_pow, List.length_cons, List.map_cons,
      List.sum_cons]
    calc
      _ ≤ (2 * (8 : ℤ) ^ Q.natDegree) *
          (2 ^ L.length * 8 ^ (L.map natDegree).sum) :=
        mul_le_mul hq ht (sq_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ, pow_add]; ring

/-- A per-factor additive allowance of one in the exponent is enough, because
there are at most logarithmically many irreducible factors. This allowance
includes X+1 automatically. The per-factor inequality remains a hypothesis. -/
theorem candidate_bound_of_factor_bound (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1])
    (hgap : ∀ Q : ℤ[X], Q.Monic → Irreducible Q →
      Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) →
      (Q.eval 3) ^ 2 ≤ 2 * (8 : ℤ) ^ Q.natDegree) :
    (digitPoly (Nat.digits 3 (2 ^ k))).natDegree ≤ 28 ∧ k ≤ 56 := by
  have hm := candidate_digitPoly_isMonicOfDegree k hg
  obtain ⟨L, hL, he⟩ := monic_irreducible_list _ hm.monic
  let D := (digitPoly (Nat.digits 3 (2 ^ k))).natDegree
  have hdeg : (L.map natDegree).sum = D := by
    have hh := natDegree_multiset_prod_of_monic (L : Multiset ℤ[X])
      (show ∀ Q ∈ (L : Multiset ℤ[X]), Q.Monic from by simpa using fun Q hQ => (hL Q hQ).1)
    simpa [he, D] using hh.symm
  have hval : L.prod.eval 3 = (2 : ℤ) ^ k := by
    rw [he, digitPoly_eval_three]
    norm_cast
  have hb := list_eval_square_bound L (fun Q hQ =>
    hgap Q (hL Q hQ).1 (hL Q hQ).2 (by rw [← he]; exact List.dvd_prod hQ))
  rw [hval, hdeg, ← pow_mul] at hb
  have hbN : 2 ^ (2 * k) ≤ 2 ^ L.length * 8 ^ D := by
    rw [Nat.mul_comm k 2] at hb
    exact_mod_cast hb
  have hgapN : 2 * k ≤ 3 * D + L.length := by
    have hh : 2 ^ L.length * 8 ^ D = 2 ^ (3 * D + L.length) := by
      rw [pow_add, pow_mul]
      norm_num
      ring
    rw [hh] at hbN
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbN
  have hlenpos : 0 < (Nat.digits 3 (2 ^ k)).length := by
    apply List.length_pos_iff.mpr
    exact Nat.digits_ne_nil_iff_ne_zero.mpr (by positivity)
  have hlen : (Nat.digits 3 (2 ^ k)).length = D + 1 := by
    have hh := hm.natDegree_eq
    dsimp [D]
    omega
  have hc := candidate_factor_count_bound k hg L
    (fun Q hQ => ⟨(hL Q hQ).1,
      (hL Q hQ).1.natDegree_pos_of_not_isUnit (hL Q hQ).2.not_isUnit⟩) he
  rw [hlen] at hc
  have hsize : 3 ^ D ≤ 2 ^ k := by
    have hh := Nat.base_pow_length_digits_le 3 (2 ^ k) (by decide) (by positivity)
    rw [hlen, pow_succ] at hh
    omega
  exact Erdos406Newman.degree_bound_of_factor_gap D k L.length hsize hgapN hc

/-- An unconditional reduction: any good power beyond exponent56 forces a
monic irreducible divisor violating the soft factor bound. This does not
assert that such divisors are impossible. -/
theorem large_candidate_has_bad_factor (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (hk : 56 < k) :
    ∃ Q : ℤ[X], Q.Monic ∧ Irreducible Q ∧
      Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) ∧
      2 * (8 : ℤ) ^ Q.natDegree < (Q.eval 3) ^ 2 := by
  by_contra hh
  push_neg at hh
  have hb := candidate_bound_of_factor_bound k hg hh
  omega

/-- Conditional finiteness, with the unproved per-factor hypothesis explicit. -/
theorem finite_of_factor_bound
    (hgap : ∀ k : ℕ, Nat.digits 3 (2 ^ k) ⊆ [0, 1] →
      ∀ Q : ℤ[X], Q.Monic → Irreducible Q →
        Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) →
        (Q.eval 3) ^ 2 ≤ 2 * (8 : ℤ) ^ Q.natDegree) :
    { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] }.Finite := by
  apply ((Finset.range 57).finite_toSet.image (fun k : ℕ => 2 ^ k)).subset
  rintro n ⟨⟨k, rfl⟩, hg⟩
  refine ⟨k, ?_, rfl⟩
  have hb := (candidate_bound_of_factor_bound k hg (hgap k hg)).2
  simpa using (show k < 57 by omega)

#print axioms candidate_bound_of_factor_bound
#print axioms large_candidate_has_bad_factor
#print axioms finite_of_factor_bound
end Erdos406FactorBridge
