import Submission.NewmanQuarticTrace

/-! A uniform factor gap up to any fixed constant, or outside any fixed degree
range, suffices for Erdős 406. The gap is an explicit hypothesis throughout;
this file does not prove it and does not settle the original conjecture. -/
namespace Erdos406EventualFactorBound
open scoped Topology
open Polynomial Filter Erdos406Cyclotomic Erdos406FactorParity
  Erdos406FactorCount Erdos406FactorBridge Erdos406QuarticTrace

lemma exponential_dominates_polynomial (c : ℕ) :
    ∃ N : ℕ, ∀ D ≥ N, 8 ^ D * (D + 1) ^ c < 9 ^ D := by
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one c
    (by norm_num : (0 : ℝ) ≤ 8 / 9) (by norm_num : (8 / 9 : ℝ) < 1)).comp
      (tendsto_add_atTop_nat 1)
  have ht' : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ c * (8 / 9 : ℝ) ^ n)
      atTop (𝓝 0) := by
    have hh : Tendsto
        (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ c * (8 / 9 : ℝ) ^ (n + 1)) * (9 / 8))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, zero_mul] using ht.mul_const (9 / 8 : ℝ)
    apply hh.congr'
    filter_upwards [] with n
    rw [pow_succ]
    ring
  obtain ⟨N, hN⟩ := (ht'.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).exists_forall_of_atTop
  refine ⟨N, fun D hD => ?_⟩
  have hh := hN D hD
  rw [div_pow, ← mul_div_assoc, div_lt_one (by positivity : (0 : ℝ) < 9 ^ D)] at hh
  have hr : (8 : ℝ) ^ D * ((D + 1 : ℕ) : ℝ) ^ c < 9 ^ D := by nlinarith only [hh]
  exact_mod_cast hr

lemma list_eval_square_bound_constant (L : List ℤ[X]) (c : ℕ)
    (hL : ∀ Q ∈ L, (Q.eval 3) ^ 2 ≤ (2 : ℤ) ^ c * 8 ^ Q.natDegree) :
    (L.prod.eval 3) ^ 2 ≤ ((2 : ℤ) ^ L.length) ^ c *
      8 ^ (L.map natDegree).sum := by
  induction L with
  | nil => simp
  | cons Q L ih =>
    have hq := hL Q (by simp)
    have ht := ih (fun A hA => hL A (by simp [hA]))
    simp only [List.prod_cons, eval_mul, mul_pow, List.length_cons, List.map_cons,
      List.sum_cons]
    calc
      _ ≤ (2 ^ c * (8 : ℤ) ^ Q.natDegree) *
          ((2 ^ L.length) ^ c * 8 ^ (L.map natDegree).sum) :=
        mul_le_mul hq ht (sq_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ, mul_pow, pow_add]; ring

lemma candidate_length_and_size (k : ℕ) (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) :
    let D := (digitPoly (Nat.digits 3 (2 ^ k))).natDegree
    (Nat.digits 3 (2 ^ k)).length = D + 1 ∧
      3 ^ D ≤ 2 ^ k ∧ k < 2 * (D + 1) := by
  dsimp only
  let D := (digitPoly (Nat.digits 3 (2 ^ k))).natDegree
  have hm := candidate_digitPoly_isMonicOfDegree k hg
  have hlenpos : 0 < (Nat.digits 3 (2 ^ k)).length :=
    List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (by positivity))
  have hlen : (Nat.digits 3 (2 ^ k)).length = D + 1 := by
    have hh := hm.natDegree_eq
    dsimp [D]
    omega
  refine ⟨hlen, ?_, ?_⟩
  · change 3 ^ D ≤ 2 ^ k
    have hh := Nat.base_pow_length_digits_le 3 (2 ^ k) (by decide) (by positivity)
    rw [hlen, pow_succ] at hh
    omega
  · have hh := Nat.lt_base_pow_length_digits (m := 2 ^ k) (by decide : 1 < 3)
    rw [hlen] at hh
    have hb : 2 ^ k < 2 ^ (2 * (D + 1)) := by
      calc
        _ < 3 ^ (D + 1) := hh
        _ ≤ 4 ^ (D + 1) := Nat.pow_le_pow_left (by decide) _
        _ = _ := by rw [pow_mul]; norm_num
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hb

/-- The accumulated constant is only polynomial in the total degree, because
there are at most logarithmically many irreducible factors. -/
lemma candidate_polynomial_bound (k c : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1])
    (hgap : ∀ Q : ℤ[X], Q.Monic → Irreducible Q →
      Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) →
      (Q.eval 3) ^ 2 ≤ (2 : ℤ) ^ c * 8 ^ Q.natDegree) :
    let D := (digitPoly (Nat.digits 3 (2 ^ k))).natDegree
    9 ^ D ≤ 8 ^ D * (D + 1) ^ c := by
  let P := digitPoly (Nat.digits 3 (2 ^ k))
  let D := P.natDegree
  obtain ⟨L, hL, he⟩ := monic_irreducible_list P
    (candidate_digitPoly_isMonicOfDegree k hg).monic
  have hdeg : (L.map natDegree).sum = D := by
    have hh := natDegree_multiset_prod_of_monic (L : Multiset ℤ[X])
      (show ∀ Q ∈ (L : Multiset ℤ[X]), Q.Monic from by
        simpa using fun Q hQ => (hL Q hQ).1)
    simpa [he, D] using hh.symm
  have hval : L.prod.eval 3 = (2 : ℤ) ^ k := by
    rw [he]
    dsimp [P]
    rw [digitPoly_eval_three]
    norm_cast
  have hb := list_eval_square_bound_constant L c (fun Q hQ =>
    hgap Q (hL Q hQ).1 (hL Q hQ).2 (by change Q ∣ P; rw [← he]; exact List.dvd_prod hQ))
  rw [hval, hdeg] at hb
  have hbN : (2 ^ k) ^ 2 ≤ (2 ^ L.length) ^ c * 8 ^ D := by exact_mod_cast hb
  have hlen := (candidate_length_and_size k hg).1
  have hsize := (candidate_length_and_size k hg).2.1
  have hc := candidate_factor_count_bound k hg L
    (fun Q hQ => ⟨(hL Q hQ).1,
      (hL Q hQ).1.natDegree_pos_of_not_isUnit (hL Q hQ).2.not_isUnit⟩) he
  rw [hlen] at hc
  change 9 ^ D ≤ 8 ^ D * (D + 1) ^ c
  calc
    9 ^ D = (3 ^ D) ^ 2 := by rw [← pow_mul, Nat.mul_comm D 2, pow_mul]; norm_num
    _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hsize _
    _ ≤ (2 ^ L.length) ^ c * 8 ^ D := hbN
    _ ≤ (D + 1) ^ c * 8 ^ D := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hc _)
    _ = _ := Nat.mul_comm _ _

/-- A uniform multiplicative constant of any fixed size is sufficient.
The factor bound is a premise, not a conclusion. -/
theorem finite_of_uniform_constant (c : ℕ)
    (hgap : ∀ k : ℕ, Nat.digits 3 (2 ^ k) ⊆ [0, 1] →
      ∀ Q : ℤ[X], Q.Monic → Irreducible Q →
        Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) →
        (Q.eval 3) ^ 2 ≤ (2 : ℤ) ^ c * 8 ^ Q.natDegree) :
    { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] }.Finite := by
  obtain ⟨N, hN⟩ := exponential_dominates_polynomial c
  apply ((Finset.range (2 * N)).finite_toSet.image (fun k : ℕ => 2 ^ k)).subset
  rintro n ⟨⟨k, rfl⟩, hg⟩
  let D := (digitPoly (Nat.digits 3 (2 ^ k))).natDegree
  have hb := candidate_polynomial_bound k c hg (hgap k hg)
  have hd : D < N := by
    by_contra hn
    exact (not_lt_of_ge hb) (hN D (by omega))
  have hk := (candidate_length_and_size k hg).2.2
  refine ⟨k, ?_, rfl⟩
  simpa using (show k < 2 * N by omega)

/-- A fixed range of low-degree exceptions can be absorbed using the elementary
root bound |Q(3)| ≤ 5^degree. No finite classification of those exceptions is
needed. -/
theorem finite_of_eventual_factor_bound (B c : ℕ)
    (hgap : ∀ k : ℕ, Nat.digits 3 (2 ^ k) ⊆ [0, 1] →
      ∀ Q : ℤ[X], Q.Monic → Irreducible Q →
        Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) → B < Q.natDegree →
        (Q.eval 3) ^ 2 ≤ (2 : ℤ) ^ c * 8 ^ Q.natDegree) :
    { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] }.Finite := by
  apply finite_of_uniform_constant (c + 5 * B)
  intro k hg Q hQ hI hd
  by_cases hB : B < Q.natDegree
  · have hb := hgap k hg Q hQ hI hd hB
    exact hb.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega : c ≤ c + 5 * B))
      (by positivity))
  · have hdeg : Q.natDegree ≤ B := by omega
    have hb := monic_eval_three_abs_bound Q hQ (candidate_factor_root_bound k hg Q hQ hd)
    have hsq : (Q.eval 3) ^ 2 ≤ (25 : ℤ) ^ Q.natDegree := by
      calc
        _ = |Q.eval 3| ^ 2 := (sq_abs _).symm
        _ ≤ (5 ^ Q.natDegree) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = _ := by rw [← pow_mul, Nat.mul_comm Q.natDegree 2, pow_mul]; norm_num
    calc
      _ ≤ (25 : ℤ) ^ Q.natDegree := hsq
      _ ≤ 32 ^ Q.natDegree := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = 2 ^ (5 * Q.natDegree) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ (c + 5 * B) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega)
      _ ≤ 2 ^ (c + 5 * B) * 8 ^ Q.natDegree := by
        have hh : (1 : ℤ) ≤ 8 ^ Q.natDegree := one_le_pow₀ (by norm_num)
        nlinarith only [hh, show (0 : ℤ) ≤ 2 ^ (c + 5 * B) by positivity]

/-- Negating finiteness forces exceptions of arbitrarily large degree and
arbitrarily large fixed multiplicative allowance. This is a necessary
condition for a disproof, not a disproof itself. -/
theorem infinite_forces_unbounded_bad_factors
    (hinf : ¬ { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] }.Finite)
    (B c : ℕ) :
    ∃ k : ℕ, Nat.digits 3 (2 ^ k) ⊆ [0, 1] ∧
      ∃ Q : ℤ[X], Q.Monic ∧ Irreducible Q ∧
        Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) ∧ B < Q.natDegree ∧
        (2 : ℤ) ^ c * 8 ^ Q.natDegree < (Q.eval 3) ^ 2 := by
  by_contra hn
  push_neg at hn
  apply hinf
  exact finite_of_eventual_factor_bound B c (by
    intro k hg Q hQ hI hd hB
    exact hn k hg Q hQ hI hd hB)

#print axioms finite_of_uniform_constant
#print axioms finite_of_eventual_factor_bound
#print axioms infinite_forces_unbounded_bad_factors
end Erdos406EventualFactorBound
