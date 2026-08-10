import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A193279: Number of distinct sums of distinct proper divisors of $n$.
The count excludes an empty subset of proper divisors that would give $0$ as a sum.
-/
def A193279 (n : ℕ) : ℕ :=
  let D := properDivisors n
  -- The set of all distinct sums of subsets of D, including the sum of the empty set (0).
  let S := D.powerset.image (fun s : Finset ℕ => s.sum id)
  -- The number of distinct sums, minus the single sum 0 from the empty set.
  S.card - 1

/--
%C A193279 a(n)=n if n is an even perfect number (is the converse true?)
-/
lemma mem_subsetSum_powers_two_of_lt {r K : ℕ} (hr : r < 2 ^ K) :
    r ∈ ((Finset.range K).image (fun i : ℕ => 2 ^ i)).subsetSum := by
  classical
  let I : Finset ℕ := r.bitIndices.toFinset
  let B : Finset ℕ := I.image (fun i : ℕ => 2 ^ i)
  refine Finset.mem_subsetSum_iff.mpr ⟨B, ?_, ?_⟩
  · intro x hx
    simp only [B, I, mem_image, List.mem_toFinset] at hx
    rcases hx with ⟨i, hi, rfl⟩
    simp only [mem_image, mem_range]
    refine ⟨i, ?_, rfl⟩
    have hle : 2 ^ i ≤ r := Nat.two_pow_le_of_mem_bitIndices hi
    have hlt : 2 ^ i < 2 ^ K := lt_of_le_of_lt hle hr
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  · simp only [B]
    rw [Finset.sum_image]
    · rw [← Nat.twoPowSum_bitIndices r]
      rw [← List.sum_toFinset]
      simp
    · intro a _ b _ h
      exact pow_right_injective₀ (by norm_num : (0 : ℕ) < 2) (by norm_num : (2 : ℕ) ≠ 1) h

lemma mem_subsetSum_scaled_powers_two_of_lt {q y K : ℕ} (hq : q ≠ 0) (hy : y < 2 ^ K) :
    q * y ∈ ((Finset.range K).image (fun i : ℕ => q * 2 ^ i)).subsetSum := by
  classical
  let I : Finset ℕ := y.bitIndices.toFinset
  let B : Finset ℕ := I.image (fun i : ℕ => q * 2 ^ i)
  refine Finset.mem_subsetSum_iff.mpr ⟨B, ?_, ?_⟩
  · intro x hx
    simp only [B, I, mem_image, List.mem_toFinset] at hx
    rcases hx with ⟨i, hi, rfl⟩
    simp only [mem_image, mem_range]
    refine ⟨i, ?_, rfl⟩
    have hle : 2 ^ i ≤ y := Nat.two_pow_le_of_mem_bitIndices hi
    have hlt : 2 ^ i < 2 ^ K := lt_of_le_of_lt hle hy
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  · simp only [B]
    rw [Finset.sum_image]
    · rw [← Finset.mul_sum]
      congr 1
      rw [← Nat.twoPowSum_bitIndices y]
      rw [← List.sum_toFinset]
      simp
    · intro a _ b _ h
      apply pow_right_injective₀ (by norm_num : (0 : ℕ) < 2) (by norm_num : (2 : ℕ) ≠ 1)
      exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hq) h

lemma add_mem_subsetSum_union_of_disjoint {A C : Finset ℕ} {x y : ℕ}
    (hdisj : Disjoint A C) (hx : x ∈ A.subsetSum) (hy : y ∈ C.subsetSum) :
    x + y ∈ (A ∪ C).subsetSum := by
  classical
  rcases Finset.mem_subsetSum_iff.mp hx with ⟨Bx, hBx, hsumx⟩
  rcases Finset.mem_subsetSum_iff.mp hy with ⟨By, hBy, hsumy⟩
  refine Finset.mem_subsetSum_iff.mpr ⟨Bx ∪ By, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Finset.mem_union_left _ (hBx hz)
    · exact Finset.mem_union_right _ (hBy hz)
  · have hdisj' : Disjoint Bx By := hdisj.mono hBx hBy
    rw [Finset.sum_union hdisj']
    rw [hsumx, hsumy]

lemma two_pow_lt_mersenne_succ {k : ℕ} (hk : k ≠ 0) : 2 ^ k < mersenne (k + 1) := by
  cases k with
  | zero => contradiction
  | succ l =>
      simp [mersenne, pow_succ]
      have hpos : 0 < 2 ^ l := pow_pos (by norm_num) l
      omega

lemma powers_two_subset_proper_mersenne {k q : ℕ} (hq1 : 1 < q) :
    ((Finset.range (k + 1)).image (fun i : ℕ => 2 ^ i)) ⊆ (2 ^ k * q).properDivisors := by
  intro x hx
  simp only [mem_image, mem_range] at hx
  rcases hx with ⟨i, hi, rfl⟩
  have hik : i ≤ k := Nat.lt_succ_iff.mp hi
  rw [Nat.mem_properDivisors]
  constructor
  · refine ⟨2 ^ (k - i) * q, ?_⟩
    calc
      2 ^ k * q = (2 ^ i * 2 ^ (k - i)) * q := by rw [← pow_add, Nat.add_sub_of_le hik]
      _ = 2 ^ i * (2 ^ (k - i) * q) := by rw [mul_assoc]
  · have hle : 2 ^ i ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hik
    have hlt : 2 ^ k < 2 ^ k * q := by
      nth_rw 1 [← mul_one (2 ^ k)]
      exact (Nat.mul_lt_mul_left (pow_pos (by norm_num) k)).mpr hq1
    exact lt_of_le_of_lt hle hlt

lemma scaled_powers_two_subset_proper_mersenne {k q : ℕ} (hq0 : q ≠ 0) :
    ((Finset.range k).image (fun i : ℕ => q * 2 ^ i)) ⊆ (2 ^ k * q).properDivisors := by
  intro x hx
  simp only [mem_image, mem_range] at hx
  rcases hx with ⟨i, hi, rfl⟩
  rw [Nat.mem_properDivisors]
  constructor
  · refine ⟨2 ^ (k - i), ?_⟩
    calc
      2 ^ k * q = (2 ^ i * 2 ^ (k - i)) * q := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hi)]
      _ = (q * 2 ^ i) * 2 ^ (k - i) := by ac_rfl
  · have hltpow : 2 ^ i < 2 ^ k := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr hi
    have hlt : q * 2 ^ i < q * 2 ^ k :=
      (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hq0)).mpr hltpow
    simpa [mul_comm] using hlt

lemma disjoint_powers_scaled_mersenne {k q : ℕ} (h2kq : 2 ^ k < q) :
    Disjoint ((Finset.range (k + 1)).image (fun i : ℕ => 2 ^ i))
      ((Finset.range k).image (fun i : ℕ => q * 2 ^ i)) := by
  rw [Finset.disjoint_left]
  intro x hxA hxC
  simp only [mem_image, mem_range] at hxA hxC
  rcases hxA with ⟨i, hi, rfl⟩
  rcases hxC with ⟨j, hj, hEq⟩
  have hik : i ≤ k := Nat.lt_succ_iff.mp hi
  have hle : 2 ^ i ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hik
  have hlt : 2 ^ i < q := lt_of_le_of_lt hle h2kq
  have hqle : q ≤ q * 2 ^ j := by
    nth_rw 1 [← mul_one q]
    exact Nat.mul_le_mul_left q (one_le_pow₀ (by norm_num : (0 : ℕ) < 2))
  omega

lemma ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

lemma range_subset_subsetSum_proper_mersenne {k q : ℕ}
    (hqeq : q = mersenne (k + 1)) (hqprime : q.Prime)
    (hsum : ∑ i ∈ (2 ^ k * q).properDivisors, i = 2 ^ k * q) :
    Finset.range (2 ^ k * q + 1) ⊆ (2 ^ k * q).properDivisors.subsetSum := by
  classical
  intro x hx
  have hxle : x ≤ 2 ^ k * q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  by_cases hxn : x = 2 ^ k * q
  · subst x
    exact Finset.mem_subsetSum_iff.mpr ⟨(2 ^ k * q).properDivisors, subset_rfl, hsum⟩
  · have hxlt : x < 2 ^ k * q := lt_of_le_of_ne hxle hxn
    have hqpos : 0 < q := hqprime.pos
    have hq0 : q ≠ 0 := hqprime.ne_zero
    have hq1 : 1 < q := hqprime.one_lt
    have hk0 : k ≠ 0 := by
      apply ne_zero_of_prime_mersenne k
      simpa [hqeq] using hqprime
    let y := x / q
    let r := x % q
    let A : Finset ℕ := (Finset.range (k + 1)).image (fun i : ℕ => 2 ^ i)
    let C : Finset ℕ := (Finset.range k).image (fun i : ℕ => q * 2 ^ i)
    have hy : y < 2 ^ k := by
      change x / q < 2 ^ k
      exact (Nat.div_lt_iff_lt_mul hqpos).mpr (by simpa [mul_comm] using hxlt)
    have hrq : r < q := by simpa [r] using Nat.mod_lt x hqpos
    have hq_lt : q < 2 ^ (k + 1) := by
      rw [hqeq, mersenne]
      have hp : 0 < 2 ^ (k + 1) := pow_pos (by norm_num) (k + 1)
      omega
    have hr : r < 2 ^ (k + 1) := lt_trans hrq hq_lt
    have hA : r ∈ A.subsetSum := by
      simpa [A] using mem_subsetSum_powers_two_of_lt (r := r) (K := k + 1) hr
    have hC : q * y ∈ C.subsetSum := by
      simpa [C] using mem_subsetSum_scaled_powers_two_of_lt (q := q) (y := y) (K := k) hq0 hy
    have hdisj : Disjoint A C := by
      have h2kq : 2 ^ k < q := by
        rw [hqeq]
        exact two_pow_lt_mersenne_succ hk0
      simpa [A, C] using disjoint_powers_scaled_mersenne (k := k) (q := q) h2kq
    have hmem_union : r + q * y ∈ (A ∪ C).subsetSum :=
      add_mem_subsetSum_union_of_disjoint hdisj hA hC
    have hunion_sub : A ∪ C ⊆ (2 ^ k * q).properDivisors := by
      intro z hz
      rcases Finset.mem_union.mp hz with hzA | hzC
      · exact powers_two_subset_proper_mersenne (k := k) (q := q) hq1 hzA
      · exact scaled_powers_two_subset_proper_mersenne (k := k) (q := q) hq0 hzC
    have hmemD : r + q * y ∈ (2 ^ k * q).properDivisors.subsetSum :=
      Finset.subsetSum_mono hunion_sub hmem_union
    convert hmemD using 1
    change x = x % q + q * (x / q)
    rw [add_comm, Nat.div_add_mod]

namespace LocalPerfect

open ArithmeticFunction Finset
open scoped sigma

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [ArithmeticFunction.sigma_one_apply, mersenne, ← one_add_one_eq_two,
    ← geom_sum_mul_add 1 (k + 1)]
  norm_num

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
    ← succ_mersenne, add_mul, one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply Nat.ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose! hm
    simp [hm]

end LocalPerfect

theorem oeis_193279_conjecture_0 (n : ℕ) :
  (Nat.Perfect n ∧ Even n) → A193279 n = n := by
  intro h
  rcases h with ⟨hperf, heven⟩
  obtain ⟨k, hqprime, hn⟩ :=
    LocalPerfect.eq_two_pow_mul_prime_mersenne_of_even_perfect heven hperf
  subst n
  let q := mersenne (k + 1)
  have hsum : ∑ i ∈ (2 ^ k * q).properDivisors, i = 2 ^ k * q := by
    simpa [q] using hperf.1
  have hset : (2 ^ k * q).properDivisors.subsetSum = Finset.range (2 ^ k * q + 1) := by
    apply subset_antisymm
    · intro x hx
      rw [Finset.mem_range, Nat.lt_succ_iff]
      rcases Finset.mem_subsetSum_iff.mp hx with ⟨B, hB, rfl⟩
      exact (Finset.sum_le_sum_of_subset_of_nonneg hB (by
        intro a _ _
        exact Nat.zero_le a)).trans_eq hsum
    · exact range_subset_subsetSum_proper_mersenne (k := k) (q := q) rfl hqprime hsum
  unfold A193279
  change ((2 ^ k * q).properDivisors.subsetSum).card - 1 = 2 ^ k * q
  rw [hset]
  simp
