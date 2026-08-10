import FormalConjectures.Util.ProblemImports

open Finset Nat

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : ArithmeticFunction.sigma 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [ArithmeticFunction.sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
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
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
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
        apply _root_.ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply Nat.pow_lt_pow_right (by decide) (Nat.succ_lt_succ k.succ_pos)
    contrapose! hm
    simp [hm]

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

lemma exists_subset_sum_pow_two (p : ℕ) :
    ∀ m < 2^p, ∃ s ⊆ (Finset.range p).image (fun i => 2^i), s.sum _root_.id = m := by
  induction p with
  | zero =>
    intro m hm
    simp only [pow_zero] at hm
    have : m = 0 := by omega
    subst this
    use ∅
    simp
  | succ p ih =>
    intro m hm
    have h_pow : 2^(p+1) = 2^p + 2^p := by ring
    rw [h_pow] at hm
    by_cases h : m < 2^p
    · obtain ⟨s, hs_sub, hs_sum⟩ := ih m h
      use s
      constructor
      · rw [Finset.range_add_one, Finset.image_insert]
        exact hs_sub.trans (Finset.subset_insert _ _)
      · exact hs_sum
    · have h1 : m - 2^p < 2^p := by omega
      obtain ⟨s, hs_sub, hs_sum⟩ := ih (m - 2^p) h1
      let s' := insert (2^p) s
      use s'
      constructor
      · rw [Finset.range_add_one, Finset.image_insert]
        apply Finset.insert_subset_insert
        exact hs_sub
      · have h_not_mem : 2^p ∉ s := by
          intro h_mem
          have h_in_img := hs_sub h_mem
          rcases Finset.mem_image.mp h_in_img with ⟨i, hi, heq⟩
          rw [Finset.mem_range] at hi
          have h_lt : 2^i < 2^p := Nat.pow_lt_pow_right (by decide) hi
          rw [heq] at h_lt
          omega
        rw [Finset.sum_insert h_not_mem]
        rw [hs_sum]
        simp only [_root_.id_eq]
        omega

/--
%C A193279 a(n)=n if n is an even perfect number (is the converse true?)
-/
theorem oeis_193279_conjecture_0 (n : ℕ) :
  (Nat.Perfect n ∧ Even n) → A193279 n = n := by
  rintro ⟨h_perfect, h_even⟩
  obtain ⟨k, h_prime, h_n⟩ := eq_two_pow_mul_prime_mersenne_of_even_perfect h_even h_perfect
  let q := mersenne (k + 1)
  have hk : 0 < k := by
    by_contra h_zero
    have hk0 : k = 0 := by omega
    subst hk0
    rw [pow_zero, one_mul] at h_n
    have h_even_q : Even (mersenne 1) := by
      rw [← h_n]
      exact h_even
    have h_m1 : mersenne 1 = 1 := rfl
    rw [h_m1] at h_even_q
    have h_not : ¬ Even 1 := by
      rintro ⟨c, hc⟩
      omega
    exact h_not h_even_q
  subst h_n
  let A := (Finset.range (k + 1)).image (fun i => 2^i)
  let B := (Finset.range k).image (fun i => 2^i * q)
  have h_hq_gt : 1 < q := Nat.Prime.one_lt h_prime
  have hA : A ⊆ properDivisors (2^k * q) := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    rw [mem_properDivisors]
    constructor
    · have h_dvd1 : 2^i ∣ 2^k := Nat.pow_dvd_pow 2 (by omega)
      have h_dvd2 : 2^k ∣ 2^k * q := dvd_mul_right _ _
      exact dvd_trans h_dvd1 h_dvd2
    · have h_le : 2^i ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
      have h_lt : 2^k < 2^k * q := by
        have : 1 * 2^k < q * 2^k := Nat.mul_lt_mul_of_pos_right h_hq_gt (by positivity)
        rw [one_mul, mul_comm] at this
        exact this
      exact h_le.trans_lt h_lt
  have hB : B ⊆ properDivisors (2^k * q) := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    rw [mem_properDivisors]
    constructor
    · have h_dvd : 2^i ∣ 2^k := Nat.pow_dvd_pow 2 (by omega)
      exact mul_dvd_mul_right h_dvd q
    · have h_lt : 2^i < 2^k := Nat.pow_lt_pow_right (by decide) hi
      have h_q_pos : 0 < q := by omega
      exact Nat.mul_lt_mul_of_pos_right h_lt h_q_pos
  have h_subset_sum : ∀ m ≤ 2^k * q, ∃ s ⊆ A ∪ B, s.sum _root_.id = m := by
    intro m hm
    let d := if m = 2^k * q then 2^k - 1 else m / q
    let r := if m = 2^k * q then q else m % q
    have hd_lt : d < 2^k := by
      by_cases h_mn : m = 2^k * q
      · simp [h_mn, d]
      · simp [h_mn, d]
        have h_lt : m < q * 2^k := by
          rw [mul_comm]
          omega
        exact Nat.div_lt_of_lt_mul h_lt
    have hr_lt : r < 2^(k+1) := by
      by_cases h_mn : m = 2^k * q
      · simp only [h_mn, r, ↓reduceIte]
        have : q = 2^(k+1) - 1 := rfl
        omega
      · simp only [h_mn, r, ↓reduceIte]
        have h_hq : 0 < q := by omega
        have h_mod := Nat.mod_lt m h_hq
        have hq : q = 2^(k+1) - 1 := rfl
        rw [hq] at h_mod ⊢
        omega
    have h_eq : d * q + r = m := by
      by_cases h_mn : m = 2^k * q
      · simp only [h_mn, d, r, ↓reduceIte]
        rw [Nat.sub_mul, one_mul]
        have h_k_pos : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
        have h_le_mul : q ≤ 2^k * q := by
          have h_le_mul_left := Nat.mul_le_mul_right q h_k_pos
          rw [one_mul] at h_le_mul_left
          exact h_le_mul_left
        rw [Nat.sub_add_cancel h_le_mul]
      · simp only [h_mn, d, r, ↓reduceIte]
        rw [mul_comm]
        exact Nat.div_add_mod m q
    obtain ⟨s_pow, hs_pow_sub, hs_pow_sum⟩ := exists_subset_sum_pow_two k d hd_lt
    let s_B := s_pow.image (fun x => x * q)
    have hs_B_sub : s_B ⊆ B := by
      intro x hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨y, hy, rfl⟩
      have hy_img := hs_pow_sub hy
      rcases Finset.mem_image.mp hy_img with ⟨i, hi, rfl⟩
      exact Finset.mem_image_of_mem (fun i => 2^i * q) hi
    obtain ⟨s_A, hs_A_sub, hs_A_sum⟩ := exists_subset_sum_pow_two (k + 1) r hr_lt
    let s := s_A ∪ s_B
    use s
    constructor
    · apply Finset.union_subset_union hs_A_sub hs_B_sub
    · have h_disj : Disjoint s_A s_B := by
        have h_disj_AB : Disjoint A B := by
          rw [Finset.disjoint_iff_ne]
          intro x hx y hy
          rw [Finset.mem_image] at hx hy
          rcases hx with ⟨i, hi, rfl⟩
          rcases hy with ⟨j, hj, rfl⟩
          rw [Finset.mem_range] at hi hj
          have h_x_le : 2^i ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
          have h_y_ge : q ≤ 2^j * q := by
            have : 1 ≤ 2^j := Nat.one_le_pow j 2 (by decide)
            have : q * 1 ≤ q * 2^j := Nat.mul_le_mul_left q this
            rw [mul_one, mul_comm] at this
            exact this
          have h_q : 2^k < q := by
            have : q = 2^(k+1) - 1 := rfl
            have : 2^(k+1) = 2^k * 2 := by ring
            omega
          omega
        exact Disjoint.mono hs_A_sub hs_B_sub h_disj_AB
      rw [Finset.sum_union h_disj]
      have hs_B_sum : s_B.sum _root_.id = d * q := by
        have h_inj : ∀ x ∈ s_pow, ∀ y ∈ s_pow, x * q = y * q → x = y := by
          intro x _ y _ h_eq
          have h_q_pos : 0 < q := by omega
          exact Nat.eq_of_mul_eq_mul_right h_q_pos h_eq
        simp only [id_eq, _root_.id_eq]
        rw [Finset.sum_image h_inj]
        rw [← Finset.sum_mul]
        simp only [id_eq, _root_.id_eq] at hs_pow_sum
        rw [hs_pow_sum]
      simp only [id_eq] at hs_A_sum hs_B_sum ⊢
      rw [hs_A_sum, hs_B_sum]
      omega
  have hS : (properDivisors (2^k * mersenne (k + 1))).powerset.image (fun s : Finset ℕ => s.sum _root_.id) = Finset.range (2^k * mersenne (k + 1) + 1) := by
    apply Finset.Subset.antisymm
    · intro m hm
      rw [Finset.mem_image] at hm
      rcases hm with ⟨s, hs, rfl⟩
      rw [Finset.mem_powerset] at hs
      rw [Finset.mem_range]
      have h_le : s.sum _root_.id ≤ (properDivisors (2^k * mersenne (k + 1))).sum _root_.id := by
        apply Finset.sum_le_sum_of_subset
        intro x hx
        exact hs hx
      simp only [id_eq, _root_.id_eq] at h_perfect h_le ⊢
      have h_sum_proper : (∑ x ∈ properDivisors (2^k * mersenne (k + 1)), x) = 2^k * mersenne (k + 1) := h_perfect.1
      rw [h_sum_proper] at h_le
      omega
    · intro m hm
      have hq : q = mersenne (k + 1) := rfl
      rw [← hq] at hm
      rw [Finset.mem_range] at hm
      have hm_le : m ≤ 2^k * q := by omega
      obtain ⟨s, hs_sub, hs_sum⟩ := h_subset_sum m hm_le
      rw [Finset.mem_image]
      use s
      constructor
      · rw [Finset.mem_powerset]
        have h_union : A ∪ B ⊆ properDivisors (2^k * q) := Finset.union_subset hA hB
        exact hs_sub.trans h_union
      · exact hs_sum
  unfold A193279
  simp only [id_eq] at hS ⊢
  rw [hS]
  simp
