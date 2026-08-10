import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A129365: $a(n) = A092287(n)/A129364(n)$.
$$a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$$
-/
def a (n : ℕ) : ℕ :=
  -- A092287(n) = Product Product gcd(j,k)
  let numerator : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
  -- A129364(n) = Product (floor(n/k)!)^k
  let denominator : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

  -- The conjecture guarantees that the division is exact.
  numerator / denominator

-- Helper function for A004125, b(n) = floor(n/2)
def b (n : ℕ) : ℕ := n / 2

-- Note: `(m.factorization p)` is the exponent of p in the prime factorization of m,
-- corresponding to ordp(m, p).



def numerator (N : ℕ) : ℕ := (Icc 1 N).prod fun j => (Icc 1 N).prod fun k => Nat.gcd j k

def denominator (N : ℕ) : ℕ := (Icc 1 N).prod fun k => (Nat.factorial (N / k)) ^ k

def aa (n : ℕ) : ℕ := numerator n / denominator n

lemma a_eq_aa (N : ℕ) : a N = aa N := by
  simp [a, aa, numerator, denominator]






lemma div_np_add_k_by_p (n p k : ℕ) (hp0 : 0 < p) (hk : k < p) :
    (n * p + k) / p = n := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp0]
  simp [Nat.div_eq_of_lt hk]

lemma div_np_add_k_by_pow (n p k i : ℕ) (hp0 : 0 < p) (hk : k < p) (hi : 1 ≤ i) :
    (n * p + k) / p ^ i = (n * p) / p ^ i := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [pow_add, pow_one]
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  rw [div_np_add_k_by_p n p k hp0 hk]
  rw [Nat.mul_comm n p, Nat.mul_div_right _ hp0]

lemma gcd_ne_zero_of_mem_Icc {N j k : ℕ} (hj : j ∈ Icc 1 N) (hk : k ∈ Icc 1 N) :
    Nat.gcd j k ≠ 0 := by
  have hjpos : 0 < j := by exact Nat.lt_of_lt_of_le zero_lt_one (mem_Icc.mp hj).1
  exact Nat.gcd_ne_zero_left hjpos.ne'

lemma numerator_factorization (N p : ℕ) :
    (numerator N).factorization p =
      ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (Nat.gcd j k).factorization p := by
  simp only [numerator]
  rw [Nat.factorization_prod]
  · rw [show ((∑ x ∈ Icc 1 N, ((Icc 1 N).prod fun k => Nat.gcd x k).factorization) p) =
        ∑ x ∈ Icc 1 N, ((Icc 1 N).prod fun k => Nat.gcd x k).factorization p from by
        simpa using Finset.sum_apply p (Icc 1 N) (fun x => ((Icc 1 N).prod fun k => Nat.gcd x k).factorization)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.factorization_prod]
    · simpa using Finset.sum_apply p (Icc 1 N) (fun k => (Nat.gcd j k).factorization)
    · intro k hk
      exact gcd_ne_zero_of_mem_Icc hj hk
  · intro j hj
    exact Finset.prod_ne_zero_iff.mpr fun k hk => gcd_ne_zero_of_mem_Icc hj hk

lemma denominator_factorization (N p : ℕ) :
    (denominator N).factorization p =
      ∑ k ∈ Icc 1 N, ((Nat.factorial (N / k)) ^ k).factorization p := by
  simp only [denominator]
  rw [Nat.factorization_prod]
  · simpa using Finset.sum_apply p (Icc 1 N) (fun k => ((Nat.factorial (N / k)) ^ k).factorization)
  · intro k hk
    exact pow_ne_zero _ (Nat.factorial_ne_zero _)

lemma denominator_factorization' (N p : ℕ) :
    (denominator N).factorization p =
      ∑ k ∈ Icc 1 N, k * (Nat.factorial (N / k)).factorization p := by
  rw [denominator_factorization]
  simp [Nat.factorization_pow]

lemma aa_factorization_eq_sub {N p : ℕ} (hdiv : denominator N ∣ numerator N) :
    (aa N).factorization p = (numerator N).factorization p - (denominator N).factorization p := by
  simpa [aa] using congrArg (fun f => f p) (Nat.factorization_div hdiv)








lemma gcd_factorization_as_sum (N q j k : ℕ) (hq : Nat.Prime q)
    (hj : j ∈ Icc 1 N) (hk : k ∈ Icc 1 N) :
    (Nat.gcd j k).factorization q =
      ∑ i ∈ Icc 1 N, if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0 := by
  have hgj0 : Nat.gcd j k ≠ 0 := gcd_ne_zero_of_mem_Icc hj hk
  have hgpos : 0 < Nat.gcd j k := Nat.pos_of_ne_zero hgj0
  have hg_le_N : Nat.gcd j k ≤ N := by
    exact (Nat.gcd_le_left k (Nat.lt_of_lt_of_le zero_lt_one (mem_Icc.mp hj).1)).trans (mem_Icc.mp hj).2
  have hlt : Nat.gcd j k < q ^ (N + 1) := by
    exact lt_of_le_of_lt hg_le_N (lt_trans (Nat.lt_succ_self N) (Nat.lt_pow_self hq.one_lt))
  rw [Nat.factorization_eq_card_pow_dvd_of_lt hq hgpos hlt]
  rw [Finset.card_filter]
  rw [← Ico_succ_right_eq_Icc]
  apply Finset.sum_congr rfl
  intro i hi
  have hpow_gcd : q ^ i ∣ Nat.gcd j k ↔ q ^ i ∣ j ∧ q ^ i ∣ k := by
    exact Nat.dvd_gcd_iff
  by_cases h : q ^ i ∣ j ∧ q ^ i ∣ k
  · simp [h, hpow_gcd.mpr h]
  · simp [h, hpow_gcd, h]

lemma card_Icc_filter_pow_dvd (N q i : ℕ) :
    #{x ∈ Icc 1 N | q ^ i ∣ x} = N / q ^ i := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div N (q ^ i)]
  congr 1


lemma sum_pair_indicator_eq_card_sq {α : Type*} [DecidableEq α]
    (S : Finset α) (P : α → Prop) [DecidablePred P] :
    (∑ j ∈ S, ∑ k ∈ S, if P j ∧ P k then 1 else 0) = (#{x ∈ S | P x}) ^ 2 := by
  classical
  rw [Finset.card_filter]
  simp only [pow_two]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hpj : P j
  · simp [hpj]
  · simp [hpj]

lemma numerator_factorization_formula (N q : ℕ) (hq : Nat.Prime q) :
    (numerator N).factorization q = ∑ i ∈ Icc 1 N, (N / q ^ i) ^ 2 := by
  rw [numerator_factorization]
  calc
    (∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (Nat.gcd j k).factorization q)
        = ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
            ∑ i ∈ Icc 1 N, if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          exact gcd_factorization_as_sum N q j k hq hj hk
    _ = ∑ i ∈ Icc 1 N, ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
            if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0 := by
          conv_lhs =>
            arg 2
            intro j
            rw [Finset.sum_comm]
          rw [Finset.sum_comm]
    _ = ∑ i ∈ Icc 1 N, (N / q ^ i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [sum_pair_indicator_eq_card_sq]
          rw [card_Icc_filter_pow_dvd]

lemma factorial_factorization_as_sum (N q k : ℕ) (hq : Nat.Prime q) (hk : k ∈ Icc 1 N) :
    (Nat.factorial (N / k)).factorization q = ∑ i ∈ Icc 1 N, (N / k) / q ^ i := by
  have hkpos : 0 < k := Nat.lt_of_lt_of_le zero_lt_one (mem_Icc.mp hk).1
  have hk_le : k ≤ N := (mem_Icc.mp hk).2
  have hdivpos : 0 < N / k := Nat.div_pos hk_le hkpos
  have hdiv_le : N / k ≤ N := Nat.div_le_self N k
  have hlt : N / k < q ^ (N + 1) := by
    exact lt_of_le_of_lt hdiv_le (lt_trans (Nat.lt_succ_self N) (Nat.lt_pow_self hq.one_lt))
  have hlog : Nat.log q (N / k) < N + 1 := Nat.log_lt_of_lt_pow hdivpos.ne' hlt
  rw [Nat.factorization_factorial hq hlog]
  rw [← Ico_succ_right_eq_Icc]
  rfl

lemma denominator_factorization_formula (N q : ℕ) (hq : Nat.Prime q) :
    (denominator N).factorization q =
      ∑ k ∈ Icc 1 N, k * (∑ i ∈ Icc 1 N, (N / k) / q ^ i) := by
  rw [denominator_factorization']
  apply Finset.sum_congr rfl
  intro k hk
  rw [factorial_factorization_as_sum N q k hq hk]

lemma denominator_factorization_formula_swap (N q : ℕ) (hq : Nat.Prime q) :
    (denominator N).factorization q =
      ∑ i ∈ Icc 1 N, ∑ k ∈ Icc 1 N, k * ((N / k) / q ^ i) := by
  rw [denominator_factorization_formula N q hq]
  calc
    (∑ k ∈ Icc 1 N, k * (∑ i ∈ Icc 1 N, (N / k) / q ^ i))
        = ∑ k ∈ Icc 1 N, ∑ i ∈ Icc 1 N, k * ((N / k) / q ^ i) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mul_sum]
    _ = ∑ i ∈ Icc 1 N, ∑ k ∈ Icc 1 N, k * ((N / k) / q ^ i) := by
            rw [Finset.sum_comm]

lemma div_div_comm (N k d : ℕ) : (N / k) / d = (N / d) / k := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

lemma inner_den_le_sq (N q i : ℕ) :
    (∑ k ∈ Icc 1 N, k * ((N / k) / q ^ i)) ≤ (N / q ^ i) ^ 2 := by
  let m := N / q ^ i
  have hmN : m ≤ N := Nat.div_le_self N (q ^ i)
  have hsub : Icc 1 m ⊆ Icc 1 N := by
    intro x hx
    exact mem_Icc.mpr ⟨(mem_Icc.mp hx).1, (mem_Icc.mp hx).2.trans hmN⟩
  calc
    (∑ k ∈ Icc 1 N, k * ((N / k) / q ^ i))
        = ∑ k ∈ Icc 1 N, k * (m / k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [div_div_comm]
    _ = ∑ k ∈ Icc 1 m, k * (m / k) := by
            symm
            apply Finset.sum_subset hsub
            intro x hxN hxnot
            have hxgt : m < x := by
              have hx1 : 1 ≤ x := (mem_Icc.mp hxN).1
              have hxNm : ¬ x ∈ Icc 1 m := hxnot
              by_contra hle
              exact hxNm (mem_Icc.mpr ⟨hx1, le_of_not_gt hle⟩)
            rw [Nat.div_eq_of_lt hxgt, mul_zero]
    _ ≤ ∑ k ∈ Icc 1 m, m := by
            apply Finset.sum_le_sum
            intro k hk
            rw [mul_comm]
            exact Nat.div_mul_le_self m k
    _ = m ^ 2 := by
            rw [Finset.sum_const, card_Icc]
            simp [pow_two]

lemma denominator_factorization_le_numerator (N q : ℕ) (hq : Nat.Prime q) :
    (denominator N).factorization q ≤ (numerator N).factorization q := by
  rw [denominator_factorization_formula_swap N q hq, numerator_factorization_formula N q hq]
  apply Finset.sum_le_sum
  intro i hi
  exact inner_den_le_sq N q i

lemma numerator_ne_zero (N : ℕ) : numerator N ≠ 0 := by
  unfold numerator
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact gcd_ne_zero_of_mem_Icc hj hk

lemma denominator_ne_zero (N : ℕ) : denominator N ≠ 0 := by
  unfold denominator
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact pow_ne_zero _ (Nat.factorial_ne_zero _)

lemma denominator_dvd_numerator (N : ℕ) : denominator N ∣ numerator N := by
  rw [← Nat.factorization_le_iff_dvd (denominator_ne_zero N) (numerator_ne_zero N)]
  intro q
  by_cases hq : Nat.Prime q
  · exact denominator_factorization_le_numerator N q hq
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]



def denTerm (N q i : ℕ) : ℕ :=
  ∑ k ∈ Icc 1 (N / q ^ i), k * ((N / q ^ i) / k)

lemma inner_den_eq_denTerm (N q i : ℕ) :
    (∑ k ∈ Icc 1 N, k * ((N / k) / q ^ i)) = denTerm N q i := by
  unfold denTerm
  let m := N / q ^ i
  have hmN : m ≤ N := Nat.div_le_self N (q ^ i)
  have hsub : Icc 1 m ⊆ Icc 1 N := by
    intro x hx
    exact mem_Icc.mpr ⟨(mem_Icc.mp hx).1, (mem_Icc.mp hx).2.trans hmN⟩
  calc
    (∑ k ∈ Icc 1 N, k * ((N / k) / q ^ i))
        = ∑ k ∈ Icc 1 N, k * (m / k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [div_div_comm]
    _ = ∑ k ∈ Icc 1 m, k * (m / k) := by
            symm
            apply Finset.sum_subset hsub
            intro x hxN hxnot
            have hxgt : m < x := by
              have hx1 : 1 ≤ x := (mem_Icc.mp hxN).1
              by_contra hle
              exact hxnot (mem_Icc.mpr ⟨hx1, le_of_not_gt hle⟩)
            rw [Nat.div_eq_of_lt hxgt, mul_zero]

lemma denominator_factorization_closed (N q : ℕ) (hq : Nat.Prime q) :
    (denominator N).factorization q = ∑ i ∈ Icc 1 N, denTerm N q i := by
  rw [denominator_factorization_formula_swap N q hq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_den_eq_denTerm]

lemma div_pow_eq_zero_of_lt_index (N q i : ℕ) (hq : Nat.Prime q) (hNi : N < i) :
    N / q ^ i = 0 := by
  apply Nat.div_eq_of_lt
  exact lt_of_lt_of_le (Nat.lt_pow_self hq.one_lt)
    (Nat.pow_le_pow_right hq.pos (Nat.le_of_lt hNi))

lemma sum_Icc_extend_right {F : ℕ → ℕ} {N B : ℕ} (hNB : N ≤ B)
    (hzero : ∀ i, i ∈ Icc 1 B → i ∉ Icc 1 N → F i = 0) :
    (∑ i ∈ Icc 1 N, F i) = ∑ i ∈ Icc 1 B, F i := by
  apply Finset.sum_subset
  · intro i hi
    exact mem_Icc.mpr ⟨(mem_Icc.mp hi).1, (mem_Icc.mp hi).2.trans hNB⟩
  · exact hzero

lemma numerator_factorization_formula_bound (N B q : ℕ) (hq : Nat.Prime q) (hNB : N ≤ B) :
    (numerator N).factorization q = ∑ i ∈ Icc 1 B, (N / q ^ i) ^ 2 := by
  rw [numerator_factorization_formula N q hq]
  apply sum_Icc_extend_right hNB
  intro i hiB hiN
  have hNi : N < i := by
    have hi1 : 1 ≤ i := (mem_Icc.mp hiB).1
    by_contra hle
    exact hiN (mem_Icc.mpr ⟨hi1, le_of_not_gt hle⟩)
  rw [div_pow_eq_zero_of_lt_index N q i hq hNi]
  simp

lemma denominator_factorization_closed_bound (N B q : ℕ) (hq : Nat.Prime q) (hNB : N ≤ B) :
    (denominator N).factorization q = ∑ i ∈ Icc 1 B, denTerm N q i := by
  rw [denominator_factorization_closed N q hq]
  apply sum_Icc_extend_right hNB
  intro i hiB hiN
  have hNi : N < i := by
    have hi1 : 1 ≤ i := (mem_Icc.mp hiB).1
    by_contra hle
    exact hiN (mem_Icc.mpr ⟨hi1, le_of_not_gt hle⟩)
  unfold denTerm
  rw [div_pow_eq_zero_of_lt_index N q i hq hNi]
  simp


lemma numerator_factorization_eq_of_floor (N M B p : ℕ) (hp : Nat.Prime p)
    (hNB : N ≤ B) (hMB : M ≤ B)
    (hfloor : ∀ i, i ∈ Icc 1 B → N / p ^ i = M / p ^ i) :
    (numerator N).factorization p = (numerator M).factorization p := by
  rw [numerator_factorization_formula_bound N B p hp hNB,
      numerator_factorization_formula_bound M B p hp hMB]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfloor i hi]

lemma denominator_factorization_eq_of_floor (N M B p : ℕ) (hp : Nat.Prime p)
    (hNB : N ≤ B) (hMB : M ≤ B)
    (hfloor : ∀ i, i ∈ Icc 1 B → N / p ^ i = M / p ^ i) :
    (denominator N).factorization p = (denominator M).factorization p := by
  rw [denominator_factorization_closed_bound N B p hp hNB,
      denominator_factorization_closed_bound M B p hp hMB]
  apply Finset.sum_congr rfl
  intro i hi
  unfold denTerm
  rw [hfloor i hi]

lemma aa_factorization_eq_of_floor (N M B p : ℕ) (hp : Nat.Prime p)
    (hNB : N ≤ B) (hMB : M ≤ B)
    (hfloor : ∀ i, i ∈ Icc 1 B → N / p ^ i = M / p ^ i) :
    (aa N).factorization p = (aa M).factorization p := by
  have hnum := numerator_factorization_eq_of_floor N M B p hp hNB hMB hfloor
  have hden := denominator_factorization_eq_of_floor N M B p hp hNB hMB hfloor
  rw [aa_factorization_eq_sub (N := N) (p := p) (denominator_dvd_numerator N),
      aa_factorization_eq_sub (N := M) (p := p) (denominator_dvd_numerator M)]
  rw [hnum, hden]


/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  rw [a_eq_aa (n * p), a_eq_aa (n * p + k)]
  let N0 := n * p
  let N1 := n * p + k
  have hN0B : N0 ≤ N1 := by simp [N0, N1]
  have hN1B : N1 ≤ N1 := le_rfl
  apply aa_factorization_eq_of_floor N0 N1 N1 p hp hN0B hN1B
  intro i hi
  have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
  dsimp [N0, N1]
  symm
  exact div_np_add_k_by_pow n p k i hp.pos hk hi1
