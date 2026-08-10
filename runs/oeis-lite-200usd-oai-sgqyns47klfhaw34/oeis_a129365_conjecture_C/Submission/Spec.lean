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

def numerator (n : ℕ) : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k

def denominator (n : ℕ) : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

lemma no_prime_dvd_between {n p k x : ℕ} (hp : Nat.Prime p) (hk : k < p)
    (hx1 : n * p < x) (hx2 : x ≤ n * p + k) : ¬ p ∣ x := by
  intro hpx
  have hpm : p ∣ n * p := by exact dvd_mul_left p n
  have hpdiff : p ∣ x - n * p := Nat.dvd_sub hpx hpm
  have hdiffpos : 0 < x - n * p := Nat.sub_pos_of_lt hx1
  have hdiffle : x - n * p ≤ k := by omega
  have hdiff_lt_p : x - n * p < p := lt_of_le_of_lt hdiffle hk
  have hp_le : p ≤ x - n * p := Nat.le_of_dvd hdiffpos hpdiff
  omega



lemma div_eq_add_lt_prime {n p k D : ℕ} (hp : Nat.Prime p) (hk : k < p)
    (hDpos : 0 < D) (hpD : p ∣ D) : (n * p + k) / D = (n * p) / D := by
  let q := (n * p) / D
  apply Nat.div_eq_of_lt_le
  · exact (Nat.div_mul_le_self (n * p) D).trans (by omega)
  · by_contra hnot
    push_neg at hnot
    have hqgt : n * p < (q + 1) * D := by
      have := Nat.lt_div_mul_add (a := n * p) (b := D) hDpos
      simpa [q, Nat.add_mul] using this
    have hbad : ¬ p ∣ (q + 1) * D := no_prime_dvd_between hp hk hqgt hnot
    exact hbad (dvd_mul_of_dvd_right hpD (q+1))


lemma gcd_factorization_zero_of_left_not_dvd {p j l : ℕ} (h : ¬ p ∣ j) : (Nat.gcd j l).factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hg
  exact h (hg.trans (Nat.gcd_dvd_left j l))

lemma gcd_factorization_zero_of_right_not_dvd {p j l : ℕ} (h : ¬ p ∣ l) : (Nat.gcd j l).factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hg
  exact h (hg.trans (Nat.gcd_dvd_right j l))

lemma numerator_factorization_stable (n p k : ℕ) (hp : Nat.Prime p) (hk : k < p) :
    (numerator (n * p + k)).factorization p = (numerator (n * p)).factorization p := by
  unfold numerator
  rw [Nat.factorization_prod_apply, Nat.factorization_prod_apply]
  · calc
      (∑ x ∈ Icc 1 (n * p + k), (∏ k_1 ∈ Icc 1 (n * p + k), x.gcd k_1).factorization p)
          = ∑ x ∈ Icc 1 (n * p), (∏ k_1 ∈ Icc 1 (n * p + k), x.gcd k_1).factorization p := by
            symm
            refine Finset.sum_subset ?subset ?zero
            · intro j hj
              simp at hj ⊢
              omega
            · intro j hjBig hjNot
              have hjgt : n * p < j := by
                simp at hjBig hjNot ⊢
                omega
              have hjBig' := mem_Icc.mp hjBig
              have hjndvd : ¬ p ∣ j := no_prime_dvd_between hp hk hjgt hjBig'.2
              rw [Nat.factorization_prod_apply]
              · exact sum_eq_zero fun l hl => gcd_factorization_zero_of_left_not_dvd hjndvd
              · intro l hl
                have hjpos : 0 < j := by
                  exact lt_of_lt_of_le zero_lt_one (mem_Icc.mp hjBig).1
                exact Nat.gcd_ne_zero_left hjpos.ne'
      _ = ∑ x ∈ Icc 1 (n * p), (∏ k_1 ∈ Icc 1 (n * p), x.gcd k_1).factorization p := by
            apply Finset.sum_congr rfl
            intro j hjSmall
            rw [Nat.factorization_prod_apply, Nat.factorization_prod_apply]
            · symm
              refine Finset.sum_subset ?subset2 ?zero2
              · intro l hl; simp at hl ⊢; omega
              · intro l hlBig hlNot
                have hlgt : n * p < l := by
                  simp at hlBig hlNot ⊢
                  omega
                have hlBig' := mem_Icc.mp hlBig
                have hlndvd : ¬ p ∣ l := no_prime_dvd_between hp hk hlgt hlBig'.2
                exact gcd_factorization_zero_of_right_not_dvd hlndvd
            · intro l hl
              have hjpos : 0 < j := by
                exact lt_of_lt_of_le zero_lt_one (mem_Icc.mp hjSmall).1
              exact Nat.gcd_ne_zero_left hjpos.ne'
            · intro l hl
              have hjpos : 0 < j := by
                exact lt_of_lt_of_le zero_lt_one (mem_Icc.mp hjSmall).1
              exact Nat.gcd_ne_zero_left hjpos.ne'
  · intro j hj
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    have hjpos : 0 < j := lt_of_lt_of_le zero_lt_one (mem_Icc.mp hj).1
    exact Nat.gcd_ne_zero_left hjpos.ne'
  · intro j hj
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    have hjpos : 0 < j := lt_of_lt_of_le zero_lt_one (mem_Icc.mp hj).1
    exact Nat.gcd_ne_zero_left hjpos.ne'


lemma factorial_factorization_stable (n p k r : ℕ) (hp : Nat.Prime p) (hk : k < p)
    (hr : r ∈ Icc 1 (n * p)) :
    (Nat.factorial ((n * p + k) / r)).factorization p =
      (Nat.factorial ((n * p) / r)).factorization p := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  rw [← padicValNat_mul_div_factorial ((n * p + k) / r),
      ← padicValNat_mul_div_factorial ((n * p) / r)]
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one (mem_Icc.mp hr).1
  have hdiv : ((n * p + k) / r) / p = ((n * p) / r) / p := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    exact div_eq_add_lt_prime hp hk (Nat.mul_pos hrpos hp.pos) (by exact dvd_mul_left p r)
  rw [hdiv]

lemma denominator_factorization_stable (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
    (denominator (n * p + k)).factorization p = (denominator (n * p)).factorization p := by
  unfold denominator
  rw [Nat.factorization_prod_apply, Nat.factorization_prod_apply]
  · calc
      (∑ x ∈ Icc 1 (n * p + k), (((n * p + k) / x)! ^ x).factorization p)
          = ∑ x ∈ Icc 1 (n * p), (((n * p + k) / x)! ^ x).factorization p := by
            symm
            refine Finset.sum_subset ?subset ?zero
            · intro x hx; simp at hx ⊢; omega
            · intro x hxBig hxNot
              have hx' := mem_Icc.mp hxBig
              have hxgt : n * p < x := by simp at hxBig hxNot ⊢; omega
              have hxle : x ≤ n * p + k := hx'.2
              have hdivone : (n * p + k) / x = 1 := by
                apply Nat.div_eq_of_lt_le
                · simpa using hxle
                · have hppos : 0 < p := hp.pos
                  have hple : p ≤ n * p := by
                    exact Nat.le_mul_of_pos_left p hn
                  omega
              simp [hdivone]
      _ = ∑ x ∈ Icc 1 (n * p), (((n * p) / x)! ^ x).factorization p := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Nat.factorization_pow, Nat.factorization_pow]
            simp [factorial_factorization_stable n p k x hp hk hx]
  · intro x hx; exact pow_ne_zero _ (Nat.factorial_ne_zero _)
  · intro x hx; exact pow_ne_zero _ (Nat.factorial_ne_zero _)


lemma sum_mul_floor_div_le_sq (n Q : ℕ) (hQ : 0 < Q) :
    (∑ r ∈ Icc 1 n, r * (n / (r * Q))) ≤ (n / Q) ^ 2 := by
  let s := n / Q
  have hsle : s ≤ n := Nat.div_le_self n Q
  calc
    (∑ r ∈ Icc 1 n, r * (n / (r * Q)))
        = ∑ r ∈ Icc 1 s, r * (n / (r * Q)) := by
          symm
          refine Finset.sum_subset ?subset ?zero
          · intro r hr
            have hr' := mem_Icc.mp hr
            exact mem_Icc.mpr ⟨hr'.1, hr'.2.trans hsle⟩
          · intro r hrn hrs
            have hrn' := mem_Icc.mp hrn
            have hrs_gt : s < r := by
              by_contra h
              push_neg at h
              exact hrs (mem_Icc.mpr ⟨hrn'.1, h⟩)
            have hlt : n < r * Q := by
              rw [← Nat.div_lt_iff_lt_mul hQ]
              exact hrs_gt
            have hdiv0 : n / (r * Q) = 0 := by
              apply Nat.div_eq_of_lt
              exact hlt
            simp [hdiv0]
    _ ≤ ∑ r ∈ Icc 1 s, s := by
          refine sum_le_sum ?_
          intro r hr
          have hmul : (r * (n / (r * Q))) * Q ≤ n := by
            calc
              (r * (n / (r * Q))) * Q = (n / (r * Q)) * (r * Q) := by ring
              _ ≤ n := Nat.div_mul_le_self n (r * Q)
          exact (Nat.le_div_iff_mul_le hQ).2 hmul
    _ = (n / Q) ^ 2 := by
          simp [s, pow_two]




lemma denominator_factorization_le_levelSum (n q : ℕ) (hq : Nat.Prime q) :
    (denominator n).factorization q ≤ ∑ i ∈ Ico 1 (n + 1), (n / q ^ i) ^ 2 := by
  unfold denominator
  rw [Nat.factorization_prod_apply]
  · calc
      (∑ r ∈ Icc 1 n, (((n / r)!) ^ r).factorization q)
          = ∑ r ∈ Icc 1 n, r * ((n / r)!).factorization q := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [Nat.factorization_pow]
            simp [nsmul_eq_mul]
      _ = ∑ r ∈ Icc 1 n, r * (∑ i ∈ Ico 1 (n + 1), (n / r) / q ^ i) := by
            apply Finset.sum_congr rfl
            intro r hr
            congr 1
            rw [Nat.factorization_factorial hq]
            exact lt_of_le_of_lt (Nat.log_le_self q (n / r)) ((Nat.div_le_self n r).trans_lt (Nat.lt_succ_self n))
      _ = ∑ i ∈ Ico 1 (n + 1), ∑ r ∈ Icc 1 n, r * ((n / r) / q ^ i) := by
            simp_rw [mul_sum]
            rw [Finset.sum_comm]
      _ = ∑ i ∈ Ico 1 (n + 1), ∑ r ∈ Icc 1 n, r * (n / (r * q ^ i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro r hr
            rw [Nat.div_div_eq_div_mul]
      _ ≤ ∑ i ∈ Ico 1 (n + 1), (n / q ^ i) ^ 2 := by
            refine sum_le_sum ?_
            intro i hi
            exact sum_mul_floor_div_le_sq n (q ^ i) (pow_pos hq.pos i)
  · intro r hr; exact pow_ne_zero _ (Nat.factorial_ne_zero _)



lemma gcd_factorization_eq_indicator_sum (n q j l : ℕ) (hq : Nat.Prime q)
    (hj : j ∈ Icc 1 n) (hl : l ∈ Icc 1 n) :
    (Nat.gcd j l).factorization q =
      ∑ i ∈ Ico 1 (n + 1), if q ^ i ∣ j ∧ q ^ i ∣ l then 1 else 0 := by
  classical
  have hjpos : 0 < j := lt_of_lt_of_le zero_lt_one (mem_Icc.mp hj).1
  have hlpos : 0 < l := lt_of_lt_of_le zero_lt_one (mem_Icc.mp hl).1
  have hgpos : 0 < Nat.gcd j l := Nat.gcd_pos_of_pos_left l hjpos
  have hgle : Nat.gcd j l ≤ n := (le_of_dvd hjpos (Nat.gcd_dvd_left j l)).trans (mem_Icc.mp hj).2
  have hnpos : 0 < n := lt_of_lt_of_le hgpos hgle
  have hbound : Nat.gcd j l < q ^ (n + 1) := by
    have hqpow : n < q ^ n := Nat.lt_pow_self hq.one_lt
    have hmono : q ^ n ≤ q ^ (n + 1) := Nat.pow_le_pow_right hq.pos (Nat.le_succ n)
    exact lt_of_le_of_lt hgle (hqpow.trans_le hmono)
  rw [Nat.factorization_eq_card_pow_dvd_of_lt hq hgpos hbound]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Nat.dvd_gcd_iff]

lemma card_Icc_filter_dvd_eq_div (n Q : ℕ) :
    #{x ∈ Icc 1 n | Q ∣ x} = n / Q := by
  simpa [Ioc, Nat.succ_le_iff] using Nat.Ioc_filter_dvd_card_eq_div n Q

lemma pair_dvd_indicator_sum (n Q : ℕ) :
    (∑ j ∈ Icc 1 n, ∑ l ∈ Icc 1 n, if Q ∣ j ∧ Q ∣ l then 1 else 0) = (n / Q) ^ 2 := by
  classical
  change (Icc 1 n).sum (fun j => (Icc 1 n).sum (fun l => if Q ∣ j ∧ Q ∣ l then 1 else 0)) = (n / Q) ^ 2
  rw [← (Finset.sum_product (Icc 1 n) (Icc 1 n) (fun x : ℕ × ℕ => if Q ∣ x.1 ∧ Q ∣ x.2 then 1 else 0))]
  rw [Finset.sum_boole]
  rw [Finset.filter_product]
  rw [Finset.card_product]
  simp [card_Icc_filter_dvd_eq_div, pow_two]


lemma numerator_factorization_eq_levelSum (n q : ℕ) (hq : Nat.Prime q) :
    (numerator n).factorization q = ∑ i ∈ Ico 1 (n + 1), (n / q ^ i) ^ 2 := by
  classical
  unfold numerator
  rw [Nat.factorization_prod_apply]
  · calc
      (∑ j ∈ Icc 1 n, ((∏ k ∈ Icc 1 n, j.gcd k)).factorization q)
          = ∑ j ∈ Icc 1 n, ∑ l ∈ Icc 1 n, (j.gcd l).factorization q := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Nat.factorization_prod_apply]
            intro l hl
            have hjpos : 0 < j := lt_of_lt_of_le zero_lt_one (mem_Icc.mp hj).1
            exact Nat.gcd_ne_zero_left hjpos.ne'
      _ = ∑ j ∈ Icc 1 n, ∑ l ∈ Icc 1 n, ∑ i ∈ Ico 1 (n + 1), if q ^ i ∣ j ∧ q ^ i ∣ l then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro l hl
            exact gcd_factorization_eq_indicator_sum n q j l hq hj hl
      _ = ∑ j ∈ Icc 1 n, ∑ i ∈ Ico 1 (n + 1), ∑ l ∈ Icc 1 n, if q ^ i ∣ j ∧ q ^ i ∣ l then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_comm]
      _ = ∑ i ∈ Ico 1 (n + 1), ∑ j ∈ Icc 1 n, ∑ l ∈ Icc 1 n, if q ^ i ∣ j ∧ q ^ i ∣ l then 1 else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ i ∈ Ico 1 (n + 1), (n / q ^ i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact pair_dvd_indicator_sum n (q ^ i)
  · intro j hj
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    have hjpos : 0 < j := lt_of_lt_of_le zero_lt_one (mem_Icc.mp hj).1
    exact Nat.gcd_ne_zero_left hjpos.ne'

lemma numerator_ne_zero (n : ℕ) : numerator n ≠ 0 := by
  unfold numerator
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  rw [Finset.prod_ne_zero_iff]
  intro l hl
  have hjpos : 0 < j := lt_of_lt_of_le zero_lt_one (mem_Icc.mp hj).1
  exact Nat.gcd_ne_zero_left hjpos.ne'

lemma denominator_ne_zero (n : ℕ) : denominator n ≠ 0 := by
  unfold denominator
  rw [Finset.prod_ne_zero_iff]
  intro r hr
  exact pow_ne_zero _ (Nat.factorial_ne_zero _)

lemma denominator_dvd_numerator (n : ℕ) : denominator n ∣ numerator n := by
  apply (Nat.factorization_le_iff_dvd (denominator_ne_zero n) (numerator_ne_zero n)).mp
  intro q
  by_cases hq : Nat.Prime q
  · rw [numerator_factorization_eq_levelSum n q hq]
    exact denominator_factorization_le_levelSum n q hq
  · rw [Nat.factorization_eq_zero_of_not_prime (denominator n) hq]
    exact Nat.zero_le _


/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  change ((numerator (n * p)) / (denominator (n * p))).factorization p =
    ((numerator (n * p + k)) / (denominator (n * p + k))).factorization p
  rw [Nat.factorization_div (denominator_dvd_numerator (n * p)),
      Nat.factorization_div (denominator_dvd_numerator (n * p + k))]
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  rw [numerator_factorization_stable n p k hp hk,
      denominator_factorization_stable n p k hn hp hk]
