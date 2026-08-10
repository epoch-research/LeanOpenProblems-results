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

namespace Scratch

def delta (m : ℕ) : ℕ := m*m - (Icc 1 m).sum (fun k => k * (m / k))


def num (n : ℕ) : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k

def den (n : ℕ) : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

lemma num_ne_zero (n : ℕ) : num n ≠ 0 := by
  unfold num
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hj0 : j ≠ 0 := (Nat.ne_of_gt (mem_Icc.mp hj).1)
  have hk0 : k ≠ 0 := (Nat.ne_of_gt (mem_Icc.mp hk).1)
  simpa [Nat.gcd_eq_zero_iff, hj0, hk0]

lemma den_ne_zero (n : ℕ) : den n ≠ 0 := by
  unfold den
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact pow_ne_zero _ (Nat.factorial_ne_zero _)

lemma factorization_num (n p : ℕ) :
    (num n).factorization p =
      (Icc 1 n).sum fun j => (Icc 1 n).sum fun k => min (j.factorization p) (k.factorization p) := by
  unfold num
  rw [Nat.factorization_prod_apply]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.factorization_prod_apply]
    · apply Finset.sum_congr rfl
      intro k hk
      have hj0 : j ≠ 0 := (Nat.ne_of_gt (mem_Icc.mp hj).1)
      have hk0 : k ≠ 0 := (Nat.ne_of_gt (mem_Icc.mp hk).1)
      rw [Nat.factorization_gcd hj0 hk0]
      simp [Finsupp.inf_apply]
    · intro k hk
      have hj0 : j ≠ 0 := (Nat.ne_of_gt (mem_Icc.mp hj).1)
      have hk0 : k ≠ 0 := (Nat.ne_of_gt (mem_Icc.mp hk).1)
      simpa [Nat.gcd_eq_zero_iff, hj0, hk0]
  · intro j hj
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have hj0 : j ≠ 0 := (Nat.ne_of_gt (mem_Icc.mp hj).1)
    have hk0 : k ≠ 0 := (Nat.ne_of_gt (mem_Icc.mp hk).1)
    simpa [Nat.gcd_eq_zero_iff, hj0, hk0]

lemma factorization_den (n p : ℕ) :
    (den n).factorization p =
      (Icc 1 n).sum fun k => k * ((Nat.factorial (n / k)).factorization p) := by
  unfold den
  rw [Nat.factorization_prod_apply]
  · apply Finset.sum_congr rfl
    intro k hk
    simp [Nat.factorization_pow]
  · intro k hk
    exact pow_ne_zero _ (Nat.factorial_ne_zero _)


lemma min_factorization_eq_card_common {n p j k : ℕ} (hp : p.Prime)
    (hj : j ∈ Icc 1 n) (hk : k ∈ Icc 1 n) :
    min (j.factorization p) (k.factorization p) =
      #{i ∈ Icc 1 n | p ^ i ∣ j ∧ p ^ i ∣ k} := by
  have hj0 : j ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hj).1
  have hk0 : k ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hk).1
  have hcard : #(Icc 1 (min (j.factorization p) (k.factorization p))) =
      min (j.factorization p) (k.factorization p) := by simp [Nat.card_Icc]
  rw [← hcard]
  congr 1
  ext i
  simp only [mem_Icc, mem_filter]
  constructor
  · intro hi
    have hi1 : 1 ≤ i := hi.1
    have hifj : i ≤ j.factorization p := le_trans hi.2 (min_le_left _ _)
    have hifk : i ≤ k.factorization p := le_trans hi.2 (min_le_right _ _)
    have hin : i ≤ n := by
      have hlt : i < j := lt_of_le_of_lt hifj (Nat.factorization_lt p hj0)
      exact le_trans (Nat.le_of_lt hlt) (mem_Icc.mp hj).2
    exact ⟨⟨hi1, hin⟩, (hp.pow_dvd_iff_le_factorization hj0).2 hifj,
      (hp.pow_dvd_iff_le_factorization hk0).2 hifk⟩
  · rintro ⟨⟨hi1, hin⟩, hdj, hdk⟩
    exact ⟨hi1, le_min ((hp.pow_dvd_iff_le_factorization hj0).1 hdj)
      ((hp.pow_dvd_iff_le_factorization hk0).1 hdk)⟩

lemma Icc_filter_dvd_card_eq_div (n q : ℕ) : #{x ∈ Icc 1 n | q ∣ x} = n / q := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div n q]
  congr 1


lemma card_filter_eq_sum_ite {α : Type*} [DecidableEq α] (s : Finset α) (P : α → Prop)
    [DecidablePred P] : #(s.filter P) = ∑ x ∈ s, (if P x then 1 else 0) := by
  exact (sum_boole P s (R := ℕ)).symm


lemma sum_card_common_pow (n p : ℕ) :
    (Icc 1 n).sum (fun j => (Icc 1 n).sum fun k =>
      #{i ∈ Icc 1 n | p ^ i ∣ j ∧ p ^ i ∣ k}) =
    (Icc 1 n).sum (fun i => (n / p ^ i) * (n / p ^ i)) := by
  classical
  calc
    (Icc 1 n).sum (fun j => (Icc 1 n).sum fun k =>
      #{i ∈ Icc 1 n | p ^ i ∣ j ∧ p ^ i ∣ k})
        = (Icc 1 n).sum (fun j => (Icc 1 n).sum fun k =>
            (Icc 1 n).sum fun i => if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          rw [card_filter_eq_sum_ite]
    _ = (Icc 1 n).sum (fun j => (Icc 1 n).sum fun i => (Icc 1 n).sum fun k =>
            if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_comm]
    _ = (Icc 1 n).sum (fun i => (Icc 1 n).sum fun j => (Icc 1 n).sum fun k =>
            if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) := by
          rw [Finset.sum_comm]
    _ = (Icc 1 n).sum (fun i => (n / p ^ i) * (n / p ^ i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          let q := p ^ i
          have hj : (Icc 1 n).sum (fun j => if q ∣ j then 1 else 0) = n / q := by
            rw [← card_filter_eq_sum_ite, Icc_filter_dvd_card_eq_div]
          have hk : (Icc 1 n).sum (fun k => if q ∣ k then 1 else 0) = n / q := by
            rw [← card_filter_eq_sum_ite, Icc_filter_dvd_card_eq_div]
          calc
            (Icc 1 n).sum (fun j => (Icc 1 n).sum fun k => if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0)
                = (Icc 1 n).sum (fun j => (if q ∣ j then 1 else 0) *
                    ((Icc 1 n).sum fun k => if q ∣ k then 1 else 0)) := by
                  apply Finset.sum_congr rfl
                  intro j hjmem
                  by_cases hjdvd : q ∣ j
                  · simp [q, hjdvd]
                  · simp [q, hjdvd]
            _ = ((Icc 1 n).sum (fun j => if q ∣ j then 1 else 0)) *
                    ((Icc 1 n).sum fun k => if q ∣ k then 1 else 0) := by
                  rw [Finset.sum_mul]
            _ = (n / p ^ i) * (n / p ^ i) := by
                  simpa [q] using congrArg (fun x : ℕ => x * x) (Icc_filter_dvd_card_eq_div n (p ^ i))


lemma factorization_num_formula (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (num n).factorization p = (Icc 1 n).sum (fun i => (n / p ^ i) * (n / p ^ i)) := by
  rw [factorization_num]
  calc
    (Icc 1 n).sum (fun j => (Icc 1 n).sum fun k => min (j.factorization p) (k.factorization p))
        = (Icc 1 n).sum (fun j => (Icc 1 n).sum fun k =>
            #{i ∈ Icc 1 n | p ^ i ∣ j ∧ p ^ i ∣ k}) := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          exact min_factorization_eq_card_common hp hj hk
    _ = (Icc 1 n).sum (fun i => (n / p ^ i) * (n / p ^ i)) := sum_card_common_pow n p



lemma Ico_one_succ_eq_Icc (n : ℕ) : Ico 1 (n+1) = Icc 1 n := by
  ext x
  simp only [mem_Ico, mem_Icc]
  omega

lemma factorial_factorization_sum_Icc (n m : ℕ) {p : ℕ} (hp : p.Prime) (hmn : m ≤ n) :
    (Nat.factorial m).factorization p = (Icc 1 n).sum (fun i => m / p ^ i) := by
  have hlog : Nat.log p m < n + 1 := by
    exact lt_of_le_of_lt ((Nat.log_le_self p m).trans hmn) (Nat.lt_succ_self n)
  rw [Nat.factorization_factorial hp hlog]
  rw [Ico_one_succ_eq_Icc]

lemma factorization_den_formula (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (den n).factorization p =
      (Icc 1 n).sum (fun i => (Icc 1 n).sum fun k => k * ((n / p ^ i) / k)) := by
  rw [factorization_den]
  calc
    (Icc 1 n).sum (fun k => k * ((Nat.factorial (n / k)).factorization p))
        = (Icc 1 n).sum (fun k => k * ((Icc 1 n).sum fun i => (n / k) / p ^ i)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [factorial_factorization_sum_Icc n (n/k) hp (Nat.div_le_self n k)]
    _ = (Icc 1 n).sum (fun k => (Icc 1 n).sum fun i => k * ((n / k) / p ^ i)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
    _ = (Icc 1 n).sum (fun i => (Icc 1 n).sum fun k => k * ((n / p ^ i) / k)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro k hk
          rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
          rw [mul_comm k (p ^ i)]










lemma sum_le_mul_self (m : ℕ) : (Icc 1 m).sum (fun k => k * (m / k)) ≤ m * m := by
  calc
    (Icc 1 m).sum (fun k => k * (m / k)) ≤ (Icc 1 m).sum (fun _ => m) := by
      apply Finset.sum_le_sum
      intro k hk
      exact Nat.mul_div_le m k
    _ = m * m := by
      simp [Nat.card_Icc]

lemma sum_extend_eq (n m : ℕ) (hmn : m ≤ n) :
    (Icc 1 n).sum (fun k => k * (m / k)) = (Icc 1 m).sum (fun k => k * (m / k)) := by
  symm
  apply Finset.sum_subset
  · intro k hk
    exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1, le_trans (mem_Icc.mp hk).2 hmn⟩
  · intro k hkn hkm
    have hmk : m < k := by
      by_contra h
      exact hkm (mem_Icc.mpr ⟨(mem_Icc.mp hkn).1, le_of_not_gt h⟩)
    rw [Nat.div_eq_of_lt hmk, mul_zero]

lemma sum_le_mul_self_extend (n m : ℕ) (hmn : m ≤ n) :
    (Icc 1 n).sum (fun k => k * (m / k)) ≤ m * m := by
  rw [sum_extend_eq n m hmn]
  exact sum_le_mul_self m

lemma den_factorization_le_num_factorization (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (den n).factorization p ≤ (num n).factorization p := by
  rw [factorization_den_formula n hp, factorization_num_formula n hp]
  apply Finset.sum_le_sum
  intro i hi
  exact sum_le_mul_self_extend n (n / p ^ i) (Nat.div_le_self n (p ^ i))

lemma den_dvd_num (n : ℕ) : den n ∣ num n := by
  rw [← Nat.factorization_prime_le_iff_dvd (den_ne_zero n) (num_ne_zero n)]
  intro p hp
  exact den_factorization_le_num_factorization n hp

lemma term_eq_delta (n m : ℕ) (hmn : m ≤ n) :
    m * m - (Icc 1 n).sum (fun k => k * (m / k)) = delta m := by
  unfold delta
  rw [sum_extend_eq n m hmn]

lemma quotient_factorization_formula (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (num n / den n).factorization p = (Icc 1 n).sum (fun i => delta (n / p ^ i)) := by
  have hle : ∀ i ∈ Icc 1 n,
      (Icc 1 n).sum (fun k => k * ((n / p ^ i) / k)) ≤ (n / p ^ i) * (n / p ^ i) := by
    intro i hi
    exact sum_le_mul_self_extend n (n / p ^ i) (Nat.div_le_self n (p ^ i))
  rw [Nat.factorization_div (den_dvd_num n)]
  rw [Finsupp.coe_tsub, Pi.sub_apply]
  rw [factorization_num_formula n hp, factorization_den_formula n hp]
  rw [← Finset.sum_tsub_distrib (s := Icc 1 n) hle]
  apply Finset.sum_congr rfl
  intro i hi
  exact term_eq_delta n (n / p ^ i) (Nat.div_le_self n (p ^ i))

lemma delta_eq_zero_of_lt_three {m : ℕ} (hm : m < 3) : delta m = 0 := by
  interval_cases m <;> decide

lemma delta_pos_of_three_le {m : ℕ} (hm : 3 ≤ m) : 0 < delta m := by
  unfold delta
  have hle := sum_le_mul_self m
  rw [Nat.sub_pos_iff_lt]
  -- Need strict: sum < m*m
  calc
    (Icc 1 m).sum (fun k => k * (m / k)) < (Icc 1 m).sum (fun _ => m) := by
      apply Finset.sum_lt_sum
      · intro k hk
        exact Nat.mul_div_le m k
      · refine ⟨m-1, ?_, ?_⟩
        · simp only [mem_Icc]
          omega
        · rw [Nat.lt_iff_le_and_ne]
          constructor
          · exact Nat.mul_div_le m (m-1)
          · intro h
            have hpos : 0 < m - 1 := by omega
            have hdiv : m / (m - 1) = 1 := by
              apply Nat.div_eq_of_lt_le
              · omega
              · omega
            rw [hdiv, mul_one] at h
            omega
    _ = m * m := by
      simp [Nat.card_Icc]

lemma delta_pos_iff {m : ℕ} : 0 < delta m ↔ 3 ≤ m := by
  constructor
  · intro h
    by_contra hm
    have : m < 3 := by omega
    rw [delta_eq_zero_of_lt_three this] at h
    omega
  · exact delta_pos_of_three_le

lemma sum_pos_iff_exists_pos {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    0 < s.sum f ↔ ∃ x ∈ s, 0 < f x := by
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    have hzero : s.sum f = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact Nat.eq_zero_of_le_zero (hno x hx)
    omega
  · rintro ⟨x, hx, hfx⟩
    exact lt_of_lt_of_le hfx (Finset.single_le_sum (fun y hy => Nat.zero_le (f y)) hx)

lemma quotient_ne_zero (n : ℕ) : num n / den n ≠ 0 := by
  have hdvd := den_dvd_num n
  have hdenpos : 0 < den n := Nat.pos_of_ne_zero (den_ne_zero n)
  have hle : den n ≤ num n := Nat.le_of_dvd (Nat.pos_of_ne_zero (num_ne_zero n)) hdvd
  exact Nat.ne_of_gt (Nat.div_pos hle hdenpos)

lemma quotient_factorization_pos_iff (n : ℕ) {p : ℕ} (hp : p.Prime) :
    0 < (num n / den n).factorization p ↔ p ≤ n / 3 := by
  rw [quotient_factorization_formula n hp]
  rw [sum_pos_iff_exists_pos]
  constructor
  · rintro ⟨i, hi, hpos⟩
    rw [delta_pos_iff] at hpos
    have hi_ge : 1 ≤ i := (mem_Icc.mp hi).1
    have hp2 : 2 ≤ p := hp.two_le
    have hp_pow : p ≤ p ^ i := by
      cases i with
      | zero => omega
      | succ t =>
          simpa [pow_succ, mul_comm] using Nat.le_mul_of_pos_right p (pow_pos hp.pos t)
    have hle : p * 3 ≤ n := by
      calc
        p * 3 ≤ (p ^ i) * (n / p ^ i) := by
          exact Nat.mul_le_mul hp_pow hpos
        _ ≤ n := Nat.mul_div_le n (p ^ i)
    exact Nat.le_div_iff_mul_le (by norm_num : 0 < 3) |>.2 (by simpa [mul_comm] using hle)
  · intro hp_le
    refine ⟨1, ?_, ?_⟩
    · have hp_pos : 0 < p := hp.pos
      have : 1 ≤ n := by omega
      simp [this]
    · rw [delta_pos_iff]
      have hmul : p * 3 ≤ n := by
        exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).1 hp_le
      have hmul' : 3 * p ≤ n := by simpa [mul_comm] using hmul
      simpa using (Nat.le_div_iff_mul_le hp.pos).2 hmul'

end Scratch

-- Note: `(m.factorization p)` is the exponent of p in the prime factorization of m,
-- corresponding to ordp(m, p).

/--
oeis_a129365_conjecture_B: If p is a prime then p|a(n) if and only if p <= n/3.
Note: Since `a n` is non-zero for $n > 0$, $p \mid a n$ iff $p$ is in the factorization of $a n$.
-/
theorem oeis_a129365_conjecture_B (n p : ℕ) (hn : 0 < n) (hp : Nat.Prime p) :
  p ∣ a n ↔ p ≤ n / 3 := by
  have ha : a n = Scratch.num n / Scratch.den n := by
    unfold a Scratch.num Scratch.den
    rfl
  rw [ha]
  rw [hp.dvd_iff_one_le_factorization (Scratch.quotient_ne_zero n)]
  change 0 < (Scratch.num n / Scratch.den n).factorization p ↔ p ≤ n / 3
  exact Scratch.quotient_factorization_pos_iff n hp
