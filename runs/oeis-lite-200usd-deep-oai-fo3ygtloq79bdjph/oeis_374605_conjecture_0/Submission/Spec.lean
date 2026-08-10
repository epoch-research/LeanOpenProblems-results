import FormalConjectures.Util.ProblemImports
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.style.moduleDocstring false
set_option linter.all false

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

private noncomputable def tsumnd (n j : ℕ) : ℚ :=
  ((Nat.choose n j : ℚ) ^ 2 * (Nat.choose (n + 1) (2 * j) : ℚ) *
      (Nat.choose (n + j) j : ℚ)) /
    ((Nat.choose (2 * n) j : ℚ) ^ 2 * (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ))

private def tpref (n : ℕ) : ℕ :=
  Nat.choose (3 * n) n * (Nat.choose (2 * n) n) ^ 2

private noncomputable def trhs (n : ℕ) : ℚ :=
  (tpref n : ℚ) *
    Finset.sum (Finset.range (n + 1)) (fun j => tsumnd n j)

private def tstmt (n : ℕ) : Prop :=
  ((a n : ℕ) : ℚ) = trhs n

private lemma mod_eq_sub_of_between (p m : ℕ) (hpm : p ≤ m) (hmp : m < 2 * p) :
    m % p = m - p := by
  rw [← Nat.sub_add_cancel hpm]
  rw [Nat.add_mod_right]
  rw [Nat.mod_eq_of_lt]
  · omega
  · omega

private def istmt (n : ℕ) : Prop :=
  (3 * n + 1) * a n = (n + 1) *
    Finset.sum (Finset.range (n + 1)) (fun j =>
      if 2 * j ≤ n + 1 then
        Nat.choose (3 * n + 1) (n + 1 - 2 * j) * Nat.choose (n + j) j *
          (Nat.choose (2 * n - j) n) ^ 2
      else 0)

private lemma tt_intQ (n j : ℕ) (hj : 2 * j ≤ n + 1) :
    ((Nat.choose (3 * n) n * (Nat.choose (2 * n) n) ^ 2 : ℕ) : ℚ) * tsumnd n j =
      ((n + 1 : ℕ) : ℚ) / ((3 * n + 1 : ℕ) : ℚ) *
        ((Nat.choose (3 * n + 1) (n + 1 - 2 * j) : ℚ) *
          (Nat.choose (n + j) j : ℚ) *
          (Nat.choose (2 * n - j) n : ℚ) ^ 2) := by
  unfold tsumnd
  have hjn : j ≤ n := by omega
  have h2j_n1 : 2 * j ≤ n + 1 := hj
  have h3n : n ≤ 3 * n := by omega
  have h2n : n ≤ 2 * n := by omega
  have hj2n : j ≤ 2 * n := by omega
  have hj_nj : j ≤ n + j := by omega
  have h2j_top : 2 * j ≤ 2 * n + 2 * j := by omega
  have hm_top : n + 1 - 2 * j ≤ 3 * n + 1 := by omega
  have hn_top2 : n ≤ 2 * n - j := by omega
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [Nat.cast_choose (K := ℚ) h3n]
  rw [Nat.cast_choose (K := ℚ) h2n]
  rw [Nat.cast_choose (K := ℚ) hjn]
  rw [Nat.cast_choose (K := ℚ) h2j_n1]
  rw [Nat.cast_choose (K := ℚ) hj_nj]
  rw [Nat.cast_choose (K := ℚ) hj2n]
  rw [Nat.cast_choose (K := ℚ) h2j_top]
  rw [Nat.cast_choose (K := ℚ) hm_top]
  rw [Nat.cast_choose (K := ℚ) hn_top2]
  have hsubA : 3 * n - n = 2 * n := by omega
  have hsubB : 2 * n - n = n := by omega
  have hsubC : 2 * n + 2 * j - 2 * j = 2 * n := by omega
  have hsubD : 3 * n + 1 - (n + 1 - 2 * j) = 2 * n + 2 * j := by omega
  have hsubE : 2 * n - j - n = n - j := by omega
  have hfac : ∀ m : ℕ, ((m.factorial : ℕ) : ℚ) ≠ 0 := fun m => by exact_mod_cast (Nat.factorial_pos m).ne'
  field_simp [hfac]
  rw [hsubC, hsubD, hsubE, hsubA, hsubB]
  rw [Nat.factorial_succ n]
  rw [show (3 * n + 1).factorial = (3 * n + 1) * (3 * n).factorial by
    rw [show 3 * n + 1 = (3 * n) + 1 by omega, Nat.factorial_succ]]
  norm_num [Nat.cast_mul, Nat.cast_add]
  ring_nf

private lemma tt_intIte (n j : ℕ) :
    ((Nat.choose (3 * n) n * (Nat.choose (2 * n) n) ^ 2 : ℕ) : ℚ) * tsumnd n j =
      ((n + 1 : ℕ) : ℚ) / ((3 * n + 1 : ℕ) : ℚ) *
        (if 2 * j ≤ n + 1 then
          ((Nat.choose (3 * n + 1) (n + 1 - 2 * j) * Nat.choose (n + j) j *
            (Nat.choose (2 * n - j) n) ^ 2 : ℕ) : ℚ)
        else 0) := by
  by_cases hj : 2 * j ≤ n + 1
  · simp [hj]
    simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc] using tt_intQ n j hj
  · have hz : Nat.choose (n + 1) (2 * j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [tsumnd, hj, hz]

private lemma trhs_intQ (n : ℕ) :
    trhs n =
      ((n + 1 : ℕ) : ℚ) / ((3 * n + 1 : ℕ) : ℚ) *
        ((Finset.sum (Finset.range (n + 1)) (fun j =>
          if 2 * j ≤ n + 1 then
            Nat.choose (3 * n + 1) (n + 1 - 2 * j) * Nat.choose (n + j) j *
              (Nat.choose (2 * n - j) n) ^ 2
          else 0) : ℕ) : ℚ) := by
  unfold trhs tpref
  rw [Finset.mul_sum]
  calc
    (∑ x ∈ Finset.range (n + 1),
        ((Nat.choose (3 * n) n * Nat.choose (2 * n) n ^ 2 : ℕ) : ℚ) * tsumnd n x)
        = ∑ x ∈ Finset.range (n + 1),
            ((n + 1 : ℕ) : ℚ) / ((3 * n + 1 : ℕ) : ℚ) *
              (if 2 * x ≤ n + 1 then
                ((Nat.choose (3 * n + 1) (n + 1 - 2 * x) * Nat.choose (n + x) x *
                  (Nat.choose (2 * n - x) n) ^ 2 : ℕ) : ℚ)
              else 0) := by
          exact Finset.sum_congr rfl (fun x hx => tt_intIte n x)
    _ = ((n + 1 : ℕ) : ℚ) / ((3 * n + 1 : ℕ) : ℚ) *
        (∑ x ∈ Finset.range (n + 1),
              (if 2 * x ≤ n + 1 then
                ((Nat.choose (3 * n + 1) (n + 1 - 2 * x) * Nat.choose (n + x) x *
                  (Nat.choose (2 * n - x) n) ^ 2 : ℕ) : ℚ)
              else 0)) := by rw [Finset.mul_sum]
    _ = ((n + 1 : ℕ) : ℚ) / ((3 * n + 1 : ℕ) : ℚ) *
        ((Finset.sum (Finset.range (n + 1)) (fun j =>
          if 2 * j ≤ n + 1 then
            Nat.choose (3 * n + 1) (n + 1 - 2 * j) * Nat.choose (n + j) j *
              (Nat.choose (2 * n - j) n) ^ 2
          else 0) : ℕ) : ℚ) := by
          congr 1
          rw [Nat.cast_sum]
          exact Finset.sum_congr rfl (fun x hx => by by_cases h : 2 * x ≤ n + 1 <;> simp [h, Nat.cast_mul, Nat.cast_pow])

private lemma it_of_tid (n : ℕ)
    (hId : tstmt n) : istmt n := by
  unfold tstmt at hId
  unfold istmt
  have hR := trhs_intQ n
  rw [hR] at hId
  have hden : ((3 * n + 1 : ℕ) : ℚ) ≠ 0 := by
    norm_num
    linarith
  have hQ : (((3 * n + 1) * a n : ℕ) : ℚ) =
      (((n + 1) * Finset.sum (Finset.range (n + 1)) (fun j =>
      if 2 * j ≤ n + 1 then
        Nat.choose (3 * n + 1) (n + 1 - 2 * j) * Nat.choose (n + j) j *
          (Nat.choose (2 * n - j) n) ^ 2
      else 0) : ℕ) : ℚ) := by
    rw [Nat.cast_mul, Nat.cast_mul, hId]
    field_simp [hden]
  exact_mod_cast hQ

private lemma prime_dvd_choose_three_n_one (p n j : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hnlow : (2 * p + 3) / 3 ≤ n) (hnhigh : n ≤ p - 1)
    (hj : 2 * j ≤ n + 1) (hn1lt : n + 1 < p) (hnjlt : n + j < p) :
    p ∣ Nat.choose (3 * n + 1) (n + 1 - 2 * j) := by
  let m := n + 1 - 2 * j
  have hmp : m < p := by omega
  have hNpos : 3 * n + 1 ≠ 0 := by omega
  have hNlt : 3 * n + 1 < p ^ 2 := by nlinarith [hp5, hnhigh]
  have hlog : Nat.log p (3 * n + 1) < 2 := Nat.log_lt_of_lt_pow hNpos hNlt
  have hmle : m ≤ 3 * n + 1 := by omega
  rw [hp.dvd_iff_one_le_factorization (Nat.choose_ne_zero hmle)]
  rw [Nat.factorization_choose (p := p) (n := 3 * n + 1) (k := m) (b := 2) hp hmle hlog]
  apply Nat.succ_le_iff.mp
  apply Finset.card_pos.2
  refine ⟨1, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · omega
  · have hm_mod : m % p = m := Nat.mod_eq_of_lt hmp
    have hsub : 3 * n + 1 - m = 2 * n + 2 * j := by omega
    have hp_le_rest : p ≤ 2 * n + 2 * j := by omega
    have hrest_lt : 2 * n + 2 * j < 2 * p := by omega
    have hrest_mod : (2 * n + 2 * j) % p = 2 * n + 2 * j - p :=
      mod_eq_sub_of_between p (2 * n + 2 * j) hp_le_rest hrest_lt
    rw [pow_one, hm_mod, hsub, hrest_mod]
    omega

private lemma prime_dvd_extra_factor (p n j : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hnlow : (2 * p + 3) / 3 ≤ n) (hnhigh : n ≤ p - 1) (hj : 2 * j ≤ n + 1) :
    p ∣ (n + 1) * Nat.choose (3 * n + 1) (n + 1 - 2 * j) * Nat.choose (n + j) j := by
  by_cases hp_n1 : p ∣ n + 1
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp_n1 _) _
  · have hnp : n < p := by omega
    have hn1le : n + 1 ≤ p := by omega
    have hn1lt : n + 1 < p := lt_of_le_of_ne hn1le (by intro h; apply hp_n1; exact ⟨1, by omega⟩)
    have hjp : j < p := by omega
    by_cases hcross : p ≤ n + j
    · have hdiv : p ∣ Nat.choose (n + j) j := hp.dvd_choose hjp (by omega) hcross
      exact dvd_mul_of_dvd_right hdiv ((n + 1) * Nat.choose (3 * n + 1) (n + 1 - 2 * j))
    · have hnjlt : n + j < p := by omega
      have hdiv : p ∣ Nat.choose (3 * n + 1) (n + 1 - 2 * j) :=
        prime_dvd_choose_three_n_one p n j hp hp5 hnlow hnhigh hj hn1lt hnjlt
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdiv (n+1)) (Nat.choose (n+j) j)

private lemma prime_dvd_choose_two_n_sub_j (p n j : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hnlow : (2 * p + 3) / 3 ≤ n) (hnhigh : n ≤ p - 1) (hj : 2 * j ≤ n + 1) :
    p ∣ Nat.choose (2 * n - j) n := by
  have hnp : n < p := by omega
  have htop : p ≤ 2 * n - j := by omega
  have hdiff : (2 * n - j) - n < p := by omega
  exact hp.dvd_choose (a := n) (b := 2 * n - j) hnp hdiff htop

private lemma pow_three_dvd_integer_transform_core (p n j : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hnlow : (2 * p + 3) / 3 ≤ n) (hnhigh : n ≤ p - 1) (hsurv : 2 * j ≤ n + 1) :
    p ^ 3 ∣ (n + 1) * (Nat.choose (3 * n + 1) (n + 1 - 2 * j) * Nat.choose (n + j) j *
        (Nat.choose (2 * n - j) n) ^ 2) := by
  obtain ⟨u, hu⟩ := prime_dvd_extra_factor p n j hp hp5 hnlow hnhigh hsurv
  obtain ⟨v, hv⟩ := prime_dvd_choose_two_n_sub_j p n j hp hp5 hnlow hnhigh hsurv
  use u * v ^ 2
  rw [show (n + 1) * ((3 * n + 1).choose (n + 1 - 2 * j) * (n + j).choose j * (2 * n - j).choose n ^ 2)
      = ((n + 1) * (3 * n + 1).choose (n + 1 - 2 * j) * (n + j).choose j) * ((2 * n - j).choose n)^2 by ring]
  rw [hu, hv]
  ring

private lemma main_of_int (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hnlow : (2 * p + 3) / 3 ≤ n) (hnhigh : n ≤ p - 1)
    (hId : istmt n) :
    (p ^ 3 : ℕ) ∣ a n := by
  unfold istmt at hId
  have hterms : p ^ 3 ∣ (n + 1) *
      Finset.sum (Finset.range (n + 1)) (fun j =>
        if hsurv : 2 * j ≤ n + 1 then
          Nat.choose (3 * n + 1) (n + 1 - 2 * j) * Nat.choose (n + j) j *
            (Nat.choose (2 * n - j) n) ^ 2
        else 0) := by
    rw [Finset.mul_sum]
    apply Finset.dvd_sum
    intro j hj
    by_cases hsurv : 2 * j ≤ n + 1
    · simp [hsurv]
      exact pow_three_dvd_integer_transform_core p n j hp hp5 hnlow hnhigh hsurv
    · simp [hsurv]
  have hmul : p ^ 3 ∣ (3 * n + 1) * a n := by
    rwa [hId]
  have hnot : ¬ p ∣ 3 * n + 1 := by
    intro hdvd
    obtain ⟨t, ht⟩ := hdvd
    have hp_pos : 0 < p := hp.pos
    have hlt3 : 3 * n + 1 < 3 * p := by omega
    have hgt2 : 2 * p < 3 * n + 1 := by omega
    rw [ht] at hlt3 hgt2
    rw [mul_comm 3 p] at hlt3
    rw [mul_comm 2 p] at hgt2
    have htlt : t < 3 := Nat.lt_of_mul_lt_mul_left hlt3
    have htwo_lt_t : 2 < t := (Nat.mul_lt_mul_left hp_pos).mp hgt2
    omega
  have hcop : Nat.Coprime (p ^ 3) (3 * n + 1) := (hp.coprime_iff_not_dvd.mpr hnot).pow_left 3
  exact hcop.dvd_of_dvd_mul_left hmul

open scoped BigOperators
open Finset

set_option maxHeartbeats 300000

namespace P

private noncomputable def rp (x : ℚ) (k : ℕ) : ℚ :=
  ∏ i ∈ Finset.range k, (x + (i : ℚ))

@[simp] lemma rp_zero (x : ℚ) : rp x 0 = 1 := by
  simp [rp]

private lemma rp_succ (x : ℚ) (k : ℕ) : rp x (k + 1) = rp x k * (x + k) := by
  simp [rp, Finset.prod_range_succ, mul_comm]

private noncomputable def pfF (a b c : ℚ) (n k : ℕ) : ℚ :=
  rp (-(n : ℚ)) k * rp a k * rp b k /
    (rp c k * rp (1 + a + b - c - (n : ℚ)) k * (Nat.factorial k : ℚ))

private noncomputable def pfRho (a b c : ℚ) (n : ℕ) : ℚ :=
  ((c - a + n) * (c - b + n)) / ((c + n) * (c - a - b + n))

private noncomputable def pfR (a b c : ℚ) (n k : ℕ) : ℚ :=
  (k : ℚ) * (c + k - 1) * (a + b - c + k - n) /
    ((c + n) * ((k : ℚ) - n - 1) * (a + b - c - n))

private noncomputable def pfG (a b c : ℚ) (n k : ℕ) : ℚ :=
  pfR a b c n k * pfF a b c n k

private noncomputable def pfNQuotRat (a b c N K : ℚ) : ℚ :=
  (-N - 1) * (a + b - c + K - N) / ((K - N - 1) * (a + b - c - N))

private noncomputable def pfRhoRat (a b c N : ℚ) : ℚ :=
  ((c - a + N) * (c - b + N)) / ((c + N) * (c - a - b + N))

private noncomputable def pfRRat (a b c N K : ℚ) : ℚ :=
  K * (c + K - 1) * (a + b - c + K - N) /
    ((c + N) * (K - N - 1) * (a + b - c - N))

private noncomputable def pfKQuotRat (a b c N K : ℚ) : ℚ :=
  ((-N + K) * (a + K) * (b + K)) /
    ((c + K) * (1 + a + b - c - N + K) * (K + 1))


private theorem pfRRat_succ_mul_pfKQuotRat (a b c N K : ℚ)
    (hcn : c + N ≠ 0)
    (hkn : K - N ≠ 0)
    (hd : a + b - c - N ≠ 0)
    (hck : c + K ≠ 0)
    (hdk : 1 + a + b - c - N + K ≠ 0)
    (hk1 : K + 1 ≠ 0) :
    pfRRat a b c N (K + 1) * pfKQuotRat a b c N K =
      (a + K) * (b + K) / ((c + N) * (a + b - c - N)) := by
  unfold pfRRat pfKQuotRat
  have hkn' : K + 1 - N - 1 ≠ 0 := by
    intro h
    apply hkn
    linarith
  field_simp [hcn, hkn, hkn', hd, hck, hdk, hk1]
  ring

private theorem pf_gosper_certificate_reduced_rat (a b c N K : ℚ)
    (hcn : c + N ≠ 0)
    (hcabn : c - a - b + N ≠ 0)
    (hkn1 : K - N - 1 ≠ 0)
    (hd : a + b - c - N ≠ 0) :
    pfNQuotRat a b c N K - pfRhoRat a b c N =
      (a + K) * (b + K) / ((c + N) * (a + b - c - N)) -
        pfRRat a b c N K := by
  unfold pfNQuotRat pfRhoRat pfRRat
  field_simp [hcn, hcabn, hkn1, hd]
  ring

private theorem pf_gosper_certificate_core_rat (a b c N K : ℚ)
    (hcn : c + N ≠ 0)
    (hcabn : c - a - b + N ≠ 0)
    (hkn1 : K - N - 1 ≠ 0)
    (hkn : K - N ≠ 0)
    (hd : a + b - c - N ≠ 0)
    (hck : c + K ≠ 0)
    (hdk : 1 + a + b - c - N + K ≠ 0)
    (hk1 : K + 1 ≠ 0) :
    pfNQuotRat a b c N K - pfRhoRat a b c N =
      pfRRat a b c N (K + 1) * pfKQuotRat a b c N K -
        pfRRat a b c N K := by
  rw [pfRRat_succ_mul_pfKQuotRat a b c N K hcn hkn hd hck hdk hk1]
  exact pf_gosper_certificate_reduced_rat a b c N K hcn hcabn hkn1 hd

private theorem pf_gosper_certificate_core_nat (a b c : ℚ) (m k : ℕ)
    (hcn : c + (m : ℚ) ≠ 0)
    (hcabn : c - a - b + (m : ℚ) ≠ 0)
    (hkn1 : (k : ℚ) - (m : ℚ) - 1 ≠ 0)
    (hkn : (k : ℚ) - (m : ℚ) ≠ 0)
    (hd : a + b - c - (m : ℚ) ≠ 0)
    (hck : c + (k : ℚ) ≠ 0)
    (hdk : 1 + a + b - c - (m : ℚ) + (k : ℚ) ≠ 0) :
    pfNQuotRat a b c (m : ℚ) (k : ℚ) - pfRho a b c m =
      pfR a b c m (k + 1) * pfKQuotRat a b c (m : ℚ) (k : ℚ) -
        pfR a b c m k := by
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  simpa [pfRho, pfR, pfRhoRat, pfRRat, Nat.cast_add, Nat.cast_one] using
    pf_gosper_certificate_core_rat a b c (m : ℚ) (k : ℚ)
      hcn hcabn hkn1 hkn hd hck hdk hk1

private theorem pfF_k_succ (a b c : ℚ) (n k : ℕ)
    (hc0 : rp c k ≠ 0)
    (hd0 : rp (1 + a + b - c - (n : ℚ)) k ≠ 0)
    (hck : c + (k : ℚ) ≠ 0)
    (hdk : 1 + a + b - c - (n : ℚ) + (k : ℚ) ≠ 0) :
    pfF a b c n (k + 1) =
      pfF a b c n k * pfKQuotRat a b c (n : ℚ) (k : ℚ) := by
  unfold pfF pfKQuotRat
  rw [rp_succ (-(n : ℚ)) k, rp_succ a k, rp_succ b k,
    rp_succ c k, rp_succ (1 + a + b - c - (n : ℚ)) k]
  rw [Nat.factorial_succ]
  have hkfac : ((Nat.factorial k : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos k).ne'
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp [hc0, hd0, hck, hdk, hkfac, hk1]
  simp only [Nat.cast_add, Nat.cast_mul]
  ring_nf

private lemma rp_sub_one_mul_last (x : ℚ) (k : ℕ) :
    rp (x - 1) k * (x + (k : ℚ) - 1) = (x - 1) * rp x k := by
  induction k with
  | zero => simp [rp]
  | succ k ih =>
      rw [rp_succ (x - 1) k, rp_succ x k]
      have hshift : x - 1 + (k : ℚ) = x + (k : ℚ) - 1 := by ring
      have hlast : x + ((k + 1 : ℕ) : ℚ) - 1 = x + (k : ℚ) := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      rw [hshift, hlast]
      calc
        rp (x - 1) k * (x + (k : ℚ) - 1) * (x + (k : ℚ)) =
            ((x - 1) * rp x k) * (x + (k : ℚ)) := by rw [ih]
        _ = (x - 1) * (rp x k * (x + (k : ℚ))) := by ring

private lemma rp_sub_one_eq_mul_div (x : ℚ) (k : ℕ)
    (_hx0 : x - 1 ≠ 0) (hxlast : x + (k : ℚ) - 1 ≠ 0) :
    rp (x - 1) k = rp x k * ((x - 1) / (x + (k : ℚ) - 1)) := by
  field_simp [hxlast]
  simpa [mul_comm, mul_left_comm, mul_assoc] using rp_sub_one_mul_last x k

private theorem pfF_n_succ (a b c : ℚ) (n k : ℕ)
    (hk : k ≤ n)
    (hc0 : rp c k ≠ 0)
    (hd0 : rp (1 + a + b - c - (n : ℚ)) k ≠ 0)
    (hdm0 : a + b - c - (n : ℚ) ≠ 0)
    (hdlast : a + b - c - (n : ℚ) + (k : ℚ) ≠ 0) :
    pfF a b c (n + 1) k =
      pfF a b c n k * pfNQuotRat a b c (n : ℚ) (k : ℚ) := by
  unfold pfF pfNQuotRat
  have hfac : ((Nat.factorial k : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos k).ne'
  have hneg0 : -(n : ℚ) - 1 ≠ 0 := by
    have hp : (0 : ℚ) < (n : ℚ) + 1 := by positivity
    linarith
  have hkn1 : (k : ℚ) - (n : ℚ) - 1 ≠ 0 := by
    have hle : (k : ℚ) ≤ (n : ℚ) := by exact_mod_cast hk
    linarith
  have hneglast : -(n : ℚ) + (k : ℚ) - 1 ≠ 0 := by
    convert hkn1 using 1 <;> ring
  have hneg :
      rp (-((n + 1 : ℕ) : ℚ)) k =
        rp (-(n : ℚ)) k * ((-(n : ℚ) - 1) / ((k : ℚ) - (n : ℚ) - 1)) := by
    have harg : -((n + 1 : ℕ) : ℚ) = -(n : ℚ) - 1 := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [harg]
    convert (rp_sub_one_eq_mul_div (-(n : ℚ)) k hneg0 hneglast) using 1 <;>
      ring
  have hden :
      rp (1 + a + b - c - ((n + 1 : ℕ) : ℚ)) k =
        rp (1 + a + b - c - (n : ℚ)) k *
          ((a + b - c - (n : ℚ)) / (a + b - c - (n : ℚ) + (k : ℚ))) := by
    have hx0 : (1 + a + b - c - (n : ℚ)) - 1 ≠ 0 := by
      convert hdm0 using 1 <;> ring
    have hxlast : (1 + a + b - c - (n : ℚ)) + (k : ℚ) - 1 ≠ 0 := by
      convert hdlast using 1 <;> ring
    have harg :
        1 + a + b - c - ((n + 1 : ℕ) : ℚ) =
          (1 + a + b - c - (n : ℚ)) - 1 := by
      norm_num [Nat.cast_add]
      ring
    rw [harg]
    convert (rp_sub_one_eq_mul_div (1 + a + b - c - (n : ℚ)) k hx0 hxlast) using 1 <;>
      ring
  rw [hneg, hden]
  field_simp [hc0, hd0, hfac, hneg0, hkn1, hdm0, hdlast]
  ring

private noncomputable def pfSum (a b c : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), pfF a b c n k

private noncomputable def pfClosed (a b c : ℚ) (n : ℕ) : ℚ :=
  rp (c - a) n * rp (c - b) n / (rp c n * rp (c - a - b) n)

private def pfRecHyp (a b c : ℚ) (n : ℕ) : Prop :=
  c + (n : ℚ) ≠ 0 ∧
  c - a - b + (n : ℚ) ≠ 0 ∧
  a + b - c - (n : ℚ) ≠ 0 ∧
  a + b - c ≠ 0 ∧
  (∀ k ≤ n, rp c k ≠ 0) ∧
  (∀ k ≤ n, rp (1 + a + b - c - (n : ℚ)) k ≠ 0) ∧
  rp (a + b - c - (n : ℚ)) n ≠ 0 ∧
  rp (c - a - b) n ≠ 0 ∧
  (∀ k < n,
    c + (k : ℚ) ≠ 0 ∧
    1 + a + b - c - (n : ℚ) + (k : ℚ) ≠ 0 ∧
    a + b - c - (n : ℚ) + (k : ℚ) ≠ 0)

private theorem pfClosed_succ (a b c : ℚ) (n : ℕ)
    (hc0 : rp c n ≠ 0)
    (hcab0 : rp (c - a - b) n ≠ 0)
    (hcn : c + (n : ℚ) ≠ 0)
    (hcabn : c - a - b + (n : ℚ) ≠ 0) :
    pfClosed a b c (n + 1) = pfRho a b c n * pfClosed a b c n := by
  unfold pfClosed pfRho
  rw [rp_succ (c - a) n, rp_succ (c - b) n, rp_succ c n, rp_succ (c - a - b) n]
  field_simp [hc0, hcab0, hcn, hcabn]

private theorem pfNQuotRat_diag (a b c N : ℚ)
    (hd : a + b - c - N ≠ 0) :
    pfNQuotRat a b c N N = (N + 1) * (a + b - c) / (a + b - c - N) := by
  unfold pfNQuotRat
  have hm1 : N - N - 1 ≠ 0 := by norm_num
  field_simp [hm1, hd]
  ring

private theorem pfKQuotRat_boundary (a b c N : ℚ)
    (hcn : c + N ≠ 0) (habc : a + b - c ≠ 0) (hN1 : N + 1 ≠ 0) :
    pfKQuotRat a b c (N + 1) N =
      -((a + N) * (b + N) / ((c + N) * (a + b - c) * (N + 1))) := by
  unfold pfKQuotRat
  have hdenK : 1 + a + b - c - (N + 1) + N ≠ 0 := by
    convert habc using 1 <;> ring
  field_simp [hcn, habc, hN1, hdenK]
  ring

private theorem pfRRat_diag (a b c N : ℚ)
    (hcn : c + N ≠ 0) (hd : a + b - c - N ≠ 0) :
    pfRRat a b c N N = - (N * (c + N - 1) * (a + b - c) /
      ((c + N) * (a + b - c - N))) := by
  unfold pfRRat
  have hm1 : N - N - 1 ≠ 0 := by norm_num
  field_simp [hcn, hd, hm1]
  ring

private theorem pf_boundary_core_simplified (a b c N : ℚ)
    (hcn : c + N ≠ 0)
    (hcabn : c - a - b + N ≠ 0)
    (hd : a + b - c - N ≠ 0)
    (habc : a + b - c ≠ 0)
    (hN1 : N + 1 ≠ 0) :
    (N + 1) * (a + b - c) / (a + b - c - N) -
        pfRhoRat a b c N +
        ((N + 1) * (a + b - c) / (a + b - c - N)) *
          (-((a + N) * (b + N) / ((c + N) * (a + b - c) * (N + 1)))) +
        (-(N * (c + N - 1) * (a + b - c) / ((c + N) * (a + b - c - N)))) = 0 := by
  unfold pfRhoRat
  field_simp [hcn, hcabn, hd, habc, hN1]
  ring

private theorem pf_boundary_core_rat (a b c N : ℚ)
    (hcn : c + N ≠ 0)
    (hcabn : c - a - b + N ≠ 0)
    (hd : a + b - c - N ≠ 0)
    (habc : a + b - c ≠ 0)
    (hN1 : N + 1 ≠ 0) :
    pfNQuotRat a b c N N - pfRhoRat a b c N +
        pfNQuotRat a b c N N * pfKQuotRat a b c (N + 1) N +
        pfRRat a b c N N = 0 := by
  rw [pfNQuotRat_diag a b c N hd,
    pfKQuotRat_boundary a b c N hcn habc hN1,
    pfRRat_diag a b c N hcn hd]
  exact pf_boundary_core_simplified a b c N hcn hcabn hd habc hN1

private theorem pfG_zero (a b c : ℚ) (n : ℕ) : pfG a b c n 0 = 0 := by
  unfold pfG pfR pfF
  simp

private theorem pf_gosper_boundary_top (a b c : ℚ) (n : ℕ)
    (hcn : c + (n : ℚ) ≠ 0)
    (hcabn : c - a - b + (n : ℚ) ≠ 0)
    (hd : a + b - c - (n : ℚ) ≠ 0)
    (habc : a + b - c ≠ 0)
    (hc0 : rp c n ≠ 0)
    (hd0 : rp (1 + a + b - c - (n : ℚ)) n ≠ 0)
    (hd0' : rp (a + b - c - (n : ℚ)) n ≠ 0) :
    pfF a b c (n + 1) n - pfRho a b c n * pfF a b c n n +
        pfF a b c (n + 1) (n + 1) + pfG a b c n n = 0 := by
  have hnle : n ≤ n := le_rfl
  have hnq := pfF_n_succ a b c n n hnle hc0 hd0 hd (by simpa using habc)
  have hd0'' : rp (1 + a + b - c - ((n + 1 : ℕ) : ℚ)) n ≠ 0 := by
    convert hd0' using 2
    norm_num [Nat.cast_add]
    ring
  have hdk'' : 1 + a + b - c - ((n + 1 : ℕ) : ℚ) + (n : ℚ) ≠ 0 := by
    convert habc using 1
    norm_num [Nat.cast_add]
    ring
  have hkq := pfF_k_succ a b c (n + 1) n hc0 hd0'' hcn hdk''
  have hN1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hcore := pf_boundary_core_rat a b c (n : ℚ) hcn hcabn hd habc hN1
  unfold pfG
  calc
    pfF a b c (n + 1) n - pfRho a b c n * pfF a b c n n +
        pfF a b c (n + 1) (n + 1) + pfR a b c n n * pfF a b c n n
        = pfF a b c n n * pfNQuotRat a b c (n : ℚ) (n : ℚ) -
            pfRho a b c n * pfF a b c n n +
            (pfF a b c n n * pfNQuotRat a b c (n : ℚ) (n : ℚ)) *
              pfKQuotRat a b c ((n + 1 : ℕ) : ℚ) (n : ℚ) +
            pfR a b c n n * pfF a b c n n := by
          rw [hkq]
          rw [hnq]
    _ = pfF a b c n n *
          (pfNQuotRat a b c (n : ℚ) (n : ℚ) - pfRho a b c n +
            pfNQuotRat a b c (n : ℚ) (n : ℚ) *
              pfKQuotRat a b c ((n + 1 : ℕ) : ℚ) (n : ℚ) +
            pfR a b c n n) := by ring
    _ = 0 := by
          have hcore' :
              pfNQuotRat a b c (n : ℚ) (n : ℚ) - pfRho a b c n +
                pfNQuotRat a b c (n : ℚ) (n : ℚ) *
                  pfKQuotRat a b c ((n + 1 : ℕ) : ℚ) (n : ℚ) +
                pfR a b c n n = 0 := by
            simpa [pfRho, pfR, pfRhoRat, pfRRat, Nat.cast_add, Nat.cast_one] using hcore
          rw [hcore']
          ring

/-- Generic summand telescoping step, but with the rational Gosper certificate supplied externally. -/
private theorem pf_gosper_telescoping_summand_of_cert (a b c : ℚ) (n k : ℕ)
    (hk : k < n)
    (hc0 : rp c k ≠ 0)
    (hd0 : rp (1 + a + b - c - (n : ℚ)) k ≠ 0)
    (hck : c + (k : ℚ) ≠ 0)
    (hdk : 1 + a + b - c - (n : ℚ) + (k : ℚ) ≠ 0)
    (hd : a + b - c - (n : ℚ) ≠ 0)
    (hdlast : a + b - c - (n : ℚ) + (k : ℚ) ≠ 0)
    (hcert : pfNQuotRat a b c (n : ℚ) (k : ℚ) - pfRho a b c n =
      pfR a b c n (k + 1) * pfKQuotRat a b c (n : ℚ) (k : ℚ) - pfR a b c n k) :
    pfF a b c (n + 1) k - pfRho a b c n * pfF a b c n k =
      pfG a b c n (k + 1) - pfG a b c n k := by
  have hk_le : k ≤ n := Nat.le_of_lt hk
  have hnq := pfF_n_succ a b c n k hk_le hc0 hd0 hd hdlast
  have hkq := pfF_k_succ a b c n k hc0 hd0 hck hdk
  unfold pfG
  calc
    pfF a b c (n + 1) k - pfRho a b c n * pfF a b c n k =
        pfF a b c n k * pfNQuotRat a b c (n : ℚ) (k : ℚ) -
          pfRho a b c n * pfF a b c n k := by rw [hnq]
    _ = pfF a b c n k *
          (pfNQuotRat a b c (n : ℚ) (k : ℚ) - pfRho a b c n) := by ring
    _ = pfF a b c n k *
          (pfR a b c n (k + 1) * pfKQuotRat a b c (n : ℚ) (k : ℚ) -
            pfR a b c n k) := by rw [hcert]
    _ = pfR a b c n (k + 1) * (pfF a b c n k * pfKQuotRat a b c (n : ℚ) (k : ℚ)) -
          pfR a b c n k * pfF a b c n k := by ring
    _ = pfR a b c n (k + 1) * pfF a b c n (k + 1) -
          pfR a b c n k * pfF a b c n k := by rw [← hkq]

/-- Pfaff step using externally supplied specialized Gosper certificates. -/
private theorem pfSum_succ_of_cert (a b c : ℚ) (n : ℕ) (h : pfRecHyp a b c n)
    (hcertAll : ∀ k < n,
      pfNQuotRat a b c (n : ℚ) (k : ℚ) - pfRho a b c n =
        pfR a b c n (k + 1) * pfKQuotRat a b c (n : ℚ) (k : ℚ) - pfR a b c n k) :
    pfSum a b c (n + 1) = pfRho a b c n * pfSum a b c n := by
  rcases h with ⟨hcn, hcabn, hd, habc, hcAll, hdAll, hd0top, hcab0, hlocal⟩
  have hboundary := pf_gosper_boundary_top a b c n hcn hcabn hd habc
    (hcAll n le_rfl) (hdAll n le_rfl) hd0top
  have hlocal_sum :
      (∑ k ∈ Finset.range n,
        (pfF a b c (n + 1) k - pfRho a b c n * pfF a b c n k)) =
        ∑ k ∈ Finset.range n, (pfG a b c n (k + 1) - pfG a b c n k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    rcases hlocal k hklt with ⟨hck, hdk, hdlast⟩
    exact pf_gosper_telescoping_summand_of_cert a b c n k hklt
      (hcAll k (Nat.le_of_lt hklt)) (hdAll k (Nat.le_of_lt hklt)) hck hdk hd hdlast
      (hcertAll k hklt)
  have hdiff : pfSum a b c (n + 1) - pfRho a b c n * pfSum a b c n = 0 := by
    calc
      pfSum a b c (n + 1) - pfRho a b c n * pfSum a b c n =
          (∑ k ∈ Finset.range n,
            (pfF a b c (n + 1) k - pfRho a b c n * pfF a b c n k)) +
          (pfF a b c (n + 1) n - pfRho a b c n * pfF a b c n n) +
          pfF a b c (n + 1) (n + 1) := by
            unfold pfSum
            rw [Finset.sum_range_succ (f := fun k => pfF a b c (n + 1) k)]
            rw [Finset.sum_range_succ (f := fun k => pfF a b c (n + 1) k)]
            rw [Finset.sum_range_succ (f := fun k => pfF a b c n k)]
            rw [mul_add]
            rw [Finset.mul_sum]
            rw [Finset.sum_sub_distrib]
            ring
      _ = (∑ k ∈ Finset.range n, (pfG a b c n (k + 1) - pfG a b c n k)) +
          (pfF a b c (n + 1) n - pfRho a b c n * pfF a b c n n) +
          pfF a b c (n + 1) (n + 1) := by rw [hlocal_sum]
      _ = (pfG a b c n n - pfG a b c n 0) +
          (pfF a b c (n + 1) n - pfRho a b c n * pfF a b c n n) +
          pfF a b c (n + 1) (n + 1) := by
            rw [Finset.sum_range_sub]
      _ = 0 := by
            rw [pfG_zero]
            linarith [hboundary]
  exact sub_eq_zero.mp hdiff

private theorem pfaff_saalschutz_finite_explicit_of_cert (a b c : ℚ) (n : ℕ)
    (H : ∀ m < n, pfRecHyp a b c m)
    (Hcert : ∀ m < n, ∀ k < m,
      pfNQuotRat a b c (m : ℚ) (k : ℚ) - pfRho a b c m =
        pfR a b c m (k + 1) * pfKQuotRat a b c (m : ℚ) (k : ℚ) - pfR a b c m k) :
    (∑ k ∈ Finset.range (n + 1),
      rp (-(n : ℚ)) k * rp a k * rp b k /
        (rp c k * rp (1 + a + b - c - (n : ℚ)) k * (Nat.factorial k : ℚ))) =
      rp (c - a) n * rp (c - b) n / (rp c n * rp (c - a - b) n) := by
  have hmain : pfSum a b c n = pfClosed a b c n := by
    induction n with
    | zero =>
        simp [pfSum, pfClosed, pfF]
    | succ n ih =>
        have Hn : pfRecHyp a b c n := H n (Nat.lt_succ_self n)
        have hsum := pfSum_succ_of_cert a b c n Hn (Hcert n (Nat.lt_succ_self n))
        rcases Hn with ⟨hcn, hcabn, hd, habc, hcAll, hdAll, hd0top, hcab0, hlocal⟩
        have Hprev : ∀ m < n, pfRecHyp a b c m := by
          intro m hm
          exact H m (Nat.lt_trans hm (Nat.lt_succ_self n))
        have Hcertprev : ∀ m < n, ∀ k < m,
            pfNQuotRat a b c (m : ℚ) (k : ℚ) - pfRho a b c m =
              pfR a b c m (k + 1) * pfKQuotRat a b c (m : ℚ) (k : ℚ) - pfR a b c m k := by
          intro m hm
          exact Hcert m (Nat.lt_trans hm (Nat.lt_succ_self n))
        have hclosed := pfClosed_succ a b c n (hcAll n le_rfl) hcab0 hcn hcabn
        calc
          pfSum a b c (n + 1) = pfRho a b c n * pfSum a b c n := hsum
          _ = pfRho a b c n * pfClosed a b c n := by rw [ih Hprev Hcertprev]
          _ = pfClosed a b c (n + 1) := by rw [hclosed]
  simpa [pfSum, pfClosed, pfF] using hmain

end P

open scoped BigOperators
open Finset

namespace S

private noncomputable def rp (x : ℚ) (k : ℕ) : ℚ :=
  ∏ i ∈ Finset.range k, (x + (i : ℚ))

@[simp] lemma rp_zero (x : ℚ) : rp x 0 = 1 := by
  simp [rp]

private lemma rp_succ (x : ℚ) (k : ℕ) : rp x (k + 1) = rp x k * (x + k) := by
  simp [rp, Finset.range_add_one, Finset.prod_insert]
  ring

private lemma fcz (k : ℕ) : ((Nat.factorial k : ℕ) : ℚ) ≠ 0 := by
  exact_mod_cast (Nat.factorial_pos k).ne'

private lemma rpo (k : ℕ) : rp 1 k = (Nat.factorial k : ℚ) := by
  induction k with
  | zero => simp [rp]
  | succ k ih =>
      rw [rp_succ, ih, Nat.factorial_succ]
      norm_num [Nat.cast_mul, Nat.cast_add]
      ring

@[simp] lemma rp_one_ne_zero (k : ℕ) : rp 1 k ≠ 0 := by
  rw [rpo]
  exact fcz k

private lemma rpp (x : ℚ) (k : ℕ) (hx : 0 < x) : 0 < rp x k := by
  unfold rp
  exact Finset.prod_pos fun i hi => by
    have hi0 : (0 : ℚ) ≤ i := by exact_mod_cast (Nat.zero_le i)
    linarith

private lemma rpzp (x : ℚ) (k : ℕ) (hx : 0 < x) : rp x k ≠ 0 :=
  (rpp x k hx).ne'

private lemma rp_half_two_mul_add_one_ne_zero (n k : ℕ) :
    rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) k ≠ 0 := by
  apply rpzp
  positivity

private lemma rp_neg_two_mul_ne_zero_of_le (n j : ℕ) (hj : j ≤ n) :
    rp (-(2 * n : ℕ) : ℚ) j ≠ 0 := by
  unfold rp
  apply Finset.prod_ne_zero_iff.2
  intro i hi hzero
  have hij : i < j := Finset.mem_range.mp hi
  have hi_lt_2n : i < 2 * n := by omega
  have h_eq : (i : ℚ) = (2 * n : ℕ) := by linarith
  have h_nat : i = 2 * n := by exact_mod_cast h_eq
  omega

private lemma rpn (m k : ℕ) (hk : k ≤ m) :
    rp (-(m : ℚ)) k = (-1 : ℚ) ^ k * (m.descFactorial k : ℚ) := by
  induction k with
  | zero => simp [rp]
  | succ k ih =>
      have hk_le : k ≤ m := Nat.le_of_succ_le hk
      rw [rp_succ, ih hk_le, Nat.descFactorial_succ]
      have hsub : ((m - k : ℕ) : ℚ) = (m : ℚ) - (k : ℚ) := by
        exact Nat.cast_sub hk_le
      rw [Nat.cast_mul, hsub]
      ring

private lemma rp_neg_self_eq (m : ℕ) :
    rp (-(m : ℚ)) m = (-1 : ℚ) ^ m * (Nat.factorial m : ℚ) := by
  simpa [Nat.descFactorial_self] using rpn m m le_rfl

private lemma rp_neg_two_mul_at_n_eq (n : ℕ) :
    rp (-(2 * n : ℕ) : ℚ) n = (-1 : ℚ) ^ n * ((2 * n).descFactorial n : ℚ) := by
  simpa using rpn (2 * n) n (by omega)

private lemma central_choose_eq_rp_neg_ratio (n : ℕ) :
    (Nat.choose (2 * n) n : ℚ) = rp (-(2 * n : ℕ) : ℚ) n / rp (-(n : ℚ)) n := by
  rw [rp_neg_two_mul_at_n_eq, rp_neg_self_eq]
  have hfac : (Nat.factorial n : ℚ) ≠ 0 := fcz n
  have hsign : (-1 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hfac, hsign]
  have hdesc : (((2 * n).descFactorial n : ℕ) : ℚ) =
      (Nat.factorial n : ℚ) * (Nat.choose (2 * n) n : ℚ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (2 * n) n
  rw [hdesc]
  ring

private lemma central_choose_sq_eq_rp_neg_ratio_sq (n : ℕ) :
    (Nat.choose (2 * n) n : ℚ) ^ 2 =
      (rp (-(2 * n : ℕ) : ℚ) n / rp (-(n : ℚ)) n) ^ 2 := by
  rw [central_choose_eq_rp_neg_ratio]

private lemma prefactor (n : ℕ) :
    (Nat.choose (2 * n) n : ℚ) ^ 2 =
      (rp (-(2 * n : ℕ) : ℚ) n / rp (-(n : ℚ)) n) ^ 2 :=
  central_choose_sq_eq_rp_neg_ratio_sq n

private lemma rp_neg_nat_div_factorial_eq_choose (m k : ℕ) (hk : k ≤ m) :
    rp (-(m : ℚ)) k / (Nat.factorial k : ℚ) =
      (-1 : ℚ) ^ k * (Nat.choose m k : ℚ) := by
  rw [rpn m k hk]
  have hfac : (Nat.factorial k : ℚ) ≠ 0 := fcz k
  have hdesc : (m.descFactorial k : ℚ) =
      (Nat.factorial k : ℚ) * (Nat.choose m k : ℚ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose m k
  rw [hdesc]
  field_simp [hfac]

private lemma rp_neg_ratio_eq_choose_ratio (n j : ℕ) (hj : j ≤ n) :
    rp (-(n : ℚ)) j / rp (-(2 * n : ℕ) : ℚ) j =
      (Nat.choose n j : ℚ) / (Nat.choose (2 * n) j : ℚ) := by
  rw [rpn n j hj]
  rw [rpn (2 * n) j (by omega)]
  have hsign : (-1 : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdesc₁ : (n.descFactorial j : ℚ) =
      (Nat.factorial j : ℚ) * (Nat.choose n j : ℚ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n j
  have hdesc₂ : ((2 * n).descFactorial j : ℚ) =
      (Nat.factorial j : ℚ) * (Nat.choose (2 * n) j : ℚ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (2 * n) j
  have hfac : (Nat.factorial j : ℚ) ≠ 0 := fcz j
  have hchoose : (Nat.choose (2 * n) j : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : j ≤ 2 * n)).ne'
  rw [hdesc₁, hdesc₂]
  field_simp [hsign, hfac, hchoose]

private lemma rp_duplication (x : ℚ) (k : ℕ) :
    rp x (2 * k) = (4 : ℚ) ^ k * rp (x / 2) k * rp ((x + 1) / 2) k := by
  induction k with
  | zero => simp [rp]
  | succ k ih =>
      have htwo : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [htwo]
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega]
      rw [rp_succ, rp_succ]
      rw [ih]
      rw [rp_succ (x / 2) k, rp_succ ((x + 1) / 2) k]
      norm_num [pow_succ]
      ring

private lemma rpa (m k : ℕ) : rp (m : ℚ) k = (m.ascFactorial k : ℚ) := by
  induction k with
  | zero => simp [rp]
  | succ k ih =>
      rw [rp_succ, ih, Nat.ascFactorial_succ]
      norm_num [Nat.cast_mul, Nat.cast_add]
      ring

private lemma rp_nat_add_one_div_factorial_eq_choose (n k : ℕ) :
    rp ((n + 1 : ℕ) : ℚ) k / (Nat.factorial k : ℚ) = (Nat.choose (n + k) k : ℚ) := by
  rw [rpa]
  have hfac : (Nat.factorial k : ℚ) ≠ 0 := fcz k
  have hasc : (((n + 1).ascFactorial k : ℕ) : ℚ) =
      (Nat.factorial k : ℚ) * (Nat.choose (n + k) k : ℚ) := by
    have hdesc : (n + k).descFactorial k = (n + 1).ascFactorial k := by
      exact Nat.add_descFactorial_eq_ascFactorial n k
    rw [← hdesc]
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (n + k) k
  rw [hasc]
  field_simp [hfac]

private lemma rp_nat_ratio_eq_choose_ratio (n k : ℕ) :
    rp ((3 * n + 1 : ℕ) : ℚ) (2 * k) / rp ((2 * n + 1 : ℕ) : ℚ) (2 * k) =
      (Nat.choose (3 * n + 2 * k) n : ℚ) / (Nat.choose (3 * n) n : ℚ) := by
  rw [rpa, rpa]
  have hdenpos : 0 < (2 * n + 1).ascFactorial (2 * k) := by positivity
  have hden : (((2 * n + 1).ascFactorial (2 * k) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hdenpos.ne'
  have hchoose : (Nat.choose (3 * n) n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 3 * n)).ne'
  have hA : (3 * n + 2 * k).descFactorial (2 * k) = (3 * n + 1).ascFactorial (2 * k) := by
    have h := Nat.add_descFactorial_eq_ascFactorial (3 * n) (2 * k)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hB : (2 * n + 2 * k).descFactorial (2 * k) = (2 * n + 1).ascFactorial (2 * k) := by
    have h := Nat.add_descFactorial_eq_ascFactorial (2 * n) (2 * k)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hdescA : (((3 * n + 1).ascFactorial (2 * k) : ℕ) : ℚ) =
      (Nat.factorial (2 * k) : ℚ) * (Nat.choose (3 * n + 2 * k) (2 * k) : ℚ) := by
    rw [← hA]
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (3 * n + 2 * k) (2 * k)
  have hdescB : (((2 * n + 1).ascFactorial (2 * k) : ℕ) : ℚ) =
      (Nat.factorial (2 * k) : ℚ) * (Nat.choose (2 * n + 2 * k) (2 * k) : ℚ) := by
    rw [← hB]
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (2 * n + 2 * k) (2 * k)
  have hfac : (Nat.factorial (2 * k) : ℚ) ≠ 0 := fcz (2 * k)
  rw [hdescA, hdescB]
  rw [Nat.cast_choose (K := ℚ) (by omega : 2 * k ≤ 3 * n + 2 * k)]
  rw [Nat.cast_choose (K := ℚ) (by omega : 2 * k ≤ 2 * n + 2 * k)]
  rw [Nat.cast_choose (K := ℚ) (by omega : n ≤ 3 * n + 2 * k)]
  rw [Nat.cast_choose (K := ℚ) (by omega : n ≤ 3 * n)]
  rw [show 3 * n + 2 * k - 2 * k = 3 * n by omega]
  rw [show 2 * n + 2 * k - 2 * k = 2 * n by omega]
  rw [show 3 * n + 2 * k - n = 2 * n + 2 * k by omega]
  rw [show 3 * n - n = 2 * n by omega]
  have hfacAll : ∀ m : ℕ, ((Nat.factorial m : ℕ) : ℚ) ≠ 0 := fcz
  field_simp [hfac, hfacAll]

private lemma lhs_half_factor_eq_binom_ratio (n k : ℕ) :
    rp ((((3 * n : ℕ) + 1 : ℚ) / 2)) k * rp ((((3 * n : ℕ) + 2 : ℚ) / 2)) k /
        (rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) k * (Nat.factorial k : ℚ)) =
      (Nat.choose (n + k) k : ℚ) *
        ((Nat.choose (3 * n + 2 * k) n : ℚ) / (Nat.choose (3 * n) n : ℚ)) := by
  have hdupA : rp (((3 * n + 1 : ℕ) : ℚ)) (2 * k) =
      (4 : ℚ) ^ k * rp ((((3 * n : ℕ) + 1 : ℚ) / 2)) k *
        rp ((((3 * n : ℕ) + 2 : ℚ) / 2)) k := by
    have h₁ : (((3 * n + 1 : ℕ) : ℚ) / 2) = (((3 * n : ℕ) + 1 : ℚ) / 2) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
    have h₂ : ((((3 * n + 1 : ℕ) : ℚ) + 1) / 2) = (((3 * n : ℕ) + 2 : ℚ) / 2) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    have base := rp_duplication (((3 * n + 1 : ℕ) : ℚ)) k
    rw [h₁, h₂] at base
    simpa using base
  have hdupB : rp (((2 * n + 1 : ℕ) : ℚ)) (2 * k) =
      (4 : ℚ) ^ k * rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) k *
        rp (((n + 1 : ℕ) : ℚ)) k := by
    have h₁ : (((2 * n + 1 : ℕ) : ℚ) / 2) = (((2 * n : ℕ) + 1 : ℚ) / 2) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
    have h₂ : ((((2 * n + 1 : ℕ) : ℚ) + 1) / 2) = (((n + 1 : ℕ) : ℚ)) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    have base := rp_duplication (((2 * n + 1 : ℕ) : ℚ)) k
    rw [h₁, h₂] at base
    simpa using base
  have hpow : (4 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdenHalf : rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) k ≠ 0 := rp_half_two_mul_add_one_ne_zero n k
  have hfac : (Nat.factorial k : ℚ) ≠ 0 := fcz k
  have hnatpos : rp (((n + 1 : ℕ) : ℚ)) k ≠ 0 := rpzp _ _ (by positivity)
  have hBnon : rp (((2 * n + 1 : ℕ) : ℚ)) (2 * k) ≠ 0 := by
    rw [hdupB]
    exact mul_ne_zero (mul_ne_zero hpow hdenHalf) hnatpos
  calc
    rp ((((3 * n : ℕ) + 1 : ℚ) / 2)) k * rp ((((3 * n : ℕ) + 2 : ℚ) / 2)) k /
        (rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) k * (Nat.factorial k : ℚ))
        = (rp (((3 * n + 1 : ℕ) : ℚ)) (2 * k) / (4 : ℚ) ^ k) /
          (rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) k * (Nat.factorial k : ℚ)) := by
            rw [hdupA]
            field_simp [hpow]
    _ = (rp (((3 * n + 1 : ℕ) : ℚ)) (2 * k) / rp (((2 * n + 1 : ℕ) : ℚ)) (2 * k)) *
          (rp (((n + 1 : ℕ) : ℚ)) k / (Nat.factorial k : ℚ)) := by
            rw [hdupB]
            field_simp [hpow, hdenHalf, hfac, hnatpos, hBnon]
    _ = (Nat.choose (3 * n + 2 * k) n : ℚ) / (Nat.choose (3 * n) n : ℚ) *
          (Nat.choose (n + k) k : ℚ) := by
            rw [rp_nat_ratio_eq_choose_ratio, rp_nat_add_one_div_factorial_eq_choose]
    _ = (Nat.choose (n + k) k : ℚ) *
          ((Nat.choose (3 * n + 2 * k) n : ℚ) / (Nat.choose (3 * n) n : ℚ)) := by ring

private lemma rp_neg_nat_eq_zero_of_lt (m k : ℕ) (h : m < k) :
    rp (-(m : ℚ)) k = 0 := by
  unfold rp
  rw [Finset.prod_eq_zero_iff]
  exact ⟨m, Finset.mem_range.mpr h, by ring⟩

private lemma rp_neg_nat_even_ratio_eq_choose_ratio (n j : ℕ) (h : 2 * j ≤ n + 1) :
    rp (-((n : ℚ) + 1)) (2 * j) / rp (((2 * n + 1 : ℕ) : ℚ)) (2 * j) =
      (Nat.choose (n + 1) (2 * j) : ℚ) /
        (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ) := by
  have hn1 : -((n : ℚ) + 1) = -(((n + 1 : ℕ) : ℚ)) := by
    norm_num [Nat.cast_add]
  rw [hn1]
  rw [rpn (n + 1) (2 * j) (by simpa using h)]
  rw [rpa]
  have hsign : (-1 : ℚ) ^ (2 * j) = 1 := by
    rw [show 2 * j = 2 * j by rfl]
    rw [pow_mul]
    norm_num
  rw [hsign, one_mul]
  have hB : (2 * n + 2 * j).descFactorial (2 * j) = (2 * n + 1).ascFactorial (2 * j) := by
    have h0 := Nat.add_descFactorial_eq_ascFactorial (2 * n) (2 * j)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h0
  have hdescA : (((n + 1).descFactorial (2 * j) : ℕ) : ℚ) =
      (Nat.factorial (2 * j) : ℚ) * (Nat.choose (n + 1) (2 * j) : ℚ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (n + 1) (2 * j)
  have hdescB : (((2 * n + 1).ascFactorial (2 * j) : ℕ) : ℚ) =
      (Nat.factorial (2 * j) : ℚ) * (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ) := by
    rw [← hB]
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (2 * n + 2 * j) (2 * j)
  have hfac : (Nat.factorial (2 * j) : ℚ) ≠ 0 := fcz (2 * j)
  have hchoose : (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 * j ≤ 2 * n + 2 * j)).ne'
  rw [hdescA, hdescB]
  field_simp [hfac, hchoose]

private lemma transformed_half_factor_eq_binom_ratio_of_le (n j : ℕ) (h : 2 * j ≤ n + 1) :
    rp (-(n : ℚ) / 2) j * rp (-((n : ℚ) + 1) / 2) j /
        (rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) j * (Nat.factorial j : ℚ)) =
      (Nat.choose (n + 1) (2 * j) : ℚ) * (Nat.choose (n + j) j : ℚ) /
        (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ) := by
  have hdupA : rp (-((n : ℚ) + 1)) (2 * j) =
      (4 : ℚ) ^ j * rp (-((n : ℚ) + 1) / 2) j * rp (-(n : ℚ) / 2) j := by
    have base := rp_duplication (-((n : ℚ) + 1)) j
    have hx : ((-((n : ℚ) + 1) + 1) / 2) = -(n : ℚ) / 2 := by ring
    rw [hx] at base
    simpa using base
  have hdupB : rp (((2 * n + 1 : ℕ) : ℚ)) (2 * j) =
      (4 : ℚ) ^ j * rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) j *
        rp (((n + 1 : ℕ) : ℚ)) j := by
    have h₁ : (((2 * n + 1 : ℕ) : ℚ) / 2) = (((2 * n : ℕ) + 1 : ℚ) / 2) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
    have h₂ : ((((2 * n + 1 : ℕ) : ℚ) + 1) / 2) = (((n + 1 : ℕ) : ℚ)) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    have base := rp_duplication (((2 * n + 1 : ℕ) : ℚ)) j
    rw [h₁, h₂] at base
    simpa using base
  have hpow : (4 : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hhalfden : rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) j ≠ 0 := rp_half_two_mul_add_one_ne_zero n j
  have hfac : (Nat.factorial j : ℚ) ≠ 0 := fcz j
  have hnatpos : rp (((n + 1 : ℕ) : ℚ)) j ≠ 0 := rpzp _ _ (by positivity)
  have hBnon : rp (((2 * n + 1 : ℕ) : ℚ)) (2 * j) ≠ 0 := by
    rw [hdupB]
    exact mul_ne_zero (mul_ne_zero hpow hhalfden) hnatpos
  calc
    rp (-(n : ℚ) / 2) j * rp (-((n : ℚ) + 1) / 2) j /
        (rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) j * (Nat.factorial j : ℚ))
        = (rp (-((n : ℚ) + 1)) (2 * j) / (4 : ℚ) ^ j) /
          (rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) j * (Nat.factorial j : ℚ)) := by
            rw [hdupA]
            field_simp [hpow]
    _ = (rp (-((n : ℚ) + 1)) (2 * j) / rp (((2 * n + 1 : ℕ) : ℚ)) (2 * j)) *
          (rp (((n + 1 : ℕ) : ℚ)) j / (Nat.factorial j : ℚ)) := by
            rw [hdupB]
            field_simp [hpow, hhalfden, hfac, hnatpos, hBnon]
    _ = ((Nat.choose (n + 1) (2 * j) : ℚ) /
          (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ)) *
          (Nat.choose (n + j) j : ℚ) := by
            rw [rp_neg_nat_even_ratio_eq_choose_ratio n j h,
              rp_nat_add_one_div_factorial_eq_choose]
    _ = (Nat.choose (n + 1) (2 * j) : ℚ) * (Nat.choose (n + j) j : ℚ) /
        (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ) := by ring

private lemma transformed_half_factor_eq_binom_ratio_of_not_le (n j : ℕ) (h : ¬ 2 * j ≤ n + 1) :
    rp (-(n : ℚ) / 2) j * rp (-((n : ℚ) + 1) / 2) j /
        (rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) j * (Nat.factorial j : ℚ)) =
      (Nat.choose (n + 1) (2 * j) : ℚ) * (Nat.choose (n + j) j : ℚ) /
        (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ) := by
  have hlt : n + 1 < 2 * j := Nat.lt_of_not_ge h
  have hdupA : rp (-((n : ℚ) + 1)) (2 * j) =
      (4 : ℚ) ^ j * rp (-((n : ℚ) + 1) / 2) j * rp (-(n : ℚ) / 2) j := by
    have base := rp_duplication (-((n : ℚ) + 1)) j
    have hx : ((-((n : ℚ) + 1) + 1) / 2) = -(n : ℚ) / 2 := by ring
    rw [hx] at base
    simpa using base
  have hpow : (4 : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hzeroA : rp (-((n : ℚ) + 1)) (2 * j) = 0 := by
    simpa [Nat.cast_add] using rp_neg_nat_eq_zero_of_lt (n + 1) (2 * j) hlt
  have hprod : rp (-(n : ℚ) / 2) j * rp (-((n : ℚ) + 1) / 2) j = 0 := by
    rw [hzeroA] at hdupA
    have hz : (4 : ℚ) ^ j * (rp (-((n : ℚ) + 1) / 2) j * rp (-(n : ℚ) / 2) j) = 0 := by
      simpa [mul_assoc] using hdupA.symm
    have hz' : rp (-((n : ℚ) + 1) / 2) j * rp (-(n : ℚ) / 2) j = 0 :=
      (mul_eq_zero.mp hz).resolve_left hpow
    simpa [mul_comm] using hz'
  have hchoose0 : (Nat.choose (n + 1) (2 * j) : ℚ) = 0 := by
    exact_mod_cast Nat.choose_eq_zero_of_lt hlt
  rw [hprod, hchoose0]
  simp

private lemma transformed_half_factor_eq_binom_ratio (n j : ℕ) :
    rp (-(n : ℚ) / 2) j * rp (-((n : ℚ) + 1) / 2) j /
        (rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) j * (Nat.factorial j : ℚ)) =
      (Nat.choose (n + 1) (2 * j) : ℚ) * (Nat.choose (n + j) j : ℚ) /
        (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ) := by
  by_cases h : 2 * j ≤ n + 1
  · exact transformed_half_factor_eq_binom_ratio_of_le n j h
  · exact transformed_half_factor_eq_binom_ratio_of_not_le n j h

private noncomputable def F43Term (a b c d e f g : ℚ) (k : ℕ) : ℚ :=
  rp a k * rp b k * rp c k * rp d k /
    (rp e k * rp f k * rp g k * (Nat.factorial k : ℚ))

private noncomputable def F43Sum (a b c d e f g : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), F43Term a b c d e f g k

private noncomputable def searsLHS (n : ℕ) : ℚ :=
  F43Sum (-(n : ℚ)) (-(n : ℚ)) (((3 * n : ℕ) + 1 : ℚ) / 2)
    (((3 * n : ℕ) + 2 : ℚ) / 2) 1 1 (((2 * n : ℕ) + 1 : ℚ) / 2) n

private noncomputable def searsTransformedSum (n : ℕ) : ℚ :=
  F43Sum (-(n : ℚ)) (-(n : ℚ)) (-(n : ℚ) / 2) (-((n : ℚ) + 1) / 2)
    (-(2 * n : ℕ) : ℚ) (-(2 * n : ℕ) : ℚ) (((2 * n : ℕ) + 1 : ℚ) / 2) n

private noncomputable def ss (n : ℕ) : Prop :=
  searsLHS n = (Nat.choose (2 * n) n : ℚ) ^ 2 * searsTransformedSum n

private noncomputable def slbin (n k : ℕ) : ℚ :=
  (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (n + k) k : ℚ) *
    ((Nat.choose (3 * n + 2 * k) n : ℚ) / (Nat.choose (3 * n) n : ℚ))

private noncomputable def tsumnd (n j : ℕ) : ℚ :=
  ((Nat.choose n j : ℚ) ^ 2 * (Nat.choose (n + 1) (2 * j) : ℚ) *
      (Nat.choose (n + j) j : ℚ)) /
    ((Nat.choose (2 * n) j : ℚ) ^ 2 * (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ))

private lemma f43tr (n j : ℕ) (hj : j ≤ n) :
    F43Term (-(n : ℚ)) (-(n : ℚ)) (-(n : ℚ) / 2) (-((n : ℚ) + 1) / 2)
      (-(2 * n : ℕ) : ℚ) (-(2 * n : ℕ) : ℚ) (((2 * n : ℕ) + 1 : ℚ) / 2) j =
      tsumnd n j := by
  unfold F43Term tsumnd
  have hden : rp (-(2 * n : ℕ) : ℚ) j ≠ 0 := rp_neg_two_mul_ne_zero_of_le n j hj
  have hchoose2n : (Nat.choose (2 * n) j : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : j ≤ 2 * n)).ne'
  have hneg := rp_neg_ratio_eq_choose_ratio n j hj
  have hhalf := transformed_half_factor_eq_binom_ratio n j
  calc
    rp (-(n : ℚ)) j * rp (-(n : ℚ)) j * rp (-(n : ℚ) / 2) j *
          rp (-((n : ℚ) + 1) / 2) j /
        (rp (-(2 * n : ℕ) : ℚ) j * rp (-(2 * n : ℕ) : ℚ) j *
          rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) j * (Nat.factorial j : ℚ))
        = (rp (-(n : ℚ)) j / rp (-(2 * n : ℕ) : ℚ) j) ^ 2 *
          (rp (-(n : ℚ) / 2) j * rp (-((n : ℚ) + 1) / 2) j /
            (rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) j * (Nat.factorial j : ℚ))) := by
            field_simp [hden]
    _ = ((Nat.choose n j : ℚ) / (Nat.choose (2 * n) j : ℚ)) ^ 2 *
          ((Nat.choose (n + 1) (2 * j) : ℚ) * (Nat.choose (n + j) j : ℚ) /
            (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ)) := by
            rw [hneg, hhalf]
    _ = (Nat.choose n j : ℚ) ^ 2 * (Nat.choose (n + 1) (2 * j) : ℚ) *
          (Nat.choose (n + j) j : ℚ) /
        ((Nat.choose (2 * n) j : ℚ) ^ 2 *
          (Nat.choose (2 * n + 2 * j) (2 * j) : ℚ)) := by
            field_simp [hchoose2n]

private lemma stsum (n : ℕ) :
    searsTransformedSum n = ∑ j ∈ Finset.range (n + 1), tsumnd n j := by
  unfold searsTransformedSum F43Sum
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact f43tr n j
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

private lemma f43lhs (n k : ℕ) (hk : k ≤ n) :
    F43Term (-(n : ℚ)) (-(n : ℚ)) (((3 * n : ℕ) + 1 : ℚ) / 2)
      (((3 * n : ℕ) + 2 : ℚ) / 2) 1 1 (((2 * n : ℕ) + 1 : ℚ) / 2) k =
      slbin n k := by
  unfold F43Term slbin
  have hfac : (Nat.factorial k : ℚ) ≠ 0 := fcz k
  have hhalfden : rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) k ≠ 0 :=
    rp_half_two_mul_add_one_ne_zero n k
  have hneg := rp_neg_nat_div_factorial_eq_choose n k hk
  have hhalf := lhs_half_factor_eq_binom_ratio n k
  have hsgn : ((-1 : ℚ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [rpo]
  calc
    rp (-(n : ℚ)) k * rp (-(n : ℚ)) k *
          rp ((((3 * n : ℕ) + 1 : ℚ) / 2)) k *
          rp ((((3 * n : ℕ) + 2 : ℚ) / 2)) k /
        ((Nat.factorial k : ℚ) * (Nat.factorial k : ℚ) *
          rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) k * (Nat.factorial k : ℚ))
        = (rp (-(n : ℚ)) k / (Nat.factorial k : ℚ)) ^ 2 *
            (rp ((((3 * n : ℕ) + 1 : ℚ) / 2)) k *
              rp ((((3 * n : ℕ) + 2 : ℚ) / 2)) k /
              (rp ((((2 * n : ℕ) + 1 : ℚ) / 2)) k * (Nat.factorial k : ℚ))) := by
          field_simp [hfac, hhalfden]
    _ = ((-1 : ℚ) ^ k * (Nat.choose n k : ℚ)) ^ 2 *
          ((Nat.choose (n + k) k : ℚ) *
            ((Nat.choose (3 * n + 2 * k) n : ℚ) / (Nat.choose (3 * n) n : ℚ))) := by
          rw [hneg, hhalf]
    _ = (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (n + k) k : ℚ) *
          ((Nat.choose (3 * n + 2 * k) n : ℚ) / (Nat.choose (3 * n) n : ℚ)) := by
          rw [mul_pow, hsgn, one_mul]
          ring

private lemma slsum (n : ℕ) :
    searsLHS n = ∑ k ∈ Finset.range (n + 1), slbin n k := by
  unfold searsLHS F43Sum
  refine Finset.sum_congr rfl ?_
  intro k hk
  exact f43lhs n k (by exact Nat.le_of_lt_succ (Finset.mem_range.mp hk))

end S

open scoped BigOperators
open Finset


namespace Q

private lemma pf_rpnz (M k : ℕ) (hk : k ≤ M) :
    P.rp (-(M : ℚ)) k ≠ 0 := by
  unfold P.rp
  apply Finset.prod_ne_zero_iff.2
  intro i hi hzero
  have hik : i < k := Finset.mem_range.mp hi
  have hiM : i < M := lt_of_lt_of_le hik hk
  have h_eq : (i : ℚ) = (M : ℚ) := by linarith
  have h_nat : i = M := by exact_mod_cast h_eq
  omega

private lemma pf_rp_nat_add_one_ne_zero (M k : ℕ) :
    P.rp ((M + 1 : ℕ) : ℚ) k ≠ 0 := by
  unfold P.rp
  apply Finset.prod_ne_zero_iff.2
  intro i hi hzero
  have hpos : (0 : ℚ) < ((M + 1 : ℕ) : ℚ) + (i : ℚ) := by positivity
  exact hpos.ne' hzero

private lemma inner_pfaff_recHyp (n j : ℕ) (hj : j ≤ n) :
    ∀ m < n - j,
      P.pfRecHyp (-(n : ℚ) + (j : ℚ))
        (-((2 * n : ℕ) : ℚ) - 1)
        (-((2 * n : ℕ) : ℚ) + (j : ℚ)) m := by
  intro m hm
  unfold P.pfRecHyp
  constructor
  · -- c + m ≠ 0
    intro h
    have hltq : ((j + m : ℕ) : ℚ) < ((2 * n : ℕ) : ℚ) := by
      exact_mod_cast (by omega : j + m < 2 * n)
    have : ((j + m : ℕ) : ℚ) = ((2 * n : ℕ) : ℚ) := by
      norm_num [Nat.cast_add, Nat.cast_mul] at h ⊢
      linarith
    linarith
  constructor
  · -- c - a - b + m = n + 1 + m ≠ 0
    intro h
    have hpos : (0 : ℚ) < (n : ℚ) + 1 + (m : ℚ) := by positivity
    have : (n : ℚ) + 1 + (m : ℚ) = 0 := by
      norm_num [Nat.cast_add, Nat.cast_mul] at h ⊢
      linarith
    linarith
  constructor
  · -- a + b - c - m = -n-1-m ≠ 0
    have hpos : (0 : ℚ) < (n : ℚ) + 1 + (m : ℚ) := by positivity
    linarith
  constructor
  · -- a + b - c = -n-1 ≠ 0
    have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
    linarith
  constructor
  · -- rp c k ≠ 0
    intro k hk
    have harg : -((2 * n : ℕ) : ℚ) + (j : ℚ) = -(((2 * n) - j : ℕ) : ℚ) := by
      have hj2 : j ≤ 2 * n := by omega
      rw [Nat.cast_sub hj2]
      ring
    rw [harg]
    apply pf_rpnz
    omega
  constructor
  · -- rp (1+a+b-c-m) k = rp (-(n+m)) k ≠ 0
    intro k hk
    have harg :
        1 + (-(n : ℚ) + (j : ℚ)) + (-((2 * n : ℕ) : ℚ) - 1) -
            (-((2 * n : ℕ) : ℚ) + (j : ℚ)) - (m : ℚ) =
          -(((n + m : ℕ)) : ℚ) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    rw [harg]
    apply pf_rpnz
    omega
  constructor
  · -- rp (a+b-c-m) m = rp (-(n+m+1)) m ≠ 0
    have harg :
        (-(n : ℚ) + (j : ℚ)) + (-((2 * n : ℕ) : ℚ) - 1) -
            (-((2 * n : ℕ) : ℚ) + (j : ℚ)) - (m : ℚ) =
          -(((n + m + 1 : ℕ)) : ℚ) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    rw [harg]
    apply pf_rpnz
    omega
  constructor
  · -- rp (c-a-b) m = rp (n+1) m ≠ 0
    have harg :
        (-((2 * n : ℕ) : ℚ) + (j : ℚ)) - (-(n : ℚ) + (j : ℚ)) -
            (-((2 * n : ℕ) : ℚ) - 1) = (((n + 1 : ℕ)) : ℚ) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
    rw [harg]
    exact pf_rp_nat_add_one_ne_zero n m
  · -- local scalar denominator conditions
    intro k hk
    constructor
    · intro h
      have hltq : ((j + k : ℕ) : ℚ) < ((2 * n : ℕ) : ℚ) := by
        exact_mod_cast (by omega : j + k < 2 * n)
      have : ((j + k : ℕ) : ℚ) = ((2 * n : ℕ) : ℚ) := by
        norm_num [Nat.cast_add, Nat.cast_mul] at h ⊢
        linarith
      linarith
    constructor
    · -- `1+a+b-c-m+k = -n-m+k`.
      have hpos : (0 : ℚ) < (n : ℚ) + (m : ℚ) - (k : ℚ) := by
        have hklt_nm : k < n + m := by omega
        have hkq : (k : ℚ) < (n + m : ℕ) := by exact_mod_cast hklt_nm
        norm_num [Nat.cast_add] at hkq
        linarith
      intro h
      have : (n : ℚ) + (m : ℚ) - (k : ℚ) = 0 := by
        norm_num [Nat.cast_add, Nat.cast_mul] at h ⊢
        linarith
      linarith
    · -- `a+b-c-m+k = -n-1-m+k`.
      have hpos : (0 : ℚ) < (n : ℚ) + 1 + (m : ℚ) - (k : ℚ) := by
        have hk_le_nm : k ≤ n + m := by omega
        have hkq : (k : ℚ) ≤ (n + m : ℕ) := by exact_mod_cast hk_le_nm
        norm_num [Nat.cast_add] at hkq
        linarith
      intro h
      have : (n : ℚ) + 1 + (m : ℚ) - (k : ℚ) = 0 := by
        norm_num [Nat.cast_add, Nat.cast_mul] at h ⊢
        linarith
      linarith

private theorem inner_pfaff_closed_form (n j : ℕ) (hj : j ≤ n) :
    (∑ k ∈ Finset.range (n - j + 1),
      P.rp (-((n - j : ℕ) : ℚ)) k *
          P.rp (-(n : ℚ) + (j : ℚ)) k *
          P.rp (-((2 * n : ℕ) : ℚ) - 1) k /
        (P.rp (-((2 * n : ℕ) : ℚ) + (j : ℚ)) k *
          P.rp (-((2 * n : ℕ) : ℚ) + (j : ℚ)) k *
          (Nat.factorial k : ℚ))) =
      P.rp (-(n : ℚ)) (n - j) *
          P.rp (((j + 1 : ℕ) : ℚ)) (n - j) /
        (P.rp (-((2 * n : ℕ) : ℚ) + (j : ℚ)) (n - j) *
          P.rp (((n + 1 : ℕ) : ℚ)) (n - j)) := by
  have hpf := P.pfaff_saalschutz_finite_explicit_of_cert
    (a := (-(n : ℚ) + (j : ℚ)))
    (b := (-((2 * n : ℕ) : ℚ) - 1))
    (c := (-((2 * n : ℕ) : ℚ) + (j : ℚ)))
    (n := n - j) (inner_pfaff_recHyp n j hj) ?_
  · have ha : -(↑(n - j) : ℚ) = -(n : ℚ) + (j : ℚ) := by
      rw [Nat.cast_sub hj]
      ring
    have hd :
        1 + (-(n : ℚ) + (j : ℚ)) + (-((2 * n : ℕ) : ℚ) - 1) -
            (-((2 * n : ℕ) : ℚ) + (j : ℚ)) - ((n - j : ℕ) : ℚ) =
          -((2 * n : ℕ) : ℚ) + (j : ℚ) := by
      rw [Nat.cast_sub hj]
      norm_num [Nat.cast_mul]
      ring
    have hca :
        (-((2 * n : ℕ) : ℚ) + (j : ℚ)) - (-(n : ℚ) + (j : ℚ)) = -(n : ℚ) := by
      norm_num [Nat.cast_mul]
      ring
    have hcb :
        (-((2 * n : ℕ) : ℚ) + (j : ℚ)) - (-((2 * n : ℕ) : ℚ) - 1) = ((j + 1 : ℕ) : ℚ) := by
      norm_num [Nat.cast_add]
    have hcab :
        (-((2 * n : ℕ) : ℚ) + (j : ℚ)) - (-(n : ℚ) + (j : ℚ)) -
            (-((2 * n : ℕ) : ℚ) - 1) = ((n + 1 : ℕ) : ℚ) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
    rw [hd] at hpf
    have hca' : -(2 * (n : ℚ)) + (n : ℚ) = -(n : ℚ) := by ring
    have hcab' : -(n : ℚ) - (-(2 * (n : ℚ)) - 1) = (n : ℚ) + 1 := by ring
    simpa [ha, hca, hca', hcb, hcab, hcab', Nat.cast_add, Nat.cast_mul] using hpf
  · intro m hm k hk
    have Hm := inner_pfaff_recHyp n j hj m hm
    rcases Hm with ⟨hcn, hcabn, hd, habc, hcAll, hdAll, hd0top, hcab0, hlocal⟩
    rcases hlocal k hk with ⟨hck, hdk, hdlast⟩
    have hkn1 : (k : ℚ) - (m : ℚ) - 1 ≠ 0 := by
      have hle : (k : ℚ) ≤ (m : ℚ) := by exact_mod_cast (Nat.le_of_lt hk)
      linarith
    have hkn : (k : ℚ) - (m : ℚ) ≠ 0 := by
      have hlt : (k : ℚ) < (m : ℚ) := by exact_mod_cast hk
      linarith
    exact P.pf_gosper_certificate_core_nat
      (a := (-(n : ℚ) + (j : ℚ)))
      (b := (-((2 * n : ℕ) : ℚ) - 1))
      (c := (-((2 * n : ℕ) : ℚ) + (j : ℚ)))
      (m := m) (k := k) hcn hcabn hkn1 hkn hd hck hdk

end Q

open scoped BigOperators
open Finset

set_option maxHeartbeats 300000

namespace R

private noncomputable abbrev rp : ℚ → ℕ → ℚ := P.rp

private noncomputable def B (n : ℕ) : ℚ := (((3 * n : ℕ) + 1 : ℚ) / 2)
private noncomputable def C (n : ℕ) : ℚ := (((3 * n : ℕ) + 2 : ℚ) / 2)
private noncomputable def D (n : ℕ) : ℚ := (((2 * n : ℕ) + 1 : ℚ) / 2)
noncomputable def pref (n : ℕ) : ℚ := (Nat.choose (2 * n) n : ℚ) ^ 2

private noncomputable def coeff (n j : ℕ) : ℚ :=
  rp (-(n : ℚ)) j ^ 2 * rp (B n) j * rp (C n) j /
    (rp (D n) j * rp (-(2 * n : ℕ) : ℚ) j ^ 2 * (Nat.factorial j : ℚ))

private noncomputable def inner (n j l : ℕ) : ℚ :=
  rp (-((n - j : ℕ) : ℚ)) l * rp (-(n : ℚ) + (j : ℚ)) l *
      rp (-((2 * n : ℕ) : ℚ) - 1) l /
    (rp (-((2 * n : ℕ) : ℚ) + (j : ℚ)) l ^ 2 * (Nat.factorial l : ℚ))

private noncomputable def transformedF43Term (n s : ℕ) : ℚ :=
  rp (-(n : ℚ)) s ^ 2 * rp (-(n : ℚ) / 2) s * rp (-((n : ℚ) + 1) / 2) s /
    (rp (-(2 * n : ℕ) : ℚ) s ^ 2 * rp (D n) s * (Nat.factorial s : ℚ))

private noncomputable def lhsF43Term (n j : ℕ) : ℚ :=
  rp (-(n : ℚ)) j ^ 2 * rp (B n) j * rp (C n) j /
    (rp 1 j ^ 2 * rp (D n) j * (Nat.factorial j : ℚ))

private noncomputable def ACommon (n s : ℕ) : ℚ :=
  rp (-(n : ℚ)) s ^ 2 / rp (-(2 * n : ℕ) : ℚ) s ^ 2 *
    (rp (-((2 * n : ℕ) : ℚ) - 1) s / (Nat.factorial s : ℚ))

private lemma rp_add (x : ℚ) (a b : ℕ) : rp x (a + b) = rp x a * rp (x + (a : ℚ)) b := by
  induction b with
  | zero => simp [rp]
  | succ b ih =>
      calc
        rp x (a + (b + 1)) = rp x (a + b) * (x + ((a + b : ℕ) : ℚ)) := by
          simpa [Nat.add_assoc] using P.rp_succ x (a + b)
        _ = (rp x a * rp (x + (a : ℚ)) b) * (x + ((a + b : ℕ) : ℚ)) := by
          rw [ih]
        _ = rp x a * (rp (x + (a : ℚ)) b * ((x + (a : ℚ)) + (b : ℚ))) := by
          norm_num [Nat.cast_add]
          ring
        _ = rp x a * rp (x + (a : ℚ)) (b + 1) := by
          have hs : rp (x + (a : ℚ)) (b + 1) =
              rp (x + (a : ℚ)) b * ((x + (a : ℚ)) + (b : ℚ)) := by
            simpa using P.rp_succ (x + (a : ℚ)) b
          rw [hs]

private lemma rp_split_of_le (x : ℚ) {a b : ℕ} (h : a ≤ b) :
    rp x b = rp x a * rp (x + (a : ℚ)) (b - a) := by
  have hb : b = a + (b - a) := (Nat.add_sub_of_le h).symm
  conv_lhs => rw [hb]
  exact rp_add x a (b - a)

private def A_summand_factorization_target (n s j : ℕ) : Prop :=
  j ≤ s → s ≤ n →
    coeff n j * inner n j (s - j) =
      ACommon n s * P.pfF (B n) (C n) (D n) s j

private def A_statement (n s : ℕ) : Prop :=
  s ≤ n →
    (∑ j ∈ Finset.range (s + 1), coeff n j * inner n j (s - j)) = transformedF43Term n s

private def B_statement (n j : ℕ) : Prop :=
  j ≤ n →
    pref n * coeff n j * (∑ l ∈ Finset.range (n - j + 1), inner n j l) = lhsF43Term n j

private theorem B_inner_sum_closed_form (n j : ℕ) (hj : j ≤ n) :
    (∑ l ∈ Finset.range (n - j + 1), inner n j l) =
      rp (-(n : ℚ)) (n - j) * rp (((j + 1 : ℕ) : ℚ)) (n - j) /
        (rp (-((2 * n : ℕ) : ℚ) + (j : ℚ)) (n - j) *
          rp (((n + 1 : ℕ) : ℚ)) (n - j)) := by
  simpa [inner, pow_two] using Q.inner_pfaff_closed_form n j hj

private lemma fcz (k : ℕ) : (Nat.factorial k : ℚ) ≠ 0 := by
  exact_mod_cast (Nat.factorial_pos k).ne'

private lemma rpo (k : ℕ) : rp 1 k = (Nat.factorial k : ℚ) := by
  induction k with
  | zero => simp [rp]
  | succ k ih =>
      rw [show rp 1 (k + 1) = rp 1 k * (1 + (k : ℚ)) by
        simpa [rp] using P.rp_succ 1 k]
      rw [ih, Nat.factorial_succ]
      norm_num [Nat.cast_mul, Nat.cast_add]
      ring

private lemma rpn (m k : ℕ) (hk : k ≤ m) :
    rp (-(m : ℚ)) k = (-1 : ℚ) ^ k * (m.descFactorial k : ℚ) := by
  induction k with
  | zero => simp [rp]
  | succ k ih =>
      have hk_le : k ≤ m := Nat.le_of_succ_le hk
      rw [show rp (-(m : ℚ)) (k + 1) = rp (-(m : ℚ)) k * (-(m : ℚ) + (k : ℚ)) by
        simpa [rp] using P.rp_succ (-(m : ℚ)) k]
      rw [ih hk_le, Nat.descFactorial_succ]
      have hsub : ((m - k : ℕ) : ℚ) = (m : ℚ) - (k : ℚ) := by
        exact Nat.cast_sub hk_le
      rw [Nat.cast_mul, hsub]
      ring

private lemma rpa (m k : ℕ) : rp (m : ℚ) k = (m.ascFactorial k : ℚ) := by
  induction k with
  | zero => simp [rp]
  | succ k ih =>
      rw [show rp (m : ℚ) (k + 1) = rp (m : ℚ) k * ((m : ℚ) + (k : ℚ)) by
        simpa [rp] using P.rp_succ (m : ℚ) k]
      rw [ih, Nat.ascFactorial_succ]
      norm_num [Nat.cast_mul, Nat.cast_add]
      ring

private lemma rp_neg_self_sq_eq_rp_one_sq (k : ℕ) :
    rp (-(k : ℚ)) k ^ 2 = rp 1 k ^ 2 := by
  rw [rpn k k le_rfl, rpo]
  rw [Nat.descFactorial_self]
  rw [mul_pow]
  have hsgn : ((-1 : ℚ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨k, by ring⟩
  rw [hsgn, one_mul]

private lemma rpnz (m k : ℕ) (hk : k ≤ m) : rp (-(m : ℚ)) k ≠ 0 := by
  rw [rpn m k hk]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast (Nat.descFactorial_pos.2 hk).ne')

private lemma rpp (x : ℚ) (k : ℕ) (hx : 0 < x) : 0 < rp x k := by
  unfold rp
  exact Finset.prod_pos fun i hi => by
    have hi0 : (0 : ℚ) ≤ i := by exact_mod_cast (Nat.zero_le i)
    linarith

private lemma rpzp (x : ℚ) (k : ℕ) (hx : 0 < x) : rp x k ≠ 0 :=
  (rpp x k hx).ne'

private lemma rpdz (n j : ℕ) : rp (D n) j ≠ 0 := by
  unfold D
  apply rpzp
  positivity

private lemma rp_cons (x : ℚ) (k : ℕ) : rp x (k + 1) = x * rp (x + 1) k := by
  rw [show k + 1 = 1 + k by omega]
  calc
    rp x (1 + k) = rp x 1 * rp (x + (1 : ℚ)) k := rp_add x 1 k
    _ = x * rp (x + 1) k := by
        rw [show rp x 1 = x by
          simpa [rp] using P.rp_succ x 0]

private lemma rp_reflect (k : ℕ) (x : ℚ) :
    rp (1 - x - (k : ℚ)) k = (-1 : ℚ) ^ k * rp x k := by
  induction k generalizing x with
  | zero => simp [rp]
  | succ k ih =>
      have hstart : 1 - x - ((k + 1 : ℕ) : ℚ) = 1 - (x + 1) - (k : ℚ) := by
        norm_num [Nat.cast_add]
        ring
      rw [hstart]
      rw [show rp (1 - (x + 1) - (k : ℚ)) (k + 1) =
          rp (1 - (x + 1) - (k : ℚ)) k * ((1 - (x + 1) - (k : ℚ)) + (k : ℚ)) by
        simpa using P.rp_succ (1 - (x + 1) - (k : ℚ)) k]
      rw [ih (x + 1)]
      rw [rp_cons x k]
      norm_num [Nat.cast_add]
      ring

private lemma rp_complement_formula (a : ℚ) {j s : ℕ} (hj : j ≤ s)
    (hden : rp (1 - a - (s : ℚ)) j ≠ 0) :
    rp a (s - j) / (Nat.factorial (s - j) : ℚ) =
      rp a s / (Nat.factorial s : ℚ) *
        rp (-(s : ℚ)) j / rp (1 - a - (s : ℚ)) j := by
  set l : ℕ := s - j
  have hs : s = l + j := by
    dsimp [l]
    omega
  have hsplit : rp a s = rp a l * rp (a + (l : ℚ)) j := by
    conv_lhs => rw [hs]
    exact rp_add a l j
  have href : rp (1 - a - (s : ℚ)) j = (-1 : ℚ) ^ j * rp (a + (l : ℚ)) j := by
    have harg : 1 - a - (s : ℚ) = 1 - (a + (l : ℚ)) - (j : ℚ) := by
      rw [hs]
      norm_num [Nat.cast_add]
      ring
    rw [harg]
    exact rp_reflect j (a + (l : ℚ))
  have hneg : rp (-(s : ℚ)) j = (-1 : ℚ) ^ j * (s.descFactorial j : ℚ) :=
    rpn s j hj
  have hfacrel : ((Nat.factorial (s - j) : ℚ) * (s.descFactorial j : ℚ)) =
      (Nat.factorial s : ℚ) := by
    have h := Nat.factorial_mul_descFactorial hj
    exact_mod_cast h
  have hfacl : (Nat.factorial (s - j) : ℚ) ≠ 0 := fcz (s - j)
  have hfacs : (Nat.factorial s : ℚ) ≠ 0 := fcz s
  rw [hsplit, href, hneg]
  have hsgn : (-1 : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hrpl : rp (a + (l : ℚ)) j ≠ 0 := by
    intro hz
    apply hden
    rw [href, hz]
    simp

  field_simp [hden, hfacl, hfacs, hsgn, hrpl]
  rw [← hfacrel]
  ring

private lemma A_pfaff_recHyp (n s : ℕ) (hsn : s ≤ n) :
    ∀ m < s, P.pfRecHyp (B n) (C n) (D n) m := by
  intro m hm
  unfold P.pfRecHyp
  constructor
  · unfold D
    positivity
  constructor
  · unfold B C D
    norm_num [Nat.cast_add, Nat.cast_mul]
    have hmle : (m : ℚ) < (n : ℚ) := by exact_mod_cast (lt_of_lt_of_le hm hsn)
    linarith
  constructor
  · unfold B C D
    norm_num [Nat.cast_add, Nat.cast_mul]
    have hmle : (m : ℚ) < (n : ℚ) := by exact_mod_cast (lt_of_lt_of_le hm hsn)
    linarith
  constructor
  · intro hzero
    unfold B C D at hzero
    norm_num [Nat.cast_add, Nat.cast_mul] at hzero
    have hpos : (0 : ℚ) < 2 * (n : ℚ) + 1 := by positivity
    linarith
  constructor
  · intro k hk
    apply rpzp
    unfold D
    positivity
  constructor
  · intro k hk
    apply rpzp
    unfold B C D
    norm_num [Nat.cast_add, Nat.cast_mul]
    have hmle : (m : ℚ) < (n : ℚ) := by exact_mod_cast (lt_of_lt_of_le hm hsn)
    linarith
  constructor
  · apply rpzp
    unfold B C D
    norm_num [Nat.cast_add, Nat.cast_mul]
    have hmle : (m : ℚ) < (n : ℚ) := by exact_mod_cast (lt_of_lt_of_le hm hsn)
    linarith
  constructor
  · have harg : D n - B n - C n = -(((2 * n + 1 : ℕ)) : ℚ) := by
      unfold B C D
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    rw [harg]
    apply rpnz
    omega
  · intro k hk
    constructor
    · unfold D
      positivity
    constructor
    · unfold B C D
      norm_num [Nat.cast_add, Nat.cast_mul]
      have hmle : (m : ℚ) < (n : ℚ) := by exact_mod_cast (lt_of_lt_of_le hm hsn)
      have hkq : (k : ℚ) < (m : ℚ) := by exact_mod_cast hk
      linarith
    · unfold B C D
      norm_num [Nat.cast_add, Nat.cast_mul]
      have hmle : (m : ℚ) < (n : ℚ) := by exact_mod_cast (lt_of_lt_of_le hm hsn)
      have hkq : (k : ℚ) < (m : ℚ) := by exact_mod_cast hk
      linarith

private theorem A_pfaff_closed_form_direct (n s : ℕ) (hsn : s ≤ n) :
    (∑ j ∈ Finset.range (s + 1), P.pfF (B n) (C n) (D n) s j) =
      rp (D n - B n) s * rp (D n - C n) s /
        (rp (D n) s * rp (D n - B n - C n) s) := by
  have hpf := P.pfaff_saalschutz_finite_explicit_of_cert (B n) (C n) (D n) s
    (A_pfaff_recHyp n s hsn) ?_
  · simpa [P.pfF]
      using hpf
  · intro m hm k hk
    have Hm := A_pfaff_recHyp n s hsn m hm
    rcases Hm with ⟨hcn, hcabn, hd, habc, hcAll, hdAll, hd0top, hcab0, hlocal⟩
    rcases hlocal k hk with ⟨hck, hdk, hdlast⟩
    have hkn1 : (k : ℚ) - (m : ℚ) - 1 ≠ 0 := by
      have hle : (k : ℚ) ≤ (m : ℚ) := by exact_mod_cast (Nat.le_of_lt hk)
      linarith
    have hkn : (k : ℚ) - (m : ℚ) ≠ 0 := by
      have hlt : (k : ℚ) < (m : ℚ) := by exact_mod_cast hk
      linarith
    exact P.pf_gosper_certificate_core_nat
      (a := B n) (b := C n) (c := D n) (m := m) (k := k)
      hcn hcabn hkn1 hkn hd hck hdk



private lemma A_summand_factorization_alg (u b c d v fj x fs e ps den y : ℚ)
    (hd : d ≠ 0) (hv : v ≠ 0) (hfj : fj ≠ 0) (hfs : fs ≠ 0) (hden : den ≠ 0)
    (hy : y ≠ 0) :
    (u ^ 2 * b * c / (d * v ^ 2 * fj)) *
        (x * x * (fs * (e * ps / den)) / (y ^ 2 * fs)) =
      ((u * x) ^ 2 / (v * y) ^ 2 * e) * (ps * b * c / (d * den * fj)) := by
  field_simp [hd, hv, hfj, hfs, hden, hy]

private lemma A_summand_factorization (n s j : ℕ) : A_summand_factorization_target n s j := by
  intro hj hsn
  have hjn : j ≤ n := le_trans hj hsn
  have h2jn : j ≤ 2 * n := by omega
  have h2sn : s ≤ 2 * n := by omega
  have hdencomp : rp (1 - (-((2 * n : ℕ) : ℚ) - 1) - (s : ℚ)) j ≠ 0 := by
    have harg : 1 - (-((2 * n : ℕ) : ℚ) - 1) - (s : ℚ) = ((2 * n + 2 - s : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : s ≤ 2 * n + 2)]
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    rw [harg]
    apply rpzp
    exact_mod_cast (by omega : 0 < 2 * n + 2 - s)
  have hcomp := rp_complement_formula (-((2 * n : ℕ) : ℚ) - 1) hj hdencomp
  have hfac_sj : (Nat.factorial (s - j) : ℚ) ≠ 0 := fcz (s - j)
  have hE : rp (-((2 * n : ℕ) : ℚ) - 1) (s - j) =
      (Nat.factorial (s - j) : ℚ) *
        (rp (-((2 * n : ℕ) : ℚ) - 1) s / (Nat.factorial s : ℚ) *
          rp (-(s : ℚ)) j /
            rp (1 - (-((2 * n : ℕ) : ℚ) - 1) - (s : ℚ)) j) := by
    rw [← hcomp]
    field_simp [hfac_sj]

  have hnsub : -((n - j : ℕ) : ℚ) = -(n : ℚ) + (j : ℚ) := by
    rw [Nat.cast_sub hjn]
    ring
  have hdenpf : 1 + B n + C n - D n - (s : ℚ) =
      1 - (-((2 * n : ℕ) : ℚ) - 1) - (s : ℚ) := by
    unfold B C D
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  unfold coeff inner ACommon P.pfF
  rw [hnsub]
  rw [hE]
  rw [hdenpf]
  have hdenD : rp (D n) j ≠ 0 := rpdz n j
  have hfj : (Nat.factorial j : ℚ) ≠ 0 := fcz j
  have hv : rp (-((2 * n : ℕ) : ℚ)) j ≠ 0 := by
    apply rpnz
    omega
  have hy : rp (-((2 * n : ℕ) : ℚ) + (j : ℚ)) (s - j) ≠ 0 := by
    have harg : -(((2 * n - j : ℕ) : ℚ)) = -((2 * n : ℕ) : ℚ) + (j : ℚ) := by
      rw [Nat.cast_sub h2jn]
      ring
    rw [← harg]
    apply rpnz
    omega
  rw [rp_split_of_le (-(n : ℚ)) hj]
  rw [rp_split_of_le (-((2 * n : ℕ) : ℚ)) hj]
  exact
    A_summand_factorization_alg
      (u := rp (-(n : ℚ)) j) (b := rp (B n) j) (c := rp (C n) j)
      (d := rp (D n) j) (v := rp (-((2 * n : ℕ) : ℚ)) j)
      (fj := (Nat.factorial j : ℚ)) (x := rp (-(n : ℚ) + (j : ℚ)) (s - j))
      (fs := (Nat.factorial (s - j) : ℚ))
      (e := rp (-((2 * n : ℕ) : ℚ) - 1) s / (Nat.factorial s : ℚ))
      (ps := rp (-(s : ℚ)) j)
      (den := rp (1 - (-((2 * n : ℕ) : ℚ) - 1) - (s : ℚ)) j)
      (y := rp (-((2 * n : ℕ) : ℚ) + (j : ℚ)) (s - j))
      hdenD hv hfj hfac_sj hdencomp hy

private lemma A_closed_form_simplification (n s : ℕ) (hsn : s ≤ n) :
    ACommon n s *
        (rp (D n - B n) s * rp (D n - C n) s /
          (rp (D n) s * rp (D n - B n - C n) s)) = transformedF43Term n s := by
  have hDB : D n - B n = -(n : ℚ) / 2 := by
    unfold B D
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  have hDC : D n - C n = -((n : ℚ) + 1) / 2 := by
    unfold C D
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  have hDBC : D n - B n - C n = -(((2 * n + 1 : ℕ)) : ℚ) := by
    unfold B C D
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  have hnum : -((2 * n : ℕ) : ℚ) - 1 = -(((2 * n + 1 : ℕ)) : ℚ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  have hden2 : rp (-((2 * n : ℕ) : ℚ)) s ≠ 0 := rpnz (2 * n) s (by omega)
  have hdenD : rp (D n) s ≠ 0 := rpdz n s
  have hfac : (Nat.factorial s : ℚ) ≠ 0 := fcz s
  have hcancel : rp (-(((2 * n + 1 : ℕ)) : ℚ)) s ≠ 0 := by
    apply rpnz
    omega
  unfold ACommon transformedF43Term
  rw [hDBC, hDB, hDC, hnum]
  field_simp [hden2, hdenD, hfac, hcancel]

private theorem A_statement_proof (n s : ℕ) : A_statement n s := by
  intro hsn
  have hfac := A_summand_factorization n s
  calc
    (∑ j ∈ Finset.range (s + 1), coeff n j * inner n j (s - j))
        = ∑ j ∈ Finset.range (s + 1), ACommon n s * P.pfF (B n) (C n) (D n) s j := by
          refine Finset.sum_congr rfl ?_
          intro j hjmem
          have hjlt : j < s + 1 := Finset.mem_range.mp hjmem
          have hj : j ≤ s := by omega
          exact hfac j hj hsn
    _ = ACommon n s * (∑ j ∈ Finset.range (s + 1), P.pfF (B n) (C n) (D n) s j) := by
          rw [Finset.mul_sum]
    _ = ACommon n s *
        (rp (D n - B n) s * rp (D n - C n) s /
          (rp (D n) s * rp (D n - B n - C n) s)) := by
          have hpf := A_pfaff_closed_form_direct n s hsn
          simpa [P.pfF] using congrArg (fun x => ACommon n s * x) hpf
    _ = transformedF43Term n s := A_closed_form_simplification n s hsn

private lemma B_pref_closed_factor (n j : ℕ) (hj : j ≤ n) :
    pref n *
        (rp (-(n : ℚ)) (n - j) * rp (((j + 1 : ℕ) : ℚ)) (n - j) /
          (rp (-((2 * n : ℕ) : ℚ) + (j : ℚ)) (n - j) *
            rp (((n + 1 : ℕ) : ℚ)) (n - j))) =
      rp (-(2 * n : ℕ) : ℚ) j ^ 2 / rp 1 j ^ 2 := by
  have harg2 : -(((2 * n - j : ℕ) : ℚ)) = (-((2 * n : ℕ) : ℚ) + (j : ℚ)) := by
    have hj2' : j ≤ 2 * n := by omega
    rw [Nat.cast_sub hj2']
    ring
  unfold pref
  rw [S.prefactor]
  change (S.rp (-((2 * n : ℕ) : ℚ)) n / S.rp (-(n : ℚ)) n) ^ 2 *
        (rp (-(n : ℚ)) (n - j) * rp (((j + 1 : ℕ) : ℚ)) (n - j) /
          (rp (-((2 * n : ℕ) : ℚ) + (j : ℚ)) (n - j) *
            rp (((n + 1 : ℕ) : ℚ)) (n - j))) =
      rp (-(2 * n : ℕ) : ℚ) j ^ 2 / rp 1 j ^ 2
  -- Replace the `S.rp` occurrences from the imported prefactor by the local `rp`.
  change (rp (-((2 * n : ℕ) : ℚ)) n / rp (-(n : ℚ)) n) ^ 2 *
        (rp (-(n : ℚ)) (n - j) * rp (((j + 1 : ℕ) : ℚ)) (n - j) /
          (rp (-((2 * n : ℕ) : ℚ) + (j : ℚ)) (n - j) *
            rp (((n + 1 : ℕ) : ℚ)) (n - j))) =
      rp (-(2 * n : ℕ) : ℚ) j ^ 2 / rp 1 j ^ 2
  rw [rpn n (n - j) (by omega)]
  rw [rpa (j + 1) (n - j)]
  rw [← harg2, rpn (2 * n - j) (n - j) (by omega)]
  rw [rpa (n + 1) (n - j)]
  rw [rpn (2 * n) n (by omega)]
  rw [rpn n n le_rfl]
  rw [rpn (2 * n) j (by omega)]
  rw [rpo]
  have hA : (j + 1).ascFactorial (n - j) = n.descFactorial (n - j) := by
    have h := Nat.add_descFactorial_eq_ascFactorial j (n - j)
    simpa [Nat.add_sub_of_le hj] using h.symm
  have hB : (n + 1).ascFactorial (n - j) = (2 * n - j).descFactorial (n - j) := by
    have h := Nat.add_descFactorial_eq_ascFactorial n (n - j)
    have hadd : n + (n - j) = 2 * n - j := by omega
    simpa [hadd] using h.symm
  rw [hA, hB]
  have hfacj : (Nat.factorial j : ℚ) ≠ 0 := fcz j
  have hnDesc : (n.descFactorial (n - j) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.2 (by omega : n - j ≤ n)).ne'
  have h2Desc : ((2 * n - j).descFactorial (n - j) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.2 (by omega : n - j ≤ 2 * n - j)).ne'
  have hnFull : (n.descFactorial n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.2 le_rfl).ne'
  have h2Full : ((2 * n).descFactorial n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.2 (by omega : n ≤ 2 * n)).ne'
  have hsignn : (-1 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hfacj, hnDesc, h2Desc, hnFull, h2Full, hsignn]
  have hsgnj : ((-1 : ℚ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨j, by ring⟩
  rw [hsgnj]
  have hnrel : (Nat.factorial j : ℚ) * (n.descFactorial (n - j) : ℚ) =
      (n.descFactorial n : ℚ) := by
    have h := Nat.factorial_mul_descFactorial (show n - j ≤ n by omega)
    rw [show n - (n - j) = j by omega] at h
    simpa [Nat.descFactorial_self] using (show ((j.factorial * n.descFactorial (n - j) : ℕ) : ℚ) = (n.factorial : ℚ) by exact_mod_cast h)
  have h2rel : ((2 * n - j).descFactorial (n - j) : ℚ) *
      ((2 * n).descFactorial j : ℚ) = ((2 * n).descFactorial n : ℚ) := by
    have h := Nat.descFactorial_mul_descFactorial (n := 2 * n) (k := j) (m := n) hj
    exact_mod_cast h
  rw [← hnrel, ← h2rel]
  ring

private theorem B_statement_proof (n j : ℕ) : B_statement n j := by
  intro hj
  rw [B_inner_sum_closed_form n j hj]
  unfold coeff lhsF43Term
  have hbridge := B_pref_closed_factor n j hj
  have hden2 : rp (-(2 * n : ℕ) : ℚ) j ≠ 0 := rpnz (2 * n) j (by omega)
  have hdenD : rp (D n) j ≠ 0 := rpdz n j
  have hfac : (Nat.factorial j : ℚ) ≠ 0 := fcz j
  have hrp1 : rp 1 j ≠ 0 := by rw [rpo]; exact hfac
  set a := rp (-(n : ℚ)) j ^ 2 * rp (B n) j * rp (C n) j
  set c := rp (-(n : ℚ)) (n - j) * rp (((j + 1 : ℕ) : ℚ)) (n - j) /
    (rp (-((2 * n : ℕ) : ℚ) + (j : ℚ)) (n - j) * rp (((n + 1 : ℕ) : ℚ)) (n - j))
  set q := rp (D n) j * rp (-(2 * n : ℕ) : ℚ) j ^ 2 * (Nat.factorial j : ℚ)
  change pref n * (a / q) * c = a / (rp 1 j ^ 2 * rp (D n) j * (Nat.factorial j : ℚ))
  calc
    pref n * (a / q) * c = (pref n * c) * (a / q) := by ring
    _ = (rp (-(2 * n : ℕ) : ℚ) j ^ 2 / rp 1 j ^ 2) * (a / q) := by rw [hbridge]
    _ = a / (rp 1 j ^ 2 * rp (D n) j * (Nat.factorial j : ℚ)) := by
        subst q
        field_simp [hden2, hdenD, hfac, hrp1]

private lemma triangle_reindex_sum (n : ℕ) (F : ℕ → ℕ → ℚ) :
    (∑ s ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (s + 1), F j (s - j)) =
      ∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n - j + 1), F j l := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hleft :
          (∑ s ∈ Finset.range (n.succ + 1), ∑ j ∈ Finset.range (s + 1), F j (s - j)) =
            (∑ s ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (s + 1), F j (s - j)) +
              ∑ j ∈ Finset.range (n + 2), F j (n + 1 - j) := by
        rw [show n.succ + 1 = n + 2 by omega]
        rw [show n + 2 = (n + 1) + 1 by omega]
        rw [Finset.sum_range_succ]
      have hright_step :
          (∑ j ∈ Finset.range (n.succ + 1), ∑ l ∈ Finset.range (n.succ - j + 1), F j l) =
            (∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n - j + 1), F j l) +
              ∑ j ∈ Finset.range (n + 2), F j (n + 1 - j) := by
        rw [show n.succ + 1 = n + 2 by omega]
        rw [show n + 2 = (n + 1) + 1 by omega]
        rw [Finset.sum_range_succ]
        have hsplit :
            (∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n.succ - j + 1), F j l) =
              (∑ j ∈ Finset.range (n + 1),
                  ((∑ l ∈ Finset.range (n - j + 1), F j l) + F j (n + 1 - j))) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hjle : j ≤ n := by exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hlen : n.succ - j + 1 = (n - j + 1) + 1 := by omega
          rw [hlen, Finset.sum_range_succ]
          rw [← Nat.sub_add_comm hjle]
        rw [hsplit]
        rw [Finset.sum_add_distrib]
        have hlast : (∑ l ∈ Finset.range (n.succ - (n + 1) + 1), F (n + 1) l) = F (n + 1) 0 := by
          simp
        rw [hlast]
        have hdiag :
            (∑ j ∈ Finset.range (n + 2), F j (n + 1 - j)) =
              (∑ j ∈ Finset.range (n + 1), F j (n + 1 - j)) + F (n + 1) 0 := by
          rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ]
          rw [show n + 1 - (n + 1) = 0 by omega]
        rw [hdiag]
        ring
      rw [hleft, hright_step, ih]

private lemma searsTransformedSum_eq_transformedF43Term_sum (n : ℕ) :
    S.searsTransformedSum n =
      ∑ s ∈ Finset.range (n + 1), transformedF43Term n s := by
  unfold S.searsTransformedSum S.F43Sum S.F43Term transformedF43Term D
  refine Finset.sum_congr rfl ?_
  intro s hs
  simp only [S.rp, rp, P.rp]
  ring

private lemma searsLHS_eq_lhsF43Term_sum (n : ℕ) :
    S.searsLHS n =
      ∑ j ∈ Finset.range (n + 1), lhsF43Term n j := by
  unfold S.searsLHS S.F43Sum S.F43Term lhsF43Term B C D
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp only [S.rp, rp, P.rp]
  ring

private theorem ssp (n : ℕ) : S.ss n := by
  unfold S.ss
  rw [searsLHS_eq_lhsF43Term_sum, searsTransformedSum_eq_transformedF43Term_sum]
  change (∑ j ∈ Finset.range (n + 1), lhsF43Term n j) =
    pref n * (∑ s ∈ Finset.range (n + 1), transformedF43Term n s)
  have hA_sum :
      (∑ s ∈ Finset.range (n + 1), transformedF43Term n s) =
        ∑ s ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (s + 1), coeff n j * inner n j (s - j) := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    have hsn : s ≤ n := by exact Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    exact (A_statement_proof n s hsn).symm
  have htri := triangle_reindex_sum n (fun j l => coeff n j * inner n j l)
  calc
    (∑ j ∈ Finset.range (n + 1), lhsF43Term n j)
        = ∑ j ∈ Finset.range (n + 1),
            pref n * coeff n j * (∑ l ∈ Finset.range (n - j + 1), inner n j l) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hjn : j ≤ n := by exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          exact (B_statement_proof n j hjn).symm
    _ = pref n * (∑ j ∈ Finset.range (n + 1),
            coeff n j * (∑ l ∈ Finset.range (n - j + 1), inner n j l)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = pref n * (∑ j ∈ Finset.range (n + 1),
            ∑ l ∈ Finset.range (n - j + 1), coeff n j * inner n j l) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Finset.mul_sum]
    _ = pref n * (∑ s ∈ Finset.range (n + 1),
            ∑ j ∈ Finset.range (s + 1), coeff n j * inner n j (s - j)) := by
          rw [htri]
    _ = pref n * (∑ s ∈ Finset.range (n + 1), transformedF43Term n s) := by
          rw [hA_sum]

end R

private lemma tIdS (n : ℕ) : tstmt n := by
  unfold tstmt trhs tpref
  have hs := R.ssp n
  unfold S.ss at hs
  let C3 : ℚ := (Nat.choose (3 * n) n : ℚ)
  let SS : ℚ := ∑ j ∈ Finset.range (n + 1), tsumnd n j
  have hC3 : C3 ≠ 0 := by
    dsimp [C3]
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 3 * n)).ne'
  have hLmul : S.searsLHS n * C3 = ((a n : ℕ) : ℚ) := by
    rw [S.slsum]
    unfold a S.slbin C3
    rw [Nat.cast_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
    field_simp [show (Nat.choose (3 * n) n : ℚ) ≠ 0 by exact hC3]
  have hL : S.searsLHS n = ((a n : ℕ) : ℚ) / C3 := by
    rw [eq_div_iff hC3]
    exact hLmul
  have hT : S.searsTransformedSum n = SS := by
    rw [S.stsum]
    dsimp [SS]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rfl
  rw [hL, hT] at hs
  have hmul := congrArg (fun x : ℚ => x * C3) hs
  field_simp [hC3] at hmul
  dsimp [SS, C3] at hmul ⊢
  rw [hmul]
  simp only [Nat.cast_mul, Nat.cast_pow]

theorem oeis_374605_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ,
    (2 * p + 3) / 3 ≤ n →
    n ≤ p - 1 →
    (p ^ 3 : ℕ) ∣ a n := by
  intro n hnlow hnhigh
  exact main_of_int p n hp hp5 hnlow hnhigh
    (it_of_tid n (tIdS n))
