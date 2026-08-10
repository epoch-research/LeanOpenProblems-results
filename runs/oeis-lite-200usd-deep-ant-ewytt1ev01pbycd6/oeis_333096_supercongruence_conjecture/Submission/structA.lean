import Submission.mainformula
open PowerSeries Finset

/-- Lower support: `qser^j` has order `≥ j`. -/
lemma qpow_low (p : ℕ) : ∀ (j N : ℕ), N < j → (PowerSeries.coeff N) (qser p ^ j) = 0 := by
  intro j
  induction j with
  | zero => intro N hN; omega
  | succ k ih =>
    intro N hN
    rw [pow_succ, coeffMul]
    apply Finset.sum_eq_zero
    intro a ha
    rw [Finset.mem_range] at ha
    -- term: coeff a (qser^k) * coeff (N-a) (qser)
    -- qser coeff nonzero only for 1≤ idx ≤ p-1
    by_cases hidx : 1 ≤ N - a ∧ N - a ≤ p - 1
    · -- then N - a ≥ 1, so a ≤ N-1 < k, use ih on coeff a (qser^k)
      have : a < k := by omega
      rw [ih a this, zero_mul]
    · rw [coeff_qser, show qc p (N - a) = 0 by unfold qc; rw [if_neg hidx], mul_zero]

/-- coeff 0 of qser^j is 0 for j ≥ 1. -/
lemma qpow_coeff0 (p j : ℕ) (hj : 1 ≤ j) : (PowerSeries.coeff 0) (qser p ^ j) = 0 :=
  qpow_low p j 0 (by omega)

/-- coeff 0 of qser^j*Gser is 0 for j ≥ 1. -/
lemma qpowG_coeff0 (p j : ℕ) (hj : 1 ≤ j) : (PowerSeries.coeff 0) (qser p ^ j * Gser) = 0 := by
  rw [coeffMulG, Finset.sum_range_one, qpow_coeff0 p j hj, zero_mul]

/-- Lower support of the product: `coeff N = 0` for `N < j`. -/
lemma qpowG_low (p j N : ℕ) (hN : N < j) : (PowerSeries.coeff N) (qser p ^ j * Gser) = 0 := by
  rw [coeffMulG]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  rw [qpow_low p j k (by omega), zero_mul]

/-- Upper support of the product: `coeff N = 0` for `N > j*(p-1)`, `j ≥ 1`. -/
lemma qpowG_high (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ (j : ℕ), 1 ≤ j → ∀ (N : ℕ), j * (p - 1) < N → (PowerSeries.coeff N) (qser p ^ j * Gser) = 0 := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro N hN
    rw [pow_one]
    exact qG_coeff_zero p hp hp5 N (by omega)
  | succ k hk ih =>
    intro N hN
    -- qser^(k+1) * G = qser * (qser^k * G)
    rw [pow_succ, mul_comm (qser p ^ k) (qser p), mul_assoc, coeffMul]
    apply Finset.sum_eq_zero
    intro a ha
    rw [Finset.mem_range] at ha
    by_cases hidx : 1 ≤ a ∧ a ≤ p - 1
    · -- coeff (N-a) (qser^k * G) = 0 since N-a > k*(p-1)
      have hexp : (k + 1) * (p - 1) = k * (p - 1) + (p - 1) := by ring
      have : k * (p - 1) < N - a := by omega
      rw [ih (N - a) this, mul_zero]
    · rw [coeff_qser, show qc p a = 0 by unfold qc; rw [if_neg hidx], zero_mul]

/-- Convolution with `qser` expressed as a sum over `range (p+1)`, valid when `coeff 0 H = 0`. -/
lemma qmul_coeff (p n : ℕ) (H : PowerSeries ℤ) (h0 : (PowerSeries.coeff 0) H = 0) :
    (PowerSeries.coeff n) (qser p * H)
      = ∑ a ∈ range (p + 1), qc p a * (PowerSeries.coeff (n - a)) H := by
  rw [coeffMul]
  simp only [coeff_qser]
  have e1 : ∑ a ∈ range (n + 1), qc p a * (PowerSeries.coeff (n - a)) H
          = ∑ a ∈ range (n + p + 1), qc p a * (PowerSeries.coeff (n - a)) H := by
    apply Finset.sum_subset
    · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    · intro x hx hxns
      rw [Finset.mem_range] at hxns
      rw [show n - x = 0 by omega, h0, mul_zero]
  have e2 : ∑ a ∈ range (p + 1), qc p a * (PowerSeries.coeff (n - a)) H
          = ∑ a ∈ range (n + p + 1), qc p a * (PowerSeries.coeff (n - a)) H := by
    apply Finset.sum_subset
    · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    · intro x hx hxns
      rw [Finset.mem_range] at hxns
      rw [show qc p x = 0 by unfold qc; rw [if_neg (by omega)], zero_mul]
  rw [e1, ← e2]

/-- Antipalindrome symmetry about `j*p/2`. -/
lemma qpowG_anti (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ (j : ℕ), 1 ≤ j → ∀ (n : ℕ),
      (PowerSeries.coeff n) (qser p ^ j * Gser)
        + (PowerSeries.coeff (j * p - n)) (qser p ^ j * Gser) = 0 := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro n
    simp only [pow_one, one_mul]
    by_cases hn : n ≤ p
    · have hD := Dzero p hp hp5 n hn
      unfold Dd Rr at hD
      linarith [hD]
    · have h1 : (PowerSeries.coeff n) (qser p * Gser) = 0 :=
        qG_coeff_zero p hp hp5 n (by omega)
      have h2 : (PowerSeries.coeff (p - n)) (qser p * Gser) = 0 := by
        rw [show p - n = 0 by omega]
        have := qpowG_coeff0 p 1 (by norm_num)
        rwa [pow_one] at this
      rw [h1, h2]; ring
  | succ k hk ih =>
    have hPP : qser p ^ (k + 1) * Gser = qser p * (qser p ^ k * Gser) := by
      rw [pow_succ']; ring
    have h0 : (PowerSeries.coeff 0) (qser p ^ k * Gser) = 0 := qpowG_coeff0 p k hk
    have hexp : (k + 1) * p = k * p + p := by ring
    have hkp : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
    have key : ∀ n, n ≤ k * p →
        (PowerSeries.coeff n) (qser p ^ (k + 1) * Gser)
          + (PowerSeries.coeff ((k + 1) * p - n)) (qser p ^ (k + 1) * Gser) = 0 := by
      intro n hn
      rw [hPP, qmul_coeff p n _ h0, qmul_coeff p ((k + 1) * p - n) _ h0]
      have hrefl := Finset.sum_range_reflect
        (fun a => qc p a * (PowerSeries.coeff ((k + 1) * p - n - a)) (qser p ^ k * Gser)) (p + 1)
      simp only [Nat.add_sub_cancel] at hrefl
      rw [← hrefl, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.mem_range] at ha
      have ha_le : a ≤ p := by omega
      rw [qc_symm p a ha_le]
      have hidx : (k + 1) * p - n - (p - a) = k * p - n + a := by omega
      rw [hidx]
      have hih := ih (k * p - n + a)
      have hidx2 : k * p - (k * p - n + a) = n - a := by omega
      rw [hidx2] at hih
      have hsum : (PowerSeries.coeff (n - a)) (qser p ^ k * Gser)
          + (PowerSeries.coeff (k * p - n + a)) (qser p ^ k * Gser) = 0 := by linarith [hih]
      rw [← mul_add, hsum, mul_zero]
    intro n
    by_cases hn : n ≤ k * p
    · exact key n hn
    · by_cases hnM : n ≤ (k + 1) * p
      · have h' := key ((k + 1) * p - n) (by omega)
        rw [show (k + 1) * p - ((k + 1) * p - n) = n by omega] at h'
        linarith [h']
      · have hz1 : (PowerSeries.coeff n) (qser p ^ (k + 1) * Gser) = 0 := by
          apply qpowG_high p hp hp5 (k + 1) (by omega) n
          have he2 : (k + 1) * (p - 1) + (k + 1) = (k + 1) * p := by
            rw [← Nat.mul_succ]; congr 1; omega
          omega
        have hz2 : (PowerSeries.coeff ((k + 1) * p - n)) (qser p ^ (k + 1) * Gser) = 0 := by
          rw [show (k + 1) * p - n = 0 by omega]
          exact qpowG_coeff0 p (k + 1) (by omega)
        rw [hz1, hz2]; ring

/-- Cartier coefficient sequence `W`. -/
noncomputable def Wc (p j k : ℕ) : ℤ := (PowerSeries.coeff (p * k)) (qser p ^ j * Gser)

lemma Wc_anti (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) (hj : 1 ≤ j) (k : ℕ) :
    Wc p j k + Wc p j (j - k) = 0 := by
  unfold Wc
  have h := qpowG_anti p hp hp5 j hj (p * k)
  have he : j * p - p * k = p * (j - k) := by rw [Nat.mul_sub, mul_comm p j]
  rwa [he] at h

lemma Wc_high (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) (hj : 1 ≤ j) (k : ℕ) (hk : j ≤ k) :
    Wc p j k = 0 := by
  unfold Wc
  apply qpowG_high p hp hp5 j hj
  have h1 : j * (p - 1) = j * p - j := by rw [Nat.mul_sub, Nat.mul_one]
  have h2 : j * p ≤ p * k := by rw [mul_comm]; exact Nat.mul_le_mul_left p hk
  have h5 : 0 < j * p := Nat.mul_pos (by omega) (by omega)
  rw [h1]; omega

lemma Wc_zero (p j : ℕ) (hj : 1 ≤ j) : Wc p j 0 = 0 := by
  unfold Wc; rw [Nat.mul_zero]; exact qpowG_coeff0 p j hj

lemma Wc_total (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) (hj : 1 ≤ j) :
    ∑ k ∈ range (j + 1), Wc p j k = 0 := by
  have hrefl := Finset.sum_range_reflect (fun k => Wc p j k) (j + 1)
  simp only [Nat.add_sub_cancel] at hrefl
  have hneg : ∑ k ∈ range (j + 1), Wc p j (j - k) = - ∑ k ∈ range (j + 1), Wc p j k := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have := Wc_anti p hp hp5 j hj k
    linarith [this]
  rw [hneg] at hrefl
  linarith [hrefl]

/-- Prefix-sum reflection: the key to palindromy of the partial sums. -/
lemma Sc_pref (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) (hj : 1 ≤ j) (i : ℕ) (hi : i < j) :
    ∑ k ∈ range (i + 1), Wc p j k = ∑ k ∈ range (j - i), Wc p j k := by
  have hC : ∑ m ∈ Finset.Ico (i + 1) (j + 1), Wc p j m
          = ∑ k ∈ range (j - i), Wc p j (i + 1 + k) := by
    rw [Finset.sum_Ico_eq_sum_range, show (j + 1) - (i + 1) = j - i from by omega]
  have hD : (∑ k ∈ range (i + 1), Wc p j k)
              + (∑ m ∈ Finset.Ico (i + 1) (j + 1), Wc p j m) = 0 := by
    rw [Finset.sum_range_add_sum_Ico (fun k => Wc p j k) (show i + 1 ≤ j + 1 from by omega)]
    exact Wc_total p hp hp5 j hj
  have hB : ∑ k ∈ range (j - i), Wc p j (j - i - 1 - k)
          = - ∑ k ∈ range (j - i), Wc p j (i + 1 + k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hidx : j - (j - i - 1 - k) = i + 1 + k := by omega
    have hh := Wc_anti p hp hp5 j hj (j - i - 1 - k)
    rw [hidx] at hh
    linarith [hh]
  have hA := Finset.sum_range_reflect (fun k => Wc p j k) (j - i)
  calc ∑ k ∈ range (i + 1), Wc p j k
      = - ∑ m ∈ Finset.Ico (i + 1) (j + 1), Wc p j m := by linarith [hD]
    _ = - ∑ k ∈ range (j - i), Wc p j (i + 1 + k) := by rw [hC]
    _ = ∑ k ∈ range (j - i), Wc p j (j - i - 1 - k) := hB.symm
    _ = ∑ k ∈ range (j - i), Wc p j k := hA

/-- The palindromic sequence `S` = negative partial sums of `W`. -/
noncomputable def Sc (p j i : ℕ) : ℤ := - ∑ k ∈ range (i + 1), Wc p j k

theorem structA (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (j : ℕ) (hj : 3 ≤ j) :
    ∃ S : ℕ → ℤ,
      (∀ i, S i = S (j - 1 - i)) ∧
      (∀ i, j - 1 < i → S i = 0) ∧
      (∀ i, i < 1 + (j - 1) / p → S i = 0) ∧
      (∀ i, (PowerSeries.coeff (p * i)) (qser p ^ j * Gser)
              = (if i = 0 then - S 0 else S (i - 1) - S i)) := by
  have hj1 : 1 ≤ j := by omega
  refine ⟨Sc p j, ?_, ?_, ?_, ?_⟩
  · -- palindromy
    intro i
    by_cases hi : i < j
    · show - ∑ k ∈ range (i + 1), Wc p j k = - ∑ k ∈ range ((j - 1 - i) + 1), Wc p j k
      rw [show (j - 1 - i) + 1 = j - i from by omega, Sc_pref p hp hp5 j hj1 i hi]
    · -- i ≥ j: both zero
      have hup1 : Sc p j i = 0 := by
        show - ∑ k ∈ range (i + 1), Wc p j k = 0
        have heq : ∑ k ∈ range (i + 1), Wc p j k = ∑ k ∈ range (j + 1), Wc p j k := by
          symm; apply Finset.sum_subset
          · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
          · intro x hx hxns; rw [Finset.mem_range] at hx hxns
            exact Wc_high p hp hp5 j hj1 x (by omega)
        rw [heq, Wc_total p hp hp5 j hj1]; ring
      have hup2 : Sc p j (j - 1 - i) = 0 := by
        rw [show j - 1 - i = 0 from by omega]
        show - ∑ k ∈ range (0 + 1), Wc p j k = 0
        rw [Finset.sum_range_one, Wc_zero p j hj1]; ring
      rw [hup1, hup2]
  · -- support upper
    intro i hi
    show - ∑ k ∈ range (i + 1), Wc p j k = 0
    have heq : ∑ k ∈ range (i + 1), Wc p j k = ∑ k ∈ range (j + 1), Wc p j k := by
      symm; apply Finset.sum_subset
      · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
      · intro x hx hxns; rw [Finset.mem_range] at hx hxns
        exact Wc_high p hp hp5 j hj1 x (by omega)
    rw [heq, Wc_total p hp hp5 j hj1]; ring
  · -- support lower
    intro i hi
    show - ∑ k ∈ range (i + 1), Wc p j k = 0
    have hz : ∀ k ∈ range (i + 1), Wc p j k = 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      unfold Wc
      apply qpowG_low
      -- p * k < j
      have hdiv : p * ((j - 1) / p) ≤ j - 1 := Nat.mul_div_le (j - 1) p
      have : k ≤ (j - 1) / p := by omega
      have : p * k ≤ p * ((j - 1) / p) := Nat.mul_le_mul_left p this
      omega
    rw [Finset.sum_eq_zero hz]; ring
  · -- W = (X-1)·S relation
    intro i
    show (PowerSeries.coeff (p * i)) (qser p ^ j * Gser) = _
    have hW : (PowerSeries.coeff (p * i)) (qser p ^ j * Gser) = Wc p j i := rfl
    rw [hW]
    by_cases hi0 : i = 0
    · subst hi0
      rw [if_pos rfl]
      show Wc p j 0 = - Sc p j 0
      unfold Sc
      rw [Finset.sum_range_one]; ring
    · rw [if_neg hi0]
      show Wc p j i = Sc p j (i - 1) - Sc p j i
      unfold Sc
      rw [show i - 1 + 1 = i from by omega, Finset.sum_range_succ]
      ring
