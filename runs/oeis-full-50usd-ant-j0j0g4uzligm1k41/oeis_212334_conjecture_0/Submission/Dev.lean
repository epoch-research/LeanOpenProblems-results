import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def A212334 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (Finset.range n) fun k =>
      (n.choose k) * ((n - 1).choose k) * ((n + k - 1).choose k) ^ 2

/-- The summand term as an integer. -/
def term (n k : ℕ) : ℤ :=
  (n.choose k : ℤ) * ((n - 1).choose k) * ((n + k - 1).choose k) ^ 2

lemma A212334_pos (n : ℕ) (hn : 0 < n) :
    (A212334 n : ℤ) = ∑ k ∈ Finset.range n, term n k := by
  unfold A212334 term
  rw [if_neg (by omega)]
  push_cast
  rfl

-- valuation of choose (p^r) k
lemma fact_choose_pr (p r k : ℕ) (hp : Nat.Prime p) (hk0 : k ≠ 0) (hkn : k ≤ p ^ r) :
    (Nat.choose (p ^ r) k).factorization p = r - k.factorization p :=
  Nat.factorization_choose_prime_pow hp hkn hk0

-- valuation of choose (p^r - 1) k  = 0
lemma fact_choose_pr_sub_one (p r k : ℕ) (hp : Nat.Prime p) (hkn : k ≤ p ^ r - 1) :
    (Nat.choose (p ^ r - 1) k).factorization p = 0 := by
  have hpr : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp.pos
  -- identity: p^r * choose (p^r - 1) k = choose (p^r) (k+1) * (k+1)
  have hid : p ^ r * Nat.choose (p ^ r - 1) k
      = Nat.choose (p ^ r) (k + 1) * (k + 1) := by
    have := Nat.succ_mul_choose_eq (p ^ r - 1) k
    simp only [Nat.succ_eq_add_one] at this
    rw [Nat.sub_add_cancel hpr] at this
    linarith [this]
  have hk1 : k + 1 ≤ p ^ r := by omega
  have hadd := Nat.factorization_choose_prime_pow_add_factorization hp hk1 (Nat.succ_ne_zero k)
  have hcne : Nat.choose (p ^ r - 1) k ≠ 0 :=
    (Nat.choose_pos (by omega)).ne'
  -- take factorization of hid at p
  have hfac : (p ^ r * Nat.choose (p ^ r - 1) k).factorization p
      = (Nat.choose (p ^ r) (k + 1) * (k + 1)).factorization p := by rw [hid]
  rw [Nat.factorization_mul (pow_pos hp.pos r).ne' hcne,
    Nat.factorization_mul (Nat.choose_pos hk1).ne' (Nat.succ_ne_zero k),
    Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow_self hp] at hfac
  simp only [Nat.succ_eq_add_one] at hfac hadd
  omega

-- v_p(p^r + k) = v_p(k) for 1 ≤ k < p^r
lemma fact_pr_add (p r k : ℕ) (hp : Nat.Prime p) (hk0 : 0 < k) (hkn : k < p ^ r) :
    (p ^ r + k).factorization p = k.factorization p := by
  have hkne : k ≠ 0 := hk0.ne'
  have hpkne : p ^ r + k ≠ 0 := by positivity
  set t := k.factorization p with ht
  have htr : t < r := by
    by_contra h
    push_neg at h
    have hdvd : p ^ r ∣ k := by
      have : p ^ t ∣ k := Nat.ordProj_dvd k p
      exact dvd_trans (pow_dvd_pow p h) this
    exact absurd (Nat.le_of_dvd hk0 hdvd) (by omega)
  have hptk : p ^ t ∣ k := Nat.ordProj_dvd k p
  have hptpr : p ^ t ∣ p ^ r := pow_dvd_pow p htr.le
  have hnpt1k : ¬ p ^ (t + 1) ∣ k := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization hp hkne, ← ht]; omega
  have hpt1pr : p ^ (t + 1) ∣ p ^ r := pow_dvd_pow p htr
  apply le_antisymm
  · -- (p^r+k).factorization p ≤ t : ¬ p^(t+1) ∣ p^r+k
    by_contra hcon
    push_neg at hcon
    have hd : p ^ (t + 1) ∣ p ^ r + k :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hpkne).2 hcon
    exact hnpt1k ((Nat.dvd_add_right hpt1pr).1 hd)
  · -- t ≤ (p^r+k).factorization p : p^t ∣ p^r+k
    rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hpkne]
    exact Dvd.dvd.add hptpr hptk

-- v_p(choose (p^r + k - 1) k) = r - v_p(k) for 1 ≤ k < p^r
lemma fact_choose_pr_add (p r : ℕ) (hp : Nat.Prime p) :
    ∀ k, 1 ≤ k → k < p ^ r →
      (Nat.choose (p ^ r + k - 1) k).factorization p = r - k.factorization p := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    have : p ^ r + 1 - 1 = p ^ r := by omega
    rw [this, Nat.choose_one_right, Nat.factorization_pow_self hp, Nat.factorization_one]
    simp
  | succ k hk ih =>
    intro hk1lt
    have hklt : k < p ^ r := by omega
    have ihk := ih hklt
    have hpr1 : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp.pos
    -- p^r + k - 1 + 1 = p^r + k
    have he : p ^ r + k - 1 + 1 = p ^ r + k := by omega
    have hident := Nat.succ_mul_choose_eq (p ^ r + k - 1) k
    simp only [Nat.succ_eq_add_one, he] at hident
    -- hident : (p^r+k) * choose (p^r+k-1) k = choose (p^r+k) (k+1) * (k+1)
    -- note choose (p^r+k) (k+1) = choose (p^r + (k+1) - 1) (k+1)
    have he2 : p ^ r + (k + 1) - 1 = p ^ r + k := by omega
    rw [he2]
    -- factorization of both sides
    have hcne : Nat.choose (p ^ r + k - 1) k ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hc2ne : Nat.choose (p ^ r + k) (k + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hpak : p ^ r + k ≠ 0 := by positivity
    have hfac : ((p ^ r + k) * Nat.choose (p ^ r + k - 1) k).factorization p
        = (Nat.choose (p ^ r + k) (k + 1) * (k + 1)).factorization p := by rw [hident]
    rw [Nat.factorization_mul hpak hcne,
        Nat.factorization_mul hc2ne (Nat.succ_ne_zero k),
        Finsupp.add_apply, Finsupp.add_apply] at hfac
    rw [fact_pr_add p r k hp (by omega) hklt, ihk] at hfac
    simp only [Nat.succ_eq_add_one] at hfac
    -- hfac : v_p(k) + (r - v_p(k)) = v_p(choose (p^r+k)(k+1)) + v_p(k+1)
    have hvk : k.factorization p ≤ r := Nat.factorization_le_of_le_pow hklt.le
    rw [Nat.add_sub_cancel' hvk] at hfac
    omega

-- ================ SKELETON ================

/-- The "new" sum (over k not divisible by p) is divisible by p^(3r+3). -/
lemma key_Snew (p r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hr : 2 ≤ r) :
    (p : ℤ) ^ (3 * r + 3) ∣
      ∑ k ∈ (Finset.range (p ^ r)).filter (fun k => ¬ p ∣ k), term (p ^ r) k := by
  sorry

/-- The "matching" sum is divisible by p^(3r+3). -/
lemma key_match (p r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hr : 2 ≤ r) :
    (p : ℤ) ^ (3 * r + 3) ∣
      ∑ m ∈ Finset.range (p ^ (r - 1)), (term (p ^ r) (p * m) - term (p ^ (r - 1)) m) := by
  sorry

theorem main_div (p r : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (hr : 2 ≤ r) :
    (p : ℤ) ^ (3 * r + 3) ∣ ((A212334 (p ^ r) : ℤ) - A212334 (p ^ (r - 1))) := by
  have hppos : 0 < p := hp.pos
  have hr1 : 1 ≤ r := by omega
  have hpr : 0 < p ^ r := Nat.pow_pos hppos
  have hpr1 : 0 < p ^ (r - 1) := Nat.pow_pos hppos
  rw [A212334_pos _ hpr, A212334_pos _ hpr1]
  -- reindex p | k part
  have hpre : p ^ r = p * p ^ (r - 1) := by
    rw [← _root_.pow_succ']; congr 1; omega
  -- the p|k part is reindexed by m ↦ p*m
  have himg : (Finset.range (p ^ r)).filter (fun k => p ∣ k)
      = (Finset.range (p ^ (r - 1))).image (fun m => p * m) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, c, rfl⟩
      exact ⟨c, by rw [hpre] at hk; exact lt_of_mul_lt_mul_left hk (Nat.zero_le _), rfl⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨?_, dvd_mul_right p m⟩
      rw [hpre]; exact (Nat.mul_lt_mul_left hppos).mpr hm
  have hpm_sum : ∑ k ∈ (Finset.range (p ^ r)).filter (fun k => p ∣ k), term (p ^ r) k
      = ∑ m ∈ Finset.range (p ^ (r - 1)), term (p ^ r) (p * m) := by
    rw [himg, Finset.sum_image]
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hppos hab
  have hkey : ∑ k ∈ Finset.range (p ^ r), term (p ^ r) k
      = (∑ k ∈ (Finset.range (p ^ r)).filter (fun k => ¬ p ∣ k), term (p ^ r) k)
        + ∑ m ∈ Finset.range (p ^ (r - 1)), term (p ^ r) (p * m) := by
    rw [← hpm_sum, add_comm]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.range (p ^ r)) (fun k => p ∣ k) _).symm
  have hsplit :
      (∑ k ∈ Finset.range (p ^ r), term (p ^ r) k)
        - (∑ m ∈ Finset.range (p ^ (r - 1)), term (p ^ (r - 1)) m)
      = (∑ k ∈ (Finset.range (p ^ r)).filter (fun k => ¬ p ∣ k), term (p ^ r) k)
        + (∑ m ∈ Finset.range (p ^ (r - 1)),
            (term (p ^ r) (p * m) - term (p ^ (r - 1)) m)) := by
    rw [hkey, Finset.sum_sub_distrib]; ring
  rw [hsplit]
  exact dvd_add (key_Snew p r hp h5 hr) (key_match p r hp h5 hr)

theorem oeis_212334_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (h_ge5 : 5 ≤ p) (h_ge2 : 2 ≤ r) :
    A212334 (p ^ r) % (p ^ (3 * r + 3)) = A212334 (p ^ (r - 1)) % (p ^ (3 * r + 3)) := by
  have h := main_div p r hp h_ge5 h_ge2
  have : A212334 (p ^ r) ≡ A212334 (p ^ (r - 1)) [MOD p ^ (3 * r + 3)] := by
    rw [Nat.modEq_iff_dvd]
    push_cast
    rw [show ((A212334 (p ^ (r - 1)) : ℤ) - A212334 (p ^ r))
        = -((A212334 (p ^ r) : ℤ) - A212334 (p ^ (r - 1))) by ring]
    exact (dvd_neg).mpr h
  exact this
