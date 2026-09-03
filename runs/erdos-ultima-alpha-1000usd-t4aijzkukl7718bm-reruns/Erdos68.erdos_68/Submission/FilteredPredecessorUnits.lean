import Submission.FilteredPeriodicUnits

/-!
Sharper periodic units for binomial filters of degree at least two.
These auxiliary statements do not settle Erdős Problem 68.
-/

namespace FilteredPredecessorUnits

open Erdos68Development BinomialFilteredLambert FilteredPeriodicUnits
  FilteredWindowGcd

lemma choose_dvd_pow_mul_add_one (p r t k : ℕ) (hp : p.Prime)
    (hk : 2 ≤ k) (hkr : k < p^r) : p ∣ (p^r*t+1).choose k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Nat.choose_succ_succ]
  exact Nat.dvd_add
    (choose_dvd_of_pow_mul p r t j hp (by omega) (by omega))
    (choose_dvd_of_pow_mul p r t (j+1) hp (by omega) hkr)

/-- A residue-one index modulo a sufficiently large prime power suffices.
The restriction to degrees at least two is essential here. -/
theorem filtered_at_pow_pred (ks : List ℕ) (p r t : ℕ) (hp : p.Prime)
    (ht : 0 < t) (hks : ∀ k ∈ ks, 2 ≤ k ∧ k < p^(r+1)) :
    Int.ModEq p (filtered ks (p^(r+1)*t+1)) 1 := by
  have hp0 := hp.pos
  have hn : 2 ≤ p^(r+1)*t+1 := by
    have : 0 < p^(r+1)*t := by positivity
    omega
  have hd : p ∣ p^(r+1)*t+1-1 := by
    simp only [Nat.add_sub_cancel]
    exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) t
  apply (filterSteps_modEq ks p (p^(r+1)*t+1)
    (fun n => (lambertCoeff n : ℤ))
    (fun k hk => choose_dvd_pow_mul_add_one p (r+1) t k hp
      (hks k hk).1 (hks k hk).2)).trans
  exact Int.natCast_modEq_iff.mpr ((lambertCoeff_modEq_pred hn).of_dvd hd)

/-- The low digits of the lower binomial index agree with the top index,
and all higher lower digits are zero. -/
lemma choose_pow_mul_add_modEq_one (p r t s : ℕ) (hp : p.Prime)
    (hs : s < p^r) : Nat.ModEq p ((p^r*t+s).choose s) 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  induction r generalizing s with
  | zero =>
    have : s=0 := by simpa using hs
    subst s
    simp only [Nat.choose_zero_right]
    rfl
  | succ r ih =>
    have he : p^(r+1)*t+s = p*(p^r*t)+s := by rw [pow_succ']; ring
    rw [he]
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := p) (n := p*(p^r*t)+s) (k := s)
    have hdiv : s/p < p^r := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
      simpa only [pow_succ] using hs
    simpa [Nat.mul_add_div hp.pos] using hl.trans (by
      simpa [Nat.mul_add_div hp.pos] using ih (s/p) hdiv)

lemma factorial_valuation_pow_block (p r t s : ℕ) (hp : p.Prime)
    (hs : s < p^r) :
    (p^r*t+s).factorial.factorization p =
      (p^r*t).factorial.factorization p+s.factorial.factorization p := by
  have hunit := choose_pow_mul_add_modEq_one p r t s hp hs
  have hnot : ¬p ∣ (p^r*t+s).choose s := by
    intro hd
    have hzero := Nat.modEq_zero_iff_dvd.mpr hd
    exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp (hunit.symm.trans hzero))
  have hc0 : (p^r*t+s).choose s ≠ 0 := by
    intro hz
    exact hnot (hz ▸ dvd_zero p)
  have he := Nat.add_choose_mul_factorial_mul_factorial (p^r*t) s
  have hv := congrArg (fun n : ℕ => n.factorization p) he
  dsimp only at hv
  simp only [Nat.factorization_mul (mul_ne_zero hc0 (Nat.factorial_ne_zero (p^r*t)))
      (Nat.factorial_ne_zero s),
    Nat.factorization_mul hc0 (Nat.factorial_ne_zero (p^r*t)), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnot, zero_add] at hv
  omega

lemma factorial_quotient_valuation_eq (p r t s : ℕ) (hp : p.Prime)
    (hs : s < p^(r+1)) :
    ((p^(r+1)*t+s+1).factorial/(p^(r+1)*t+1).factorial).factorization p =
      (p^(r+1)*t+s+1).factorization p+s.factorial.factorization p := by
  let u := p^(r+1)*t+1
  let N := p^(r+1)*t+s+1
  have huN : u ≤ N := by dsimp [u, N]; omega
  have hu0 : 0 < u := by dsimp [u]; omega
  have hN0 : 0 < N := hu0.trans_le huN
  have hpdiv : p ∣ p^(r+1)*t :=
    dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) t
  have hnot : ¬p ∣ u := by
    intro h
    have h1 : p ∣ 1 := by
      simpa only [u, Nat.add_sub_cancel_left] using Nat.dvd_sub h hpdiv
    exact hp.not_dvd_one h1
  have hunit : u.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnot
  have huval : u.factorial.factorization p = (p^(r+1)*t).factorial.factorization p := by
    dsimp only [u]
    rw [Nat.factorial_succ, Nat.factorization_mul hu0.ne'
      (Nat.factorial_ne_zero _), Finsupp.add_apply, hunit, zero_add]
  have hNval : N.factorial.factorization p =
      N.factorization p+(p^(r+1)*t).factorial.factorization p+
        s.factorial.factorization p := by
    change (p^(r+1)*t+s+1).factorial.factorization p =
      (p^(r+1)*t+s+1).factorization p+
        (p^(r+1)*t).factorial.factorization p+s.factorial.factorization p
    rw [Nat.factorial_succ, Nat.factorization_mul hN0.ne'
      (Nat.factorial_ne_zero _), Finsupp.add_apply,
      factorial_valuation_pow_block p (r+1) t s hp hs]
    dsimp only [N]
    omega
  have hq0 := (factorial_quotient_pos u N huN).ne'
  have he := Nat.div_mul_cancel (Nat.factorial_dvd_factorial huN)
  have hv := congrArg (fun n : ℕ => n.factorization p) he
  dsimp only at hv
  rw [Nat.factorization_mul hq0 (Nat.factorial_ne_zero u), Finsupp.add_apply,
    huval, hNval] at hv
  change (N.factorial/u.factorial).factorization p = N.factorization p+
    s.factorial.factorization p
  omega

lemma exists_aligned_unit_index (p r H N : ℕ) (hp : p.Prime)
    (hH : 2 ≤ H) (hwide : H+p^(r+1) ≤ N) :
    ∃ t s, 0 < t ∧ s < p^(r+1) ∧ N=p^(r+1)*t+s+1 ∧ H ≤ p^(r+1)*t+1 := by
  have hp0 := hp.pos
  let B := p^(r+1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hBN : B ≤ N-1 := by change H+B ≤ N at hwide; omega
  let t := (N-1)/B
  let s := (N-1)%B
  have ht : 0 < t := Nat.div_pos hBN hB
  have hs : s < B := Nat.mod_lt _ hB
  have he := Nat.mod_add_div (N-1) B
  change s+B*t=N-1 at he
  change H+B ≤ N at hwide
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · change N=B*t+s+1
    omega
  · change H ≤ B*t+1
    omega

/-- The p-part beyond the current index is bounded independently of the
window endpoint. The bound applies to the actual filtered coefficients. -/
theorem filtered_window_valuation_bound (ks : List ℕ) (p r H N : ℕ)
    (hp : p.Prime) (hH : 2 ≤ H) (hwide : H+p^(r+1) ≤ N)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k < p^(r+1)) :
    (windowGcd (filtered ks) H N).factorization p ≤
      N.factorization p+(p^(r+1)-1).factorial.factorization p := by
  obtain ⟨t, s, ht, hs, he, hHu⟩ := exists_aligned_unit_index p r H N hp hH hwide
  have huN : p^(r+1)*t+1 ≤ N := by omega
  have hu : p^(r+1)*t+1 ∈ Finset.Icc H N := Finset.mem_Icc.mpr ⟨hHu, huN⟩
  have hunit := filtered_at_pow_pred ks p r t hp ht hks
  have hv := window_valuation_le_quotient (filtered ks) p H N (p^(r+1)*t+1) hp hu hunit
  have hfac : s.factorial.factorization p ≤ (p^(r+1)-1).factorial.factorization p :=
    ((Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero s)
      (Nat.factorial_ne_zero _)).mpr (Nat.factorial_dvd_factorial (by omega))) p
  calc
    (windowGcd (filtered ks) H N).factorization p ≤
        (N.factorial/(p^(r+1)*t+1).factorial).factorization p := hv
    _ = N.factorization p+s.factorial.factorization p := by
      rw [he, factorial_quotient_valuation_eq p r t s hp hs]
    _ ≤ _ := Nat.add_le_add_left hfac _

/-- A convenient coarser version, using Legendre's factorial bound. -/
theorem filtered_window_valuation_bound_div (ks : List ℕ) (p r H N : ℕ)
    (hp : p.Prime) (hH : 2 ≤ H) (hwide : H+p^(r+1) ≤ N)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k < p^(r+1)) :
    (windowGcd (filtered ks) H N).factorization p ≤
      N.factorization p+(p^(r+1)-1)/(p-1) := by
  exact (filtered_window_valuation_bound ks p r H N hp hH hwide hks).trans
    (Nat.add_le_add_left (Nat.factorization_factorial_le_div_pred hp _) _)

end FilteredPredecessorUnits

#print axioms FilteredPredecessorUnits.filtered_at_pow_pred
#print axioms FilteredPredecessorUnits.factorial_quotient_valuation_eq
#print axioms FilteredPredecessorUnits.filtered_window_valuation_bound
#print axioms FilteredPredecessorUnits.filtered_window_valuation_bound_div
