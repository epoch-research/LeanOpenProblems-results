import Submission.ArithmeticReduction

/-! A finite second-moment tail potential using Chebyshev's theta bound. -/
namespace Erdos7ChebyshevTail
open scoped BigOperators
open Erdos7No23Sieve
set_option maxHeartbeats 4000000

noncomputable def potential (x t : ℝ) : ℝ :=
  (9/25 : ℝ) / x * (1 + (1-t/((7/5)*x)) + (1-t/((7/5)*x))^2/2)

lemma potential_nonneg {x t : ℝ} (hx : 0 < x) (ht : t ≤ (7/5)*x) :
    0 ≤ potential x t := by
  have hr : 0 ≤ 1-t/((7/5)*x) := by
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity)).mpr ht
  unfold potential
  positivity

lemma potential_antitone_theta {x s t : ℝ} (hx : 0 < x)
    (hst : s ≤ t) (ht : t ≤ (7/5)*x) :
    potential x t ≤ potential x s := by
  have hden : 0 < (7/5 : ℝ)*x := by positivity
  have ht1 : t/((7/5)*x) ≤ 1 := (div_le_one hden).mpr ht
  have hst1 : s/((7/5)*x) ≤ t/((7/5)*x) := div_le_div_of_nonneg_right hst hden.le
  unfold potential
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [sq_nonneg (t/((7/5)*x)-s/((7/5)*x))]

lemma potential_antitone_x {x y t : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (ht0 : 0 ≤ t) (ht : t ≤ (7/5)*x) :
    potential y t ≤ potential x t := by
  have hy : 0 < y := hx.trans_le hxy
  let d := y-x
  let e := (7/5)*x-t
  have hd : 0 ≤ d := sub_nonneg.mpr hxy
  have he : 0 ≤ e := sub_nonneg.mpr ht
  have hid : potential x t - potential y t =
      (9/25 : ℝ)*(y-x)/(2*(7/5)^2*x^3*y^3) *
      ((7/5)^2*x^2*d*(x+2*d) + 2*(7/5)*x*e*(x^2+3*x*d+d^2) +
        e^2*(3*x^2+3*x*d+d^2)) := by
    dsimp [potential, d, e]
    field_simp
    <;> ring
  have hz : 0 ≤ potential x t - potential y t := by
    rw [hid]
    positivity
  linarith

lemma local_potential_drop {x t l : ℝ} (hx : 0 < x)
    (ht0 : 0 ≤ t) (ht : t ≤ (7/5)*x) (hl : 23/2 ≤ l) :
    (157/100 : ℝ)/x^2 + (1 + (377/100 : ℝ)/x)*potential x t ≤
      potential x (t-l) := by
  let r := 1-t/((7/5)*x)
  let d := l/((7/5)*x)
  have hden : 0 < (7/5 : ℝ)*x := by positivity
  have hr0 : 0 ≤ r := by dsimp [r]; exact sub_nonneg.mpr ((div_le_one hden).mpr ht)
  have hr1 : r ≤ 1 := by dsimp [r]; have := div_nonneg ht0 hden.le; linarith
  have hd : 0 ≤ d := by dsimp [d]; apply div_nonneg (by linarith) hden.le
  have hpoly : (157/100 : ℝ) + (9/25)*(377/100)*(1+r+r^2/2) ≤
      (9/25)*(l/(7/5))*(1+r) := by
    have hrr : r^2 ≤ r := by nlinarith
    have hh := mul_nonneg (show 0 ≤ l-23/2 by linarith) (show 0 ≤ 1+r by linarith)
    nlinarith
  have hid : (potential x (t-l) - (1+(377/100)/x)*potential x t)*x^2 =
      (9/25)*(l/(7/5))*(1+r) + (9/25)*x*d^2/2 -
      (9/25)*(377/100)*(1+r+r^2/2) := by
    dsimp [potential, r, d]
    field_simp
    <;> ring
  have hdrop : (157/100 : ℝ) ≤
      (potential x (t-l) - (1+(377/100)/x)*potential x t)*x^2 := by
    rw [hid]
    nlinarith [mul_nonneg hx.le (sq_nonneg d)]
  have hdiv := (div_le_iff₀ (sq_pos_of_pos hx)).mpr hdrop
  linarith

lemma multiplier_bound {p : ℕ} (hp : 1000 ≤ p) :
    (multiplier p : ℝ) ≤ 1 + (377/100 : ℝ)/p := by
  have hpR : (1000 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (0 : ℝ) < p := by linarith
  have h1 : (0 : ℝ) < p-1 := by linarith
  unfold multiplier
  push_cast
  apply (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < 100*p*(p-1)^2)).mp
  field_simp
  nlinarith [sq_nonneg ((p : ℝ)-1000)]

lemma charge_bound {p : ℕ} (hp : 1000 ≤ p) :
    (charge p : ℝ) ≤ (157/100 : ℝ)/(p : ℝ)^2 := by
  have hpR : (1000 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (0 : ℝ) < p := by linarith
  have h1 : (0 : ℝ) < p-1 := by linarith
  unfold charge
  push_cast
  apply (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < 400*p^2*(p-1)^2)).mp
  field_simp
  nlinarith [sq_nonneg ((p : ℝ)-1000)]

lemma theta_upper (x : ℝ) (hx : 0 ≤ x) : Chebyshev.theta x ≤ (7/5)*x := by
  have hl : Real.log 4 ≤ (7/5 : ℝ) := by
    have he : Real.log (4 : ℝ) = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num
    rw [he]
    linarith [Real.log_two_lt_d9]
  exact (Chebyshev.theta_le_log4_mul_x hx).trans (mul_le_mul_of_nonneg_right hl hx)

lemma log_large {p : ℕ} (hp : 100000 ≤ p) : (23/2 : ℝ) ≤ Real.log p := by
  have h0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have he : Real.exp (23 : ℝ) < (100000 : ℝ)^2 := by
    calc
      Real.exp (23 : ℝ) = (Real.exp 1)^23 := by rw [← Real.exp_nat_mul]; norm_num
      _ < (2719/1000 : ℝ)^23 := by gcongr; linarith [Real.exp_one_lt_d9]
      _ < (100000 : ℝ)^2 := by norm_num
  have hlog := Real.log_lt_log (Real.exp_pos _) he
  rw [Real.log_exp, Real.log_pow] at hlog
  have hpR : (100000 : ℝ) ≤ p := by exact_mod_cast hp
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 100000) hpR
  norm_num at hlog
  linarith

lemma theta_prime_step {p : ℕ} (hp : p.Prime) :
    Chebyshev.theta (p : ℝ) = Chebyshev.theta ((p-1 : ℕ) : ℝ) + Real.log p := by
  classical
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  have he : Finset.Icc 0 p = insert p (Finset.Icc 0 (p-1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [he, Finset.filter_insert]
  simp only [hp, if_true]
  rw [Finset.sum_insert]
  · ring
  · simp only [Finset.mem_filter, Finset.mem_Icc]
    have := hp.two_le
    omega

lemma prime_potential_drop {p : ℕ} (hp : p.Prime) (hpN : 100000 ≤ p) :
    (charge p : ℝ) + (multiplier p : ℝ)*
      potential (p : ℝ) (Chebyshev.theta p) ≤
      potential (p : ℝ) (Chebyshev.theta ((p-1 : ℕ) : ℝ)) := by
  have h0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ht := theta_upper (p : ℝ) h0.le
  have hbefore : Chebyshev.theta ((p-1 : ℕ) : ℝ) = Chebyshev.theta p - Real.log p := by
    linarith [theta_prime_step hp]
  rw [hbefore]
  exact (add_le_add (charge_bound (by omega))
    (mul_le_mul_of_nonneg_right (multiplier_bound (by omega))
      (potential_nonneg h0 ht))).trans
    (local_potential_drop h0 (Chebyshev.theta_nonneg _) ht (log_large hpN))

lemma potential_before_mono {n p : ℕ} (hn : 0 < n) (hnp : n ≤ p) :
    potential (p : ℝ) (Chebyshev.theta ((p-1 : ℕ) : ℝ)) ≤
      potential (n : ℝ) (Chebyshev.theta ((n-1 : ℕ) : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (n : ℝ) ≤ p := by exact_mod_cast hnp
  have ht : Chebyshev.theta ((p-1 : ℕ) : ℝ) ≤ (7/5)*(p : ℝ) := by
    apply (theta_upper _ (Nat.cast_nonneg _)).trans
    gcongr
    exact_mod_cast Nat.sub_le p 1
  have htheta : Chebyshev.theta ((n-1 : ℕ) : ℝ) ≤
      Chebyshev.theta ((p-1 : ℕ) : ℝ) :=
    Chebyshev.theta_mono (by exact_mod_cast Nat.sub_le_sub_right hnp 1)
  apply (potential_antitone_theta (hnR.trans_le hpR) htheta ht).trans
  apply potential_antitone_x hnR hpR (Chebyshev.theta_nonneg _)
  apply (theta_upper _ (Nat.cast_nonneg _)).trans
  gcongr
  exact_mod_cast Nat.sub_le n 1

/-- Uniform tail bound retaining the actual initial theta value. -/
theorem tail_cost_potential (S : Finset ℕ) (n : ℕ) (hn : 100000 ≤ n)
    (hS : ∀ p ∈ S, p.Prime ∧ n ≤ p) :
    (budgetCost S : ℝ) ≤ potential (n : ℝ) (Chebyshev.theta ((n-1 : ℕ) : ℝ)) := by
  classical
  induction S using Finset.strongInductionOn generalizing n with
  | _ S ih =>
    by_cases hne : S.Nonempty
    · let p := S.min' hne
      have hpS : p ∈ S := Finset.min'_mem _ _
      have hp : p.Prime := (hS p hpS).1
      have hpN : 100000 ≤ p := hn.trans (hS p hpS).2
      let T := S.erase p
      have hTS : T ⊂ S := Finset.erase_ssubset hpS
      have hT (q : ℕ) (hq : q ∈ T) : q.Prime ∧ p+1 ≤ q := by
        have hh := Finset.mem_erase.mp hq
        have hmin : p ≤ q := Finset.min'_le _ _ hh.2
        exact ⟨(hS q hh.2).1, by omega⟩
      have htail := ih T hTS (p+1) (by omega) hT
      have hPU : S = {p} ∪ T := by simp [T, Finset.insert_erase hpS]
      have horder : ∀ a ∈ ({p} : Finset ℕ), ∀ b ∈ T, a < b := by
        intro a ha b hb
        rw [Finset.mem_singleton.mp ha]
        exact (hT b hb).2
      rw [hPU, budgetCost_union horder, budgetCost_singleton, budgetProduct_singleton]
      push_cast
      have hm0 : (0 : ℝ) ≤ (multiplier p : ℝ) := by
        exact_mod_cast multiplier_nonneg p (by omega)
      have hstep : potential ((p+1 : ℕ) : ℝ) (Chebyshev.theta p) ≤
          potential (p : ℝ) (Chebyshev.theta p) := by
        apply potential_antitone_x (by exact_mod_cast hp.pos)
          (by norm_cast; omega) (Chebyshev.theta_nonneg _) (theta_upper _ (Nat.cast_nonneg _))
      simp only [Nat.add_sub_cancel] at htail
      apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left (htail.trans hstep) hm0)).trans
      exact (prime_potential_drop hp hpN).trans
        (potential_before_mono (by omega) (hS p hpS).2)
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he, budgetCost_empty]
      norm_num only [Rat.cast_zero]
      apply potential_nonneg (by exact_mod_cast (show 0 < n by omega))
      apply (theta_upper _ (Nat.cast_nonneg _)).trans
      gcongr
      exact_mod_cast Nat.sub_le n 1

#print axioms tail_cost_potential
end Erdos7ChebyshevTail
