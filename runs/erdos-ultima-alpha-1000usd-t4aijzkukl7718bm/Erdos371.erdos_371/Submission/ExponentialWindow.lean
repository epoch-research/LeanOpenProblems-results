import FormalConjecturesUtil

/-! A finite linear combination of exponential weights approximates a sharp
prefix uniformly on bounded sequences. This is an analytic Tauberian tool;
no prime-factor cancellation hypothesis is proved here. -/
namespace Erdos371.ExponentialWindow
open Finset Filter
open scoped Topology

noncomputable def window (k : ℕ) (r : ℝ) (n : ℕ) : ℝ := 1-(1-r^n)^k

lemma window_nonneg (k n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ window k r n := by
  have h0 : 0 ≤ r^n := pow_nonneg hr _
  have h1 : r^n ≤ 1 := pow_le_one₀ hr hr1
  exact sub_nonneg.mpr (pow_le_one₀ (by linarith) (by linarith))

lemma window_geom (k : ℕ) (r : ℝ) (n : ℕ) :
    window k r n = (∑ j ∈ range k, (1-r^n)^j) * r^n := by
  have he := geom_sum_mul_neg (1-r^n) k
  simpa only [sub_sub_cancel] using he.symm

lemma window_le_geometric (k n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    window k r n ≤ k*r^n := by
  have h0 : 0 ≤ r^n := pow_nonneg hr _
  have h1 : r^n ≤ 1 := pow_le_one₀ hr hr1
  rw [window_geom]
  apply mul_le_mul_of_nonneg_right _ h0
  calc
    _ ≤ ∑ _j ∈ range k, (1 : ℝ) :=
      sum_le_sum (fun j _ => pow_le_one₀ (by linarith) (by linarith))
    _ = _ := by simp

lemma power_deficit_bound (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (k*x)*(1-x)^k ≤ 1 := by
  have he : (∑ j ∈ range k, (1-x)^j)*x = 1-(1-x)^k := by
    simpa only [sub_sub_cancel] using geom_sum_mul_neg (1-x) k
  have hs : (k : ℝ)*(1-x)^k ≤ ∑ j ∈ range k, (1-x)^j := by
    calc
      _ = ∑ _j ∈ range k, (1-x)^k := by simp
      _ ≤ _ := sum_le_sum (fun j hj =>
        pow_le_pow_of_le_one (by linarith) (by linarith) (mem_range.mp hj).le)
  have hh := mul_le_mul_of_nonneg_right hs hx
  rw [he] at hh
  nlinarith [pow_nonneg (sub_nonneg.mpr hx1) k]

lemma window_deficit_bound (k N n : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hkr : (k : ℝ)*r^N = 1) (hn : n ≤ N) :
    1-window k r n ≤ r^(N-n) := by
  have h := power_deficit_bound k (pow_nonneg hr n) (pow_le_one₀ hr hr1)
  have hh := mul_le_mul_of_nonneg_right h (pow_nonneg hr (N-n))
  have he : ((k : ℝ)*r^n)*(1-r^n)^k*r^(N-n) = (1-r^n)^k := by
    calc
      _ = ((k : ℝ)*(r^n*r^(N-n)))*(1-r^n)^k := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hn, hkr, one_mul]
  rw [he, one_mul] at hh
  simpa only [window, sub_sub_cancel] using hh

lemma sum_reverse_powers (N : ℕ) (r : ℝ) :
    (∑ n ∈ range N, r^(N-n)) = r * ∑ n ∈ range N, r^n := by
  have h := sum_range_reflect (fun n => r^(n+1)) N
  have he : (∑ n ∈ range N, r^(N-1-n+1)) = ∑ n ∈ range N, r^(N-n) := by
    apply sum_congr rfl
    intro n hn
    congr 1
    have := mem_range.mp hn
    omega
  rw [he] at h
  rw [h, mul_sum]
  apply sum_congr rfl
  intro n _
  rw [pow_succ, mul_comm]

lemma sum_window_deficit_le (k N : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hkr : (k : ℝ)*r^N = 1) :
    (∑ n ∈ range N, (1-window k r n)) ≤ r/(1-r) := by
  calc
    _ ≤ ∑ n ∈ range N, r^(N-n) := sum_le_sum (fun n hn =>
      window_deficit_bound k N n hr hr1.le hkr (mem_range.mp hn).le)
    _ = r*∑ n ∈ range N, r^n := sum_reverse_powers N r
    _ ≤ r*∑' n : ℕ, r^n := mul_le_mul_of_nonneg_left
      ((summable_geometric_of_lt_one hr hr1).sum_le_tsum (range N)
        (fun n _ => pow_nonneg hr n)) hr
    _ = _ := by rw [tsum_geometric_of_lt_one hr hr1, div_eq_mul_inv]

lemma summable_weighted_window (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => f n * window k r n) := by
  apply Summable.of_norm_bounded ((summable_geometric_of_lt_one hr hr1).mul_left (k : ℝ))
  intro n
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (window_nonneg k n hr hr1.le)]
  exact (mul_le_of_le_one_left (window_nonneg k n hr hr1.le) (hf n)).trans
    (window_le_geometric k n hr hr1.le)

/-- The total prefix-versus-window error is at most (1+r)/(1-r),
provided k*r^N=1. The sequence is arbitrary apart from boundedness. -/
theorem prefix_window_error (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (k N : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hkr : (k : ℝ)*r^N = 1) :
    |(∑ n ∈ range N, f n) - ∑' n : ℕ, f n * window k r n| ≤ (1+r)/(1-r) := by
  have hs := summable_weighted_window f hf k hr hr1
  rw [← hs.sum_add_tsum_nat_add N]
  have he : (∑ n ∈ range N, f n) -
      ((∑ n ∈ range N, f n*window k r n) + ∑' n, f (n+N)*window k r (n+N)) =
      (∑ n ∈ range N, f n*(1-window k r n)) -
        ∑' n, f (n+N)*window k r (n+N) := by
    simp only [mul_sub, mul_one, sum_sub_distrib]
    ring
  rw [he]
  have hi : |∑ n ∈ range N, f n*(1-window k r n)| ≤ r/(1-r) := by
    calc
      _ ≤ ∑ n ∈ range N, |f n*(1-window k r n)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ range N, (1-window k r n) := by
        apply sum_le_sum
        intro n hn
        have h0 : 0 ≤ 1-window k r n := by
          simp only [window, sub_sub_cancel]
          exact pow_nonneg (sub_nonneg.mpr (pow_le_one₀ hr hr1.le)) _
        rw [abs_mul, abs_of_nonneg h0]
        exact mul_le_of_le_one_left h0 (hf n)
      _ ≤ _ := sum_window_deficit_le k N hr hr1 hkr
  have ht : |∑' n, f (n+N)*window k r (n+N)| ≤ 1/(1-r) := by
    have hgs : Summable (fun n : ℕ => (k : ℝ)*r^(n+N)) :=
      (summable_nat_add_iff N).mpr ((summable_geometric_of_lt_one hr hr1).mul_left (k : ℝ))
    have hb (n : ℕ) : ‖f (n+N)*window k r (n+N)‖ ≤ (k : ℝ)*r^(n+N) := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (window_nonneg k (n+N) hr hr1.le)]
      exact (mul_le_of_le_one_left (window_nonneg k (n+N) hr hr1.le) (hf _)).trans
        (window_le_geometric k (n+N) hr hr1.le)
    calc
      _ ≤ ∑' n : ℕ, (k : ℝ)*r^(n+N) := by
        rw [← Real.norm_eq_abs]
        exact tsum_of_norm_bounded hgs.hasSum hb
      _ = 1/(1-r) := by
        simp only [pow_add, show ∀ n : ℕ, (k : ℝ)*(r^n*r^N) = ((k : ℝ)*r^N)*r^n
          from fun n => by ring, hkr, one_mul]
        rw [tsum_geometric_of_lt_one hr hr1, one_div]
  calc
    _ ≤ |∑ n ∈ range N, f n*(1-window k r n)| +
        |∑' n, f (n+N)*window k r (n+N)| := abs_sub _ _
    _ ≤ r/(1-r)+1/(1-r) := add_le_add hi ht
    _ = _ := by ring

#print axioms prefix_window_error
end Erdos371.ExponentialWindow
