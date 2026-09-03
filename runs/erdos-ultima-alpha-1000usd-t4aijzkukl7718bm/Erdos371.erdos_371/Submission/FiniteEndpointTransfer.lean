import Submission.CyclicCorrelationTransfer

/-! Finite endpoint and cyclic-boundary estimates. Dilation is recorded with
its actual shorter endpoint `N/q`, not replaced by an unjustified endpoint `N`. -/
namespace Erdos371.FiniteInformation
open Finset

noncomputable def prefixMean (N : ℕ) (F : ℕ → ℝ) : ℝ := (∑ n ∈ range N, F n) / N

lemma prefixMean_congr (N : ℕ) (F G : ℕ → ℝ) (h : ∀ n < N, F n = G n) :
    prefixMean N F = prefixMean N G := by
  unfold prefixMean
  congr 1
  exact sum_congr rfl (fun n hn => h n (mem_range.mp hn))

lemma prefixMean_sub (N : ℕ) (F G : ℕ → ℝ) :
    prefixMean N (fun n => F n-G n) = prefixMean N F-prefixMean N G := by
  simp only [prefixMean, sum_sub_distrib, sub_div]

lemma abs_sum_range_le (N : ℕ) (F : ℕ → ℝ) (B : ℝ) (hF : ∀ n < N, |F n| ≤ B) :
    |∑ n ∈ range N, F n| ≤ B*N := by
  calc
    _ ≤ ∑ n ∈ range N, |F n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ range N, B := sum_le_sum (fun n hn => hF n (mem_range.mp hn))
    _ = _ := by simp [mul_comm]

lemma abs_prefixMean_le (N : ℕ) (hN : 0 < N) (F : ℕ → ℝ) (B : ℝ)
    (hF : ∀ n < N, |F n| ≤ B) : |prefixMean N F| ≤ B := by
  unfold prefixMean
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  exact (div_le_iff₀ (by exact_mod_cast hN)).mpr (abs_sum_range_le N F B hF)

/-- A change of endpoint costs only the relative length of the discarded tail. -/
lemma prefixMean_endpoint_bound (M N : ℕ) (hM : 0 < M) (hMN : M ≤ N)
    (F : ℕ → ℝ) (B : ℝ) (hF : ∀ n < N, |F n| ≤ B) :
    |prefixMean N F-prefixMean M F| ≤ 2*B*(N-M : ℕ)/N := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le hM hMN
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hsum : (∑ n ∈ range N, F n) =
      (∑ n ∈ range M, F n) + ∑ j ∈ range (N-M), F (M+j) := by
    simpa only [Nat.add_sub_of_le hMN] using sum_range_add F M (N-M)
  have he : prefixMean N F-prefixMean M F =
      ((∑ j ∈ range (N-M), F (M+j)) - (N-M : ℕ)*prefixMean M F)/N := by
    unfold prefixMean
    rw [hsum, Nat.cast_sub hMN]
    field_simp
    ring
  have htail := abs_sum_range_le (N-M) (fun j => F (M+j)) B
    (fun j hj => hF (M+j) (by omega))
  have hinit := abs_prefixMean_le M hM F B (fun n hn => hF n (lt_of_lt_of_le hn hMN))
  rw [he, abs_div, abs_of_pos hN]
  apply div_le_div_of_nonneg_right _ hN.le
  have habs := abs_sub (∑ j ∈ range (N-M), F (M+j)) ((N-M : ℕ)*prefixMean M F)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (N-M) : (0 : ℝ) ≤ (N-M : ℕ))] at habs
  have hm := mul_le_mul_of_nonneg_left hinit (Nat.cast_nonneg (α := ℝ) (N-M))
  nlinarith

/-- If two bounded arrays agree off a tail of length `q`, their means differ
by at most `2 B q/N`. -/
lemma prefixMean_tail_bound (N q : ℕ) (hq : q ≤ N)
    (F G : ℕ → ℝ) (B : ℝ) (hF : ∀ n < N, |F n| ≤ B)
    (hG : ∀ n < N, |G n| ≤ B) (he : ∀ n < N-q, F n = G n) :
    |prefixMean N F-prefixMean N G| ≤ 2*B*q/N := by
  have hsum : (∑ n ∈ range N, (F n-G n)) =
      ∑ j ∈ range q, (F (N-q+j)-G (N-q+j)) := by
    have h := sum_range_add (fun n => F n-G n) (N-q) q
    rw [Nat.sub_add_cancel hq] at h
    have hz : ∑ n ∈ range (N-q), (F n-G n) = 0 :=
      sum_eq_zero fun n hn => by rw [he n (mem_range.mp hn), sub_self]
    simpa only [hz, zero_add] using h
  rw [← prefixMean_sub, prefixMean, hsum, abs_div, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have hbound := abs_sum_range_le q (fun j => F (N-q+j)-G (N-q+j)) (2*B)
    (fun j hj => by
      have hn : N-q+j < N := by omega
      have h := abs_sub (F (N-q+j)) (G (N-q+j))
      linarith [hF _ hn, hG _ hn])
  exact hbound

lemma sum_uniform_zmod_range (N : ℕ) [NeZero N] (V : ZMod N → ℝ) :
    (∑ x, V x) = ∑ n ∈ range N, V (n : ZMod N) := by
  classical
  apply sum_nbij' ZMod.val (fun n => (n : ZMod N))
  · intro x _
    exact mem_range.mpr x.val_lt
  · intro n _
    exact mem_univ _
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro n hn
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hn)]
  · intro x _
    rw [ZMod.natCast_zmod_val]

lemma mean_uniform_zmod_prefix (N : ℕ) [NeZero N] (V : ZMod N → ℝ) :
    mean (uniformLaw (ZMod N)) V = prefixMean N (fun n => V (n : ZMod N)) := by
  unfold mean prefixMean
  simp only [uniformLaw, ZMod.card, mul_comm (N : ℝ)⁻¹, ← div_eq_mul_inv, ← sum_div]
  rw [sum_uniform_zmod_range]

lemma sum_divisible_range (q T : ℕ) (hq : 0 < q) (F : ℕ → ℝ) :
    (∑ n ∈ range (q*T), if q ∣ n then F n else 0) = ∑ m ∈ range T, F (q*m) := by
  classical
  rw [← sum_filter]
  symm
  apply sum_nbij' (fun m => q*m) (fun n => n/q)
  · intro m hm
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mul_lt_mul_of_pos_left (mem_range.mp hm) hq),
      dvd_mul_right _ _⟩
  · intro n hn
    have hn' := mem_range.mp (mem_filter.mp hn).1
    apply mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul hq).mpr (by simpa [mul_comm] using hn')
  · intro m _
    exact Nat.mul_div_right m hq
  · intro n hn
    exact Nat.mul_div_cancel' (mem_filter.mp hn).2
  · intro m _
    rfl

/-- Exact dilation identity: the conditioned term has endpoint `N/q`. -/
theorem conditioned_prefix_dilation {A : Type*} (L : ℕ → A) (C : A → A → ℝ)
    (q N : ℕ) (hq : 0 < q) (hN : 0 < N) (hd : q ∣ N)
    (hL : ∀ m, L (q*m) = L m) :
    q * prefixMean N (fun n => if q ∣ n then C (L n) (L (n+q)) else 0) =
      prefixMean (N/q) (fun m => C (L m) (L (m+1))) := by
  have hT : 0 < N/q := Nat.div_pos (Nat.le_of_dvd hN hd) hq
  have heN : N = q*(N/q) := (Nat.mul_div_cancel' hd).symm
  have he : (∑ n ∈ range N, if q ∣ n then C (L n) (L (n+q)) else 0) =
      ∑ m ∈ range (N/q), C (L m) (L (m+1)) := by
    conv_lhs => rw [heN]
    rw [sum_divisible_range q (N/q) hq]
    apply sum_congr rfl
    intro m _
    rw [← Nat.mul_add_one, hL, hL]
  unfold prefixMean
  rw [he]
  have hNc : (N : ℝ) = (q : ℝ)*(N/q : ℕ) := by exact_mod_cast heN
  rw [hNc]
  have hqc : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hTc : (N/q : ℕ) ≠ 0 := hT.ne'
  field_simp

#print axioms prefixMean_endpoint_bound
#print axioms conditioned_prefix_dilation
end Erdos371.FiniteInformation
