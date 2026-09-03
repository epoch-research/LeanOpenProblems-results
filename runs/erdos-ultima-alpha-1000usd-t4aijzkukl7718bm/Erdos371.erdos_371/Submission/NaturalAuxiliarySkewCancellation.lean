import Submission.CyclicAuxiliarySkewCancellation

/-! Removal of cyclic wrap-around for auxiliary-gap skew cancellation, and an
exact dilation identity recording the auxiliary gap that remains after
conditioning only on the prime multiplier. -/
namespace Erdos371.SkewKernel
open Finset Filter FiniteInformation
open scoped Topology

lemma cyclic_pairMean_prefix (N q : ℕ) [NeZero N] {A : Type*}
    (L : ℕ → A) (C : A → A → ℝ) :
    mean (uniformLaw (ZMod N)) (fun x => C (L x.val) (L (x+(q : ZMod N)).val)) =
      prefixMean N (fun n => C (L n) (L ((n+q)%N))) := by
  rw [mean_uniform_zmod_prefix]
  apply prefixMean_congr
  intro n hn
  simp only [← Nat.cast_add, ZMod.val_natCast, Nat.mod_eq_of_lt hn]

lemma cyclic_pairMean_natural_error (N q : ℕ) [NeZero N] (hq : q ≤ N) {A : Type*}
    (L : ℕ → A) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |mean (uniformLaw (ZMod N)) (fun x => C (L x.val) (L (x+(q : ZMod N)).val)) -
      prefixMean N (fun n => C (L n) (L (n+q)))| ≤ 2*q/N := by
  rw [cyclic_pairMean_prefix]
  have he := prefixMean_tail_bound N q hq
    (fun n => C (L n) (L ((n+q)%N))) (fun n => C (L n) (L (n+q))) 1
    (fun _ _ => hC _ _) (fun _ _ => hC _ _)
    (fun n hn => by dsimp only; rw [Nat.mod_eq_of_lt (by omega : n+q < N)])
  simpa only [mul_one] using he

/-- Auxiliary positive-gap cancellation is uniform over arbitrary natural
label sequences, including sequences depending on the endpoint. The kernel is
chosen before any bound on the base gap. -/
theorem exists_natural_auxiliary_skew_kernel (A : Type*) [Fintype A] (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, ∃ w : ℕ → ℝ,
      (∀ k, 0 ≤ w k) ∧ w 0 = 0 ∧ (∀ k, H ≤ k → w k = 0) ∧
      (∑ k ∈ range H, w k) = 1 ∧
      ∀ B : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (L : ℕ → A) (C : A → A → ℝ),
        (∀ a b, C b a = -C a b) → (∀ a b, |C a b| ≤ 1) → ∀ p ≤ B,
        |∑ k ∈ range H, w k * prefixMean N (fun n => C (L n) (L (n+k*p)))| < ε := by
  obtain ⟨H,w,hw0,hwz,hwH,hws,hcyc⟩ := exists_cyclic_auxiliary_skew_kernel A (ε/2) (by positivity)
  refine ⟨H,w,hw0,hwz,hwH,hws,?_⟩
  intro B
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2*((H*B : ℕ) : ℝ))
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (H*B),
    ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/2)] with N hN hNB ht
  letI : NeZero N := ⟨hN.ne'⟩
  intro L C hC hCb p hp
  let V (k : ℕ) : ℝ := mean (uniformLaw (ZMod N))
    (fun x => C (L x.val) (L (x+((k*p : ℕ) : ZMod N)).val))
  let U (k : ℕ) : ℝ := prefixMean N (fun n => C (L n) (L (n+k*p)))
  have hc : |∑ k ∈ range H, w k*V k| < ε/2 := by
    simpa only [V, Nat.cast_mul] using hcyc N (fun x => L x.val) C hC hCb (p : ZMod N)
  have he : |(∑ k ∈ range H, w k*V k)-(∑ k ∈ range H, w k*U k)| ≤ 2*(H*B : ℕ)/N := by
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ k ∈ range H, |w k*V k-w k*U k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range H, w k*(2*(H*B : ℕ)/N) := by
        apply sum_le_sum
        intro k hk
        have hkH : k ≤ H := (mem_range.mp hk).le
        have hkB : k*p ≤ H*B := Nat.mul_le_mul hkH hp
        have hb := cyclic_pairMean_natural_error N (k*p) (hkB.trans hNB) L C hCb
        rw [← mul_sub, abs_mul, abs_of_nonneg (hw0 k)]
        apply mul_le_mul_of_nonneg_left (hb.trans ?_) (hw0 k)
        gcongr
      _ = _ := by rw [← sum_mul,hws,one_mul]
  have htri := abs_sub_le (∑ k ∈ range H, w k*U k) (∑ k ∈ range H, w k*V k) 0
  simp only [sub_zero] at htri
  rw [abs_sub_comm] at he
  change |∑ k ∈ range H, w k*U k| < ε
  linarith

/-- Conditioning only on q|n leaves an auxiliary gap `a` after dilation.
Multiplier invariance does not turn this into the adjacent comparison. -/
theorem conditioned_prefix_dilation_gap {A : Type*} (L : ℕ → A) (C : A → A → ℝ)
    (q N a : ℕ) (hq : 0 < q) (hN : 0 < N) (hd : q ∣ N)
    (hL : ∀ m, L (q*m) = L m) :
    q*prefixMean N (fun n => if q ∣ n then C (L n) (L (n+q*a)) else 0) =
      prefixMean (N/q) (fun m => C (L m) (L (m+a))) := by
  have hT : 0 < N/q := Nat.div_pos (Nat.le_of_dvd hN hd) hq
  have heN : N = q*(N/q) := (Nat.mul_div_cancel' hd).symm
  have he : (∑ n ∈ range N, if q ∣ n then C (L n) (L (n+q*a)) else 0) =
      ∑ m ∈ range (N/q), C (L m) (L (m+a)) := by
    conv_lhs => rw [heN]
    rw [sum_divisible_range q (N/q) hq]
    apply sum_congr rfl
    intro m _
    rw [← Nat.mul_add, hL, hL]
  unfold prefixMean
  rw [he]
  have hNc : (N : ℝ) = (q : ℝ)*(N/q : ℕ) := by exact_mod_cast heN
  rw [hNc]
  have hqc : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hTc : (N/q : ℕ) ≠ 0 := hT.ne'
  field_simp

/-- The exact auxiliary-gap identity with a rounding error when q does not
necessarily divide N. The error does not depend on the auxiliary gap. -/
theorem conditioned_prefix_dilation_gap_error {A : Type*} (L : ℕ → A) (C : A → A → ℝ)
    (q N a : ℕ) (hq : 0 < q) (hqN : q ≤ N)
    (hC : ∀ x y, |C x y| ≤ 1) (hL : ∀ m, L (q*m) = L m) :
    |q*prefixMean N (fun n => if q ∣ n then C (L n) (L (n+q*a)) else 0) -
      prefixMean (N/q) (fun m => C (L m) (L (m+a)))| ≤ 2*(q : ℝ)^2/N := by
  classical
  let M := q*(N/q)
  have hT : 0 < N/q := Nat.div_pos hqN hq
  have hM : 0 < M := Nat.mul_pos hq hT
  have hMN : M ≤ N := Nat.mul_div_le N q
  have htail : N-M ≤ q := by
    have he := Nat.div_add_mod N q
    have hr := Nat.mod_lt N hq
    dsimp [M]
    omega
  have hd : q ∣ M := dvd_mul_right q (N/q)
  have h := conditioned_prefix_dilation_gap L C q M a hq hM hd hL
  have hquot : M/q = N/q := Nat.mul_div_right _ hq
  rw [hquot] at h
  rw [← h, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  have hb := prefixMean_endpoint_bound M N hM hMN
    (fun n => if q ∣ n then C (L n) (L (n+q*a)) else 0) 1
    (fun n _ => by dsimp only; split_ifs <;> simp_all)
  simp only [mul_one] at hb
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) q)
  calc
    _ ≤ (q : ℝ)*(2*(N-M : ℕ)/N) := hm
    _ ≤ (q : ℝ)*(2*q/N) := by gcongr
    _ = _ := by ring

#print axioms exists_natural_auxiliary_skew_kernel
#print axioms conditioned_prefix_dilation_gap_error
end Erdos371.SkewKernel
