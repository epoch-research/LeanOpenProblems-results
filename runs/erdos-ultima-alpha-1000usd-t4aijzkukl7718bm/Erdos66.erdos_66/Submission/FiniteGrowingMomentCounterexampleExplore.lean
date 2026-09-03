import Submission.SparseStartCompletePaletteExplore

/-! Finite cyclic Boolean sets need not satisfy Gaussian lower bounds for
moments of order comparable to their logarithmic mean. This is a limitation
of a possible proof method, not a disproof of Erdős 66 over the naturals. -/
namespace Erdos66FiniteGrowingMomentCounterexample
open Filter Erdos66SparseStartCompletePalette Erdos66SaturatingCyclicFamily
  Erdos66OuterCarryProfile Erdos66LogTuning
open scoped Classical Topology
set_option maxHeartbeats 1700000

lemma factorial_lower (k : ℕ) : ((k:ℝ)/Real.exp 1)^k ≤ (k.factorial:ℝ) := by
  have h := Real.pow_div_factorial_le_exp (k:ℝ) (Nat.cast_nonneg k) k
  have he : Real.exp (k:ℝ)=(Real.exp 1)^k := by
    simpa only [mul_one] using Real.exp_nat_mul 1 k
  rw [he] at h
  have hp : (0:ℝ)<k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hh := (div_le_iff₀ hp).mp h
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (Real.exp_pos 1) k)).mpr
  simpa only [mul_comm] using hh

lemma finite_even_moment_bound {α : Type*} [Fintype α] [Nonempty α]
    (e : α → ℝ) (E : ℝ) (hE : 0 ≤ E) (he : ∀ a, |e a| ≤ E) (k : ℕ) :
    (∑ a : α, (e a)^(2*k))/(Fintype.card α:ℝ) ≤ E^(2*k) := by
  have hpoint (a : α) : (e a)^(2*k) ≤ E^(2*k) := by
    have hh : (e a)^2 ≤ E^2 := by
      have ht := pow_le_pow_left₀ (abs_nonneg (e a)) (he a) 2
      simpa only [sq_abs] using ht
    simpa only [←pow_mul] using pow_le_pow_left₀ (sq_nonneg (e a)) hh k
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hpoint a)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α := α))).mpr
  simpa only [mul_comm] using hs

lemma even_moment_lt_factorial {α : Type*} [Fintype α] [Nonempty α]
    (e : α → ℝ) (μ : ℝ) (hμ : 0 < μ) (k : ℕ) (hk : k≠0)
    (hsize : μ/2 ≤ (k:ℝ)) (he : ∀ a, |e a| ≤ μ/16) :
    (∑ a : α, (e a)^(2*k))/(Fintype.card α:ℝ) < (k.factorial:ℝ)*μ^k := by
  have hb := finite_even_moment_bound e (μ/16) (by positivity) he k
  have hsmall : (μ/16)^2 < (k:ℝ)*μ/Real.exp 1 := by
    apply (lt_div_iff₀ (Real.exp_pos 1)).mpr
    have h₁ := mul_le_mul_of_nonneg_right hsize hμ.le
    have h₂ := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (sq_nonneg (μ/16))
    nlinarith [sq_pos_of_pos hμ]
  have hp := pow_lt_pow_left₀ hsmall (sq_nonneg (μ/16)) hk
  have hf := mul_le_mul_of_nonneg_right (factorial_lower k) (pow_nonneg hμ.le k)
  have heq : ((k:ℝ)*μ/Real.exp 1)^k=((k:ℝ)/Real.exp 1)^k*μ^k := by
    rw [←mul_pow]
    congr 1
    ring
  rw [heq] at hp
  rw [pow_mul] at hb
  exact hb.trans_lt (hp.trans_le hf)

/-- There are arbitrarily large cyclic groups with actual logarithmic mean
and a moment order k growing with that mean, yet the centered 2k-th moment
is strictly less than k! times mean^k. Thus such a uniform Gaussian lower
bound cannot follow from finite cyclic Boolean convolution alone. -/
theorem exists_logarithmic_counterexample (N₀ K₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ ∃ hM : NeZero M,
      ∃ B : Finset (ZMod M), ∃ k : ℕ,
        let μ := actualMean M B B
        0<μ ∧ |μ/Real.log M-1/2|<1/4 ∧
        K₀<k ∧ (k:ℝ)≤Real.log M ∧ μ/2≤(k:ℝ) ∧
        (∀ z, |(cyclicCount M B B z:ℝ)-μ|≤μ/16) ∧
        (∑ z : ZMod M, ((cyclicCount M B B z:ℝ)-μ)^(2*k))/(M:ℝ)<
          (k.factorial:ℝ)*μ^k := by
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    (log_nat_atTop.eventually_gt_atTop (8*((K₀:ℝ)+2)))
  obtain ⟨M,hMN,hodd,hM,B,P,hB,hBP,htune,hsub,hnest,hflat,hfull,hcard,hcover⟩ :=
    exists_sparse_start_complete_palette (1/2) (1/4) (1/16) 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (max N₀ (max L 2))
  letI := hM
  let μ := actualMean M B B
  have hM2 : 2<M := by omega
  have hl : 0<Real.log (M:ℝ) := Real.log_pos (by exact_mod_cast (show 1<M by omega))
  have hlogbig : 8*((K₀:ℝ)+2)<Real.log (M:ℝ) := hL M (by omega)
  have hμlo : Real.log (M:ℝ)/4<μ := by
    have hh := (abs_lt.mp htune).1
    have hd : 1/4<μ/Real.log (M:ℝ) := by dsimp only [μ]; linarith
    have hp := (lt_div_iff₀ hl).mp hd
    linarith
  have hμhi : μ<3/4*Real.log (M:ℝ) := by
    have hh := (abs_lt.mp htune).2
    have hd : μ/Real.log (M:ℝ)<3/4 := by dsimp only [μ]; linarith
    exact (div_lt_iff₀ hl).mp hd
  have hμ : 0<μ := by linarith
  have hμbig : 2*((K₀:ℝ)+2)<μ := by linarith
  let k : ℕ := ⌊μ⌋₊
  have hklo : μ<(k:ℝ)+1 := Nat.lt_floor_add_one μ
  have hkhi : (k:ℝ)≤μ := Nat.floor_le hμ.le
  have hkK : K₀<k := by
    have hh : (K₀:ℝ)<k := by nlinarith [Nat.cast_nonneg (α := ℝ) K₀]
    exact_mod_cast hh
  have hkhalf : μ/2≤(k:ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) K₀]
  have hfl (z : ZMod M) : |(cyclicCount M B B z:ℝ)-μ|≤μ/16 := by
    have hh := hflat B hBP B hBP z
    dsimp only [μ]
    convert hh using 1 <;> ring
  refine ⟨M,by omega,hM,B,k,hμ,htune,hkK,by linarith,hkhalf,hfl,?_⟩
  simpa only [ZMod.card] using even_moment_lt_factorial
    (fun z : ZMod M ↦ (cyclicCount M B B z:ℝ)-μ) μ hμ k (by omega) hkhalf hfl

end Erdos66FiniteGrowingMomentCounterexample
