import Submission.PrimeRotation

/-! A finite Fejér-kernel argument for prime rotations. -/
namespace Erdos972PrimeFejer
open Finset Complex
open scoped ComplexConjugate
open Erdos972ExponentialSum Erdos972VaughanSums Erdos972PrimeRotation

lemma conjugate_phase (x : ℝ) : conj (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

lemma primeExpSum_neg (x : ℝ) (N : ℕ) : primeExpSum (-x) N = conj (primeExpSum x N) := by
  unfold primeExpSum
  rw [map_sum]
  apply sum_congr rfl
  intro p hp
  rw [map_mul, Complex.conj_ofReal, conjugate_phase]
  congr 1
  congr 1
  ring

lemma norm_primeExpSum_neg (x : ℝ) (N : ℕ) : ‖primeExpSum (-x) N‖ = ‖primeExpSum x N‖ := by
  rw [primeExpSum_neg, norm_conj]

lemma norm_primeExpSum_difference_le (θ E : ℝ) (N H : ℕ)
    (hE : ∀ h : ℕ, 0 < h → h ≤ H → ‖primeExpSum ((h : ℝ) * θ) N‖ ≤ E)
    {i j : ℕ} (hi : i < H) (hj : j < H) (hij : i ≠ j) :
    ‖primeExpSum (((i : ℝ) - j) * θ) N‖ ≤ E := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have he : ((i : ℝ) - j) * θ = -((j - i : ℕ) * θ) := by
      rw [Nat.cast_sub hij.le]
      ring
    rw [he, norm_primeExpSum_neg]
    exact hE (j - i) (Nat.sub_pos_of_lt hij) ((Nat.sub_le j i).trans hj.le)
  · have he : ((i : ℝ) - j) * θ = (i - j : ℕ) * θ := by rw [Nat.cast_sub hji.le]
    rw [he]
    exact hE (i - j) (Nat.sub_pos_of_lt hji) ((Nat.sub_le i j).trans hi.le)

noncomputable def dirichletKernel (H : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ range H, phase (x * j)

lemma norm_dirichletKernel_le (H : ℕ) (x : ℝ) : ‖dirichletKernel H x‖ ≤ H := by
  calc
    _ ≤ ∑ j ∈ range H, ‖phase (x * j)‖ := norm_sum_le _ _
    _ = _ := by simp

lemma norm_dirichletKernel_mul_le (H : ℕ) (x : ℝ) :
    ‖dirichletKernel H x‖ * ‖phase x - 1‖ ≤ 2 := by
  have he : dirichletKernel H x = ∑ j ∈ range H, (phase x) ^ j := by
    exact sum_congr rfl (fun j hj => phase_nat_mul x j)
  rw [he]
  exact geom_sum_norm_mul_le_two (norm_phase x) H

lemma dirichletKernel_energy (H : ℕ) (x : ℝ) :
    ((‖dirichletKernel H x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ range H, ∑ j ∈ range H, phase (((i : ℝ) - j) * x) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  unfold dirichletKernel
  rw [map_sum, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [conjugate_phase, ← phase_add]
  congr 1
  ring

noncomputable def primeKernelEnergy (θ t : ℝ) (N H : ℕ) : ℝ :=
  ∑ p ∈ (Ioc 0 N).filter Nat.Prime, Real.log p * ‖dirichletKernel H (θ * p - t)‖ ^ 2

lemma primeKernelEnergy_fourier (θ t : ℝ) (N H : ℕ) :
    (primeKernelEnergy θ t N H : ℂ) =
      ∑ i ∈ range H, ∑ j ∈ range H,
        phase (-((i : ℝ) - j) * t) * primeExpSum (((i : ℝ) - j) * θ) N := by
  unfold primeKernelEnergy
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, dirichletKernel_energy, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  unfold primeExpSum
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  have he : ((i : ℝ) - j) * (θ * p - t) =
      -((i : ℝ) - j) * t + (((i : ℝ) - j) * θ) * p := by ring
  rw [he, phase_add]
  ring

lemma primeExpSum_zero (N : ℕ) : primeExpSum 0 N = (Chebyshev.theta N : ℂ) := by
  simp only [primeExpSum, zero_mul, phase, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one, Chebyshev.theta, Nat.floor_natCast, Complex.ofReal_sum]

/-- The diagonal Fourier terms dominate when all nonzero frequencies are small. -/
theorem primeKernelEnergy_lower (θ t E : ℝ) (N H : ℕ) (hE0 : 0 ≤ E)
    (hE : ∀ h : ℕ, 0 < h → h ≤ H → ‖primeExpSum ((h : ℝ) * θ) N‖ ≤ E) :
    (H : ℝ) * Chebyshev.theta N - (H : ℝ) ^ 2 * E ≤ primeKernelEnergy θ t N H := by
  let A : ℕ → ℕ → ℂ := fun i j =>
    phase (-((i : ℝ) - j) * t) * primeExpSum (((i : ℝ) - j) * θ) N
  have hdiag (i : ℕ) : A i i = (Chebyshev.theta N : ℂ) := by
    simp only [A, sub_self, neg_zero, zero_mul, primeExpSum_zero, phase,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  have hpoint (i j : ℕ) (hi : i ∈ range H) (hj : j ∈ range H) :
      ‖A i j - (if i = j then (Chebyshev.theta N : ℂ) else 0)‖ ≤ E := by
    by_cases hij : i = j
    · subst j
      simpa only [if_true, hdiag, sub_self, norm_zero] using hE0
    · rw [if_neg hij, sub_zero]
      dsimp [A]
      rw [norm_mul, norm_phase, one_mul]
      exact norm_primeExpSum_difference_le θ E N H hE (mem_range.mp hi) (mem_range.mp hj) hij
  have he : ((primeKernelEnergy θ t N H - (H : ℝ) * Chebyshev.theta N : ℝ) : ℂ) =
      ∑ i ∈ range H, ∑ j ∈ range H,
        (A i j - if i = j then (Chebyshev.theta N : ℂ) else 0) := by
    simp only [sum_sub_distrib, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast]
    rw [primeKernelEnergy_fourier]
    congr 1
    simp only [sum_ite_eq, mem_range]
    simp only [sum_congr rfl (fun i hi => if_pos (mem_range.mp hi)), sum_const, card_range,
      nsmul_eq_mul]
  have hb : ‖((primeKernelEnergy θ t N H - (H : ℝ) * Chebyshev.theta N : ℝ) : ℂ)‖ ≤
      (H : ℝ) ^ 2 * E := by
    rw [he]
    calc
      _ ≤ ∑ i ∈ range H, ‖∑ j ∈ range H,
          (A i j - if i = j then (Chebyshev.theta N : ℂ) else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range H, ∑ j ∈ range H, E := by
        apply sum_le_sum
        intro i hi
        exact (norm_sum_le _ _).trans (sum_le_sum (fun j hj => hpoint i j hi hj))
      _ = _ := by simp; ring
  rw [Complex.norm_real, Real.norm_eq_abs] at hb
  linarith [(abs_le.mp hb).1]

lemma dirichletKernel_sq_le_of_avoids (H : ℕ) (x δ : ℝ) (hδ : 0 < δ)
    (hx : δ ≤ ‖phase x - 1‖) : ‖dirichletKernel H x‖ ^ 2 ≤ 4 / δ ^ 2 := by
  have hb : ‖dirichletKernel H x‖ ≤ 2 / δ := by
    apply (le_div_iff₀ hδ).mpr
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans (norm_dirichletKernel_mul_le H x)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hs

/-- If every sufficiently large prime misses an arc, the kernel energy has a
uniform upper bound controlled by the finitely many small primes. -/
theorem primeKernelEnergy_upper_of_avoids (θ t δ : ℝ) (hδ : 0 < δ) (B N H : ℕ)
    (havoid : ∀ p : ℕ, B < p → p.Prime → δ ≤ ‖phase (θ * p - t) - 1‖) :
    primeKernelEnergy θ t N H ≤
      (H : ℝ) ^ 2 * Chebyshev.theta B + (4 / δ ^ 2) * Chebyshev.theta N := by
  classical
  let s := (Ioc 0 N).filter Nat.Prime
  have hsmall : (∑ p ∈ s, if p ≤ B then Real.log p else 0) ≤ Chebyshev.theta B := by
    rw [← sum_filter, Chebyshev.theta, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp, hpB⟩ := mem_filter.mp hp
      obtain ⟨hpN, hpprime⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hpN).1, hpB⟩, hpprime⟩
    · intro p hp hnot
      exact Real.log_natCast_nonneg p
  have hlarge : (∑ p ∈ s, Real.log p) = Chebyshev.theta N := by
    simp only [s, Chebyshev.theta, Nat.floor_natCast]
  have hpoint (p : ℕ) (hp : p ∈ s) :
      Real.log p * ‖dirichletKernel H (θ * p - t)‖ ^ 2 ≤
        (H : ℝ) ^ 2 * (if p ≤ B then Real.log p else 0) +
          (4 / δ ^ 2) * Real.log p := by
    have hlog := Real.log_natCast_nonneg p
    by_cases hpB : p ≤ B
    · rw [if_pos hpB]
      have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_dirichletKernel_le H (θ * p - t)) 2
      have ht := mul_le_mul_of_nonneg_left hh hlog
      have hpos : 0 ≤ 4 / δ ^ 2 * Real.log p := by positivity
      nlinarith
    · rw [if_neg hpB, mul_zero, zero_add]
      have hb := dirichletKernel_sq_le_of_avoids H (θ * p - t) δ hδ
        (havoid p (Nat.lt_of_not_ge hpB) (mem_filter.mp hp).2)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hlog
  have ht := sum_le_sum hpoint
  simp only [sum_add_distrib, ← mul_sum, hlarge] at ht
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)) le_rfl)

/-- Every arc of an irrational rotation is visited by arbitrarily large primes.
The proof uses common good scales, not an all-scale prime number theorem. -/
theorem exists_prime_phase_close {θ : ℝ} (hθ : 1 < θ) (hI : Irrational θ)
    (t δ : ℝ) (hδ : 0 < δ) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ‖phase (θ * p - t) - 1‖ < δ := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨H, hH⟩ := exists_nat_gt (8 / δ ^ 2)
  have hH0 : 0 < H := by
    have h0 : (0 : ℝ) < H := lt_of_lt_of_le (by positivity : 0 < 8 / δ ^ 2) hH.le
    exact_mod_cast h0
  have hHpos : (0 : ℝ) < H := Nat.cast_pos.mpr hH0
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  let ε : ℝ := c / (4 * H)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp Erdos972ChebyshevLower.eventually_theta_lower
  obtain ⟨R, hR⟩ := exists_nat_gt (max A (4 * H * Chebyshev.theta B / c))
  obtain ⟨u, huR, hfreq⟩ := exists_common_prime_scale hθ hI H hH0 hε R
  have hu0 : 0 < u := (Nat.zero_le R).trans_lt huR
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu0
  have hule : (u : ℝ) ≤ (u : ℝ) ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hu1 (show 1 ≤ 6 by omega)
  have hX : max A (4 * H * Chebyshev.theta B / c) < (u : ℝ) ^ 6 :=
    (hR.trans (Nat.cast_lt.mpr huR)).trans_le hule
  have htheta : c * (u : ℝ) ^ 6 ≤ Chebyshev.theta (u ^ 6 : ℕ) := by
    have hh := hA ((u : ℝ) ^ 6) ((le_max_left _ _).trans hX.le)
    simpa only [c, Nat.cast_pow] using hh
  have hthetaPos : 0 < Chebyshev.theta (u ^ 6 : ℕ) :=
    lt_of_lt_of_le (by positivity) htheta
  have hlarge : 4 * H * Chebyshev.theta B < (u : ℝ) ^ 6 * c :=
    (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt hX)
  have hlow := primeKernelEnergy_lower θ t (ε * (u : ℝ) ^ 6) (u ^ 6) H
    (by positivity) hfreq
  have hupp := primeKernelEnergy_upper_of_avoids θ t δ hδ B (u ^ 6) H hnone
  have hcoef : (H : ℝ) / 2 < H - 4 / δ ^ 2 := by
    have he : (8 : ℝ) / δ ^ 2 = 2 * (4 / δ ^ 2) := by ring
    rw [he] at hH
    linarith
  have hmul := mul_lt_mul_of_pos_right hcoef hthetaPos
  have hthetam := mul_le_mul_of_nonneg_left htheta (show (0 : ℝ) ≤ H / 2 by positivity)
  have hsmallm := mul_lt_mul_of_pos_left hlarge hHpos
  have heps : (H : ℝ) ^ 2 * ε = H * c / 4 := by dsimp [ε]; field_simp
  rw [← mul_assoc, heps] at hlow
  nlinarith

lemma phase_intCast (m : ℤ) : phase (m : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I m using 1
  congr 1
  push_cast
  ring

lemma phase_sub_eq_fract_sub (x t : ℝ) : phase (x - t) = phase (Int.fract x - t) := by
  have he : x - t = (Int.fract x - t) + (⌊x⌋ : ℝ) := by
    linarith [Int.fract_add_floor x]
  rw [he, phase_add, phase_intCast, mul_one]

lemma norm_phase_abs_sub_one (x : ℝ) : ‖phase |x| - 1‖ = ‖phase x - 1‖ := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), ← conjugate_phase]
    have he : conj (phase x) - 1 = conj (phase x - 1) := by simp only [map_sub, map_one]
    rw [he, norm_conj]

lemma fract_mem_Ioo_of_phase_close (x t η : ℝ) (hη : 0 < η)
    (hηt : η ≤ t) (hηt' : η ≤ 1 - t)
    (hx : ‖phase (x - t) - 1‖ < 4 * η) :
    t - η < Int.fract x ∧ Int.fract x < t + η := by
  let z : ℝ := Int.fract x - t
  have hz : |z| ≤ 1 - η := abs_le.mpr (by
    dsimp [z]
    constructor <;> linarith [Int.fract_nonneg x, Int.fract_lt_one x])
  have hz1 : |z| ≤ 1 := by linarith
  have hb := norm_phase_sub_one_lower (abs_nonneg z) hz1
  rw [norm_phase_abs_sub_one] at hb
  rw [phase_sub_eq_fract_sub] at hx
  change ‖phase z - 1‖ < 4 * η at hx
  have hza : |z| < η := by
    by_contra hnot
    have hm : η ≤ min |z| (1 - |z|) := le_min (le_of_not_gt hnot) (by linarith)
    linarith
  obtain ⟨hzlo, hzhi⟩ := abs_lt.mp hza
  dsimp [z] at hzlo hzhi
  constructor <;> linarith

/-- Qualitative Vinogradov density: primes visit every nonempty fractional-part
interval under an irrational rotation. -/
theorem exists_prime_fract_mem {θ : ℝ} (hθ : 1 < θ) (hI : Irrational θ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ a < Int.fract (θ * p) ∧ Int.fract (θ * p) < b := by
  obtain ⟨p, hpB, hp, hclose⟩ := exists_prime_phase_close hθ hI
    ((a + b) / 2) (4 * ((b - a) / 2)) (by linarith) B
  have hf := fract_mem_Ioo_of_phase_close (θ * p) ((a + b) / 2) ((b - a) / 2)
    (by linarith) (by linarith) (by linarith) hclose
  refine ⟨p, hpB, hp, ?_, ?_⟩ <;> linarith [hf.1, hf.2]

lemma floor_coprime_of_fract_div_mem {x : ℝ} (hx : 0 ≤ x)
    (M : ℕ) (hM : 0 < M)
    (hlo : 1 / (M : ℝ) < Int.fract (x / M))
    (hhi : Int.fract (x / M) < 2 / (M : ℝ)) : (⌊x⌋₊).Coprime M := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have he := Int.floor_add_fract (x / M)
  have hm := congrArg (fun y : ℝ => y * M) he
  dsimp only at hm
  rw [div_mul_cancel₀ _ hMr.ne'] at hm
  have hl := (div_lt_iff₀ hMr).mp hlo
  have hh := (lt_div_iff₀ hMr).mp hhi
  have hf : ⌊x⌋ = (M : ℤ) * ⌊x / M⌋ + 1 := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> nlinarith
  change Nat.gcd ⌊x⌋₊ M = 1
  rw [← Int.gcd_natCast_natCast, Int.natCast_floor_eq_floor hx, hf]
  rw [add_comm, Int.gcd_add_mul_left_left]
  simp

/-- Any fixed finite set of local divisibility obstructions can be avoided
while keeping the input genuinely prime. This does not assert that the output
is prime. -/
theorem exists_large_prime_coprime_output {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (M : ℕ) (hM : 0 < M) (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ (⌊α * p⌋₊).Coprime M := by
  by_cases hM1 : M = 1
  · subst M
    obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (B + 1)
    exact ⟨p, by omega, hp, by simp⟩
  have hM2 : 2 ≤ M := by omega
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  let θ : ℝ := α / M + 2
  have hθ : 1 < θ := by
    have ha : 0 < α / M := div_pos (by linarith) hMr
    dsimp [θ]
    linarith
  have hθI : Irrational θ := (hI.div_natCast hM.ne').add_natCast 2
  obtain ⟨p, hpB, hp, hlo, hhi⟩ := exists_prime_fract_mem hθ hθI
    (1 / M) (2 / M) (by positivity)
    (div_lt_div_of_pos_right (by norm_num) hMr)
    ((div_le_one hMr).mpr (by exact_mod_cast hM2)) B
  have he : Int.fract (θ * p) = Int.fract (α * p / M) := by
    have he' : θ * p = α * p / M + ((2 * p : ℕ) : ℝ) := by
      dsimp [θ]
      push_cast
      ring
    rw [he', Int.fract_add_natCast]
  rw [he] at hlo hhi
  exact ⟨p, hpB, hp, floor_coprime_of_fract_div_mem (by positivity) M hM hlo hhi⟩

/-- An unconditional infinite-set consequence with prime inputs and a fixed
output modulus. The modulus is fixed before choosing the prime. -/
theorem infinite_prime_inputs_coprime_outputs {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (M : ℕ) (hM : 0 < M) :
    {p : ℕ | p.Prime ∧ (⌊α * p⌋₊).Coprime M}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨p, hpB, hp, hcop⟩ := exists_large_prime_coprime_output hα hI M hM B
  exact ⟨p, ⟨hp, hcop⟩, hpB⟩

#print axioms infinite_prime_inputs_coprime_outputs
#print axioms exists_large_prime_coprime_output
#print axioms exists_prime_fract_mem
#print axioms exists_prime_phase_close
#print axioms primeKernelEnergy_upper_of_avoids
#print axioms primeKernelEnergy_lower
#print axioms primeKernelEnergy_fourier
end Erdos972PrimeFejer
