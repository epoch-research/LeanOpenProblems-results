import Submission.PrimeOutputGcdDeterminant

/-! The logarithmic individual-row bound is attained near the output
cutoff. This is not a disproof of the original prime-pair conjecture. -/
namespace Erdos972PrimeRowLogSharpness

open Finset Filter
open scoped Topology
open Erdos972PrimeOutputGcdDeterminant Erdos972PrimePowerError
open Erdos972PrimeRoughOutputs Erdos972SelbergLowerTest
open Erdos972ChebyshevPNT Erdos972ChebyshevRowMean Erdos972ExponentialSum

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- At a prime cutoff, its own full output divisor carries exactly one
nonzero prime input. Thus the full logarithmic weight is attained. -/
theorem output_row_at_prime_cutoff {α : ℝ} (hα : 1 ≤ α) {p : ℕ}
    (hp : p.Prime) (hαp : α < p) :
    row (Ioc 0 p) primeWeight (floorMul α) (floorMul α p) = Real.log p := by
  have hpd := self_le_floorMul hα p
  have hd : α < (floorMul α p:ℝ) := hαp.trans_le (Nat.cast_le.mpr hpd)
  unfold row
  rw [sum_eq_single p]
  · simp only [dvd_refl, if_true, primeWeight, hp]
  · intro q hq hqp
    by_cases hdiv : floorMul α p ∣ floorMul α q
    · rw [if_pos hdiv]
      have hnq : ¬ q.Prime := by
        intro hqprime
        exact hqp (at_most_one_prime_input hα hd hpd (mem_Ioc.mp hq).2 le_rfl
          hqprime hp hdiv (dvd_refl _))
      simp only [primeWeight, if_neg hnq]
    · simp only [if_neg hdiv]
  · intro hnot
    exact (hnot (mem_Ioc.mpr ⟨hp.pos, le_rfl⟩)).elim

/-- There is no uniform constant bound for full prime-input rows even when
the output divisor is at least the input cutoff. -/
theorem exists_arbitrarily_large_full_row {α : ℝ} (hα : 1 ≤ α) (C : ℝ) (B : ℕ) :
    ∃ N d : ℕ, B < N ∧ N.Prime ∧ d = floorMul α N ∧
      N ≤ d ∧ α < (d:ℝ) ∧ C < row (Ioc 0 N) primeWeight (floorMul α) d := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((hlog.eventually_gt_atTop C).and
      (tendsto_natCast_atTop_atTop.eventually_gt_atTop α))
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max (B+1) T)
  have hBp : B < p := by have := (le_max_left (B+1) T).trans hpge; omega
  obtain ⟨hlogp, hαp⟩ := hT p ((le_max_right (B+1) T).trans hpge)
  have hpd := self_le_floorMul hα p
  refine ⟨p, floorMul α p, hBp, hp, rfl, hpd,
    hαp.trans_le (Nat.cast_le.mpr hpd), ?_⟩
  rw [output_row_at_prime_cutoff hα hp hαp]
  exact hlogp

/-- In particular, the bound M*log N cannot be replaced by C*M uniformly
in the full stated divisor range: the case M=1 already forbids it. -/
theorem no_uniform_constant_multiple_bound {α : ℝ} (hα : 1 ≤ α) :
    ¬ ∃ C : ℝ, ∀ N d M : ℕ, 0 < M → N ≤ d*M → α*(M:ℝ) < d →
      row (Ioc 0 N) primeWeight (floorMul α) d ≤ C*M := by
  rintro ⟨C, hC⟩
  obtain ⟨N, d, _, _, _, hNd, hd, hrow⟩ := exists_arbitrarily_large_full_row hα C 0
  have hh := hC N d 1 (by decide) (by simpa using hNd) (by simpa using hd)
  simp only [Nat.cast_one, mul_one] at hh
  exact (not_lt_of_ge hh) hrow

lemma primeWeight_sum_theta (N : ℕ) :
    (∑ p ∈ Ioc 0 N, primeWeight p) = Chebyshev.theta N := by
  simp only [Chebyshev.theta, Nat.floor_natCast, primeWeight, sum_filter]

lemma output_row_ge_primeWeight {α : ℝ} {N p : ℕ} (hp : p ∈ Ioc 0 N) :
    primeWeight p ≤ row (Ioc 0 N) primeWeight (floorMul α) (floorMul α p) := by
  have hh := single_le_sum (s := Ioc 0 N)
    (f := fun n => if floorMul α p ∣ floorMul α n then primeWeight n else 0)
    (fun n hn => by dsimp only; split_ifs <;> first | exact primeWeight_nonneg _ | exact le_rfl) hp
  simpa only [dvd_refl, if_true, row] using hh

noncomputable def terminalBlockEnergy (α : ℝ) (X : ℕ) : ℝ :=
  ∑ d ∈ Ioc (floorMul α X) (floorMul α (2*X)),
    (row (Ioc 0 (2*X)) primeWeight (floorMul α) d-Chebyshev.psi (2*X:ℕ)/(d:ℝ))^2

/-- The large-output block has a genuine logarithmic variance contribution,
coming from the distinct full output divisors of prime inputs. -/
theorem terminalBlockEnergy_lower {α : ℝ} (hα : 1 ≤ α) {X : ℕ}
    (hX : 0 < X) (hlog : 28 ≤ Real.log X) :
    (Real.log X-28)*(Chebyshev.theta (2*X:ℕ)-Chebyshev.theta X) ≤
      terminalBlockEnergy α X := by
  classical
  let P := (Ioc X (2*X)).filter Nat.Prime
  let f : ℕ → ℝ := fun d =>
    (row (Ioc 0 (2*X)) primeWeight (floorMul α) d-Chebyshev.psi (2*X:ℕ)/(d:ℝ))^2
  have hterm (p : ℕ) (hp : p ∈ P) : (Real.log X-28)*Real.log p ≤ f (floorMul α p) := by
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    have hXp := (mem_Ioc.mp hpI).1
    have hpN : p ∈ Ioc 0 (2*X) := mem_Ioc.mpr ⟨hX.trans hXp, (mem_Ioc.mp hpI).2⟩
    have hrow := output_row_ge_primeWeight (α := α) hpN
    rw [primeWeight, if_pos hpp] at hrow
    have hg : (X:ℝ) ≤ floorMul α p := Nat.cast_le.mpr (hXp.le.trans (self_le_floorMul hα p))
    have hXR : (0:ℝ) < X := Nat.cast_pos.mpr hX
    have hpsi : Chebyshev.psi (2*X:ℕ) ≤ 14*(X:ℝ) := by
      have hh := psi_le_seven_mul (Nat.cast_nonneg (2*X) : (0:ℝ) ≤ (2*X:ℕ))
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hh ⊢
      linarith only [hh]
    have hc : Chebyshev.psi (2*X:ℕ)/(floorMul α p:ℝ) ≤ 14 :=
      (div_le_iff₀ (hXR.trans_le hg)).mpr (by linarith only [hpsi, hg])
    have hlp := monotone_log_natCast hXp.le
    have ha : 0 ≤ Real.log p-14 := by linarith only [hlp, hlog]
    have hb : Real.log p-14 ≤ row (Ioc 0 (2*X)) primeWeight (floorMul α) (floorMul α p)-
        Chebyshev.psi (2*X:ℕ)/(floorMul α p:ℝ) := by linarith only [hc, hrow]
    have hs := pow_le_pow_left₀ ha hb 2
    have hm := mul_nonneg (sub_nonneg.mpr hlp) (Real.log_natCast_nonneg p)
    dsimp only [f]
    nlinarith only [hs, hm]
  have hs : (Real.log X-28)*(Chebyshev.theta (2*X:ℕ)-Chebyshev.theta X) =
      ∑ p ∈ P, (Real.log X-28)*Real.log p := by
    rw [← mul_sum]
    congr 1
    have he := sum_Ioc_consecutive primeWeight (Nat.zero_le X) (show X ≤ 2*X by omega)
    rw [primeWeight_sum_theta, primeWeight_sum_theta] at he
    have heP : (∑ p ∈ P, Real.log p) = ∑ p ∈ Ioc X (2*X), primeWeight p := by
      simp only [P, sum_filter, primeWeight]
    rw [heP]
    linarith only [he]
  rw [hs]
  apply (sum_le_sum hterm).trans
  have hinj : Set.InjOn (floorMul α) (↑P : Set ℕ) := (floorMul_strictMono hα).injective.injOn
  have hsub : P.image (floorMul α) ⊆ Ioc (floorMul α X) (floorMul α (2*X)) := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
    obtain ⟨hpI, _⟩ := mem_filter.mp hp
    exact mem_Ioc.mpr ⟨floorMul_strictMono hα (mem_Ioc.mp hpI).1,
      (floorMul_strictMono hα).monotone (mem_Ioc.mp hpI).2⟩
  calc
    _ = ∑ d ∈ P.image (floorMul α), f d := by rw [sum_image hinj]
    _ ≤ terminalBlockEnergy α X := sum_le_sum_of_subset_of_nonneg hsub (fun d hd hnot => sq_nonneg _)

/-- Even the NORMALIZED block energy is unbounded. Thus removing the
logarithm uniformly over all large divisor blocks is impossible. -/
theorem terminalBlockEnergy_div_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun X : ℕ => terminalBlockEnergy α X/(2*(X:ℝ))) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmain : Tendsto (fun X : ℕ => (Real.log X-28)/4) atTop atTop := by
    have hs : Tendsto (fun X : ℕ => Real.log X-28) atTop atTop := by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-28) hlog
    have hh := hs.const_mul_atTop (by norm_num : (0:ℝ) < 1/4)
    convert hh using 1
    funext X
    ring
  apply tendsto_atTop_mono' atTop _ hmain
  have htheta := tendsto_natCast_atTop_atTop.eventually
    (eventually_theta_interval_lower (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) < 2))
  filter_upwards [hlog.eventually_ge_atTop 28, eventually_ge_atTop (1:ℕ), htheta] with X hL hX htheta
  have hX' : (0:ℝ) < X := Nat.cast_pos.mpr hX
  have htheta' : (X:ℝ)/2 ≤ Chebyshev.theta (2*X:ℕ)-Chebyshev.theta X := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, one_mul, sub_self, sub_zero] at htheta ⊢
    convert htheta using 1
    ring
  have hh := mul_le_mul_of_nonneg_left htheta' (sub_nonneg.mpr hL)
  have hl := hh.trans (terminalBlockEnergy_lower hα hX hL)
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*X)).mpr
  convert hl using 1
  ring

#print axioms terminalBlockEnergy_lower
#print axioms terminalBlockEnergy_div_tendsto
#print axioms output_row_at_prime_cutoff
#print axioms exists_arbitrarily_large_full_row
#print axioms no_uniform_constant_multiple_bound

end Erdos972PrimeRowLogSharpness
