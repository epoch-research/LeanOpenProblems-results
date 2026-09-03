import Submission.QuantitativeSmoothReciprocal

/-! Exact total harmonic dilation defects for the largest-prime-factor label.
For a prime multiplier p, their size is at least log p. Thus the previously
proved uniform logarithmic upper bound has the correct order of magnitude.
This is not a proof or disproof of the natural-density conjecture. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

noncomputable def maxPrimeHarmonicDefect (k : ℕ) : ℝ :=
  ∑' n, ‖labelDilationDefect k Nat.maxPrimeFac n/(n : ℝ)‖

lemma mem_smoothNumbers_iff_maxPrimeFac_lt (B n : ℕ) (hB : 1<B) :
    n ∈ B.smoothNumbers ↔ n≠0 ∧ Nat.maxPrimeFac n<B := by
  constructor
  · intro hn
    refine ⟨hn.1,?_⟩
    by_cases hn1 : n=1
    · simpa only [hn1,Nat.maxPrimeFac_one] using hB
    · exact Nat.mem_smoothNumbers'.mp hn (Nat.maxPrimeFac n)
        (Nat.prime_maxPrimeFac_of_one_lt n (by have := hn.1; omega)) Nat.maxPrimeFac_dvd
  · rintro ⟨hn,hp⟩
    apply Nat.mem_smoothNumbers'.mpr
    intro p hprime hpn
    exact (Nat.le_maxPrimeFac hn hprime hpn).trans_lt hp

/-- The exceptional set for a multiplier k>1 is exactly the integers whose
largest prime factor is strictly smaller than P(k). -/
lemma maxPrimeFac_harmonic_defect_eq_smooth (k n : ℕ) (hk : 1<k) :
    ‖labelDilationDefect k Nat.maxPrimeFac n/(n : ℝ)‖ =
      smoothReciprocal (Nat.maxPrimeFac k-1) n := by
  classical
  have hp : 1<Nat.maxPrimeFac k := (Nat.one_lt_maxPrimeFac_iff k).mpr hk
  have he : Nat.maxPrimeFac k-1+1=Nat.maxPrimeFac k := by omega
  by_cases hn : n=0
  · subst n
    simp [smoothReciprocal]
  simp only [smoothReciprocal,he,mem_smoothNumbers_iff_maxPrimeFac_lt _ _ hp]
  unfold labelDilationDefect
  rw [Nat.maxPrimeFac_mul (by omega) hn]
  by_cases hpn : Nat.maxPrimeFac n<Nat.maxPrimeFac k
  · have hne : Nat.maxPrimeFac k≠Nat.maxPrimeFac n := by omega
    simp only [max_eq_left hpn.le,hne,ne_eq,not_false_eq_true,if_true,hn,hpn,
      and_self,norm_div,Real.norm_natCast,norm_one]
  · have hle : Nat.maxPrimeFac k≤Nat.maxPrimeFac n := by omega
    simp [max_eq_right hle,hpn]

/-- An exact finite Euler product, not just a majorant. -/
theorem maxPrimeHarmonicDefect_eq_product (k : ℕ) (hk : 1<k) :
    maxPrimeHarmonicDefect k =
      ∏ p ∈ (Nat.maxPrimeFac k).primesBelow, (1-(p : ℝ)⁻¹)⁻¹ := by
  have hp : 1<Nat.maxPrimeFac k := (Nat.one_lt_maxPrimeFac_iff k).mpr hk
  unfold maxPrimeHarmonicDefect
  simp_rw [maxPrimeFac_harmonic_defect_eq_smooth k _ hk]
  rw [(smoothReciprocal_hasSum (Nat.maxPrimeFac k-1)).tsum_eq]
  congr 2
  omega

theorem log_maxPrimeFac_le_total_harmonic_defect (k : ℕ) (hk : 1<k) :
    Real.log (Nat.maxPrimeFac k) ≤ maxPrimeHarmonicDefect k := by
  have hp : 1<Nat.maxPrimeFac k := (Nat.one_lt_maxPrimeFac_iff k).mpr hk
  have he : Nat.maxPrimeFac k-1+1=Nat.maxPrimeFac k := by omega
  rw [maxPrimeHarmonicDefect_eq_product k hk]
  have h := (log_add_one_le_harmonic (Nat.maxPrimeFac k-1)).trans
    (harmonic_le_primeEulerProduct (Nat.maxPrimeFac k-1))
  simpa only [he] using h

/-- The natural size parameter is P(k), which can be much smaller than k. -/
theorem total_harmonic_defect_le_log_maxPrimeFac (k : ℕ) (hk : 1<k) :
    maxPrimeHarmonicDefect k ≤
      Real.exp 4 * (1+Real.log (Nat.maxPrimeFac k)/Real.log 2) := by
  rw [maxPrimeHarmonicDefect_eq_product k hk]
  exact primeEulerProduct_le_log _ ((Nat.one_lt_maxPrimeFac_iff k).mpr hk)

lemma prime_log_le_total_harmonic_defect (p : ℕ) (hp : p.Prime) :
    Real.log p ≤ maxPrimeHarmonicDefect p := by
  simpa only [hp.maxPrimeFac_eq_self] using log_maxPrimeFac_le_total_harmonic_defect p hp.one_lt

/-- In particular, the ratio of the total defect to log k does not tend to
zero. Prime multipliers obstruct any such uniform improvement. -/
theorem not_total_harmonic_defect_sublogarithmic :
    ¬Tendsto (fun k : ℕ => maxPrimeHarmonicDefect k/Real.log k) atTop (𝓝 0) := by
  intro h
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (h.eventually_lt_const (by norm_num : (0 : ℝ)<1))
  obtain ⟨p,hpK,hp⟩ := Nat.exists_infinite_primes K
  have hh := hK p hpK
  have hlog : 0<Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hle : 1 ≤ maxPrimeHarmonicDefect p/Real.log p :=
    (le_div_iff₀ hlog).mpr (by simpa using prime_log_le_total_harmonic_defect p hp)
  linarith

#print axioms maxPrimeHarmonicDefect_eq_product
#print axioms log_maxPrimeFac_le_total_harmonic_defect
#print axioms total_harmonic_defect_le_log_maxPrimeFac
#print axioms not_total_harmonic_defect_sublogarithmic
end Erdos371
