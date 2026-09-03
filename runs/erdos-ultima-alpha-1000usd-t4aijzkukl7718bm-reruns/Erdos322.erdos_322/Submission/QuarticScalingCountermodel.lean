import Submission.DivisorBound
import Submission.GrowthReduction

/-! A subpolynomial sequence with stronger strict scaling than the available
quartic count comparisons. This is a countermodel to a proposed inference,
not a counterexample to the representation-count conjecture. -/

namespace Erdos322Research.QuarticScalingCountermodel

/-- Divisors supported away from the two exceptional primes. -/
def divisorsAway (n : ℕ) : Finset ℕ := n.divisors.filter (fun d ↦ d.Coprime 10)

def modelCount (n : ℕ) : ℕ := (divisorsAway n).card

private theorem mem_divisorsAway (n d : ℕ) :
    d ∈ divisorsAway n ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime 10 := by
  simp only [divisorsAway, Finset.mem_filter, Nat.mem_divisors, and_assoc]

private theorem subset_scale (m n : ℕ) (hm : 0 < m) :
    divisorsAway n ⊆ divisorsAway (m^4*n) := by
  intro d hd
  obtain ⟨hd,hn,hc⟩ := (mem_divisorsAway n d).mp hd
  exact (mem_divisorsAway _ _).mpr
    ⟨dvd_mul_of_dvd_right hd _, mul_ne_zero (pow_ne_zero _ hm.ne') hn, hc⟩

/-- The model is monotone under every positive fourth-power scaling. -/
theorem scale_mono (m n : ℕ) (hm : 0 < m) : modelCount n ≤ modelCount (m^4*n) :=
  Finset.card_le_card (subset_scale m n hm)

private theorem unchanged_of_dvd_ten (m n : ℕ) (hm : 0 < m) (h10 : m ∣ 10) :
    modelCount (m^4*n) = modelCount n := by
  unfold modelCount
  congr 1
  apply le_antisymm
  · intro d hd
    obtain ⟨hd,hn,hc⟩ := (mem_divisorsAway _ _).mp hd
    have hcm : d.Coprime (m^4) := (hc.of_dvd_right h10).pow_right 4
    exact (mem_divisorsAway _ _).mpr
      ⟨hcm.dvd_of_dvd_mul_left hd, right_ne_zero_of_mul hn, hc⟩
  · exact subset_scale m n hm

/-- Scaling by 2 preserves every model count. -/
theorem scale_two (n : ℕ) : modelCount (2^4*n) = modelCount n :=
  unchanged_of_dvd_ten 2 n (by decide) (by decide)

/-- Scaling by 5 preserves every model count. -/
theorem scale_five (n : ℕ) : modelCount (5^4*n) = modelCount n :=
  unchanged_of_dvd_ten 5 n (by decide) (by decide)

/-- In contrast to the presently proved representation-count comparison,
strictness in this subpolynomial model holds at EVERY positive target. -/
theorem scale_prime_strict (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hn : 0 < n) : modelCount n < modelCount (p^4*n) := by
  have hc : p.Coprime 10 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have he : p ∣ 2*5 := hd
    rcases hp.dvd_mul.mp he with he | he
    · exact hp2 ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp he |>.resolve_left hp.ne_one)
    · exact hp5 ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp he |>.resolve_left hp.ne_one)
  let d := p^(n.factorization p+1)
  have hdnot : d ∉ divisorsAway n := by
    intro hd
    exact Nat.pow_succ_factorization_not_dvd hn.ne' hp ((mem_divisorsAway _ _).mp hd).1
  have hdyes : d ∈ divisorsAway (p^4*n) := by
    apply (mem_divisorsAway _ _).mpr
    refine ⟨?_, mul_ne_zero (pow_ne_zero _ hp.ne_zero) hn.ne', hc.pow_left _⟩
    have he : p^(n.factorization p)*p ∣ n*p^4 :=
      mul_dvd_mul (Nat.ordProj_dvd n p) (dvd_pow_self p (by decide : 4 ≠ 0))
    change p^(n.factorization p+1) ∣ p^4*n
    rw [pow_succ, mul_comm (p^4) n]
    exact he
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_scale p n hp.pos, ?_⟩
  intro he
  exact hdnot (he.symm ▸ hdyes)

/-- Despite that strong scaling growth, the model has no polynomial peaks. -/
theorem no_polynomial_peaks :
    ¬ ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (modelCount n : ℝ)}.Infinite := by
  apply (no_polynomial_peaks_iff_uniform_bound modelCount).mpr
  intro ε hε
  obtain ⟨C,hC,he⟩ := divisor_count_subpolynomial ε hε
  refine ⟨C,hC,fun n hn ↦ ?_⟩
  have hle : modelCount n ≤ n.divisors.card := Finset.card_filter_le _ _
  exact (Nat.cast_le.mpr hle).trans (he n (by omega))

/-- The model is unbounded even along a single fourth-power scaling chain. -/
theorem chain_lower (j : ℕ) : j+1 ≤ modelCount (3^(4*j)) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have hs := scale_prime_strict 3 (3^(4*j)) (by decide) (by decide) (by decide)
      (pow_pos (by decide : 0 < 3) _)
    have he : 3^4*3^(4*j) = 3^(4*(j+1)) := by rw [← pow_add]; congr 1; omega
    rw [he] at hs
    omega

end Erdos322Research.QuarticScalingCountermodel
