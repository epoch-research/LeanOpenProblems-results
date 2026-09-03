import Submission.LocalPowerPeaks
import Submission.LocalCRTConcentration

/-! Full critical power-sum counts have arbitrarily high logarithmic peaks.
This still does not prove positive powers of the target. -/
namespace Erdos322Research.LocalSuperlogPeaks
noncomputable section
open Finset LocalPeakCounting LocalPowerPeaks LocalCRTConcentration
set_option maxHeartbeats 0

/-- An exact peak family of any prescribed polynomial order in its depth,
with targets at most exponential in that depth. -/
theorem polynomial_depth_family (k r : ℕ) :
    ∃ C : ℕ, 1 < C ∧ ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∃ n : ℕ,
      0 < n ∧ (d+1)^(r+1) < Erdos322.representationCount (k+2) n ∧ n ≤ C^(d+1) := by
  obtain ⟨B,hB,h⟩ := arbitrary_order_concentration k (r+1)
  let C := (k+2)*B^((k+2)*(k+3))
  let D := (k+2)*B^(k+1)+1
  have hC : 1 < C := by
    have hh : 1 ≤ B^((k+2)*(k+3)) := one_le_pow₀ hB.le
    dsimp only [C]
    nlinarith
  refine ⟨C,hC,D,?_⟩
  intro d hd
  let q := B^((k+2)*d+1)
  let A := B^((k+2)*d*(k+1))
  let M := (d+1)^(r+1)
  have hq : 0 < q := pow_pos (by omega : 0 < B) _
  have hA : 0 < A := pow_pos (by omega : 0 < B) _
  have hM : 0 < M := pow_pos (by omega) _
  have hqpow : q^(k+1)=B^(k+1)*A := by
    dsimp only [q,A]
    rw [← pow_mul,show ((k+2)*d+1)*(k+1)=(k+1)+(k+2)*d*(k+1) by ring,pow_add]
  have hcount := h d
  change (d+1)^(r+1+1)*A ≤ rootCount (k+2) q at hcount
  have hsize : ((k+2)*q^(k+1)+1)*M < rootCount (k+2) q := by
    calc
      ((k+2)*q^(k+1)+1)*M ≤ (D*A)*M := by
        apply Nat.mul_le_mul_right M
        rw [hqpow]
        dsimp only [D]
        nlinarith
      _ < ((d+1)*A)*M :=
        Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right (by omega : D < d+1) hA) hM
      _ = (d+1)^(r+1+1)*A := by dsimp only [M]; rw [pow_succ]; ring
      _ ≤ _ := hcount
  obtain ⟨n,hn,hpeak,hbound⟩ := peak_of_rootCount (k+2) q M (by omega) hq hM hsize
  refine ⟨n,hn,hpeak,hbound.trans ?_⟩
  dsimp only [q,C]
  rw [mul_pow,← pow_mul,← pow_mul]
  apply Nat.mul_le_mul
  · exact Nat.le_pow (by omega)
  · apply Nat.pow_le_pow_right hB.le
    nlinarith [Nat.zero_le ((k+2)*d)]

/-- For every critical exponent at least two and every positive integer m,
the full count exceeds a positive multiple of (log n)^m infinitely often. -/
theorem arbitrary_log_power_peaks (k : ℕ) (hk : 2 ≤ k) (r : ℕ) :
    ∃ c > (0 : ℝ),
      {n : ℕ | c*(Real.log (n : ℝ))^(r+1) < Erdos322.representationCount k n}.Infinite := by
  obtain ⟨s,hs⟩ := Nat.exists_eq_add_of_le hk
  have hks : k=s+2 := by omega
  obtain ⟨C,hC,D,h⟩ := polynomial_depth_family s r
  rw [← hks] at h
  have hlogC : 0 < Real.log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  let c : ℝ := 1/(2*(Real.log (C : ℝ))^(r+1))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hpeak (d n : ℕ) (hn : 0 < n)
      (hcount : (d+1)^(r+1) < Erdos322.representationCount k n) (hb : n ≤ C^(d+1)) :
      c*(Real.log (n : ℝ))^(r+1) < Erdos322.representationCount k n := by
    have hlog : Real.log (n : ℝ) ≤ (d+1)*Real.log (C : ℝ) := by
      calc
        Real.log (n : ℝ) ≤ Real.log ((C : ℝ)^(d+1)) := by
          apply Real.log_le_log (by exact_mod_cast hn)
          exact_mod_cast hb
        _ = (d+1)*Real.log (C : ℝ) := by rw [Real.log_pow]; push_cast; rfl
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hpow : (Real.log (n : ℝ))^(r+1) ≤
        ((d+1 : ℕ) : ℝ)^(r+1)*(Real.log (C : ℝ))^(r+1) := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ hlog0
      exact_mod_cast hlog
    have hcast : ((d+1 : ℕ) : ℝ)^(r+1) < Erdos322.representationCount k n := by
      exact_mod_cast hcount
    have hpos : 0 < (Real.log (C : ℝ))^(r+1) := pow_pos hlogC _
    have hnonneg : (0 : ℝ) ≤ Erdos322.representationCount k n := Nat.cast_nonneg _
    dsimp only [c]
    rw [one_div_mul_eq_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2*(Real.log (C : ℝ))^(r+1))).mpr
    nlinarith
  refine ⟨c,hc,?_⟩
  by_contra hfin
  have hf : {n : ℕ | c*(Real.log (n : ℝ))^(r+1) < Erdos322.representationCount k n}.Finite :=
    Set.not_infinite.mp hfin
  obtain ⟨M,hM⟩ := (hf.image (Erdos322.representationCount k)).bddAbove
  obtain ⟨n,hn,hcount,hb⟩ := h (D+M+1) (by omega)
  have hm : Erdos322.representationCount k n ≤ M :=
    hM ⟨n,hpeak (D+M+1) n hn hcount hb,rfl⟩
  have hpow : D+M+1+1 ≤ (D+M+1+1)^(r+1) := Nat.le_pow (by omega)
  omega


/-- Every fixed logarithmic power, with every fixed positive multiplier,
is exceeded infinitely often. The exponent on n in Erdos 322 is still not obtained. -/
theorem exceeds_every_log_power (k : ℕ) (hk : 2 ≤ k) (r : ℕ) (A : ℝ) :
    {n : ℕ | A*(Real.log (n : ℝ))^r < Erdos322.representationCount k n}.Infinite := by
  obtain ⟨c,hc,hS⟩ := arbitrary_log_power_peaks k hk r
  have ht : Filter.Tendsto (fun n : ℕ ↦ c*Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp
    ((ht.eventually_ge_atTop A).and (Filter.eventually_ge_atTop (1 : ℕ)))
  apply (hS.diff (Set.finite_Iio N)).mono
  intro n hn
  have hnN : N ≤ n := by simpa only [Set.mem_Iio,not_lt] using hn.2
  obtain ⟨hlog,hn1⟩ := hN n hnN
  have hnonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  change A*(Real.log (n : ℝ))^r < _
  calc
    A*(Real.log (n : ℝ))^r ≤ (c*Real.log (n : ℝ))*(Real.log (n : ℝ))^r := by
      exact mul_le_mul_of_nonneg_right hlog (pow_nonneg hnonneg _)
    _ = c*(Real.log (n : ℝ))^(r+1) := by rw [pow_succ]; ring
    _ < _ := hn.1

end
end Erdos322Research.LocalSuperlogPeaks
