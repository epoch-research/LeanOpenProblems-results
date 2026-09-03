import Submission.LocalUniformCRT
import Submission.LocalPowerPeaks

/-! Quantitative full-count peaks for even critical exponents. -/
namespace Erdos322Research.LocalEvenQuantitativePeaks
noncomputable section
open Finset LocalPeakCounting LocalPowerPeaks LocalUniformCRT
open scoped Classical
set_option maxHeartbeats 0
set_option Elab.async false

/-- A family with quadratic growth of log(count) versus linear growth of
log(log(target)). This is still weaker than every positive power of the target. -/
theorem quadratic_log_depth_family (k r : ℕ) (he : Even (k+2)) (hr : 1 ≤ r) :
    ∃ n : ℕ, 0 < n ∧ (base k)^(r*r) < Erdos322.representationCount (k+2) n ∧
      n ≤ (base k)^((base k)^(2*r+7)) := by
  obtain ⟨B,hB,hBbound,h⟩ := bounded_even_concentration k r he
  let A := base k
  let C := 2*(k+2)
  let d := C*A^(r+2)
  let q := B^((k+2)*d+1)
  let M := A^(r*r)
  have hA : 2*(k+2)+2 ≤ A := base_large k
  have hA1 : 1 ≤ A := by omega
  have hA0 : 0 < A := by omega
  have hC : 0 < C := by dsimp only [C]; omega
  have hq : 0 < q := pow_pos hB _
  have hM : 0 < M := pow_pos hA0 _
  have hqp : 0 < q^(k+1) := pow_pos hq _
  have hCp : 0 < C^r := pow_pos hC _
  have hlarge : k+3 < A^(2*r) := by
    exact (by omega : k+3 < A).trans_le (Nat.le_pow (by omega))
  have hdepth : C^r*A^(2*r)*M=d^r := by
    dsimp only [d,M]
    conv_rhs => rw [mul_pow,← pow_mul]
    rw [mul_assoc,← pow_add]
    congr 1
    ring
  have hsize : ((k+2)*q^(k+1)+1)*M < rootCount (k+2) q := by
    have hh : C^r*(((k+2)*q^(k+1)+1)*M) < C^r*rootCount (k+2) q := by
      calc
        C^r*(((k+2)*q^(k+1)+1)*M) ≤ C^r*((k+3)*q^(k+1)*M) := by
          gcongr
          nlinarith
        _ < C^r*(A^(2*r)*q^(k+1)*M) := by gcongr
        _ = d^r*q^(k+1) := by rw [← hdepth]; ring
        _ ≤ (d+1)^r*q^(k+1) := by gcongr; omega
        _ ≤ _ := h d
    exact Nat.lt_of_mul_lt_mul_left hh
  obtain ⟨n,hn,hpeak,hbound⟩ := peak_of_rootCount (k+2) q M (by omega) hq hM (by simpa using hsize)
  refine ⟨n,hn,hpeak,hbound.trans ?_⟩
  have hd : d ≤ A^(r+3) := by
    dsimp only [d]
    calc
      C*A^(r+2) ≤ A*A^(r+2) := Nat.mul_le_mul_right _ (by dsimp only [C]; omega)
      _ = A^(r+3) := by rw [← pow_succ']
  have hed : (k+2)*d+1 ≤ A^(r+5) := by
    have h0 : 1 ≤ A^(r+4) := one_le_pow₀ hA1
    calc
      (k+2)*d+1 ≤ A*A^(r+3)+1 := by gcongr; omega
      _ = A^(r+4)+1 := by rw [← pow_succ']
      _ ≤ 2*A^(r+4) := by omega
      _ ≤ A*A^(r+4) := Nat.mul_le_mul_right _ (by omega)
      _ = A^(r+5) := by rw [← pow_succ']
  have heq : ((k+2)*d+1)*(k+2) ≤ A^(r+6) := by
    calc
      ((k+2)*d+1)*(k+2) ≤ A^(r+5)*A := Nat.mul_le_mul hed (by omega)
      _ = A^(r+6) := by rw [← pow_succ]
  have hBB : B ≤ A^(A^r) := hBbound
  change (k+2)*q^(k+2) ≤ A^(A^(2*r+7))
  calc
    (k+2)*q^(k+2) ≤ A*(A^(A^r))^(A^(r+6)) := by
      dsimp only [q]
      rw [← pow_mul]
      apply Nat.mul_le_mul (by omega)
      exact (Nat.pow_le_pow_left hBB _).trans
        (Nat.pow_le_pow_right (one_le_pow₀ hA1) heq)
    _ = A^(1+A^(2*r+6)) := by
      rw [← pow_mul,← pow_add,show r+(r+6)=2*r+6 by omega,← pow_succ']
      congr 1
      omega
    _ ≤ A^(A^(2*r+7)) := by
      apply Nat.pow_le_pow_right hA1
      have hh : 1 ≤ A^(2*r+6) := one_le_pow₀ hA1
      calc
        1+A^(2*r+6) ≤ 2*A^(2*r+6) := by omega
        _ ≤ A*A^(2*r+6) := Nat.mul_le_mul_right _ (by omega)
        _ = A^(2*r+7) := by rw [← pow_succ']


/-- The exact critical count for every even exponent has peaks exceeding
exp(c (log log n)^2), for a positive c depending on the exponent. -/
theorem exp_loglog_square_peaks_aux (k : ℕ) (he : Even (k+2)) :
    ∃ c > (0 : ℝ),
      {n : ℕ | Real.exp (c*(Real.log (Real.log (n : ℝ)))^2) <
        Erdos322.representationCount (k+2) n}.Infinite := by
  let A := base k
  let L := Real.log (A : ℝ)
  let c : ℝ := 1/(100*L)
  have hA : 2*(k+2)+2 ≤ A := base_large k
  have hA1 : 1 < A := by omega
  have hAr : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hA1)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hpeak (r n : ℕ) (hr : 1 ≤ r) (hn : 0 < n)
      (hlogn : 1 ≤ Real.log (n : ℝ))
      (hcount : A^(r*r) < Erdos322.representationCount (k+2) n)
      (hbound : n ≤ A^(A^(2*r+7))) :
      Real.exp (c*(Real.log (Real.log (n : ℝ)))^2) <
        Erdos322.representationCount (k+2) n := by
    have hlog : Real.log (n : ℝ) ≤ (A : ℝ)^(2*r+7)*L := by
      calc
        Real.log (n : ℝ) ≤ Real.log ((A : ℝ)^(A^(2*r+7))) := by
          apply Real.log_le_log (by exact_mod_cast hn)
          exact_mod_cast hbound
        _ = (A : ℝ)^(2*r+7)*L := by rw [Real.log_pow,Nat.cast_pow]
    have hloglog : Real.log (Real.log (n : ℝ)) ≤ (10*(r : ℝ))*L := by
      calc
        Real.log (Real.log (n : ℝ)) ≤ Real.log ((A : ℝ)^(2*r+7)*L) :=
          Real.log_le_log (by linarith) hlog
        _ = (2*(r : ℝ)+7)*L+Real.log L := by
          rw [Real.log_mul (pow_ne_zero _ hAr.ne') hL.ne',Real.log_pow]
          push_cast
          rfl
        _ ≤ (2*(r : ℝ)+8)*L := by
          have hh := Real.log_le_sub_one_of_pos hL
          nlinarith
        _ ≤ (10*(r : ℝ))*L := by
          have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr
          gcongr
          linarith
    have hll0 : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg hlogn
    have hc_bound : c*(Real.log (Real.log (n : ℝ)))^2 ≤ ((r*r : ℕ) : ℝ)*L := by
      calc
        c*(Real.log (Real.log (n : ℝ)))^2 ≤ c*((10*(r : ℝ))*L)^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hll0 hloglog 2) hc.le
        _ = ((r*r : ℕ) : ℝ)*L := by
          dsimp only [c]
          push_cast
          field_simp
          ring
    calc
      Real.exp (c*(Real.log (Real.log (n : ℝ)))^2) ≤ Real.exp (((r*r : ℕ) : ℝ)*L) :=
        Real.exp_le_exp.mpr hc_bound
      _ = (A : ℝ)^(r*r) := by rw [Real.exp_nat_mul,Real.exp_log hAr]
      _ < _ := by exact_mod_cast hcount
  refine ⟨c,hc,?_⟩
  have ht : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop 1)
  by_contra hfin
  have hf := Set.not_infinite.mp hfin
  have hbad := hf.union (Set.finite_Iio N)
  obtain ⟨M,hM⟩ := (hbad.image (Erdos322.representationCount (k+2))).bddAbove
  obtain ⟨n,hn,hcount,hbound⟩ := quadratic_log_depth_family k (M+1) he (by omega)
  change A^((M+1)*(M+1)) < Erdos322.representationCount (k+2) n at hcount
  have hpower : M < A^((M+1)*(M+1)) := by
    have hh : M+1 < A^(M+1) := Nat.lt_pow_self hA1
    apply (by omega : M < M+1).trans (hh.trans_le ?_)
    apply Nat.pow_le_pow_right hA1.le
    nlinarith
  have hnN : N ≤ n := by
    by_contra hnN
    have hh : Erdos322.representationCount (k+2) n ≤ M :=
      hM ⟨n,Or.inr (by simpa only [Set.mem_Iio] using (show n < N by omega)),rfl⟩
    omega
  have hm : Erdos322.representationCount (k+2) n ≤ M :=
    hM ⟨n,Or.inl (hpeak (M+1) n (by omega) hn (hN n hnN) hcount hbound),rfl⟩
  omega

/-- Quantitative superlogarithmic peaks for all even critical exponents. -/
theorem exp_loglog_square_peaks (k : ℕ) (hk : 2 ≤ k) (he : Even k) :
    ∃ c > (0 : ℝ),
      {n : ℕ | Real.exp (c*(Real.log (Real.log (n : ℝ)))^2) <
        Erdos322.representationCount k n}.Infinite := by
  obtain ⟨s,hs⟩ := Nat.exists_eq_add_of_le hk
  have hh : k=s+2 := by omega
  rw [hh] at he ⊢
  exact exp_loglog_square_peaks_aux s he

end
end Erdos322Research.LocalEvenQuantitativePeaks
