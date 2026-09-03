import Submission.PowerSeparatedVaughan

/-! The polynomial-cutoff Vaughan reduction for the actual signed prime
kernel. Proper prime powers have their previously proved summable error;
no assertion is made that the surviving long kernel has mean zero. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

theorem cutoffPrimeSkew_power_vaughan_error (N U V B C : ℕ) (P : Finset ℕ)
    (F : ℕ → ℕ) (a b u v : ℝ) (hN : 1 ≤ N)
    (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hUV : U*V ≤ C)
    (hB : 2 ≤ B) (hBC : B ≤ C)
    (hP : ∀ p ∈ P, p.Prime ∧ B<p)
    (hF : ∀ k ∈ Icc 1 (N/(C+1)), k*F k ≤ N) (hsize : N+1 ≤ B^2)
    (hcard : (P.card : ℝ) ≤ (N : ℝ)^a) (hC : (N : ℝ)^b ≤ C)
    (hU : (U : ℝ) ≤ (N : ℝ)^u) (hV : (V : ℝ) ≤ (N : ℝ)^v) :
    |(cutoffPrimeSkew P (Icc 1 (N/(C+1))) C F-
        vaughanLongKernel U V P (Icc 1 (N/(C+1))) C F)/N| ≤
      primePowerKernelTail C+12*(N : ℝ)^(-(b-a-u-v)) := by
  have hshort := mangoldtKernel_power_vaughan_error N U V C P F a b u v hN hU1 hV1 hUV
    (fun p hp => (hP p hp).1.pos) hcard hC hU hV
  have hprime := mangoldtCutoffSkew_prime_error P (Icc 1 (N/(C+1))) B C N F
    hB hBC hP (fun k hk => (mem_Icc.mp hk).1) hF hsize
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hsmall : |(cutoffPrimeSkew P (Icc 1 (N/(C+1))) C F-
      mangoldtCutoffSkew P (Icc 1 (N/(C+1))) C F)/N| ≤ primePowerKernelTail C := by
    rw [abs_div,abs_of_pos hNr,abs_sub_comm]
    apply (div_le_iff₀ hNr).mpr
    simpa only [mul_comm] using hprime
  have hsplit : (cutoffPrimeSkew P (Icc 1 (N/(C+1))) C F-
      vaughanLongKernel U V P (Icc 1 (N/(C+1))) C F)/N =
      (cutoffPrimeSkew P (Icc 1 (N/(C+1))) C F-
        mangoldtCutoffSkew P (Icc 1 (N/(C+1))) C F)/N+
      (mangoldtCutoffSkew P (Icc 1 (N/(C+1))) C F-
        vaughanLongKernel U V P (Icc 1 (N/(C+1))) C F)/N := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hsmall hshort)

/-- Above the square-root boundary, a fixed positive power separation of
prime ranges makes the prime kernel equal, up to o(N), to its long Vaughan
kernel with BOTH truncation levels equal to floor(N^γ). -/
theorem cutoffPrimeSkew_polynomial_vaughan_remainder_tendsto (a b γ : ℝ)
    (ha : 0 ≤ a) (hγ : 0 < γ) (hgap : a+2*γ < b)
    (B C : ℕ → ℕ) (P : ℕ → Finset ℕ) (F : ℕ → ℕ → ℕ)
    (harith : ∀ᶠ N : ℕ in atTop, 2 ≤ B N ∧ B N ≤ C N ∧ N+1 ≤ (B N)^2 ∧
      (∀ p ∈ P N, p.Prime ∧ B N<p) ∧
      (∀ k ∈ Icc 1 (N/(C N+1)), k*F N k ≤ N))
    (hsize : ∀ᶠ N : ℕ in atTop, (P N).card ≤ (N : ℝ)^a ∧ (N : ℝ)^b ≤ C N) :
    Tendsto (fun N => (cutoffPrimeSkew (P N) (Icc 1 (N/(C N+1))) (C N) (F N)-
      vaughanLongKernel (vaughanPowerCutoff γ N) (vaughanPowerCutoff γ N)
        (P N) (Icc 1 (N/(C N+1))) (C N) (F N))/N) atTop (𝓝 0) := by
  have hC : Tendsto (fun N => (C N : ℝ)) atTop atTop :=
    tendsto_atTop_mono' _ (hsize.mono (fun _ hn => hn.2))
      ((tendsto_rpow_atTop (by linarith : 0 < b)).comp tendsto_natCast_atTop_atTop)
  have hCN : Tendsto C atTop atTop := tendsto_natCast_atTop_iff.mp hC
  have hpow := ((tendsto_rpow_neg_atTop (by linarith : 0 < b-a-γ-γ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 12
  have ht := (primePowerKernelTail_tendsto.comp hCN).add hpow
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [harith,hsize,eventually_ge_atTop (1 : ℕ)] with N har hs hN
  have hT := vaughanPowerCutoff_pos γ hγ.le N hN
  rw [Real.norm_eq_abs]
  exact cutoffPrimeSkew_power_vaughan_error N _ _ (B N) (C N) (P N) (F N) a b γ γ
    hN hT hT (vaughanPowerCutoff_sq_le γ b (by linarith) N (C N) hN hs.2)
    har.1 har.2.1 har.2.2.2.1 har.2.2.2.2 har.2.2.1 hs.1 hs.2
    (vaughanPowerCutoff_le γ N) (vaughanPowerCutoff_le γ N)

#print axioms cutoffPrimeSkew_power_vaughan_error
#print axioms cutoffPrimeSkew_polynomial_vaughan_remainder_tendsto
end Erdos371
