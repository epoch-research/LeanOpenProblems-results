import Submission.LocalSharpAPDensity
import Submission.LocalPowerPeaks
import Submission.APPrimeProductsSharp

/-! Sharper divisor-scale peaks for every critical exponent. The exponent on
n is still c/log(log n), not a fixed positive constant. -/
namespace Erdos322Research.LocalSharpDivisorPeaks
noncomputable section
open Finset Filter LocalPeakCounting LocalPowerPeaks LocalSharpAPDensity APPrimeProducts
open scoped Classical Topology
set_option Elab.async false
set_option maxHeartbeats 0

/-- A real lower density gives an exact-count peak after a harmless factor two. -/
theorem peak_of_prime_set (k M : ℕ) (hM : 1 ≤ M) (b : ℝ) (hb : 1 < b)
    (hMb : (M : ℝ)*b ≤ ((2*M-1 : ℕ) : ℝ)) (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime)
    (hd : ∀ p ∈ S, (2*M-1)*(p^(k+2))^(k+1) ≤ M*rootCount (k+2) (p^(k+2)))
    (hX : 1 ≤ b^S.card/(2*(k+3 : ℕ))) :
    ∃ n : ℕ, 0 < n ∧ b^S.card/(2*(k+3 : ℕ)) < Erdos322.representationCount (k+2) n ∧
      n ≤ (k+2)*(∏ p ∈ S,p)^((k+2)^2) := by
  let r := S.card
  let P := ∏ p ∈ S,p
  let q := P^(k+2)
  let X : ℝ := b^r/(2*(k+3 : ℕ))
  let m := ⌊X⌋₊
  have hP : 0 < P := prod_pos fun p hpS ↦ (hp p hpS).pos
  have hq : 0 < q := pow_pos hP _
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hbr : 0 < b^r := pow_pos (by linarith) _
  have hqp : (0 : ℝ) < (q : ℝ)^(k+1) := pow_pos (by exact_mod_cast hq) _
  have hqone : (1 : ℝ) ≤ (q : ℝ)^(k+1) := by exact_mod_cast one_le_pow₀ (show 1 ≤ q by omega)
  have hdens : b^r*(q : ℝ)^(k+1) ≤ rootCount (k+2) q := by
    have hh := product_density k M S hp hd
    change (2*M-1)^r*q^(k+1) ≤ M^r*rootCount (k+2) q at hh
    apply le_of_mul_le_mul_left (a := (M : ℝ)^r) ?_ (pow_pos hMr _)
    calc
      (M : ℝ)^r*(b^r*(q : ℝ)^(k+1)) = ((M : ℝ)*b)^r*(q : ℝ)^(k+1) := by
        rw [mul_pow]; ring
      _ ≤ (((2*M-1 : ℕ) : ℝ)^r)*(q : ℝ)^(k+1) := by gcongr
      _ ≤ (M : ℝ)^r*rootCount (k+2) q := by exact_mod_cast hh
  have hm : 1 ≤ m := Nat.le_floor (by simpa only [X,r,Nat.cast_one] using hX)
  have hf : (m : ℝ) ≤ X := Nat.floor_le (by change 0 ≤ X; linarith [hX])
  have hXe : (2*(k+3 : ℕ) : ℝ)*X=b^r := by
    dsimp [X]
    field_simp
  have hsize : ((k+2)*q^(k+1)+1)*m < rootCount (k+2) q := by
    have hcoef : (k+2 : ℕ)*(q : ℝ)^(k+1)+1 ≤ (k+3 : ℕ)*(q : ℝ)^(k+1) := by
      push_cast
      nlinarith
    have hh := mul_le_mul hcoef hf (Nat.cast_nonneg m) (by positivity)
    have hXnonneg : 0 ≤ X := by linarith [hX]
    have hmain : (((k+2 : ℕ)*(q : ℝ)^(k+1)+1)*(m : ℝ)) < rootCount (k+2) q := by
      have he : (k+3 : ℕ)*(q : ℝ)^(k+1)*X = b^r*(q : ℝ)^(k+1)/2 := by
        nlinarith [congrArg (fun z : ℝ ↦ z*(q : ℝ)^(k+1)) hXe]
      rw [he] at hh
      have hpos := mul_pos hbr hqp
      linarith
    exact_mod_cast hmain
  obtain ⟨n,hn,hcount,hheight⟩ := peak_of_rootCount (k+2) q m (by omega) hq hm hsize
  refine ⟨n,hn,?_,?_⟩
  · have hfloor : X < (m : ℝ)+1 := Nat.lt_floor_add_one X
    have hh : (m : ℝ)+1 ≤ Erdos322.representationCount (k+2) n := by
      exact_mod_cast (show m+1 ≤ Erdos322.representationCount (k+2) n by omega)
    exact hfloor.trans_le hh
  · simpa only [q,← pow_mul,← pow_two] using hheight

private lemma logarithmic_height_bound (A : ℝ) (r n : ℕ) (hA : 1 ≤ A)
    (hr : 0 < r) (hlog : 1 ≤ Real.log (Real.log (n : ℝ)))
    (hheight : Real.log (n : ℝ) ≤ A*r*Real.log (r : ℝ)) :
    Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)) ≤ A*r := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hLpos : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  apply (div_le_iff₀ hLpos).mpr
  by_cases hsmall : Real.log (n : ℝ) ≤ r
  · have hscale : (r : ℝ) ≤ A*r := by nlinarith
    have hprod : A*r ≤ (A*r)*Real.log (Real.log (n : ℝ)) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ A) hrp.le]
    exact hsmall.trans (hscale.trans hprod)
  · have hrl : Real.log (r : ℝ) ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_le_log hrp (le_of_not_ge hsmall)
    exact hheight.trans (mul_le_mul_of_nonneg_left hrl (by positivity))

/-- Every positive constant smaller than log(2)/K^2 is available in the
universal divisor-scale lower bound. This is NOT a fixed-power peak theorem. -/
theorem exp_log_div_loglog_peaks_aux (k : ℕ) (c : ℝ) (hc : 0 < c)
    (hclim : c < Real.log 2/((k+2 : ℕ) : ℝ)^2) :
    {n : ℕ | Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
      Erdos322.representationCount (k+2) n}.Infinite := by
  let K : ℝ := k+2
  have hK : 2 ≤ K := by dsimp [K]; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hK0 : 0 < K := by linarith
  have hK2 : 0 < K^2 := sq_pos_of_pos hK0
  have hratio : K^2 < Real.log 2/c := by
    apply (lt_div_iff₀ hc).mpr
    have hcK : c < Real.log 2/K^2 := by simpa [K] using hclim
    have hh := (lt_div_iff₀ hK2).mp hcK
    nlinarith
  obtain ⟨A,hAK,hAlim⟩ := exists_between hratio
  have hA : 1 < A := by nlinarith
  have hcA : c*A < Real.log 2 := by
    have hh := (lt_div_iff₀ hc).mp hAlim
    nlinarith
  obtain ⟨α,hα,hαA⟩ := exists_between (show (1 : ℝ) < A/K^2 by exact (lt_div_iff₀ hK2).mpr (by simpa using hAK))
  have hδ : 0 < A-α*K^2 := by
    have hh := (lt_div_iff₀ hK2).mp hαA
    linarith
  have heb : Real.exp (c*A) < 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_lt_exp.mpr hcA
  obtain ⟨b,hbexp,hb2⟩ := exists_between heb
  have hb : 1 < b := (Real.one_lt_exp_iff.mpr (mul_pos hc (by linarith))).trans hbexp
  have hb0 : 0 < b := by linarith
  have hgap : 0 < Real.log b-c*A := by
    have hh := Real.log_lt_log (Real.exp_pos _) hbexp
    rw [Real.log_exp] at hh
    linarith
  obtain ⟨M,hMbig⟩ := exists_nat_gt (max 2 (1/(2-b)))
  have hM2 : (2 : ℝ) < M := (le_max_left _ _).trans_lt hMbig
  have hM : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
  have hMb : (M : ℝ)*b ≤ ((2*M-1 : ℕ) : ℝ) := by
    have hh : 1/(2-b) < (M : ℝ) := (le_max_right _ _).trans_lt hMbig
    have hh' := (div_lt_iff₀ (by linarith : 0 < 2-b)).mp hh
    rw [Nat.cast_sub (by omega : 1 ≤ 2*M)]
    push_cast
    nlinarith
  obtain ⟨q,hq,a,ha,hgood⟩ := exists_density_progression k M hM
  letI : NeZero q := hq
  have hlogr : ∀ᶠ r : ℕ in atTop, 1 ≤ Real.log (r : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hδr : ∀ᶠ r : ℕ in atTop, Real.log K/(A-α*K^2) ≤ (r : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hgr : ∀ᶠ r : ℕ in atTop, Real.log (2*(K+1))/(Real.log b-c*A) < (r : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  have ht : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  apply Set.infinite_of_forall_exists_gt
  intro bound
  let T := max N (bound+1)
  let D := (range T).sup (Erdos322.representationCount (k+2))
  have hpow : Tendsto (fun r : ℕ ↦ b^r/(2*(K+1))) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hb).atTop_div_const (by positivity)
  obtain ⟨R,hR⟩ := eventually_atTop.mp
    (hlogr.and (hδr.and (hgr.and (hpow.eventually_gt_atTop ((D : ℝ)+1)))))
  obtain ⟨S,hRS,hS,hp,hP⟩ := APPrimeProductsSharp.exists_prime_set_small_product a ha α hα R
  let r := S.card
  let P := ∏ p ∈ S,p
  obtain ⟨hlogr,hδr,hgr,hcountD⟩ := hR r hRS
  have hX : 1 ≤ b^S.card/(2*(k+3 : ℕ)) := by
    have hK' : (k+3 : ℕ)=K+1 := by dsimp [K]; push_cast; ring
    rw [hK']
    change 1 ≤ b^r/(2*(K+1))
    linarith [Nat.cast_nonneg (α := ℝ) D]
  obtain ⟨n,hn,hcount,hheight⟩ := peak_of_prime_set k M hM b hb hMb S
    (fun p hpS ↦ (hp p hpS).1) (fun p hpS ↦ hgood p (hp p hpS)) hX
  have hK' : ((k+2 : ℕ) : ℝ)=K := by dsimp [K]; push_cast; rfl
  have hK'' : ((k+3 : ℕ) : ℝ)=K+1 := by dsimp [K]; push_cast; ring
  change b^r/(2*(k+3 : ℕ)) < Erdos322.representationCount (k+2) n at hcount
  rw [hK''] at hcount
  have hnT : T ≤ n := by
    by_contra hh
    have hnmem : n ∈ range T := mem_range.mpr (by omega)
    have hbd : Erdos322.representationCount (k+2) n ≤ D := le_sup hnmem
    have hbd' : (Erdos322.representationCount (k+2) n : ℝ) ≤ D := by exact_mod_cast hbd
    linarith
  have hnlog : 1 ≤ Real.log (Real.log (n : ℝ)) := hN n ((le_max_left _ _).trans hnT)
  have hrp : (0 : ℝ) < r := by exact_mod_cast hS
  have hPpos : 0 < P := prod_pos fun p hpS ↦ (hp p hpS).1.pos
  have hPp : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogP : Real.log (P : ℝ) ≤ (α*r)*Real.log (r : ℝ) := by
    have hh := Real.log_le_log hPp hP
    change Real.log (P : ℝ) ≤ Real.log ((r : ℝ)^(α*r)) at hh
    rwa [Real.log_rpow hrp] at hh
  have hheight' : Real.log (n : ℝ) ≤ A*r*Real.log (r : ℝ) := by
    have hh := Real.log_le_log hnp (show (n : ℝ) ≤ K*(P : ℝ)^((k+2)^2) by
      rw [← hK']; exact_mod_cast hheight)
    rw [Real.log_mul hK0.ne' (pow_ne_zero _ hPp.ne'),Real.log_pow] at hh
    have hKsq : (((k+2)^2 : ℕ) : ℝ)=K^2 := by push_cast; rfl
    rw [hKsq] at hh
    have hδr' := (div_le_iff₀ hδ).mp hδr
    have hδprod : (A-α*K^2)*(r : ℝ) ≤ (A-α*K^2)*r*Real.log (r : ℝ) :=
      le_mul_of_one_le_right (mul_nonneg hδ.le hrp.le) hlogr
    nlinarith
  have hbound := logarithmic_height_bound A r n hA.le hS hnlog hheight'
  have hgr' := (div_lt_iff₀ hgap).mp hgr
  have hexp : Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
      b^r/(2*(K+1)) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2*(K+1))).mpr
    calc
      _ ≤ Real.exp (c*(A*r))*(2*(K+1)) := by
        gcongr
      _ = Real.exp (Real.log (2*(K+1))+c*(A*r)) := by
        rw [Real.exp_add,Real.exp_log (by positivity)]
        ring
      _ < Real.exp ((r : ℝ)*Real.log b) := by
        apply Real.exp_lt_exp.mpr
        nlinarith
      _ = b^r := by rw [Real.exp_nat_mul,Real.exp_log hb0]
  exact ⟨n,hexp.trans hcount,by have := le_max_right N (bound+1); omega⟩

/-- The improved universal lower bound, using the actual power exponent. -/
theorem exp_log_div_loglog_peaks (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc : 0 < c)
    (hclim : c < Real.log 2/(k : ℝ)^2) :
    {n : ℕ | Real.exp (c*(Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
      Erdos322.representationCount k n}.Infinite := by
  obtain ⟨s,hs⟩ := Nat.exists_eq_add_of_le hk
  have he : k=s+2 := by omega
  rw [he] at hclim ⊢
  exact exp_log_div_loglog_peaks_aux s c hc hclim

end
end Erdos322Research.LocalSharpDivisorPeaks
