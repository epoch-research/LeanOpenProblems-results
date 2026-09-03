import FormalConjecturesUtil
import Submission.NearFullPenaltyWitnesses
import Submission.SharpNumericPenaltySelection

/-! Near-full degree-penalized witnesses with a lower-degree coefficient
arbitrarily close to c*α. This is not a rationality theorem. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713SharpPenaltyWitnesses
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713Cloning
open Erdos713CloneResistance Erdos713NearFullPenaltyWitnesses
variable {W : Type*}
set_option maxHeartbeats 2000000

theorem near_full_sharp_controlled [Fintype W] (H : SimpleGraph W) (hH : H.IsBipartite)
    (hEdge : ∃ v w, H.Adj v w) {α c : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ a : ℝ, 0 < a → a < c*α →
      ∀ ε : ℝ, 0 < ε →
      ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        L ≤ n ∧ H.Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
        (∀ v, a*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
        κ*(n : ℝ)^α ≤ (∑ v, if SingleFold H G v then degreeR G v else 0) ∧
        ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ GlobalOptimal H G lam mu ∧
          κ*(n : ℝ)^α ≤ netBudget G lam mu ∧
          lam*energy G ≤ 7*ε*(n : ℝ)^α ∧
          a*(n : ℝ)^(α-1) ≤ mu*(2*n-1) := by
  classical
  let C := c*α/2
  let M := c*(1-α/2)
  have ha0 : 0 < α := by linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hM : 0 < M := mul_pos hc (by linarith)
  have hCM : C+M=c := by dsimp [C,M]; ring
  have hz : Tendsto (fun n : ℕ => (extremalNumber n H : ℝ)/(n : ℝ)^2) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using Erdos713FutureRecords.higher_ratio_zero ha2 h
  obtain ⟨a0,_,hBaseline⟩ := Erdos713NearOptimalExpanders.near_full_density H hH hEdge ha ha2 hc h
  refine ⟨M/4,by positivity,?_⟩
  intro a haLower haSlope ε hε
  obtain ⟨η,hη,hη1,hηc,hηM,hηε,hNumeric⟩ :=
    Erdos713SharpNumericPenaltySelection.selection_errors_sharp ha ha2 hc hε haSlope
  obtain ⟨D,hD,hBase⟩ := hBaseline η hη hηc
  obtain ⟨B,hB,hEnvelope⟩ := global_upper_envelope H hc hη h
  let A := η/(2*D*(c+1))
  have hA : 0 < A := by dsimp [A]; positivity
  have hLargePower : Tendsto (fun k : ℕ => η*(k : ℝ)^α) atTop atTop :=
    ((tendsto_rpow_atTop ha0).comp tendsto_natCast_atTop_atTop).const_mul_atTop hη
  have hSmallPenalty : Tendsto (fun k : ℕ => A*(k : ℝ)^(-(α-1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_rpow_neg_atTop (show 0 < α-1 by linarith)).comp
        tendsto_natCast_atTop_atTop).const_mul A
  have hLargeOrder : Tendsto (fun k : ℕ => η*(k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hη
  have hevent : ∀ᶠ k : ℕ in atTop,
      B ≤ η*(k : ℝ)^α ∧ A*(k : ℝ)^(-(α-1)) ≤ η/(10*(c+1)) ∧ 2*C ≤ η*k :=
    (hLargePower.eventually_ge_atTop B).and
      ((hSmallPenalty.eventually_le_const (by positivity)).and (hLargeOrder.eventually_ge_atTop (2*C)))
  obtain ⟨K0,hK0⟩ := eventually_atTop.mp hevent
  refine ⟨2/A,by positivity,?_⟩
  intro L
  obtain ⟨U,instU,K,hBig,hTwo,hFree,hDenseK,hDegK,_⟩ := hBase (max K0 (2*L+2))
  let N := Fintype.card U
  have hNK : K0 ≤ N := (le_max_left _ _).trans hBig
  have hNL : 2*L+2 ≤ N := (le_max_right _ _).trans hBig
  have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hBsmall,hLamSmall,hCsmall⟩ := hK0 N hNK
  let P : ℝ := (N : ℝ)^α
  have hP : 0 < P := Real.rpow_pos_of_pos hN α
  let lam := A*(N : ℝ)^(-(α-1))
  let mu := C*(N : ℝ)^(α-2)
  have hlam : 0 < lam := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have hmu : 0 < mu := mul_pos hC (Real.rpow_pos_of_pos hN _)
  have hmuN : mu*(N : ℝ)^2=C*P := by
    dsimp [mu,P]
    rw [Real.rpow_sub hN,Real.rpow_two]
    field_simp
  have hmuN' : mu*(N : ℝ)=C*(N : ℝ)^(α-1) := by
    dsimp [mu]
    rw [show α-1=(α-2)+1 by ring,Real.rpow_add hN,Real.rpow_one]
    ring
  have hLamScale : lam*(2*D*(N : ℝ)^(α-1))=η/(c+1) := by
    dsimp [lam,A]
    rw [Real.rpow_neg hN.le]
    field_simp [(Real.rpow_pos_of_pos hN (α-1)).ne', hD.ne', (by positivity : c+1 ≠ 0)]
  have hEkUpper : edgesR K ≤ (c+1)*P := by
    have hh := card_edgeFinset_le_extremalNumber hFree
    have he : edgesR K ≤ (extremalNumber N H : ℝ) := by
      unfold edgesR
      exact_mod_cast (by simpa only [N,edgeFinset_card,Nat.card_eq_fintype_card] using hh)
    have hb := hEnvelope N
    change (extremalNumber N H : ℝ) ≤ (c+η)*P+B at hb
    change B ≤ η*P at hBsmall
    have herr := mul_le_mul_of_nonneg_right (show 2*η ≤ 1 by linarith) hP.le
    nlinarith only [he,hb,hBsmall,herr]
  have hEnergyK : lam*energy K ≤ η*P := by
    have hh := energy_le_max_degree K (D := D*(N : ℝ)^(α-1)) (fun v => (hDegK v).2)
    calc
      _ ≤ lam*(2*(D*(N : ℝ)^(α-1))*edgesR K) := mul_le_mul_of_nonneg_left hh hlam.le
      _ = (η/(c+1))*edgesR K := by rw [← hLamScale]; ring
      _ ≤ (η/(c+1))*((c+1)*P) := mul_le_mul_of_nonneg_left hEkUpper (by positivity)
      _ = η*P := by field_simp
  have hPotentialK : (M-2*η)*P ≤ potential lam mu K := by
    change (c-η)*P ≤ edgesR K at hDenseK
    unfold potential score
    change (M-2*η)*P ≤ edgesR K-lam*energy K-mu*(N : ℝ)^2
    rw [hmuN]
    rw [← hCM] at hDenseK
    nlinarith only [hDenseK,hEnergyK]
  have hMη : 0 < M-2*η := by change η ≤ M/20 at hηM; linarith
  have hPosK : 0 < potential lam mu K := (mul_pos hMη hP).trans_le hPotentialK
  obtain ⟨n,G,hG,hMax⟩ := exists_global_graph H (ne_bot_iff_exists_adj.mpr hEdge)
    hlam.le hmu hz K hFree hPosK
  have hPot : (M-2*η)*P ≤ edgesR G-lam*energy G-mu*(n : ℝ)^2 := by
    have hh := hPotentialK.trans hMax
    simpa only [potential,score,Fintype.card_fin] using hh
  let t : ℝ := (n : ℝ)/(N : ℝ)
  let e := edgesR G/P
  let p := lam*energy G/P
  have ht : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) hN.le
  have hp : 0 ≤ p := div_nonneg (mul_nonneg hlam.le (energy_nonneg G)) hP.le
  have hmuRatio : mu*(n : ℝ)^2/P=C*t^2 := by
    dsimp [mu,P,t]
    rw [Real.rpow_sub hN,Real.rpow_two]
    field_simp [(Real.rpow_pos_of_pos hN α).ne']
  have hPowerRatio : (n : ℝ)^α=t^α*P := by
    dsimp [t,P]
    rw [Real.div_rpow (Nat.cast_nonneg _) hN.le]
    exact (div_mul_cancel₀ _ (Real.rpow_pos_of_pos hN α).ne').symm
  have hNormPot : M-2*η ≤ e-p-C*t^2 := by
    dsimp only [e,p]
    rw [← hmuRatio,← sub_div,← sub_div]
    exact (le_div_iff₀ hP).mpr hPot
  have hEdgeUpper : edgesR G ≤ (c+η)*(n : ℝ)^α+η*P := by
    have he : edgesR G ≤ (extremalNumber n H : ℝ) := by
      have hh := card_edgeFinset_le_extremalNumber hG.free
      unfold edgesR
      exact_mod_cast (by simpa only [edgeFinset_card,Nat.card_eq_fintype_card,Fintype.card_fin] using hh)
    exact he.trans ((hEnvelope n).trans (add_le_add le_rfl hBsmall))
  have hNormUpper : e ≤ (c+η)*t^α+η := by
    dsimp only [e]
    apply (div_le_iff₀ hP).mpr
    rw [hPowerRatio] at hEdgeUpper
    nlinarith only [hEdgeUpper]
  obtain ⟨htlow,hthigh,hNormDense,hNormEnergy,hNormEdges,hNormSlope⟩ := hNumeric t e p ht hp hNormPot hNormUpper
  have hnlow : (N : ℝ) < 2*n := by
    have hh := (lt_div_iff₀ hN).mp htlow
    linarith
  have hnhigh : (n : ℝ) ≤ 2*N := ((div_lt_iff₀ hN).mp hthigh).le
  have hnN : N < 2*n := by exact_mod_cast hnlow
  have hnpos : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hDense : (c-ε)*(n : ℝ)^α ≤ edgesR G := by
    have hh := (le_div_iff₀ hP).mp hNormDense
    rw [hPowerRatio]
    nlinarith only [hh]
  have hEnergy : lam*energy G ≤ 7*η*P := (div_le_iff₀ hP).mp hNormEnergy
  have hEdges : edgesR G ≤ 5*(c+1)*P := (div_le_iff₀ hP).mp hNormEdges
  have hLamEdges : 2*lam*edgesR G ≤ η*P := by
    have hh := mul_le_mul_of_nonneg_left hEdges (show 0 ≤ 2*lam by positivity)
    have hs := (le_div_iff₀ (show 0 < 10*(c+1) by positivity)).mp hLamSmall
    have hsP := mul_le_mul_of_nonneg_right hs hP.le
    change lam*(10*(c+1))*P ≤ η*P at hsP
    nlinarith only [hh,hsP]
  have hMuSmall : mu*(n : ℝ) ≤ η*P := by
    apply (mul_le_mul_iff_left₀ hN).mp
    have hh := mul_le_mul_of_nonneg_left hnhigh hmu.le
    have hhN := mul_le_mul_of_nonneg_left hh hN.le
    have hs := mul_le_mul_of_nonneg_right hCsmall hP.le
    nlinarith only [hhN,hs,hmuN]
  have hBudgetLarge : M*P ≤ netBudget G lam mu := by
    have herr := mul_nonneg (show 0 ≤ M-13*η by change η ≤ M/20 at hηM; linarith) hP.le
    unfold netBudget
    simp only [Fintype.card_fin]
    nlinarith only [hPot,hEnergy,hLamEdges,hMuSmall,herr]
  have hMassLarge : M*P ≤ ∑ v, if SingleFold H G v then degreeR G v else 0 :=
    hBudgetLarge.trans (budget_le_fold_mass hG hlam.le hmu.le)
  have hPowerFour : (n : ℝ)^α ≤ 4*P := by
    have htPow := Real.rpow_le_rpow ht hthigh.le ha0.le
    have hTwoPow : (2 : ℝ)^α ≤ 4 := by
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha2.le
      norm_num [Real.rpow_two] at hh ⊢
      exact hh
    have hmul := mul_le_mul_of_nonneg_right (htPow.trans hTwoPow) hP.le
    rwa [← hPowerRatio] at hmul
  have hBudgetFinal : M/4*(n : ℝ)^α ≤ netBudget G lam mu := by
    have hh := mul_le_mul_of_nonneg_left hPowerFour (show 0 ≤ M/4 by positivity)
    nlinarith only [hh,hBudgetLarge]
  have hMassFinal : M/4*(n : ℝ)^α ≤ ∑ v, if SingleFold H G v then degreeR G v else 0 := by
    have hh := mul_le_mul_of_nonneg_left hPowerFour (show 0 ≤ M/4 by positivity)
    nlinarith only [hh,hMassLarge]
  have hPowUp : (N : ℝ)^(α-1) ≤ 2*(n : ℝ)^(α-1) :=
    small_power_double hN.le hnR.le hnlow.le (by linarith) (by linarith)
  have hPowDown : (n : ℝ)^(α-1) ≤ 2*(N : ℝ)^(α-1) :=
    small_power_double hnR.le hN.le hnhigh (by linarith) (by linarith)
  have hPowerBack : P ≤ 4*(n : ℝ)^α := by
    have hh := Real.rpow_le_rpow hN.le hnlow.le ha0.le
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hnR.le] at hh
    have htwo : (2 : ℝ)^α ≤ 4 := by
      have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha2.le
      simpa only [Real.rpow_two,show (2 : ℝ)^2=4 by norm_num] using ht
    exact hh.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hnR.le α))
  have hEnergyFinal : lam*energy G ≤ 7*ε*(n : ℝ)^α := by
    calc
      _ ≤ 7*η*P := hEnergy
      _ ≤ 7*η*(4*(n : ℝ)^α) := mul_le_mul_of_nonneg_left hPowerBack (by positivity)
      _ = 7*(4*η)*(n : ℝ)^α := by ring
      _ ≤ 7*ε*(n : ℝ)^α := by gcongr
  have hBetaRatio : (n : ℝ)^(α-1)=t^(α-1)*(N : ℝ)^(α-1) := by
    dsimp [t]
    rw [Real.div_rpow (Nat.cast_nonneg _) hN.le]
    exact (div_mul_cancel₀ _ (Real.rpow_pos_of_pos hN (α-1)).ne').symm
  have hMuTiny : mu ≤ η*(N : ℝ)^(α-1) := by
    apply (mul_le_mul_iff_left₀ hN).mp
    have hh := mul_le_mul_of_nonneg_right (show C ≤ η*(N : ℝ) by linarith)
      (Real.rpow_nonneg hN.le (α-1))
    nlinarith only [hh,hmuN']
  have hSlopeScale : (c*α*t)*((N : ℝ)^(α-1))=2*mu*(n : ℝ) := by
    calc
      _ = (2*C*(N : ℝ)^(α-1))*t := by dsimp [C]; ring
      _ = (2*(mu*(N : ℝ)))*t := by rw [hmuN']; ring
      _ = _ := by dsimp [t]; field_simp
  have hSlope : a*(n : ℝ)^(α-1) ≤ mu*(2*n-1) := by
    have hh := mul_le_mul_of_nonneg_right hNormSlope
      (Real.rpow_nonneg hN.le (α-1))
    rw [hSlopeScale] at hh
    have hBeta : a*t^(α-1)*(N : ℝ)^(α-1)=a*(n : ℝ)^(α-1) := by
      rw [hBetaRatio]; ring
    rw [add_mul,hBeta] at hh
    nlinarith only [hh,hMuTiny]
  have hInvLam : 1/lam=(1/A)*(N : ℝ)^(α-1) := by
    dsimp [lam]
    rw [Real.rpow_neg hN.le]
    field_simp
  refine ⟨n,G,by omega,hG.free,hDense,?_,hMassFinal,lam,mu,hlam,hmu,hG,hBudgetFinal,hEnergyFinal,hSlope⟩
  intro v
  obtain ⟨hdlo,hdhi⟩ := hG.degree_bounds hlam v
  simp only [Fintype.card_fin] at hdlo hdhi
  constructor
  · exact hSlope.trans hdlo
  · rw [hInvLam] at hdhi
    have hh := mul_le_mul_of_nonneg_left hPowUp (show 0 ≤ 1/A by positivity)
    calc
      degreeR G v ≤ (1/A)*(N : ℝ)^(α-1) := hdhi
      _ ≤ (1/A)*(2*(n : ℝ)^(α-1)) := hh
      _ = (2/A)*(n : ℝ)^(α-1) := by ring

#print axioms near_full_sharp_controlled
end Erdos713SharpPenaltyWitnesses
