import FormalConjecturesUtil
import Submission.CloneResistance
import Submission.NumericPenaltySelection

/-! Near-full-density witnesses with simultaneous degree bounds and positive
cloning-obstruction mass. No rationality or quotient-rate transfer is claimed. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713NearFullPenaltyWitnesses
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713Cloning Erdos713CloneResistance
variable {U W : Type*}
set_option maxHeartbeats 2000000

lemma exists_global_graph [Fintype U] (H : SimpleGraph W) (hH : H ≠ ⊥) {lam mu : ℝ}
    (hlam : 0 ≤ lam) (hmu : 0 < mu)
    (hz : Tendsto (fun n : ℕ => (extremalNumber n H : ℝ)/(n : ℝ)^2) atTop (𝓝 0))
    (K : SimpleGraph U) (hK : H.Free K) (hpos : 0 < potential lam mu K) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), GlobalOptimal H G lam mu ∧
      potential lam mu K ≤ potential lam mu G := by
  let e := Fintype.equivFin U
  let J := K.map e.toEmbedding
  let f : K ≃g J := Iso.map e K
  have hf : H.Free J := fun h => hK (h.trans ⟨f.symm.toCopy⟩)
  have he : potential lam mu J = potential lam mu K := potential_iso f lam mu
  obtain ⟨n,G,hG,hmax⟩ := exists_global H hH hlam hmu hz J hf (by rwa [he])
  exact ⟨n,G,hG,by rwa [he] at hmax⟩

lemma global_upper_envelope (H : SimpleGraph W) {α c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, (extremalNumber n H : ℝ) ≤ (c+η)*(n : ℝ)^α+B := by
  have hev : ∀ᶠ n : ℕ in atTop, (extremalNumber n H : ℝ) ≤ (c+η)*(n : ℝ)^α := by
    filter_upwards [(Erdos713FutureRecords.ratio_limit h).eventually_lt_const
      (show c < c+η by linarith),eventually_gt_atTop (0 : ℕ)] with n hn hnp
    exact ((div_lt_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hnp : (0 : ℝ) < n) α)).mp hn).le
  obtain ⟨L,hL⟩ := eventually_atTop.mp hev
  let B : ℕ := ∑ j ∈ range L, extremalNumber j H
  refine ⟨B,Nat.cast_nonneg _,?_⟩
  intro n
  by_cases hn : L ≤ n
  · exact (hL n hn).trans (le_add_of_nonneg_right (Nat.cast_nonneg B))
  · have hh : extremalNumber n H ≤ B := single_le_sum (s := range L) (f := fun j => extremalNumber j H)
      (fun j _ => Nat.zero_le _) (mem_range.mpr (by omega : n < L))
    have hhR : (extremalNumber n H : ℝ) ≤ B := by exact_mod_cast hh
    have hp : 0 ≤ (c+η)*(n : ℝ)^α := by positivity
    linarith

lemma small_power_double {x y β : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ≤ 2*y) (hb : 0 ≤ β) (hb1 : β ≤ 1) : x^β ≤ 2*y^β := by
  have hh := Real.rpow_le_rpow hx hxy hb
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hy] at hh
  have hc : (2 : ℝ)^β ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hb1
  exact hh.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hy β))

/-- The lower-degree and fold-mass coefficients are fixed before the desired
accuracy. The upper-degree coefficient may depend on that accuracy. -/
theorem near_full_joint_controlled [Fintype W] (H : SimpleGraph W) (hH : H.IsBipartite)
    (hEdge : ∃ v w, H.Adj v w) {α c : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
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
  refine ⟨C/4,M/4,by positivity,by positivity,?_⟩
  intro ε hε
  obtain ⟨η,hη,hη1,hηc,hηM,hηε,hNumeric⟩ :=
    Erdos713NumericPenaltySelection.selection_errors_strong ha0 ha2 hc hε
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
  obtain ⟨htlow,hthigh,hNormDense,hNormEnergy,hNormEdges⟩ := hNumeric t e p ht hp hNormPot hNormUpper
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
  have hSlope : C/4*(n : ℝ)^(α-1) ≤ mu*(2*n-1) := by
    have hh := mul_le_mul_of_nonneg_left hPowDown (show 0 ≤ C/4 by positivity)
    have hnmu := mul_le_mul_of_nonneg_left hnlow.le hmu.le
    have hbase := mul_nonneg hmu.le (sub_nonneg.mpr hn1)
    nlinarith only [hh,hnmu,hmuN',hbase]
  have hInvLam : 1/lam=(1/A)*(N : ℝ)^(α-1) := by
    dsimp [lam]
    rw [Real.rpow_neg hN.le]
    field_simp
  refine ⟨n,G,by omega,hG.free,hDense,?_,hMassFinal,lam,mu,hlam,hmu,hG,hBudgetFinal,hEnergyFinal,hSlope⟩
  intro v
  obtain ⟨hdlo,hdhi⟩ := hG.degree_bounds hlam v
  simp only [Fintype.card_fin] at hdlo hdhi
  constructor
  · have hh := mul_le_mul_of_nonneg_left hPowDown (show 0 ≤ C/4 by positivity)
    have hnmu := mul_le_mul_of_nonneg_left hnlow.le hmu.le
    have hbase : mu*(n : ℝ) ≤ degreeR G v := by nlinarith only [hdlo,mul_nonneg hmu.le (sub_nonneg.mpr hn1)]
    nlinarith only [hh,hnmu,hmuN',hbase]
  · rw [hInvLam] at hdhi
    have hh := mul_le_mul_of_nonneg_left hPowUp (show 0 ≤ 1/A by positivity)
    calc
      degreeR G v ≤ (1/A)*(N : ℝ)^(α-1) := hdhi
      _ ≤ (1/A)*(2*(n : ℝ)^(α-1)) := hh
      _ = (2/A)*(n : ℝ)^(α-1) := by ring

/-- The quantitative-budget API, discarding explicit parameter controls. -/
theorem near_full_joint_budget [Fintype W] (H : SimpleGraph W) (hH : H.IsBipartite)
    (hEdge : ∃ v w, H.Adj v w) {α c : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        L ≤ n ∧ H.Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
        (∀ v, a*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
        κ*(n : ℝ)^α ≤ (∑ v, if SingleFold H G v then degreeR G v else 0) ∧
        ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ GlobalOptimal H G lam mu ∧
          κ*(n : ℝ)^α ≤ netBudget G lam mu := by
  obtain ⟨a,κ,ha',hκ,hs⟩ := near_full_joint_controlled H hH hEdge ha ha2 hc h
  refine ⟨a,κ,ha',hκ,?_⟩
  intro ε hε
  obtain ⟨D,hD,hD'⟩ := hs ε hε
  refine ⟨D,hD,?_⟩
  intro L
  obtain ⟨n,G,hn,hFree,hDense,hDeg,hMass,lam,mu,hlam,hmu,hG,hBudget,_⟩ := hD' L
  exact ⟨n,G,hn,hFree,hDense,hDeg,hMass,lam,mu,hlam,hmu,hG,hBudget⟩

/-- The original joint-witness conclusion, discarding the quantitative budget. -/
theorem near_full_joint [Fintype W] (H : SimpleGraph W) (hH : H.IsBipartite)
    (hEdge : ∃ v w, H.Adj v w) {α c : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        L ≤ n ∧ H.Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
        (∀ v, a*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
        κ*(n : ℝ)^α ≤ (∑ v, if SingleFold H G v then degreeR G v else 0) ∧
        ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ GlobalOptimal H G lam mu := by
  obtain ⟨a,κ,ha',hκ,hs⟩ := near_full_joint_budget H hH hEdge ha ha2 hc h
  refine ⟨a,κ,ha',hκ,?_⟩
  intro ε hε
  obtain ⟨D,hD,hD'⟩ := hs ε hε
  refine ⟨D,hD,?_⟩
  intro L
  obtain ⟨n,G,hn,hFree,hDense,hDeg,hMass,lam,mu,hlam,hmu,hG,_⟩ := hD' L
  exact ⟨n,G,hn,hFree,hDense,hDeg,hMass,lam,mu,hlam,hmu,hG⟩

#print axioms near_full_joint_controlled
#print axioms near_full_joint_budget
#print axioms near_full_joint
end Erdos713NearFullPenaltyWitnesses
