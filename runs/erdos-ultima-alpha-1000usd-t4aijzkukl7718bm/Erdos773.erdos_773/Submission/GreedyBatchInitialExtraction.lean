import Submission.GreedyBatchProfileIteration

/-! Initial regularization and exact density transfer for the shrinking
mixed-batch theorem. The initial hypergraph is genuinely four-uniform. -/
namespace Erdos773.GreedyBatchInitialExtraction
open Finset HypergraphDegreeTrim UniformLayerRegularization GreedyHypergraphState
open FourUniformRegularization (pairDegree)
open GreedyBatchCertificate GreedyBatchProfiles GreedyBatchProfileStep
open GreedyBatchDensityStep GreedyBatchDensityProfile GreedyBatchVolume
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option exponentiation.threshold 2048
noncomputable section
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

omit [Fintype α] in
lemma layer_four (H : Finset (Finset α)) (hfour : ∀ e ∈ H, e.card=4) : layer H 4=H := by
  ext e
  simp only [layer,mem_filter]
  exact ⟨And.left,fun he => ⟨he,hfour e he⟩⟩

omit [Fintype α] in
lemma layer_empty (H : Finset (Finset α)) (hfour : ∀ e ∈ H, e.card=4) (k : ℕ) (hk : k≠4) :
    layer H k=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hc⟩ := mem_filter.mp he
  exact hk (hc.symm.trans (hfour e he))

lemma common_zero (H : Finset (Finset α)) (hfour : ∀ e ∈ H, e.card=4) (x y : α) :
    RegularizationCommonNeighbors.common H x y=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨⟨hne,he⟩,_⟩ := RegularizationCommonNeighbors.mem_both.mp hz
  have hh := hfour _ he
  simp [hne] at hh

lemma shared_zero (H : Finset (Finset α)) (hfour : ∀ e ∈ H, e.card=4) (x y : α) :
    RegularizationSharedLinks.count H x y=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hc,hx,_,hm,_⟩ := RegularizationSharedLinks.mem_links.mp he
  have hh := hfour _ hm
  rw [card_insert_of_notMem hx,hc] at hh
  omega

lemma initial_range (m : ℕ) (d T : ℝ) (P : ℕ) (hm : 2000000≤ m)
    (hd : 0<d) (hP : 1≤P) (hPm : P≤ m) (hT : 1≤T)
    (hterminal : (m:ℝ)^1000≤d*Real.exp (-a m*((T+1)^3-1))) : Range m d 1 3 P := by
  have hm100 : 100≤ m := by omega
  have hmR : (100:ℝ)≤ m := by exact_mod_cast hm100
  have hpow : (1:ℝ)≤(T+1)^3 := one_le_pow₀ (by linarith only [hT])
  have ha := (coefficients m hm100).2.2.2.1
  have hexp : Real.exp (-a m*((T+1)^3-1))≤1 := by
    apply Real.exp_le_one_iff.mpr
    have := mul_nonneg ha (sub_nonneg.mpr hpow)
    nlinarith only [this]
  refine ⟨hm100,hterminal.trans ?_,le_rfl,by linarith only [hmR],?_,by omega,hP,hPm⟩
  · exact (mul_le_mul_of_nonneg_left hexp hd.le).trans_eq (mul_one d)
  · exact (show 3≤ m by omega).trans (Nat.le_pow (by omega : 0<60))

/-- No density is lost in regularizing the original four-uniform carrier.
The enlarged exponent accounts for every copy used by this initial step. -/
theorem independent (H : Finset (Finset α)) (m A : ℕ) (d T : ℝ) (P : ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment (A+increment A)≤ m)
    (hd : 0<d) (hdU : d≤ (m:ℝ)^A) (hP : 1≤P) (hPm : P≤ m)
    (hT : 1≤T) (hT3 : T^3≤(m:ℝ)/16)
    (hterminal : (m:ℝ)^1000≤d*Real.exp (-a m*((T+1)^3-1)))
    (hvol : Fintype.card α≤ m^A) (hfour : ∀ e ∈ H, e.card=4)
    (hdegree : ∀ x, (degree H x:ℝ)≤d^3)
    (hpair : ∀ x y, x≠y → pairDegree H x y≤P)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e≠f → (e∩f).card≤2) :
    ∃ I : Finset α, Independent H I ∧ efficiency m*(T-1)/d*Fintype.card α≤(I.card:ℝ) := by
  let c := caps m d 1 3 P
  have hr := initial_range m d T P hm hd hP hPm hT hterminal
  have hdegree' (x : α) : degree (layer H 4) x≤c.D4 := by
    rw [layer_four H hfour]
    exact_mod_cast (hdegree x).trans (Nat.le_ceil (f4 d))
  obtain ⟨r,hprime,hrL,hrU,G,hGr,hG2,hG3,hG4,hGp,hGi,hGc,ht,hGb⟩ :=
    MixedLayerRegularization.exists_regularization H c.D2 c.D3 c.D4 P 0
      (fun e he => by rw [hfour e he]; omega)
      (fun x => by rw [layer_empty H hfour 2 (by omega)]; simp [degree])
      (fun x => by rw [layer_empty H hfour 3 (by omega)]; simp [degree])
      hdegree' hP hpair hinter (fun x y _ => by rw [common_zero H hfour])
  letI : Fact r.Prime := ⟨hprime⟩
  have hG : Regular G c := ⟨hGr,hGi,hG2,hG3,hG4,hGp,hGc,
    hGb c.B (fun x y _ => by rw [shared_zero H hfour]; omega)⟩
  have hcopy : 24*r^3≤ m^(increment A) :=
    (Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hrU 3)).trans
      (copies_bound m A d 1 3 P hr hdU)
  have hGV : Fintype.card (MixedLayerRegularization.Model α r)≤ m^(A+increment A) := by
    rw [MixedLayerRegularization.model_card,pow_add]
    exact (Nat.mul_le_mul hcopy hvol).trans_eq (Nat.mul_comm _ _)
  have hdV : d≤(m:ℝ)^(A+increment A) :=
    hdU.trans (pow_le_pow_right₀ hr.m_one (Nat.le_add_right _ _))
  obtain ⟨B,hB,hcard⟩ := GreedyBatchProfileIteration.uniform_horizon m (A+increment A) d T P
    hm hmV hd hdV hP hPm hT hT3 hterminal (MixedLayerRegularization.Model α r) G hG hGV
  have hcard' : efficiency m*(T-1)/d*(24*(r:ℝ)^3*Fintype.card α)≤(B.card:ℝ) := by
    simpa only [MixedLayerRegularization.model_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hcard
  exact MixedLayerRegularization.density_transfer hprime H G ht B hB _ hcard'

/-- Ambient finite-set form of the four-uniform selection theorem. -/
theorem selection {β : Type u} [DecidableEq β] (V : Finset β) (H : Finset (Finset β))
    (m A : ℕ) (d T : ℝ) (P : ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment (A+increment A)≤ m)
    (hd : 0<d) (hdU : d≤(m:ℝ)^A) (hP : 1≤P) (hPm : P≤ m)
    (hT : 1≤T) (hT3 : T^3≤(m:ℝ)/16)
    (hterminal : (m:ℝ)^1000≤d*Real.exp (-a m*((T+1)^3-1)))
    (hvol : V.card≤ m^A) (hH : ∀ e ∈ H, e⊆V) (hfour : ∀ e ∈ H, e.card=4)
    (hdegree : ∀ x ∈ V, (degree H x:ℝ)≤d^3)
    (hpair : ∀ x ∈ V, ∀ y ∈ V, x≠y → pairDegree H x y≤P)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e≠f → (e∩f).card≤2) :
    ∃ I⊆V, (∀ e ∈ H, ¬e⊆I) ∧ efficiency m*(T-1)/d*V.card≤(I.card:ℝ) := by
  let K := FiniteHypergraphRestriction.restrict V H
  have hfour' : ∀ e ∈ K, e.card=4 := by
    intro e he
    have hh := hfour _ ((FiniteHypergraphRestriction.mem_restrict hH).mp he)
    simpa only [FiniteHypergraphRestriction.up_card] using hh
  have hdeg' (x : FiniteHypergraphRestriction.Carrier V) : (degree K x:ℝ)≤d^3 := by
    rw [← layer_four K hfour',FiniteHypergraphRestriction.degree_eq hH,layer_four H hfour]
    exact hdegree x.val x.property
  obtain ⟨I,hI,hcard⟩ := independent K m A d T P
    hm hmV hd hdU hP hPm hT hT3 hterminal (by simpa only [Fintype.card_coe] using hvol)
    hfour' hdeg'
    (fun x y hxy => by
      rw [FiniteHypergraphRestriction.pair_eq hH]
      exact hpair x.val x.property y.val y.property (fun he => hxy (Subtype.ext he)))
    (FiniteHypergraphRestriction.intersections hH 2 hinter)
  refine ⟨FiniteHypergraphRestriction.up V I,FiniteHypergraphRestriction.up_subset I,
    (FiniteHypergraphRestriction.independent_iff hH I).mp hI,?_⟩
  simpa only [FiniteHypergraphRestriction.up_card,Fintype.card_coe] using hcard

#print axioms initial_range
#print axioms independent
#print axioms selection
end
end Erdos773.GreedyBatchInitialExtraction
