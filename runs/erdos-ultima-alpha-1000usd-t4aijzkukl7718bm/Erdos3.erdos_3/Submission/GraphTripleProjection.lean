import Submission.PhaseCubicSmoothing

/-! Exact one-frequency-per-row formulas for graph triple convolution.
Local additivity on 4T-4T suffices; no global linear extension is assumed. -/
namespace Erdos3GraphTripleProjection
open Finset Erdos3PhaseCubicSmoothing Erdos3CorrelationSifting Erdos3PopularAlmostPeriods
  Erdos3SpectralGraphEnergy Erdos3FrequencyGraph Erdos3GraphSkewAnnihilation
  Erdos3UnlocalizedBilinearExtraction Erdos3LocalQuadraticIntegration
  Erdos3LocalSkewSymmetry Erdos3AntidiagonalTwistedEnergy Erdos3TwistedCorrelationEnergy
  Erdos3FiniteFourier
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def triple (T : Finset G) (x : G) : ℝ := diffSmooth T (indicator T) x

lemma triple_nonneg (T : Finset G) (x : G) : 0 ≤ triple T x :=
  diffSmooth_nonneg T _ (indicator_nonneg T) x

lemma triple_le_one (T : Finset G) (hT : T.Nonempty) (x : G) : triple T x ≤ 1 := by
  apply diffSmooth_le_one T hT
  intro y
  unfold indicator
  split_ifs <;> norm_num

lemma triple_mem {T : Finset G} {x : G} (hx : triple T x ≠ 0) : x ∈ (T+T)-T := by
  obtain ⟨b,_,hb⟩ := exists_ne_zero_of_expect_ne_zero hx
  obtain ⟨a,_,ha⟩ := exists_ne_zero_of_expect_ne_zero hb
  have hc : x+(a : G)-b ∈ T := by
    by_contra hc
    exact ha (if_neg hc)
  exact mem_sub.mpr ⟨(x+(a : G)-b)+b,add_mem_add hc b.property,a,a.property,by abel⟩

lemma triple_mem_diffBall {T : Finset G} (h0 : (0 : G) ∈ T) {x : G} (hx : triple T x ≠ 0) :
    x ∈ diffBall T 3 := by
  obtain ⟨p,hp,a,ha,rfl⟩ := mem_sub.mp (triple_mem hx)
  obtain ⟨b,hb,c,hc,rfl⟩ := mem_add.mp hp
  exact diffBall_sub (diffBall_add (subset_diffBall_one T h0 hb) (subset_diffBall_one T h0 hc))
    (subset_diffBall_one T h0 ha)

lemma local_triple_value (T : Finset G) (h0 : (0 : G) ∈ T) (F : G → AddChar G ℂ)
    (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    {a b c : G} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) :
    F (c+b-a) = F c+F b-F a := by
  have hT : T.Nonempty := ⟨0,h0⟩
  have h1 := subset_diffBall_one T h0
  have hcb : c+b ∈ diffBall T 2 := diffBall_add (h1 hc) (h1 hb)
  have hx : c+b-a ∈ diffBall T 3 := diffBall_sub hcb (h1 ha)
  rw [local_sub hF (diffBall_mono T hT (by decide) hcb)
    (diffBall_mono T hT (by decide) (h1 ha)) (diffBall_mono T hT (by decide) hx)]
  rw [hF c (diffBall_mono T hT (by decide) (h1 hc)) b
    (diffBall_mono T hT (by decide) (h1 hb)) (diffBall_mono T hT (by decide) hcb)]

lemma skew_triple_value (T : Finset G) (h0 : (0 : G) ∈ T) (F : G → AddChar G ℂ)
    (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    {a b c : G} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (d : G) :
    skewPhase F (c+b-a) d = skewPhase F c d*skewPhase F b d*conj (skewPhase F a d) := by
  simp only [skewPhase,local_triple_value T h0 F hF ha hb hc,character_sub_apply,
    AddChar.add_apply,char_sub,AddChar.map_add_eq_mul,map_mul,starRingEnd_self_apply]
  ring

/-- The scalar phase-weighted cubic convolution equals skew(x,d) times a
nonnegative scalar triple convolution, even though F is only locally additive. -/
theorem cubicSmooth_skew_factor (T : Finset G) (h0 : (0 : G) ∈ T) (F : G → AddChar G ℂ)
    (hF : LocallyAdditive (diffBall T 4 : Set G) F) (x d : G) :
    cubicSmooth T (fun y ↦ skewPhase F y d) x = skewPhase F x d*(triple T x : ℂ) := by
  rw [cubicSmooth_eq T ⟨0,h0⟩]
  have he (b a : T) : phaseMask T (fun y ↦ skewPhase F y d) (x-(b : G)+a)*
      skewPhase F b d*conj (skewPhase F a d) =
      skewPhase F x d*(indicator T (x+(a : G)-b) : ℂ) := by
    by_cases hc : x+(a : G)-b ∈ T
    · have hc' : x-(b : G)+a ∈ T := by simpa only [sub_add_eq_add_sub] using hc
      simp only [phaseMask,if_pos hc',indicator,if_pos hc,Complex.ofReal_one,mul_one]
      have hh := skew_triple_value T h0 F hF a.property b.property hc' d
      simpa only [show (x-(b : G)+a)+b-a = x by abel] using hh.symm
    · have hc' : x-(b : G)+a ∉ T := by simpa only [sub_add_eq_add_sub] using hc
      simp only [phaseMask,if_neg hc',indicator,if_neg hc,zero_mul,Complex.ofReal_zero,mul_zero]
  simp_rw [he,← mul_expect]
  congr 1
  simp only [triple,diffSmooth,ofReal_expect]

lemma graph_triple_indicator (T : Finset G) (h0 : (0 : G) ∈ T) (F : G → AddChar G ℂ)
    (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (x : G) (ψ : AddChar G ℂ) (b a : T) :
    indicator (frequencyGraph T F) ((x,ψ)+((a : G),F a)-((b : G),F b)) =
      if ψ = F x then indicator T (x+(a : G)-b) else 0 := by
  by_cases hc : x+(a : G)-b ∈ T
  · have hval : F (x+(a : G)-b)+F b-F a = F x := by
      have hh := local_triple_value T h0 F hF a.property b.property hc
      simpa only [show (x+(a : G)-b)+b-a = x by abel] using hh.symm
    have he : ψ+F a-F b = F (x+(a : G)-b) ↔ ψ = F x := by
      constructor
      · intro h
        rw [← hval,← h]
        abel
      · intro h
        rw [h,← hval]
        abel
    simp only [indicator,mem_frequencyGraph,Prod.fst_sub,Prod.fst_add,Prod.snd_sub,Prod.snd_add,
      hc,true_and,he,if_true]
  · simp only [indicator,mem_frequencyGraph,Prod.fst_sub,Prod.fst_add,Prod.snd_sub,Prod.snd_add,
      hc,false_and,if_false,ite_self]

/-- A graph triple convolution has at most one nonzero vertical coordinate
in each row. No averaging over the dual group is lost. -/
theorem graph_triple_projection (T : Finset G) (h0 : (0 : G) ∈ T) (F : G → AddChar G ℂ)
    (hF : LocallyAdditive (diffBall T 4 : Set G) F) (x : G) (ψ : AddChar G ℂ) :
    triple (frequencyGraph T F) (x,ψ) = if ψ = F x then triple T x else 0 := by
  have he : triple (frequencyGraph T F) (x,ψ) = 𝔼 b : T, 𝔼 a : T,
      indicator (frequencyGraph T F) ((x,ψ)+((a : G),F a)-((b : G),F b)) := by
    unfold triple diffSmooth
    symm
    apply Fintype.expect_equiv (graphEquiv T F)
    intro b
    exact Fintype.expect_equiv (graphEquiv T F) _ _ (fun a ↦ rfl)
  rw [he]
  simp_rw [graph_triple_indicator T h0 F hF]
  by_cases hψ : ψ = F x
  · simp only [if_pos hψ,triple,diffSmooth]
  · simp only [if_neg hψ,expect_const_zero]

lemma local_add_of_triple_nonzero (T : Finset G) (h0 : (0 : G) ∈ T) (F : G → AddChar G ℂ)
    (hF : LocallyAdditive (diffBall T 4 : Set G) F) {x s : G} (hs : s ∈ T)
    (hx : triple T (x+s) ≠ 0) : F (x+s) = F x+F s := by
  have hT : T.Nonempty := ⟨0,h0⟩
  have hxs := triple_mem_diffBall h0 hx
  have hs1 := subset_diffBall_one T h0 hs
  have hx4 : x ∈ diffBall T 4 := by
    simpa only [add_sub_cancel_right] using diffBall_sub hxs hs1
  exact hF x hx4 s (diffBall_mono T hT (by decide) hs1) (diffBall_mono T hT (by decide) hxs)

lemma graph_triple_shift (T : Finset G) (h0 : (0 : G) ∈ T) (F : G → AddChar G ℂ)
    (hF : LocallyAdditive (diffBall T 4 : Set G) F) (x : G) {s : G} (hs : s ∈ T) :
    triple (frequencyGraph T F) ((x,F x)+(s,F s)) = triple T (x+s) := by
  change triple (frequencyGraph T F) (x+s,F x+F s) = _
  rw [graph_triple_projection T h0 F hF]
  by_cases hx : triple T (x+s) = 0
  · simp only [hx,ite_self]
  · rw [if_pos (local_add_of_triple_nonzero T h0 F hF hs hx).symm]

/-- Exact phase transport at every translate by a point of T, including rows
outside the local domain, where the relevant scalar convolution vanishes. -/
lemma cubicSmooth_skew_shift (T : Finset G) (h0 : (0 : G) ∈ T) (F : G → AddChar G ℂ)
    (hF : LocallyAdditive (diffBall T 4 : Set G) F) (x d : G) {s : G} (hs : s ∈ T) :
    cubicSmooth T (fun y ↦ skewPhase F y d) (x+s) =
      skewPhase F x d*skewPhase F s d*(triple T (x+s) : ℂ) := by
  rw [cubicSmooth_skew_factor T h0 F hF]
  by_cases hx : triple T (x+s) = 0
  · simp only [hx,Complex.ofReal_zero,mul_zero]
  · congr 1
    simp only [skewPhase,local_add_of_triple_nonzero T h0 F hF hs hx,
      AddChar.add_apply,AddChar.map_add_eq_mul,map_mul]
    ring

#print axioms cubicSmooth_skew_factor
#print axioms graph_triple_projection
#print axioms cubicSmooth_skew_shift
end Erdos3GraphTripleProjection
