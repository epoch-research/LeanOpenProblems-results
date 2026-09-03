import Submission.FractionalEnvelope
import Submission.MixedSmoothing
import Submission.CountCriticalFractional
import Submission.FractionalSeparated

/-!
Uniform means over all even edge subgraphs. Complementation gives an
unconditional integral mean bound. The analogous fixed-factor fractional
comparison is ONLY a hypothesis of the final conditional reduction.
This file does not settle Erdos 184.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.UniformEvenMean
open CycleEnvelope CountCritical CycleNumberSubmodularity
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

noncomputable def mean (G : SimpleGraph V) (f : SimpleGraph V → ℝ) : ℝ :=
  (∑ H ∈ evenSubgraphs G, f H) / (evenSubgraphs G).card

lemma card_pos (G : SimpleGraph V) : 0 < (evenSubgraphs G).card :=
  Finset.card_pos.mpr (FractionalEnvelope.evenSubgraphs_nonempty G)

lemma mean_nonneg (G : SimpleGraph V) (f : SimpleGraph V → ℝ)
    (hf : ∀ H ∈ evenSubgraphs G, 0 ≤ f H) : 0 ≤ mean G f := by
  exact div_nonneg (Finset.sum_nonneg hf) (Nat.cast_nonneg _)

lemma mean_le (G : SimpleGraph V) (f : SimpleGraph V → ℝ) (B : ℝ)
    (hf : ∀ H ∈ evenSubgraphs G, f H ≤ B) : mean G f ≤ B := by
  have hp : (0 : ℝ) < (evenSubgraphs G).card := by exact_mod_cast card_pos G
  apply (div_le_iff₀ hp).mpr
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using Finset.sum_le_sum hf

lemma mean_mono (G : SimpleGraph V) (f g : SimpleGraph V → ℝ)
    (hfg : ∀ H ∈ evenSubgraphs G, f H ≤ g H) : mean G f ≤ mean G g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum hfg) (Nat.cast_nonneg _)

lemma complement_mem {G H : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    (hH : H ∈ evenSubgraphs G) : G \ H ∈ evenSubgraphs G := by
  obtain ⟨hle,heH⟩ := mem_evenSubgraphs.mp hH
  apply mem_evenSubgraphs.mpr
  refine ⟨sdiff_le, ?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
    even_sdiff_of_even hle he heH v

omit [Fintype V] in
lemma complement_complement {G H : SimpleGraph V} (hle : H ≤ G) :
    G \ (G \ H) = H := by
  ext u v
  simp only [sdiff_adj]
  constructor
  · rintro ⟨hg,hn⟩
    by_contra hh
    exact hn ⟨hg,hh⟩
  · intro hh
    exact ⟨hle hh,fun hn => hn.2 hh⟩

lemma sum_complement (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (f : SimpleGraph V → ℝ) :
    (∑ H ∈ evenSubgraphs G, f (G \ H)) = ∑ H ∈ evenSubgraphs G, f H := by
  apply Finset.sum_bij (fun H _ => G \ H)
  · intro H hH
    exact complement_mem he hH
  · intro H hH K hK h
    have hh := congrArg (fun A : SimpleGraph V => G \ A) h
    simpa only [complement_complement (mem_evenSubgraphs.mp hH).1,
      complement_complement (mem_evenSubgraphs.mp hK).1] using hh
  · intro H hH
    exact ⟨G \ H, complement_mem he hH,
      complement_complement (mem_evenSubgraphs.mp hH).1⟩
  · intros
    rfl

lemma mean_complement (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (f : SimpleGraph V → ℝ) : mean G (fun H => f (G \ H)) = mean G f := by
  unfold mean
  rw [sum_complement G he f]

lemma number_le_complement_sum (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (H : SimpleGraph V) (hH : H ∈ evenSubgraphs G) :
    cycleNumber G ≤ cycleNumber H + cycleNumber (G \ H) := by
  obtain ⟨hle,heH⟩ := mem_evenSubgraphs.mp hH
  have her := (mem_evenSubgraphs.mp (complement_mem he hH)).2
  obtain ⟨D,hcD,hdD,hcardD⟩ := minimum_exists H heH
  obtain ⟨E,hcE,hdE,hcardE⟩ := minimum_exists (G \ H) her
  have hd : Disjoint H.edgeSet (G \ H).edgeSet := by
    rw [edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hcov : H.edgeSet ∪ (G \ H).edgeSet = G.edgeSet := by
    rw [edgeSet_sdiff]
    exact Set.union_diff_cancel (edgeSet_mono hle)
  obtain ⟨P,hcP,hdP,hcardP⟩ := combine_pure_decompositions hle sdiff_le hd hcov
    D E hcD hcE hdD hdE
  rw [hcardD,hcardE] at hcardP
  exact (number_le G P hcP hdP).trans hcardP

/-- Complementation bounds the integral count by twice the INTEGRAL mean.
It does not allow replacement of that mean by the smaller fractional mean. -/
lemma number_le_twice_integral_mean (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) :
    (cycleNumber G : ℝ) ≤ 2 * mean G (fun H => (cycleNumber H : ℝ)) := by
  have hs : (∑ _H ∈ evenSubgraphs G, (cycleNumber G : ℝ)) ≤
      ∑ H ∈ evenSubgraphs G, ((cycleNumber H : ℝ) + cycleNumber (G \ H)) := by
    apply Finset.sum_le_sum
    intro H hH
    exact_mod_cast number_le_complement_sum G he H hH
  rw [Finset.sum_add_distrib, sum_complement G he (fun H => (cycleNumber H : ℝ))] at hs
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hp : (0 : ℝ) < (evenSubgraphs G).card := by exact_mod_cast card_pos G
  unfold mean
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hp).mpr
  nlinarith

noncomputable def fractionalMean (G : SimpleGraph V) : ℝ :=
  mean G FractionalEnvelope.optimum

lemma fractionalMean_nonneg (G : SimpleGraph V) : 0 ≤ fractionalMean G := by
  apply mean_nonneg
  intro H hH
  exact FractionalEnvelope.optimum_nonneg H (mem_evenSubgraphs.mp hH).2

lemma fractionalMean_le_integralMean (G : SimpleGraph V) :
    fractionalMean G ≤ mean G (fun H => (cycleNumber H : ℝ)) := by
  apply mean_mono
  intro H hH
  exact FractionalEnvelope.optimum_le_number H (mem_evenSubgraphs.mp hH).2

lemma fractionalMean_le_linear (G : SimpleGraph V) :
    fractionalMean G ≤ 2 * Fintype.card V := by
  apply mean_le
  intro H hH
  exact FractionalEnvelope.optimum_le_linear H (mem_evenSubgraphs.mp hH).2

lemma fractionalMean_le_envelope (G : SimpleGraph V) :
    fractionalMean G ≤ FractionalEnvelope.envelope G := by
  apply mean_le
  intro H hH
  obtain ⟨hle,heH⟩ := mem_evenSubgraphs.mp hH
  exact FractionalEnvelope.optimum_le_envelope hle heH


lemma optimum_le_complement_sum (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (H : SimpleGraph V) (hH : H ∈ evenSubgraphs G) :
    FractionalEnvelope.optimum G ≤
      FractionalEnvelope.optimum H + FractionalEnvelope.optimum (G \ H) := by
  obtain ⟨hle,heH⟩ := mem_evenSubgraphs.mp hH
  have her := (mem_evenSubgraphs.mp (complement_mem he hH)).2
  obtain ⟨s,hs,hcs⟩ := FractionalEnvelope.optimum_attained H heH
  obtain ⟨t,ht,hct⟩ := FractionalEnvelope.optimum_attained (G \ H) her
  have hd : Disjoint H.edgeSet (G \ H).edgeSet := by
    rw [edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hcov : H.edgeSet ∪ (G \ H).edgeSet = G.edgeSet := by
    rw [edgeSet_sdiff]
    exact Set.union_diff_cancel (edgeSet_mono hle)
  obtain ⟨w,hw,hcw⟩ := FractionalSeparated.combine hcov hd s t hs ht
  have hh := FractionalEnvelope.optimum_le_cost hw
  rwa [hcw,hcs,hct] at hh

/-- Fractional subadditivity gives the same averaging inequality for the
fractional optimum, not for the integral count. -/
lemma optimum_le_twice_fractionalMean (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) :
    FractionalEnvelope.optimum G ≤ 2 * fractionalMean G := by
  have hs := Finset.sum_le_sum (fun H (hH : H ∈ evenSubgraphs G) =>
    optimum_le_complement_sum G he H hH)
  rw [Finset.sum_add_distrib, sum_complement G he FractionalEnvelope.optimum] at hs
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hp : (0 : ℝ) < (evenSubgraphs G).card := by exact_mod_cast card_pos G
  unfold fractionalMean mean
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hp).mpr
  nlinarith

lemma degree_le_four_fractionalMean (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (v : V) :
    (G.degree v : ℝ) ≤ 4 * fractionalMean G := by
  have hd := FractionalEnvelope.degree_le_twice_optimum G he v
  have hm := optimum_le_twice_fractionalMean G he
  linarith

universe u
/-- A fixed positive-fraction comparison on critical graphs would suffice.
The comparison premise is not proved in this file. -/
lemma conjecture_of_critical_mean_comparison (K : ℝ) (hK : 0 ≤ K)
    (hcomp : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      IsCountCritical k G → (k : ℝ) ≤ K * fractionalMean G) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_bound.mpr
  refine ⟨2*K,?_⟩
  intro V _ _ G he
  obtain ⟨D,hc,hd,hcard⟩ := bound_of_critical_subgraph_bound G he
    ((2*K)*Fintype.card V) (by positivity) (by
      intro H _ k hk
      have hl := hcomp H k hk
      have hu := mul_le_mul_of_nonneg_left (fractionalMean_le_linear H) hK
      nlinarith)
  refine ⟨D,?_,hd,hcard⟩
  intro H hH
  apply Or.inl
  refine ⟨(hc H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hc H hH).2 v

end Erdos184.UniformEvenMean
