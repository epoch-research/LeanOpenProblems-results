import Submission.GreedyBatchReward
import Submission.MixedLayerRegularization

/-! One backward density step for conservative batches, with an explicit
forward volume bound. Residuals are restricted to their true carriers before
regularization. There is no assertion of a successful asymptotic iteration. -/
namespace Erdos773.GreedyBatchDensityStep
open Finset HypergraphDegreeTrim UniformLayerRegularization GreedyBatchState
open GreedyBatchCertificate GreedyBatchReward GreedyHypergraphState
open FiniteHypergraphRestriction (Carrier restrict up)
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 3500000
noncomputable section
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

def post (c : Caps) : Caps := { c with C := c.C+3 }

def copies (c : Caps) : ℕ := 24*(2*MixedLayerRegularization.cap c.D2 c.D3 c.D4)^3

/-- The bounded-volume induction predicate. -/
def UniformDensity (c : Caps) (V : ℕ) (δ : ℝ) : Prop :=
  ∀ (β : Type u) [Fintype β] [DecidableEq β] (H : Finset (Finset β)),
    Regular H c → Fintype.card β≤V →
      ∃ A : Finset β, Independent H A ∧ δ*Fintype.card β≤(A.card:ℝ)

lemma zero_density (c : Caps) (V : ℕ) : UniformDensity.{u} c V 0 := by
  intro β _ _ H h hV
  refine ⟨∅,?_,by simp⟩
  intro e he hesub
  have hh := card_le_card hesub
  have hr := (h.ranks e he).1
  simp only [card_empty] at hh
  omega

/-- A regular model of the actual conservative residual. Its independent
sets transfer to the restricted residual before any extension is attempted. -/
theorem regularize_next (H : Finset (Finset α)) (R : Finset α) (c c' : Caps)
    (h : Regular H c) (hn : NextBounds (next H R) c') (hP : c.P≤c'.P) (hPpos : 1≤c'.P) :
    ∃ r : ℕ, ∃ hprime : r.Prime,
      letI : Fact r.Prime := ⟨hprime⟩
      MixedLayerRegularization.cap c'.D2 c'.D3 c'.D4≤r ∧
      r≤2*MixedLayerRegularization.cap c'.D2 c'.D3 c'.D4 ∧
      ∃ G : Finset (Finset (MixedLayerRegularization.Model (Carrier (carrier H R)) r)),
        Regular G (post c') ∧
        (∀ B : Finset (MixedLayerRegularization.Model (Carrier (carrier H R)) r), Independent G B →
          ∃ A : Finset (Carrier (carrier H R)), Independent (restrict (carrier H R) (next H R)) A ∧
            B.card≤24*r^3*A.card) := by
  let Q := carrier H R
  let K := restrict Q (next H R)
  have hQ : ∀ e∈next H R, e⊆Q := fun e he => next_subset he
  have hrank : ∀ e∈K, 2≤e.card ∧ e.card≤4 := by
    intro e he
    have hh := next_rank (fun e he => (h.ranks e he).2) ((FiniteHypergraphRestriction.mem_restrict hQ).mp he)
    simpa only [FiniteHypergraphRestriction.up_card] using hh
  have h2 (x : Carrier Q) : degree (layer K 2) x≤c'.D2 := by
    rw [FiniteHypergraphRestriction.degree_eq hQ]
    exact hn.degree2 x.val
  have h3 (x : Carrier Q) : degree (layer K 3) x≤c'.D3 := by
    rw [FiniteHypergraphRestriction.degree_eq hQ]
    exact hn.degree3 x.val
  have h4 (x : Carrier Q) : degree (layer K 4) x≤c'.D4 := by
    rw [FiniteHypergraphRestriction.degree_eq hQ]
    exact hn.degree4 x.val
  have hp (x y : Carrier Q) (hxy : x≠y) : pairDegree K x y≤c'.P := by
    rw [FiniteHypergraphRestriction.pair_eq hQ]
    exact (GreedyBatchStructure.pair_le H R x.val y.val).trans
      ((h.pair _ _ (fun he => hxy (Subtype.ext he))).trans hP)
  have hc (x y : Carrier Q) (hxy : x≠y) : RegularizationCommonNeighbors.common K x y≤c'.C := by
    rw [FiniteHypergraphRestriction.common_eq hQ]
    exact hn.common _ _ (fun he => hxy (Subtype.ext he))
  have hb (x y : Carrier Q) (hxy : x≠y) : RegularizationSharedLinks.count K x y≤c'.B :=
    (GreedyBatchStructure.shared_restrict hQ x y).trans
      (hn.shared _ _ (fun he => hxy (Subtype.ext he)))
  obtain ⟨r,hprime,hrL,hrU,G,hr,hg2,hg3,hg4,hgp,hgi,hgc,ht,hbG⟩ :=
    MixedLayerRegularization.exists_regularization K c'.D2 c'.D3 c'.D4 c'.P c'.C
      hrank h2 h3 h4 hPpos hp
      (FiniteHypergraphRestriction.intersections hQ 2 (GreedyBatchStructure.intersections R 2 h.intersections)) hc
  letI : Fact r.Prime := ⟨hprime⟩
  refine ⟨r,hprime,hrL,hrU,G,?_,ht⟩
  exact ⟨hr,hgi,hg2,hg3,hg4,hgp,hgc,hbG c'.B hb⟩

/-- Continue on a good residual using the bounded-volume future density
hypothesis. The selected batch is added only after density transfer. -/
theorem continue_batch (H : Finset (Finset α)) (R : Finset α) (c c' : Caps) (V W : ℕ) (δ : ℝ)
    (h : Regular H c) (hn : NextBounds (next H R) c') (hP : c.P≤c'.P) (hPpos : 1≤c'.P)
    (hV : Fintype.card α≤V) (hW : copies c'*V≤W)
    (hfuture : UniformDensity.{u} (post c') W δ) :
    ∃ A : Finset α, Independent H A ∧ GreedyBatchSelection.reward H δ R≤(A.card:ℝ) := by
  obtain ⟨r,hprime,hrL,hrU,G,hG,ht⟩ := regularize_next H R c c' h hn hP hPpos
  letI : Fact r.Prime := ⟨hprime⟩
  let Q := carrier H R
  have hvol : Fintype.card (MixedLayerRegularization.Model (Carrier Q) r)≤W := by
    rw [MixedLayerRegularization.model_card,Fintype.card_coe]
    apply le_trans _ hW
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hrU 3))
      ((card_le_univ Q).trans hV)
  obtain ⟨B,hB,hδB⟩ := hfuture (MixedLayerRegularization.Model (Carrier Q) r) G hG hvol
  have hδB' : δ*(24*(r:ℝ)^3*Fintype.card (Carrier Q))≤(B.card:ℝ) := by
    simpa only [MixedLayerRegularization.model_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hδB
  obtain ⟨J,hJ,hδJ⟩ := MixedLayerRegularization.density_transfer hprime (restrict Q (next H R)) G ht B hB δ hδB'
  let A := up Q J
  have hA : A⊆carrier H R := FiniteHypergraphRestriction.up_subset J
  have hi : Independent (next H R) A :=
    (FiniteHypergraphRestriction.independent_iff (fun e he => next_subset he) J).mp hJ
  refine ⟨chosen H R∪A,extension R (fun e he => card_pos.mp (by have := (h.ranks e he).1; omega)) hA hi,?_⟩
  have hcard : δ*(carrier H R).card≤(A.card:ℝ) := by
    simpa only [Fintype.card_coe,A,FiniteHypergraphRestriction.up_card] using hδJ
  rw [extension_card H R hA,Nat.cast_add]
  exact add_le_add le_rfl hcard

/-- One rigorous backward induction step. The numerical hypotheses involve
only current caps, proposed margins, future caps, and forward volume bounds. -/
theorem density_step (c c' : Caps) (L : Margins) (p η δ ρ b : ℝ) (q V W : ℕ)
    (hL : L.Positive) (hp : ProbabilityRange c p η) (hf : Fits c L p η c')
    (hP : c.P≤c'.P) (hδ : 0≤δ) (hδ1 : δ≤1) (hρ : 0<ρ) (hb : 0≤b)
    (hv : ∀ i, vertexError c L p η q i≤b) (he : ∀ i, pairError c L p η q i≤b)
    (hrate : ρ≤rate c p δ-tests V*b) (hW : copies c'*V≤W)
    (hfuture : UniformDensity.{u} (post c') W δ) : UniformDensity.{u} c V ρ := by
  intro β _ _ H h hV
  by_cases hempty : Fintype.card β=0
  · refine ⟨∅,?_,by simp [hempty]⟩
    intro e he hesub
    have hh := card_le_card hesub
    have hr := (h.ranks e he).1
    simp only [card_empty] at hh
    omega
  have hvolpos : (0:ℝ)<Fintype.card β := by exact_mod_cast Nat.pos_of_ne_zero hempty
  have hm := mul_le_mul_of_nonneg_right (tests_mono hV) hb
  have hrate' : ρ≤rate c p δ-tests (Fintype.card β)*b := by linarith only [hrate,hm]
  have hpositive : 0<GreedyBatchSelection.lowerReward H p δ-
      (Fintype.card β:ℝ)*tests (Fintype.card β)*b := by
    rw [lowerReward_eq H c h]
    have hh := mul_pos hvolpos (hρ.trans_le hrate')
    nlinarith only [hh]
  obtain ⟨R,hn,hr⟩ := exists_batch H c c' L p η δ b q h hL hp hf hδ hδ1 hb hv he hpositive
  have hPpos : 1≤c'.P := by
    have hh := hp.dp_pos
    have hn := Nat.pos_of_mul_pos_left hh
    omega
  obtain ⟨A,hA,hrA⟩ := continue_batch H R c c' V W δ h hn hP hPpos hV hW hfuture
  refine ⟨A,hA,?_⟩
  have hmul := mul_le_mul_of_nonneg_left hrate' hvolpos.le
  rw [lowerReward_eq H c h] at hr
  nlinarith only [hmul,hr,hrA]

#print axioms zero_density
#print axioms regularize_next
#print axioms continue_batch
#print axioms density_step
end
end Erdos773.GreedyBatchDensityStep
