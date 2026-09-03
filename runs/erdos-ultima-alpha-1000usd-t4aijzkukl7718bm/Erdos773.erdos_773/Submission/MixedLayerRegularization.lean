import Submission.RegularizationCommonNeighbors
import Submission.RegularizationSharedLinks

/-! Simultaneous rank-2/3/4 regularization with polynomially many copies.
It preserves independent-set density and the original codegree/intersection
caps, and increases the graph common-neighbor cap by at most three.
No stochastic restart or asymptotic square-Sidon bound is asserted here. -/
namespace Erdos773.MixedLayerRegularization
open Finset UniformLayerRegularization HypergraphDegreeTrim
open FourUniformRegularization (pairDegree)
open RegularizationCommonNeighbors (common)
set_option maxHeartbeats 2500000
noncomputable section

section OneLayer
variable {α ρ F : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Nontrivial ρ]
  [Field F] [Fintype F] [DecidableEq F]

/-- Exact data for one regularized degree layer, retaining every other rank. -/
structure Result (H : Finset (Finset α)) (D K C : ℕ)
    (G : Finset (Finset (Vertex α ρ F))) : Prop where
  ranks : ∀ e ∈ G, 2≤e.card ∧ e.card≤4
  target : ∀ x, degree (layer G (Fintype.card ρ)) x=D
  other : ∀ k, k≠Fintype.card ρ → ∀ x, degree (layer G k) x=degree (layer H k) x.1
  pair : ∀ x y, x≠y → pairDegree G x y≤K
  intersections : ∀ e ∈ G, ∀ f ∈ G, e≠f → (e∩f).card≤2
  common : ∀ x y, x≠y → RegularizationCommonNeighbors.common G x y≤C
  transfer : ∀ B : Finset (Vertex α ρ F), (∀ e ∈ G, ¬e⊆B) →
    ∃ A : Finset α, (∀ e ∈ H, ¬e⊆A) ∧ B.card≤(Fintype.card ρ*Fintype.card F)*A.card
  shared : ∀ B : ℕ, (∀ a b, a≠b → RegularizationSharedLinks.count H a b≤B) →
    ∀ x y, x≠y → RegularizationSharedLinks.count G x y≤B

/-- Higher-rank additions do not change the graph common-neighbor bound. -/
theorem higher (H : Finset (Finset α)) (D K C : ℕ)
    (hH : ∀ e ∈ H, 2≤e.card ∧ e.card≤4)
    (hdeg : ∀ a, degree (layer H (Fintype.card ρ)) a≤D)
    (hK : 1≤K) (hpair : ∀ a b, a≠b → pairDegree H a b≤K)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e≠f → (e∩f).card≤2)
    (hcommon : ∀ a b, a≠b → common H a b≤C)
    (hρ : 2≤Fintype.card ρ ∧ Fintype.card ρ≤4) (hne : Fintype.card ρ≠2)
    (hD : D≤Fintype.card F) (h : ρ → F) (hh : Function.Injective h) :
    ∃ G : Finset (Finset (Vertex α ρ F)), Result H D K C G := by
  obtain ⟨S,hS⟩ := exists_slopes (F := F) (layer H (Fintype.card ρ)) D hD
  refine ⟨regularized H h S,⟨rank_range H h S hH hρ,?_,
    fun k hk x => degree_layer_other H h S hk x,
    regularized_pair_degree H h hh S K hK hpair,
    regularized_intersections H h hh S 2 (by omega) hinter,
    RegularizationCommonNeighbors.higher_common_bound H h S hne C hcommon,
    independent_slice H h S,RegularizationSharedLinks.count_bound H h hh S⟩⟩
  intro x
  rw [degree_layer_same H h hh S x,hS x.1]
  exact Nat.add_sub_of_le (hdeg x.1)

/-- A Sidon reservoir makes the rank-two padding graph sparse in common
neighbors, including when the old graph layer is nonempty. -/
theorem two (H : Finset (Finset α)) (D K C : ℕ)
    (hH : ∀ e ∈ H, 2≤e.card ∧ e.card≤4)
    (hdeg : ∀ a, degree (layer H 2) a≤D)
    (hK : 1≤K) (hpair : ∀ a b, a≠b → pairDegree H a b≤K)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e≠f → (e∩f).card≤2)
    (hcommon : ∀ a b, a≠b → common H a b≤C)
    (T : Finset F) (hTcard : D≤T.card) (hT : IsSidon (T:Set F))
    (h : Fin 2 → F) (hh : Function.Injective h) :
    ∃ G : Finset (Finset (Vertex α (Fin 2) F)), Result H D K (C+3) G := by
  obtain ⟨S,hST,hS⟩ := exists_slopes_subset (layer H 2) D T hTcard
  refine ⟨regularized H h S,⟨rank_range H h S hH (by norm_num),?_,
    fun k hk x => degree_layer_other H h S hk x,
    regularized_pair_degree H h hh S K hK hpair,
    regularized_intersections H h hh S 2 (by omega) hinter,
    RegularizationCommonNeighbors.two_common_bound H h hh S T hST hT C hcommon,
    independent_slice H h S,RegularizationSharedLinks.count_bound H h hh S⟩⟩
  intro x
  rw [degree_layer_same H h hh S x]
  simp only [Fintype.card_fin,hS]
  exact Nat.add_sub_of_le (hdeg x.1)
end OneLayer

/-- One prime field suffices for all three regularization layers. -/
def cap (D2 D3 D4 : ℕ) : ℕ := max (max D3 D4) (2*PolynomialSidonSlopes.height D2+5)

abbrev Model (α : Type*) (p : ℕ) :=
  Vertex (Vertex (Vertex α (Fin 4) (ZMod p)) (Fin 3) (ZMod p)) (Fin 2) (ZMod p)

def labels (r p : ℕ) : Fin r → ZMod p := fun i => i.val

lemma labels_injective {r p : ℕ} (hp : r≤p) : Function.Injective (labels r p) := by
  intro i j he
  apply Fin.ext
  have hh := (ZMod.natCast_eq_natCast_iff' i.val j.val p).mp he
  simpa only [Nat.mod_eq_of_lt (i.isLt.trans_le hp),Nat.mod_eq_of_lt (j.isLt.trans_le hp)] using hh

lemma model_card {α : Type*} [Fintype α] {p : ℕ} [NeZero p] :
    Fintype.card (Model α p)=24*p^3*Fintype.card α := by
  simp only [Model,Vertex,Copy,Fintype.card_prod,Fintype.card_fin,ZMod.card]
  ring

section Assemble
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A genuine finite mixed-rank regularization. All three target degrees
are achieved simultaneously. The number of copies is exactly 24*p^3,
with p bounded polynomially in the three prescribed degree caps. -/
theorem exists_regularization (H : Finset (Finset α)) (D2 D3 D4 K C : ℕ)
    (hH : ∀ e ∈ H, 2≤e.card ∧ e.card≤4)
    (h2 : ∀ a, degree (layer H 2) a≤D2)
    (h3 : ∀ a, degree (layer H 3) a≤D3)
    (h4 : ∀ a, degree (layer H 4) a≤D4)
    (hK : 1≤K) (hpair : ∀ a b, a≠b → pairDegree H a b≤K)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e≠f → (e∩f).card≤2)
    (hcommon : ∀ a b, a≠b → common H a b≤C) :
    ∃ p : ℕ, ∃ hprime : p.Prime,
      letI : Fact p.Prime := ⟨hprime⟩
      cap D2 D3 D4≤p ∧ p≤2*cap D2 D3 D4 ∧
      ∃ G : Finset (Finset (Model α p)),
        (∀ e ∈ G, 2≤e.card ∧ e.card≤4) ∧
        (∀ x, degree (layer G 2) x=D2) ∧
        (∀ x, degree (layer G 3) x=D3) ∧
        (∀ x, degree (layer G 4) x=D4) ∧
        (∀ x y, x≠y → pairDegree G x y≤K) ∧
        (∀ e ∈ G, ∀ f ∈ G, e≠f → (e∩f).card≤2) ∧
        (∀ x y, x≠y → common G x y≤C+3) ∧
        (∀ B : Finset (Model α p), (∀ e ∈ G, ¬e⊆B) →
          ∃ A : Finset α, (∀ e ∈ H, ¬e⊆A) ∧ B.card≤24*p^3*A.card) ∧
        (∀ B : ℕ, (∀ a b, a≠b → RegularizationSharedLinks.count H a b≤B) →
          ∀ x y, x≠y → RegularizationSharedLinks.count G x y≤B) := by
  have hcap : 5≤cap D2 D3 D4 := by unfold cap; omega
  obtain ⟨p,hprime,hp,hpupper⟩ := Nat.exists_prime_lt_and_le_two_mul (cap D2 D3 D4) (by omega)
  letI : Fact p.Prime := ⟨hprime⟩
  have hp5 : 5≤p := hcap.trans hp.le
  have hp3 : D3≤Fintype.card (ZMod p) := by
    rw [ZMod.card]
    exact (le_max_left D3 D4).trans ((le_max_left _ _).trans hp.le)
  have hp4 : D4≤Fintype.card (ZMod p) := by
    rw [ZMod.card]
    exact (le_max_right D3 D4).trans ((le_max_left _ _).trans hp.le)
  have hpT : 2*PolynomialSidonSlopes.height D2<p := by
    have hh := (le_max_right (max D3 D4) (2*PolynomialSidonSlopes.height D2+5)).trans hp.le
    omega
  obtain ⟨G4,g4⟩ := higher (ρ := Fin 4) H D4 K C hH
    (by simpa only [Fintype.card_fin] using h4) hK hpair hinter hcommon
    (by norm_num) (by norm_num) hp4 (labels 4 p) (labels_injective (by omega))
  have g43 : ∀ x, degree (layer G4 3) x≤D3 := by
    intro x
    rw [g4.other 3 (by norm_num)]
    exact h3 x.1
  obtain ⟨G3,g3⟩ := higher (ρ := Fin 3) G4 D3 K C g4.ranks
    (by simpa only [Fintype.card_fin] using g43) hK g4.pair g4.intersections g4.common
    (by norm_num) (by norm_num) hp3 (labels 3 p) (labels_injective (by omega))
  have g32 : ∀ x, degree (layer G3 2) x≤D2 := by
    intro x
    rw [g3.other 2 (by norm_num),g4.other 2 (by norm_num)]
    exact h2 x.1.1
  obtain ⟨G2,g2⟩ := two G3 D2 K C g3.ranks g32 hK g3.pair g3.intersections g3.common
    (PolynomialSidonSlopes.seed D2 p) (by rw [PolynomialSidonSlopes.seed_card D2 p hpT])
    (PolynomialSidonSlopes.seed_sidon D2 p hpT) (labels 2 p) (labels_injective (by omega))
  refine ⟨p,hprime,hp.le,hpupper,G2,g2.ranks,?_,?_,?_,g2.pair,g2.intersections,g2.common,?_,?_⟩
  · simpa only [Fintype.card_fin] using g2.target
  · intro x
    rw [g2.other 3 (by norm_num)]
    exact g3.target x.1
  · intro x
    rw [g2.other 4 (by norm_num),g3.other 4 (by norm_num)]
    exact g4.target x.1.1
  · intro B hB
    obtain ⟨A3,hA3,hc3⟩ := g2.transfer B hB
    obtain ⟨A4,hA4,hc4⟩ := g3.transfer A3 hA3
    obtain ⟨A,hA,hc⟩ := g4.transfer A4 hA4
    refine ⟨A,hA,?_⟩
    simp only [Fintype.card_fin,ZMod.card] at hc3 hc4 hc
    calc
      B.card ≤ (2*p)*A3.card := hc3
      _ ≤ (2*p)*((3*p)*A4.card) := Nat.mul_le_mul_left _ hc4
      _ ≤ (2*p)*((3*p)*((4*p)*A.card)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc)
      _ = 24*p^3*A.card := by ring
  · intro B hB
    exact g2.shared B (g3.shared B (g4.shared B hB))

omit [DecidableEq α] in
/-- The resulting cardinality transfer is precisely a density transfer,
not a further constant-factor loss. -/
lemma density_transfer {p : ℕ} (hp : p.Prime) (H : Finset (Finset α))
    (G : Finset (Finset (Model α p)))
    (htransfer : ∀ B : Finset (Model α p), (∀ e ∈ G, ¬e⊆B) →
      ∃ A : Finset α, (∀ e ∈ H, ¬e⊆A) ∧ B.card≤24*p^3*A.card)
    (B : Finset (Model α p)) (hB : ∀ e ∈ G, ¬e⊆B) (δ : ℝ)
    (hδ : δ*(24*p^3*Fintype.card α)≤(B.card:ℝ)) :
    ∃ A : Finset α, (∀ e ∈ H, ¬e⊆A) ∧ δ*Fintype.card α≤(A.card:ℝ) := by
  obtain ⟨A,hA,hcard⟩ := htransfer B hB
  refine ⟨A,hA,?_⟩
  have hc : (B.card:ℝ)≤24*(p:ℝ)^3*A.card := by exact_mod_cast hcard
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  apply le_of_mul_le_mul_left (a := 24*(p:ℝ)^3) _ (by positivity)
  nlinarith only [hδ,hc]
end Assemble

#print axioms higher
#print axioms two
#print axioms model_card
#print axioms exists_regularization
#print axioms density_transfer
end
end Erdos773.MixedLayerRegularization
