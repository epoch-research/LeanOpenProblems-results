import Submission.GrassmannFourChart
import Submission.VoltageFusion

/-! Arbitrary nonzero hyperplanes on the explicit Grassmannian four-chart.
All edge thinnings are allowed. This is not a bound for arbitrary graphs. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714SlicedBlocks
open Erdos714Packing
variable {X T C : Type*} [Fintype X] [Fintype T] [Fintype C]

def block (Z : X → Finset C) (R : X × T → Finset C) (x : X) (t : T) : Finset (Z x) :=
  univ.filter (fun c => c.val ∈ R (x,t))

omit [Fintype X] [Fintype T] [Fintype C] in
lemma block_free (Z : X → Finset C) (R : X × T → Finset C) (x : X)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence R)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (block Z R x)) := by
  rw [free_iff_no_rectangle _ (by decide)] at hf ⊢
  intro f g h
  let l : T ↪ X × T := ⟨fun t => (x,t), fun _ _ he => congrArg Prod.snd he⟩
  let e : Z x ↪ C := ⟨Subtype.val, Subtype.val_injective⟩
  apply hf (f.trans l) (g.trans e)
  intro i j
  exact (mem_filter.mp (h i j)).2

omit [Fintype X] [Fintype T] [Fintype C] in
lemma block_card (Z : X → Finset C) (R : X × T → Finset C)
    (hR : ∀ x t, R (x,t) ⊆ Z x) (x : X) (t : T) :
    (block Z R x t).card = (R (x,t)).card := by
  apply card_bij (fun c _ => c.val)
  · intro c hc
    exact (mem_filter.mp hc).2
  · intro c hc d hd he
    exact Subtype.ext he
  · intro c hc
    exact ⟨⟨c,hR x t hc⟩,mem_filter.mpr ⟨mem_univ _,hc⟩,rfl⟩

omit [Fintype C] in
/-- Slice sizes need not be uniform. The sum of their accessible-column
counts, rather than their maximum, controls the main term. -/
theorem fourth_power (Z : X → Finset C) (R : X × T → Finset C)
    (hR : ∀ x t, R (x,t) ⊆ Z x)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence R)) :
    (∑ p, (R p).card)^4 ≤
      24*Fintype.card T^3*(∑ x, (Z x).card)^4 +
      648*(Fintype.card X*Fintype.card T)^4 := by
  let e (x : X) := ∑ t, (R (x,t)).card
  let d (x : X) := e x-3*Fintype.card T
  have hb (x : X) : (d x)^4 ≤ 3*Fintype.card T^3*(Z x).card^4 := by
    have h := Erdos714Unbalanced.power_bound (block Z R x) (by decide : 1≤4)
      (block_free Z R x hf)
    simpa only [block_card Z R hR,Fintype.card_coe,show (4:ℕ)-1=3 from rfl] using h
  have hs : (∑ x, d x)^4 ≤ 3*Fintype.card T^3*(∑ x, (Z x).card)^4 := by
    simpa only [one_mul] using
      Erdos714FusionBounds.sum_relative_fourth d (fun x => (Z x).card)
        1 (3*Fintype.card T^3) (by decide) (fun x => by simpa only [one_mul] using hb x)
  have he : (∑ p, (R p).card) ≤ (∑ x, d x)+3*(Fintype.card X*Fintype.card T) := by
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ x, (d x+3*Fintype.card T) := sum_le_sum (fun x _ => by dsimp [e,d]; omega)
      _ = _ := by rw [sum_add_distrib]; simp; ring
  have hp := add_pow_le (Nat.zero_le (∑ x, d x))
    (Nat.zero_le (3*(Fintype.card X*Fintype.card T))) 4
  norm_num only at hp
  calc
    _ ≤ ((∑ x, d x)+3*(Fintype.card X*Fintype.card T))^4 := Nat.pow_le_pow_left he 4
    _ ≤ 8*((∑ x, d x)^4+(3*(Fintype.card X*Fintype.card T))^4) := hp
    _ ≤ 8*(3*Fintype.card T^3*(∑ x, (Z x).card)^4+
        (3*(Fintype.card X*Fintype.card T))^4) := by gcongr
    _ = _ := by ring

#print axioms fourth_power
end Erdos714SlicedBlocks

namespace Erdos714GrassmannHyperplanes
open Erdos714GrassmannFourChart Erdos714Packing
variable {F C : Type*} [Field F] [Fintype F] [Fintype C]

def neighbors (l : C → Ambient F) (c : C) : Finset (Point F) :=
  univ.filter (fun p => dot (l c) (chart p)=0)
def graph (l : C → Ambient F) : SimpleGraph (C ⊕ Point F) := incidence (neighbors l)
def goodGraph (l : C → Ambient F) : SimpleGraph (C ⊕ Point F) :=
  Erdos714BilinearProfiles.goodGraph (fun x c => profile (l c) x)
def badNeighbors (l : C → Ambient F) (c : C) : Finset (Point F) :=
  univ.filter (fun p => profile (l c) p.1=0)
def badGraph (l : C → Ambient F) : SimpleGraph (C ⊕ Point F) := incidence (badNeighbors l)
def zeroColumns (l : C → Ambient F) (x : F × F) : Finset C :=
  univ.filter (fun c => profile (l c) x=0)

lemma zero_columns_budget (l : C → Ambient F) (hl : ∀ c, l c ≠ 0)
    (hC : Fintype.card C ≤ Fintype.card F^4) :
    (∑ x, (zeroColumns l x).card) ≤ 2*Fintype.card F^5 := by
  have he : (∑ x, (zeroColumns l x).card) = ∑ c, (zeroProfiles (l c)).card := by
    simp only [zeroColumns,zeroProfiles,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  calc
    _ = ∑ c, (zeroProfiles (l c)).card := he
    _ ≤ ∑ _c : C, 2*Fintype.card F := sum_le_sum (fun c _ => zero_profile_bound (hl c))
    _ = Fintype.card C*(2*Fintype.card F) := by simp
    _ ≤ Fintype.card F^4*(2*Fintype.card F) := Nat.mul_le_mul_right _ hC
    _ = _ := by ring

lemma bad_thinning_bound (l : C → Ambient F) (hl : ∀ c, l c ≠ 0)
    (hC : Fintype.card C ≤ Fintype.card F^4)
    (H : SimpleGraph (C ⊕ Point F)) (hH : H ≤ badGraph l)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 1032*Fintype.card F^26 := by
  let S := Erdos714Unbalanced.neighborhoods H
  have hcomplete : H ≤ completeBipartiteGraph C (Point F) := by
    intro u v huv
    have h := hH huv
    cases u <;> cases v <;> simp_all [badGraph,incidence]
  have hi : incidence S=H := Erdos714Unbalanced.incidence_neighborhoods H hcomplete
  let R := dual S
  have hr : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence R) := by
    rw [free_iff_common_card _ (by decide)]
    apply (common_card_dual_iff S (by decide)).mp
    apply (free_iff_common_card S (by decide)).mp
    rwa [hi]
  have hR (x t : F × F) : R (x,t) ⊆ zeroColumns l x := by
    intro c hc
    have ha : H.Adj (.inl c) (.inr (x,t)) := (mem_filter.mp ((mem_dual S c (x,t)).mp hc)).2
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (hH ha)).2⟩
  have he : H.edgeFinset.card=∑ p, (R p).card := by
    rw [←hi,incidence_edges]
    exact (Erdos714Blowup.sum_dual_card S).symm
  have hb := Erdos714SlicedBlocks.fourth_power (zeroColumns l) R hR hr
  have hz := zero_columns_budget l hl hC
  have hcard : Fintype.card (F × F)=Fintype.card F^2 := by simp [pow_two]
  rw [hcard] at hb
  have h16 : Fintype.card F^16 ≤ Fintype.card F^26 :=
    pow_le_pow_right' Fintype.card_pos (by decide)
  calc
    _ = (∑ p, (R p).card)^4 := by rw [he]
    _ ≤ 24*(Fintype.card F^2)^3*(∑ x, (zeroColumns l x).card)^4+
        648*(Fintype.card F^2*Fintype.card F^2)^4 := hb
    _ ≤ 24*(Fintype.card F^2)^3*(2*Fintype.card F^5)^4+
        648*(Fintype.card F^2*Fintype.card F^2)^4 := by gcongr
    _ = 384*Fintype.card F^26+648*Fintype.card F^16 := by ring
    _ ≤ 384*Fintype.card F^26+648*Fintype.card F^26 := by gcongr
    _ = _ := by ring

omit [Fintype C] in
lemma host_le_sup (l : C → Ambient F) : graph l ≤ goodGraph l ⊔ badGraph l := by
  have he (c : C) (p : Point F) (h : dot (l c) (chart p)=0) :
      (goodGraph l).Adj (.inl c) (.inr p) ∨ (badGraph l).Adj (.inl c) (.inr p) := by
    by_cases hp : profile (l c) p.1=0
    · right
      exact mem_filter.mpr ⟨mem_univ _,hp⟩
    · left
      exact mem_filter.mpr ⟨mem_univ _,hp,(dot_eq_form (l c) p.1 p.2).symm.trans h⟩
  intro u v huv
  cases u with
  | inl c =>
    cases v with
    | inl d => exact False.elim huv
    | inr p => exact he c p ((mem_filter.mp huv).2)
  | inr p =>
    cases v with
    | inr q => exact False.elim huv
    | inl c => exact he c p ((mem_filter.mp huv).2)

/-- Coefficients may repeat and depend arbitrarily on their column. The
nonzero requirement is essential: zero hyperplanes would give a complete host. -/
theorem thinning_bound (l : C → Ambient F) (hl : ∀ c, l c ≠ 0)
    (hC : Fintype.card C ≤ Fintype.card F^4)
    (H : SimpleGraph (C ⊕ Point F)) (hH : H ≤ graph l)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 6635528256*Fintype.card F^27 := by
  let G := H ⊓ goodGraph l
  let B := H ⊓ badGraph l
  have hgf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free G := by
    intro h
    exact hf (h.mono_right inf_le_left)
  have hbf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free B := by
    intro h
    exact hf (h.mono_right inf_le_left)
  have hg : G.edgeFinset.card^4 ≤ 829440000*Fintype.card F^27 := by
    have ht := Erdos714BilinearProfiles.good_thinning_bound
      (fun x c => profile (l c) x) G inf_le_right hgf (by simp [pow_two]) hC
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using ht
  have hb : B.edgeFinset.card^4 ≤ 1032*Fintype.card F^26 := by
    have ht := bad_thinning_bound l hl hC B inf_le_right hbf
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using ht
  have hs : H ≤ G ⊔ B := by
    dsimp [G,B]
    rw [←inf_sup_left]
    exact le_inf le_rfl (hH.trans (host_le_sup l))
  have he : H.edgeFinset.card ≤ G.edgeFinset.card+B.edgeFinset.card := by
    have h := card_le_card (edgeFinset_mono hs)
    rw [edgeFinset_sup] at h
    exact h.trans (card_union_le _ _)
  have hp := add_pow_le (Nat.zero_le G.edgeFinset.card) (Nat.zero_le B.edgeFinset.card) 4
  norm_num only at hp
  have h26 : Fintype.card F^26 ≤ Fintype.card F^27 :=
    pow_le_pow_right' Fintype.card_pos (by decide)
  calc
    _ ≤ (G.edgeFinset.card+B.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
    _ ≤ 8*(G.edgeFinset.card^4+B.edgeFinset.card^4) := hp
    _ ≤ 8*(829440000*Fintype.card F^27+1032*Fintype.card F^26) := by gcongr
    _ ≤ 8*(829440000*Fintype.card F^27+1032*Fintype.card F^27) := by gcongr
    _ = _ := by ring

theorem size_budget (l : C → Ambient F) (hl : ∀ c, l c ≠ 0)
    (hC : Fintype.card C ≤ Fintype.card F^4)
    (H : SimpleGraph (C ⊕ Point F)) (hH : H ≤ graph l)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (D : ℕ) (he : Fintype.card F^7 ≤ D*H.edgeFinset.card) :
    Fintype.card F ≤ 6635528256*D^4 := by
  have hp : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(6635528256*D^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (D*H.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
      _ = D^4*H.edgeFinset.card^4 := by ring
      _ ≤ D^4*(6635528256*Fintype.card F^27) :=
        Nat.mul_le_mul_left _ (thinning_bound l hl hC H hH hf)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hp (pow_pos Fintype.card_pos 27)

#print axioms zero_columns_budget
#print axioms bad_thinning_bound
#print axioms thinning_bound
#print axioms size_budget
end Erdos714GrassmannHyperplanes
