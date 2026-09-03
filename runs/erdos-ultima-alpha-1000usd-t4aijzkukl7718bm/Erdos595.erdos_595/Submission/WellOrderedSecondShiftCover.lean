import Submission.SecondArcBacktracking
import Submission.LargeSecondShiftExponential
import Submission.ShiftExponentialCover

/-!
All well-ordered second-shift domains satisfying the uncountable chromatic
hypothesis are excluded as exponential witnesses with countable K4-free targets.
The finite backtracking argument, not a larger Ramsey host, supplies the cover.
This is not a settlement of Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph Cardinal
namespace Erdos595WellOrderedSecondShift
open Erdos595MiddleCorner Erdos595SecondShiftExponential

variable {A : Type*} [LinearOrder A]

/-- An injection into two iterated powersets of N gives a countable proper
coloring of the second ordered-shift graph. -/
theorem coloring_of_encoding (e : A → Set (Set ℕ)) (he : Function.Injective e) :
    Nonempty ((oneGraph A).Coloring ℕ) := by
  classical
  let P := {p : A × A // p.1 < p.2}
  have hd (p : P) : ∃ S : Set ℕ,
      decide (S ∈ e p.val.1) ≠ decide (S ∈ e p.val.2) := by
    by_contra hn
    push_neg at hn
    apply p.property.ne
    apply he
    ext S
    exact decide_eq_decide.mp (hn S)
  choose d hd using hd
  let bit : P → Bool := fun p => decide (d p ∈ e p.val.1)
  let code : P → ℕ → Bool := fun p n => match n with
    | 0 => bit p
    | n+1 => decide (n ∈ d p)
  have hc (a b c : A) (hab : a < b) (hbc : b < c) :
      code ⟨(a,b),hab⟩ ≠ code ⟨(b,c),hbc⟩ := by
    intro hh
    let p : P := ⟨(a,b),hab⟩
    let q : P := ⟨(b,c),hbc⟩
    have hD : d p = d q := by
      ext n
      exact decide_eq_decide.mp (congrFun hh (n+1))
    have hbit := congrFun hh 0
    change decide (d p ∈ e a) = decide (d q ∈ e b) at hbit
    rw [← hD] at hbit
    exact hd p hbit
  have hx (x : Triple A) : ∃ n,
      code ⟨(x.a,x.b),x.ab⟩ n ≠ code ⟨(x.b,x.c),x.bc⟩ n := by
    by_contra hn
    push_neg at hn
    exact hc x.a x.b x.c x.ab x.bc (funext hn)
  choose n hn using hx
  let col : Triple A → ℕ × Bool := fun x =>
    (n x,code ⟨(x.a,x.b),x.ab⟩ (n x))
  have hforward (x y : Triple A) (hxy : One x y) : col x ≠ col y := by
    intro hh
    have hN := congrArg Prod.fst hh
    have hB := congrArg Prod.snd hh
    change n x = n y at hN
    change code ⟨(x.a,x.b),x.ab⟩ (n x) = code ⟨(y.a,y.b),y.ab⟩ (n y) at hB
    have hP : (⟨(x.b,x.c),x.bc⟩ : P) = ⟨(y.a,y.b),y.ab⟩ := by
      apply Subtype.ext
      exact Prod.ext hxy.1 hxy.2
    apply hn x
    rw [hP,hN]
    simpa only [hN] using hB
  obtain ⟨enc,henc⟩ := exists_injective_nat (ℕ × Bool)
  refine ⟨SimpleGraph.Coloring.mk (enc ∘ col) ?_⟩
  intro x y hxy hh
  have hh' := henc hh
  exact hxy.elim (fun h => hforward x y h hh') (fun h => hforward y x h hh'.symm)

/-- The precise cardinal lower bound needed below. -/
theorem size_lower {A : Type} [LinearOrder A]
    (hA : IsEmpty ((oneGraph A).Coloring ℕ)) :
    Cardinal.mk (Set (Set ℕ)) < Cardinal.mk A := by
  by_contra hn
  have hle := le_of_not_gt hn
  have hex : Nonempty (A ↪ Set (Set ℕ)) :=
    Cardinal.lift_mk_le'.mp (by simpa only [Cardinal.lift_uzero] using hle)
  obtain ⟨e⟩ := hex
  exact hA.false (coloring_of_encoding e e.injective).some

private lemma prod_bound {X Y : Type} {κ : Cardinal} (hκ : ℵ₀ ≤ κ)
    (hX : #X ≤ κ) (hY : #Y ≤ κ) : #(X × Y) ≤ κ := by
  rw [Cardinal.mk_prod,Cardinal.lift_uzero,Cardinal.lift_uzero]
  exact (mul_le_mul' hX hY).trans_eq (Cardinal.mul_eq_self hκ)

private def bicliqueCode {X : Type} (R : X → X → Prop)
    (p : Erdos595DirectedRight.Biclique R) : Set (Bool × X) :=
  {x | if x.1 then x.2 ∈ p.val.2 else x.2 ∈ p.val.1}

private lemma bicliqueCode_injective {X : Type} (R : X → X → Prop) :
    Function.Injective (bicliqueCode R) := by
  intro p q hh
  apply Subtype.ext
  apply Prod.ext
  · ext x
    have h := congrArg (fun S : Set (Bool × X) => (false,x) ∈ S) hh
    simpa only [bicliqueCode,Set.mem_setOf_eq,Bool.false_eq_true,if_false] using Iff.of_eq h
  · ext x
    have h := congrArg (fun S : Set (Bool × X) => (true,x) ∈ S) hh
    simpa only [bicliqueCode,Set.mem_setOf_eq,if_true] using Iff.of_eq h

private lemma biclique_bound {X : Type} (R : X → X → Prop) {κ : Cardinal}
    (hκ : ℵ₀ ≤ κ) (hX : #X ≤ κ) :
    #(Erdos595DirectedRight.Biclique R) ≤ 2 ^ κ := by
  have hp : #(Bool × X) ≤ κ := prod_bound hκ (Cardinal.mk_le_aleph0.trans hκ) hX
  calc
    #(Erdos595DirectedRight.Biclique R) ≤ #(Set (Bool × X)) :=
      Cardinal.mk_le_of_injective (bicliqueCode_injective R)
    _ = 2 ^ #(Bool × X) := Cardinal.mk_set
    _ ≤ 2 ^ κ := Cardinal.power_le_power_left (by simp) hp

/-- The canonical profile palette never exceeds two powersets of N. -/
theorem palette_bound {W : Type} [Countable W] (H : SimpleGraph W) :
    #(Palette H) ≤ #(Set (Set ℕ)) := by
  have h₁ : #(Erdos595DirectedRight.Biclique H.Adj) ≤ Cardinal.continuum := by
    simpa only [Cardinal.two_power_aleph0] using
      biclique_bound H.Adj (le_refl ℵ₀) Cardinal.mk_le_aleph0
  have h₂ : #(Erdos595DirectedRight.Biclique (Erdos595DirectedRight.right H.Adj)) ≤
      #(Set (Set ℕ)) := by
    simpa only [Cardinal.mk_set,Cardinal.mk_nat,Cardinal.two_power_aleph0] using
      biclique_bound (Erdos595DirectedRight.right H.Adj) Cardinal.aleph0_le_continuum h₁
  exact prod_bound (Cardinal.infinite_iff.mp inferInstance) h₂ (le_refl _)

/-- An arbitrary well-ordered high-chromatic second-shift domain contains
the canonical index required by the countable target. -/
theorem canonical_embedding {A W : Type} [LinearOrder A] [WellFoundedLT A]
    [Countable W] (H : SimpleGraph W) (hA : IsEmpty ((oneGraph A).Coloring ℕ)) :
    Nonempty (CanonicalIndex H ↪o A) := by
  have hp : max ℵ₀ #(Palette H) ≤ #(Set (Set ℕ)) :=
    max_le (Cardinal.infinite_iff.mp inferInstance) (palette_bound H)
  have hcard : Order.succ (max ℵ₀ #(Palette H)) ≤ #A :=
    Order.succ_le_iff.mpr (hp.trans_lt (size_lower hA))
  have ht : Ordinal.type (fun x y : CanonicalIndex H => x < y) ≤
      Ordinal.type (fun x y : A => x < y) := by
    rw [Ordinal.type_toType]
    exact (Cardinal.ord_le_ord.mpr hcard).trans (Cardinal.ord_le_type _)
  obtain ⟨e⟩ := Ordinal.type_le_iff.mp ht
  exact ⟨OrderEmbedding.ofStrictMono e (fun _ _ h => e.map_rel_iff.mpr h)⟩

/-- The well-ordered intermediate domains are now excluded as well. -/
theorem all_well_ordered_domains_cover {A W : Type} [LinearOrder A] [WellFoundedLT A]
    [Countable W] (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (hA : IsEmpty ((oneGraph A).Coloring ℕ)) :
    Erdos595Work.IsCountableUnionOfTriangleFree
      (Erdos595Exponential.exponential H (oneGraph A) hA) := by
  obtain ⟨e⟩ := canonical_embedding H hA
  exact Erdos595LargeSecondShiftExponential.cover_of_domain_hom H
    (oneGraph (CanonicalIndex H)) (oneGraph A) (canonical_not_colorable H) hA
    (Erdos595LargeSecondShiftExponential.oneGraphMap e)
    (Erdos595SecondArcBacktracking.canonical_secondShift_cover H hH)

#print axioms coloring_of_encoding
#print axioms canonical_embedding
#print axioms all_well_ordered_domains_cover
end Erdos595WellOrderedSecondShift
