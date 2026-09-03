import FormalConjecturesUtil

/-!
Local residue counts for pairs of split nonsingular binary quadratics.
These are finite-field calculations, not a density assertion.
-/
namespace Erdos1206.BinaryQuadraticLocalSieve
open Finset
open scoped Classical
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

noncomputable def affineRoots (a b c : K) : Finset K :=
  univ.filter (fun x => a*x^2+b*x+c=0)

lemma affineRoots_card_two (a b c : K) (ha : a ≠ 0) (h2 : (2:K) ≠ 0)
    (hD : b^2-4*a*c ≠ 0) (hDs : IsSquare (b^2-4*a*c)) :
    (affineRoots a b c).card=2 := by
  letI : NeZero (2:K) := ⟨h2⟩
  obtain ⟨s,hs⟩ := hDs
  have hs0 : s ≠ 0 := by intro hh; rw [hh,mul_zero] at hs; exact hD hs
  have hda : 2*a ≠ 0 := mul_ne_zero h2 ha
  have hs' : discrim a b c=s*s := by simpa only [discrim,pow_two] using hs
  have hne : (-b+s)/(2*a) ≠ (-b-s)/(2*a) := by
    intro hh
    have he := (div_left_inj' hda).mp hh
    have hz : (2:K)*s=0 := by linear_combination he
    exact mul_ne_zero h2 hs0 hz
  have he : affineRoots a b c={(-b+s)/(2*a),(-b-s)/(2*a)} := by
    ext x
    simp only [affineRoots,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
    simpa only [pow_two] using quadratic_eq_zero_iff ha hs' x
  rw [he,card_pair hne]

/-- Points on one of the specified lines, with their common origin counted
just once. -/
noncomputable def lineSet (R : Finset K) : Finset (K × K) :=
  insert (0,0) ((R ×ˢ (univ.erase (0:K))).image (fun x : K × K => (x.1*x.2,x.2)))

lemma lineSet_card (R : Finset K) :
    (lineSet R).card=1+R.card*(Fintype.card K-1) := by
  have hi : Set.InjOn (fun x : K × K => (x.1*x.2,x.2))
      (↑(R ×ˢ (univ.erase (0:K))) : Set (K × K)) := by
    intro x hx y hy he
    have hxy2 := congrArg Prod.snd he
    have hmul := congrArg Prod.fst he
    have hx0 : x.2 ≠ 0 := (mem_erase.mp (mem_product.mp hx).2).1
    have hxy1 : x.1=y.1 := by
      dsimp only at hxy2 hmul
      rw [← hxy2] at hmul
      exact mul_right_cancel₀ hx0 hmul
    exact Prod.ext hxy1 hxy2
  have hn : (0,0) ∉ (R ×ˢ (univ.erase (0:K))).image (fun x : K × K => (x.1*x.2,x.2)) := by
    rintro hh
    obtain ⟨x,hx,he⟩ := mem_image.mp hh
    have hx0 := (mem_erase.mp (mem_product.mp hx).2).1
    exact hx0 (congrArg Prod.snd he)
  rw [lineSet,card_insert_of_notMem hn,card_image_iff.mpr hi,card_product,
    card_erase_of_mem (mem_univ _),card_univ]
  omega

lemma mem_lineSet {R : Finset K} {x y : K} :
    (x,y) ∈ lineSet R ↔ (x=0 ∧ y=0) ∨ ∃ r ∈ R, x=r*y ∧ y ≠ 0 := by
  simp only [lineSet,mem_insert,Prod.mk.injEq,mem_image,mem_product,mem_erase,
    mem_univ,and_true,Prod.exists]
  constructor
  · rintro (h | ⟨r,t,⟨hr,ht⟩,he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r,hr,by rw [← he.2,← he.1],he.2 ▸ ht⟩
  · rintro (h | ⟨r,hr,hx,hy⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r,y,⟨hr,hy⟩,hx.symm,rfl⟩

lemma lineSet_quadratic_zero {a b c x y : K}
    (h : (x,y) ∈ lineSet (affineRoots a b c)) : a*x^2+b*x*y+c*y^2=0 := by
  rcases mem_lineSet.mp h with ⟨rfl,rfl⟩ | ⟨r,hr,rfl,hy⟩
  · simp
  · have hh := (mem_filter.mp hr).2
    linear_combination y^2*hh

lemma lineSet_pair_zero {a b c d e f x y : K}
    (h : (x,y) ∈ lineSet (affineRoots a b c ∪ affineRoots d e f)) :
    a*x^2+b*x*y+c*y^2=0 ∨ d*x^2+e*x*y+f*y^2=0 := by
  rcases mem_lineSet.mp h with ⟨rfl,rfl⟩ | ⟨r,hr,hx,hy⟩
  · left; simp
  · rcases mem_union.mp hr with hr | hr
    · left
      exact lineSet_quadratic_zero (mem_lineSet.mpr (Or.inr ⟨r,hr,hx,hy⟩))
    · right
      exact lineSet_quadratic_zero (mem_lineSet.mpr (Or.inr ⟨r,hr,hx,hy⟩))

theorem pair_lineSet_card (a b c d e f : K) (ha : a ≠ 0) (hd : d ≠ 0)
    (h2 : (2:K) ≠ 0)
    (hD₁ : b^2-4*a*c ≠ 0) (hs₁ : IsSquare (b^2-4*a*c))
    (hD₂ : e^2-4*d*f ≠ 0) (hs₂ : IsSquare (e^2-4*d*f))
    (hno : ∀ x : K, ¬ (a*x^2+b*x+c=0 ∧ d*x^2+e*x+f=0)) :
    (lineSet (affineRoots a b c ∪ affineRoots d e f)).card=1+4*(Fintype.card K-1) := by
  have hdis : Disjoint (affineRoots a b c) (affineRoots d e f) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hno x ⟨(mem_filter.mp hx).2,(mem_filter.mp hy).2⟩
  rw [lineSet_card,card_union_of_disjoint hdis,
    affineRoots_card_two a b c ha h2 hD₁ hs₁,affineRoots_card_two d e f hd h2 hD₂ hs₂]

#print axioms affineRoots_card_two
#print axioms pair_lineSet_card
end Erdos1206.BinaryQuadraticLocalSieve
