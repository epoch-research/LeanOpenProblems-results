import FormalConjecturesUtil

/-!
# Erdős Problem 241

The conjecture remains unresolved. The checked auxiliary development below
recovers the cubic Bose–Chowla lower construction at prime-indexed lengths
and the elementary extremal-size bridge. These do not establish the sharp
asymptotic upper bound.
-/

open Filter Finset
open scoped Asymptotics

namespace Erdos241

/-- The maximum size of a subset of `{1,...,N}` with unique multiset `r`-sums. -/
noncomputable def f (N r : ℕ) : ℕ :=
  open scoped Classical in
  letI candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card

end Erdos241

namespace Erdos241.FourCircuitCompletion
/-- Indexed uniqueness of three-sums, with repeated coordinates allowed. -/
def ThreeUnique {α : Type*} (w : α → ℕ) : Prop :=
  ∀ a b c d e f, w a+w b+w c=w d+w e+w f →
    ({a,b,c} : Multiset α)={d,e,f}
end Erdos241.FourCircuitCompletion

namespace Erdos241.NaturalFourthEnergy
/-- The exact multiset condition from the definition of `f`, specialized to three. -/
def IsB3 (A : Finset ℕ) : Prop :=
  ∀ m₁ m₂ : Multiset ℕ, m₁.card=3 → m₂.card=3 →
    (∀ x∈m₁, x∈A) → (∀ x∈m₂, x∈A) → m₁.sum=m₂.sum → m₁=m₂
end Erdos241.NaturalFourthEnergy


/-! The cubic Bose–Chowla polynomial argument, separated from asymptotic claims. -/
open Finset Polynomial
open scoped Classical
namespace Erdos241.BoseChowlaCore
set_option maxHeartbeats 3000000
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

noncomputable def triplePoly (a b c : F) : F[X] := (X+C a)*(X+C b)*(X+C c)

lemma triple_monic (a b c : F) : IsMonicOfDegree (triplePoly a b c) 3 := by
  exact (IsMonicOfDegree.mul
    (IsMonicOfDegree.mul ⟨natDegree_X_add_C a,monic_X_add_C a⟩
      ⟨natDegree_X_add_C b,monic_X_add_C b⟩)
    ⟨natDegree_X_add_C c,monic_X_add_C c⟩)

lemma gen_add_ne_zero (pb : PowerBasis F K) (hd : pb.dim=3) (a : F) :
    pb.gen+algebraMap F K a≠0 := by
  intro ha
  have he : aeval pb.gen (X+C a)=0 := by simpa using ha
  have hh := pb.dim_le_natDegree_of_root (monic_X_add_C a).ne_zero he
  rw [hd,natDegree_X_add_C] at hh
  omega

lemma triple_roots (a b c : F) :
    (triplePoly a b c).roots=({-a,-b,-c} : Multiset F) := by
  rw [triplePoly,roots_mul (mul_ne_zero
    ((monic_X_add_C a).mul (monic_X_add_C b)).ne_zero (monic_X_add_C c).ne_zero),
    roots_mul (mul_ne_zero (monic_X_add_C a).ne_zero (monic_X_add_C b).ne_zero)]
  simp only [roots_X_add_C]
  rfl

/-- Equality of products of three affine-line elements determines the multiset of parameters. -/
theorem triple_product_unique (pb : PowerBasis F K) (hd : pb.dim=3)
    (a b c d e f : F)
    (he : (pb.gen+algebraMap F K a)*(pb.gen+algebraMap F K b)*(pb.gen+algebraMap F K c)=
      (pb.gen+algebraMap F K d)*(pb.gen+algebraMap F K e)*(pb.gen+algebraMap F K f)) :
    ({a,b,c} : Multiset F)={d,e,f} := by
  have hr : aeval pb.gen (triplePoly a b c-triplePoly d e f)=0 := by
    simpa only [map_sub,triplePoly,map_mul,map_add,aeval_X,aeval_C,sub_eq_zero] using he
  have hlt : (triplePoly a b c-triplePoly d e f).natDegree < 3 :=
    IsMonicOfDegree.natDegree_sub_lt (by decide) (triple_monic a b c) (triple_monic d e f)
  have hz : triplePoly a b c-triplePoly d e f=0 := by
    by_contra hn
    have hh := pb.dim_le_natDegree_of_root hn hr
    rw [hd] at hh
    omega
  have hp := sub_eq_zero.mp hz
  have hm := congrArg Polynomial.roots hp
  rw [triple_roots,triple_roots] at hm
  have hh := congrArg (Multiset.map (fun x : F => -x)) hm
  simpa using hh

variable [Fintype F] [Fintype K]

/-- A cyclic logarithm realizes the affine line as positive integer exponents. -/
theorem exists_exponents (pb : PowerBasis F K) (hd : pb.dim=3) :
    ∃ n : F → ℕ, Function.Injective n ∧
      (∀ a, 1 ≤ n a ∧ n a ≤ Fintype.card K-1) ∧
      (∀ a b c d e f, n a+n b+n c=n d+n e+n f →
        ({a,b,c} : Multiset F)={d,e,f}) := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α:=Kˣ)
  let line : F → Kˣ := fun a => Units.mk0 (pb.gen+algebraMap F K a) (gen_add_ne_zero pb hd a)
  have he (a : F) : ∃ n : ℕ, n < orderOf g ∧ g^n=line a := by
    have hm := (mem_zpowers_iff_mem_range_orderOf).mp (hg (line a))
    obtain ⟨n,hn,he⟩ := mem_image.mp hm
    exact ⟨n,mem_range.mp hn,he⟩
  choose ex hex heq using he
  have ho : orderOf g=Fintype.card K-1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,Nat.card_eq_fintype_card,Fintype.card_units]
  have hinj : Function.Injective ex := by
    intro a b hab
    have hu : line a=line b := (heq a).symm.trans ((congrArg (g^·) hab).trans (heq b))
    have hv := congrArg (fun u : Kˣ => (u : K)) hu
    change pb.gen+algebraMap F K a=pb.gen+algebraMap F K b at hv
    exact (algebraMap F K).injective (add_left_cancel hv)
  refine ⟨fun a => ex a+1,?_,?_,?_⟩
  · intro a b hab
    dsimp only at hab
    apply hinj
    omega
  · intro a
    dsimp only
    have hh := hex a
    rw [ho] at hh
    omega
  · intro a b c d e f hab
    dsimp only at hab
    have hs : ex a+ex b+ex c=ex d+ex e+ex f := by omega
    have hp : line a*line b*line c=line d*line e*line f := by
      have hh := congrArg (g^·) hs
      simpa only [pow_add,heq] using hh
    have hp' := congrArg (fun u : Kˣ => (u : K)) hp
    apply triple_product_unique pb hd a b c d e f
    simpa only [Units.val_mul,Units.val_mk0] using hp'

end Erdos241.BoseChowlaCore


/-! Prime-indexed Bose–Chowla sets satisfying the exact natural-multiset B3 condition. -/
open Finset
open scoped Classical
namespace Erdos241.NaturalBoseChowla
open FourCircuitCompletion NaturalFourthEnergy
set_option maxHeartbeats 3000000

lemma image_isB3 {α : Type*} [Fintype α] [DecidableEq α]
    (n : α → ℕ) (hn : ThreeUnique n) : IsB3 (univ.image n) := by
  intro m₁ m₂ h₁ h₂ hm₁ hm₂ hs
  obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp h₁
  obtain ⟨d,e,f,rfl⟩ := Multiset.card_eq_three.mp h₂
  obtain ⟨a',ha,rfl⟩ := mem_image.mp (hm₁ a (by simp))
  obtain ⟨b',hb,rfl⟩ := mem_image.mp (hm₁ b (by simp))
  obtain ⟨c',hc,rfl⟩ := mem_image.mp (hm₁ c (by simp))
  obtain ⟨d',hd,rfl⟩ := mem_image.mp (hm₂ d (by simp))
  obtain ⟨e',he,rfl⟩ := mem_image.mp (hm₂ e (by simp))
  obtain ⟨f',hf,rfl⟩ := mem_image.mp (hm₂ f (by simp))
  have hsum : n a'+n b'+n c'=n d'+n e'+n f' := by simpa [add_assoc] using hs
  have hh := congrArg (Multiset.map n) (hn a' b' c' d' e' f' hsum)
  simpa using hh

/-- Bose–Chowla's cubic lower construction, with positive integer representatives. -/
theorem exists_set (p : ℕ) (hp : p.Prime) :
    ∃ A : Finset ℕ, A⊆Icc 1 (p^3-1) ∧ A.card=p ∧ IsB3 A := by
  letI : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p 3
  letI : Fintype K := Fintype.ofFinite K
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod p) K
  have hd : pb.dim=3 := by
    rw [←pb.finrank]
    exact GaloisField.finrank p (by decide)
  have hK : Fintype.card K=p^3 := by
    rw [←Nat.card_eq_fintype_card]
    exact GaloisField.card p 3 (by decide)
  obtain ⟨n,hi,hr,hu⟩ := BoseChowlaCore.exists_exponents pb hd
  refine ⟨univ.image n,?_,?_,image_isB3 n hu⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    have hh := hr a
    rw [hK] at hh
    exact mem_Icc.mpr hh
  · rw [card_image_of_injective _ hi,card_univ,ZMod.card]

end Erdos241.NaturalBoseChowla


/-! The finite extremal problem, developed without importing the admitted conjecture. -/
open Finset Filter
open scoped Classical
namespace Erdos241.ExtremalB3
open NaturalFourthEnergy
set_option maxHeartbeats 3000000

noncomputable def candidates (N : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 N).powerset.filter IsB3

noncomputable def maxSize (N : ℕ) : ℕ := (candidates N).sup card

lemma mem_candidates {N : ℕ} {A : Finset ℕ} :
    A∈candidates N ↔ A⊆Icc 1 N ∧ IsB3 A := by
  simp [candidates]

lemma empty_isB3 : IsB3 (∅ : Finset ℕ) := by
  intro m₁ m₂ h₁ h₂ hm₁ hm₂ hs
  obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp h₁
  have ha := hm₁ a (by simp)
  simp at ha

lemma candidates_nonempty (N : ℕ) : (candidates N).Nonempty :=
  ⟨∅,mem_candidates.mpr ⟨empty_subset _,empty_isB3⟩⟩

lemma card_le_maxSize {N : ℕ} {A : Finset ℕ} (hsub : A⊆Icc 1 N) (hA : IsB3 A) :
    A.card ≤ maxSize N := le_sup (mem_candidates.mpr ⟨hsub,hA⟩)

lemma exists_maximizer (N : ℕ) :
    ∃ A : Finset ℕ, A⊆Icc 1 N ∧ IsB3 A ∧ A.card=maxSize N := by
  obtain ⟨A,hA,he⟩ := exists_mem_eq_sup (candidates N) (candidates_nonempty N) card
  exact ⟨A,(mem_candidates.mp hA).1,(mem_candidates.mp hA).2,he.symm⟩

lemma monotone_maxSize : Monotone maxSize := by
  intro N M hNM
  apply Finset.sup_le
  intro A hA
  obtain ⟨hsub,hB⟩ := mem_candidates.mp hA
  apply card_le_maxSize ?_ hB
  intro x hx
  obtain ⟨hl,hu⟩ := mem_Icc.mp (hsub hx)
  exact mem_Icc.mpr ⟨hl,hu.trans hNM⟩

lemma maxSize_le (N : ℕ) : maxSize N ≤ N := by
  obtain ⟨A,hsub,hA,he⟩ := exists_maximizer N
  rw [←he]
  have hh := card_le_card hsub
  simpa using hh

lemma prime_lower_bound {p : ℕ} (hp : p.Prime) : p ≤ maxSize (p^3-1) := by
  obtain ⟨A,hsub,hcard,hA⟩ := NaturalBoseChowla.exists_set p hp
  simpa only [hcard] using card_le_maxSize hsub hA

lemma tendsto_maxSize : Tendsto maxSize atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  obtain ⟨p,hbp,hp⟩ := Nat.exists_infinite_primes b
  exact ⟨p^3-1,fun n hn => hbp.trans ((prime_lower_bound hp).trans (monotone_maxSize hn))⟩

/-- Infinitely far out, the cube of the extremal cardinality is at least `N+1`. -/
lemma arbitrarily_large_cubic_lower (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ N+1 ≤ (maxSize N)^3 := by
  obtain ⟨p,hMp,hp⟩ := Nat.exists_infinite_primes (M+2)
  have hp3 : p ≤ p^3 := Nat.le_self_pow (by decide) p
  have hp0 : 0 < p^3 := pow_pos hp.pos 3
  refine ⟨p^3-1,by omega,?_⟩
  have hcube := Nat.pow_le_pow_left (prime_lower_bound hp) 3
  omega

end Erdos241.ExtremalB3

namespace Erdos241

lemma f_three_eq_maxSize (N : ℕ) : f N 3=ExtremalB3.maxSize N := rfl

lemma f_three_prime_lower {p : ℕ} (hp : p.Prime) : p ≤ f (p^3-1) 3 := by
  rw [f_three_eq_maxSize]
  exact ExtremalB3.prime_lower_bound hp

lemma f_three_monotone : Monotone (fun N => f N 3) := by
  simpa only [f_three_eq_maxSize] using ExtremalB3.monotone_maxSize

lemma f_three_tendsto : Tendsto (fun N => f N 3) atTop atTop := by
  simpa only [f_three_eq_maxSize] using ExtremalB3.tendsto_maxSize

lemma arbitrarily_large_f_cubic_lower (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ N+1 ≤ (f N 3)^3 := by
  simpa only [f_three_eq_maxSize] using ExtremalB3.arbitrarily_large_cubic_lower M

theorem erdos_241 :
    (fun N ↦ (f N 3 : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3)) := by
  sorry

end Erdos241
