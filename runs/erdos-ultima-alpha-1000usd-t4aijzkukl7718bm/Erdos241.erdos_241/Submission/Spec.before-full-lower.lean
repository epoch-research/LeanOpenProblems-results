import FormalConjecturesUtil

/-!
# Erdős Problem 241

The conjecture remains unresolved. The checked auxiliary development below
recovers the cubic Bose–Chowla lower construction at prime-indexed lengths,
the extremal-size bridge, and the elementary asymptotic cubic upper bound
with constant four. These do not establish the sharp constant-one asymptotic.
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


/- The cubic Bose–Chowla polynomial argument, separated from asymptotic claims. -/
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


/- Prime-indexed Bose–Chowla sets satisfying the exact natural-multiset B3 condition. -/
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


/- The finite extremal problem, developed without importing the admitted conjecture. -/
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

namespace Erdos241.FourCircuitCompletion
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]
omit [DecidableEq α] in
lemma signed_unique {w : α → ℕ} (hw : ThreeUnique w)
    {a b c d e f : α} (hca : c≠a) (hcb : c≠b)
    (he : w a+w b+w f=w d+w e+w c) :
    c=f ∧ ({a,b} : Multiset α)={d,e} := by
  have hh := hw a b f d e c he
  have hcf : c=f := by
    have hm : c∈({a,b,f} : Multiset α) := by rw [hh]; simp
    simpa [hca,hcb] using hm
  refine ⟨hcf,?_⟩
  subst f
  apply add_right_cancel (b:=({c} : Multiset α))
  simpa using hh

end Erdos241.FourCircuitCompletion

namespace Erdos241.NaturalFourthEnergy
open FourCircuitCompletion
lemma indexed_unique {A : Finset ℕ} (hA : IsB3 A) : ThreeUnique (fun a : A => a.val) := by
  intro a b c d e f he
  have hm : ({a.val,b.val,c.val} : Multiset ℕ)={d.val,e.val,f.val} := by
    apply hA
    · simp
    · simp
    · intro x hx
      simp at hx
      rcases hx with rfl|rfl|rfl
      · exact a.prop
      · exact b.prop
      · exact c.prop
    · intro x hx
      simp at hx
      rcases hx with rfl|rfl|rfl
      · exact d.prop
      · exact e.prop
      · exact f.prop
    · simpa [add_assoc] using he
  apply (Multiset.map_eq_map (f:=fun x : A => x.val) Subtype.val_injective).mp
  simpa using hm

end Erdos241.NaturalFourthEnergy

namespace Erdos241.FourthEnergyTupleBasics
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]
/-- The multiset of coordinates, retaining every repetition. -/
def tupleMultiset {n : ℕ} (t : Fin n → α) : Multiset α := ∑ i, {t i}

lemma tupleMultiset_eq_coe {n : ℕ} (t : Fin n → α) :
    tupleMultiset t=(List.ofFn t : Multiset α) := by
  rw [tupleMultiset,←List.sum_ofFn]
  have he : List.ofFn (fun i => ({t i} : Multiset α))=(List.ofFn t).map (fun x => ({x} : Multiset α)) := by
    rw [List.map_ofFn]
    rfl
  rw [he]
  generalize List.ofFn t=l
  induction l with
  | nil => simp
  | cons a l ih => simpa [ih]

variable [Fintype α]
lemma multiset_fiber_card {n : ℕ} (m : Multiset α) :
    (univ.filter (fun t : Fin n → α => tupleMultiset t=m)).card ≤ n.factorial := by
  let S := univ.filter (fun t : Fin n → α => tupleMultiset t=m)
  by_cases hs : S.Nonempty
  · obtain ⟨u,hu⟩ := hs
    have hum : tupleMultiset u=m := (mem_filter.mp hu).2
    have hsub : S.image List.ofFn ⊆ (List.ofFn u).permutations.toFinset := by
      intro l hl
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hl
      apply List.mem_toFinset.mpr
      apply List.mem_permutations.mpr
      apply Multiset.coe_eq_coe.mp
      rw [←tupleMultiset_eq_coe,←tupleMultiset_eq_coe,hum]
      exact (mem_filter.mp ht).2
    calc
      _ = (S.image List.ofFn).card := (card_image_of_injective _ List.ofFn_injective).symm
      _ ≤ (List.ofFn u).permutations.toFinset.card := card_le_card hsub
      _ ≤ (List.ofFn u).permutations.length := List.toFinset_card_le _
      _ = n.factorial := by rw [List.length_permutations,List.length_ofFn]
  · have he : S=∅ := not_nonempty_iff_eq_empty.mp hs
    change S.card ≤ _
    rw [he,card_empty]
    exact Nat.zero_le _

lemma card_bound_of_fibers {β : Type*} [DecidableEq β] (S : Finset α) (T : Finset β)
    (f : α → β) (M : ℕ) (hmap : ∀ a∈S, f a∈T)
    (hM : ∀ b∈T, (S.filter (fun a => f a=b)).card ≤ M) : S.card ≤ T.card*M := by
  rw [card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ _b∈T, M := sum_le_sum hM
    _ = T.card*M := by simp

end Erdos241.FourthEnergyTupleBasics

namespace Erdos241.SignedShiftEnergy
open Finset
open scoped Classical
section Generic
variable {U V : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]

noncomputable def fiber (g : U → V) (v : V) : Finset U :=
  univ.filter (fun u => g u=v)

noncomputable def collisions (g : U → V) : Finset (U × U) :=
  univ.filter (fun p => g p.1=g p.2)

lemma collision_fiber (g : U → V) (v : V) :
    (collisions g).filter (fun p => g p.1=v) = (fiber g v) ×ˢ (fiber g v) := by
  ext p
  simp only [collisions,fiber,mem_filter,mem_univ,true_and,mem_product]
  constructor
  · rintro ⟨h,hv⟩
    exact ⟨hv,h.symm.trans hv⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨h₁.trans h₂.symm,h₁⟩

lemma sum_fiber_sq_le (g : U → V) (D : Finset V) :
    ∑ v∈D, (fiber g v).card^2 ≤ (collisions g).card := by
  have hf (v : V) : (fiber g v).card^2 =
      ((collisions g).filter (fun p => g p.1=v)).card := by
    rw [collision_fiber,card_product,pow_two]
  simp_rw [hf]
  rw [sum_card_fiberwise_eq_card_filter]
  exact card_filter_le _ _

lemma sum_fiber_sq_cauchy (g : U → V) (D : Finset V) :
    (∑ v∈D, (fiber g v).card)^2 ≤ D.card*(collisions g).card := by
  have hc := sum_mul_sq_le_sq_mul_sq D (fun _ => (1 : ℕ)) (fun v => (fiber g v).card)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hc
  exact hc.trans (Nat.mul_le_mul_left D.card (sum_fiber_sq_le g D))
end Generic

variable {α : Type*} [LinearOrder α] [Fintype α]

/-- The signed shift `a+b-c-d` is integer-valued, so no subtraction is truncated. -/
def shift (w : α → ℕ) (t : Fin 4 → α) : ℤ :=
  (w (t 0) : ℤ)+w (t 1)-w (t 2)-w (t 3)

noncomputable def representations (A : Finset ℕ) (d : ℤ) : ℕ :=
  (fiber (shift (fun a : A => a.val)) d).card

end Erdos241.SignedShiftEnergy


/- Pointwise bounds with the exceptional difference shifts retained. -/
open Finset
open scoped Classical
namespace Erdos241.PointwiseShiftBound
open FourCircuitCompletion FourthEnergyTupleBasics SignedShiftEnergy
set_option maxHeartbeats 3000000
variable {α : Type*} [LinearOrder α] [Fintype α]

def IsDifference (w : α → ℕ) (d : ℤ) : Prop :=
  ∃ a b, (w a : ℤ)-w b=d

def lastTwo (t : Fin 4 → α) : Fin 2 → α := ![t 2,t 3]

lemma nonshared {w : α → ℕ} {d : ℤ} (hd : ¬IsDifference w d)
    {u : Fin 4 → α} (hu : shift w u=d) : u 1≠u 2 ∧ u 1≠u 3 := by
  constructor
  · intro he
    apply hd
    refine ⟨u 0,u 3,?_⟩
    simp only [shift,he] at hu
    omega
  · intro he
    apply hd
    refine ⟨u 0,u 2,?_⟩
    simp only [shift,he] at hu
    omega

lemma fixed_first {w : α → ℕ} (hw : ThreeUnique w) {d : ℤ}
    (hd : ¬IsDifference w d) {t u : Fin 4 → α}
    (ht : shift w t=d) (hu : shift w u=d) (h0 : t 0=u 0) :
    t 1=u 1 ∧ tupleMultiset (lastTwo t)=tupleMultiset (lastTwo u) := by
  obtain ⟨hu12,hu13⟩ := nonshared hd hu
  have he : w (u 2)+w (u 3)+w (t 1)=w (t 2)+w (t 3)+w (u 1) := by
    simp only [shift,h0] at ht hu
    omega
  obtain ⟨he1,he2⟩ := signed_unique hw hu12 hu13 he
  refine ⟨he1.symm,?_⟩
  simpa [tupleMultiset,lastTwo,Fin.sum_univ_succ] using he2.symm

/-- The `2k` estimate excludes the shifts in `A-A`. -/
theorem non_difference_bound {w : α → ℕ} (hw : ThreeUnique w) {d : ℤ}
    (hd : ¬IsDifference w d) :
    (fiber (shift w) d).card ≤ 2*Fintype.card α := by
  have hh := card_bound_of_fibers (fiber (shift w) d) univ (fun t => t 0) 2
    (by intros; exact mem_univ _)
  have hf : ∀ a∈(univ : Finset α),
      ((fiber (shift w) d).filter (fun t => t 0=a)).card ≤ 2 := by
    intro a ha
    let T := (fiber (shift w) d).filter (fun t => t 0=a)
    by_cases hT : T.Nonempty
    · obtain ⟨u,hu⟩ := hT
      have hu0 : u 0=a := (mem_filter.mp hu).2
      have hud : shift w u=d := (mem_filter.mp (mem_filter.mp hu).1).2
      have ht0 (t) (ht : t∈T) : t 0=u 0 := (mem_filter.mp ht).2.trans hu0.symm
      have htu (t) (ht : t∈T) : t 1=u 1 ∧
          tupleMultiset (lastTwo t)=tupleMultiset (lastTwo u) :=
        fixed_first hw hd (mem_filter.mp (mem_filter.mp ht).1).2 hud (ht0 t ht)
      have hmap : ∀ t∈T,
          lastTwo t∈univ.filter (fun v : Fin 2 → α => tupleMultiset v=tupleMultiset (lastTwo u)) := by
        intro t ht
        exact mem_filter.mpr ⟨mem_univ _,(htu t ht).2⟩
      have hinj : Set.InjOn lastTwo (T : Set (Fin 4 → α)) := by
        intro t ht v hv he
        funext i
        fin_cases i
        · exact (ht0 t ht).trans (ht0 v hv).symm
        · exact (htu t ht).1.trans (htu v hv).1.symm
        · have hx := congrFun he 0
          simpa [lastTwo] using hx
        · have hx := congrFun he 1
          simpa [lastTwo] using hx
      have hc := card_le_card_of_injOn lastTwo hmap hinj
      have hm := multiset_fiber_card (n:=2) (tupleMultiset (lastTwo u))
      norm_num only [Nat.factorial] at hm
      exact hc.trans hm
    · have he : T=∅ := not_nonempty_iff_eq_empty.mp hT
      change T.card ≤ 2
      simp [he]
  simpa [mul_comm] using hh hf

lemma pair_eq_cases {a b c d : α} (h : ({a,b} : Multiset α)={c,d}) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hm : a∈({c,d} : Multiset α) := by rw [←h]; simp
  have ha : a=c ∨ a=d := by simpa using hm
  rcases ha with ha|ha
  · subst c
    exact Or.inl ⟨rfl,Multiset.singleton_inj.mp ((Multiset.cons_inj_right a).mp h)⟩
  · subst d
    rw [Multiset.pair_comm c a] at h
    exact Or.inr ⟨rfl,Multiset.singleton_inj.mp ((Multiset.cons_inj_right a).mp h)⟩

def exceptionTuple (a b : α) (p : Fin 2 × Fin 2 × α) : Fin 4 → α :=
  ![if p.1=0 then a else p.2.2, if p.1=0 then p.2.2 else a,
    if p.2.1=0 then b else p.2.2, if p.2.1=0 then p.2.2 else b]

lemma exception_form {w : α → ℕ} (hw : ThreeUnique w) {d : ℤ} (hd : d≠0)
    {a b : α} (hab : (w a : ℤ)-w b=d) {t : Fin 4 → α} (ht : shift w t=d) :
    ∃ p : Fin 2 × Fin 2 × α, exceptionTuple a b p=t := by
  have hab' : a≠b := by intro he; simp [he] at hab; exact hd hab.symm
  have he : w (t 0)+w (t 1)+w b=w (t 2)+w (t 3)+w a := by
    simp only [shift] at ht
    omega
  have h3 := hw (t 0) (t 1) b (t 2) (t 3) a he
  have hm : a∈({t 0,t 1,b} : Multiset α) := by rw [h3]; simp
  have ha : a=t 0 ∨ a=t 1 := by simpa [hab'] using hm
  rcases ha with ha|ha
  · have hp : ({t 1,b} : Multiset α)={t 2,t 3} := by
      apply (Multiset.cons_inj_right a).mp
      rw [←ha] at h3
      change a ::ₘ (t 1) ::ₘ b ::ₘ 0 = (t 2) ::ₘ (t 3) ::ₘ a ::ₘ 0 at h3
      rw [Multiset.cons_swap (t 3) a,Multiset.cons_swap (t 2) a] at h3
      exact h3
    rcases pair_eq_cases hp with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · refine ⟨(0,1,t 1),?_⟩
      funext i
      fin_cases i <;> simp [exceptionTuple,ha,h₁,h₂]
    · refine ⟨(0,0,t 1),?_⟩
      funext i
      fin_cases i <;> simp [exceptionTuple,ha,h₁,h₂]
  · have hp : ({t 0,b} : Multiset α)={t 2,t 3} := by
      apply (Multiset.cons_inj_right a).mp
      rw [←ha] at h3
      change (t 0) ::ₘ a ::ₘ b ::ₘ 0 = (t 2) ::ₘ (t 3) ::ₘ a ::ₘ 0 at h3
      rw [Multiset.cons_swap (t 0) a,Multiset.cons_swap (t 3) a,Multiset.cons_swap (t 2) a] at h3
      exact h3
    rcases pair_eq_cases hp with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · refine ⟨(1,1,t 0),?_⟩
      funext i
      fin_cases i <;> simp [exceptionTuple,ha,h₁,h₂]
    · refine ⟨(1,0,t 0),?_⟩
      funext i
      fin_cases i <;> simp [exceptionTuple,ha,h₁,h₂]

/-- At a nonzero difference, there are at most `4k` ordered representations. -/
theorem difference_bound {w : α → ℕ} (hw : ThreeUnique w) {d : ℤ} (hd : d≠0)
    (hD : IsDifference w d) :
    (fiber (shift w) d).card ≤ 4*Fintype.card α := by
  obtain ⟨a,b,hab⟩ := hD
  have hs : fiber (shift w) d ⊆ univ.image (exceptionTuple a b) := by
    intro t ht
    obtain ⟨p,hp⟩ := exception_form hw hd hab (mem_filter.mp ht).2
    exact mem_image.mpr ⟨p,mem_univ _,hp⟩
  have hc := (card_le_card hs).trans card_image_le
  simpa [Fintype.card_prod,←mul_assoc] using hc

noncomputable def differenceSet (w : α → ℕ) : Finset ℤ :=
  univ.image (fun p : α × α => (w p.1 : ℤ)-w p.2)

lemma mem_differenceSet (w : α → ℕ) (d : ℤ) :
    d∈differenceSet w ↔ IsDifference w d := by
  simp [differenceSet,IsDifference,Prod.exists]

lemma difference_card (w : α → ℕ) : (differenceSet w).card ≤ (Fintype.card α)^2 := by
  have hc : (differenceSet w).card ≤ (univ : Finset (α × α)).card := card_image_le
  simpa [Fintype.card_prod,pow_two] using hc

/-- A finite window bound with both nonzero-difference exceptions and repetitions included. -/
theorem window_bound {w : α → ℕ} (hw : ThreeUnique w) (D : Finset ℤ) (h0 : 0∉D) :
    ∑ d∈D, (fiber (shift w) d).card ≤
      2*Fintype.card α*D.card+2*(Fintype.card α)^3 := by
  let E := D.filter (IsDifference w)
  let G := D.filter (fun d => ¬IsDifference w d)
  have hc : E.card+G.card=D.card := card_filter_add_card_filter_not _
  have hs : (∑ d∈E, (fiber (shift w) d).card)+
      (∑ d∈G, (fiber (shift w) d).card)=∑ d∈D, (fiber (shift w) d).card :=
    sum_filter_add_sum_filter_not _ _ _
  have hE : (∑ d∈E, (fiber (shift w) d).card) ≤ 4*Fintype.card α*E.card := by
    calc
      _ ≤ ∑ _d∈E, 4*Fintype.card α := by
        apply sum_le_sum
        intro d hd
        have hdD : d∈D := (mem_filter.mp hd).1
        apply difference_bound hw (by intro he; subst d; exact h0 hdD)
        exact (mem_filter.mp hd).2
      _ = _ := by simp [mul_comm]
  have hG : (∑ d∈G, (fiber (shift w) d).card) ≤ 2*Fintype.card α*G.card := by
    calc
      _ ≤ ∑ _d∈G, 2*Fintype.card α := by
        exact sum_le_sum (fun d hd => non_difference_bound hw (mem_filter.mp hd).2)
      _ = _ := by simp [mul_comm]
  have hsub : E⊆differenceSet w := by
    intro d hd
    exact (mem_differenceSet w d).mpr (mem_filter.mp hd).2
  have hEC := (card_le_card hsub).trans (difference_card w)
  have hmul := Nat.mul_le_mul_left (2*Fintype.card α) hEC
  have heq := congrArg (fun x => 2*Fintype.card α*x) hc
  nlinarith

open NaturalFourthEnergy

theorem natural_window_bound {A : Finset ℕ} (hA : IsB3 A) (D : Finset ℤ) (h0 : 0∉D) :
    ∑ d∈D, representations A d ≤ 2*A.card*D.card+2*A.card^3 := by
  simpa only [representations,Fintype.card_coe] using
    window_bound (indexed_unique hA) D h0

end Erdos241.PointwiseShiftBound


/- The translated-two-sum packing inequality, with all exceptional terms retained. -/
open Finset
open scoped Classical
namespace Erdos241.PairShiftPacking
open FourCircuitCompletion FourthEnergyTupleBasics SignedShiftEnergy PointwiseShiftBound
set_option maxHeartbeats 5000000

lemma collision_cauchy {U V : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
    (g : U → V) (D : Finset V) (hmap : ∀ u, g u∈D) :
    (Fintype.card U)^2 ≤ D.card*(collisions g).card := by
  have hs : (∑ v∈D, (fiber g v).card)=Fintype.card U := by
    simp only [fiber]
    rw [sum_card_fiberwise_eq_card_filter]
    simp [hmap]
  rw [←hs]
  exact sum_fiber_sq_cauchy g D

variable {α : Type*} [LinearOrder α] [Fintype α]

lemma two_unique {w : α → ℕ} (hw : ThreeUnique w) {a b c d : α}
    (he : w a+w b=w c+w d) : ({a,b} : Multiset α)={c,d} := by
  have hh := hw a b a c d a (by omega)
  apply add_right_cancel (b:=({a} : Multiset α))
  simpa using hh

def zeroTuple (p : (Fin 2 → α) × Fin 2) : Fin 4 → α :=
  ![p.1 0,p.1 1,if p.2=0 then p.1 0 else p.1 1,if p.2=0 then p.1 1 else p.1 0]

lemma zero_shift_bound {w : α → ℕ} (hw : ThreeUnique w) :
    (fiber (shift w) 0).card ≤ 2*(Fintype.card α)^2 := by
  have hs : fiber (shift w) 0 ⊆ univ.image (zeroTuple (α:=α)) := by
    intro t ht
    have he : w (t 0)+w (t 1)=w (t 2)+w (t 3) := by
      have hh := (mem_filter.mp ht).2
      simp only [shift] at hh
      omega
    rcases pair_eq_cases (two_unique hw he) with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · refine mem_image.mpr ⟨(![t 0,t 1],0),mem_univ _,?_⟩
      funext i
      fin_cases i <;> simp [zeroTuple,h₁,h₂]
    · refine mem_image.mpr ⟨(![t 0,t 1],1),mem_univ _,?_⟩
      funext i
      fin_cases i <;> simp [zeroTuple,h₁,h₂]
  have hc := (card_le_card hs).trans card_image_le
  simpa [Fintype.card_prod,Fintype.card_fun,mul_comm] using hc

abbrev Domain (α : Type*) (m : ℕ) := (Fin 2 → α) × Fin m

def shiftedSum (w : α → ℕ) {m : ℕ} (t : Domain α m) : ℕ :=
  w (t.1 0)+w (t.1 1)+t.2.val

def shiftPair {m : ℕ} (j : Fin m × Fin m) : ℤ := (j.2.val : ℤ)-j.1.val

def quad {m : ℕ} (p : Domain α m × Domain α m) : Fin 4 → α :=
  ![p.1.1 0,p.1.1 1,p.2.1 0,p.2.1 1]

lemma collision_fiber_bound (w : α → ℕ) {m : ℕ} (j : Fin m × Fin m) :
    ((collisions (shiftedSum w (m:=m))).filter
      (fun p => (p.1.2,p.2.2)=j)).card ≤ (fiber (shift w) (shiftPair j)).card := by
  let T := (collisions (shiftedSum w (m:=m))).filter (fun p => (p.1.2,p.2.2)=j)
  have hmap : ∀ p∈T, quad p∈fiber (shift w) (shiftPair j) := by
    intro p hp
    have hj := (mem_filter.mp hp).2
    have hj₁ := congrArg Prod.fst hj
    have hj₂ := congrArg Prod.snd hj
    have he := (mem_filter.mp (mem_filter.mp hp).1).2
    simp only [shiftedSum] at he
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    simp [shift,quad,shiftPair]
    dsimp only at hj₁ hj₂
    rw [hj₁,hj₂] at he
    omega
  have hinj : Set.InjOn quad (T : Set (Domain α m × Domain α m)) := by
    intro p hp q hq he
    have hpj := (mem_filter.mp hp).2
    have hqj := (mem_filter.mp hq).2
    have hj := hpj.trans hqj.symm
    apply Prod.ext
    · apply Prod.ext
      · funext i
        fin_cases i
        · simpa [quad] using congrFun he 0
        · simpa [quad] using congrFun he 1
      · exact congrArg (fun z : Fin m × Fin m => z.1) hj
    · apply Prod.ext
      · funext i
        fin_cases i
        · simpa [quad] using congrFun he 2
        · simpa [quad] using congrFun he 3
      · exact congrArg (fun z : Fin m × Fin m => z.2) hj
  exact card_le_card_of_injOn quad hmap hinj

lemma collisions_le_sum (w : α → ℕ) (m : ℕ) :
    (collisions (shiftedSum w (m:=m))).card ≤
      ∑ j : Fin m × Fin m, (fiber (shift w) (shiftPair j)).card := by
  rw [card_eq_sum_card_fiberwise (t:=univ) (f:=fun p => (p.1.2,p.2.2))
    (fun _ _ => mem_univ _)]
  exact sum_le_sum (fun j _ => collision_fiber_bound w j)

lemma shiftPair_fiber (m : ℕ) (d : ℤ) :
    (univ.filter (fun j : Fin m × Fin m => shiftPair j=d)).card ≤ m := by
  let T := univ.filter (fun j : Fin m × Fin m => shiftPair j=d)
  have hmap : ∀ j∈T, j.1∈(univ : Finset (Fin m)) := by intros; exact mem_univ _
  have hinj : Set.InjOn Prod.fst (T : Set (Fin m × Fin m)) := by
    intro p hp q hq he
    apply Prod.ext he
    apply Fin.ext
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    simp only [shiftPair,he] at hp' hq'
    omega
  have hc : T.card ≤ (univ : Finset (Fin m)).card :=
    card_le_card_of_injOn (fun j : Fin m × Fin m => j.1) hmap hinj
  simpa only [card_univ,Fintype.card_fin] using hc

lemma shiftPair_set_bound (m : ℕ) (D : Finset ℤ) :
    (univ.filter (fun j : Fin m × Fin m => shiftPair j∈D)).card ≤ m*D.card := by
  let T := univ.filter (fun j : Fin m × Fin m => shiftPair j∈D)
  have hmap : ∀ j∈T, shiftPair j∈D := fun _ hj => (mem_filter.mp hj).2
  have hf : ∀ d∈D, (T.filter (fun j => shiftPair j=d)).card ≤ m := by
    intro d hd
    have hsub : T.filter (fun j => shiftPair j=d) ⊆
        univ.filter (fun j : Fin m × Fin m => shiftPair j=d) := by
      intro j hj
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2⟩
    exact (card_le_card hsub).trans (shiftPair_fiber m d)
  simpa only [mul_comm] using card_bound_of_fibers T D shiftPair m hmap hf

lemma sum_representations_bound {w : α → ℕ} (hw : ThreeUnique w) (m : ℕ) :
    (∑ j : Fin m × Fin m, (fiber (shift w) (shiftPair j)).card) ≤
      2*Fintype.card α*m^2+2*m*(Fintype.card α)^3+2*m*(Fintype.card α)^2 := by
  let k := Fintype.card α
  let E := univ.filter (fun j : Fin m × Fin m => IsDifference w (shiftPair j))
  let Z := univ.filter (fun j : Fin m × Fin m => shiftPair j=0)
  have hpt (j : Fin m × Fin m) : (fiber (shift w) (shiftPair j)).card ≤
      2*k+(if IsDifference w (shiftPair j) then 2*k else 0)+
        (if shiftPair j=0 then 2*k^2 else 0) := by
    by_cases hz : shiftPair j=0
    · rw [hz]
      have hh := zero_shift_bound hw
      dsimp only [k]
      split_ifs <;> omega
    · by_cases he : IsDifference w (shiftPair j)
      · have hh := difference_bound hw hz he
        simp only [if_pos he,if_neg hz]
        dsimp only [k]
        omega
      · have hh := non_difference_bound hw he
        simp only [if_neg he,if_neg hz,add_zero]
        exact hh
  have hs : (∑ j : Fin m × Fin m, (fiber (shift w) (shiftPair j)).card) ≤
      2*k*m^2+2*k*E.card+2*k^2*Z.card := by
    calc
      _ ≤ ∑ j : Fin m × Fin m, (2*k+
          (if IsDifference w (shiftPair j) then 2*k else 0)+
          (if shiftPair j=0 then 2*k^2 else 0)) := sum_le_sum (fun j _ => hpt j)
      _ = _ := by
        simp [sum_add_distrib,sum_ite,E,Z,Fintype.card_prod,pow_two,mul_comm,mul_left_comm,mul_assoc]
  have hE : E.card ≤ m*k^2 := by
    have hh := shiftPair_set_bound m (differenceSet w)
    simp only [mem_differenceSet] at hh
    exact hh.trans (Nat.mul_le_mul_left m (difference_card w))
  have hZ : Z.card ≤ m := shiftPair_fiber m 0
  have hmE := Nat.mul_le_mul_left (2*k) hE
  have hmZ := Nat.mul_le_mul_left (2*k^2) hZ
  dsimp only [k] at *
  nlinarith

/-- Cauchy–Schwarz on the translated two-sums gives this exact finite inequality. -/
theorem finite_packing {w : α → ℕ} (hw : ThreeUnique w) (N m : ℕ)
    (hN : ∀ a, w a ≤ N) :
    (Fintype.card α)^4*m^2 ≤ (2*N+m)*
      (2*Fintype.card α*m^2+2*m*(Fintype.card α)^3+2*m*(Fintype.card α)^2) := by
  have hmap : ∀ t : Domain α m, shiftedSum w t∈range (2*N+m) := by
    intro t
    apply mem_range.mpr
    have h₀ := hN (t.1 0)
    have h₁ := hN (t.1 1)
    have hj := t.2.isLt
    simp only [shiftedSum]
    omega
  have hc := collision_cauchy (shiftedSum w (m:=m)) (range (2*N+m)) hmap
  have he := (collisions_le_sum w m).trans (sum_representations_bound hw m)
  have hm := Nat.mul_le_mul_left (2*N+m) he
  simp only [card_range,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin] at hc
  nlinarith

/-- Taking a window of length `t*k^2` and cancelling the positive factors. -/
theorem scaled_finite_packing {w : α → ℕ} (hw : ThreeUnique w) (N t : ℕ)
    (ht : 0 < t) (hN : ∀ a, w a ≤ N) :
    t*(Fintype.card α)^3 ≤ (2*N+t*(Fintype.card α)^2)*(2*t+4) := by
  let k := Fintype.card α
  by_cases hk0 : k=0
  · change t*k^3 ≤ (2*N+t*k^2)*(2*t+4)
    simp [hk0]
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  have hpow : k^4 ≤ k^5 := Nat.pow_le_pow_right hk (by decide)
  have h0 := finite_packing hw N (t*k^2) hN
  change k^4*(t*k^2)^2 ≤ (2*N+t*k^2)*(2*k*(t*k^2)^2+2*(t*k^2)*k^3+2*(t*k^2)*k^2) at h0
  have h1 : 2*k*(t*k^2)^2+2*(t*k^2)*k^3+2*(t*k^2)*k^2 ≤ t*k^5*(2*t+4) := by
    have hh := Nat.mul_le_mul_left (2*t) hpow
    nlinarith
  have h2 := h0.trans (Nat.mul_le_mul_left (2*N+t*k^2) h1)
  have h3 : (t*k^5)*(t*k^3) ≤ (t*k^5)*((2*N+t*k^2)*(2*t+4)) := by
    convert h2 using 1 <;> ring
  exact Nat.le_of_mul_le_mul_left h3 (mul_pos ht (pow_pos hk 5))

end Erdos241.PairShiftPacking


/- The elementary cubic constant four, obtained from the exact finite shift estimate. -/
open Finset Filter
namespace Erdos241.IntervalCubicBound
open NaturalFourthEnergy ExtremalB3
set_option maxHeartbeats 5000000

lemma natural_scaled_bound {A : Finset ℕ} (hA : IsB3 A) {N : ℕ}
    (hsub : A⊆Icc 1 N) (t : ℕ) (ht : 0 < t) :
    t*A.card^3 ≤ (2*N+t*A.card^2)*(2*t+4) := by
  have hN : ∀ a : A, a.val ≤ N := fun a => (mem_Icc.mp (hsub a.prop)).2
  simpa only [Fintype.card_coe] using
    PairShiftPacking.scaled_finite_packing (indexed_unique hA) N t ht hN

lemma maxSize_scaled_bound (N t : ℕ) (ht : 0 < t) :
    t*(maxSize N)^3 ≤ (2*N+t*(maxSize N)^2)*(2*t+4) := by
  obtain ⟨A,hsub,hA,he⟩ := exists_maximizer N
  simpa only [he] using natural_scaled_bound hA hsub t ht

/-- A real-variable absorption lemma for the lower-order cardinality term. -/
lemma absorb {k N t ε : ℝ} (hk : 0 < k) (hN : 0 ≤ N) (ht : 0 < t) (hε : 0 < ε)
    (hden : 0 < t*ε-8)
    (hklarge : ((2*t^2+4*t)*(4+ε))/(t*ε-8) < k)
    (hB : t*k^3 ≤ (2*N+t*k^2)*(2*t+4)) :
    k^3 ≤ (4+ε)*N := by
  have hK := (div_lt_iff₀ hden).mp hklarge
  have hK2 := mul_lt_mul_of_pos_right hK (sq_pos_of_pos hk)
  have hBc := mul_le_mul_of_nonneg_right hB (show 0 ≤ 4+ε by linarith)
  by_contra hbad
  have hbad' : (4+ε)*N < k^3 := lt_of_not_ge hbad
  have hbad2 := mul_lt_mul_of_pos_left hbad' (show 0 < 4*t+8 by positivity)
  nlinarith

/-- This is an upper bound with constant four, not the constant one in the conjecture. -/
theorem eventually_cubic_upper {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (maxSize N : ℝ)^3 ≤ (4+ε)*(N : ℝ) := by
  obtain ⟨t,ht⟩ := exists_nat_gt ((8 : ℝ)/ε)
  have htR : (0 : ℝ) < t := lt_trans (div_pos (by norm_num) hε) ht
  have htN : 0 < t := by exact_mod_cast htR
  have hden : (0 : ℝ) < (t : ℝ)*ε-8 := by
    have hh := (div_lt_iff₀ hε).mp ht
    nlinarith
  let B : ℝ := ((2*(t : ℝ)^2+4*t)*(4+ε))/((t : ℝ)*ε-8)
  have hk : Tendsto (fun N => (maxSize N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_maxSize
  filter_upwards [hk.eventually (eventually_gt_atTop (max 0 B))] with N hN
  have hkpos : (0 : ℝ) < maxSize N := lt_of_le_of_lt (le_max_left _ _) hN
  have hklarge : B < (maxSize N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hB : (t : ℝ)*(maxSize N : ℝ)^3 ≤
      (2*(N : ℝ)+(t : ℝ)*(maxSize N : ℝ)^2)*(2*(t : ℝ)+4) := by
    exact_mod_cast maxSize_scaled_bound N t htN
  exact absorb hkpos (Nat.cast_nonneg N) htR hε hden hklarge hB

end Erdos241.IntervalCubicBound

namespace Erdos241.CubicNormalization
set_option maxHeartbeats 3000000

lemma cube_root_cube (N : ℕ) : ((N : ℝ)^((1 : ℝ)/3))^3=(N : ℝ) := by
  rw [←Real.rpow_mul_natCast (Nat.cast_nonneg N) ((1 : ℝ)/3) 3]
  norm_num

lemma cube_cube_root (N : ℕ) : ((N : ℝ)^3)^((1 : ℝ)/3)=(N : ℝ) := by
  rw [←Real.rpow_natCast_mul (Nat.cast_nonneg N) 3 ((1 : ℝ)/3)]
  norm_num

lemma equivalent_iff (k : ℕ → ℕ) :
    (fun N => (k N : ℝ)) ~[atTop] (fun N => (N : ℝ)^((1 : ℝ)/3)) ↔
      Tendsto (fun N => (k N : ℝ)^3/(N : ℝ)) atTop (nhds 1) := by
  have hz : ∀ᶠ N : ℕ in atTop, (N : ℝ)≠0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact_mod_cast (show N≠0 by omega)
  constructor
  · intro h
    have h3 : (fun N => (k N : ℝ)^3) ~[atTop] (fun N => (N : ℝ)) := by
      have hh := h.pow 3
      change (fun N => (k N : ℝ)^3) ~[atTop] (fun N => ((N : ℝ)^((1 : ℝ)/3))^3) at hh
      simpa only [cube_root_cube] using hh
    exact (Asymptotics.isEquivalent_iff_tendsto_one hz).mp h3
  · intro h
    have h3 : (fun N => (k N : ℝ)^3) ~[atTop] (fun N => (N : ℝ)) :=
      (Asymptotics.isEquivalent_iff_tendsto_one hz).mpr h
    have hr := Asymptotics.IsEquivalent.rpow (r:=((1 : ℝ)/3))
      (show (0 : ℕ → ℝ) ≤ (fun N : ℕ => (N : ℝ)) from fun N => Nat.cast_nonneg N) h3
    change (fun N => ((k N : ℝ)^3)^((1 : ℝ)/3)) ~[atTop]
      (fun N => (N : ℝ)^((1 : ℝ)/3)) at hr
    simpa only [cube_cube_root] using hr

/-- A truly unbounded cubic-density improvement would disprove the asymptotic. -/
lemma not_equivalent_of_frequently_dense (k : ℕ → ℕ) {c : ℝ} (hc : 1 < c)
    (hfreq : ∃ᶠ N : ℕ in atTop, c*(N : ℝ) ≤ (k N : ℝ)^3) :
    ¬(fun N => (k N : ℝ)) ~[atTop] (fun N => (N : ℝ)^((1 : ℝ)/3)) := by
  intro h
  have ht := (equivalent_iff k).mp h
  have hlt : ∀ᶠ N : ℕ in atTop, (k N : ℝ)^3/(N : ℝ) < c := ht.eventually_lt_const hc
  obtain ⟨N,⟨hN,hge⟩,hh⟩ := ((hfreq.and_eventually (eventually_ge_atTop (1 : ℕ))).and_eventually hlt).exists
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbad := (div_lt_iff₀ hpos).mp hh
  linarith

end Erdos241.CubicNormalization

namespace Erdos241.CubicNormalization
set_option maxHeartbeats 3000000

/-- The precise two-sided cubic target, with no number-theoretic hypotheses hidden. -/
lemma equivalent_iff_eventually_bounds (k : ℕ → ℕ) :
    (fun N => (k N : ℝ)) ~[atTop] (fun N => (N : ℝ)^((1 : ℝ)/3)) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (1-ε)*(N : ℝ) ≤ (k N : ℝ)^3 ∧ (k N : ℝ)^3 ≤ (1+ε)*(N : ℝ) := by
  rw [equivalent_iff]
  constructor
  · intro h ε hε
    have hlo := h.eventually_const_lt (show 1-ε < (1 : ℝ) by linarith)
    have hhi := h.eventually_lt_const (show (1 : ℝ) < 1+ε by linarith)
    filter_upwards [hlo,hhi,eventually_ge_atTop (1 : ℕ)] with N hl hu hN
    have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact ⟨((lt_div_iff₀ hp).mp hl).le,((div_lt_iff₀ hp).mp hu).le⟩
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [h (ε/2) (by linarith),eventually_ge_atTop (1 : ℕ)] with N hB hN
    have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hl := (le_div_iff₀ hp).mpr hB.1
    have hu := (div_le_iff₀ hp).mpr hB.2
    rw [Real.dist_eq,abs_lt]
    constructor <;> linarith

end Erdos241.CubicNormalization

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

lemma eventually_f_three_cubic_upper {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3 ≤ (4+ε)*(N : ℝ) := by
  simpa only [f_three_eq_maxSize] using IntervalCubicBound.eventually_cubic_upper hε

/-- An exact target reformulation, not a proof of the conjecture. -/
lemma f_three_asymptotic_iff_cubic_bounds :
    (fun N ↦ (f N 3 : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3)) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (1-ε)*(N : ℝ) ≤ (f N 3 : ℝ)^3 ∧
        (f N 3 : ℝ)^3 ≤ (1+ε)*(N : ℝ) :=
  CubicNormalization.equivalent_iff_eventually_bounds (fun N => f N 3)

theorem erdos_241 :
    (fun N ↦ (f N 3 : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3)) := by
  sorry

end Erdos241
