import FormalConjecturesUtil

/-!
# Erdős Problem 241

The conjecture remains unresolved. The checked auxiliary development below
proves the constant-one asymptotic lower bound using the cubic Bose–Chowla
construction and a compact-frequency proof of relative prime gaps. It also
proves the elementary asymptotic cubic upper bound with constant four.
The sharp constant-one upper bound, and hence the conjecture, remain unresolved.
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


/- A compactly supported Fourier test against a moving continuous boundary. -/
open MeasureTheory Filter Set FourierTransform
open scoped Topology FourierTransform
namespace Erdos241.MovingBoundaryFourier
set_option maxHeartbeats 3000000

lemma norm_fourier_le (f : ℝ → ℂ) (T : ℝ) :
    ‖𝓕 f T‖ ≤ ∫ t, ‖f t‖ := by
  rw [Real.fourier_eq]
  calc
    _ ≤ ∫ t, ‖𝐞 (-inner ℝ t T) • f t‖ := norm_integral_le_integral_norm _
    _ = _ := by simp only [Circle.norm_smul]

lemma fourier_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (T : ℝ) :
    𝓕 (fun t => f t-g t) T=𝓕 f T-𝓕 g T := by
  simp only [Real.fourier_eq,smul_sub]
  rw [integral_sub ((Real.fourierIntegral_convergent_iff T).mpr hf)
    ((Real.fourierIntegral_convergent_iff T).mpr hg)]

lemma boundary_error_tendsto {F : ℝ → ℝ → ℂ} (hF : Continuous F.uncurry)
    {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g)
    {σ : ℝ → ℝ} (hσ : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun T => ∫ t, ‖g t*(F (σ T) t-F 0 t)‖) atTop (𝓝 0) := by
  have hcont : Continuous (fun s : ℝ => ∫ t : ℝ, ‖g t*(F s t-F 0 t)‖) := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (k:=tsupport g) hc.isCompact
    · apply Continuous.continuousOn
      change Continuous (fun p : ℝ × ℝ => ‖g p.2*(F p.1 p.2-F 0 p.2)‖)
      exact ((hg.comp continuous_snd).mul
        (hF.sub (hF.comp (continuous_const.prodMk continuous_snd)))).norm
    · intro s t _ ht
      have hz : g t=0 := image_eq_zero_of_notMem_tsupport ht
      simp [hz]
  convert hcont.continuousAt.tendsto.comp hσ using 1 <;> simp

lemma moving_fourier_tendsto {F : ℝ → ℝ → ℂ} (hF : Continuous F.uncurry)
    {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g)
    {σ : ℝ → ℝ} (hσ : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun T => 𝓕 (fun t => g t*F (σ T) t) T) atTop (𝓝 0) := by
  have hi (s : ℝ) : Integrable (fun t => g t*F s t) :=
    (hg.mul (hF.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport hc.mul_right
  have herr : Tendsto (fun T => 𝓕 (fun t => g t*(F (σ T) t-F 0 t)) T)
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun T => norm_fourier_le _ T) (boundary_error_tendsto hF hg hc hσ)
  have hbase : Tendsto (fun T : ℝ => 𝓕 (fun t => g t*F 0 t) T) atTop (𝓝 0) :=
    (Real.zero_at_infty_fourier _).mono_left atTop_le_cocompact
  have hsum := herr.add hbase
  convert hsum using 1
  · funext T
    have hh := fourier_sub (hi (σ T)) (hi 0) T
    simp only [←mul_sub] at hh
    rw [hh,sub_add_cancel]
  · simp

end Erdos241.MovingBoundaryFourier


/- The ordinary von Mangoldt boundary function, specialized from modulus one. -/
open MeasureTheory Filter Set FourierTransform Complex ArithmeticFunction
open scoped Topology FourierTransform
namespace Erdos241.VonMangoldtBoundary
set_option maxHeartbeats 3000000

noncomputable def aux (z : ℂ) : ℂ :=
  vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) z

lemma continuousOn_aux : ContinuousOn aux {z : ℂ | 1 ≤ z.re} :=
  vonMangoldt.continuousOn_LFunctionResidueClassAux (1 : ZMod 1)

lemma residue_one (n : ℕ) : vonMangoldt.residueClass (1 : ZMod 1) n=vonMangoldt n := by
  have he : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  simp [vonMangoldt.residueClass,he]

lemma aux_eq {z : ℂ} (hz : 1 < z.re) :
    aux z=LSeries (fun n => (vonMangoldt n : ℂ)) z-1/(z-1) := by
  have hh := vonMangoldt.eqOn_LFunctionResidueClassAux (isUnit_one : IsUnit (1 : ZMod 1)) hz
  simpa only [aux,residue_one,Nat.totient_one,Nat.cast_one,inv_one] using hh

lemma summable_nonprime :
    Summable (fun n : ℕ => (if n.Prime then 0 else vonMangoldt n)/(n : ℝ)) := by
  simpa only [residue_one] using vonMangoldt.summable_residueClass_non_primes_div (1 : ZMod 1)

noncomputable def boundary (s t : ℝ) : ℂ :=
  aux (1+(|s| : ℝ)-((2*Real.pi*t : ℝ) : ℂ)*I)

lemma continuous_boundary : Continuous boundary.uncurry := by
  apply continuousOn_aux.comp_continuous
  · change Continuous (fun p : ℝ × ℝ =>
      (1 : ℂ)+(|p.1| : ℝ)-((2*Real.pi*p.2 : ℝ) : ℂ)*I)
    fun_prop
  · intro p
    simp only [mem_setOf_eq,sub_re,add_re,one_re,ofReal_re,mul_re,I_re,mul_zero,
      ofReal_im,I_im,mul_one,sub_self,sub_zero]
    exact le_add_of_nonneg_right (abs_nonneg _)

lemma boundary_eq {s : ℝ} (hs : 0 < s) (t : ℝ) :
    boundary s t=
      LSeries (fun n => (vonMangoldt n : ℂ)) (1+(s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I)-
        1/((s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I) := by
  rw [boundary,abs_of_pos hs,aux_eq]
  · congr 2 <;> ring
  · simp only [sub_re,add_re,one_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,
      mul_one,sub_self,sub_zero]
    linarith

lemma smoothed_boundary_tendsto {g : ℝ → ℂ} (hg : Continuous g)
    (hc : HasCompactSupport g) {σ : ℝ → ℝ} (hσ : Tendsto σ atTop (𝓝 0)) :
    Tendsto (fun T => 𝓕 (fun t => g t*boundary (σ T) t) T) atTop (𝓝 0) :=
  MovingBoundaryFourier.moving_fourier_tendsto continuous_boundary hg hc hσ

end Erdos241.VonMangoldtBoundary


/- Schwartz-space tools for a compact-frequency interval minorant. -/
open MeasureTheory Filter Set FourierTransform Complex ComplexConjugate
open scoped Topology FourierTransform SchwartzMap Convolution ContDiff
namespace Erdos241.SchwartzMinorant
set_option maxHeartbeats 3000000

noncomputable def post {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (f : 𝓢(ℝ,E)) : 𝓢(ℝ,F) :=
  SchwartzMap.bilinLeftCLM (((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip).comp L)
    (g:=fun _ : ℝ => (1 : ℝ)) (by fun_prop) f

@[simp] lemma post_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (f : 𝓢(ℝ,E)) (x : ℝ) : post L f x=L (f x) := by
  simp [post]

noncomputable def reflect (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E:=ℝ)).toContinuousLinearEquiv f

@[simp] lemma reflect_apply (f : 𝓢(ℝ,ℂ)) (x : ℝ) : reflect f x=f (-x) := rfl

noncomputable def starReflect (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  post Complex.conjCLE.toContinuousLinearMap (reflect f)

@[simp] lemma starReflect_apply (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    starReflect f x=conj (f (-x)) := by simp [starReflect]

lemma fourier_star_neg (f : ℝ → ℂ) (x : ℝ) :
    𝓕 (fun t => conj (f (-t))) x=conj (𝓕 f x) := by
  simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]
  rw [←integral_conj]
  calc
    _ = ∫ t : ℝ, Complex.exp ((-2*Real.pi*(-t)*x : ℝ)*I)*conj (f t) := by
      symm
      convert integral_neg_eq_self (fun t : ℝ => Complex.exp ((-2*Real.pi*t*x : ℝ)*I)*conj (f (-t))) (μ:=volume) using 1
      simp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [map_mul,←Complex.exp_conj,Complex.conj_ofReal,Complex.conj_I]
      congr 2
      push_cast
      ring

lemma fourier_starReflect (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    𝓕 (starReflect f) x=conj (𝓕 f x) := by
  have he : (starReflect f : ℝ → ℂ)=(fun t => conj (f (-t))) := funext (starReflect_apply f)
  simp only [SchwartzMap.fourier_coe,he]
  exact fourier_star_neg _ _

lemma compact_starReflect {f : 𝓢(ℝ,ℂ)} (hf : HasCompactSupport (f : ℝ → ℂ)) :
    HasCompactSupport (starReflect f : ℝ → ℂ) := by
  have hr := hf.comp_homeomorph (Homeomorph.neg ℝ)
  have hc := hr.comp_left (show conj (0 : ℂ)=0 by simp)
  convert hc using 1
  funext x
  exact starReflect_apply f x

noncomputable def autoCorr (h : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) h (starReflect h)

lemma fourier_autoCorr (h : 𝓢(ℝ,ℂ)) (x : ℝ) :
    𝓕 (autoCorr h) x=(‖𝓕 h x‖^2 : ℝ) := by
  rw [autoCorr,SchwartzMap.fourier_convolution]
  simp only [SchwartzMap.pairing_apply_apply,ContinuousLinearMap.mul_apply',fourier_starReflect,
    Complex.mul_conj']
  norm_cast

lemma compact_autoCorr {h : 𝓢(ℝ,ℂ)} (hc : HasCompactSupport (h : ℝ → ℂ)) :
    HasCompactSupport (autoCorr h : ℝ → ℂ) := by
  have hh : (autoCorr h : ℝ → ℂ)=
      (h : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (starReflect h : ℝ → ℂ) := by
    funext x
    exact SchwartzMap.convolution_apply _ _ _ _
  rw [hh]
  exact hc.convolution (ContinuousLinearMap.mul ℂ ℂ) (compact_starReflect hc)

noncomputable def dd (h : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ h)

lemma fourier_deriv (h : 𝓢(ℝ,ℂ)) (x : ℝ) :
    𝓕 (SchwartzMap.derivCLM ℂ ℂ h) x=(2*Real.pi*I*(x : ℂ))*𝓕 h x := by
  have he : (SchwartzMap.derivCLM ℂ ℂ h : ℝ → ℂ)=deriv h :=
    funext (SchwartzMap.derivCLM_apply ℂ h)
  rw [SchwartzMap.fourier_coe,he,Real.fourier_deriv h.integrable h.differentiable]
  · rfl
  · rw [←he]
    exact (SchwartzMap.derivCLM ℂ ℂ h).integrable

lemma fourier_dd (h : 𝓢(ℝ,ℂ)) (x : ℝ) :
    𝓕 (dd h) x=-(4*Real.pi^2*(x : ℂ)^2)*𝓕 h x := by
  rw [dd,fourier_deriv,fourier_deriv]
  linear_combination (4*(Real.pi : ℂ)^2*(x : ℂ)^2*𝓕 h x)*Complex.I_sq

lemma compact_dd {h : 𝓢(ℝ,ℂ)} (hc : HasCompactSupport (h : ℝ → ℂ)) :
    HasCompactSupport (dd h : ℝ → ℂ) := by
  change HasCompactSupport (fun x => deriv (SchwartzMap.derivCLM ℂ ℂ h) x)
  have he : (SchwartzMap.derivCLM ℂ ℂ h : ℝ → ℂ)=deriv h :=
    funext (SchwartzMap.derivCLM_apply ℂ h)
  rw [he]
  exact hc.deriv.deriv

noncomputable def kernel (h : 𝓢(ℝ,ℂ)) (c : ℝ) : 𝓢(ℝ,ℂ) :=
  (c : ℂ) • autoCorr h + (1/(4*Real.pi^2) : ℂ) • dd (autoCorr h)

lemma fourier_kernel (h : 𝓢(ℝ,ℂ)) (c x : ℝ) :
    𝓕 (kernel h c) x=((c-x^2)*‖𝓕 h x‖^2 : ℝ) := by
  simp only [kernel,FourierTransform.fourier_add,FourierTransform.fourier_smul,
    SchwartzMap.add_apply,SchwartzMap.smul_apply,smul_eq_mul,fourier_dd,fourier_autoCorr]
  push_cast
  have hp : (Real.pi : ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  <;> ring

lemma compact_kernel {h : 𝓢(ℝ,ℂ)} (hc : HasCompactSupport (h : ℝ → ℂ)) (c : ℝ) :
    HasCompactSupport (kernel h c : ℝ → ℂ) :=
  ((compact_autoCorr hc).smul_left).add ((compact_dd (compact_autoCorr hc)).smul_left)

lemma autoCorr_zero (h : 𝓢(ℝ,ℂ)) :
    autoCorr h 0=((∫ t : ℝ, ‖h t‖^2 : ℝ) : ℂ) := by
  rw [autoCorr,SchwartzMap.convolution_apply]
  change (∫ t : ℝ, h t*starReflect h (0-t))= _
  simp only [starReflect_apply,zero_sub,neg_neg,Complex.mul_conj']
  simp_rw [←ofReal_pow]
  exact integral_ofReal

lemma autoCorr_zero_pos {h : 𝓢(ℝ,ℂ)} (hc : HasCompactSupport (h : ℝ → ℂ))
    (hn : ∃ x, h x≠0) : 0 < (autoCorr h 0).re := by
  rw [autoCorr_zero,ofReal_re]
  obtain ⟨x,hx⟩ := hn
  exact (h.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hc.norm.comp_left (g:=fun t : ℝ => t^2) (by simp)) (fun _ => sq_nonneg _) (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))

lemma integral_fourier (h : 𝓢(ℝ,ℂ)) : (∫ t : ℝ, 𝓕 h t)=h 0 := by
  have hh := congrArg (fun f : 𝓢(ℝ,ℂ) => f 0) (fourierInv_fourier_eq (F:=𝓢(ℝ,ℂ)) h)
  dsimp only at hh
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq] at hh
  simpa using hh

lemma kernel_positive_integral {h : 𝓢(ℝ,ℂ)}
    (hp : 0 < (autoCorr h 0).re) :
    ∃ c : ℝ, 0 < c ∧ 0 < (∫ t : ℝ, 𝓕 (kernel h c) t).re := by
  let b : ℝ := ((1/(4*Real.pi^2) : ℂ)*dd (autoCorr h) 0).re
  obtain ⟨c,hc⟩ := exists_gt (max 0 (-b/(autoCorr h 0).re))
  refine ⟨c,lt_of_le_of_lt (le_max_left _ _) hc,?_⟩
  rw [integral_fourier]
  have hb : -b/(autoCorr h 0).re < c := lt_of_le_of_lt (le_max_right _ _) hc
  have hh := (div_lt_iff₀ hp).mp hb
  simp only [kernel,SchwartzMap.add_apply,SchwartzMap.smul_apply,smul_eq_mul,
    add_re,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
  change 0 < c*(autoCorr h 0).re+b
  linarith

noncomputable def dilate (R : ℝ) (hR : R≠0) (h : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 R⁻¹ (inv_ne_zero hR))) h

@[simp] lemma dilate_apply (R : ℝ) (hR : R≠0) (h : 𝓢(ℝ,ℂ)) (x : ℝ) :
    dilate R hR h x=h (x/R) := by simp [dilate,div_eq_mul_inv]

lemma compact_dilate {h : 𝓢(ℝ,ℂ)} (hc : HasCompactSupport (h : ℝ → ℂ))
    (R : ℝ) (hR : R≠0) : HasCompactSupport (dilate R hR h : ℝ → ℂ) :=
  hc.comp_homeomorph (ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 R⁻¹ (inv_ne_zero hR))).toHomeomorph

lemma fourier_dilate_fun (h : ℝ → ℂ) {R : ℝ} (hR : 0 < R) (x : ℝ) :
    𝓕 (fun t => h (t/R)) x=(R : ℂ)*𝓕 h (R*x) := by
  simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]
  calc
    _ = ∫ t : ℝ, (fun u => Complex.exp ((-2*Real.pi*u*(R*x) : ℝ)*I)*h u) (t/R) := by
      apply integral_congr_ae
      filter_upwards with t
      congr 3
      field_simp
    _ = |R| • (∫ u : ℝ, Complex.exp ((-2*Real.pi*u*(R*x) : ℝ)*I)*h u) :=
      MeasureTheory.Measure.integral_comp_div (fun u : ℝ => Complex.exp ((-2*Real.pi*u*(R*x) : ℝ)*I)*h u) R
    _ = _ := by rw [abs_of_pos hR]; rfl

lemma fourier_dilate (h : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 < R) (x : ℝ) :
    𝓕 (dilate R hR.ne' h) x=(R : ℂ)*𝓕 h (R*x) := by
  rw [SchwartzMap.fourier_coe,SchwartzMap.fourier_coe]
  have he : (dilate R hR.ne' h : ℝ → ℂ)=fun t => h (t/R) := funext (dilate_apply _ _ _)
  rw [he]
  exact fourier_dilate_fun h hR x

lemma exists_compact_nonzero_schwartz :
    ∃ h : 𝓢(ℝ,ℂ), HasCompactSupport (h : ℝ → ℂ) ∧ ∃ x, h x≠0 := by
  let u : ℝ → ℝ := ExistsContDiffBumpBase.u
  have hc : HasCompactSupport (fun x => (u x : ℂ)) :=
    (ExistsContDiffBumpBase.u_compact_support ℝ).comp_left (g:=Complex.ofReal) (by simp)
  have hs : ContDiff ℝ ∞ (fun x => (u x : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (ExistsContDiffBumpBase.u_smooth ℝ)
  refine ⟨hc.toSchwartzMap hs,hc,0,?_⟩
  have hn : u 0≠0 := by
    have hm : (0 : ℝ) ∈ Function.support u := by
      rw [show Function.support u=Metric.ball 0 1 from ExistsContDiffBumpBase.u_support ℝ]
      simp
    exact hm
  change (u 0 : ℂ)≠0
  exact_mod_cast hn

/-- A Schwartz test with compact frequency support, positive total mass, and
nonpositive Fourier transform outside any prescribed interval. -/
theorem exists_minorant {a : ℝ} (ha : 0 < a) :
    ∃ g : 𝓢(ℝ,ℂ), HasCompactSupport (g : ℝ → ℂ) ∧
      (∀ x : ℝ, (𝓕 g x).im=0) ∧
      (∀ x : ℝ, a ≤ |x| → (𝓕 g x).re ≤ 0) ∧
      0 < (∫ x : ℝ, 𝓕 g x).re := by
  obtain ⟨h,hc,hn⟩ := exists_compact_nonzero_schwartz
  obtain ⟨c,hcpos,hint⟩ := kernel_positive_integral (autoCorr_zero_pos hc hn)
  let R : ℝ := (c+1)/a
  have hR : 0 < R := div_pos (by linarith) ha
  have hRa : R*a=c+1 := div_mul_cancel₀ _ ha.ne'
  refine ⟨dilate R hR.ne' (kernel h c),compact_dilate (compact_kernel hc c) R hR.ne',?_,?_,?_⟩
  · intro x
    rw [fourier_dilate _ hR,fourier_kernel,←ofReal_mul]
    exact ofReal_im _
  · intro x hx
    rw [fourier_dilate _ hR,fourier_kernel]
    simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
    have hx2 : a^2 ≤ x^2 := by nlinarith [sq_abs x]
    have hmul := mul_le_mul_of_nonneg_left hx2 (sq_nonneg R)
    have hc2 : c ≤ (R*x)^2 := by nlinarith [sq_nonneg c]
    exact mul_nonpos_of_nonneg_of_nonpos hR.le
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))
  · rw [integral_fourier,dilate_apply,zero_div]
    simpa only [integral_fourier] using hint

end Erdos241.SchwartzMinorant


/- Termwise Fourier smoothing of absolutely summable exponential series. -/
open MeasureTheory Filter Set FourierTransform Complex
open scoped Topology FourierTransform SchwartzMap
namespace Erdos241.FourierSeries
set_option maxHeartbeats 3000000

noncomputable def phase (x : ℝ) : ℂ := 𝐞 x

@[simp] lemma norm_phase (x : ℝ) : ‖phase x‖=1 := by simp [phase]
lemma continuous_phase : Continuous phase := by
  unfold phase
  simp_rw [Real.fourierChar_apply]
  fun_prop
lemma phase_add (x y : ℝ) : phase (x+y)=phase x*phase y := by
  simp only [phase,AddChar.map_add_eq_mul,Circle.coe_mul]

lemma fourier_eq (g : ℝ → ℂ) (T : ℝ) :
    𝓕 g T=∫ t : ℝ, phase (-t*T)*g t := by
  rw [Real.fourier_eq]
  congr 1
  funext t
  simp [phase,Circle.smul_def,mul_comm]

lemma term_integrable (g : 𝓢(ℝ,ℂ)) (c : ℂ) (b T : ℝ) :
    Integrable (fun t : ℝ => phase (-t*T)*g t*(c*phase (b*t))) := by
  have hn : Integrable (fun t : ℝ => ‖c‖*‖g t‖) := g.integrable.norm.const_mul _
  apply hn.mono' ?_ (Eventually.of_forall (fun t => ?_))
  · exact ((continuous_phase.comp (by fun_prop)).mul g.continuous |>.mul
      (continuous_const.mul (continuous_phase.comp (by fun_prop)))).aestronglyMeasurable
  · simp [norm_mul,mul_comm]

lemma term_integral (g : 𝓢(ℝ,ℂ)) (c : ℂ) (b T : ℝ) :
    (∫ t : ℝ, phase (-t*T)*g t*(c*phase (b*t)))=c*𝓕 (g : ℝ → ℂ) (T-b) := by
  rw [fourier_eq,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have he : phase (-t*(T-b))=phase (-t*T)*phase (b*t) := by
    rw [←phase_add]
    congr 1
    ring
  rw [he]
  ring

lemma termwise (g : 𝓢(ℝ,ℂ)) (c : ℕ → ℂ) (b : ℕ → ℝ)
    (hc : Summable (fun n => ‖c n‖)) (T : ℝ) :
    𝓕 (fun t : ℝ => g t*(∑' n : ℕ, c n*phase (b n*t))) T=
      ∑' n : ℕ, c n*𝓕 (g : ℝ → ℂ) (T-b n) := by
  have hs : Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖phase (-t*T)*g t*(c n*phase (b n*t))‖) := by
    simp only [norm_mul,norm_phase,one_mul,mul_one]
    simp_rw [integral_mul_const]
    exact hc.mul_left _
  have hh := integral_tsum_of_summable_integral_norm
    (fun n => term_integrable g (c n) (b n) T) hs
  rw [fourier_eq]
  calc
    _ = ∫ t : ℝ, ∑' n : ℕ, phase (-t*T)*g t*(c n*phase (b n*t)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [←mul_assoc,tsum_mul_left]
    _ = ∑' n : ℕ, ∫ t : ℝ, phase (-t*T)*g t*(c n*phase (b n*t)) := hh.symm
    _ = _ := tsum_congr (fun n => term_integral g (c n) (b n) T)

end Erdos241.FourierSeries


/- Higher prime powers disappear from translated bounded Fourier tests. -/
open MeasureTheory Filter Set FourierTransform Complex ArithmeticFunction
open scoped Topology FourierTransform SchwartzMap
namespace Erdos241.NonprimeSmoothing
set_option maxHeartbeats 3000000

noncomputable def damping (T : ℝ) : ℝ := Real.exp (-T)
lemma damping_pos (T : ℝ) : 0 < damping T := Real.exp_pos _
lemma damping_tendsto : Tendsto damping atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
lemma damping_mul_tendsto : Tendsto (fun T : ℝ => damping T*T) atTop (𝓝 0) := by
  simpa [damping,mul_comm] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1

lemma weighted_translate_tendsto (w : ℕ → ℝ) (hw : Summable w) (hw0 : ∀ n, 0 ≤ w n)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (g : 𝓢(ℝ,ℂ)) :
    Tendsto (fun T : ℝ => ∑' n : ℕ,
      (w n*Real.exp (-damping T*b n) : ℝ)*𝓕 (g : ℝ → ℂ) (T-b n)) atTop (𝓝 0) := by
  let C : ℝ := SchwartzMap.seminorm ℝ 0 0 (𝓕 g)
  have hC : 0 ≤ C := apply_nonneg _ _
  have hs : Summable (fun n => w n*C) := hw.mul_right C
  have hh : ∀ n, Tendsto (fun T : ℝ =>
      (w n*Real.exp (-damping T*b n) : ℝ)*𝓕 (g : ℝ → ℂ) (T-b n)) atTop (𝓝 (0 : ℂ)) := by
    intro n
    have he : Tendsto (fun T : ℝ => (w n*Real.exp (-damping T*b n) : ℝ)) atTop (𝓝 (w n)) := by
      convert tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp
        (damping_tendsto.neg.mul_const (b n))) using 1 <;> simp
    have hf : Tendsto (fun T : ℝ => 𝓕 (g : ℝ → ℂ) (T-b n)) atTop (𝓝 0) :=
      ((Real.zero_at_infty_fourier _).mono_left atTop_le_cocompact).comp (by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(b n)) tendsto_id)
    have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp he).mul hf
    simpa using hh
  have hd : ∀ᶠ T : ℝ in atTop, ∀ n,
      ‖(w n*Real.exp (-damping T*b n) : ℝ)*𝓕 (g : ℝ → ℂ) (T-b n)‖ ≤ w n*C := by
    apply Eventually.of_forall
    intro T n
    have he : Real.exp (-damping T*b n) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [damping_pos T,hb n]
    have hn : ‖𝓕 (g : ℝ → ℂ) (T-b n)‖ ≤ C := SchwartzMap.norm_le_seminorm ℝ (𝓕 g) _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw0 n) (Real.exp_pos _).le)]
    calc
      _ ≤ (w n*1)*C := mul_le_mul (mul_le_mul_of_nonneg_left he (hw0 n)) hn
        (norm_nonneg _) (by simpa using hw0 n)
      _ = _ := by ring
  simpa using tendsto_tsum_of_dominated_convergence hs hh hd

noncomputable def weight (n : ℕ) : ℝ :=
  (if n.Prime then 0 else vonMangoldt n)/(n : ℝ)

lemma weight_nonneg (n : ℕ) : 0 ≤ weight n := by
  unfold weight
  positivity [vonMangoldt_nonneg (n:=n)]

lemma higher_prime_powers_vanish (g : 𝓢(ℝ,ℂ)) :
    Tendsto (fun T : ℝ => ∑' n : ℕ,
      (weight n*Real.exp (-damping T*Real.log n) : ℝ)*
        𝓕 (g : ℝ → ℂ) (T-Real.log n)) atTop (𝓝 0) :=
  weighted_translate_tendsto weight VonMangoldtBoundary.summable_nonprime weight_nonneg
    (fun n => Real.log n) (fun n => Real.log_natCast_nonneg n) g

end Erdos241.NonprimeSmoothing


/- The pole's smoothed contribution tends to the mass of the Fourier test. -/
open MeasureTheory Filter Set FourierTransform Complex
open scoped Topology FourierTransform SchwartzMap
namespace Erdos241.SmoothedPole
open FourierSeries NonprimeSmoothing
set_option maxHeartbeats 3000000

lemma fourier_product_neg (g : 𝓢(ℝ,ℂ)) {h : ℝ → ℂ} (hh : Integrable h) (T : ℝ) :
    𝓕 (fun t => g t*𝓕 h (-t)) T=∫ u : ℝ, h u*𝓕 (g : ℝ → ℂ) (T-u) := by
  have hint : Integrable (fun p : ℝ × ℝ =>
      phase (-p.1*T)*g p.1*(phase (p.2*p.1)*h p.2)) (volume.prod volume) := by
    apply (g.integrable.norm.mul_prod hh.norm).mono' ?_ (Eventually.of_forall (fun p => ?_))
    · exact ((continuous_phase.comp (by fun_prop)).aestronglyMeasurable.mul
        g.integrable.aestronglyMeasurable.comp_fst).mul
        ((continuous_phase.comp (by fun_prop)).aestronglyMeasurable.mul hh.aestronglyMeasurable.comp_snd)
    · simp [norm_mul]
  rw [fourier_eq]
  calc
    _ = ∫ t : ℝ, ∫ u : ℝ, phase (-t*T)*g t*(phase (u*t)*h u) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [fourier_eq,integral_const_mul]
      simp only [neg_mul_neg]
      ring
    _ = ∫ u : ℝ, ∫ t : ℝ, phase (-t*T)*g t*(phase (u*t)*h u) :=
      integral_integral_swap hint
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [fourier_eq,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      have he : phase (-t*(T-u))=phase (-t*T)*phase (u*t) := by
        rw [←phase_add]
        congr 1
        ring
      rw [he]
      ring

noncomputable def halfExp (s : ℝ) : ℝ → ℂ :=
  (Set.Ioi 0).indicator (fun u : ℝ => Complex.exp (-(s : ℂ)*u))

lemma halfExp_integrable {s : ℝ} (hs : 0 < s) : Integrable (halfExp s) := by
  rw [halfExp,integrable_indicator_iff measurableSet_Ioi]
  exact integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs) 0

lemma fourier_halfExp {s : ℝ} (hs : 0 < s) (t : ℝ) :
    𝓕 (halfExp s) (-t)=1/((s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I) := by
  rw [fourier_eq]
  have he : (fun u : ℝ => phase (-u*(-t))*halfExp s u)=
      (Set.Ioi 0).indicator (fun u : ℝ =>
        Complex.exp ((-(s : ℂ)+((2*Real.pi*t : ℝ) : ℂ)*I)*u)) := by
    funext u
    by_cases hu : 0 < u
    · simp only [halfExp,Set.indicator_of_mem (show u ∈ Set.Ioi (0 : ℝ) from hu),neg_mul_neg,phase,
        Real.fourierChar_apply,←Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp [halfExp,hu]
  rw [he,integral_indicator measurableSet_Ioi,integral_exp_mul_complex_Ioi]
  · simp only [ofReal_zero,mul_zero,Complex.exp_zero]
    rw [show (-(s : ℂ)+((2*Real.pi*t : ℝ) : ℂ)*I)=
      -((s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I) by ring]
    rw [neg_div_neg_eq]
  · simp only [add_re,neg_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,mul_one,sub_self,add_zero]
    linarith

lemma pole_identity (g : 𝓢(ℝ,ℂ)) {s : ℝ} (hs : 0 < s) (T : ℝ) :
    𝓕 (fun t : ℝ => g t*(1/((s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I))) T=
      ∫ u : ℝ, halfExp s u*𝓕 (g : ℝ → ℂ) (T-u) := by
  simpa only [fourier_halfExp hs] using fourier_product_neg g (halfExp_integrable hs) T

noncomputable def cutWeight (T x : ℝ) : ℝ :=
  if x < T then Real.exp (-damping T*(T-x)) else 0

lemma cutWeight_bounds (T x : ℝ) : 0 ≤ cutWeight T x ∧ cutWeight T x ≤ 1 := by
  unfold cutWeight
  split_ifs with hx
  · constructor
    · positivity
    · apply Real.exp_le_one_iff.mpr
      nlinarith [damping_pos T]
  · norm_num

lemma cutWeight_tendsto (x : ℝ) : Tendsto (fun T : ℝ => cutWeight T x) atTop (𝓝 1) := by
  have he : Tendsto (fun T : ℝ => -damping T*(T-x)) atTop (𝓝 0) := by
    have hh := damping_mul_tendsto.neg.add (damping_tendsto.mul_const x)
    convert hh using 1 <;> simp [mul_sub]
  have hh := Real.continuous_exp.continuousAt.tendsto.comp he
  simp only [Real.exp_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop x] with T hT
  simp [cutWeight,hT]

lemma halfExp_translate (T x : ℝ) :
    halfExp (damping T) (T-x)=(cutWeight T x : ℂ) := by
  by_cases hx : x < T
  · simp only [halfExp,Set.mem_Ioi,sub_pos.mpr hx,indicator_of_mem,cutWeight,hx,↓reduceIte]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  · have hnot : ¬0 < T-x := by linarith
    simp [halfExp,cutWeight,hx,hnot]

lemma pole_translate (g : 𝓢(ℝ,ℂ)) (T : ℝ) :
    𝓕 (fun t : ℝ => g t*(1/((damping T : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I))) T=
      ∫ x : ℝ, (cutWeight T x : ℂ)*𝓕 (g : ℝ → ℂ) x := by
  rw [pole_identity g (damping_pos T)]
  have hh := integral_sub_left_eq_self
    (fun x : ℝ => halfExp (damping T) (T-x)*𝓕 (g : ℝ → ℂ) x) volume T
  simpa only [sub_sub_cancel,halfExp_translate] using hh

lemma pole_tendsto (g : 𝓢(ℝ,ℂ)) :
    Tendsto (fun T : ℝ =>
      𝓕 (fun t : ℝ => g t*(1/((damping T : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I))) T)
      atTop (𝓝 (∫ x : ℝ, 𝓕 (g : ℝ → ℂ) x)) := by
  simp only [pole_translate]
  apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => ‖𝓕 (g : ℝ → ℂ) x‖)
  · apply Eventually.of_forall
    intro T
    apply AEStronglyMeasurable.mul
    · have hc : Measurable (cutWeight T) := by
        unfold cutWeight
        apply Measurable.ite measurableSet_Iio <;> fun_prop
      exact (Complex.continuous_ofReal.measurable.comp hc).aestronglyMeasurable
    · exact (𝓕 g).continuous.aestronglyMeasurable
  · apply Eventually.of_forall
    intro T
    filter_upwards with x
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (cutWeight_bounds T x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (cutWeight_bounds T x).2
  · exact (𝓕 g).integrable.norm
  · filter_upwards with x
    have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp (cutWeight_tendsto x)).mul_const
      (𝓕 (g : ℝ → ℂ) x)
    simpa using hh

end Erdos241.SmoothedPole


/- A smoothed von Mangoldt asymptotic from the continuous pole-subtracted boundary. -/
open MeasureTheory Filter Set FourierTransform Complex ArithmeticFunction
open scoped Topology FourierTransform SchwartzMap
namespace Erdos241.VonMangoldtSmoothing
open FourierSeries NonprimeSmoothing VonMangoldtBoundary
set_option maxHeartbeats 3000000

noncomputable def coeff (s : ℝ) (n : ℕ) : ℝ :=
  (vonMangoldt n/(n : ℝ))*Real.exp (-s*Real.log n)

lemma coeff_nonneg (s : ℝ) (n : ℕ) : 0 ≤ coeff s n := by
  unfold coeff
  positivity [vonMangoldt_nonneg (n:=n)]

lemma term_expansion (s t : ℝ) (n : ℕ) :
    LSeries.term (fun n => (vonMangoldt n : ℂ))
      (1+(s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I) n=
      (coeff s n : ℂ)*phase (Real.log n*t) := by
  by_cases hn : n=0
  · subst n
    simp [coeff]
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn
  rw [LSeries.term_def₀ (by simp),Complex.cpow_def_of_ne_zero hnC]
  have he : Complex.log n * -(1+(s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I)=
      -Complex.log n+(-s*Real.log n : ℝ)+((2*Real.pi*(Real.log n*t) : ℝ) : ℂ)*I := by
    rw [←Complex.natCast_log]
    push_cast
    ring
  rw [he,Complex.exp_add,Complex.exp_add,Complex.exp_neg,Complex.exp_log hnC]
  simp only [coeff,phase,Real.fourierChar_apply,ofReal_mul,ofReal_div,
    Complex.ofReal_exp,Complex.ofReal_natCast,div_eq_mul_inv]
  push_cast
  ring

lemma summable_coeff_norm {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => ‖(coeff s n : ℂ)‖) := by
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s:=1+(s : ℂ)-((2*Real.pi*(0 : ℝ) : ℝ) : ℂ)*I) (by simp; linarith)
  change Summable _ at hsum
  have hn := hsum.norm
  have he (n : ℕ) : LSeries.term (fun n => (vonMangoldt n : ℂ))
      (1+(s : ℂ)-((2*Real.pi*(0 : ℝ) : ℝ) : ℂ)*I) n=(coeff s n : ℂ) := by
    simpa only [mul_zero,zero_mul,phase,Real.fourierChar_apply,ofReal_zero,
      Complex.exp_zero,mul_one] using term_expansion s 0 n
  convert hn using 1
  funext n
  exact (congrArg norm (he n)).symm

lemma lseries_expansion (s t : ℝ) :
    LSeries (fun n => (vonMangoldt n : ℂ)) (1+(s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I)=
      ∑' n : ℕ, (coeff s n : ℂ)*phase (Real.log n*t) := by
  unfold LSeries
  exact tsum_congr (term_expansion s t)

lemma smoothed_identity (g : 𝓢(ℝ,ℂ)) {s : ℝ} (hs : 0 < s) (T : ℝ) :
    𝓕 (fun t : ℝ => g t*LSeries (fun n => (vonMangoldt n : ℂ))
      (1+(s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I)) T=
      ∑' n : ℕ, (coeff s n : ℂ)*𝓕 (g : ℝ → ℂ) (T-Real.log n) := by
  simpa only [lseries_expansion] using
    termwise g (fun n => (coeff s n : ℂ)) (fun n => Real.log n) (summable_coeff_norm hs) T

lemma pole_denominator_ne_zero {s : ℝ} (hs : 0 < s) (t : ℝ) :
    (s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I≠0 := by
  intro he
  have hr := congrArg Complex.re he
  simp only [sub_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,mul_one,sub_self,sub_zero,zero_re] at hr
  linarith

lemma boundary_pole_integrable (g : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport (g : ℝ → ℂ))
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun t : ℝ => g t*boundary s t) ∧
      Integrable (fun t : ℝ => g t*(1/((s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I))) := by
  constructor
  · exact (g.continuous.mul (continuous_boundary.comp
      (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport hc.mul_right
  · apply Continuous.integrable_of_hasCompactSupport _ hc.mul_right
    exact g.continuous.mul (continuous_const.div (by fun_prop) (pole_denominator_ne_zero hs))

lemma fourier_add {f h : ℝ → ℂ} (hf : Integrable f) (hh : Integrable h) (T : ℝ) :
    𝓕 (fun t => f t+h t) T=𝓕 f T+𝓕 h T := by
  simp only [Real.fourier_eq,smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff T).mpr hf)
    ((Real.fourierIntegral_convergent_iff T).mpr hh)

lemma split_smoothed (g : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport (g : ℝ → ℂ))
    {s : ℝ} (hs : 0 < s) (T : ℝ) :
    (∑' n : ℕ, (coeff s n : ℂ)*𝓕 (g : ℝ → ℂ) (T-Real.log n))=
      𝓕 (fun t => g t*boundary s t) T+
        𝓕 (fun t : ℝ => g t*(1/((s : ℂ)-((2*Real.pi*t : ℝ) : ℂ)*I))) T := by
  rw [←smoothed_identity g hs T]
  obtain ⟨hi,hp⟩ := boundary_pole_integrable g hc hs
  rw [←fourier_add hi hp T]
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f T)
  funext t
  rw [boundary_eq hs]
  ring

lemma smoothed_mangoldt_tendsto (g : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport (g : ℝ → ℂ)) :
    Tendsto (fun T : ℝ => ∑' n : ℕ,
      (coeff (damping T) n : ℂ)*𝓕 (g : ℝ → ℂ) (T-Real.log n))
      atTop (𝓝 (∫ x : ℝ, 𝓕 (g : ℝ → ℂ) x)) := by
  simp only [split_smoothed g hc (damping_pos _)]
  simpa using (smoothed_boundary_tendsto g.continuous hc damping_tendsto).add (SmoothedPole.pole_tendsto g)

end Erdos241.VonMangoldtSmoothing


/- Relative prime gaps from a compact-frequency minorant and the zeta boundary. -/
open MeasureTheory Filter Set FourierTransform Complex ArithmeticFunction
open scoped Topology FourierTransform SchwartzMap
namespace Erdos241.RelativePrimeGaps
open VonMangoldtSmoothing NonprimeSmoothing
set_option maxHeartbeats 3000000

noncomputable def summand (g : 𝓢(ℝ,ℂ)) (s T : ℝ) (n : ℕ) : ℂ :=
  (coeff s n : ℂ)*𝓕 (g : ℝ → ℂ) (T-Real.log n)

lemma summable_summand (g : 𝓢(ℝ,ℂ)) {s : ℝ} (hs : 0 < s) (T : ℝ) :
    Summable (summand g s T) := by
  let C : ℝ := SchwartzMap.seminorm ℝ 0 0 (𝓕 g)
  apply ((summable_coeff_norm hs).mul_right C).of_norm_bounded
  intro n
  rw [summand,norm_mul]
  exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ (𝓕 g) _) (norm_nonneg _)

lemma summable_nonprime_summand (g : 𝓢(ℝ,ℂ)) {s : ℝ} (hs : 0 < s) (T : ℝ) :
    Summable (fun n : ℕ => if n.Prime then (0 : ℂ) else summand g s T n) := by
  have hh := (summable_summand g hs T).indicator {n : ℕ | ¬n.Prime}
  apply hh.congr
  intro n
  by_cases hn : n.Prime <;> simp [hn]

lemma nonprime_summand_eq (g : 𝓢(ℝ,ℂ)) (T : ℝ) (n : ℕ) :
    (if n.Prime then (0 : ℂ) else summand g (damping T) T n)=
      (weight n*Real.exp (-damping T*Real.log n) : ℝ)*𝓕 (g : ℝ → ℂ) (T-Real.log n) := by
  by_cases hn : n.Prime <;> simp [summand,VonMangoldtSmoothing.coeff,weight,hn]

lemma prime_smoothed_tendsto (g : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport (g : ℝ → ℂ)) :
    Tendsto (fun T : ℝ => (∑' n : ℕ, summand g (damping T) T n)-
      ∑' n : ℕ, if n.Prime then (0 : ℂ) else summand g (damping T) T n)
      atTop (𝓝 (∫ x : ℝ, 𝓕 (g : ℝ → ℂ) x)) := by
  have ht := (smoothed_mangoldt_tendsto g hc).sub (higher_prime_powers_vanish g)
  simp only [nonprime_summand_eq]
  simpa only [summand,sub_zero] using ht

/-- Every sufficiently far out fixed-width logarithmic interval contains a prime. -/
theorem eventually_log_prime {a : ℝ} (ha : 0 < a) :
    ∀ᶠ T : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ |T-Real.log p| < a := by
  obtain ⟨g,hc,him,hneg,hint⟩ := SchwartzMinorant.exists_minorant ha
  have ht := Complex.continuous_re.continuousAt.tendsto.comp (prime_smoothed_tendsto g hc)
  have hpos : ∀ᶠ T : ℝ in atTop, 0 < ((∑' n : ℕ, summand g (damping T) T n)-
      ∑' n : ℕ, if n.Prime then (0 : ℂ) else summand g (damping T) T n).re :=
    ht.eventually_const_lt hint
  filter_upwards [hpos] with T hT
  by_contra hn
  have hbad (p : ℕ) (hp : p.Prime) : a ≤ |T-Real.log p| := by
    by_contra hh
    exact hn ⟨p,hp,lt_of_not_ge hh⟩
  have hle (n : ℕ) : (summand g (damping T) T n).re ≤
      (if n.Prime then (0 : ℂ) else summand g (damping T) T n).re := by
    by_cases hp : n.Prime
    · simp only [hp,↓reduceIte,zero_re,summand,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (coeff_nonneg _ _) (hneg _ (hbad n hp))
    · simp [hp]
  have hs := summable_summand g (damping_pos T) T
  have hns := summable_nonprime_summand g (damping_pos T) T
  have hrs : Summable (fun n => (summand g (damping T) T n).re) :=
    Complex.reCLM.summable hs
  have hrns : Summable (fun n : ℕ => (if n.Prime then (0 : ℂ) else summand g (damping T) T n).re) :=
    Complex.reCLM.summable hns
  have hr := hrs.tsum_le_tsum hle hrns
  rw [←Complex.re_tsum hs,←Complex.re_tsum hns] at hr
  simp only [sub_re] at hT
  linarith

/-- A relative interval of any fixed positive width eventually contains a prime. -/
theorem eventually_prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < (1+ε)*x := by
  let a : ℝ := Real.log (1+ε)/2
  have ha : 0 < a := div_pos (Real.log_pos (by linarith)) (by norm_num)
  have hcenter : Tendsto (fun x : ℝ => Real.log x+a) atTop atTop :=
    tendsto_atTop_add_const_right _ a Real.tendsto_log_atTop
  filter_upwards [hcenter.eventually (eventually_log_prime ha),eventually_gt_atTop (0 : ℝ)] with x hx hx0
  obtain ⟨p,hp,hclose⟩ := hx
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hclose
  have hloglo : Real.log x < Real.log p := by linarith
  have hloghi : Real.log p < Real.log x+2*a := by linarith
  refine ⟨p,hp,?_,?_⟩
  · simpa only [Real.exp_log hx0,Real.exp_log hp0] using Real.exp_lt_exp.mpr hloglo
  · have hh := Real.exp_lt_exp.mpr hloghi
    rw [Real.exp_log hp0,Real.exp_add] at hh
    have he : Real.exp (2*a)=1+ε := by
      rw [show 2*a=Real.log (1+ε) by dsimp [a]; ring,Real.exp_log (by linarith)]
    rw [Real.exp_log hx0,he] at hh
    simpa only [mul_comm] using hh

end Erdos241.RelativePrimeGaps


/- The constant-one lower asymptotic for the strong B3 extremal problem. -/
open MeasureTheory Filter Set FourierTransform Complex ArithmeticFunction
open scoped Topology Asymptotics
namespace Erdos241.FullBoseLower
open ExtremalB3
set_option maxHeartbeats 3000000

lemma eventually_prime_below {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∀ᶠ y : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ γ*y < (p : ℝ) ∧ (p : ℝ) < y := by
  let ε : ℝ := 1/γ-1
  have hε : 0 < ε := by
    have hh : 1 < 1/γ := (lt_div_iff₀ hγ).mpr (by simpa using hγ1)
    dsimp [ε]
    linarith
  have ht : Tendsto (fun y : ℝ => γ*y) atTop atTop := tendsto_id.const_mul_atTop hγ
  filter_upwards [ht.eventually (RelativePrimeGaps.eventually_prime_between hε)] with y hy
  obtain ⟨p,hp,hl,hu⟩ := hy
  refine ⟨p,hp,hl,?_⟩
  have he : (1+ε)*(γ*y)=y := by dsimp [ε]; field_simp; ring
  rwa [he] at hu

lemma cube_root_tendsto :
    Tendsto (fun N : ℕ => (N : ℝ)^((1 : ℝ)/3)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/3)).comp tendsto_natCast_atTop_atTop

lemma eventually_root_lower {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∀ᶠ N : ℕ in atTop, γ*(N : ℝ)^((1 : ℝ)/3) ≤ (maxSize N : ℝ) := by
  filter_upwards [cube_root_tendsto.eventually (eventually_prime_below hγ hγ1)] with N hN
  obtain ⟨p,hp,hlo,hhi⟩ := hN
  have hcube : (p : ℝ)^3 ≤ ((N : ℝ)^((1 : ℝ)/3))^3 := by gcongr
  rw [CubicNormalization.cube_root_cube] at hcube
  have hNat : p^3 ≤ N := by exact_mod_cast hcube
  have hsize : p ≤ maxSize N :=
    (prime_lower_bound hp).trans (monotone_maxSize (by omega : p^3-1 ≤ N))
  exact hlo.le.trans (by exact_mod_cast hsize)

/-- The lower half of the desired asymptotic, uniformly at all sufficiently large N. -/
theorem eventually_cubic_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (1-ε)*(N : ℝ) ≤ (maxSize N : ℝ)^3 := by
  by_cases hε1 : 1 ≤ ε
  · apply Eventually.of_forall
    intro N
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg N)).trans (by positivity)
  have hεlt : ε < 1 := lt_of_not_ge hε1
  let γ : ℝ := 1-ε/3
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hγ1 : γ < 1 := by dsimp [γ]; linarith
  have hcoeff : 1-ε ≤ γ^3 := by
    have hh : 0 ≤ ε^2*(9-ε) := mul_nonneg (sq_nonneg ε) (by linarith)
    dsimp [γ]
    nlinarith
  filter_upwards [eventually_root_lower hγ hγ1] with N hN
  calc
    (1-ε)*(N : ℝ) ≤ γ^3*(N : ℝ) := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg N)
    _ = (γ*(N : ℝ)^((1 : ℝ)/3))^3 := by rw [mul_pow,CubicNormalization.cube_root_cube]
    _ ≤ (maxSize N : ℝ)^3 := by gcongr

end Erdos241.FullBoseLower

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

/-- The constant-one cubic lower bound, now valid at all sufficiently large lengths. -/
lemma eventually_f_three_cubic_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (1-ε)*(N : ℝ) ≤ (f N 3 : ℝ)^3 := by
  simpa only [f_three_eq_maxSize] using FullBoseLower.eventually_cubic_lower hε

/-- With the lower half proved, only the sharp upper half remains. -/
lemma f_three_asymptotic_iff_sharp_upper :
    (fun N ↦ (f N 3 : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3)) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (f N 3 : ℝ)^3 ≤ (1+ε)*(N : ℝ) := by
  rw [f_three_asymptotic_iff_cubic_bounds]
  constructor
  · intro h ε hε
    exact (h ε hε).mono (fun _ hN => hN.2)
  · intro h ε hε
    exact (eventually_f_three_cubic_lower hε).and (h ε hε)

/-- An exact description of a possible disproof, not a construction of one. -/
lemma not_f_three_asymptotic_iff_dense_subsequence :
    (¬(fun N ↦ (f N 3 : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3))) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ N : ℕ in atTop,
        (1+ε)*(N : ℝ) < (f N 3 : ℝ)^3 := by
  rw [f_three_asymptotic_iff_sharp_upper]
  simp only [not_forall,Filter.not_eventually,not_le,exists_prop]

theorem erdos_241 :
    (fun N ↦ (f N 3 : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3)) := by
  sorry

end Erdos241
