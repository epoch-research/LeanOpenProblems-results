import Submission.SignedQuadraticReduction
import Submission.ColoredC4Bound

/-! Quantitative signed-rectangle obstruction for balanced quadratic fibers. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714SignedQuadratic
open Erdos714Packing
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
variable [Fintype V] [Fintype W]

local instance : Fintype (SignClass V) := Fintype.ofFinite _
local instance : Fintype (NZClass V) := Fintype.ofFinite _

variable (h2 : Function.Injective (fun x : V => x+x))

def pairEquiv : V × V ≃ V × V := Equiv.ofBijective
  (fun p => (p.1+p.2,p.1-p.2))
  ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
    intro a b h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    change a.1+a.2=b.1+b.2 at h₁
    change a.1-a.2=b.1-b.2 at h₂
    have ha : a.1=b.1 := by
      apply h2
      change a.1+a.1=b.1+b.1
      calc
        _ = (a.1+a.2)+(a.1-a.2) := by abel
        _ = (b.1+b.2)+(b.1-b.2) := by rw [h₁,h₂]
        _ = _ := by abel
    apply Prod.ext ha
    rw [ha] at h₁
    exact add_left_cancel h₁,rfl⟩)

variable (Q : V → W) (c : W)
def level : Finset V := univ.filter (fun x => Q x=c)
def pointRel (x y : V) : Prop := Q (x+y)=c ∧ Q (x-y)=c
def pairSet : Finset (V × V) := univ.filter (fun p => pointRel Q c p.1 p.2)
def nzPairSet : Finset (V × V) := (pairSet Q c).filter (fun p => p.1≠0 ∧ p.2≠0)

omit [AddCommGroup W] [Fintype W] in
include h2 in
lemma pair_card : (pairSet Q c).card=(level Q c).card^2 := by
  have h := card_nbij (pairEquiv h2)
    (s := pairSet Q c) (t := level Q c ×ˢ level Q c) (by
      intro p hp
      simpa [pairEquiv,pairSet,pointRel,level] using hp)
    (by intro a ha b hb hab; exact (pairEquiv h2).injective hab) (by
      intro p hp
      obtain ⟨a,ha⟩ := (pairEquiv h2).surjective p
      refine ⟨a,?_,ha⟩
      have hh : (pairEquiv h2 a).1∈level Q c ∧ (pairEquiv h2 a).2∈level Q c := by
        rw [ha]
        exact mem_product.mp hp
      simpa [pairEquiv,pairSet,pointRel,level] using hh)
  simpa only [card_product,pow_two] using h

omit [AddCommGroup W] [Fintype W] in
lemma discarded_pairs : (pairSet Q c).card ≤ (nzPairSet Q c).card+2*(level Q c).card := by
  let bad := (pairSet Q c).filter (fun p => ¬(p.1≠0 ∧ p.2≠0))
  have hb : bad ⊆ ({0} ×ˢ level Q c) ∪ (level Q c ×ˢ {0}) := by
    intro p hp
    have hh := (mem_filter.mp hp).1
    have hn := (mem_filter.mp hp).2
    have he : pointRel Q c p.1 p.2 := (mem_filter.mp hh).2
    rcases not_and_or.mp hn with h | h
    · have hz : p.1=0 := not_not.mp h
      apply mem_union_left
      simp only [mem_product,mem_singleton,level,mem_filter,mem_univ,true_and]
      exact ⟨hz,by simpa [hz] using he.1⟩
    · have hz : p.2=0 := not_not.mp h
      apply mem_union_right
      simp only [mem_product,mem_singleton,level,mem_filter,mem_univ,true_and]
      exact ⟨by simpa [hz] using he.1,hz⟩
  have hcard : bad.card ≤ 2*(level Q c).card := by
    have h := (card_le_card hb).trans (card_union_le _ _)
    simpa [card_product,two_mul] using h
  have h := card_filter_add_card_filter_not (s := pairSet Q c)
    (fun p => p.1≠0 ∧ p.2≠0)
  change (nzPairSet Q c).card+bad.card=(pairSet Q c).card at h
  omega

def nzCls (x : V) (hx : x≠0) : NZClass V := ⟨cls x,by
  intro h
  have hh := (cls_eq_iff x 0).mp h
  exact hx (by simpa using hh)⟩

omit [AddCommGroup W] [Fintype V] [Fintype W] in
lemma rel_of_representatives (heven : ∀ x, Q (-x)=Q x) {x y : V}
    (hx : x≠0) (hy : y≠0) (h : pointRel Q c x y) :
    signedRel Q c (nzCls x hx) (nzCls y hy) := by
  change Q (rep (cls x)+rep (cls y))=c ∧ Q (rep (cls x)-rep (cls y))=c
  rcases rep_cls x with hx' | hx' <;> rcases rep_cls y with hy' | hy'
  · simpa only [hx',hy'] using h
  · simpa only [hx',hy',sub_neg_eq_add,sub_eq_add_neg,neg_neg] using And.symm h
  · rw [hx',hy',show -x+y= -(x-y) by abel,show -x-y= -(x+y) by abel,heven,heven]
    exact And.symm h
  · rw [hx',hy',← neg_add,show -x- -y= -(x-y) by abel,heven,heven]
    exact h

abbrev SignedEdges := Σ u : NZClass V, ↥(signedRows Q c u)
def compress (heven : ∀ x, Q (-x)=Q x) (p : ↥(nzPairSet Q c)) : SignedEdges Q c := by
  have hp := mem_filter.mp p.property
  let u := nzCls p.val.1 hp.2.1
  let v := nzCls p.val.2 hp.2.2
  refine ⟨u,⟨v,?_⟩⟩
  simp only [signedRows,mem_filter,mem_univ,true_and]
  exact rel_of_representatives Q c heven hp.2.1 hp.2.2 ((mem_filter.mp hp.1).2)

omit [AddCommGroup W] [Fintype W] in
lemma compress_fiber (heven : ∀ x, Q (-x)=Q x) (e : SignedEdges Q c) :
    (univ.filter (fun p : ↥(nzPairSet Q c) => compress Q c heven p=e)).card ≤ 4 := by
  let T : Finset (V × V) := {rep e.1.val,-rep e.1.val} ×ˢ
    {rep e.2.val.val,-rep e.2.val.val}
  have hc := card_le_card_of_injOn
    (s := univ.filter (fun p : ↥(nzPairSet Q c) => compress Q c heven p=e))
    (t := T) Subtype.val (by
      intro p hp
      have he : compress Q c heven p=e := (mem_filter.mp hp).2
      have h₁ : cls p.val.1=e.1.val := congrArg (fun z : SignedEdges Q c => z.1.val) he
      have h₂ : cls p.val.2=e.2.val.val := congrArg (fun z : SignedEdges Q c => z.2.val.val) he
      rw [← cls_rep e.1.val] at h₁
      rw [← cls_rep e.2.val.val] at h₂
      exact mem_product.mpr ⟨by simpa using (cls_eq_iff _ _).mp h₁,
        by simpa using (cls_eq_iff _ _).mp h₂⟩)
    (by intro a ha b hb hab; exact Subtype.ext hab)
  have hT : T.card≤4 := by
    dsimp [T]
    rw [card_product]
    have h₁ : ({rep e.1.val,-rep e.1.val} : Finset V).card≤2 := by simpa using card_insert_le _ ({-rep e.1.val} : Finset V)
    have h₂ : ({rep e.2.val.val,-rep e.2.val.val} : Finset V).card≤2 := by simpa using card_insert_le _ ({-rep e.2.val.val} : Finset V)
    nlinarith
  exact hc.trans hT

omit [AddCommGroup W] [Fintype W] in
lemma compressed_count (heven : ∀ x, Q (-x)=Q x) :
    (nzPairSet Q c).card ≤ 4*(∑ u : NZClass V, (signedRows Q c u).card) := by
  have h := card_le_mul_card_image_of_maps_to
    (s := (univ : Finset ↥(nzPairSet Q c))) (t := (univ : Finset (SignedEdges Q c)))
    (f := compress Q c heven) (fun _ _ => mem_univ _) 4 (fun e _ => compress_fiber Q c heven e)
  simpa only [card_univ,Fintype.card_coe,Fintype.card_sigma] using h

omit [AddCommGroup W] [Fintype W] in
include h2 in
/-- Compression loses at most four per nondegenerate pair; axes cost at most 2|S|. -/
theorem signed_square_bound (heven : ∀ x, Q (-x)=Q x) :
    (level Q c).card^2 ≤ 4*(∑ u : NZClass V, (signedRows Q c u).card)+2*(level Q c).card := by
  rw [← pair_card h2]
  exact (discarded_pairs Q c).trans (Nat.add_le_add_right (compressed_count Q c heven) _)

omit [AddCommGroup W] [Fintype W] in
/-- Signed classes inject into their actual representatives, also on each color fiber. -/
lemma class_fiber_bound (q : ℕ) (hq : ∀ w, Fintype.card {x : V // Q x=w}≤q^2) (w : W) :
    Fintype.card {u : NZClass V // Q (rep u.val)=w}≤q^2 := by
  let f : {u : NZClass V // Q (rep u.val)=w} → {x : V // Q x=w} :=
    fun u => ⟨rep u.val.val,u.property⟩
  have hi : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    apply rep_injective
    exact congrArg Subtype.val h
  exact (Fintype.card_le_of_injective f hi).trans (hq w)

include h2 in
/-- A balanced quadratic fiber is too large for K44-freeness once its square
exceeds this explicit signed-C4 budget. -/
theorem quadratic_fiber_bound (heven : ∀ x, Q (-x)=Q x)
    (hW : Function.Injective (fun w : W => w+w))
    (hpar : ∀ x y, Q (x+y)+Q (x-y)=(Q x+Q y)+(Q x+Q y))
    (q : ℕ) (hq : ∀ w, Fintype.card {x : V // Q x=w}≤q^2)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (connectionRows Q c))) :
    (level Q c).card^2 ≤ 4*(q+1)*Fintype.card V+2*(level Q c).card := by
  have hfree := signed_free h2 Q c heven hf
  have hcol (u v : NZClass V) (hv : v ∈ signedRows Q c u) :
      Q (rep u.val)=c-Q (rep v.val) := by
    have hh := signed_color Q c hW hpar ((mem_filter.mp hv).2)
    rw [hh]
    abel
  have hb := Erdos714ColoredC4.colored_bound (signedRows Q c)
    (fun u => Q (rep u.val)) (fun v => c-Q (rep v.val)) hcol q
    (class_fiber_bound Q q hq) hfree
  have hn : Fintype.card (NZClass V)≤Fintype.card V :=
    Fintype.card_le_of_injective _ rep_injective
  have hs := signed_square_bound h2 Q c heven
  calc
    _ ≤ 4*(q*Fintype.card (NZClass V)+Fintype.card (NZClass V))+2*(level Q c).card := by omega
    _ ≤ 4*(q*Fintype.card V+Fintype.card V)+2*(level Q c).card := by gcongr
    _ = _ := by ring

/-- A convenient integer form of the resulting two-thirds power obstruction.
The constant is intentionally not optimized. -/
lemma cubic_budget (s N C : ℕ) (hC : 1≤C) (hsN : s≤N)
    (h : s^2≤4*(Nat.sqrt (C*s)+2)*N+2*s) : s^3≤576*C*N^2 := by
  by_cases hs : 4≤s
  · have hCs : 1≤C*s := by nlinarith
    have hk := Nat.sqrt_le' (C*s)
    have hk' := Nat.sqrt_le_self (C*s)
    have hr : (Nat.sqrt (C*s)+2)^2≤9*C*s := by nlinarith
    have hs4 : 4*s≤s^2 := by nlinarith
    have hlow : s^2≤8*(Nat.sqrt (C*s)+2)*N := by nlinarith
    have hh : s^4≤576*C*s*N^2 := by
      calc
        _ = (s^2)^2 := by ring
        _ ≤ (8*(Nat.sqrt (C*s)+2)*N)^2 := Nat.pow_le_pow_left hlow 2
        _ = 64*(Nat.sqrt (C*s)+2)^2*N^2 := by ring
        _ ≤ 64*(9*C*s)*N^2 := by gcongr
        _ = _ := by ring
    have hm : s*s^3≤s*(576*C*N^2) := by nlinarith [hh]
    exact Nat.le_of_mul_le_mul_left hm (by omega)
  · have hs3 : s≤3 := by omega
    calc
      s^3 = s*s^2 := by ring
      _ ≤ 3*N^2 := by gcongr
      _ ≤ 576*C*N^2 := by nlinarith [Nat.mul_le_mul_right (N^2) hC]

include h2 in
/-- If all fibers are within a fixed factor of this one, its connection set
has at most the two-thirds power scale, rather than the conjectured three-quarters scale. -/
theorem balanced_fiber_cubic_bound (heven : ∀ x, Q (-x)=Q x)
    (hW : Function.Injective (fun w : W => w+w))
    (hpar : ∀ x y, Q (x+y)+Q (x-y)=(Q x+Q y)+(Q x+Q y))
    (C : ℕ) (hC : 1≤C)
    (hbal : ∀ w, Fintype.card {x : V // Q x=w}≤C*(level Q c).card)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (connectionRows Q c))) :
    (level Q c).card^3≤576*C*(Fintype.card V)^2 := by
  let s := (level Q c).card
  let q := Nat.sqrt (C*s)+1
  have hq (w : W) : Fintype.card {x : V // Q x=w}≤q^2 :=
    (hbal w).trans (Nat.lt_succ_sqrt' (C*s)).le
  have h := quadratic_fiber_bound h2 Q c heven hW hpar q hq hf
  have hs : s≤Fintype.card V := card_le_univ _
  apply cubic_budget s (Fintype.card V) C hC hs
  simpa only [q,Nat.add_assoc] using h

#print axioms pair_card
#print axioms compressed_count
#print axioms signed_square_bound
#print axioms quadratic_fiber_bound
#print axioms balanced_fiber_cubic_bound
end Erdos714SignedQuadratic
