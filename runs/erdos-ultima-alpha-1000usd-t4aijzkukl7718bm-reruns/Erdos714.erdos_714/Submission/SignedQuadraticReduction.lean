import Submission.UnbalancedBounds

/-!
Signed rectangles in odd-order additive groups. This is an obstruction tool
for quadratic translation graphs, not a proof of Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714SignedQuadratic
open Erdos714Packing
variable {V : Type*} [AddCommGroup V]

def signSetoid (V : Type*) [AddCommGroup V] : Setoid V where
  r x y := x = y ∨ x = -y
  iseqv := ⟨fun _ => Or.inl rfl, by
    intro x y h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h,neg_neg]), by
    intro x y z hxy hyz
    rcases hxy with rfl | rfl <;> rcases hyz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)⟩

abbrev SignClass (V : Type*) [AddCommGroup V] := Quotient (signSetoid V)
def cls (x : V) : SignClass V := Quotient.mk _ x
lemma cls_eq_iff (x y : V) : cls x = cls y ↔ x=y ∨ x=-y := Quotient.eq
lemma cls_neg (x : V) : cls (-x) = cls x := (cls_eq_iff _ _).mpr (Or.inr rfl)
def rep (u : SignClass V) : V := u.out
lemma cls_rep (u : SignClass V) : cls (rep u) = u := Quotient.out_eq u
lemma rep_cls (x : V) : rep (cls x)=x ∨ rep (cls x)=-x :=
  (cls_eq_iff _ _).mp (cls_rep _)

abbrev NZClass (V : Type*) [AddCommGroup V] := {u : SignClass V // u ≠ cls 0}
lemma rep_ne_zero (u : NZClass V) : rep u.val ≠ 0 := by
  intro h
  apply u.property
  rw [← cls_rep u.val,h]
lemma rep_injective : Function.Injective (fun u : NZClass V => rep u.val) := by
  intro u v h
  apply Subtype.ext
  change rep u.val = rep v.val at h
  rw [← cls_rep u.val,← cls_rep v.val,h]

variable (h2 : Function.Injective (fun x : V => x+x))
include h2 in
lemma ne_neg_of_ne_zero {x : V} (hx : x ≠ 0) : x ≠ -x := by
  intro h
  apply hx
  apply h2
  change x+x=0+0
  calc
    x+x = -x+x := congrArg (·+x) h
    _ = 0+0 := by simp

def signed (b : Bool) (x : V) : V := if b then -x else x
lemma cls_signed (b : Bool) (x : V) : cls (signed b x)=cls x := by
  cases b <;> simp [signed,cls_neg]
include h2 in
lemma signed_injective (f : Fin 2 ↪ NZClass V) :
    Function.Injective (fun p : Bool × Fin 2 => signed p.1 (rep (f p.2).val)) := by
  intro p q h
  have hi : p.2=q.2 := by
    apply f.injective
    apply Subtype.ext
    have hh := congrArg cls h
    simpa only [cls_signed,cls_rep] using hh
  rcases p with ⟨b,i⟩
  rcases q with ⟨c,j⟩
  dsimp at hi
  subst j
  have hn := ne_neg_of_ne_zero h2 (rep_ne_zero (f i))
  cases b <;> cases c <;> simp_all [signed]

def fourEquiv : Fin 4 ≃ Bool × Fin 2 := Fintype.equivOfCardEq (by simp)
def signedFour (f : Fin 2 ↪ NZClass V) : Fin 4 ↪ V :=
  fourEquiv.toEmbedding.trans ⟨_,signed_injective h2 f⟩

variable {W : Type*} [AddCommGroup W]
variable (Q : V → W) (c : W)

def connectionRows [Fintype V] (x : V) : Finset V := univ.filter (fun y => Q (x+y)=c)
def signedRel (u v : NZClass V) : Prop :=
  Q (rep u.val+rep v.val)=c ∧ Q (rep u.val-rep v.val)=c

def signedRows [Fintype (NZClass V)] (u : NZClass V) : Finset (NZClass V) :=
  univ.filter (signedRel Q c u)

omit [AddCommGroup W] in
lemma signed_incidence (heven : ∀ x, Q (-x)=Q x) {u v : NZClass V}
    (h : signedRel Q c u v) (b d : Bool) :
    Q (signed b (rep u.val)+signed d (rep v.val))=c := by
  cases b <;> cases d
  · exact h.1
  · simpa only [signed,Bool.false_eq_true,if_false,if_true,sub_eq_add_neg] using h.2
  · change Q (-rep u.val+rep v.val)=c
    rw [show -rep u.val+rep v.val= -(rep u.val-rep v.val) by abel,heven]
    exact h.2
  · change Q (-rep u.val+-rep v.val)=c
    rw [← neg_add,heven]
    exact h.1

omit [AddCommGroup W] in
include h2 in
/-- A signed C4 gives an actual K44, including all vertex-injectivity conditions. -/
theorem signed_free [Fintype V] [Fintype (NZClass V)]
    (heven : ∀ x, Q (-x)=Q x)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (connectionRows Q c))) :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free (incidence (signedRows Q c)) := by
  rw [free_iff_no_rectangle _ (by decide)] at hfree ⊢
  intro f g hfg
  apply hfree (signedFour h2 f) (signedFour h2 g)
  intro i j
  simp only [connectionRows,mem_filter,mem_univ,true_and]
  apply signed_incidence Q c heven
  have h := hfg (fourEquiv i).2 (fourEquiv j).2
  simpa only [signedRows,mem_filter,mem_univ,true_and] using h

/-- Parallelogram identities force a single complementary color for each signed edge. -/
lemma signed_color (hW : Function.Injective (fun w : W => w+w))
    (hpar : ∀ x y, Q (x+y)+Q (x-y)=(Q x+Q y)+(Q x+Q y))
    {u v : NZClass V} (h : signedRel Q c u v) : Q (rep v.val)=c-Q (rep u.val) := by
  have hh := hpar (rep u.val) (rep v.val)
  rw [h.1,h.2] at hh
  have he := hW hh
  exact eq_sub_of_add_eq' he.symm

#print axioms signed_free
#print axioms signed_color
end Erdos714SignedQuadratic
