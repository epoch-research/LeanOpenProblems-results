import Submission.ArcAdjoint

/-!
Elementary finite ranking for bounded increasing paths. Auxiliary work for
ordered-cycle obstructions to right-adjoint constructions; not a settlement
of Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595BoundedPath

variable {A B : Type*}

inductive Chain (r : A → A → Prop) : ℕ → A → A → Prop
  | nil (a : A) : Chain r 0 a a
  | snoc {n a b c} : Chain r n a b → r b c → Chain r (n+1) a c

namespace Chain
variable {r : A → A → Prop} {s : B → B → Prop}

lemma single {a b} (h : r a b) : Chain r 1 a b := .snoc (.nil a) h

lemma append {m n a b c} (h : Chain r m a b) (k : Chain r n b c) :
    Chain r (m+n) a c := by
  induction k with
  | nil => simpa using h
  | snoc _ hk ih => exact .snoc (ih h) hk

lemma prepend {n a b c} (h : r a b) (k : Chain r n b c) :
    Chain r (n+1) a c := by
  simpa only [Nat.add_comm 1 n] using (single h).append k

lemma map {n a b} (h : Chain r n a b) (f : A → B)
    (hf : ∀ x y, r x y → s (f x) (f y)) : Chain s n (f a) (f b) := by
  induction h with
  | nil => exact .nil _
  | snoc _ hab ih => exact .snoc ih (hf _ _ hab)

lemma constant {n a b} (h : Chain r n a b) (f : A → B)
    (hf : ∀ x y, r x y → f x = f y) : f a = f b := by
  induction h with
  | nil => rfl
  | snoc _ hab ih => exact ih.trans (hf _ _ hab)

lemma mono {n a b} (h : Chain r n a b) [Preorder B] (f : A → B)
    (hf : ∀ x y, r x y → f x ≤ f y) : f a ≤ f b := by
  induction h with
  | nil => exact le_rfl
  | snoc _ hab ih => exact ih.trans (hf _ _ hab)

lemma split_last {n a c} (h : Chain r (n+1) a c) :
    ∃ b, Chain r n a b ∧ r b c := by
  cases h with
  | snoc h hbc => exact ⟨_,h,hbc⟩

/-- An odd alternating path ends on the other side. -/
lemma odd_bool {n a b} (h : Chain r (2*n+1) a b) (tag : A → Bool)
    (ht : ∀ x y, r x y → tag x ≠ tag y) : tag a ≠ tag b := by
  induction n generalizing a b with
  | zero =>
    obtain ⟨c,hac,hcb⟩ := h.split_last
    cases hac
    exact ht _ _ hcb
  | succ n ih =>
    have hn : 2*(n+1)+1 = (2*n+1)+1+1 := by omega
    rw [hn] at h
    obtain ⟨c,hac,hcb⟩ := h.split_last
    obtain ⟨d,had,hdc⟩ := hac.split_last
    have h₁ := ih had
    have h₂ := ht _ _ hdc
    have h₃ := ht _ _ hcb
    cases ha : tag a <;> cases hd : tag d <;> cases hc : tag c <;>
      cases hb : tag b <;> simp_all

end Chain

/-- Any relation with a uniform finite path bound has a finite strictly
increasing rank. No finiteness assumption on its underlying type is needed. -/
theorem finite_rank (r : A → A → Prop) (N : ℕ)
    (hN : ∀ a b, ¬Chain r N a b) :
    ∃ h : A → Fin (N+1), ∀ a b, r a b → h a < h b := by
  classical
  let reachable (n : ℕ) (b : A) : Prop := ∃ a, Chain r n a b
  have hex (b : A) : ∃ n, ¬reachable n b := ⟨N,fun ⟨a,h⟩ => hN a b h⟩
  let height (b : A) : ℕ := Nat.find (hex b)
  have hbound (b : A) : height b ≤ N := Nat.find_min' (hex b) (fun ⟨a,h⟩ => hN a b h)
  have hpos (b : A) : 0 < height b := by
    by_contra hn
    have hh : height b = 0 := by omega
    have h := Nat.find_spec (hex b)
    change ¬reachable (height b) b at h
    exact h (hh ▸ ⟨b,Chain.nil b⟩)
  have hstep (a b : A) (hab : r a b) : height a < height b := by
    by_contra hn
    obtain ⟨n,he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hpos b))
    have hsmall : n < height a := by omega
    have ha : reachable n a := Classical.not_not.mp (Nat.find_min (hex a) hsmall)
    obtain ⟨x,hxa⟩ := ha
    have hb := Nat.find_spec (hex b)
    change ¬reachable (height b) b at hb
    apply hb
    rw [he]
    exact ⟨x,Chain.snoc hxa hab⟩
  exact ⟨fun a => ⟨height a,Nat.lt_succ_of_le (hbound a)⟩,fun a b hab => hstep a b hab⟩

/-- A finite proper arc coloring gives a finite proper coloring of the
original graph, using the sets of colors of its outgoing arcs. -/
noncomputable def coloring_of_arc {C : Type*} (G : SimpleGraph A)
    (c : (Erdos595ArcAdjoint.arcGraph G).Coloring C) : G.Coloring (Set C) :=
  SimpleGraph.Coloring.mk (fun a => {k | ∃ e : Erdos595ArcAdjoint.Arc G, e.1.1 = a ∧ c e = k})
    (by
      intro a b hab he
      let e : Erdos595ArcAdjoint.Arc G := ⟨(a,b),hab⟩
      have hm : c e ∈ {k | ∃ e : Erdos595ArcAdjoint.Arc G, e.1.1 = a ∧ c e = k} :=
        ⟨e,rfl,rfl⟩
      dsimp only at he
      rw [he] at hm
      obtain ⟨d,hd,heq⟩ := hm
      exact c.valid (Or.inl hd.symm) heq.symm)

def arcMap {F : SimpleGraph A} {G : SimpleGraph B} (f : F →g G) :
    Erdos595ArcAdjoint.arcGraph F →g Erdos595ArcAdjoint.arcGraph G where
  toFun e := ⟨(f e.1.1,f e.1.2),f.map_adj e.2⟩
  map_rel' := by
    intro e d hed
    exact hed.elim (fun h => Or.inl (congrArg f h)) (fun h => Or.inr (congrArg f h))

def reverseArc (F : SimpleGraph A) : Erdos595ArcAdjoint.arcGraph F →g Erdos595ArcAdjoint.arcGraph F where
  toFun e := ⟨(e.1.2,e.1.1),e.2.symm⟩
  map_rel' := by
    intro e d hed
    exact hed.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)

/-- A countable partition with countably colorable induced pieces gives a
countable PROPER coloring, not just a triangle-free edge cover. -/
theorem coloring_of_countable_fibers {C : Type*} [Countable C]
    (F : SimpleGraph A) (tag : A → C)
    (hc : ∀ i, Nonempty ((F.induce {a | tag a = i}).Coloring ℕ)) :
    Nonempty (F.Coloring ℕ) := by
  classical
  let ci (i : C) := Classical.choice (hc i)
  let f (i : C) (a : A) : ℕ := if h : tag a = i then ci i ⟨a,h⟩ else 0
  obtain ⟨enc,henc⟩ := exists_injective_nat (C × ℕ)
  refine ⟨SimpleGraph.Coloring.mk (fun a => enc (tag a,f (tag a) a)) ?_⟩
  intro a b hab he
  have he' := henc he
  have ht : tag a = tag b := congrArg Prod.fst he'
  have hf : f (tag a) a = f (tag b) b := congrArg Prod.snd he'
  rw [ht] at hf
  have hf' : ci (tag b) ⟨a,ht⟩ = ci (tag b) ⟨b,rfl⟩ := by
    simpa only [f, dif_pos ht, dif_pos rfl] using hf
  have hab' :
      (F.induce {a | tag a = tag b}).Adj
        (⟨a, ht⟩ : {a | tag a = tag b})
        (⟨b, rfl⟩ : {a | tag a = tag b}) := hab
  exact (ci (tag b)).valid hab' hf'

#print axioms finite_rank
#print axioms coloring_of_arc
#print axioms coloring_of_countable_fibers
end Erdos595BoundedPath
