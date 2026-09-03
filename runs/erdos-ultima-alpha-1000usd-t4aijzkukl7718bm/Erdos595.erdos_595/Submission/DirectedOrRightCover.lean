import Submission.SecondArcBacktracking

/-!
One directed biclique right adjoint of a countable K4-free target, with OR
symmetrization, has a countable proper vertex coloring. Common anchor pairs
exclude even a directed walk of length two in each anchor class. A second
right stage therefore has a proper vertex palette Set N. No K4-freeness of
the right-adjoint graphs is assumed, and this does not settle Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595DirectedOrRight
open Erdos595DirectedRight Erdos595BoundedPath
variable {V W C : Type*}

def orGraph (R : V → V → Prop) (hR : Irreflexive R) : SimpleGraph V where
  Adj a b := R a b ∨ R b a
  symm := fun _ _ h => h.symm
  loopless := fun a h => h.elim (hR a) (hR a)

abbrev one (H : SimpleGraph W) := orGraph (right H.Adj) (right_irrefl H.loopless)
abbrev two (H : SimpleGraph W) :=
  orGraph (right (right H.Adj)) (right_irrefl (right_irrefl H.loopless))

noncomputable def tag (H : SimpleGraph W) (p : Biclique H.Adj) : Option (W × W) := by
  classical
  exact if h : p.val.1.Nonempty ∧ p.val.2.Nonempty then
    some (h.1.choose,h.2.choose) else none

lemma tag_some (H : SimpleGraph W) (p : Biclique H.Adj) (a b : W)
    (h : tag H p = some (a,b)) : a ∈ p.val.1 ∧ b ∈ p.val.2 := by
  classical
  unfold tag at h
  split_ifs at h with hp
  · have he := Option.some.inj h
    have ha := congrArg Prod.fst he
    have hb := congrArg Prod.snd he
    change hp.1.choose = a at ha
    change hp.2.choose = b at hb
    exact ⟨ha ▸ hp.1.choose_spec,hb ▸ hp.2.choose_spec⟩

/-- Two consecutive arrows with one common ordered anchor pair force K4. -/
theorem no_two (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (p q r : Biclique H.Adj) (hpq : right H.Adj p q) (hqr : right H.Adj q r)
    (h₁ : tag H p = tag H q) (h₂ : tag H q = tag H r) : False := by
  classical
  obtain ⟨x,hxP,hxQ⟩ := hpq
  obtain ⟨y,hyQ,hyR⟩ := hqr
  have hq : q.val.1.Nonempty ∧ q.val.2.Nonempty := ⟨⟨x,hxQ⟩,⟨y,hyQ⟩⟩
  have heq : tag H q = some (hq.1.choose,hq.2.choose) := by simp only [tag,dif_pos hq]
  let a := hq.1.choose
  let b := hq.2.choose
  have hp := tag_some H p a b (h₁.trans heq)
  have hr := tag_some H r a b (h₂.symm.trans heq)
  exact Erdos595Work.no_adj_common_neighbors hH
    (q.property a hq.1.choose_spec b hq.2.choose_spec)
    (p.property a hp.1 x hxP)
    (q.property x hxQ b hq.2.choose_spec).symm
    (q.property a hq.1.choose_spec y hyQ)
    (r.property y hyR b hr.2).symm
    (q.property x hxQ y hyQ)

/-- Every tag class is bipartite, and the tag palette is countable. -/
theorem one_countable [Countable W] (H : SimpleGraph W) (hH : H.CliqueFree 4) :
    Nonempty ((one H).Coloring ℕ) := by
  classical
  let R : Option (W × W) → Biclique H.Adj → Biclique H.Adj → Prop :=
    fun k p q => right H.Adj p q ∧ tag H p = k ∧ tag H q = k
  have hn (k : Option (W × W)) (p r : Biclique H.Adj) : ¬Chain (R k) 2 p r := by
    intro h
    obtain ⟨q,hpq,hqr⟩ := h.split_last
    obtain ⟨p',hpp',hpq⟩ := hpq.split_last
    cases hpp'
    exact no_two H hH p q r hpq.1 hqr.1
      (hpq.2.1.trans hpq.2.2.symm) (hqr.2.1.trans hqr.2.2.symm)
  choose rank hrank using fun k => finite_rank (R k) 2 (hn k)
  obtain ⟨enc,henc⟩ := exists_injective_nat (Option (W × W) × Fin 3)
  refine ⟨SimpleGraph.Coloring.mk (fun p => enc (tag H p,rank (tag H p) p)) ?_⟩
  intro p q hpq hh
  have he := henc hh
  have ht := congrArg Prod.fst he
  have hval := congrArg Prod.snd he
  change tag H p = tag H q at ht
  change rank (tag H p) p = rank (tag H q) q at hval
  rw [← ht] at hval
  rcases hpq with hpq | hqp
  · exact (hrank (tag H p) p q ⟨hpq,rfl,ht.symm⟩).ne hval
  · exact (hrank (tag H p) q p ⟨hqp,ht.symm,rfl⟩).ne hval.symm

/-- A proper coloring of a directed relation gives a powerset coloring of
its OR-symmetrized right adjoint, using incoming color sets. -/
def powersetColor {R : V → V → Prop} (hR : Irreflexive R)
    (c : (orGraph R hR).Coloring C) :
    (orGraph (right R) (right_irrefl hR)).Coloring (Set C) :=
  SimpleGraph.Coloring.mk (fun p => c '' p.val.1) (by
    intro p q hpq he
    have hdir : ∀ p q : Biclique R, right R p q → c '' p.val.1 = c '' q.val.1 → False := by
      intro p q hpq he
      obtain ⟨x,hxB,hxA⟩ := hpq
      have hx : c x ∈ c '' p.val.1 := he.symm ▸ Set.mem_image_of_mem c hxA
      obtain ⟨y,hy,hyx⟩ := hx
      exact c.valid (Or.inl (p.property y hy x hxB)) hyx
    exact hpq.elim (fun h => hdir p q h he) (fun h => hdir q p h he.symm))

/-- In particular the entire second OR right adjoint has a continuum-sized
proper palette. Its source need not be K4-free. -/
theorem two_powerset [Countable W] (H : SimpleGraph W) (hH : H.CliqueFree 4) :
    Nonempty ((two H).Coloring (Set ℕ)) := by
  obtain ⟨c⟩ := one_countable H hH
  exact ⟨powersetColor (right_irrefl H.loopless) c⟩

/-- Pull a directed arc labeling back through the right-adjoint coloring. -/
theorem one_pullback [Countable W] {R : V → V → Prop} (hR : Irreflexive R)
    (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (f : Arc R → W) (hf : ∀ e d, arc R e d → H.Adj (f e) (f d)) :
    Nonempty ((orGraph R hR).Coloring ℕ) := by
  obtain ⟨c⟩ := one_countable H hH
  let hom : orGraph R hR →g one H :=
    ⟨curry f hf,fun h => h.elim
      (fun h => Or.inl (curry_rel f hf h)) (fun h => Or.inr (curry_rel f hf h))⟩
  exact ⟨c.comp hom⟩

/-- The corresponding two-arc conclusion for arbitrary directed sources. -/
theorem two_pullback [Countable W] {R : V → V → Prop} (hR : Irreflexive R)
    (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (f : Arc (arc R) → W)
    (hf : ∀ e d, arc (arc R) e d → H.Adj (f e) (f d)) :
    Nonempty ((orGraph R hR).Coloring (Set ℕ)) := by
  obtain ⟨c⟩ := two_powerset H hH
  let p : V → Biclique (right H.Adj) := curry (curry f hf) (fun _ _ h => curry_rel f hf h)
  let hom : orGraph R hR →g two H :=
    ⟨p,fun h => h.elim
      (fun h => Or.inl (curry_rel (curry f hf) (fun _ _ h => curry_rel f hf h) h))
      (fun h => Or.inr (curry_rel (curry f hf) (fun _ _ h => curry_rel f hf h) h))⟩
  exact ⟨c.comp hom⟩

#print axioms no_two
#print axioms one_countable
#print axioms two_powerset
#print axioms two_pullback
end Erdos595DirectedOrRight
