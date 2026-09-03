import Submission.Work

/-!
Finite adapted labelings and extension of prescribed colorings.
This auxiliary file does not settle Erdős Problem 595.
-/

open SimpleGraph Set
namespace Erdos595FiniteAdapted

variable {V W : Type*}

def Valid (G : SimpleGraph V) (c : Sym2 V → ℕ) : Prop :=
  ∀ a b d, G.Adj a b → G.Adj a d → G.Adj b d →
    ¬(c s(a, b) = c s(a, d) ∧ c s(a, b) = c s(b, d))

def Adapted (G : SimpleGraph V) (c : Sym2 V → ℕ) (f : V → ℕ) : Prop :=
  ∀ a b, G.Adj a b → ¬(f a = c s(a, b) ∧ f b = c s(a, b))

/-- Keep old colors, use finite vertex labels across the cut, and a disjoint
palette on the new induced graph. -/
def extend (c : Sym2 V → ℕ) (d : Sym2 W → ℕ) (f : V → ℕ) (m : ℕ) :
    Sym2 (V ⊕ W) → ℕ :=
  Sym2.lift ⟨fun x y => match x, y with
    | .inl a, .inl b => c s(a, b)
    | .inl a, .inr _ => f a
    | .inr _, .inl a => f a
    | .inr a, .inr b => d s(a, b) + m,
    by intro x y; cases x <;> cases y <;> simp only [Sym2.eq_swap]⟩

theorem extend_valid (G : SimpleGraph (V ⊕ W))
    (c : Sym2 V → ℕ) (d : Sym2 W → ℕ) (f : V → ℕ) (m : ℕ)
    (hc : Valid (G.comap Sum.inl) c) (hd : Valid (G.comap Sum.inr) d)
    (hf : Adapted (G.comap Sum.inl) c f) (hm : ∀ v, f v < m) :
    Valid G (extend c d f m) := by
  intro a b t hab hat hbt heq
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      cases t with
      | inl t => exact hc a b t hab hat hbt heq
      | inr t =>
        change c s(a, b) = f a ∧ c s(a, b) = f b at heq
        exact hf a b hab ⟨heq.1.symm, heq.2.symm⟩
    | inr b =>
      cases t with
      | inl t =>
        change f a = c s(a, t) ∧ f a = f t at heq
        exact hf a t hat ⟨heq.1, heq.2.symm.trans heq.1⟩
      | inr t =>
        change f a = f a ∧ f a = d s(b, t) + m at heq
        have := hm a
        omega
  | inr a =>
    cases b with
    | inl b =>
      cases t with
      | inl t =>
        change f b = f t ∧ f b = c s(b, t) at heq
        exact hf b t hbt ⟨heq.2, heq.1.symm.trans heq.2⟩
      | inr t =>
        change f b = d s(a, t) + m ∧ f b = f b at heq
        have := hm b
        omega
    | inr b =>
      cases t with
      | inl t =>
        change d s(a, b) + m = f t ∧ d s(a, b) + m = f t at heq
        have := hm t
        omega
      | inr t =>
        change d s(a, b) + m = d s(a, t) + m ∧
          d s(a, b) + m = d s(b, t) + m at heq
        exact hd a b t hab hat hbt
          ⟨Nat.add_right_cancel heq.1, Nat.add_right_cancel heq.2⟩

theorem exists_extension (G : SimpleGraph (V ⊕ W)) (c : Sym2 V → ℕ)
    (hc : Valid (G.comap Sum.inl) c)
    (hf : ∃ (f : V → ℕ) (m : ℕ), Adapted (G.comap Sum.inl) c f ∧ ∀ v, f v < m)
    (hnew : Erdos595Work.IsCountableUnionOfTriangleFree (G.comap Sum.inr)) :
    ∃ e : Sym2 (V ⊕ W) → ℕ, Valid G e ∧
      ∀ a b : V, e s(Sum.inl a, Sum.inl b) = c s(a, b) := by
  obtain ⟨f, m, hf, hm⟩ := hf
  obtain ⟨d, hd⟩ := (Erdos595Work.countable_union_iff_edge_coloring _).mp hnew
  exact ⟨extend c d f m, extend_valid G c d f m hc hd hf hm, fun _ _ => rfl⟩

/-- Normalize the star at `p` to color zero, shifting all other old colors. -/
noncomputable def normalize (p : V) (c : Sym2 V → ℕ) : Sym2 V → ℕ := by
  classical
  exact Sym2.lift ⟨fun a b => if a = p ∨ b = p then 0 else c s(a, b) + 1,
    by intro a b; simp only [or_comm, Sym2.eq_swap]⟩

noncomputable def starLabel (p : V) (v : V) : ℕ := by
  classical
  exact if v = p then 1 else 0

lemma normalize_valid (G : SimpleGraph V) (p : V) (c : Sym2 V → ℕ)
    (hc : Valid G c) : Valid G (normalize p c) := by
  classical
  intro a b t hab hat hbt heq
  by_cases ha : a = p
  · subst a
    have hb := hab.ne.symm
    have ht := hat.ne.symm
    simp [normalize, hb, ht] at heq
  · by_cases hb : b = p
    · subst b
      have ht := hbt.ne.symm
      simp [normalize, ha, ht] at heq
    · by_cases ht : t = p
      · subst t
        simp [normalize, ha, hb] at heq
      · simp only [normalize, Sym2.lift_mk, ha, hb, ht, or_self, if_false,
          Nat.add_right_cancel_iff] at heq
        exact hc a b t hab hat hbt heq

lemma normalize_adapted (G : SimpleGraph V) (p : V) (c : Sym2 V → ℕ) :
    Adapted G (normalize p c) (starLabel p) := by
  classical
  intro a b hab heq
  by_cases ha : a = p
  · subst a
    have hb := hab.ne.symm
    simp [normalize, starLabel, hb] at heq
  · by_cases hb : b = p
    · subst b
      simp [normalize, starLabel, ha] at heq
    · simp [normalize, starLabel, ha, hb] at heq

lemma starLabel_lt (p : V) (v : V) : starLabel p v < 2 := by
  classical
  simp only [starLabel]
  split_ifs <;> omega

/-- A nonempty countably coverable graph has a coloring which is finitely
adapted and therefore extends over every countably coverable new vertex piece. -/
theorem exists_finitely_adapted (G : SimpleGraph V) (p : V)
    (hG : Erdos595Work.IsCountableUnionOfTriangleFree G) :
    ∃ (c : Sym2 V → ℕ) (f : V → ℕ), Valid G c ∧ Adapted G c f ∧ ∀ v, f v < 2 := by
  obtain ⟨c, hc⟩ := (Erdos595Work.countable_union_iff_edge_coloring _).mp hG
  exact ⟨normalize p c, starLabel p, normalize_valid G p c hc,
    normalize_adapted G p c, starLabel_lt p⟩

#print axioms exists_extension
#print axioms exists_finitely_adapted
end Erdos595FiniteAdapted
