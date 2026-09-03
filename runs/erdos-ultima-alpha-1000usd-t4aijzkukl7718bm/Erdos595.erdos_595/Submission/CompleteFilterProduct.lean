import Submission.Work

/-!
An obstruction for countably complete reduced products. If every coordinate
 graph is finitely vertex-colourable, the reduced-product graph is itself
finitely vertex-colourable. The ultrafilter used in the proof is an ordinary
ultrafilter extending a restriction of the original filter; it is NOT assumed
to be countably complete.

This is an auxiliary result, not a settlement of Erdős Problem 595.
-/

set_option autoImplicit false
open SimpleGraph Set Filter

namespace Erdos595CompleteFilterProduct

variable {I : Type*} {A : I → Type*}

/-- Adjacency holds on a filter-large set of coordinates. -/
def graph (F : Filter I) [F.NeBot] (G : ∀ i, SimpleGraph (A i)) :
    SimpleGraph (∀ i, A i) where
  Adj x y := ∀ᶠ i in F, (G i).Adj (x i) (y i)
  symm := fun _ _ h => h.mono fun _ hi => hi.symm
  loopless := fun x h => by
    obtain ⟨i, hi⟩ := h.exists
    exact (G i).loopless (x i) hi

/-- A map to a countable set has a positive fibre for a proper countably
complete filter. Positive need not mean filter-large. -/
theorem positive_fibre (F : Filter I) [F.NeBot] [CountableInterFilter F]
    {C : Type*} [Countable C] (f : I → C) :
    ∃ c, (F ⊓ Filter.principal {i | f i = c}).NeBot := by
  classical
  by_contra hn
  push_neg at hn
  have hall : ∀ c, ∀ᶠ i in F, f i ≠ c := by
    intro c
    have hb : F ⊓ Filter.principal {i | f i = c} = ⊥ := by
      simpa only [Filter.neBot_iff, not_not] using hn c
    exact Filter.inf_principal_eq_bot.mp hb
  obtain ⟨i, hi⟩ := (eventually_countable_forall.mpr hall).exists
  exact hi (f i) rfl

/-- A uniform finite colour bound on any positive set of coordinates already
colours the whole reduced product. -/
theorem colorable_of_positive (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i)) (n : ℕ)
    (hn : (F ⊓ Filter.principal {i | (G i).Colorable (n + 1)}).NeBot) :
    (graph F G).Colorable (n + 1) := by
  classical
  let S : Set I := {i | (G i).Colorable (n + 1)}
  letI : (F ⊓ Filter.principal S).NeBot := hn
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (F ⊓ Filter.principal S)
  have hUF : (U : Filter I) ≤ F := hU.trans inf_le_left
  have hUS : S ∈ (U : Filter I) :=
    (hU.trans inf_le_right) (Filter.mem_principal_self S)
  let label (i : I) : A i → Fin (n + 1) :=
    if h : (G i).Colorable (n + 1) then h.some else fun _ => 0
  have hlabel : ∀ i ∈ S, ∀ {x y : A i}, (G i).Adj x y → label i x ≠ label i y := by
    intro i hi x y hxy
    change (G i).Colorable (n + 1) at hi
    dsimp [label]
    rw [dif_pos hi]
    exact hi.some.valid hxy
  have hlimit : ∀ x : (∀ i, A i), ∃ k : Fin (n + 1),
      ∀ᶠ i in (U : Filter I), label i (x i) = k := by
    intro x
    apply Ultrafilter.eventually_exists_iff.mp
    exact Filter.Eventually.of_forall fun i => ⟨label i (x i), rfl⟩
  choose c hc using hlimit
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro x y hxy heq
  have hadj : ∀ᶠ i in (U : Filter I), (G i).Adj (x i) (y i) := hUF hxy
  have hset : ∀ᶠ i in (U : Filter I), i ∈ S := hUS
  have hevent : ∀ᶠ i in (U : Filter I),
      (G i).Adj (x i) (y i) ∧ i ∈ S ∧
        label i (x i) = c x ∧ label i (y i) = c y :=
    hadj.and (hset.and ((hc x).and (hc y)))
  obtain ⟨i, hi⟩ := hevent.exists
  exact hlabel i hi.2.1 hi.1 (hi.2.2.1.trans (heq.trans hi.2.2.2.symm))

/-- Countable completeness prevents finite chromatic numbers from escaping
to infinity on every positive set. -/
theorem finitely_colorable (F : Filter I) [F.NeBot] [CountableInterFilter F]
    (G : ∀ i, SimpleGraph (A i)) (hG : ∀ i, ∃ n, (G i).Colorable n) :
    ∃ n, (graph F G).Colorable n := by
  classical
  choose bound hbound using hG
  obtain ⟨n, hn⟩ := positive_fibre F bound
  have hsub : {i | bound i = n} ⊆ {i | (G i).Colorable (n + 1)} := by
    intro i hi
    have hc : (G i).Colorable n := hi ▸ hbound i
    exact hc.mono (Nat.le_succ n)
  have hne : (F ⊓ Filter.principal {i | (G i).Colorable (n + 1)}).NeBot :=
    hn.mono (inf_le_inf_left F (Filter.principal_mono.mpr hsub))
  exact ⟨n + 1, colorable_of_positive F G n hne⟩

/-- In particular, arbitrary finite coordinate vertex sets cannot give a
witness through a countably complete filter. -/
theorem finite_coordinates (F : Filter I) [F.NeBot] [CountableInterFilter F]
    (G : ∀ i, SimpleGraph (A i)) [∀ i, Finite (A i)] :
    ∃ n, (graph F G).Colorable n := by
  classical
  letI (i : I) : Fintype (A i) := Fintype.ofFinite (A i)
  apply finitely_colorable F G
  intro i
  refine ⟨Fintype.card (A i), ?_⟩
  exact ⟨SimpleGraph.Coloring.mk (Fintype.equivFin (A i))
    (fun h he => h.ne ((Fintype.equivFin (A i)).injective he))⟩

/-- A finite proper colouring supplies the required countable edge cover. -/
theorem cover_of_colorable {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (hG : G.Colorable n) : Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  obtain ⟨c⟩ := hG
  let f : V → ℕ → Fin 2 := fun x k => if (c x).val = k then 1 else 0
  apply Erdos595Work.countable_union_of_coloring G
  refine SimpleGraph.Coloring.mk f ?_
  intro x y hxy he
  have hne : (c y).val ≠ (c x).val :=
    fun h => c.valid hxy (Fin.ext h.symm)
  have hv := congrFun he (c x).val
  simp [f, hne] at hv

/-- The countably complete product of finitely colourable coordinate graphs
is countably triangle-free coverable, regardless of its cardinality. -/
theorem countable_cover (F : Filter I) [F.NeBot] [CountableInterFilter F]
    (G : ∀ i, SimpleGraph (A i)) (hG : ∀ i, ∃ n, (G i).Colorable n) :
    Erdos595Work.IsCountableUnionOfTriangleFree (graph F G) := by
  obtain ⟨n, hn⟩ := finitely_colorable F G hG
  exact cover_of_colorable (graph F G) hn

/-- This also applies after choosing representatives in a quotient. For the
usual eventual-equality quotient, coordinate adjacency is independent of
the choice of representatives. -/
theorem quotient_countable_cover (F : Filter I) [F.NeBot] [CountableInterFilter F]
    (G : ∀ i, SimpleGraph (A i)) (hG : ∀ i, ∃ n, (G i).Colorable n)
    (s : Setoid (∀ i, A i)) :
    Erdos595Work.IsCountableUnionOfTriangleFree
      ((graph F G).comap (Quotient.out : Quotient s → (∀ i, A i))) :=
  Erdos595Work.countable_union_of_hom (SimpleGraph.Hom.comap _ _)
    (countable_cover F G hG)

#print axioms countable_cover
#print axioms quotient_countable_cover
#print axioms positive_fibre
#print axioms colorable_of_positive
#print axioms finitely_colorable
#print axioms finite_coordinates
end Erdos595CompleteFilterProduct
