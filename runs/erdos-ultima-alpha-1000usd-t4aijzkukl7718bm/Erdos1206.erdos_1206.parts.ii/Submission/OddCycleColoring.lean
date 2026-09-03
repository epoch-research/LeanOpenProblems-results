import Submission.StrictCubeCollision
import Submission.SummableSourceColoring

/-!
An exact finite-obstruction criterion for odd-parity hypergraph colorings,
and a conditional sufficient criterion for the positive-density conjecture.
No arithmetic sieve satisfying the criterion is constructed here.
-/

namespace Erdos1206.OddCycleColoring
open Finset
open scoped Classical

/-- Consistent prescribed values on a family of vectors extend to a linear
functional. Consistency is tested on finitely supported relations. -/
theorem exists_functional_of_relations
    {K V E : Type*} [Field K] [AddCommGroup V] [Module K V]
    (r : E → V) (b : E → K)
    (h : ∀ f : E →₀ K, (f.sum fun e a => a • r e) = 0 →
      (f.sum fun e a => a * b e) = 0) :
    ∃ l : V →ₗ[K] K, ∀ e, l (r e) = b e := by
  classical
  let U : Submodule K (V × K) :=
    Submodule.span K (Set.range (fun e => (r e, b e)))
  have hv : (0, (1 : K)) ∉ U := by
    intro hv
    obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
    have hfst := congrArg (LinearMap.fst K V K) hf
    have hsnd := congrArg (LinearMap.snd K V K) hf
    simp only [map_finsuppSum, map_smul, LinearMap.fst_apply,
      LinearMap.snd_apply, smul_eq_mul] at hfst hsnd
    have hz := h f hfst
    exact zero_ne_one (hz.symm.trans hsnd)
  obtain ⟨g, hg, hg1⟩ := LinearMap.exists_extend_of_notMem
    (0 : U →ₗ[K] K) hv (1 : K)
  have hgU (v : V × K) (hv : v ∈ U) : g v = 0 := by
    have hh := LinearMap.congr_fun hg (⟨v, hv⟩ : U)
    simpa using hh
  refine ⟨(-g).comp (LinearMap.inl K V K), ?_⟩
  intro e
  have hz := hgU (r e, b e) (Submodule.subset_span (Set.mem_range_self e))
  have he : (r e, b e) = (r e, 0) + b e • (0, (1 : K)) := by
    simp
  rw [he, map_add, map_smul, hg1, smul_eq_mul, mul_one] at hz
  change -g (r e, 0) = b e
  exact neg_eq_iff_add_eq_zero.mpr hz

/-- A row records the vertices of a finite hyperedge over F₂. -/
noncomputable def row {V : Type*} (e : Finset V) : V →₀ ZMod 2 :=
  ∑ v ∈ e, Finsupp.single v 1

@[simp] lemma row_apply {V : Type*} (e : Finset V) (v : V) :
    row e v = if v ∈ e then 1 else 0 := by
  classical
  simp [row, Finsupp.single_apply]

/-- Every finite even-incidence edge collection has even cardinality.
Edges are indexed, so the criterion also allows repetitions in the family. -/
def NoOddCycle {V E : Type*} (edge : E → Finset V) : Prop :=
  ∀ s : Finset E, (∀ v, Even (s.filter fun e => v ∈ edge e).card) → Even s.card

private lemma two_ne_zero_eq_one (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  have hx : x = 0 ∨ x = 1 := by revert x; decide +kernel
  exact hx.resolve_left h

/-- With no odd even-incidence edge collection, all edge sums can be made 1. -/
theorem exists_odd_coloring {V E : Type*} (edge : E → Finset V)
    (h : NoOddCycle edge) :
    ∃ c : V → ZMod 2, ∀ e, ∑ v ∈ edge e, c v = 1 := by
  classical
  have hrel (f : E →₀ ZMod 2)
      (hf : (f.sum fun e a => a • row (edge e)) = 0) :
      (f.sum fun _ a => a * (1 : ZMod 2)) = 0 := by
    have hone (e : E) (he : e ∈ f.support) : f e = 1 :=
      two_ne_zero_eq_one _ (Finsupp.mem_support_iff.mp he)
    have hrow : ∑ e ∈ f.support, row (edge e) = 0 := by
      rw [Finsupp.sum] at hf
      calc
        ∑ e ∈ f.support, row (edge e) =
            ∑ e ∈ f.support, f e • row (edge e) := by
          apply sum_congr rfl
          intro e he
          rw [hone e he, one_smul]
        _ = 0 := hf
    have hinc (v : V) : Even (f.support.filter fun e => v ∈ edge e).card := by
      apply ZMod.natCast_eq_zero_iff_even.mp
      have hh := congrArg (fun z : V →₀ ZMod 2 => z v) hrow
      simpa only [Finsupp.finset_sum_apply, row_apply, Finset.sum_boole,
        Finsupp.zero_apply] using hh
    have hs := ZMod.natCast_eq_zero_iff_even.mpr (h f.support hinc)
    rw [Finsupp.sum]
    calc
      ∑ e ∈ f.support, f e * 1 = ∑ _ ∈ f.support, (1 : ZMod 2) := by
        apply sum_congr rfl
        intro e he
        rw [hone e he, one_mul]
      _ = 0 := by simpa using hs
  obtain ⟨l, hl⟩ := exists_functional_of_relations
    (fun e => row (edge e)) (fun _ => (1 : ZMod 2)) hrel
  refine ⟨fun v => l (Finsupp.single v 1), ?_⟩
  intro e
  simpa only [row, map_sum] using hl e

/-- The criterion is also necessary: it is an exact characterization of
odd-parity colorability, not of ordinary nonmonochromatic colorability. -/
theorem noOddCycle_of_odd_coloring {V E : Type*} (edge : E → Finset V)
    (c : V → ZMod 2) (hc : ∀ e, ∑ v ∈ edge e, c v = 1) :
    NoOddCycle edge := by
  classical
  intro s hs
  let l : (V →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    Finsupp.linearCombination (ZMod 2) c
  have hl (e : E) : l (row (edge e)) = 1 := by
    simpa [l, row, map_sum, Finsupp.linearCombination_apply,
      Finsupp.sum_single_index] using hc e
  have hz : ∑ e ∈ s, row (edge e) = 0 := by
    ext v
    simp only [Finsupp.finset_sum_apply, row_apply, Finset.sum_boole, Finsupp.zero_apply]
    exact ZMod.natCast_eq_zero_iff_even.mpr (hs v)
  have hh := congrArg l hz
  simp only [map_sum, hl, sum_const, nsmul_eq_mul, mul_one, map_zero] at hh
  exact ZMod.natCast_eq_zero_iff_even.mp hh

theorem noOddCycle_iff_odd_coloring {V E : Type*} (edge : E → Finset V) :
    NoOddCycle edge ↔ ∃ c : V → ZMod 2, ∀ e, ∑ v ∈ edge e, c v = 1 := by
  exact ⟨exists_odd_coloring edge,
    fun ⟨c, hc⟩ => noOddCycle_of_odd_coloring edge c hc⟩

/-- Unordered strict cubic collision hyperedges on a source. -/
def CubicEdges (S : Set ℕ) : Set (Finset ℕ) :=
  {e | ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
    0 < a ∧ a < b ∧ b < c ∧ c < d ∧ a^3+d^3=b^3+c^3 ∧ e={a,b,c,d}}

/-- An odd-parity coloring has cube-Sidon fibers. -/
theorem odd_coloring_good {S : Set ℕ} (c : ℕ → ZMod 2)
    (hc : ∀ e ∈ CubicEdges S, ∑ n ∈ e, c n = 1) :
    SummableSourceColoring.GoodColoringOn S c := by
  classical
  intro i
  apply (cubeSidon_iff_no_strict_positive _).mpr
  intro a ha b hb r hr d hd ha0 hab hbr hrd he
  have hae : a ≠ b := by omega
  have har : a ≠ r := by omega
  have had : a ≠ d := by omega
  have hbd : b ≠ d := by omega
  have hbr' : b ≠ r := by omega
  have hrd' : r ≠ d := by omega
  have hh := hc {a,b,r,d} ⟨a,ha.1,b,hb.1,r,hr.1,d,hd.1,
    ha0,hab,hbr,hrd,he,rfl⟩
  have hh' : i + (i + (i+i)) = 1 := by
    simpa [hae, har, had, hbr', hbd, hrd', ha.2, hb.2, hr.2, hd.2] using hh
  have hzero : i + (i + (i+i)) = 0 := by
    have hi : i+i=0 := by simpa [ZMod.neg_eq_self_mod_two] using neg_add_cancel i
    simp [hi]
  exact zero_ne_one (hzero.symm.trans hh')

/-- Conditional density reduction on a general source with prefix multipliers. -/
theorem noOddCycle_source_suffices {S : Set ℕ}
    (hM : SummableSourceColoring.PositivePrefixMultipliers S)
    (h : NoOddCycle (fun e : CubicEdges S => (e : Finset ℕ))) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a^3) '' A) := by
  classical
  obtain ⟨c,hc⟩ := exists_odd_coloring (fun e : CubicEdges S => (e : Finset ℕ)) h
  have hgood := odd_coloring_good c (fun e he => hc ⟨e,he⟩)
  let d : ℕ → Fin 2 := fun n => ⟨(c n).val, ZMod.val_lt (c n)⟩
  apply SummableSourceColoring.finite_source_coloring_suffices hM d
  intro i
  have hsub : {n | n ∈ S ∧ d n = i} ⊆
      {n | n ∈ S ∧ c n = (ZMod.finEquiv 2) i} := by
    intro n hn
    refine ⟨hn.1, ?_⟩
    have hv := congrArg Fin.val hn.2
    apply ZMod.val_injective 2
    simpa [d, ZMod.finEquiv] using hv
  have hi := Set.image_mono (f := fun n : ℕ => n^3) hsub
  intro a ha b hb r hr s hs
  exact hgood ((ZMod.finEquiv 2) i) a (hi ha) b (hi hb) r (hi hr) s (hi hs)

/-- The new global input that would suffice: a reciprocal-summable divisor
sieve, omitting 1, which removes every odd even-incidence cubic edge collection.
This theorem does not supply that sieve. -/
theorem summable_odd_cycle_cover_suffices {B : Set ℕ} (h1 : 1 ∉ B)
    (hB : Summable (fun n : ℕ => if n ∈ B then (1 : ℝ)/n else 0))
    (h : NoOddCycle
      (fun e : CubicEdges (divisorAvoider B) => (e : Finset ℕ))) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a^3) '' A) :=
  noOddCycle_source_suffices (SummableSourceColoring.summable_source_multipliers h1 hB) h

#print axioms exists_functional_of_relations
#print axioms noOddCycle_iff_odd_coloring
#print axioms summable_odd_cycle_cover_suffices

end Erdos1206.OddCycleColoring
