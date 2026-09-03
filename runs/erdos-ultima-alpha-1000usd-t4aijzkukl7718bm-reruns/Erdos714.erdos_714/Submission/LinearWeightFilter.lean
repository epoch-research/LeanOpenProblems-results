import Submission.CubicQuarticNine

/-!
A fixed finite configuration in a scalar-homogeneous graph can be moved into
an additive weight kernel when the scalar field exceeds the constraint count.
This excludes a repair of such hosts by bounded-codimension linear weight
filters; it is not a proof or disproof of Erdős 714.
-/
noncomputable section
open SimpleGraph Classical
set_option maxHeartbeats 2000000
namespace Erdos714LinearWeightFilter

section ScalarConstraints
variable {F B I : Type*} [Field F] [AddCommGroup B]
  [Fintype F] [Fintype B] [Fintype I]

/-- A nonzero scalar simultaneously puts a bounded list of weights in a kernel. -/
theorem exists_scalar (T : F →+ B) (a : I → F)
    (hcard : Fintype.card B^Fintype.card I < Fintype.card F) :
    ∃ s : F, s ≠ 0 ∧ ∀ i, T (s*a i) = 0 := by
  let f : F → I → B := fun s i => T (s*a i)
  have hn : ¬ Function.Injective f := by
    intro hi
    have h := Fintype.card_le_of_injective f hi
    rw [Fintype.card_fun] at h
    omega
  obtain ⟨x,y,hxy,hne⟩ := Function.not_injective_iff.mp hn
  refine ⟨x-y,sub_ne_zero.mpr hne,?_⟩
  intro i
  rw [sub_mul,map_sub]
  have h := congrFun hxy i
  change T (x*a i) = T (y*a i) at h
  rw [h,sub_self]
end ScalarConstraints

section Graphs
variable {F B I X : Type*} [Field F] [AddCommGroup B]
  [Fintype F] [Fintype B] [Fintype I]

/-- Exact finite-copy transfer; no transitivity or group action law is assumed. -/
theorem copy_into_kernel (G : SimpleGraph X) (weight : X → F) (T : F →+ B)
    (hscale : ∀ s : F, s ≠ 0 → ∃ e : G ≃g G, ∀ x, weight (e x) = s*weight x)
    (H : SimpleGraph I) (f : H.Copy G)
    (hcard : Fintype.card B^Fintype.card I < Fintype.card F) :
    Nonempty (H.Copy (G.induce {x | T (weight x) = 0})) := by
  obtain ⟨s,hs,ha⟩ := exists_scalar T (fun i => weight (f i)) hcard
  obtain ⟨e,he⟩ := hscale s hs
  refine ⟨⟨⟨fun i => ⟨e (f i),?_⟩,?_⟩,?_⟩⟩
  · change T (weight (e (f i))) = 0
    rw [he]
    exact ha i
  · intro i j hij
    change G.Adj (e (f i)) (e (f j))
    exact e.map_rel_iff.mpr (f.toHom.map_adj hij)
  · intro i j hij
    exact f.injective (e.injective (congrArg Subtype.val hij))

/-- At this field-size threshold, the kernel restriction has exactly the same
bounded forbidden subgraphs as its full scalar-homogeneous host. -/
theorem free_kernel_iff (G : SimpleGraph X) (weight : X → F) (T : F →+ B)
    (hscale : ∀ s : F, s ≠ 0 → ∃ e : G ≃g G, ∀ x, weight (e x) = s*weight x)
    (H : SimpleGraph I)
    (hcard : Fintype.card B^Fintype.card I < Fintype.card F) :
    H.Free (G.induce {x | T (weight x) = 0}) ↔ H.Free G := by
  constructor
  · intro hfree hf
    obtain ⟨f⟩ := hf
    exact hfree (copy_into_kernel G weight T hscale H f hcard)
  · intro hfree hf
    obtain ⟨f⟩ := hf
    exact hfree ⟨(Copy.induce G _).comp f⟩
end Graphs

section NormGraph
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

abbrev Vertex := (E × F) ⊕ (E × F)
def weight (x : Vertex (F := F) (E := E)) : F := Sum.elim Prod.snd Prod.snd x

def scalePair (l : E) (hl : l ≠ 0) (s : F) (hs : s ≠ 0) : E × F ≃ E × F where
  toFun p := (l*p.1,s*p.2)
  invFun p := (l⁻¹*p.1,s⁻¹*p.2)
  left_inv p := by ext <;> dsimp <;> field_simp
  right_inv p := by ext <;> dsimp <;> field_simp

/-- Norm surjectivity will supply l with N(l)=s^4. -/
lemma scale_relation (l : E) (hl : l ≠ 0) (s : F) (hs : s ≠ 0)
    (hN : Algebra.norm F l = s^4) (x y : E × F) :
    Erdos714CubicQuarticNine.relation (scalePair l hl s hs x) (scalePair l hl s hs y) ↔
      Erdos714CubicQuarticNine.relation x y := by
  change (s*x.2+s*y.2 ≠ 0 ∧
    Algebra.norm F (l*x.1+l*y.1) = (s*x.2+s*y.2)^4) ↔ _
  rw [← mul_add,← mul_add,map_mul,hN,mul_pow]
  have h4 : s^4 ≠ 0 := pow_ne_zero 4 hs
  simp only [ne_eq,mul_eq_zero,hs,false_or,mul_right_inj' h4]
  rfl

def scaleIso (l : E) (hl : l ≠ 0) (s : F) (hs : s ≠ 0)
    (hN : Algebra.norm F l = s^4) :
    Erdos714CubicQuarticNine.graph (F := F) (E := E) ≃g
      Erdos714CubicQuarticNine.graph (F := F) (E := E) where
  toEquiv := (scalePair l hl s hs).sumCongr (scalePair l hl s hs)
  map_rel_iff' := by
    intro x y
    cases x <;> cases y
    · rfl
    · exact scale_relation l hl s hs hN _ _
    · exact scale_relation l hl s hs hN _ _
    · rfl

lemma scaleIso_weight (l : E) (hl : l ≠ 0) (s : F) (hs : s ≠ 0)
    (hN : Algebra.norm F l = s^4) (x : Vertex (F := F) (E := E)) :
    weight (scaleIso l hl s hs hN x) = s*weight x := by
  cases x <;> rfl

variable [Fintype F] [Fintype E]

omit [Fintype F] in
/-- Scalar homogeneity holds in the ACTUAL field-norm graph. -/
theorem norm_scaling : ∀ s : F, s ≠ 0 →
    ∃ e : Erdos714CubicQuarticNine.graph (F := F) (E := E) ≃g
        Erdos714CubicQuarticNine.graph (F := F) (E := E),
      ∀ x, weight (e x) = s*weight x := by
  intro s hs
  obtain ⟨l,hl⟩ := FiniteField.norm_surjective F E (s^4)
  have hl0 : l ≠ 0 := by
    intro hz
    have hh : s^4 = 0 := by simpa [hz,Algebra.norm_zero] using hl.symm
    exact pow_ne_zero 4 hs hh
  exact ⟨scaleIso l hl0 s hs hl,scaleIso_weight l hl0 s hs hl⟩

/-- Any additive weight filter, not just an absolute trace, has this limitation. -/
theorem norm_filter_free_iff {B I : Type*} [AddCommGroup B] [Fintype B] [Fintype I]
    (T : F →+ B) (H : SimpleGraph I)
    (hcard : Fintype.card B^Fintype.card I < Fintype.card F) :
    H.Free ((Erdos714CubicQuarticNine.graph (F := F) (E := E)).induce
      {x | T (weight x) = 0}) ↔
      H.Free (Erdos714CubicQuarticNine.graph (F := F) (E := E)) :=
  free_kernel_iff _ weight T norm_scaling H hcard

/-- A bounded tuple of prime-field-linear weight equations is covered as well. -/
theorem ternary_filters_free_iff (r k : ℕ) (T : F →+ (Fin k → ZMod 3))
    (hcard : 3^(k*(2*r)) < Fintype.card F) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free
      ((Erdos714CubicQuarticNine.graph (F := F) (E := E)).induce
        {x | T (weight x) = 0}) ↔
    (completeBipartiteGraph (Fin r) (Fin r)).Free
      (Erdos714CubicQuarticNine.graph (F := F) (E := E)) := by
  apply norm_filter_free_iff
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_sum,ZMod.card,
    ← pow_mul,← two_mul] using hcard

variable [CharP F 3]

/-- Absolute trace with its canonical prime-field algebra structure. -/
def traceHom : F →+ ZMod 3 := by
  letI := ZMod.algebra F 3
  exact (Algebra.trace (ZMod 3) F).toAddMonoidHom

/-- In particular the proposed absolute-trace-zero restriction does not repair
Krr-freeness once the absolute field degree exceeds 2r. -/
theorem trace_filter_free_iff (r : ℕ) (hcard : 3^(2*r) < Fintype.card F) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free
      ((Erdos714CubicQuarticNine.graph (F := F) (E := E)).induce
        {x | traceHom (weight x) = 0}) ↔
    (completeBipartiteGraph (Fin r) (Fin r)).Free
      (Erdos714CubicQuarticNine.graph (F := F) (E := E)) := by
  apply norm_filter_free_iff
  simpa only [Fintype.card_fin,Fintype.card_sum,ZMod.card,← two_mul] using hcard

end NormGraph

#print axioms exists_scalar
#print axioms copy_into_kernel
#print axioms free_kernel_iff
#print axioms norm_scaling
#print axioms norm_filter_free_iff
#print axioms ternary_filters_free_iff
#print axioms trace_filter_free_iff

end Erdos714LinearWeightFilter
