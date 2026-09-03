import Submission.WittNormCircle

/-!
The Witt-circle obstruction with actual quadratic finite-field norms.
All finite-field parameters are supplied uniformly, not by certificates.
This is a construction obstruction, not a disproof of Erdős714.
-/
noncomputable section
open Classical SimpleGraph Finset
open scoped CharTwo
set_option maxHeartbeats 3000000
namespace Erdos714WittNormCircle
open Erdos714BinaryInverseTrace
variable {F E : Type*} [Field F] [Field E] [CharP F 2] [CharP E 2]
  [Fintype F] [Fintype E] [Algebra F E]

def fieldGraph : SimpleGraph ((E × E) ⊕ (E × E)) :=
  Erdos714Tensor.incidence fun p q =>
    (wittAdd p q).1 ≠ 0 ∧ Algebra.norm F (wittAdd p q).2 =
      (Algebra.norm F (wittAdd p q).1)^2

def conjugation (k : ℕ) : E →+* E := (frobenius E 2)^k

omit [Fintype E] in
lemma conjugation_apply (k : ℕ) (x : E) : conjugation k x=x^(2^k) := by
  rw [conjugation,RingHom.coe_pow,iterate_frobenius]

omit [CharP F 2] [Fintype E] in
lemma conjugation_coefficient (k : ℕ) (hcard : Fintype.card F=2^k) (x : F) :
    conjugation k (algebraMap F E x)=algebraMap F E x := by
  rw [conjugation_apply,←map_pow,←hcard,FiniteField.pow_card]

omit [CharP F 2] [CharP E 2] [Fintype F] [Fintype E] in
lemma map_traceSum (k : ℕ) (x : F) :
    traceSum k (algebraMap F E x)=algebraMap F E (traceSum k x) := by
  simp [traceSum,map_sum,map_pow]

omit [CharP F 2] [Fintype E] in
lemma traceSum_double_coefficient (k : ℕ) (hcard : Fintype.card F=2^k) (x : F) :
    traceSum (k+k) (algebraMap F E x)=0 := by
  have hp : (algebraMap F E x)^(2^k)=algebraMap F E x := by
    rw [←map_pow,←hcard,FiniteField.pow_card]
  simp only [traceSum,sum_range_add,pow_add,pow_mul,hp,CharTwo.add_self_eq_zero]

omit [CharP F 2] in
lemma extension_root (k : ℕ) (hcard : Fintype.card F=2^k)
    (hE : Fintype.card E=Fintype.card F^2) (c : F) (hc : traceSum k c=1) :
    ∃ y : E, y^2+y=algebraMap F E c ∧ conjugation k y=y+1 := by
  have hecard : Fintype.card E=2^(k+k) := by rw [hE,hcard,pow_two,pow_add]
  obtain ⟨y,hy⟩ := (trace_zero_iff_artinSchreier (k+k) hecard (algebraMap F E c)).mp
    (traceSum_double_coefficient k hcard c)
  refine ⟨y,hy,?_⟩
  rw [conjugation_apply,root_frobenius_iteration y _ hy]
  change y+traceSum k (algebraMap F E c)=y+1
  rw [map_traceSum,hc,map_one]

omit [CharP F 2] in
/-- Equality with the graph defined by the actual relative field norm. -/
lemma fieldGraph_eq (k : ℕ) (hcard : Fintype.card F=2^k)
    (hE : Fintype.card E=Fintype.card F^2) :
    fieldGraph (F := F) (E := E)=graph (conjugation k) := by
  have hN (x : E) : algebraMap F E (Algebra.norm F x)=conjugateNorm (conjugation k) x := by
    rw [Erdos714TranslatedNorm.quadratic_norm_power hE,hcard,conjugateNorm,conjugation_apply,pow_succ]
    exact mul_comm _ _
  ext p q
  cases p with
  | inl p =>
    cases q with
    | inl q => rfl
    | inr q =>
      change (_ ∧ _) ↔ (_ ∧ _)
      rw [←hN,←hN,←map_pow (algebraMap F E),(algebraMap F E).injective.eq_iff]
  | inr p =>
    cases q with
    | inr q => rfl
    | inl q =>
      change (_ ∧ _) ↔ (_ ∧ _)
      rw [←hN,←hN,←map_pow (algebraMap F E),(algebraMap F E).injective.eq_iff]

omit [Fintype F] in
private lemma fourth_AS (a u : F) (hu : u^2+u=a) : (u^4)^2+u^4=a^4 := by
  calc
    _ = (u^2+u)^4 := by rw [show (u^2+u)^4=(u^2)^4+u^4 from add_pow_char_pow (u^2) u 2 2]; ring
    _ = _ := by rw [hu]

/-- Uniform parameters give an actual injective complete bipartite copy. -/
def finiteCopy (k : ℕ) (hk : 4 ≤ k) (hcard : Fintype.card F=2^k)
    (hE : Fintype.card E=Fintype.card F^2) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (fieldGraph (F := F) (E := E)) := by
  apply Classical.choice
  obtain ⟨a,ha,hat,hait⟩ := exists_trace_zero_inverse k hk hcard
  obtain ⟨u,hu⟩ := (trace_zero_iff_artinSchreier k hcard a).mp hat
  obtain ⟨v,hv⟩ := (trace_zero_iff_artinSchreier k hcard a⁻¹).mp hait
  obtain ⟨x,hx⟩ := exists_traceSum_one k hcard
  have hx4 : traceSum k (x^4)=1 := by
    rw [show x^4=(x^2)^2 by ring,traceSum_square k hcard,traceSum_square k hcard,hx]
  obtain ⟨y,hy,hyf⟩ := extension_root (E := E) k hcard hE (x^4) hx4
  let X₀ (i : Bool) : F := if i then x+a⁻¹ else x
  let X (i : Bool) : E := algebraMap F E (X₀ i)
  let Y (i : Bool) : E := if i then y+algebraMap F E (v^4) else y
  let b : F := u^4+a*x
  have hXtrace (i : Bool) : traceSum k (X₀ i)=1 := by
    cases i <;> simp [X₀,traceSum_add,hx,hait]
  have hX0 (i : Bool) : X₀ i ≠ 0 := by
    intro hz
    have hh := hXtrace i
    simp [hz,traceSum] at hh
  have hXa (i : Bool) : a+X₀ i ≠ 0 := by
    intro hz
    have hh : traceSum k (a+X₀ i)=1 := by rw [traceSum_add,hat,hXtrace,zero_add]
    simp [hz,traceSum] at hh
  have hXinj : Function.Injective X := by
    intro i j hij
    have he : X₀ i=X₀ j := (algebraMap F E).injective hij
    have hainv : a⁻¹ ≠ 0 := inv_ne_zero ha
    cases i <;> cases j <;> simp_all [X₀]
  have hYf (i : Bool) : conjugation k (Y i)=Y i+1 := by
    cases i
    · exact hyf
    · simp only [Y,↓reduceIte,map_add,hyf,conjugation_coefficient k hcard]
      ring
  have hYroot (i : Bool) : (Y i)^2+Y i=(X i)^4 := by
    cases i
    · simpa [X,X₀,Y,map_pow] using hy
    · change (y+algebraMap F E (v^4))^2+(y+algebraMap F E (v^4)) = (algebraMap F E (x+a⁻¹))^4
      rw [add_pow_char,show y^2+(algebraMap F E (v^4))^2+(y+algebraMap F E (v^4)) =
        (y^2+y)+((algebraMap F E (v^4))^2+algebraMap F E (v^4)) by ring]
      rw [hy,←map_pow,←map_add,fourth_AS _ _ hv,←map_add,←map_pow]
      congr 1
      exact (add_pow_char_pow x a⁻¹ 2 2).symm
  have hd₀ (i : Bool) : (b+a*X₀ i)^2+(b+a*X₀ i)=a^4 := by
    have h2 : (2:F)=0 := CharP.cast_eq_zero F 2
    cases i
    · have he : b+a*X₀ false=u^4 := by
        dsimp [b,X₀]
        ring_nf
        simp only [h2,mul_zero,add_zero]
      rw [he]
      exact fourth_AS _ _ hu
    · have he : b+a*X₀ true=u^4+1 := by
        dsimp [b,X₀]
        rw [mul_add,mul_inv_cancel₀ ha]
        ring_nf
        simp only [h2,mul_zero,add_zero]
      rw [he,add_pow_char]
      simpa [add_assoc,add_left_comm,add_comm] using fourth_AS _ _ hu
  rw [fieldGraph_eq k hcard hE]
  refine ⟨templateCopy (conjugation k) (algebraMap F E a) (algebraMap F E b) X Y
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simpa only [map_zero] using (algebraMap F E).injective.ne ha
  · exact hXinj
  · exact conjugation_coefficient k hcard a
  · exact conjugation_coefficient k hcard b
  · intro i
    exact conjugation_coefficient k hcard (X₀ i)
  · exact hYf
  · exact hYroot
  · intro i
    simpa only [X,map_zero] using (algebraMap F E).injective.ne (hX0 i)
  · intro i
    rw [show algebraMap F E a+X i=algebraMap F E (a+X₀ i) by simp [X]]
    simpa only [map_zero] using (algebraMap F E).injective.ne (hXa i)
  · intro i
    simpa [X,map_add,map_mul,map_pow] using congrArg (algebraMap F E) (hd₀ i)

/-- Every full binary Witt norm-circle graph at q>=16 contains K44. -/
theorem fieldGraph_not_free (k : ℕ) (hk : 4 ≤ k) (hcard : Fintype.card F=2^k)
    (hE : Fintype.card E=Fintype.card F^2) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (fieldGraph (F := F) (E := E)) := by
  intro h
  exact h ⟨finiteCopy k hk hcard hE⟩

#print axioms extension_root
#print axioms fieldGraph_eq
#print axioms finiteCopy
#print axioms fieldGraph_not_free
end Erdos714WittNormCircle
