import Submission.NormTraceCharThree
import Submission.ProfileThinning

/-!
Uniform arbitrary-edge-thinning obstruction for cubic norm times an arbitrary
linear functional in characteristics two and three. Not a disproof of Erdős 714.
-/
noncomputable section
open Polynomial Module Finset SimpleGraph Classical
open Erdos714NormTraceLine Erdos714NormTraceCharThree
set_option maxHeartbeats 2000000
namespace Erdos714NormTraceThinning
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [Fintype F] [Fintype E]

/-- Additive lift without deleting any edges. -/
def liftGraph (f : E → F) : SimpleGraph ((E × F) ⊕ (E × F)) where
  Adj u v := match u,v with
    | .inl a, .inr b => a.2+b.2 = f (a.1+b.1)
    | .inr b, .inl a => a.2+b.2 = f (a.1+b.1)
    | _,_ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

omit [Algebra F E] [FiniteDimensional F E] in
/-- Every input point gives exactly one output weight at every row. -/
lemma liftGraph_edges (f : E → F) :
    (liftGraph f).edgeFinset.card = Fintype.card E^2*Fintype.card F := by
  have he : liftGraph f = Erdos714Coding.graph
      (fun (r : E × F) (x : E) => f (r.1+x)-r.2) := by
    ext z w
    rcases z with ⟨a,c⟩ | ⟨a,c⟩ <;> rcases w with ⟨b,d⟩ | ⟨b,d⟩ <;>
      simp [liftGraph, Erdos714Coding.graph, Erdos714Packing.incidence,
        eq_sub_iff_add_eq, eq_comm, add_comm]
  rw [he, Erdos714Coding.edge_count, Fintype.card_prod]
  ring

omit [FiniteDimensional F E] in
/-- The full host genuinely has the critical number of edges. -/
lemma critical_host_edges (hdim : finrank F E = 3) (f : E → F) :
    (liftGraph f).edgeFinset.card = Fintype.card F^7 := by
  rw [liftGraph_edges, Module.card_eq_pow_finrank (K := F), hdim]
  ring

omit [FiniteDimensional F E] in
/-- The full host has the intended fourth-case vertex scale. -/
lemma critical_host_vertices (hdim : finrank F E = 3) :
    Fintype.card ((E × F) ⊕ (E × F)) = 2*Fintype.card F^4 := by
  have hc : Fintype.card E = Fintype.card F^3 := by
    rw [Module.card_eq_pow_finrank (K := F), hdim]
  simp only [Fintype.card_sum, Fintype.card_prod, hc]
  ring

omit [Fintype F] [Fintype E] in
/-- Split the vector space into parallel scalar lines in a prescribed direction. -/
def lineChart (u : E) (ℓ : E →ₗ[F] F) (hℓ : ℓ u = 1) : ℓ.ker × F ≃ E where
  toFun p := p.1.val + p.2 • u
  invFun z := (⟨z-ℓ z • u, by simp [LinearMap.mem_ker, hℓ]⟩, ℓ z)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      have hzero : ℓ p.1.val = 0 := p.1.property
      simp [hzero, hℓ]
    · have hzero : ℓ p.1.val = 0 := p.1.property
      simp [hzero, hℓ]
  right_inv z := by simp

/-- Three-parameter line profiles cannot retain the fourth-case density.
The first parameter may specify an arbitrary one-variable function. -/
theorem three_parameter_thinning (hdim : finrank F E = 3)
    (f : E → F) (u : E) (hu : u ≠ 0) (A B C : E → F) (D : F → F → F)
    (hprofile : ∀ z t, f (z+t • u) = D (A z) t+B z*t+C z)
    (H : SimpleGraph ((E × F) ⊕ (E × F))) (hH : H ≤ liftGraph f)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_eq_one F hu
  have hℓ0 : ℓ ≠ 0 := by intro h; simp [h] at hℓ
  have hℓsurj : Function.Surjective ℓ := LinearMap.surjective_iff_ne_zero.mpr hℓ0
  have hkdim : finrank F ℓ.ker = 2 := by
    have h := ℓ.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hℓsurj, finrank_top, Module.finrank_self, hdim] at h
    omega
  have hkcard : Fintype.card ℓ.ker = Fintype.card F^2 := by
    rw [Module.card_eq_pow_finrank (K := F), hkdim]
  have hEcard : Fintype.card E = Fintype.card F^3 := by
    rw [Module.card_eq_pow_finrank (K := F), hdim]
  let e : ((E × F) ⊕ ((ℓ.ker × F) × F)) ≃ ((E × F) ⊕ (E × F)) :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (lineChart u ℓ hℓ) (Equiv.refl F))
  let J := H.comap e.toEmbedding
  let g (v : ℓ.ker) (r : E × F) : F × F × F :=
    (A (r.1+v.val), B (r.1+v.val), C (r.1+v.val)-r.2)
  let ev (v : ℓ.ker) (p : F × F × F) (t : F) :=
    D p.1 t+p.2.1*t+p.2.2
  have hforward (r : E × F) (p : (ℓ.ker × F) × F)
      (h : H.Adj (e (.inl r)) (e (.inr p))) :
      Erdos714ProfileThinning.code g ev r p.1 = p.2 := by
    have hh := hH h
    change r.2+p.2 = f (r.1+(p.1.1.val+p.1.2 • u)) at hh
    rw [← add_assoc, hprofile] at hh
    change D (A (r.1+p.1.1.val)) p.1.2+
      B (r.1+p.1.1.val)*p.1.2+(C (r.1+p.1.1.val)-r.2) = p.2
    linear_combination -hh
  have hJ : J ≤ Erdos714Coding.graph (Erdos714ProfileThinning.code g ev) := by
    intro z w h
    cases z with
    | inl r =>
      cases w with
      | inl s => exact False.elim (hH h)
      | inr p =>
        rcases p with ⟨i,a⟩
        simpa only [Erdos714Coding.graph, Erdos714Packing.incidence,
          Erdos714Coding.mem_symbols] using hforward r (i,a) h
    | inr p =>
      cases w with
      | inr z => exact False.elim (hH h)
      | inl r =>
        rcases p with ⟨i,a⟩
        simpa only [Erdos714Coding.graph, Erdos714Packing.incidence,
          Erdos714Coding.mem_symbols] using hforward r (i,a) h.symm
  have hJfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free J :=
    Erdos714GraphAveraging.free_comap _ H e.toEmbedding hfree
  have hb := Erdos714ProfileThinning.critical_scale_bound g ev J hJ hJfree
    (Fintype.card F) Fintype.card_pos le_rfl hkcard.le
    (show Fintype.card (E × F) ≤ Fintype.card F^4 by
      simp only [Fintype.card_prod, hEcard]; nlinarith [pow_succ (Fintype.card F) 3])
    (show Fintype.card (F × F × F) ≤ Fintype.card F^3 by
      simp only [Fintype.card_prod]; nlinarith [pow_succ (Fintype.card F) 2])
  have he : J.edgeFinset.card = H.edgeFinset.card := (SimpleGraph.Iso.comap e H).card_edgeFinset_eq
  rwa [he] at hb

section CharThree
variable [CharP F 3]

omit [Fintype F] [Fintype E] in
lemma cubic_profile (hdim : finrank F E = 3) (z : E) (t : F) :
    value (F := F) (z+algebraMap F E t) =
      Algebra.trace F E z*t^3+(Algebra.trace F E z)^2*t^2+
      (Algebra.trace F E z*(shiftPoly (F := F) z).coeff 1)*t+
      Algebra.norm F z*Algebra.trace F E z := by
  have ht : Algebra.trace F E (z+algebraMap F E t) = Algebra.trace F E z := by
    rw [(Algebra.trace F E).map_add, Algebra.trace_algebraMap, hdim, nsmul_eq_mul]
    simp only [CharP.cast_eq_zero F 3, zero_mul, add_zero]
  rw [value, ht, cubic_norm_shift hdim]
  ring

/-- All edge thinnings of the full norm-times-trace host lose a power of q. -/
theorem trace_arbitrary_thinning (hdim : finrank F E = 3)
    (H : SimpleGraph ((E × F) ⊕ (E × F)))
    (hH : H ≤ liftGraph (value (F := F)))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  apply three_parameter_thinning hdim (value (F := F)) 1 one_ne_zero
    (Algebra.trace F E)
    (fun z => Algebra.trace F E z*(shiftPoly (F := F) z).coeff 1)
    (fun z => Algebra.norm F z*Algebra.trace F E z) (fun a t => a*t^3+a^2*t^2) ?_ H hH hfree
  intro z t
  simpa only [Algebra.smul_def, mul_one] using cubic_profile hdim z t

/-- The arbitrary linear functional is represented by the nondegenerate trace
pairing, and its inverse coefficient specifies the correct line direction. -/
theorem functional_arbitrary_thinning (hdim : finrank F E = 3)
    (L : E →ₗ[F] F) (hL : L ≠ 0)
    (H : SimpleGraph ((E × F) ⊕ (E × F)))
    (hH : H ≤ liftGraph (fun z => Algebra.norm F z*L z))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  let e := (Algebra.traceForm F E).toDual (traceForm_nondegenerate F E)
  obtain ⟨δ,hδ⟩ := e.surjective L
  have hrep (z : E) : L z = Algebra.trace F E (δ*z) :=
    (congrArg (fun f : E →ₗ[F] F => f z) hδ).symm
  have hδ0 : δ ≠ 0 := by
    intro hz
    apply hL
    ext z
    simp [hrep, hz]
  let u := δ⁻¹
  let k := Algebra.norm F u
  have hk : k ≠ 0 := Algebra.norm_ne_zero_iff.mpr (inv_ne_zero hδ0)
  have hscale (z : E) : Algebra.norm F (u*z)*L (u*z) = k*value (F := F) z := by
    rw [hrep]
    have hz : δ*(u*z) = z := by dsimp only [u]; rw [← mul_assoc, mul_inv_cancel₀ hδ0, one_mul]
    rw [hz, map_mul, value]
    ring
  apply three_parameter_thinning hdim (fun z => Algebra.norm F z*L z) u (inv_ne_zero hδ0)
    (fun z => k*Algebra.trace F E (δ*z))
    (fun z => k*Algebra.trace F E (δ*z)*(shiftPoly (F := F) (δ*z)).coeff 1)
    (fun z => k*Algebra.norm F (δ*z)*Algebra.trace F E (δ*z))
    (fun a t => a*t^3+(a^2/k)*t^2) ?_ H hH hfree
  intro z t
  have he : z+t • u = u*(δ*z+algebraMap F E t) := by
    dsimp only [u]
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hδ0, one_mul, Algebra.smul_def]
    ring
  dsimp only
  rw [he, hscale, cubic_profile hdim]
  field_simp

/-- This includes the previously investigated deletion of all zero-functional
edges, as well as any further vertex or edge deletions. -/
theorem restricted_arbitrary_thinning (hdim : finrank F E = 3)
    (L : E →ₗ[F] F) (hL : L ≠ 0)
    (H : SimpleGraph ((E × F) ⊕ (E × F)))
    (hH : H ≤ functionalGraph L)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  apply functional_arbitrary_thinning hdim L hL H (le_trans hH ?_) hfree
  intro z w h
  cases z <;> cases w
  · exact h
  · exact h.2
  · exact h.2
  · exact h

/-- A fixed critical-edge constant can occur only at bounded field order. -/
theorem critical_size_bound (hdim : finrank F E = 3)
    (L : E →ₗ[F] F) (hL : L ≠ 0)
    (H : SimpleGraph ((E × F) ⊕ (E × F)))
    (hH : H ≤ liftGraph (fun z => Algebra.norm F z*L z))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (K : ℕ) (hdense : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 165888*K^4 := by
  have he := functional_arbitrary_thinning hdim L hL H hH hfree
  let q := Fintype.card F
  have hh : q^27*q ≤ q^27*(165888*K^4) := by
    calc
      q^27*q = (q^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(165888*q^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos Fintype.card_pos 27)

end CharThree

section CharTwo
variable [CharP F 2]

omit [Fintype F] [Fintype E] in
/-- In characteristic two the cubic coefficient cancels, leaving three profiles. -/
lemma cubic_profile_binary (hdim : finrank F E = 3) (z : E) (t : F) :
    value (F := F) (z+algebraMap F E t) =
      t^4+((Algebra.trace F E z)^2+(shiftPoly (F := F) z).coeff 1)*t^2+
      (Algebra.trace F E z*(shiftPoly (F := F) z).coeff 1+Algebra.norm F z)*t+
      Algebra.norm F z*Algebra.trace F E z := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h3 : (3 : F) = 1 := by linear_combination h2
  have ht : Algebra.trace F E (z+algebraMap F E t) = Algebra.trace F E z+t := by
    rw [(Algebra.trace F E).map_add, Algebra.trace_algebraMap, hdim, nsmul_eq_mul, Nat.cast_ofNat, h3, one_mul]
  rw [value, ht, cubic_norm_shift hdim]
  linear_combination Algebra.trace F E z*t^3*h2

/-- Uniform arbitrary-edge-thinning obstruction in characteristic two, with
an arbitrary nonzero linear functional, including both even and odd base degrees. -/
theorem functional_binary_thinning (hdim : finrank F E = 3)
    (L : E →ₗ[F] F) (hL : L ≠ 0)
    (H : SimpleGraph ((E × F) ⊕ (E × F)))
    (hH : H ≤ liftGraph (fun z => Algebra.norm F z*L z))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  let e := (Algebra.traceForm F E).toDual (traceForm_nondegenerate F E)
  obtain ⟨δ,hδ⟩ := e.surjective L
  have hrep (z : E) : L z = Algebra.trace F E (δ*z) :=
    (congrArg (fun f : E →ₗ[F] F => f z) hδ).symm
  have hδ0 : δ ≠ 0 := by
    intro hz
    apply hL
    ext z
    simp [hrep, hz]
  let u := δ⁻¹
  let k := Algebra.norm F u
  have hscale (z : E) : Algebra.norm F (u*z)*L (u*z) = k*value (F := F) z := by
    rw [hrep]
    have hz : δ*(u*z) = z := by dsimp only [u]; rw [← mul_assoc, mul_inv_cancel₀ hδ0, one_mul]
    rw [hz, map_mul, value]
    ring
  apply three_parameter_thinning hdim (fun z => Algebra.norm F z*L z) u (inv_ne_zero hδ0)
    (fun z => k*((Algebra.trace F E (δ*z))^2+(shiftPoly (F := F) (δ*z)).coeff 1))
    (fun z => k*(Algebra.trace F E (δ*z)*(shiftPoly (F := F) (δ*z)).coeff 1+Algebra.norm F (δ*z)))
    (fun z => k*Algebra.norm F (δ*z)*Algebra.trace F E (δ*z))
    (fun a t => k*t^4+a*t^2) ?_ H hH hfree
  intro z t
  have he : z+t • u = u*(δ*z+algebraMap F E t) := by
    dsimp only [u]
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hδ0, one_mul, Algebra.smul_def]
    ring
  dsimp only
  rw [he, hscale, cubic_profile_binary hdim]
  ring

/-- The same bound applies after deleting all zero-functional edges and then
retaining arbitrary further edges. -/
theorem restricted_binary_thinning (hdim : finrank F E = 3)
    (L : E →ₗ[F] F) (hL : L ≠ 0)
    (H : SimpleGraph ((E × F) ⊕ (E × F)))
    (hH : H ≤ functionalGraph L)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  apply functional_binary_thinning hdim L hL H (le_trans hH ?_) hfree
  intro z w h
  cases z <;> cases w
  · exact h
  · exact h.2
  · exact h.2
  · exact h

/-- A fixed critical-edge constant can occur only at bounded field order. -/
theorem binary_critical_size_bound (hdim : finrank F E = 3)
    (L : E →ₗ[F] F) (hL : L ≠ 0)
    (H : SimpleGraph ((E × F) ⊕ (E × F)))
    (hH : H ≤ liftGraph (fun z => Algebra.norm F z*L z))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (K : ℕ) (hdense : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 165888*K^4 := by
  have he := functional_binary_thinning hdim L hL H hH hfree
  let q := Fintype.card F
  have hh : q^27*q ≤ q^27*(165888*K^4) := by
    calc
      q^27*q = (q^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(165888*q^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos Fintype.card_pos 27)

end CharTwo

#print axioms critical_host_edges
#print axioms critical_host_vertices
#print axioms lineChart
#print axioms three_parameter_thinning
#print axioms trace_arbitrary_thinning
#print axioms functional_arbitrary_thinning
#print axioms restricted_arbitrary_thinning
#print axioms critical_size_bound
#print axioms cubic_profile_binary
#print axioms functional_binary_thinning
#print axioms restricted_binary_thinning
#print axioms binary_critical_size_bound
end Erdos714NormTraceThinning
