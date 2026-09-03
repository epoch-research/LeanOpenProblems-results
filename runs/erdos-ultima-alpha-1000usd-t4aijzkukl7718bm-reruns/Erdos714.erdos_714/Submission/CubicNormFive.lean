import Submission.CubicNormSpheres
import Submission.WeightedPowerSymmetry

/-!
The ordinary cubic norm graph is K55-free. This provides a genuine
construction bound, but its exponent7/4 is still below the fifth-case
Erdős714 target9/5, and it does not resolve the fourth case.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714CubicSegre
variable {E : Type*} [Field E]

/-- The norm of a sum is the pairing of complementary Segre coordinates. -/
lemma complement_pairing (σ : E →+* E) (x y : E) :
    ∑ i : Fin 8, point σ x i*point σ y i.rev = norm σ (x+y) := by
  simp [Fin.sum_univ_succ,point,segre,norm,map_add]
  ring

/-- Independent rows on both sides cannot be orthogonal in dimension nine. -/
theorem independent_no_rectangle (σ : E →+* E)
    (x y a b : Fin 5 → E)
    (hx : LinearIndependent E (fun i => point σ (x i)))
    (hy : LinearIndependent E (fun j => point σ (y j)))
    (h : ∀ i j, norm σ (x i+y j) = a i*b j) : False := by
  let A : Matrix (Fin 5) (Fin 9) E := fun i => Fin.snoc (point σ (x i)) (a i)
  let B : Matrix (Fin 9) (Fin 5) E := fun k j =>
    (Fin.snoc (fun l : Fin 8 => point σ (y j) l.rev) (-b j) : Fin 9 → E) k
  have hA : LinearIndependent E A.row := by
    apply LinearIndependent.of_comp (LinearMap.funLeft E E (fun i : Fin 8 => i.castSucc))
    simpa [A,Function.comp_def,Matrix.row,LinearMap.funLeft] using hx
  have hB : LinearIndependent E B.transpose.row := by
    apply LinearIndependent.of_comp
      (LinearMap.funLeft E E (fun i : Fin 8 => i.rev.castSucc))
    simpa [B,Function.comp_def,Matrix.row,Matrix.transpose_apply,LinearMap.funLeft] using hy
  have hAB : A*B = 0 := by
    ext i j
    change ∑ k : Fin 9, A i k*B k j = 0
    rw [Fin.sum_univ_castSucc]
    simp only [A,B,Fin.snoc_castSucc,Fin.snoc_last]
    rw [complement_pairing,h i j]
    ring
  have hr := Matrix.rank_add_rank_le_card_of_mul_eq_zero hAB
  rw [hA.rank_matrix,← Matrix.rank_transpose B,hB.rank_matrix] at hr
  norm_num at hr

/-- All row configurations, including the linearly dependent ones, are handled. -/
theorem no_five_rectangle (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (x y : Fin 5 → E) (hx : Function.Injective x) (hy : Function.Injective y)
    (a b : Fin 5 → E) (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (h : ∀ i j, norm σ (x i+y j) = a i*b j) : False := by
  by_cases hi : LinearIndependent E (fun i => point σ (x i))
  · by_cases hj : LinearIndependent E (fun j => point σ (y j))
    · exact independent_no_rectangle σ x y a b hi hj h
    · exact dependent_no_rectangle σ hσ y x hy hx b a (hb 0) ha
        (fun j i => by simpa [add_comm,mul_comm] using h i j) hj
  · exact dependent_no_rectangle σ hσ x y hx hy a b (ha 0) hb h hi

section FieldNorm
variable {F : Type*} [Field F] [Algebra F E] [Fintype F] [Fintype E]

/-- The ordinary weighted field-norm host. -/
def normGraph : SimpleGraph ((E × Fˣ) ⊕ (E × Fˣ)) :=
  Erdos714WeightedPower.graph (Units.map (Algebra.norm F (S := E)))

/-- Transfer from the conjugate formula to the actual field-norm graph. -/
theorem graph_free_of_norm_formula (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (hN : ∀ z, algebraMap F E (Algebra.norm F z) = norm σ z) :
    (completeBipartiteGraph (Fin 5) (Fin 5)).Free (normGraph (F := F) (E := E)) := by
  let S (p : E × Fˣ) := univ.filter (fun q =>
    Erdos714WeightedPower.relation (Units.map (Algebra.norm F (S := E))) p q)
  have hg : normGraph (F := F) (E := E) = Erdos714Packing.incidence S := by
    ext p q
    cases p <;> cases q <;>
      simp [normGraph,Erdos714WeightedPower.graph,Erdos714Tensor.incidence,
        Erdos714Packing.incidence,S]
  rw [hg]
  apply (Erdos714Packing.free_iff_no_rectangle S (by decide : 0 < 5)).mpr
  intro L R hrect
  have he (i j : Fin 5) : Algebra.norm F ((L i).1+(R j).1) =
      ((L i).2 : F)*((R j).2 : F) := by
    obtain ⟨z,hz,hn⟩ := (mem_filter.mp (hrect i j)).2
    have hh := congrArg (fun u : Fˣ => (u : F)) hn
    change Algebra.norm F (z : E) = ((L i).2 : F)*((R j).2 : F) at hh
    rwa [hz] at hh
  have hx : Function.Injective (fun i => (L i).1) := by
    intro i j hij
    dsimp only at hij
    have hw : ((L i).2 : F) = ((L j).2 : F) := by
      apply mul_right_cancel₀ (R 0).2.ne_zero
      rw [← he i 0,← he j 0,hij]
    exact L.injective (Prod.ext hij (Units.ext hw))
  have hy : Function.Injective (fun j => (R j).1) := by
    intro i j hij
    dsimp only at hij
    have hw : ((R i).2 : F) = ((R j).2 : F) := by
      apply mul_left_cancel₀ (L 0).2.ne_zero
      rw [← he 0 i,← he 0 j,hij]
    exact R.injective (Prod.ext hij (Units.ext hw))
  apply no_five_rectangle σ hσ (fun i => (L i).1) (fun j => (R j).1) hx hy
    (fun i => algebraMap F E ((L i).2 : F)) (fun j => algebraMap F E ((R j).2 : F))
    (fun i => (map_ne_zero _).mpr (L i).2.ne_zero)
    (fun j => (map_ne_zero _).mpr (R j).2.ne_zero)
  intro i j
  rw [← hN,he,map_mul]

/-- In every finite cubic extension, the actual cubic norm graph is K55-free.
The proof is uniform in the characteristic. -/
theorem normGraph_free (hdim : Module.finrank F E = 3) :
    (completeBipartiteGraph (Fin 5) (Fin 5)).Free (normGraph (F := F) (E := E)) := by
  let σ : E →+* E := (FiniteField.frobeniusAlgHom F E).toRingHom
  have hcard : Fintype.card E = Fintype.card F^3 := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E),hdim]
  have hσ : ∀ z, σ (σ (σ z)) = z := by
    intro z
    change ((z^Fintype.card F)^Fintype.card F)^Fintype.card F = z
    rw [← pow_mul,← pow_mul,show Fintype.card F*(Fintype.card F*Fintype.card F) =
      Fintype.card F^3 by ring,← hcard]
    exact FiniteField.pow_card z
  apply graph_free_of_norm_formula σ hσ
  intro z
  change algebraMap F E (Algebra.norm F z) =
    z*(z^Fintype.card F)*((z^Fintype.card F)^Fintype.card F)
  rw [FiniteField.algebraMap_norm_eq_prod_pow F E z,hdim]
  simp only [Finset.prod_range_succ,Finset.prod_range_zero,pow_zero,pow_one,one_mul,
    Nat.card_eq_fintype_card,← pow_mul,pow_two]

/-- Exact edge count, reusing the norm-independent symmetry/counting API. -/
theorem normGraph_edges (hdim : Module.finrank F E = 3) :
    (normGraph (F := F) (E := E)).edgeFinset.card =
      Fintype.card F^3*(Fintype.card F-1)*(Fintype.card F^3-1) := by
  rw [normGraph,Erdos714WeightedPower.edge_count,Fintype.card_units,
    Module.card_eq_pow_finrank (K := F) (V := E),hdim]

end FieldNorm
#print axioms independent_no_rectangle
#print axioms no_five_rectangle
#print axioms graph_free_of_norm_formula
#print axioms normGraph_free
#print axioms normGraph_edges
end Erdos714CubicSegre
