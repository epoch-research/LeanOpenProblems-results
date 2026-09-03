import Submission.LinearBlockThinning

/-!
Uniform arbitrary-edge-thinning bound for the quadratic cubic-recovery model.
This excludes a family of candidate constructions; it does not settle Erdős 714.
-/
noncomputable section
open Finset SimpleGraph Classical Module
set_option maxHeartbeats 3000000
namespace Erdos714QuadraticThinning
open Erdos714LinearBlocks
variable {F : Type*} [Field F] [Fintype F] [CharP F 3]
abbrev V := Fin 4 → F
abbrev U := Fin 3 → F
abbrev Allowed (Q : QuadraticForm F (V (F := F))) := {x : V (F := F) // Q x ≠ 0}

def rowLift (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) (x : Allowed Q) : U (F := F) × U (F := F) :=
  (![B x.val 0,B x.val 1,-(Q x.val)^2], ![B x.val 2,B x.val 3,-Q x.val*N x.val])

def columnLift (Q : QuadraticForm F (V (F := F))) (y : Allowed Q) :
    Module.Dual F (U (F := F)) × Module.Dual F (U (F := F)) :=
  (dotProductEquiv F (Fin 3) ![y.val 2,y.val 3,Q y.val],
    dotProductEquiv F (Fin 3) ![-y.val 0,-y.val 1,-(Q y.val)^2])

omit [Fintype F] [CharP F 3] in
lemma row_nonzero (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) (x : Allowed Q) : (rowLift Q N B x).1 ≠ 0 := by
  intro h
  have h₂ := congrFun h 2
  have hz : (Q x.val)^2 = 0 := by simpa [rowLift] using h₂
  exact pow_ne_zero 2 x.property hz

omit [Fintype F] [CharP F 3] in
lemma column_nonzero (Q : QuadraticForm F (V (F := F))) (y : Allowed Q) :
    (columnLift Q y).1 ≠ 0 := by
  intro h
  have h' : ![y.val 2,y.val 3,Q y.val] = (0 : U (F := F)) :=
    (dotProductEquiv F (Fin 3)).injective (by simpa [columnLift] using h)
  exact y.property (by simpa using congrFun h' 2)

omit [Fintype F] in
lemma row_ray_injective (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) : RayInjective (F := F) (rowLift Q N B) := by
  intro x y a h
  have hx : x.val = a • y.val := by
    apply B.injective
    rw [map_smul]
    ext i
    fin_cases i
    · simpa [rowLift] using congrArg (fun p : U (F := F) × U (F := F) => p.1 0) h
    · simpa [rowLift] using congrArg (fun p : U (F := F) × U (F := F) => p.1 1) h
    · simpa [rowLift] using congrArg (fun p : U (F := F) × U (F := F) => p.2 0) h
    · simpa [rowLift] using congrArg (fun p : U (F := F) × U (F := F) => p.2 1) h
  have hQ : Q x.val = a^2*Q y.val := by rw [hx, Q.map_smul]; simp [pow_two]
  have ha : a ≠ 0 := by intro ha; exact x.property (by simp [hQ, ha])
  have hs : (Q x.val)^2 = a*(Q y.val)^2 := by
    have hs := congrArg (fun p : U (F := F) × U (F := F) => p.1 2) h
    simpa [rowLift] using hs
  have ha4 : a^4 = a := by
    apply mul_right_cancel₀ (pow_ne_zero 2 y.property)
    rw [hQ] at hs
    linear_combination hs
  have ha3 : a^3 = 1 := by
    apply mul_left_cancel₀ ha
    calc
      a*a^3 = a^4 := by ring
      _ = a := ha4
      _ = a*1 := by ring
  have ha1 : a = 1 := frobenius_inj F 3 (by simpa only [frobenius_def, one_pow] using ha3)
  apply Subtype.ext
  simpa [ha1] using hx

omit [Fintype F] [CharP F 3] in
lemma column_ray_injective (Q : QuadraticForm F (V (F := F))) :
    RayInjective (F := F) (columnLift Q) := by
  intro x y a h
  have h₁ : ![x.val 2,x.val 3,Q x.val] = a • ![y.val 2,y.val 3,Q y.val] := by
    apply (dotProductEquiv F (Fin 3)).injective
    rw [map_smul]
    exact congrArg Prod.fst h
  have h₂ : ![-x.val 0,-x.val 1,-(Q x.val)^2] = a • ![-y.val 0,-y.val 1,-(Q y.val)^2] := by
    apply (dotProductEquiv F (Fin 3)).injective
    rw [map_smul]
    exact congrArg Prod.snd h
  have hx : x.val = a • y.val := by
    ext i
    fin_cases i
    · simpa using congrFun h₂ 0
    · simpa using congrFun h₂ 1
    · simpa using congrFun h₁ 0
    · simpa using congrFun h₁ 1
  have hQ : Q x.val = a^2*Q y.val := by rw [hx, Q.map_smul]; simp [pow_two]
  have ha : a ≠ 0 := by intro ha; exact x.property (by simp [hQ, ha])
  have hQ' : Q x.val = a*Q y.val := by simpa using congrFun h₁ 2
  have ha2 : a^2 = a := mul_right_cancel₀ y.property (hQ.symm.trans hQ')
  have ha1 : a = 1 := by
    apply mul_left_cancel₀ ha
    simpa [pow_two] using ha2
  apply Subtype.ext
  simpa [ha1] using hx

omit [Fintype F] [CharP F 3] in
lemma lift_compatibility (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) (x y : Allowed Q) :
    (columnLift Q y).1 (rowLift Q N B x).2 = (columnLift Q y).2 (rowLift Q N B x).1 ↔
      (B x.val) ⬝ᵥ y.val = (Q x.val)^2*(Q y.val)^2+Q x.val*N x.val*Q y.val := by
  simp only [rowLift, columnLift, dotProductEquiv_apply_apply, dotProduct, Fin.sum_univ_three,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  constructor <;> intro h <;> linear_combination h

def graph (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) : SimpleGraph (Allowed Q ⊕ Allowed Q) where
  Adj v w := match v,w with
    | .inl x,.inr y => (B x.val) ⬝ᵥ y.val = (Q x.val)^2*(Q y.val)^2+Q x.val*N x.val*Q y.val
    | .inr y,.inl x => (B x.val) ⬝ᵥ y.val = (Q x.val)^2*(Q y.val)^2+Q x.val*N x.val*Q y.val
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact not_false

/-- No square-sign or quartic-homogeneity assumption is needed for this obstruction. -/
theorem arbitrary_thinning (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) (H : SimpleGraph (Allowed Q ⊕ Allowed Q))
    (hH : H ≤ graph Q N B) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 456976*Fintype.card F^27 := by
  have hbi : H ≤ completeBipartiteGraph (Allowed Q) (Allowed Q) := by
    intro v w h
    have hh := hH h
    cases v <;> cases w <;> simp_all [graph]
  let E : Finset (Allowed Q × Allowed Q) :=
    univ.filter (fun p => H.Adj (.inl p.1) (.inr p.2))
  have he : E.card = H.edgeFinset.card := by
    rw [← Erdos714Unbalanced.incidence_neighborhoods H hbi, Erdos714Packing.incidence_edges]
    dsimp [E, Erdos714Unbalanced.neighborhoods]
    have hc := sum_boole (R := ℕ)
      (fun p : Allowed Q × Allowed Q => H.Adj (.inl p.1) (.inr p.2)) univ
    simp only [Nat.cast_id] at hc
    rw [← hc, Fintype.sum_prod_type]
    simp only [sum_boole, Nat.cast_id]
  have hfree : NoRectangle E := by
    intro f g hfg
    have hn := Erdos714Unbalanced.incidence_neighborhoods H hbi
    have hfree := (Erdos714Packing.free_iff_no_rectangle
      (Erdos714Unbalanced.neighborhoods H) (by decide : 0 < 4)).mp (by rwa [hn])
    apply hfree f g
    intro i j
    simpa only [E, Erdos714Unbalanced.neighborhoods, mem_filter, mem_univ, true_and] using hfg i j
  have hE : ∀ p ∈ E,
      (columnLift Q p.2).1 (rowLift Q N B p.1).2 =
        (columnLift Q p.2).2 (rowLift Q N B p.1).1 := by
    intro p hp
    apply (lift_compatibility Q N B _ _).mpr
    exact hH (mem_filter.mp hp).2
  have hn : Fintype.card (Allowed Q) ≤ Fintype.card F^4 := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_subtype_le (fun x : V (F := F) => Q x ≠ 0)
  rw [← he]
  exact chart_fourth_power (by simp [Module.finrank_fintype_fun_eq_card])
    (rowLift Q N B) (columnLift Q) (row_ray_injective Q N B) (column_ray_injective Q)
    (row_nonzero Q N B) (column_nonzero Q) E hfree hE hn hn

/-- The same asymmetric model with its pairing written as a bundled bilinear map. -/
def bilinearGraph (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (P : V (F := F) →ₗ[F] Module.Dual F (V (F := F))) :
    SimpleGraph (Allowed Q ⊕ Allowed Q) where
  Adj v w := match v,w with
    | .inl x,.inr y => P x.val y.val = (Q x.val)^2*(Q y.val)^2+Q x.val*N x.val*Q y.val
    | .inr y,.inl x => P x.val y.val = (Q x.val)^2*(Q y.val)^2+Q x.val*N x.val*Q y.val
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact not_false

/-- No appeal to a coordinate identification is left implicit in this corollary. -/
theorem bilinear_thinning (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (P : V (F := F) →ₗ[F] Module.Dual F (V (F := F))) (hP : Function.Bijective P)
    (H : SimpleGraph (Allowed Q ⊕ Allowed Q)) (hH : H ≤ bilinearGraph Q N P)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 456976*Fintype.card F^27 := by
  let B := (LinearEquiv.ofBijective P hP).trans (dotProductEquiv F (Fin 4)).symm
  have hpair (x y : V (F := F)) : B x ⬝ᵥ y = P x y := by
    have h := (dotProductEquiv F (Fin 4)).apply_symm_apply (P x)
    exact congrArg (fun f : Module.Dual F (V (F := F)) => f y) h
  apply arbitrary_thinning Q N B H _ hf
  intro v w hvw
  have h := hH hvw
  cases v <;> cases w
  all_goals first | exact h | simpa only [graph, bilinearGraph, hpair] using h

/-- In particular the critical q⁷ scale cannot persist along unbounded field orders. -/
theorem critical_size_bound (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) (H : SimpleGraph (Allowed Q ⊕ Allowed Q))
    (hH : H ≤ graph Q N B) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (K : ℕ) (hE : Fintype.card F^7 ≤ K*H.edgeFinset.card) : Fintype.card F ≤ 456976*K^4 := by
  have he := arbitrary_thinning Q N B H hH hf
  have h : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(456976*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hE 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(456976*Fintype.card F^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (by positivity)

#print axioms row_ray_injective
#print axioms column_ray_injective
#print axioms lift_compatibility
#print axioms arbitrary_thinning
#print axioms critical_size_bound
#print axioms bilinear_thinning
end Erdos714QuadraticThinning
