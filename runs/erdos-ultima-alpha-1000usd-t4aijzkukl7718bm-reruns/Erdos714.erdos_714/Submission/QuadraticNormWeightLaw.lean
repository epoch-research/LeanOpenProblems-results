import Submission.QuadraticProfileThinning

/-!
Arbitrary nonlinear weight-label laws cannot repair a quadratic norm graph
with an independent affine coordinate and an independent output weight.
The bound permits arbitrary edge deletions. This is not a solution of Erdős 714.
-/

noncomputable section
open Classical SimpleGraph Finset

namespace Erdos714QuadraticNormWeightLaw

variable {F U V : Type*} [Field F]

abbrev LeftVertex (F U : Type*) := (F × U) × F
abbrev RightVertex (F V : Type*) [Field F] := (F × V) × Fˣ

/-- `k` may be completely arbitrary, nonlinear and nonseparable. Row weights
include zero; deleting them or restricting their characters gives a subgraph. -/
def graph (δ : F) (k : U → V → F) :
    SimpleGraph (LeftVertex F U ⊕ RightVertex F V) where
  Adj p q := match p,q with
    | .inl x,.inr y => (x.1.1+y.1.1)^2-δ*(k x.1.2 y.1.2)^2 = x.2*(y.2 : F)
    | .inr y,.inl x => (x.1.1+y.1.1)^2-δ*(k x.1.2 y.1.2)^2 = x.2*(y.2 : F)
    | _,_ => False
  symm := by intro p q; cases p <;> cases q <;> simp
  loopless := by intro p; cases p <;> simp

/-- Solving for the independent row weight exposes a quadratic code profile. -/
def code (δ : F) (k : U → V → F) (c : RightVertex F V) (i : U × F) : F :=
  ((i.2+c.1.1)^2-δ*(k i.1 c.1.2)^2)/(c.2 : F)

lemma code_quadratic (δ : F) (k : U → V → F) (c : RightVertex F V) (u : U) (a : F) :
    code δ k c (u,a) =
      (c.1.1^2-δ*(k u c.1.2)^2)/(c.2 : F) +
      (2*c.1.1/(c.2 : F))*a + (1/(c.2 : F))*a^2 := by
  dsimp [code]
  ring

variable [Fintype F] [Fintype U]

/-- The profile representation is an isomorphism of the actual graphs,
including both endpoint types and the nonzero column weight. -/
def codeIso (δ : F) (k : U → V → F) :
    graph δ k ≃g Erdos714Coding.graph (code δ k) where
  toEquiv := (Equiv.sumComm _ _).trans
    ((Equiv.refl _).sumCongr (Equiv.prodCongr (Equiv.prodComm F U) (Equiv.refl F)))
  map_rel_iff' := by
    have he (x : LeftVertex F U) (y : RightVertex F V) :
        code δ k y (x.1.2,x.1.1) = x.2 ↔
        (x.1.1+y.1.1)^2-δ*(k x.1.2 y.1.2)^2 = x.2*(y.2 : F) := by
      exact div_eq_iff (Units.ne_zero y.2)
    intro p q
    cases p with
    | inl x =>
      cases q with
      | inl x' => simp [graph, Erdos714Coding.graph, Erdos714Packing.incidence]
      | inr y =>
        simpa [graph, Erdos714Coding.graph, Erdos714Packing.incidence, Prod.map] using he x y
    | inr y =>
      cases q with
      | inr y' => simp [graph, Erdos714Coding.graph, Erdos714Packing.incidence]
      | inl x =>
        simpa [graph, Erdos714Coding.graph, Erdos714Packing.incidence, Prod.map] using he x y

variable [Fintype V]

/-- Uniform obstruction at the intended fourth-case scale, in every
characteristic and for every label law `k`. No nonsquare hypotheses are needed. -/
theorem fourth_power_bound (δ : F) (k : U → V → F)
    (H : SimpleGraph (LeftVertex F U ⊕ RightVertex F V))
    (hHG : H ≤ graph δ k)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hU : Fintype.card U ≤ Fintype.card F ^ 2)
    (hV : Fintype.card V ≤ Fintype.card F ^ 2) :
    H.edgeFinset.card ^ 4 ≤ 165888 * Fintype.card F ^ 27 := by
  let e := codeIso δ k
  let K := H.comap e.symm
  have hK : K ≤ Erdos714Coding.graph (code δ k) := by
    intro p q hpq
    have he := e.toHom.map_adj (hHG hpq)
    change (Erdos714Coding.graph (code δ k)).Adj
      (e.toEquiv (e.toEquiv.symm p)) (e.toEquiv (e.toEquiv.symm q)) at he
    simpa only [Equiv.apply_symm_apply] using he
  have hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free K :=
    Erdos714GraphAveraging.free_comap _ H e.symm.toEquiv.toEmbedding hfree
  have hC : Fintype.card (RightVertex F V) ≤ Fintype.card F ^ 4 := by
    simp only [RightVertex, Fintype.card_prod, Fintype.card_units]
    calc
      Fintype.card F * Fintype.card V * (Fintype.card F-1) ≤
          Fintype.card F * (Fintype.card F ^ 2) * Fintype.card F := by gcongr; omega
      _ = _ := by ring
  have hb := Erdos714QuadraticProfileThinning.fourth_power_bound (code δ k)
    (fun u c => (c.1.1^2-δ*(k u c.1.2)^2)/(c.2 : F))
    (fun _ c => 2*c.1.1/(c.2 : F))
    (fun _ c => 1/(c.2 : F)) (code_quadratic δ k) K hK hf hU hC
  let iso : K ≃g H := ⟨e.symm.toEquiv,Iff.rfl⟩
  rw [iso.card_edgeFinset_eq] at hb
  exact hb

/-- A fixed integer lower-bound constant forces the field size to remain bounded. -/
theorem critical_scale_budget (δ : F) (k : U → V → F)
    (H : SimpleGraph (LeftVertex F U ⊕ RightVertex F V))
    (hHG : H ≤ graph δ k)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hU : Fintype.card U ≤ Fintype.card F ^ 2)
    (hV : Fintype.card V ≤ Fintype.card F ^ 2)
    (K : ℕ) (he : Fintype.card F ^ 7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 165888*K^4 := by
  have hb := fourth_power_bound δ k H hHG hfree hU hV
  have hp := Nat.pow_le_pow_left he 4
  rw [mul_pow] at hp
  have hh := hp.trans (Nat.mul_le_mul_left (K^4) hb)
  apply Nat.le_of_mul_le_mul_right (c := Fintype.card F ^ 27) ?_ (pow_pos Fintype.card_pos 27)
  convert hh using 1 <;> ring

#print axioms code_quadratic
#print axioms codeIso
#print axioms fourth_power_bound
#print axioms critical_scale_budget

end Erdos714QuadraticNormWeightLaw
