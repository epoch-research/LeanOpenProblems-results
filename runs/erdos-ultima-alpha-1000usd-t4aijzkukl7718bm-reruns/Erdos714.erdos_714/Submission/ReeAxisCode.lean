import Submission.ReeAxisFourRoots
import Submission.CoordinateCircuits

/-!
A four-root relation gives a coordinate circuit in any code using that
four-function profile on a single full field line. For the Ree twist this
rules out the full critical-size chart, even with arbitrary nonlinear
coefficient maps in the message and the other two coordinates.
This is an obstruction to a particular construction, not to Erdős 714.
-/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714ReeAxisCode

variable {F C I : Type*} [Field F] [Fintype F] [Fintype C] [Fintype I]

/-- No assumptions are made on the code away from the displayed line.
A nonzero quadratic coefficient in the root relation allows elimination
of one of the four profile coefficients. -/
theorem profile_bound (τ : F → F) (a b c d : F) (hc : c ≠ 0)
    (t : Fin 4 ↪ F) (ht : ∀ j, c*(t j)^2+d*τ (t j)+a*t j+b=0)
    (f : C → I → F) (line : F ↪ I) (P₀ P₁ P₂ P₃ : C → F)
    (hline : ∀ m x, f m (line x)=P₀ m+P₁ m*x+P₂ m*x^2+P₃ m*τ x)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Coding.graph f)) :
    Fintype.card C ≤ 3*Fintype.card F^3 := by
  let obs (m : C) : F × F × F :=
    (c*P₀ m-b*P₂ m, c*P₁ m-a*P₂ m, c*P₃ m-d*P₂ m)
  have heval (m : C) (j : Fin 4) :
      c*f m (line (t j))=(obs m).1+(obs m).2.1*t j+(obs m).2.2*τ (t j) := by
    rw [hline]
    dsimp [obs]
    linear_combination P₂ m * ht j
  have hobs : ∀ m n, obs m=obs n → ∀ j,
      f m ((t.trans line) j)=f n ((t.trans line) j) := by
    intro m n h j
    apply mul_left_cancel₀ hc
    change c*f m (line (t j))=c*f n (line (t j))
    rw [heval,heval,h]
  have hb := Erdos714CoordinateCircuits.bound_of_observation f
    (by decide : 0<4) (t.trans line) obs hobs hfree
  simpa only [Nat.reduceSub,Fintype.card_prod,pow_succ,pow_zero,one_mul,mul_assoc] using hb

variable [CharP F 3]

/-- The checked four-root theorem turns into an actual code-size obstruction. -/
theorem ree_line_bound (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hq : 3<Fintype.card F) (f : C → I → F) (line : F ↪ I)
    (P₀ P₁ P₂ P₃ : C → F)
    (hline : ∀ m x, f m (line x)=P₀ m+P₁ m*x+P₂ m*x^2+P₃ m*σ x)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Coding.graph f)) :
    Fintype.card C ≤ 3*Fintype.card F^3 := by
  obtain ⟨a,b,c,d,hc,t,ht⟩ := Erdos714ReeAxis.exists_four_roots σ hσ hq
  exact profile_bound σ a b c d hc t ht f line P₀ P₁ P₂ P₃ hline hfree

theorem ree_line_not_free (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hq : 3<Fintype.card F) (f : C → I → F) (line : F ↪ I)
    (P₀ P₁ P₂ P₃ : C → F)
    (hline : ∀ m x, f m (line x)=P₀ m+P₁ m*x+P₂ m*x^2+P₃ m*σ x)
    (hC : 3*Fintype.card F^3<Fintype.card C) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Coding.graph f) := by
  intro hf
  exact (not_le_of_gt hC) (ree_line_bound σ hσ hq f line P₀ P₁ P₂ P₃ hline hf)

/-- Three coordinate variables; the coefficient functions can be arbitrary. -/
def chart (σ : F →+* F) (P : Fin 4 → C → F → F → F) : C → (Fin 3 → F) → F :=
  fun m x => P 0 m (x 1) (x 2)+P 1 m (x 1) (x 2)*x 0+
    P 2 m (x 1) (x 2)*(x 0)^2+P 3 m (x 1) (x 2)*σ (x 0)

def axis : F ↪ (Fin 3 → F) where
  toFun t := ![t,0,0]
  inj' := by intro t u h; exact congrFun h 0

omit [Fintype F] [Fintype C] [CharP F 3] in
lemma axis_profile (σ : F →+* F) (P : Fin 4 → C → F → F → F) (m : C) (x : F) :
    chart σ P m (axis x)=P 0 m 0 0+P 1 m 0 0*x+P 2 m 0 0*x^2+P 3 m 0 0*σ x := by
  simp [chart,axis]

/-- At exactly the proposed q^4 message scale, this chart cannot be free. -/
theorem chart_not_free (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hq : 3<Fintype.card F) (P : Fin 4 → C → F → F → F)
    (hC : Fintype.card C=Fintype.card F^4) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (chart σ P)) := by
  apply ree_line_not_free σ hσ hq (chart σ P) axis
    (fun m => P 0 m 0 0) (fun m => P 1 m 0 0)
    (fun m => P 2 m 0 0) (fun m => P 3 m 0 0) (axis_profile σ P)
  rw [hC,show Fintype.card F^4=Fintype.card F*Fintype.card F^3 by ring]
  exact Nat.mul_lt_mul_of_pos_right hq (pow_pos (show 0 < Fintype.card F from by omega) 3)

omit [CharP F 3] in
/-- The unthinned chart does have the intended edge count, independently of
its coefficients. That count alone does not establish freeness. -/
theorem chart_edges (σ : F →+* F) (P : Fin 4 → C → F → F → F)
    (hC : Fintype.card C=Fintype.card F^4) :
    (Erdos714Coding.graph (chart σ P)).edgeFinset.card=Fintype.card F^7 := by
  rw [Erdos714Coding.edge_count,hC,Fintype.card_fun,Fintype.card_fin,← pow_add]

omit [Field F] [CharP F 3] in
theorem chart_vertices (hC : Fintype.card C=Fintype.card F^4) :
    Fintype.card (C ⊕ ((Fin 3 → F) × F))=2*Fintype.card F^4 := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,hC]
  ring

/-- Specialization to every actual Ree field of order at least 27. -/
theorem finite_chart_not_free (m : ℕ) (hm : 0 < m)
    (hF : Fintype.card F=3^(2*m+1)) (P : Fin 4 → C → F → F → F)
    (hC : Fintype.card C=Fintype.card F^4) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (chart (Erdos714ReeAxis.reeTwist m) P)) := by
  apply chart_not_free _ (Erdos714ReeAxis.reeTwist_square m hF) _ P hC
  rw [hF]
  exact (show 3^1=3 by norm_num) ▸
    Nat.pow_lt_pow_right (by decide : 1<3) (by omega : 1<2*m+1)

end Erdos714ReeAxisCode

#print axioms Erdos714ReeAxisCode.profile_bound
#print axioms Erdos714ReeAxisCode.ree_line_bound
#print axioms Erdos714ReeAxisCode.chart_not_free
#print axioms Erdos714ReeAxisCode.chart_edges
#print axioms Erdos714ReeAxisCode.chart_vertices
#print axioms Erdos714ReeAxisCode.finite_chart_not_free
