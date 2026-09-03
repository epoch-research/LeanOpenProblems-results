import Submission.ProfileThinning

/-!
An additive translation kernel depending on its transverse coordinates through
one scalar profile cannot retain the fourth-case critical density. The outer
functions need not be polynomial. This is not an extremal-conjecture disproof.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714ScalarProfile
variable {F V : Type*} [Field F] [AddCommGroup V] [Fintype F] [Fintype V]
abbrev Vertex := (V × F) × F

def kernel (P : F → F → F) (Q R : V → F) (z : V × F) : F :=
  P z.2 (Q z.1)+R z.1

def code (P : F → F → F) (Q R : V → F)
    (c : Vertex (F := F) (V := V)) (i : V × F) : F :=
  kernel P Q R (i+c.1)-c.2

def graph (P : F → F → F) (Q R : V → F) := Erdos714Coding.graph (code P Q R)

lemma cross_adj (P : F → F → F) (Q R : V → F)
    (c d : Vertex (F := F) (V := V)) :
    (graph P Q R).Adj (.inl c) (.inr d) ↔ kernel P Q R (c.1+d.1)=c.2+d.2 := by
  change (d.1,d.2) ∈ Erdos714Coding.symbols (code P Q R) c ↔ _
  rw [Erdos714Coding.mem_symbols]
  change kernel P Q R (d.1+c.1)-c.2=d.2 ↔ _
  rw [sub_eq_iff_eq_add,add_comm d.1 c.1,add_comm d.2 c.2]

/-- The complete profile is the scalar shift, transverse value, and offset. -/
def profile (Q R : V → F) (x : V) (c : Vertex (F := F) (V := V)) : F × F × F :=
  (c.1.2,Q (x+c.1.1),R (x+c.1.1)-c.2)

def eval (P : F → F → F) (_x : V) (p : F × F × F) (t : F) : F :=
  P (t+p.1) p.2.1+p.2.2

omit [Fintype F] [Fintype V] in
lemma code_eq (P : F → F → F) (Q R : V → F) :
    code P Q R = Erdos714ProfileThinning.code (profile Q R) (eval P) := by
  funext c i
  simp only [code,kernel,Erdos714ProfileThinning.code,profile,eval,Prod.fst_add,Prod.snd_add]
  ring

/-- This includes arbitrary edge restrictions, not just whole profile selection. -/
theorem fourth_power (P : F → F → F) (Q R : V → F)
    (H : SimpleGraph (Vertex (F := F) (V := V) ⊕ Vertex (F := F) (V := V)))
    (hH : H ≤ graph P Q R) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hV : Fintype.card V ≤ Fintype.card F^2) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  have hc : Fintype.card (Vertex (F := F) (V := V)) ≤ Fintype.card F^4 := by
    simp only [Vertex,Fintype.card_prod]
    calc
      _ ≤ (Fintype.card F^2*Fintype.card F)*Fintype.card F := by gcongr
      _ = _ := by ring
  have hp : Fintype.card (F × F × F) ≤ Fintype.card F^3 := by
    simp only [Fintype.card_prod]; nlinarith
  rw [graph,code_eq] at hH
  exact Erdos714ProfileThinning.critical_scale_bound (profile Q R) (eval P) H hH hf
    (Fintype.card F) Fintype.card_pos le_rfl hV hc hp

/-- Every point-pair fixes exactly one opposite weight. -/
theorem edge_count (P : F → F → F) (Q R : V → F) :
    (graph P Q R).edgeFinset.card = Fintype.card V^2*Fintype.card F^3 := by
  rw [graph,Erdos714Coding.edge_count]
  simp only [Vertex,Fintype.card_prod]
  ring

theorem size_budget (P : F → F → F) (Q R : V → F)
    (H : SimpleGraph (Vertex (F := F) (V := V) ⊕ Vertex (F := F) (V := V)))
    (hH : H ≤ graph P Q R) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hV : Fintype.card V ≤ Fintype.card F^2)
    (K : ℕ) (he : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 165888*K^4 := by
  have hb := fourth_power P Q R H hH hf hV
  have h : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(165888*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(165888*Fintype.card F^27) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos Fintype.card_pos 27)

#print axioms cross_adj
#print axioms code_eq
#print axioms fourth_power
#print axioms edge_count
#print axioms size_budget
end Erdos714ScalarProfile
