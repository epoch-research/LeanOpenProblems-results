import Submission.WeightedPowerKernel

/-! Power-graph weight quotients with a subfield in their kernel cannot be
repaired by retaining a fixed edge fraction. The degree-six quotient is an
application, not a proof or disproof of Erdős714. -/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000

namespace Erdos714WeightedPower
variable (E : Type*) [Field E]
abbrev Weight (d : ℕ) := (powMonoidHom d : Eˣ →* Eˣ).range

def powerMap (d : ℕ) : Eˣ →* Weight E d := (powMonoidHom d : Eˣ →* Eˣ).rangeRestrict


/-- The unit-valued definition is the usual power incidence, with its open
condition stated explicitly (also correct when d=0). -/
lemma power_relation_iff (d : ℕ) (p q : E × Weight E d) :
    relation (powerMap E d) p q ↔ p.1+q.1 ≠ 0 ∧
      (p.1+q.1)^d=((p.2 : Eˣ) : E)*((q.2 : Eˣ) : E) := by
  constructor
  · rintro ⟨z,hz,hν⟩
    refine ⟨hz ▸ Units.ne_zero z,?_⟩
    have he := congrArg (fun w : Weight E d => ((w : Eˣ) : E)) hν
    change ((z^d : Eˣ) : E)=((p.2 : Eˣ) : E)*((q.2 : Eˣ) : E) at he
    simpa only [Units.val_pow_eq_pow_val,hz] using he
  · rintro ⟨hz,he⟩
    refine ⟨Units.mk0 (p.1+q.1) hz,rfl,?_⟩
    apply Subtype.ext
    apply Units.ext
    change (((Units.mk0 (p.1+q.1) hz)^d : Eˣ) : E)=((p.2 : Eˣ) : E)*((q.2 : Eˣ) : E)
    simpa only [Units.val_pow_eq_pow_val,Units.val_mk0] using he

variable {E} {K : Type*} [Field K] [Fintype K]

lemma power_kernel (d : ℕ) (ι : K →+* E) (hd : Fintype.card K-1 ∣ d) (u : Kˣ) :
    powerMap E d (Units.map ι.toMonoidHom u)=1 := by
  apply Subtype.ext
  change (Units.map ι.toMonoidHom u)^d=1
  obtain ⟨m,rfl⟩ := hd
  have hu : u^(Fintype.card K-1)=1 := by
    simpa only [Fintype.card_units] using (pow_card_eq_one (x := u))
  rw [pow_mul,←map_pow,hu,map_one,one_pow]

variable [Fintype E]
instance (d : ℕ) : Fintype (Weight E d) := Fintype.ofFinite _

lemma weight_card (d : ℕ) :
    Fintype.card (Weight E d)=(Fintype.card E-1)/(Fintype.card E-1).gcd d := by
  simpa only [Weight,Nat.card_eq_fintype_card,Fintype.card_units] using
    IsCyclic.card_powMonoidHom_range Eˣ d

/-- This applies to every power map satisfying the stated divisibility, not
just to one cyclotomic factorization. -/
theorem power_kernel_thinning (d : ℕ) (ι : K →+* E) (hd : Fintype.card K-1 ∣ d)
    (t : ℕ) (ht : 0<t) (hcard : 2*t ≤ Fintype.card K)
    (H : SimpleGraph ((E × Weight E d) ⊕ (E × Weight E d)))
    (hH : H ≤ graph (powerMap E d))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    t*H.edgeFinset.card^4 ≤ 10368*(graph (powerMap E d)).edgeFinset.card^4 :=
  kernel_thinning (powerMap E d) ι (power_kernel d ι hd) t ht hcard H hH hfree

def quotientExponent (q : ℕ) : ℕ := (q^3+1)*(q-1)

lemma exponent_factorization (q : ℕ) (hq : 1 ≤ q) :
    q^6-1=quotientExponent q*(q^2+q+1) := by
  have he : q^6=quotientExponent q*(q^2+q+1)+1 := by
    cases q with
    | zero => omega
    | succ n => simp only [quotientExponent,Nat.add_sub_cancel]; ring
  omega

lemma quadratic_kernel_divides (q : ℕ) (hq : 1 ≤ q) : q^2-1 ∣ quotientExponent q := by
  have hsq : q ≤ q^2 := by nlinarith
  have hsub : q^2-q+q=q^2 := Nat.sub_add_cancel hsq
  have hfac : (q+1)*(q^2-q+1)=q^3+1 := by
    nlinarith [congrArg (fun x : ℕ => (q+1)*x) hsub]
  have hsqfac : q^2-1=(q+1)*(q-1) := by
    have he : q^2=(q+1)*(q-1)+1 := by
      cases q with
      | zero => omega
      | succ n => simp only [Nat.add_sub_cancel]; ring
    omega
  refine ⟨q^2-q+1,?_⟩
  rw [quotientExponent,hsqfac,←hfac]
  ring

lemma quotient_weight_card (q : ℕ) (hq : 2 ≤ q) (hE : Fintype.card E=q^6) :
    Fintype.card (Weight E (quotientExponent q))=q^2+q+1 := by
  have hd : 0<quotientExponent q := mul_pos (by positivity) (Nat.sub_pos_of_lt (by omega))
  rw [weight_card,hE,exponent_factorization q (by omega),Nat.gcd_mul_right_left]
  exact Nat.mul_div_cancel_left _ hd

/-- The quotient preserves the proposed critical size before freeness is imposed. -/
lemma quotient_edges (q : ℕ) (hq : 2 ≤ q) (hE : Fintype.card E=q^6) :
    (graph (powerMap E (quotientExponent q))).edgeFinset.card=q^6*(q^2+q+1)*(q^6-1) := by
  rw [edge_count,quotient_weight_card q hq hE,hE]

/-- At this scale the quadratic subfield supplies bicliques of order floor(q^2/2). -/
theorem quotient_thinning (q : ℕ) (hq : 2 ≤ q) (ι : K →+* E)
    (hK : Fintype.card K=q^2)
    (H : SimpleGraph ((E × Weight E (quotientExponent q)) ⊕ (E × Weight E (quotientExponent q))))
    (hH : H ≤ graph (powerMap E (quotientExponent q)))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    (q^2/2)*H.edgeFinset.card^4 ≤ 10368*(graph (powerMap E (quotientExponent q))).edgeFinset.card^4 := by
  apply power_kernel_thinning (quotientExponent q) ι
  · rw [hK]
    exact quadratic_kernel_divides q (by omega)
  · exact Nat.div_pos (by nlinarith) (by decide)
  · rw [hK,mul_comm]
    exact Nat.div_mul_le_self _ _
  · exact hH
  · exact hfree


lemma quotient_vertex_count (q : ℕ) (hq : 2 ≤ q) (hE : Fintype.card E=q^6) :
    Fintype.card ((E × Weight E (quotientExponent q)) ⊕ (E × Weight E (quotientExponent q)))=
      2*q^6*(q^2+q+1) := by
  simp only [Fintype.card_sum,Fintype.card_prod,quotient_weight_card q hq hE,hE]
  ring

/-- Even the absolute critical edge budget bounds q, independently of any
separately assumed retained-fraction estimate. -/
theorem quotient_budget (q C : ℕ) (hq : 2 ≤ q) (hE : Fintype.card E=q^6) (ι : K →+* E)
    (hK : Fintype.card K=q^2)
    (H : SimpleGraph ((E × Weight E (quotientExponent q)) ⊕ (E × Weight E (quotientExponent q))))
    (hH : H ≤ graph (powerMap E (quotientExponent q)))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hdense : q^14 ≤ C*H.edgeFinset.card) : q^2 ≤ 663552*C^4 := by
  have hpos : 0<H.edgeFinset.card := by
    have hp : 0<q^14 := pow_pos (by omega) _
    by_contra h
    have he : H.edgeFinset.card=0 := by omega
    rw [he,mul_zero] at hdense
    omega
  have hupper : (graph (powerMap E (quotientExponent q))).edgeFinset.card ≤ 2*q^14 := by
    rw [quotient_edges q hq hE]
    calc
      q^6*(q^2+q+1)*(q^6-1) ≤ q^6*(2*q^2)*q^6 := by
        gcongr
        · nlinarith
        · exact Nat.sub_le _ _
      _ = _ := by ring
  have hker : ∀ u : Kˣ, powerMap E (quotientExponent q) (Units.map ι.toMonoidHom u)=1 := by
    apply power_kernel
    rw [hK]
    exact quadratic_kernel_divides q (by omega)
  have hrel : (graph (powerMap E (quotientExponent q))).edgeFinset.card ≤ (2*C)*H.edgeFinset.card := by
    calc
      _ ≤ 2*q^14 := hupper
      _ ≤ 2*(C*H.edgeFinset.card) := Nat.mul_le_mul_left _ hdense
      _ = _ := by ring
  have ht : 0<q^2/2 := Nat.div_pos (by nlinarith) (by decide)
  have hc : 2*(q^2/2) ≤ Fintype.card K := by
    rw [hK,mul_comm]
    exact Nat.div_mul_le_self _ _
  have hb := kernel_budget (powerMap E (quotientExponent q)) ι hker (q^2/2) (2*C)
    ht hc H hH hfree hpos hrel
  have hq2 : 4 ≤ q^2 := by nlinarith
  calc
    q^2 ≤ 4*(q^2/2) := by omega
    _ ≤ 4*(10368*(2*C)^4) := Nat.mul_le_mul_left _ hb
    _ = _ := by ring

end Erdos714WeightedPower
#print axioms Erdos714WeightedPower.power_kernel
#print axioms Erdos714WeightedPower.power_kernel_thinning
#print axioms Erdos714WeightedPower.quotient_weight_card
#print axioms Erdos714WeightedPower.quotient_edges
#print axioms Erdos714WeightedPower.quotient_thinning

#print axioms Erdos714WeightedPower.quotient_vertex_count
#print axioms Erdos714WeightedPower.quotient_budget

#print axioms Erdos714WeightedPower.power_relation_iff
