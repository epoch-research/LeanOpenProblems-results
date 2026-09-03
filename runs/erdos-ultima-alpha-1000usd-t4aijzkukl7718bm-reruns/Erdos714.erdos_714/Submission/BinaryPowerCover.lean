import Submission.CyclotomicSubfield
import Submission.BinaryLift

/-! Binary fixed-order norm covers have large constant-weight kernels.
This is an obstruction to this construction, not a solution of Erdős714. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000

namespace Erdos714WeightedPower
variable {E W : Type*} [Field E] [CharP E 2] [CommGroup W]

/-- The kernel Cayley graph uses only the weight 1, so its copy lies in the
actual weight group, not in a larger full-weight host. -/
def binaryKernelCopy (ν : Eˣ →* W) :
    Copy (Erdos714BinaryLift.cayley {x : E | ∃ u : Eˣ, (u : E)=x ∧ ν u=1})
      (graph ν) where
  toHom := {
    toFun := fun x => if x.1 then Sum.inr (x.2,1) else Sum.inl (x.2,1)
    map_rel' := by
      rintro ⟨a,x⟩ ⟨b,y⟩ ⟨hab,u,hu,hν⟩
      cases a <;> cases b
      · exact (hab rfl).elim
      · exact ⟨u,hu,by simpa using hν⟩
      · exact ⟨u,by simpa only [add_comm] using hu,by simpa using hν⟩
      · exact (hab rfl).elim }
  injective' := by
    rintro ⟨a,x⟩ ⟨b,y⟩ h
    cases a <;> cases b <;> simp_all

variable [Fintype E]

omit [CharP E 2] in
lemma binary_kernel_card (ν : Eˣ →* W) :
    (univ.filter (fun x : E => ∃ u : Eˣ, (u : E)=x ∧ ν u=1)).card =
      Fintype.card ν.ker := by
  let f : ν.ker ≃ {x : E // ∃ u : Eˣ, (u : E)=x ∧ ν u=1} := {
    toFun := fun u => ⟨u.1,u.1,rfl,u.2⟩
    invFun := fun x => ⟨x.2.choose,x.2.choose_spec.2⟩
    left_inv := by
      intro u
      apply Subtype.ext
      apply Units.ext
      exact (show ∃ v : Eˣ, (v : E)=((u.1 : Eˣ) : E) ∧ ν v=1 from
        ⟨u.1,rfl,u.2⟩).choose_spec.1
    right_inv := by
      intro x
      apply Subtype.ext
      exact x.2.choose_spec.1 }
  simpa only [Fintype.card_subtype] using (Fintype.card_congr f).symm

/-- A free binary weighted host has a Sidon-sized multiplicative kernel. -/
theorem binary_kernel_bound (ν : Eˣ →* W)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph ν)) :
    Fintype.card ν.ker * (Fintype.card ν.ker-1) ≤ 2*Fintype.card E := by
  have hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714BinaryLift.cayley {x : E | ∃ u : Eˣ, (u : E)=x ∧ ν u=1}) := by
    rintro ⟨f⟩
    exact hfree ⟨(binaryKernelCopy ν).comp f⟩
  have h := Erdos714BinaryLift.cayley_card_bound
    (univ.filter (fun x : E => ∃ u : Eˣ, (u : E)=x ∧ ν u=1)) (by
      simpa only [coe_filter,coe_univ,Set.mem_univ,Finset.mem_univ,true_and] using hf)
  simpa only [binary_kernel_card] using h

omit [CharP E 2] in
lemma power_kernel_card (d : ℕ) :
    Fintype.card (powerMap E d).ker=(Fintype.card E-1).gcd d := by
  change Fintype.card (powMonoidHom d : Eˣ →* Eˣ).rangeRestrict.ker=_
  rw [← Nat.card_eq_fintype_card]
  rw [MonoidHom.ker_rangeRestrict]
  simpa only [Nat.card_eq_fintype_card,Fintype.card_units] using
    IsCyclic.card_powMonoidHom_ker Eˣ d

/-- This concerns the restricted image weight group `Weight E d`. -/
theorem binary_power_bound (d : ℕ)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (powerMap E d))) :
    (Fintype.card E-1).gcd d * ((Fintype.card E-1).gcd d-1) ≤ 2*Fintype.card E := by
  have h := binary_kernel_bound (powerMap E d) hfree
  have hk := power_kernel_card (E := E) d
  simp only [← Nat.card_eq_fintype_card] at hk h ⊢
  rwa [hk] at h


/-- The purely numerical consequence of the binary kernel estimate. -/
lemma cover_kernel_budget (q ℓ d : ℕ) (hq : 2 ≤ q) (hℓ : 0<ℓ)
    (hd : ℓ*d=q^2+q+1) (hb : d*(d-1) ≤ 2*q^3) : q ≤ 2*ℓ^2 := by
  by_contra h
  have hqℓ : ℓ ≤ q := by nlinarith [Nat.mul_le_mul_left ℓ (show 1 ≤ ℓ by omega)]
  have hdpos : 0<d := by nlinarith
  have hs : d-1+1=d := Nat.sub_add_cancel hdpos
  have he : ℓ*(d-1)+ℓ=q^2+q+1 := by nlinarith [congrArg (fun x : ℕ => ℓ*x) hs]
  have h1 : q^2 ≤ ℓ*d := by omega
  have h2 : q^2 ≤ ℓ*(d-1) := by omega
  have hp : q^4 ≤ ℓ^2*(d*(d-1)) := by
    calc
      q^4 = q^2*q^2 := by ring
      _ ≤ (ℓ*d)*(ℓ*(d-1)) := Nat.mul_le_mul h1 h2
      _ = _ := by ring
  have hc : q*q^3 ≤ (2*ℓ^2)*q^3 := by
    calc
      q*q^3 = q^4 := by ring
      _ ≤ ℓ^2*(d*(d-1)) := hp
      _ ≤ ℓ^2*(2*q^3) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  exact h (Nat.le_of_mul_le_mul_right hc (pow_pos (by omega) _))

omit [CharP E 2] in
lemma cover_exponent_divides (q ℓ d : ℕ) (hq : 2 ≤ q)
    (hd : ℓ*d=q^2+q+1) : d ∣ q^3-1 := by
  refine ⟨ℓ*(q-1),?_⟩
  have hs : q-1+1=q := Nat.sub_add_cancel (by omega)
  have he : d*(ℓ*(q-1))+1=q^3 := by
    calc
      d*(ℓ*(q-1))+1 = (ℓ*d)*(q-1)+1 := by ring
      _ = (q^2+q+1)*(q-1)+1 := by rw [hd]
      _ = q^3 := by nlinarith [congrArg (fun x : ℕ => (q^2+q+1)*x) hs]
  omega

/-- No fixed-order cover in characteristic two is free for unbounded q.
The group of weights is precisely the image of the d-th power map. -/
theorem binary_cover_budget (q ℓ d : ℕ) (hq : 2 ≤ q) (hℓ : 0<ℓ)
    (hd : ℓ*d=q^2+q+1) (hE : Fintype.card E=q^3)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (powerMap E d))) :
    q ≤ 2*ℓ^2 := by
  apply cover_kernel_budget q ℓ d hq hℓ hd
  have h := binary_power_bound d hfree
  rw [hE,Nat.gcd_eq_right (cover_exponent_divides q ℓ d hq hd)] at h
  exact h


variable [Fintype W]

omit [CharP E 2] in
lemma kernel_weight_card (ν : Eˣ →* W) :
    Fintype.card E-1 ≤ Fintype.card ν.ker * Fintype.card W := by
  have h := ν.ker.card_mul_index
  rw [Subgroup.index_ker] at h
  have hr := Nat.card_le_card_of_injective (Subtype.val : ν.range → W) Subtype.val_injective
  have hc := Nat.mul_le_mul_left (Nat.card ν.ker) hr
  rw [h] at hc
  simpa only [Nat.card_eq_fintype_card,Fintype.card_units] using hc

/-- Even allowing the image weight group to grow, every free binary
homomorphic-weight host has at most a constant times n^(5/3) edges.
This is a bound for the whole host, not for arbitrary thinnings of it. -/
theorem binary_edge_cube (ν : Eˣ →* W)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph ν)) :
    32*(graph ν).edgeFinset.card^3 ≤
      3*(Fintype.card ((E × W) ⊕ (E × W)))^5 := by
  let Q := Fintype.card E
  let w := Fintype.card W
  let d := Fintype.card ν.ker
  have hb : d*(d-1) ≤ 2*Q := binary_kernel_bound ν hfree
  have hdpos : 0<d := Fintype.card_pos
  have hdle : d ≤ Q-1 := by
    have h := Fintype.card_le_of_injective (Subtype.val : ν.ker → Eˣ) Subtype.val_injective
    simpa only [Fintype.card_units] using h
  have hd2 : d^2 ≤ 3*Q := by
    have hs : d-1+1=d := Nat.sub_add_cancel hdpos
    have hdQ : d ≤ Q := hdle.trans (Nat.sub_le _ _)
    nlinarith [congrArg (fun x : ℕ => d*x) hs]
  have hw : Q-1 ≤ d*w := kernel_weight_card ν
  have hcube : (Q-1)^3 ≤ 3*Q^2*w^2 := by
    calc
      (Q-1)^3 = (Q-1)^2*(Q-1) := by ring
      _ ≤ (d*w)^2*Q := Nat.mul_le_mul (Nat.pow_le_pow_left hw 2) (Nat.sub_le _ _)
      _ = d^2*(w^2*Q) := by ring
      _ ≤ (3*Q)*(w^2*Q) := Nat.mul_le_mul_right _ hd2
      _ = _ := by ring
  have he : (graph ν).edgeFinset.card^3 ≤ 3*(Q*w)^5 := by
    rw [edge_count]
    change (Q*w*(Q-1))^3 ≤ _
    calc
      (Q*w*(Q-1))^3 = (Q*w)^3*(Q-1)^3 := mul_pow _ _ _
      _ ≤ (Q*w)^3*(3*Q^2*w^2) := Nat.mul_le_mul_left _ hcube
      _ = _ := by ring
  have hv : Fintype.card ((E × W) ⊕ (E × W))=2*(Q*w) := by
    simp only [Fintype.card_sum,Fintype.card_prod,Q,w,two_mul]
  rw [hv]
  calc
    32*(graph ν).edgeFinset.card^3 ≤ 32*(3*(Q*w)^5) := Nat.mul_le_mul_left _ he
    _ = _ := by ring

end Erdos714WeightedPower
#print axioms Erdos714WeightedPower.binaryKernelCopy
#print axioms Erdos714WeightedPower.binary_kernel_card
#print axioms Erdos714WeightedPower.binary_kernel_bound
#print axioms Erdos714WeightedPower.power_kernel_card
#print axioms Erdos714WeightedPower.binary_power_bound
#print axioms Erdos714WeightedPower.cover_kernel_budget
#print axioms Erdos714WeightedPower.binary_cover_budget
#print axioms Erdos714WeightedPower.kernel_weight_card
#print axioms Erdos714WeightedPower.binary_edge_cube
