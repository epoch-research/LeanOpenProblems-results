import Submission.CyclotomicSubfield
import Submission.UnbalancedBounds

/-! Exact subfield-image budgets for weighted multiplicative hosts. A subfield
need not lie in the kernel: a sufficiently small image already obstructs
constant-density free thinnings. These are restricted-construction results,
not a proof or disproof of Erdős714. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714WeightedPower
variable {E K W U : Type*} [Field E] [Field K] [CommGroup W] [CommGroup U]

/-- A field injection and a compatible injective weight map give an actual
copy of the smaller weighted graph, including its nonzero-sum condition. -/
def compatibleCopy (κ : Kˣ →* U) (ν : Eˣ →* W) (ι : K →+* E)
    (φ : U →* W) (hφ : Function.Injective φ)
    (hcomp : ∀ z, ν (Units.map ι.toMonoidHom z)=φ (κ z)) :
    Copy (graph κ) (graph ν) := by
  let f : K × U → E × W := fun p => (ι p.1,φ p.2)
  have hf : Function.Injective f := by
    intro p q h
    exact Prod.ext (ι.injective (congrArg Prod.fst h)) (hφ (congrArg Prod.snd h))
  have he (p q : K × U) (hpq : relation κ p q) : relation ν (f p) (f q) := by
    obtain ⟨z,hz,hκ⟩ := hpq
    refine ⟨Units.map ι.toMonoidHom z,?_,?_⟩
    · change ι (z : K)=ι p.1+ι q.1
      rw [hz,map_add]
    · change ν (Units.map ι.toMonoidHom z)=φ p.2*φ q.2
      rw [hcomp,hκ,map_mul]
  refine ⟨⟨Sum.map f f,?_⟩,Sum.map_injective.mpr ⟨hf,hf⟩⟩
  intro p q hpq
  cases p <;> cases q
  · exact False.elim hpq
  · exact he _ _ hpq
  · exact he _ _ hpq
  · exact False.elim hpq

abbrev RestrictedWeight (ν : Eˣ →* W) (ι : K →+* E) :=
  (ν.comp (Units.map ι.toMonoidHom)).range

def restrictedMap (ν : Eˣ →* W) (ι : K →+* E) : Kˣ →* RestrictedWeight ν ι :=
  (ν.comp (Units.map ι.toMonoidHom)).rangeRestrict

def restrictionCopy (ν : Eˣ →* W) (ι : K →+* E) :
    Copy (graph (restrictedMap ν ι)) (graph ν) :=
  compatibleCopy (restrictedMap ν ι) ν ι
    (ν.comp (Units.map ι.toMonoidHom)).range.subtype Subtype.val_injective (fun _ => rfl)

/-- Power-image weights embed by applying the field map to the underlying unit.
Membership is witnessed by the mapped original power preimage. -/
def powerWeightMap (d : ℕ) (ι : K →+* E) : Weight K d →* Weight E d :=
  ((Units.map ι.toMonoidHom).comp (Weight K d).subtype).codRestrict (Weight E d) (by
    intro u
    obtain ⟨v,hv⟩ := u.property
    refine ⟨Units.map ι.toMonoidHom v,?_⟩
    change (Units.map ι.toMonoidHom v)^d=Units.map ι.toMonoidHom u.val
    rw [← map_pow]
    exact congrArg (Units.map ι.toMonoidHom) hv)

lemma powerWeightMap_injective (d : ℕ) (ι : K →+* E) :
    Function.Injective (powerWeightMap d ι) := by
  intro u v h
  apply Subtype.ext
  exact Units.map_injective ι.injective (congrArg Subtype.val h)

/-- In particular no surjection of weights is being used as a vertex injection. -/
def powerSubfieldCopy (d : ℕ) (ι : K →+* E) :
    Copy (graph (powerMap K d)) (graph (powerMap E d)) :=
  compatibleCopy (powerMap K d) (powerMap E d) ι
    (powerWeightMap d ι) (powerWeightMap_injective d ι) (by
      intro z
      apply Subtype.ext
      change (Units.map ι.toMonoidHom z)^d=Units.map ι.toMonoidHom (z^d)
      exact (map_pow _ _ _).symm)

variable [Fintype E] [Fintype W]

/-- The exact ordered-star bound uses the regular degree |E|-1, rather than
a rounded degree or a hypothesized asymptotic count. -/
lemma regular_star_bound (ν : Eˣ →* W)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph ν)) :
    (Fintype.card E-4)^4 ≤ 3*(Fintype.card E*Fintype.card W)^3 := by
  let S (p : E × W) := univ.filter (fun q => relation ν p q)
  have hg : Erdos714Packing.incidence S=graph ν := by
    ext p q
    cases p <;> cases q <;>
      simp [S,graph,Erdos714Tensor.incidence,Erdos714Packing.incidence]
  have h := Erdos714Unbalanced.star_bound S (by decide : 0 < 4) (by rwa [hg])
  simp only [S,neighbor_card,sum_const,card_univ,Fintype.card_prod,
    nsmul_eq_mul,Nat.cast_id] at h
  have hn : 1 ≤ Fintype.card E := Fintype.card_pos
  have hsub : Fintype.card E-1+1-4=Fintype.card E-4 := by omega
  have hp : (Fintype.card E-4)^4 ≤ (Fintype.card E-1).descFactorial 4 := by
    simpa only [hsub] using Nat.pow_sub_le_descFactorial (Fintype.card E-1) 4
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card E*Fintype.card W) _
    (mul_pos Fintype.card_pos Fintype.card_pos)
  calc
    _ ≤ (Fintype.card E*Fintype.card W)*(Fintype.card E-1).descFactorial 4 :=
      Nat.mul_le_mul_left _ hp
    _ ≤ 3*(Fintype.card E*Fintype.card W).descFactorial 4 := h
    _ ≤ 3*(Fintype.card E*Fintype.card W)^4 :=
      Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
    _ = _ := by ring

/-- A necessary size condition for the full host, in every characteristic. -/
theorem weight_budget (ν : Eˣ →* W)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph ν)) :
    Fintype.card E ≤ 48*Fintype.card W^3 := by
  let Q := Fintype.card E
  let w := Fintype.card W
  have hw : 1 ≤ w^3 := Nat.one_le_pow _ _ Fintype.card_pos
  by_cases hQ : 8 ≤ Q
  · have hs : Q ≤ 2*(Q-4) := by omega
    have h := regular_star_bound ν hfree
    apply Nat.le_of_mul_le_mul_right (c := Q^3) _ (pow_pos (by omega) _)
    calc
      Q*Q^3 = Q^4 := by ring
      _ ≤ (2*(Q-4))^4 := Nat.pow_le_pow_left hs 4
      _ = 16*(Q-4)^4 := by ring
      _ ≤ 16*(3*(Q*w)^3) := Nat.mul_le_mul_left _ h
      _ = _ := by ring
  · change Q ≤ 48*w^3
    omega

variable [Fintype K]

omit [Fintype E] [Fintype W] in
/-- The image is the actual subgroup of W attained by subfield units. -/
theorem subfield_image_budget (ν : Eˣ →* W) (ι : K →+* E)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph ν)) :
    Fintype.card K ≤ 48*Fintype.card (RestrictedWeight ν ι)^3 := by
  apply weight_budget (restrictedMap ν ι)
  rintro ⟨f⟩
  exact hfree ⟨(restrictionCopy ν ι).comp f⟩

variable [Fintype U]

/-- Averaging a copied weighted host controls EVERY free edge subgraph of the
larger host. Neither the subgraph nor the embedding must be invariant. -/
theorem copied_weight_thinning (κ : Kˣ →* U) (ν : Eˣ →* W)
    (c : Copy (graph κ) (graph ν))
    (H : SimpleGraph ((E × W) ⊕ (E × W))) (hH : H ≤ graph ν)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    Fintype.card K*H.edgeFinset.card^4 ≤
      165888*Fintype.card U^3*(graph ν).edgeFinset.card^4 := by
  let Q := Fintype.card K
  let w := Fintype.card U
  let e := H.edgeFinset.card
  let N := (graph ν).edgeFinset.card
  have hQ : 2 ≤ Q := Fintype.one_lt_card
  have hw : 0 < w := Fintype.card_pos
  have h := Erdos714GraphAveraging.edge_transitive_bound
    (completeBipartiteGraph (Fin 4) (Fin 4)) H (graph ν) (graph κ) c hH hfree
      (edge_transitive ν)
  have hc : Fintype.card ((K × U) ⊕ (K × U))=2*(Q*w) := by
    simp only [Fintype.card_sum,Fintype.card_prod]
    dsimp [Q,w]
    ring
  rw [edge_count,hc] at h
  have hp := Nat.pow_le_pow_left h 4
  simp only [mul_pow] at hp
  have hb := hp.trans (Nat.mul_le_mul_right (N^4)
    (show extremalNumber (2*(Q*w)) (completeBipartiteGraph (Fin 4) (Fin 4))^4 ≤
      10368*(Q*w)^7 from Erdos714BicliquePartition.extremal_fourth (Q*w)))
  have hb' : (Q-1)^4*e^4 ≤ 10368*(Q*w)^3*N^4 := by
    apply Nat.le_of_mul_le_mul_right (c := (Q*w)^4) _
      (pow_pos (mul_pos (by omega) hw) _)
    convert hb using 1 <;> dsimp [Q,w,e,N] <;> ring
  have hs : Q ≤ 2*(Q-1) := by omega
  apply Nat.le_of_mul_le_mul_right (c := Q^3) _ (pow_pos (by omega) _)
  calc
    (Q*e^4)*Q^3 = Q^4*e^4 := by ring
    _ ≤ (2*(Q-1))^4*e^4 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hs 4)
    _ = 16*((Q-1)^4*e^4) := by ring
    _ ≤ 16*(10368*(Q*w)^3*N^4) := Nat.mul_le_mul_left _ hb'
    _ = _ := by ring

omit [Fintype U] in
/-- Unlike the kernel-only result, nontrivial restricted weights are allowed. -/
theorem subfield_image_thinning (ν : Eˣ →* W) (ι : K →+* E)
    (H : SimpleGraph ((E × W) ⊕ (E × W))) (hH : H ≤ graph ν)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    Fintype.card K*H.edgeFinset.card^4 ≤
      165888*Fintype.card (RestrictedWeight ν ι)^3*(graph ν).edgeFinset.card^4 :=
  copied_weight_thinning (restrictedMap ν ι) ν (restrictionCopy ν ι) H hH hfree

omit [Fintype U] [Fintype W] [Fintype E] in
/-- A factor of the kernel exponent bounds the ACTUAL power image. -/
lemma power_image_le_factor (d a b : ℕ) (hK : Fintype.card K-1=a*b) (hd : b ∣ d) :
    Fintype.card (Weight K d) ≤ a := by
  have hKpos : 0 < Fintype.card K-1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hab : 0 < a*b := hK ▸ hKpos
  have hb : 0 < b := by nlinarith
  have hg : 0 < (a*b).gcd d := Nat.gcd_pos_of_pos_left d hab
  have hbg : b ≤ (a*b).gcd d :=
    Nat.le_of_dvd hg (Nat.dvd_gcd (dvd_mul_left b a) hd)
  rw [weight_card,hK]
  calc
    (a*b)/(a*b).gcd d ≤ (a*b)/b := Nat.div_le_div_left hbg hb
    _ = a := Nat.mul_div_cancel a hb

omit [Fintype U] [Fintype W] [Fintype E] in
/-- A numerical gcd test for every subfield of a free power host. -/
theorem power_subfield_budget (d : ℕ) (ι : K →+* E)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (powerMap E d))) :
    Fintype.card K ≤ 48*((Fintype.card K-1)/(Fintype.card K-1).gcd d)^3 := by
  rw [← weight_card (E := K)]
  apply weight_budget (powerMap K d)
  rintro ⟨f⟩
  exact hfree ⟨(powerSubfieldCopy d ι).comp f⟩

omit [Fintype U] [Fintype W] in
/-- The gcd version also bounds arbitrary non-invariant edge thinnings. -/
theorem power_subfield_thinning (d : ℕ) (ι : K →+* E)
    (H : SimpleGraph ((E × Weight E d) ⊕ (E × Weight E d)))
    (hH : H ≤ graph (powerMap E d))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    Fintype.card K*H.edgeFinset.card^4 ≤
      165888*((Fintype.card K-1)/(Fintype.card K-1).gcd d)^3*
        (graph (powerMap E d)).edgeFinset.card^4 := by
  rw [← weight_card (E := K)]
  exact copied_weight_thinning (powerMap K d) (powerMap E d)
    (powerSubfieldCopy d ι) H hH hfree

/-- A fixed retained fraction bounds the subfield-to-weight cubic ratio. -/
theorem copied_weight_retention (κ : Kˣ →* U) (ν : Eˣ →* W)
    (c : Copy (graph κ) (graph ν))
    (H : SimpleGraph ((E × W) ⊕ (E × W))) (hH : H ≤ graph ν)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (C : ℕ) (he : 0 < H.edgeFinset.card)
    (hret : (graph ν).edgeFinset.card ≤ C*H.edgeFinset.card) :
    Fintype.card K ≤ 165888*C^4*Fintype.card U^3 := by
  have h := copied_weight_thinning κ ν c H hH hfree
  apply Nat.le_of_mul_le_mul_right (c := H.edgeFinset.card^4) _ (pow_pos he _)
  calc
    _ ≤ 165888*Fintype.card U^3*(graph ν).edgeFinset.card^4 := h
    _ ≤ 165888*Fintype.card U^3*(C*H.edgeFinset.card)^4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hret 4)
    _ = _ := by ring

omit [Fintype U] [Fintype W] in
/-- This test needs only an exponent divisor, not a cyclotomic factorization. -/
theorem power_factor_retention (d a b : ℕ) (ι : K →+* E)
    (hK : Fintype.card K-1=a*b) (hd : b ∣ d)
    (H : SimpleGraph ((E × Weight E d) ⊕ (E × Weight E d)))
    (hH : H ≤ graph (powerMap E d))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (C : ℕ) (he : 0 < H.edgeFinset.card)
    (hret : (graph (powerMap E d)).edgeFinset.card ≤ C*H.edgeFinset.card) :
    Fintype.card K ≤ 165888*C^4*a^3 := by
  have h := copied_weight_retention (powerMap K d) (powerMap E d)
    (powerSubfieldCopy d ι) H hH hfree C he hret
  exact h.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (power_image_le_factor d a b hK hd) 3))

/-- A subfield of exponent s with image of exponent t is incompatible with
fixed retained density whenever 3t<s. All finite lower-order terms must be
accounted for in the supplied cardinality and image estimates. -/
theorem subfield_exponent_retention (κ : Kˣ →* U) (ν : Eˣ →* W)
    (c : Copy (graph κ) (graph ν))
    (H : SimpleGraph ((E × W) ⊕ (E × W))) (hH : H ≤ graph ν)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (q s t C : ℕ) (hq : 1 ≤ q) (hK : q^s ≤ Fintype.card K)
    (hU : Fintype.card U ≤ q^t) (hst : 3*t < s)
    (he : 0 < H.edgeFinset.card)
    (hret : (graph ν).edgeFinset.card ≤ C*H.edgeFinset.card) :
    q ≤ 165888*C^4 := by
  have hb := hK.trans (copied_weight_retention κ ν c H hH hfree C he hret)
  have hb' : q^s ≤ 165888*C^4*(q^t)^3 :=
    hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hU 3))
  apply Nat.le_of_mul_le_mul_right (c := (q^t)^3) _ (by positivity)
  calc
    q*(q^t)^3 = q^(3*t+1) := by rw [show 3*t+1=t*3+1 by omega,pow_add,pow_one,pow_mul]; ring
    _ ≤ q^s := Nat.pow_le_pow_right hq (by omega)
    _ ≤ _ := hb'

end Erdos714WeightedPower
#print axioms Erdos714WeightedPower.compatibleCopy
#print axioms Erdos714WeightedPower.regular_star_bound
#print axioms Erdos714WeightedPower.weight_budget
#print axioms Erdos714WeightedPower.subfield_image_budget
#print axioms Erdos714WeightedPower.copied_weight_thinning
#print axioms Erdos714WeightedPower.subfield_image_thinning
#print axioms Erdos714WeightedPower.powerWeightMap_injective
#print axioms Erdos714WeightedPower.powerSubfieldCopy
#print axioms Erdos714WeightedPower.power_image_le_factor
#print axioms Erdos714WeightedPower.power_subfield_budget
#print axioms Erdos714WeightedPower.power_subfield_thinning
#print axioms Erdos714WeightedPower.copied_weight_retention
#print axioms Erdos714WeightedPower.power_factor_retention
#print axioms Erdos714WeightedPower.subfield_exponent_retention
