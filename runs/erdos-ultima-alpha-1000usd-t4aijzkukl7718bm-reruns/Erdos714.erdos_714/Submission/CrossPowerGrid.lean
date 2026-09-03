import Submission.SubfieldWeightBudget
import Submission.SkewPowerGrid

/-! Coprime degree-four and degree-five Frobenius orbits produce actual
K4,5 copies in suitable power hosts. This is a construction obstruction,
not a proof or disproof of Erdős714. -/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714CrossPowerGrid
open Erdos714WeightedPower
variable {E : Type*} [Field E]

lemma periodic_iterate (σ : E ≃+* E) (k : ℕ) (x : E) (hx : (σ^k) x=x)
    (n m : ℕ) : (σ^(k*n+m)) x=(σ^m) x := by
  have hn (n : ℕ) : (σ^(k*n)) x=x := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ,pow_add,RingAut.mul_apply,hx,ih]
  rw [show k*n+m=m+k*n by omega,pow_add,RingAut.mul_apply,hn]

lemma sum_orbit (σ : E ≃+* E) (x y : E)
    (hx : (σ^4) x=x) (hy : (σ^5) y=y) (i j : ℕ) :
    (σ^(5*i+16*j)) (x+y)=(σ^i) x+(σ^j) y := by
  rw [map_add]
  have hx' := periodic_iterate σ 4 x hx (i+4*j) i
  have hy' := periodic_iterate σ 5 y hy (i+3*j) j
  rw [show 4*(i+4*j)+i=5*i+16*j by omega] at hx'
  rw [show 5*(i+3*j)+j=5*i+16*j by omega] at hy'
  rw [hx',hy']

/-- Distinct-period points cannot have opposite conjugates. -/
lemma sum_ne_zero (σ : E ≃+* E) (x y : E)
    (hx : (σ^4) x=x) (hx2 : (σ^2) x ≠ x) (hy : (σ^5) y=y) (i j : ℕ) :
    (σ^i) x+(σ^j) y ≠ 0 := by
  intro he
  have hy' : (σ^5) ((σ^j) y)=(σ^j) y := by
    rw [←RingAut.mul_apply,←pow_add,show 5+j=j+5 by omega,pow_add,RingAut.mul_apply,hy]
  have hh := congrArg (fun z : E => (σ^5) z) he
  simp only [map_add,map_zero,hy'] at hh
  have hx5' : (σ^5) ((σ^i) x)=(σ^i) x := add_right_cancel (hh.trans he.symm)
  have hx5 : (σ^5) x=x := by
    apply (σ^i).injective
    rw [←RingAut.mul_apply,←pow_add,show i+5=5+i by omega,pow_add,RingAut.mul_apply]
    exact hx5'
  have hx1 : σ x=x := by
    have ht : (σ^5) x=σ x := by
      rw [show (5 : ℕ)=1+4 by omega,pow_add,RingAut.mul_apply,hx,pow_one]
    exact ht.symm.trans hx5
  apply hx2
  rw [show (2 : ℕ)=1+1 by omega,pow_add,RingAut.mul_apply,pow_one,hx1,hx1]

lemma orbit_four (σ : E ≃+* E) (x : E)
    (hx : (σ^4) x=x) (hx2 : (σ^2) x ≠ x) :
    Function.Injective (fun i : Fin 4 => (σ^i.val) x) := by
  have hp : Function.IsPeriodicPt σ 4 x := hx
  have hn : ¬Function.IsPeriodicPt σ 2 x := hx2
  have hm := Function.minimalPeriod_eq_prime_pow (p := 2) (k := 1) hn hp
  exact Erdos714SkewPowerGrid.orbit_injective_of_period σ x hm

lemma orbit_five (σ : E ≃+* E) (y : E)
    (hy : (σ^5) y=y) (hy1 : σ y ≠ y) :
    Function.Injective (fun i : Fin 5 => (σ^i.val) y) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : Function.IsPeriodicPt σ 5 y := hy
  have hn : ¬Function.IsFixedPt σ y := hy1
  have hm := Function.minimalPeriod_eq_prime hp hn
  exact Erdos714SkewPowerGrid.orbit_injective_of_period σ y hm

def modulus (q : ℕ) : ℕ := (q^4-1)*(q^5-1)

lemma modulus_divides (q i j : ℕ) :
    modulus q ∣ (q^(5*i)-1)*(q^(16*j)-1) := by
  rw [modulus,mul_comm (q^4-1)]
  apply Nat.mul_dvd_mul
  · exact Nat.pow_sub_one_dvd_pow_sub_one _ ⟨i,rfl⟩
  · exact Nat.pow_sub_one_dvd_pow_sub_one _ ⟨4*j,by omega⟩

lemma flat_power (q : ℕ) (hq : 1 ≤ q) (w : E) (hw : w^(modulus q)=1) (i j : ℕ) :
    w^(q^(5*i+16*j))*w=w^(q^(5*i))*w^(q^(16*j)) := by
  have ha : 1 ≤ q^(5*i) := Nat.one_le_pow _ _ hq
  have hb : 1 ≤ q^(16*j) := Nat.one_le_pow _ _ hq
  have hp : w^((q^(5*i)-1)*(q^(16*j)-1))=1 := by
    obtain ⟨k,hk⟩ := modulus_divides q i j
    rw [hk,pow_mul,hw,one_pow]
  have hn : q^(5*i)*q^(16*j)+1 =
      (q^(5*i)-1)*(q^(16*j)-1)+(q^(5*i)+q^(16*j)) := by
    have ha' : q^(5*i)-1+1=q^(5*i) := Nat.sub_add_cancel ha
    have hb' : q^(16*j)-1+1=q^(16*j) := Nat.sub_add_cancel hb
    nlinarith
  rw [pow_add,←pow_succ,hn,pow_add,hp,one_mul,pow_add]

lemma power_orbit (σ : E ≃+* E) (q d : ℕ) (hσ : ∀ z, σ z=z^q)
    (x y : E) (hx : (σ^4) x=x) (hy : (σ^5) y=y) (i j : ℕ) :
    ((σ^i) x+(σ^j) y)^d=((x+y)^d)^(q^(5*i+16*j)) := by
  rw [← sum_orbit σ x y hx hy i j,Erdos714SkewPowerGrid.frobenius_iterate σ q hσ]
  rw [←pow_mul,←pow_mul,Nat.mul_comm]

/-- Flatness is checked against the ORIGINAL power equation at every entry. -/
theorem flat_orbit (σ : E ≃+* E) (q d : ℕ) (hq : 1 ≤ q)
    (hσ : ∀ z, σ z=z^q) (x y : E) (hx : (σ^4) x=x) (hy : (σ^5) y=y)
    (hw : ((x+y)^d)^(modulus q)=1) (i j : ℕ) :
    ((σ^i) x+(σ^j) y)^d*(x+y)^d =
      ((σ^i) x+y)^d*(x+(σ^j) y)^d := by
  have h := flat_power q hq ((x+y)^d) hw i j
  have hi := power_orbit σ q d hσ x y hx hy i 0
  have hj := power_orbit σ q d hσ x y hx hy 0 j
  simp only [mul_zero,add_zero,zero_add,pow_zero,RingAut.one_apply] at hi hj
  rw [power_orbit σ q d hσ x y hx hy i j,hi,hj]
  exact h

/-- The weights have explicit power preimages; no enlargement of Weight E d. -/
def crossCopy (σ : E ≃+* E) (q d : ℕ) (hq : 1 ≤ q)
    (hσ : ∀ z, σ z=z^q) (x y : E) (hx : (σ^4) x=x) (hx2 : (σ^2) x ≠ x)
    (hy : (σ^5) y=y) (hy1 : σ y ≠ y) (hw : ((x+y)^d)^(modulus q)=1) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 5)) (graph (powerMap E d)) := by
  let ν := powerMap E d
  let z (i j : ℕ) : Eˣ := Units.mk0 ((σ^i) x+(σ^j) y)
    (sum_ne_zero σ x y hx hx2 hy i j)
  let L : Fin 4 ↪ E × Weight E d :=
    ⟨fun i => ((σ^i.val) x,ν (z i.val 0)/ν (z 0 0)), by
      intro i j he
      exact orbit_four σ x hx hx2 (congrArg Prod.fst he)⟩
  let R : Fin 5 ↪ E × Weight E d :=
    ⟨fun j => ((σ^j.val) y,ν (z 0 j.val)), by
      intro i j he
      exact orbit_five σ y hy hy1 (congrArg Prod.fst he)⟩
  have he (i : Fin 4) (j : Fin 5) : relation ν (L i) (R j) := by
    refine ⟨z i.val j.val,rfl,?_⟩
    apply Subtype.ext
    apply Units.ext
    change ((z i.val j.val)^d : Eˣ).val =
      (((z i.val 0)^d/(z 0 0)^d)*(z 0 j.val)^d : Eˣ).val
    simp only [Units.val_mul,Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,
      z,Units.val_mk0,pow_zero,RingAut.one_apply]
    have hw0 : (x+y)^d ≠ 0 := pow_ne_zero _ (by
      simpa using sum_ne_zero σ x y hx hx2 hy 0 0)
    calc
      _ = (((σ^i.val) x+y)^d*(x+(σ^j.val) y)^d)/(x+y)^d :=
        (eq_div_iff hw0).mpr (flat_orbit σ q d hq hσ x y hx hy hw i.val j.val)
      _ = _ := by ring
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl k => simp at hab
    | inr j => exact he i j
  | inr j =>
    cases b with
    | inl i => exact he i j
    | inr k => simp at hab

theorem not_free_of_cross (σ : E ≃+* E) (q d : ℕ) (hq : 1 ≤ q)
    (hσ : ∀ z, σ z=z^q) (x y : E) (hx : (σ^4) x=x) (hx2 : (σ^2) x ≠ x)
    (hy : (σ^5) y=y) (hy1 : σ y ≠ y) (hw : ((x+y)^d)^(modulus q)=1) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (powerMap E d)) := by
  let e := (Function.Embedding.refl (Fin 4)).sumMap (Fin.castLEEmb (by decide : 4 ≤ 5))
  let c : Copy (completeBipartiteGraph (Fin 4) (Fin 4))
      (completeBipartiteGraph (Fin 4) (Fin 5)) :=
    ⟨⟨e,by intro a b h; cases a <;> cases b <;> simp_all [e]⟩,e.injective⟩
  intro hf
  exact hf ⟨(crossCopy σ q d hq hσ x y hx hx2 hy hy1 hw).comp c⟩

section Finite
variable {F : Type*} [Field F] [Algebra F E]

/-- A normal basis supplies the two exact orbit lengths in every characteristic. -/
theorem cross_parameters [FiniteDimensional F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E) (hσ : orderOf σ=20) :
    ∃ x y : E, (σ^4) x=x ∧ (σ^2) x ≠ x ∧ (σ^5) y=y ∧ σ y ≠ y := by
  let b := IsGalois.normalBasis F E
  have hact (e f : E ≃ₐ[F] E) : e (b f)=b (e*f) := by
    dsimp only [b]
    rw [IsGalois.normalBasis_apply f,←AlgEquiv.mul_apply,←IsGalois.normalBasis_apply (e*f)]
  have h20 : σ^20=1 := by simpa only [hσ] using pow_orderOf_eq_one σ
  have hn (n : ℕ) (h0 : 0<n) (h1 : n<20) : σ^n ≠ 1 :=
    pow_ne_one_of_lt_orderOf h0.ne' (hσ ▸ h1)
  let x := b 1+b (σ^4)+b (σ^8)+b (σ^12)+b (σ^16)
  let y := b 1+b (σ^5)+b (σ^10)+b (σ^15)
  have hx : (σ^4) x=x := by
    dsimp [x]
    simp only [map_add,hact,mul_one,←pow_add]
    norm_num only [Nat.reduceAdd]
    rw [h20]
    ring
  have hy : (σ^5) y=y := by
    dsimp [y]
    simp only [map_add,hact,mul_one,←pow_add]
    norm_num only [Nat.reduceAdd]
    rw [h20]
    ring
  refine ⟨x,y,hx,?_,hy,?_⟩
  · have hx2 : (σ^2) x=b (σ^2)+b (σ^6)+b (σ^10)+b (σ^14)+b (σ^18) := by
      dsimp [x]
      simp only [map_add,hact,mul_one,←pow_add]
    intro h
    rw [hx2] at h
    have hc := congrArg (fun z : E => b.repr z 1) h
    simp [x,hn 2 (by decide) (by decide),hn 4 (by decide) (by decide),
      hn 6 (by decide) (by decide),hn 8 (by decide) (by decide),
      hn 10 (by decide) (by decide),hn 12 (by decide) (by decide),
      hn 14 (by decide) (by decide),hn 16 (by decide) (by decide),
      hn 18 (by decide) (by decide)] at hc
  · have hy1 : σ y=b σ+b (σ^6)+b (σ^11)+b (σ^16) := by
      dsimp [y]
      simp only [map_add,hact,mul_one,←pow_succ']
    intro h
    rw [hy1] at h
    have hc := congrArg (fun z : E => b.repr z 1) h
    have hσ1 : σ ≠ 1 := by simpa only [pow_one] using hn 1 (by decide) (by decide)
    simp [y,hσ1,hn 5 (by decide) (by decide),hn 6 (by decide) (by decide),
      hn 10 (by decide) (by decide),hn 11 (by decide) (by decide),
      hn 15 (by decide) (by decide),hn 16 (by decide) (by decide)] at hc

variable [Fintype F] [Fintype E]

/-- A concrete divisor criterion, with all field parameters constructed. -/
theorem finite_not_free (hdegree : Module.finrank F E=20) (d : ℕ)
    (hd : Fintype.card E-1 ∣ d*modulus (Fintype.card F)) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (powerMap E d)) := by
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic F E
  have hσ : orderOf σ=20 :=
    (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F E).trans hdegree
  obtain ⟨x,y,hx,hx2,hy,hy1⟩ := cross_parameters σ hσ
  have hf (z : E) : σ.toRingEquiv z=z^(Fintype.card F) := rfl
  apply not_free_of_cross σ.toRingEquiv (Fintype.card F) d Fintype.card_pos
    hf x y hx hx2 hy hy1
  have hz : x+y ≠ 0 := by
    simpa using sum_ne_zero σ.toRingEquiv x y hx hx2 hy 0 0
  let u : Eˣ := Units.mk0 (x+y) hz
  have hu : u^(Fintype.card E-1)=1 := by
    simpa only [Fintype.card_units] using pow_card_eq_one (x := u)
  obtain ⟨m,hm⟩ := hd
  have hpow : u^(d*modulus (Fintype.card F))=1 := by rw [hm,pow_mul,hu,one_pow]
  have he := congrArg (fun v : Eˣ => (v : E)) hpow
  simpa only [Units.val_pow_eq_pow_val,Units.val_one,Units.val_mk0,pow_mul] using he
end Finite
end Erdos714CrossPowerGrid
#print axioms Erdos714CrossPowerGrid.sum_ne_zero
#print axioms Erdos714CrossPowerGrid.flat_orbit
#print axioms Erdos714CrossPowerGrid.crossCopy
#print axioms Erdos714CrossPowerGrid.cross_parameters
#print axioms Erdos714CrossPowerGrid.finite_not_free
