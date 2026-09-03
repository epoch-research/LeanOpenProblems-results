import Submission.TwelfthPowerQuotient

/-! The characteristic-two counterpart of the skew degree-twelve grid. -/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714AffinePowerGrid
open Erdos714SkewPowerGrid
variable {E : Type*} [Field E] [CharP E 2]

omit [CharP E 2] in
lemma affine_iterate (σ : E ≃+* E) (k : ℕ) (x : E) (hx : (σ^k) x=x+1)
    (n m : ℕ) : (σ^(k*n+m)) x=(σ^m) x+n := by
  have hn (n : ℕ) : (σ^(k*n)) x=x+n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ,pow_add,RingAut.mul_apply,hx,map_add,map_one,ih,Nat.cast_add,Nat.cast_one]
      ring
  rw [show k*n+m=m+k*n by omega,pow_add,RingAut.mul_apply,hn,map_add,map_natCast]

lemma sum_orbit (σ : E ≃+* E) (x y : E)
    (hx : (σ^2) x=x+1) (hy : (σ^3) y=y+1) (i j : ℕ) :
    (σ^(3*i+10*j)) (x+y)=(σ^i) x+(σ^j) y := by
  have h₂ : (2 : E)=0 := CharP.cast_eq_zero E 2
  have hx' := affine_iterate σ 2 x hx (i+5*j) i
  have hy' := affine_iterate σ 3 y hy (i+3*j) j
  have hix : 2*(i+5*j)+i=3*i+10*j := by omega
  have hiy : 3*(i+3*j)+j=3*i+10*j := by omega
  rw [hix] at hx'
  rw [hiy] at hy'
  rw [map_add,hx',hy']
  push_cast
  linear_combination ((i : E)+4*j)*h₂

lemma base_modulus_divides (q : ℕ) (hq : 1 ≤ q) (i j : ℕ) :
    weightSize q ∣ (q^(3*i)-1)*(q^(10*j)-1) := by
  have hs : q^2-1=(q-1)*(q+1) := by
    cases q with
    | zero => omega
    | succ k =>
      have he : (k+1)^2=k*(k+2)+1 := by ring
      simp only [Nat.add_sub_cancel]
      change (k+1)^2-1=k*(k+2)
      omega
  have hb : weightSize q ∣ (q^3-1)*(q^2-1) := by
    refine ⟨q-1,?_⟩
    rw [hs,weightSize]
    ring
  apply hb.trans
  exact Nat.mul_dvd_mul (Nat.pow_sub_one_dvd_pow_sub_one _ ⟨i,rfl⟩)
    (Nat.pow_sub_one_dvd_pow_sub_one _ ⟨5*j,by omega⟩)

omit [CharP E 2] in
lemma flat_power (q : ℕ) (hq : 1 ≤ q) (w : E) (hw : w^(weightSize q)=1) (i j : ℕ) :
    w^(q^(3*i+10*j))*w=w^(q^(3*i))*w^(q^(10*j)) := by
  have ha : 1 ≤ q^(3*i) := Nat.one_le_pow _ _ hq
  have hb : 1 ≤ q^(10*j) := Nat.one_le_pow _ _ hq
  have hp : w^((q^(3*i)-1)*(q^(10*j)-1))=1 := by
    obtain ⟨k,hk⟩ := base_modulus_divides q hq i j
    rw [hk,pow_mul,hw,one_pow]
  have hn : q^(3*i)*q^(10*j)+1 =
      (q^(3*i)-1)*(q^(10*j)-1)+(q^(3*i)+q^(10*j)) := by
    have ha' := Nat.sub_add_cancel ha
    have hb' := Nat.sub_add_cancel hb
    nlinarith
  rw [pow_add,←pow_succ,hn,pow_add,hp,one_mul,pow_add]

lemma flat_orbit (σ : E ≃+* E) (q d : ℕ) (hq : 1 ≤ q) (hσ : ∀ z, σ z=z^q)
    (x y : E) (hx : (σ^2) x=x+1) (hy : (σ^3) y=y+1)
    (hw : ((x+y)^d)^(weightSize q)=1) (i j : ℕ) :
    ((σ^i) x+(σ^j) y)^d*(x+y)^d=((σ^i) x+y)^d*(x+(σ^j) y)^d := by
  have ho (i j : ℕ) : ((σ^i) x+(σ^j) y)^d=((x+y)^d)^(q^(3*i+10*j)) := by
    rw [←sum_orbit σ x y hx hy i j,frobenius_iterate σ q hσ]
    simp only [←pow_mul]
    congr 1
    ring
  have hi := ho i 0
  have hj := ho 0 j
  simp only [mul_zero,add_zero,zero_add,pow_zero,RingAut.one_apply] at hi hj
  rw [ho,hi,hj]
  exact flat_power q hq ((x+y)^d) hw i j

lemma sum_ne_zero (σ : E ≃+* E) (x y : E)
    (hx : (σ^2) x=x+1) (hy : (σ^3) y=y+1) (i j : ℕ) :
    (σ^i) x+(σ^j) y ≠ 0 := by
  have h₂ : (2 : E)=0 := CharP.cast_eq_zero E 2
  have hx6 : (σ^6) ((σ^i) x)=(σ^i) x+1 := by
    have h := affine_iterate σ 2 x hx 3 i
    have h₃ : (3 : E)=1 := by linear_combination h₂
    simpa [pow_add,RingAut.mul_apply,h₃] using h
  have hy6 : (σ^6) ((σ^j) y)=(σ^j) y := by
    simpa [pow_add,RingAut.mul_apply,h₂] using affine_iterate σ 3 y hy 2 j
  intro he
  have he' := congrArg (fun z : E => (σ^6) z) he
  dsimp only at he'
  rw [map_add,map_zero,hx6,hy6] at he'
  have hf : (1 : E)=0 := by linear_combination he'-he
  exact one_ne_zero hf

lemma orbit_four (σ : E ≃+* E) (x : E) (hx : (σ^2) x=x+1) :
    Function.Injective (fun i : Fin 4 => (σ^i.val) x) := by
  have h₂ : (2 : E)=0 := CharP.cast_eq_zero E 2
  have hp : Function.IsPeriodicPt σ 4 x := by
    simpa [RingAut.coe_pow,h₂] using affine_iterate σ 2 x hx 2 0
  have hn : ¬Function.IsPeriodicPt σ 2 x := by
    intro h
    have he : (σ^2) x=x := h
    rw [hx] at he
    exact one_ne_zero (by linear_combination he : (1 : E)=0)
  exact orbit_injective_of_period σ x
    (Function.minimalPeriod_eq_prime_pow (p := 2) (k := 1) hn hp)

lemma orbit_six (σ : E ≃+* E) (y : E)
    (hy : (σ^3) y=y+1) (hy2 : (σ^2) y ≠ y) :
    Function.Injective (fun i : Fin 6 => (σ^i.val) y) := by
  have h₂ : (2 : E)=0 := CharP.cast_eq_zero E 2
  have hp : Function.IsPeriodicPt σ 6 y := by
    simpa [RingAut.coe_pow,h₂] using affine_iterate σ 3 y hy 2 0
  have hn2 : ¬Function.IsPeriodicPt σ 2 y := hy2
  have hn3 : ¬Function.IsPeriodicPt σ 3 y := by
    intro h
    have he : (σ^3) y=y := h
    rw [hy] at he
    exact one_ne_zero (by linear_combination he : (1 : E)=0)
  have hc : Function.minimalPeriod σ y ∈ (6 : ℕ).divisors :=
    Nat.mem_divisors.mpr ⟨hp.minimalPeriod_dvd,by decide⟩
  have hm : Function.minimalPeriod σ y=6 := by
    have hv : (6 : ℕ).divisors={1,2,3,6} := by decide
    rw [hv] at hc
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc
    have hnd2 : ¬Function.minimalPeriod σ y ∣ 2 := by
      rwa [←Function.isPeriodicPt_iff_minimalPeriod_dvd]
    have hnd3 : ¬Function.minimalPeriod σ y ∣ 3 := by
      rwa [←Function.isPeriodicPt_iff_minimalPeriod_dvd]
    rcases hc with h | h | h | h
    · rw [h] at hnd2; exact False.elim (hnd2 (one_dvd _))
    · rw [h] at hnd2; exact False.elim (hnd2 (dvd_refl _))
    · rw [h] at hnd3; exact False.elim (hnd3 (dvd_refl _))
    · exact h
  exact orbit_injective_of_period σ y hm

/-- The additive Frobenius orbit gives a genuine K4,6 in characteristic two. -/
def affineCopy (σ : E ≃+* E) (q d : ℕ) (hq : 1 ≤ q) (hσ : ∀ z, σ z=z^q)
    (x y : E) (hx : (σ^2) x=x+1) (hy : (σ^3) y=y+1)
    (hy2 : (σ^2) y ≠ y) (hw : ((x+y)^d)^(weightSize q)=1) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 6))
      (Erdos714WeightedPower.graph (Erdos714WeightedPower.powerMap E d)) := by
  let ν := Erdos714WeightedPower.powerMap E d
  let z (i j : ℕ) : Eˣ := Units.mk0 ((σ^i) x+(σ^j) y) (sum_ne_zero σ x y hx hy i j)
  let L : Fin 4 ↪ E × Erdos714WeightedPower.Weight E d :=
    ⟨fun i => ((σ^i.val) x,ν (z i.val 0)/ν (z 0 0)), by
      intro i j he
      exact orbit_four σ x hx (congrArg Prod.fst he)⟩
  let R : Fin 6 ↪ E × Erdos714WeightedPower.Weight E d :=
    ⟨fun j => ((σ^j.val) y,ν (z 0 j.val)), by
      intro i j he
      exact orbit_six σ y hy hy2 (congrArg Prod.fst he)⟩
  have he (i : Fin 4) (j : Fin 6) : Erdos714WeightedPower.relation ν (L i) (R j) := by
    refine ⟨z i.val j.val,rfl,?_⟩
    apply Subtype.ext
    apply Units.ext
    change ((z i.val j.val)^d : Eˣ).val =
      (((z i.val 0)^d/(z 0 0)^d)*(z 0 j.val)^d : Eˣ).val
    simp only [Units.val_mul,Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,
      z,Units.val_mk0,pow_zero,RingAut.one_apply]
    have hw0 : (x+y)^d ≠ 0 := pow_ne_zero _ (by simpa using sum_ne_zero σ x y hx hy 0 0)
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

end Erdos714AffinePowerGrid
#print axioms Erdos714AffinePowerGrid.flat_orbit
#print axioms Erdos714AffinePowerGrid.affineCopy
