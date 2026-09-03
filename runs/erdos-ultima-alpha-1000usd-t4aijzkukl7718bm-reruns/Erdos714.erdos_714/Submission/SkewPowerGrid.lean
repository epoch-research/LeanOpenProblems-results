import Submission.CyclotomicSubfield

/-! Skew subfield orbits in power graphs. These are construction obstructions,
not a proof or disproof of Erdős714. -/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714SkewPowerGrid
variable {E : Type*} [Field E]

lemma skew_iterate (σ : E ≃+* E) (k : ℕ) (x : E) (hx : (σ^k) x = -x)
    (n m : ℕ) : (σ^(k*n+m)) x = (-1)^n*(σ^m) x := by
  have hn (n : ℕ) : (σ^(k*n)) x = (-1)^n*x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ,pow_add,RingAut.mul_apply,hx,map_neg,ih,pow_succ]
      ring
  rw [show k*n+m=m+k*n by omega,pow_add,RingAut.mul_apply,hn,map_mul,map_pow,map_neg,map_one]

lemma sum_orbit (σ : E ≃+* E) (x y : E)
    (hx : (σ^2) x = -x) (hy : (σ^3) y = -y) (i j : ℕ) :
    (σ^(3*i+10*j)) (x+y) = (-1)^(i+j)*((σ^i) x+(σ^j) y) := by
  rw [map_add]
  have hx' := skew_iterate σ 2 x hx (i+5*j) i
  have hy' := skew_iterate σ 3 y hy (i+3*j) j
  have hix : 2*(i+5*j)+i=3*i+10*j := by omega
  have hiy : 3*(i+3*j)+j=3*i+10*j := by omega
  rw [hix] at hx'
  rw [hiy] at hy'
  rw [hx',hy']
  have hsx : (-1 : E)^(i+5*j)=(-1)^(i+j) := by
    rw [show i+5*j=i+j+4*j by omega,pow_add,pow_mul]
    norm_num
  have hsy : (-1 : E)^(i+3*j)=(-1)^(i+j) := by
    rw [show i+3*j=i+j+2*j by omega,pow_add,pow_mul]
    norm_num
  rw [hsx,hsy]
  ring

lemma frobenius_iterate (σ : E ≃+* E) (q : ℕ) (hσ : ∀ z, σ z=z^q)
    (n : ℕ) (z : E) : (σ^n) z=z^(q^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',RingAut.mul_apply,hσ,ih,pow_succ,pow_mul]

lemma power_orbit (σ : E ≃+* E) (q d : ℕ) (hσ : ∀ z, σ z=z^q)
    (x y : E) (hx : (σ^2) x = -x) (hy : (σ^3) y = -y) (i j : ℕ) :
    ((σ^i) x+(σ^j) y)^d = ((-1)^d)^(i+j)*((x+y)^d)^(q^(3*i+10*j)) := by
  have h := sum_orbit σ x y hx hy i j
  have he : (σ^i) x+(σ^j) y = (-1)^(i+j)*(σ^(3*i+10*j)) (x+y) := by
    rw [h,←mul_assoc,←pow_two]
    have hs : ((-1 : E)^(i+j))^2=1 := by rw [←pow_mul,Nat.mul_comm,pow_mul]; norm_num
    rw [hs,one_mul]
  rw [he,mul_pow,frobenius_iterate σ q hσ]
  simp only [←pow_mul]
  congr 1 <;> congr 1 <;> ring

/-- The weight modulus needed for flatness of the skew orbit rectangle. -/
def modulus (q : ℕ) : ℕ := 2*(q^3-1)*(q+1)

lemma modulus_divides (q : ℕ) (hq : Odd q) (i j : ℕ) :
    modulus q ∣ (q^(3*i)-1)*(q^(10*j)-1) := by
  obtain ⟨k,rfl⟩ := hq
  have hb : modulus (2*k+1) ∣ ((2*k+1)^3-1)*((2*k+1)^2-1) := by
    refine ⟨k,?_⟩
    have h₃ : (2*k+1)^3-1=8*k^3+12*k^2+6*k := by
      have h : (2*k+1)^3=8*k^3+12*k^2+6*k+1 := by ring
      omega
    have h₂ : (2*k+1)^2-1=4*k^2+4*k := by
      have h : (2*k+1)^2=4*k^2+4*k+1 := by ring
      omega
    rw [modulus,h₃,h₂]
    ring
  apply hb.trans
  apply Nat.mul_dvd_mul
  · exact Nat.pow_sub_one_dvd_pow_sub_one _ ⟨i,rfl⟩
  · exact Nat.pow_sub_one_dvd_pow_sub_one _ ⟨5*j,by omega⟩

lemma flat_power (q : ℕ) (hq : Odd q) (w : E) (hw : w^(modulus q)=1) (i j : ℕ) :
    w^(q^(3*i+10*j))*w = w^(q^(3*i))*w^(q^(10*j)) := by
  have hq1 : 1 ≤ q := hq.pos
  have ha : 1 ≤ q^(3*i) := Nat.one_le_pow _ _ hq1
  have hb : 1 ≤ q^(10*j) := Nat.one_le_pow _ _ hq1
  have hp : w^((q^(3*i)-1)*(q^(10*j)-1))=1 := by
    obtain ⟨k,hk⟩ := modulus_divides q hq i j
    rw [hk,pow_mul,hw,one_pow]
  have hn : q^(3*i)*q^(10*j)+1 =
      (q^(3*i)-1)*(q^(10*j)-1)+(q^(3*i)+q^(10*j)) := by
    have ha' : q^(3*i)-1+1=q^(3*i) := Nat.sub_add_cancel ha
    have hb' : q^(10*j)-1+1=q^(10*j) := Nat.sub_add_cancel hb
    nlinarith
  rw [pow_add,←pow_succ,hn,pow_add,hp,one_mul,pow_add]

/-- Every entry of the entire four-by-six orbit rectangle factors by its
row and column, provided the one initial weight has the stated order. -/
theorem flat_orbit (σ : E ≃+* E) (q d : ℕ) (hq : Odd q)
    (hσ : ∀ z, σ z=z^q) (x y : E)
    (hx : (σ^2) x = -x) (hy : (σ^3) y = -y)
    (hw : ((x+y)^d)^(modulus q)=1) (i j : ℕ) :
    ((σ^i) x+(σ^j) y)^d * (x+y)^d =
      ((σ^i) x+y)^d * (x+(σ^j) y)^d := by
  have h := flat_power q hq ((x+y)^d) hw i j
  have hi := power_orbit σ q d hσ x y hx hy i 0
  have hj := power_orbit σ q d hσ x y hx hy 0 j
  simp only [mul_zero,add_zero,zero_add,pow_zero,RingAut.one_apply] at hi hj
  rw [power_orbit σ q d hσ x y hx hy i j,hi,hj,pow_add]
  linear_combination ((-1 : E)^d)^i*((-1 : E)^d)^j*h

lemma sum_ne_zero (σ : E ≃+* E) (x y : E) (h₂ : (2 : E) ≠ 0)
    (hx0 : x ≠ 0) (hx : (σ^2) x = -x) (hy : (σ^3) y = -y) (i j : ℕ) :
    (σ^i) x+(σ^j) y ≠ 0 := by
  have hx6 : (σ^6) ((σ^i) x) = -(σ^i) x := by
    have h := skew_iterate σ 2 x hx 3 i
    norm_num [pow_add,RingAut.mul_apply] at h ⊢
    exact h
  have hy6 : (σ^6) ((σ^j) y) = (σ^j) y := by
    simpa [pow_add,RingAut.mul_apply] using skew_iterate σ 3 y hy 2 j
  intro he
  have he' := congrArg (fun z : E => (σ^6) z) he
  dsimp only at he'
  rw [map_add,map_zero,hx6,hy6] at he'
  have hzero : (2 : E)*(σ^i) x = 0 := by linear_combination he-he'
  have hx' : (σ^i) x ≠ 0 := by simpa only [map_ne_zero] using hx0
  exact mul_ne_zero h₂ hx' hzero

lemma orbit_injective_of_period (σ : E ≃+* E) (x : E) {n : ℕ}
    (hn : Function.minimalPeriod σ x=n) :
    Function.Injective (fun i : Fin n => (σ^i.val) x) := by
  intro i j he
  apply Fin.ext
  apply Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := x)
  · simpa only [Set.mem_Iio,hn] using i.isLt
  · simpa only [Set.mem_Iio,hn] using j.isLt
  · simpa only [RingAut.coe_pow] using he

lemma orbit_four (σ : E ≃+* E) (x : E) (h₂ : (2 : E) ≠ 0)
    (hx0 : x ≠ 0) (hx : (σ^2) x = -x) :
    Function.Injective (fun i : Fin 4 => (σ^i.val) x) := by
  have hp : Function.IsPeriodicPt σ 4 x := by
    have h := skew_iterate σ 2 x hx 2 0
    simpa [RingAut.coe_pow] using h
  have hn : ¬Function.IsPeriodicPt σ 2 x := by
    intro h
    have he : (σ^2) x=x := h
    rw [hx] at he
    exact mul_ne_zero h₂ hx0 (by linear_combination -he)
  have hm := Function.minimalPeriod_eq_prime_pow (p := 2) (k := 1) hn hp
  exact orbit_injective_of_period σ x hm

lemma orbit_six (σ : E ≃+* E) (y : E) (h₂ : (2 : E) ≠ 0)
    (hy0 : y ≠ 0) (hy : (σ^3) y = -y) (hy2 : (σ^2) y ≠ y) :
    Function.Injective (fun i : Fin 6 => (σ^i.val) y) := by
  have hp : Function.IsPeriodicPt σ 6 y := by
    have h := skew_iterate σ 3 y hy 2 0
    simpa [RingAut.coe_pow] using h
  have hn2 : ¬Function.IsPeriodicPt σ 2 y := hy2
  have hn3 : ¬Function.IsPeriodicPt σ 3 y := by
    intro h
    have he : (σ^3) y=y := h
    rw [hy] at he
    exact mul_ne_zero h₂ hy0 (by linear_combination -he)
  have hd := hp.minimalPeriod_dvd
  have hc : Function.minimalPeriod σ y ∈ (6 : ℕ).divisors :=
    Nat.mem_divisors.mpr ⟨hd,by decide⟩
  have hm : Function.minimalPeriod σ y=6 := by
    have hv : (6 : ℕ).divisors = {1,2,3,6} := by decide
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

/-- An actual power-graph K4,6, with all weights in the actual power image. -/
def skewCopy (σ : E ≃+* E) (q d : ℕ) (hq : Odd q)
    (hσ : ∀ z, σ z=z^q) (h₂ : (2 : E) ≠ 0) (x y : E)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : (σ^2) x = -x) (hy : (σ^3) y = -y)
    (hy2 : (σ^2) y ≠ y) (hw : ((x+y)^d)^(modulus q)=1) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 6))
      (Erdos714WeightedPower.graph (Erdos714WeightedPower.powerMap E d)) := by
  let ν := Erdos714WeightedPower.powerMap E d
  let z (i j : ℕ) : Eˣ := Units.mk0 ((σ^i) x+(σ^j) y)
    (sum_ne_zero σ x y h₂ hx0 hx hy i j)
  let L : Fin 4 ↪ E × Erdos714WeightedPower.Weight E d :=
    ⟨fun i => ((σ^i.val) x,ν (z i.val 0)/ν (z 0 0)), by
      intro i j he
      exact orbit_four σ x h₂ hx0 hx (congrArg Prod.fst he)⟩
  let R : Fin 6 ↪ E × Erdos714WeightedPower.Weight E d :=
    ⟨fun j => ((σ^j.val) y,ν (z 0 j.val)), by
      intro i j he
      exact orbit_six σ y h₂ hy0 hy hy2 (congrArg Prod.fst he)⟩
  have he (i : Fin 4) (j : Fin 6) : Erdos714WeightedPower.relation ν (L i) (R j) := by
    refine ⟨z i.val j.val,rfl,?_⟩
    apply Subtype.ext
    apply Units.ext
    change ((z i.val j.val)^d : Eˣ).val =
      (((z i.val 0)^d/(z 0 0)^d)*(z 0 j.val)^d : Eˣ).val
    simp only [Units.val_mul,Units.val_div_eq_div_val,Units.val_pow_eq_pow_val,
      z,Units.val_mk0,pow_zero,RingAut.one_apply]
    have hw0 : (x+y)^d ≠ 0 := pow_ne_zero _ (by
      simpa using sum_ne_zero σ x y h₂ hx0 hx hy 0 0)
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

theorem not_free_of_skew (σ : E ≃+* E) (q d : ℕ) (hq : Odd q)
    (hσ : ∀ z, σ z=z^q) (h₂ : (2 : E) ≠ 0) (x y : E)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : (σ^2) x = -x) (hy : (σ^3) y = -y)
    (hy2 : (σ^2) y ≠ y) (hw : ((x+y)^d)^(modulus q)=1) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714WeightedPower.graph (Erdos714WeightedPower.powerMap E d)) := by
  let e := (Function.Embedding.refl (Fin 4)).sumMap (Fin.castLEEmb (by decide : 4 ≤ 6))
  let c : Copy (completeBipartiteGraph (Fin 4) (Fin 4))
      (completeBipartiteGraph (Fin 4) (Fin 6)) :=
    ⟨⟨e,by intro a b h; cases a <;> cases b <;> simp_all [e]⟩,e.injective⟩
  intro hf
  exact hf ⟨(skewCopy σ q d hq hσ h₂ x y hx0 hy0 hx hy hy2 hw).comp c⟩

end Erdos714SkewPowerGrid
#print axioms Erdos714SkewPowerGrid.flat_orbit

#print axioms Erdos714SkewPowerGrid.skewCopy
#print axioms Erdos714SkewPowerGrid.not_free_of_skew
