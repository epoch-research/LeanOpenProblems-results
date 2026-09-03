import Submission.AdditiveCoding
import Submission.TwistedQuadraticProduct

/-! Multiplicative point codes with an even part plus an additive part
cannot realize the fourth-case critical parameters in characteristic three.
This excludes a construction family, not arbitrary K44-free graphs. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 6000000
namespace Erdos714EvenAdditiveProduct
variable {E F : Type*} [Field E] [Field F] [Fintype E] [Fintype F]

def kernelFin (L : E →+ F) : Finset E := univ.filter (fun x => L x=0)
def jointFin (L : E →+ F) (b : E) : Finset E :=
  univ.filter (fun x => L x=0 ∧ L (b*x)=0)

omit [Fintype F] in
lemma zero_mem_kernel (L : E →+ F) : 0 ∈ kernelFin L := by simp [kernelFin]
omit [Fintype F] in
lemma zero_mem_joint (L : E →+ F) (b : E) : 0 ∈ jointFin L b := by simp [jointFin]

omit [Fintype F] in
lemma joint_sum (L : E →+ F) :
    (∑ b, (jointFin L b).card) = Fintype.card E +
      ((kernelFin L).card-1)*(kernelFin L).card := by
  have hx (x : E) (hx0 : x ≠ 0) :
      (univ.filter (fun b => L (b*x)=0)).card = (kernelFin L).card := by
    apply card_equiv (Equiv.mulRight₀ x hx0)
    intro b
    simp [kernelFin]
  have he : (∑ b, (jointFin L b).card) =
      ∑ x, (univ.filter (fun b => L x=0 ∧ L (b*x)=0)).card := by
    simp only [jointFin,card_filter]
    rw [sum_comm]
  have hp (x : E) : (univ.filter (fun b => L x=0 ∧ L (b*x)=0)).card =
      (if x=0 then Fintype.card E else 0) +
      (if x ∈ (kernelFin L).erase 0 then (kernelFin L).card else 0) := by
    by_cases hx0 : x=0
    · subst x
      simp
    · by_cases hL : L x=0
      · simp only [hL,true_and]
        rw [hx x hx0]
        simp [hx0,kernelFin,hL]
      · simp [hL,hx0,kernelFin]
  rw [he]
  simp_rw [hp]
  rw [sum_add_distrib]
  simp only [sum_ite_eq',mem_univ,ite_true]
  rw [sum_ite_mem,univ_inter]
  simp only [sum_const,smul_eq_mul,card_erase_of_mem (zero_mem_kernel L)]

/-- Some nontrivial scalar multiple has an unusually large joint kernel. -/
lemma exists_large_joint (L : E →+ F) (q : ℕ) (hq : 5 ≤ q)
    (hF : Fintype.card F=q) (hE : Fintype.card E=q^3) :
    ∃ b : E, b ≠ 0 ∧ b ≠ 1 ∧ b ≠ -1 ∧ q < (jointFin L b).card := by
  let K := (kernelFin L).card
  have hK : q^2 ≤ K := by
    have h := Erdos714AdditiveCoding.card_le_alphabet_mul_kernel L
    rw [hF,hE] at h
    have hh : q*q^2 ≤ q*K := by simpa [K,kernelFin,pow_succ,mul_comm] using h
    exact Nat.le_of_mul_le_mul_left hh (by omega)
  by_contra! hn
  have hp (b : E) : (jointFin L b).card ≤
      q + if b ∈ ({0,1,-1} : Finset E) then K else 0 := by
    by_cases hb : b ∈ ({0,1,-1} : Finset E)
    · have hs : jointFin L b ⊆ kernelFin L := by
        intro x hx
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2.1⟩
      have hh := card_le_card hs
      simp only [hb,ite_true]
      omega
    · have hb' : b ≠ 0 ∧ b ≠ 1 ∧ b ≠ -1 := by simpa using hb
      have hh := hn b hb'.1 hb'.2.1 hb'.2.2
      simpa only [hb,ite_false,add_zero] using hh
  have hcard : ({0,1,-1} : Finset E).card ≤ 3 := by
    have h := card_insert_le (0 : E) {1,-1}
    have hh : ({1,-1} : Finset E).card ≤ 2 := card_le_two
    omega
  have hsum : (∑ b, (jointFin L b).card) ≤ Fintype.card E*q+3*K := by
    calc
      _ ≤ ∑ b, (q + if b ∈ ({0,1,-1} : Finset E) then K else 0) :=
        sum_le_sum (fun b _ => hp b)
      _ = Fintype.card E*q+({0,1,-1} : Finset E).card*K := by
        rw [sum_add_distrib,sum_ite_mem,univ_inter]
        simp
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right K hcard) _
  rw [joint_sum,hE] at hsum
  change q^3+(K-1)*K ≤ q^3*q+3*K at hsum
  have hk1 : 1 ≤ K := by nlinarith
  have hk4 : 4 ≤ K := by nlinarith
  have heK : K-1+1=K := Nat.sub_add_cancel hk1
  have hpos : 0 ≤ (K-q^2)*(K+q^2-4) := Nat.zero_le _
  have hsubK : K-q^2+q^2=K := Nat.sub_add_cancel hK
  have hsub4 : K+q^2-4+4=K+q^2 := Nat.sub_add_cancel (by omega)
  have hlower : q^4-4*q^2 ≤ K^2-4*K := by nlinarith
  have hq2 : 4*q^2 ≤ q^4 := by nlinarith [Nat.mul_le_mul_left (q^2) (show 4 ≤ q^2 by nlinarith)]
  have hK2 : 4*K ≤ K^2 := by nlinarith
  have hs1 := Nat.sub_add_cancel hq2
  have hs2 := Nat.sub_add_cancel hK2
  nlinarith [Nat.mul_le_mul_left (q^2) hq]

variable [CharP E 3] [CharP F 3]
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

def jointSubgroup (L : E →+ F) (b : E) : AddSubgroup E where
  carrier := {x | L x=0 ∧ L (b*x)=0}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx,hbx⟩ ⟨hy,hby⟩
    simp [mul_add,map_add,hx,hbx,hy,hby]
  neg_mem' := by
    rintro x ⟨hx,hbx⟩
    simp [hx,hbx]

omit [Fintype F] [CharP F 3] in
lemma joint_card_power (L : E →+ F) (b : E) :
    ∃ k : ℕ, (jointFin L b).card=3^k := by
  letI : Algebra (ZMod 3) E := ZMod.algebra E 3
  let P : Submodule (ZMod 3) E := AddSubgroup.toZModSubmodule 3 (jointSubgroup L b)
  letI : Fintype P := Fintype.ofFinite P
  refine ⟨Module.finrank (ZMod 3) P,?_⟩
  have hh := Module.card_eq_pow_finrank (K := ZMod 3) (V := P)
  have hc : Fintype.card P=(jointFin L b).card := by
    simp only [Fintype.card_subtype,jointFin,P,AddSubgroup.mem_toZModSubmodule]
    congr 1
    ext x
    simp [jointSubgroup]
  rw [hc] at hh
  simpa only [ZMod.card] using hh

lemma joint_card_gap (L : E →+ F) (b : E)
    (h : Fintype.card F < (jointFin L b).card) :
    3*Fintype.card F ≤ (jointFin L b).card := by
  obtain ⟨m,_,hm⟩ := FiniteField.card F 3
  obtain ⟨k,hk⟩ := joint_card_power L b
  have hmk : (m : ℕ)<k := by
    by_contra hn
    have hp : 3^k ≤ 3^(m : ℕ) := pow_le_pow_right' (by decide) (by omega)
    omega
  rw [hm,hk]
  calc
    3*3^(m : ℕ) = 3^((m : ℕ)+1) := by ring
    _ ≤ 3^k := pow_le_pow_right' (by decide) (by omega)

omit [Fintype E] in
lemma ne_neg_of_ne_zero {x : E} (hx : x ≠ 0) : x ≠ -x := by
  intro h
  have h3 : (3 : E)=0 := CharP.cast_eq_zero E 3
  apply hx
  linear_combination x*h3-h

omit [Fintype E] in
/-- A nonzero, negation-closed set containing more than two points
contains four distinct points. -/
lemma four_of_neg_closed (S : Finset E) (h0 : 0 ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) (hc : 2 < S.card) :
    ∃ f : Fin 4 ↪ E, ∀ i, f i ∈ S := by
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < S.card)
  have hx0 : x ≠ 0 := by intro h; subst x; exact h0 hx
  have hxneg := ne_neg_of_ne_zero hx0
  have hn : ¬ S ⊆ {x,-x} := by
    intro hs
    have hh := (card_le_card hs).trans (card_le_two (a := x) (b := -x))
    omega
  obtain ⟨y,hy,hy'⟩ := not_subset.mp hn
  have hy0 : y ≠ 0 := by intro h; subst y; exact h0 hy
  have hyneg := ne_neg_of_ne_zero hy0
  have hya : y ≠ x ∧ y ≠ -x := by simpa using hy'
  have hxy : x ≠ y := hya.1.symm
  have hnx : -x ≠ y := hya.2.symm
  have hxny : x ≠ -y := by
    intro h
    apply hya.2
    rw [h,neg_neg]
  have hnn : -x ≠ -y := by simpa using hxy
  let f : Fin 4 → E := ![x,-x,y,-y]
  have hi : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f,hxneg,hyneg,hxy,hnx,hxny,hnn,Ne.symm hxneg,Ne.symm hyneg,
        Ne.symm hxy,Ne.symm hnx,Ne.symm hxny,Ne.symm hnn] at hij ⊢
  refine ⟨⟨f,hi⟩,?_⟩
  intro i
  fin_cases i <;> simp only [Function.Embedding.coeFn_mk,f]
  · exact hx
  · exact hneg x hx
  · exact hy
  · exact hneg y hy

def code (Q : E → F) (L : E →+ F) (r : Eˣ × F) (x : Eˣ) : F :=
  Q ((r.1 : E)*(x : E))+L ((r.1 : E)*(x : E))+r.2

def graph (Q : E → F) (L : E →+ F) : SimpleGraph ((Eˣ × F) ⊕ (Eˣ × F)) :=
  Erdos714Coding.graph (code Q L)

omit [Fintype F] [CharP F 3] in
lemma copy_of_joint_fiber (Q : E → F) (hQ : ∀ x, Q (-x)=Q x)
    (L : E →+ F) (b : E) (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hbn : b ≠ -1)
    (t : F) (f : Fin 4 ↪ E)
    (hf : ∀ i, f i ≠ 0 ∧ L (f i)=0 ∧ L (b*f i)=0 ∧ Q (f i)-Q (b*f i)=t) :
    Nonempty (Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph Q L)) := by
  let a : Fin 4 → E := ![1,-1,b,-b]
  let s : Fin 4 → F := ![0,0,t,t]
  have h1neg : (1 : E) ≠ -1 := ne_neg_of_ne_zero one_ne_zero
  have hbneg : b ≠ -b := ne_neg_of_ne_zero hb0
  have hbn1 : -b ≠ 1 := by intro h; apply hbn; rw [← h,neg_neg]
  have hbnn : -b ≠ -1 := by simpa using hb1
  have hai : Function.Injective a := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [a,h1neg,hbneg,hb1,hbn,hbn1,hbnn,Ne.symm h1neg,Ne.symm hbneg,
        Ne.symm hb1,Ne.symm hbn,Ne.symm hbn1,Ne.symm hbnn] at hij ⊢
  have ha0 (i : Fin 4) : a i ≠ 0 := by fin_cases i <;> simp [a,hb0]
  let R : Fin 4 → Eˣ × F := fun i => (Units.mk0 (a i) (ha0 i),s i)
  let C : Fin 4 → Eˣ × F := fun j => (Units.mk0 (f j) (hf j).1,Q (f j))
  have hR : Function.Injective R := by
    intro i j h
    exact hai (congrArg (fun p : Eˣ × F => (p.1 : E)) h)
  have hC : Function.Injective C := by
    intro i j h
    exact f.injective (congrArg (fun p : Eˣ × F => (p.1 : E)) h)
  have he (i j : Fin 4) : code Q L (R i) (C j).1=(C j).2 := by
    have hh := hf j
    fin_cases i <;> dsimp [code,R,C,a,s]
    all_goals simp only [one_mul,neg_mul,map_neg,hQ,hh.2.1,hh.2.2.1,
      neg_zero,add_zero]
    all_goals linear_combination -hh.2.2.2
  let re : Fin 4 ↪ Eˣ × F := ⟨R,hR⟩
  let ce : Fin 4 ↪ Eˣ × F := ⟨C,hC⟩
  refine ⟨⟨⟨re.sumMap ce,?_⟩,(re.sumMap ce).injective⟩⟩
  intro u v huv
  cases u with
  | inl i =>
    cases v with
    | inl j => simp at huv
    | inr j => exact (Erdos714Coding.mem_symbols (code Q L) (R i) (C j).1 (C j).2).mpr (he i j)
  | inr j =>
    cases v with
    | inl i => exact (Erdos714Coding.mem_symbols (code Q L) (R i) (C j).1 (C j).2).mpr (he i j)
    | inr i => simp at huv

/-- This covers arbitrary even functions, not merely quadratic polynomials.
The additive term need not be linear over the alphabet field. -/
theorem not_free (Q : E → F) (hQ : ∀ x, Q (-x)=Q x) (L : E →+ F)
    (hq : 5 ≤ Fintype.card F) (hE : Fintype.card E=(Fintype.card F)^3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph Q L) := by
  obtain ⟨b,hb0,hb1,hbn,hb⟩ := exists_large_joint L (Fintype.card F) hq rfl hE
  have hj := joint_card_gap L b hb
  let T := (jointFin L b).erase 0
  let D : E → F := fun x => Q x-Q (b*x)
  have hT : 2*Fintype.card F < T.card := by
    dsimp [T]
    rw [card_erase_of_mem (zero_mem_joint L b)]
    omega
  have hs : ∃ t : F, 2 < (T.filter (fun x => D x=t)).card := by
    by_contra! hn
    have hh := card_eq_sum_card_fiberwise (s := T) (t := (univ : Finset F))
      (f := D) (fun _ _ => mem_univ _)
    have hu : (∑ t : F, (T.filter (fun x => D x=t)).card) ≤ Fintype.card F*2 := by
      calc
        _ ≤ ∑ _t : F, 2 := sum_le_sum (fun t _ => hn t)
        _ = _ := by simp
    omega
  obtain ⟨t,ht⟩ := hs
  let S := T.filter (fun x => D x=t)
  have hS0 : 0 ∉ S := by simp [S,T]
  have hneg : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have hx' : x ≠ 0 ∧ (L x=0 ∧ L (b*x)=0) ∧ D x=t := by
      simpa [S,T,jointFin,and_assoc] using hx
    have hD : D (-x)=D x := by simp only [D,mul_neg,hQ]
    simp [S,T,jointFin,hx'.1,hx'.2.1.1,hx'.2.1.2,hD,hx'.2.2]
  obtain ⟨f,hf⟩ := four_of_neg_closed S hS0 hneg ht
  intro hfree
  apply hfree
  apply copy_of_joint_fiber Q hQ L b hb0 hb1 hbn t f
  intro i
  have hh := hf i
  simpa [S,T,jointFin,D,and_assoc] using hh

variable [Algebra F E]

def traceLinear (γ : E) (σ : F →+ F) : E →+ F where
  toFun x := Algebra.trace F E x+σ (Algebra.trace F E (γ*x))
  map_zero' := by simp
  map_add' := by intro x y; simp [mul_add,map_add,add_assoc,add_left_comm,add_comm]

/-- No additive Frobenius/trace correction rescues an even multiplicative
point kernel in this full code model. -/
theorem trace_correction_not_free (Q : E → F) (hQ : ∀ x, Q (-x)=Q x)
    (γ : E) (σ : F →+ F) (hq : 5 ≤ Fintype.card F)
    (hdim : Module.finrank F E=3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun (r : Eˣ × F) (x : Eˣ) =>
        Q ((r.1 : E)*(x : E))+Algebra.trace F E ((r.1 : E)*(x : E))+
        σ (Algebra.trace F E (γ*((r.1 : E)*(x : E))))+r.2)) := by
  have hcard : Fintype.card E=(Fintype.card F)^3 := by
    rw [Module.card_eq_pow_finrank (K := F),hdim]
  have h := not_free Q hQ (traceLinear γ σ) hq hcard
  have he : graph Q (traceLinear γ σ) =
      Erdos714Coding.graph (fun (r : Eˣ × F) (x : Eˣ) =>
        Q ((r.1 : E)*(x : E))+Algebra.trace F E ((r.1 : E)*(x : E))+
        σ (Algebra.trace F E (γ*((r.1 : E)*(x : E))))+r.2) := by
    unfold graph
    congr 1
    funext r x
    simp only [code,traceLinear,AddMonoidHom.coe_mk,ZeroHom.coe_mk,add_assoc]
  rwa [he] at h

/-- ALL parameters in the tested trace-quadratic family fail at every
characteristic-three base-field order at least5, not just the two explicit
small-field parameters. -/
theorem all_twisted_quadratic_parameters_not_free (γ : E)
    (hq : 5 ≤ Fintype.card F) (hdim : Module.finrank F E=3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714TwistedQuadraticProduct.graph (F := F) γ) := by
  have h := trace_correction_not_free
    (fun x : E => Algebra.trace F E (x^2)) (by intro x; simp) γ
    (frobenius F 3).toAddMonoidHom hq hdim
  exact h

#print axioms exists_large_joint
#print axioms joint_card_gap
#print axioms not_free
#print axioms trace_correction_not_free
#print axioms all_twisted_quadratic_parameters_not_free
end Erdos714EvenAdditiveProduct
