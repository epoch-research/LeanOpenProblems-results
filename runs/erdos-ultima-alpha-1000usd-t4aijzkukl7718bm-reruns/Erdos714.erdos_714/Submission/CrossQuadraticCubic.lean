import Submission.ConsecutiveSquares
import Submission.BinaryConicPoints
import Submission.UniformSquarePointNorm

/-! A translated-circle obstruction to a cross-paired quadratic/cubic model.
This auxiliary file does not settle Erdős714. -/
noncomputable section
open Classical Finset SimpleGraph Polynomial
set_option maxHeartbeats 3000000
namespace Erdos714CrossQuadraticCubic
variable {F : Type*} [Field F] [CharP F 3]

abbrev Point (F : Type*) := (F × F) × (F × F)
def Q (u : F × F) : F := u.1^2+u.2^2
def C (v : F × F) : F := v.1^3-v.1*v.2^2-v.2^3
def pairing (x y : Point F) : F :=
  x.1.1*y.2.1+x.1.2*y.2.2+x.2.1*y.1.1+x.2.2*y.1.2
def Allowed (x : Point F) : Prop := Q x.1 ≠ 0 ∧ C x.2 ≠ 0 ∧ IsSquare (C x.2)
abbrev Vertex (F : Type*) [Field F] := {x : Point F // Allowed x}
def graph : SimpleGraph (Bool × Vertex F) where
  Adj x y := x.1 ≠ y.1 ∧ pairing x.2.val y.2.val =
    Q x.2.val.1*Q y.2.val.1+C x.2.val.2*C y.2.val.2+1
  symm := by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    have hp : pairing y.2.val x.2.val=pairing x.2.val y.2.val := by unfold pairing; ring
    rw [hp,h.2]
    ring
  loopless := by intro x h; exact h.1 rfl

lemma two_ne_zero : (2 : F) ≠ 0 := by
  intro h
  have h3 : (3 : F)=0 := CharP.cast_eq_zero F 3
  have : (1 : F)=0 := by linear_combination h3-h
  exact one_ne_zero this

omit [CharP F 3] in
lemma Q_zero (hns : ¬ IsSquare (-1 : F)) (u : F × F) (h : Q u=0) : u=0 := by
  by_cases hy : u.2=0
  · have hx : u.1=0 := by
      have hsq : u.1^2=0 := by simpa [Q,hy] using h
      exact eq_zero_of_pow_eq_zero hsq
    exact Prod.ext hx hy
  · apply False.elim
    apply hns
    refine ⟨u.1/u.2,?_⟩
    rw [← pow_two,div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hy)).mpr
    change -1*u.2^2=u.1^2
    dsimp [Q] at h
    linear_combination -h

omit [CharP F 3] in
lemma C_zero (hAS : ∀ z : F, z^3-z ≠ 1) (v : F × F) (h : C v=0) : v=0 := by
  by_cases hy : v.2=0
  · have hx : v.1=0 := by
      have hpow : v.1^3=0 := by simpa [C,hy] using h
      exact eq_zero_of_pow_eq_zero hpow
    exact Prod.ext hx hy
  · apply False.elim
    apply hAS (v.1/v.2)
    have he : (v.1/v.2)^3-v.1/v.2=(v.1^3-v.1*v.2^2)/v.2^3 := by field_simp
    rw [he]
    dsimp [C] at h
    apply (div_eq_iff (pow_ne_zero 3 hy)).mpr
    linear_combination h

lemma root_equations (A B : F) (h : A*B*(A+B)=1) :
    A^3- (A-B)^2*A+1=0 ∧ B^3-(A-B)^2*B+1=0 := by
  constructor
  · linear_combination (norm := ring_nf) -h
    reduce_mod_char!
  · linear_combination (norm := ring_nf) -h
    reduce_mod_char!

lemma radius_ne_zero (hAS : ∀ z : F, z^3-z ≠ 1) (A B : F)
    (h : A*B*(A+B)=1) : 1-(A-B)^2 ≠ 0 := by
  intro hz
  have he := (root_equations A B h).1
  have hsq : (A-B)^2=1 := by linear_combination -hz
  rw [hsq,one_mul] at he
  apply hAS (-A)
  linear_combination -he

variable [Fintype F]

/-- A square pair giving the required two distinct quadratic roots. -/
theorem exists_parameters (hns : ¬ IsSquare (-1 : F)) (hq : 3<Fintype.card F) :
    ∃ A B : F, A ≠ 0 ∧ B ≠ 0 ∧ A ≠ B ∧ IsSquare A ∧ IsSquare B ∧ A*B*(A+B)=1 := by
  obtain ⟨t,ht0,htm,htp,hts,_,htps⟩ := Erdos714ConsecutiveSquares.exists_three_squares hns hq
  have ht1 : t ≠ 1 := fun h => htm (by rw [h,sub_self])
  obtain ⟨r,hr⟩ := (hts.mul htps).inv
  have hden : t*(t+1) ≠ 0 := mul_ne_zero ht0 htp
  have hr0 : r ≠ 0 := by
    intro h
    rw [h,mul_zero] at hr
    exact inv_ne_zero hden hr
  obtain ⟨a,ha⟩ := surjective_frobenius F 3 r
  change a^3=r at ha
  have ha0 : a ≠ 0 := by intro h; rw [h,zero_pow (by decide)] at ha; exact hr0 ha.symm
  let A := a^2
  have hA0 : A ≠ 0 := pow_ne_zero 2 ha0
  have hA3 : A^3=(t*(t+1))⁻¹ := by
    dsimp [A]
    rw [show (a^2)^3=(a^3)*(a^3) by ring,ha]
    exact hr.symm
  refine ⟨A,t*A,hA0,mul_ne_zero ht0 hA0,?_,IsSquare.sq a,hts.mul (IsSquare.sq a),?_⟩
  · intro h
    apply ht1
    exact (mul_right_cancel₀ hA0 (show t*A=1*A by simpa using h.symm))
  · calc
      A*(t*A)*(A+t*A) = A^3*(t*(t+1)) := by ring
      _ = 1 := by rw [hA3,inv_mul_cancel₀ hden]

/-- A translated circle supplies a full field's worth of row points. -/
theorem circle_rows (hns : ¬ IsSquare (-1 : F)) (k : F) (hk : k+1 ≠ 0) :
    ∃ f : F ↪ F × F, ∀ t, Q (f t)+(f t).2=k := by
  obtain ⟨p,hp⟩ := Erdos714BinaryConic.exists_pair (F := F) two_ne_zero
    (δ := -1) (γ := k+1) (neg_ne_zero.mpr one_ne_zero)
  have hd (t : F) : 1-(-1)*t^2 ≠ 0 := by
    intro h
    apply hns
    refine ⟨t,?_⟩
    linear_combination -h
  let w (t : F) := Erdos714BinaryConic.transport (-1) p
    (Erdos714BinaryConic.circlePoint (-1) t)
  have hw (t : F) : Erdos714BinaryConic.normPair (-1) (w t)=k+1 := by
    dsimp [w]
    rw [Erdos714BinaryConic.transport_norm,Erdos714BinaryConic.circlePoint_norm _ _ (hd t),hp,mul_one]
  have hi : Function.Injective w := by
    intro x y h
    have he := Erdos714BinaryConic.transport_injective (show Erdos714BinaryConic.normPair (-1) p ≠ 0 by
      rw [hp]; exact hk) h
    have hh := congrArg (fun v : F × F => v.2/(v.1+1)) he
    simpa only [Erdos714BinaryConic.circlePoint_recover two_ne_zero _ _ (hd x),
      Erdos714BinaryConic.circlePoint_recover two_ne_zero _ _ (hd y)] using hh
  let f : F ↪ F × F := ⟨fun t => ((w t).1,(w t).2+1),by
    intro x y h
    apply hi
    apply Prod.ext
    · simpa only using congrArg Prod.fst h
    · exact add_right_cancel (congrArg Prod.snd h)⟩
  refine ⟨f,?_⟩
  intro t
  have h := hw t
  dsimp only [Erdos714BinaryConic.normPair] at h
  change (w t).1^2+((w t).2+1)^2+((w t).2+1)=k
  linear_combination (norm := ring_nf) h
  reduce_mod_char!

omit [Fintype F] [CharP F 3] in
lemma row_allowed (hns : ¬ IsSquare (-1 : F)) (k : F) (hk : k ≠ 0)
    (u : F × F) (hu : Q u+u.2=k) : Allowed (u,(1,0)) := by
  refine ⟨?_,by norm_num [C],?_⟩
  · intro h
    have hz := Q_zero hns u h
    rw [hz] at hu
    exact hk (by simpa [Q] using hu.symm)
  · exact ⟨1,by norm_num [C]⟩

omit [Fintype F] [CharP F 3] in
lemma col_allowed (s : F) (hs : s ≠ 0) : Allowed ((0,s),(0,-s^2)) := by
  refine ⟨by simpa [Q] using pow_ne_zero 2 hs,?_,?_⟩
  · simpa [C] using pow_ne_zero 6 hs
  · refine ⟨s^3,?_⟩
    dsimp [C]
    ring

omit [Fintype F] [CharP F 3] in
lemma circle_edge (k s : F) (u : F × F) (hu : Q u+u.2=k)
    (hs : s^6+k*s^2+1=0) :
    pairing (u,(1,0)) ((0,s),(0,-s^2)) =
      Q u*Q (0,s)+C (1,0)*C (0,-s^2)+1 := by
  dsimp [pairing,Q,C] at hu hs ⊢
  linear_combination -hs-s^2*hu

/-- The four columns and translated-circle rows satisfy the original cross
pairing, including both nonvanishing guards and the cubic square guard. -/
theorem not_free (hns : ¬ IsSquare (-1 : F)) (hAS : ∀ z : F, z^3-z ≠ 1)
    (hq : 3<Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F)) := by
  obtain ⟨A,B,hA,hB,hAB,hAs,hBs,hprod⟩ := exists_parameters hns hq
  obtain ⟨s,hs⟩ := hAs
  obtain ⟨t,ht⟩ := hBs
  have hs2 : s^2=A := by simpa only [pow_two] using hs.symm
  have ht2 : t^2=B := by simpa only [pow_two] using ht.symm
  have hs0 : s ≠ 0 := by intro h; exact hA (by simpa [h] using hs)
  have ht0 : t ≠ 0 := by intro h; exact hB (by simpa [h] using ht)
  have hst : s ≠ t := by intro h; exact hAB (by rw [hs,ht,h])
  have hst' : s ≠ -t := by intro h; apply hAB; rw [← hs2,← ht2,h,neg_sq]
  have hts' : t ≠ -s := by
    intro h
    exact hst' (by rw [h,neg_neg])
  have hsneg : s ≠ -s := by
    intro h
    apply hs0
    apply (mul_eq_zero.mp (show (2 : F)*s=0 by linear_combination h)).resolve_left two_ne_zero
  have htneg : t ≠ -t := by
    intro h
    apply ht0
    apply (mul_eq_zero.mp (show (2 : F)*t=0 by linear_combination h)).resolve_left two_ne_zero
  let p : Fin 4 → F := ![s,-s,t,-t]
  have hp : Function.Injective p := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [p,hsneg,htneg,hst,hst',Ne.symm hsneg,Ne.symm htneg,Ne.symm hst,
        Ne.symm hst',hts',neg_eq_iff_eq_neg] at h ⊢
  have hp0 (i : Fin 4) : p i ≠ 0 := by fin_cases i <;> simp [p,hs0,ht0]
  let k := -(A-B)^2
  have hk0 : k ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr hAB))
  have hk1 : k+1 ≠ 0 := by
    convert radius_ne_zero hAS A B hprod using 1
    dsimp [k]
    ring
  have hsroot : s^6+k*s^2+1=0 := by
    rw [show s^6=(s^2)^3 by ring,hs2]
    simpa [k,sub_eq_add_neg] using (root_equations A B hprod).1
  have htroot : t^6+k*t^2+1=0 := by
    rw [show t^6=(t^2)^3 by ring,ht2]
    simpa [k,sub_eq_add_neg] using (root_equations A B hprod).2
  have hproot (i : Fin 4) : (p i)^6+k*(p i)^2+1=0 := by
    fin_cases i
    · exact hsroot
    · change (-s)^6+k*(-s)^2+1=0
      simpa only [show (-s)^6=s^6 by ring,neg_sq] using hsroot
    · exact htroot
    · change (-t)^6+k*(-t)^2+1=0
      simpa only [show (-t)^6=t^6 by ring,neg_sq] using htroot
  obtain ⟨f,hf⟩ := circle_rows hns k hk1
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := F)
    (by simpa only [Fintype.card_fin] using (show 4≤Fintype.card F by omega))
  let L (i : Fin 4) : Bool × Vertex F :=
    (false,⟨(f (e i),(1,0)),row_allowed hns k hk0 _ (hf _)⟩)
  let R (i : Fin 4) : Bool × Vertex F :=
    (true,⟨((0,p i),(0,-(p i)^2)),col_allowed _ (hp0 i)⟩)
  have hL : Function.Injective L := by
    intro i j h
    exact e.injective (f.injective (congrArg (fun z : Bool × Vertex F => z.2.val.1) h))
  have hR : Function.Injective R := by
    intro i j h
    exact hp (congrArg (fun z : Bool × Vertex F => z.2.val.1.2) h)
  have he (i j : Fin 4) : (graph (F := F)).Adj (L i) (R j) :=
    ⟨Bool.false_ne_true,circle_edge k _ _ (hf _) (hproot j)⟩
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim L R,?_⟩,?_⟩⟩
  · intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => simp at h
      | inr j => exact he i j
    | inr i =>
      cases j with
      | inl j => exact (he j i).symm
      | inr j => simp at h
  · intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hL h)
      | inr j => exact False.elim (Bool.false_ne_true (congrArg Prod.fst h))
    | inr i =>
      cases j with
      | inl j => exact False.elim (Bool.false_ne_true (congrArg Prod.fst h).symm)
      | inr j => exact congrArg Sum.inr (hR h)

/-- The hypotheses hold along an explicit unbounded sequence of odd-degree
fields where the binary cubic is genuinely anisotropic. -/
theorem not_free_six_k_five (k : ℕ) (hcard : Fintype.card F=3^(6*k+5)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F)) := by
  apply not_free
  · rw [FiniteField.isSquare_neg_one_iff,hcard]
    have he : 6*k+5=2*(3*k+2)+1 := by omega
    simp [he,pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
  · intro z hz
    have h := Erdos714UniformSquarePoints.artinSchreier_iteration z hz (6*k+5)
    have hp : z^(3^(6*k+5))=z := by rw [← hcard]; exact FiniteField.pow_card z
    have hm : ((6*k+5 : ℕ) : F)=0 := by linear_combination hp-h
    have hd := (CharP.cast_eq_zero_iff F 3 (6*k+5)).mp hm
    omega
  · rw [hcard]
    exact lt_of_lt_of_le (by decide : 3<(3:ℕ)^5)
      (Nat.pow_le_pow_right (by decide) (by omega))

end Erdos714CrossQuadraticCubic
#print axioms Erdos714CrossQuadraticCubic.Q_zero
#print axioms Erdos714CrossQuadraticCubic.C_zero
#print axioms Erdos714CrossQuadraticCubic.exists_parameters
#print axioms Erdos714CrossQuadraticCubic.circle_rows
#print axioms Erdos714CrossQuadraticCubic.circle_edge
#print axioms Erdos714CrossQuadraticCubic.not_free
#print axioms Erdos714CrossQuadraticCubic.not_free_six_k_five
