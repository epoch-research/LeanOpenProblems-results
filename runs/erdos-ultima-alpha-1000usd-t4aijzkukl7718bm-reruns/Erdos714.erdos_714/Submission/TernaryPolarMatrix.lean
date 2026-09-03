import Submission.ConsecutiveSquares

/-! A uniform obstruction to an elliptic semilinear matrix relation.
This is not a proof or disproof of Erdős 714. -/
noncomputable section
open Classical Matrix SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714TernaryPolarMatrix
variable {F : Type*} [Field F] [CharP F 3]
abbrev Mat := Matrix (Fin 2) (Fin 2) F

def sigmaMatrix (σ : F →+* F) (M : Mat (F := F)) : Mat (F := F) :=
  fun i j => σ (M i j)

def value (σ : F →+* F) (X Y : Mat (F := F)) : F :=
  (X+Y).det+(sigmaMatrix σ X*Y+X*sigmaMatrix σ Y).trace

def disc (X : Mat (F := F)) : F := X.trace^2-4*X.det

omit [CharP F 3] in
/-- The guard concerns the actual characteristic polynomial. -/
lemma irreducible_charpoly {M : Mat (F := F)} (hM : ¬IsSquare (disc M)) :
    Irreducible M.charpoly := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [Matrix.charpoly_natDegree_eq_dim]
  · intro x hx
    have h : x^2-M.trace*x+M.det=0 := by
      simpa [Polynomial.IsRoot,Matrix.charpoly_fin_two] using hx
    apply hM
    refine ⟨2*x-M.trace,?_⟩
    dsimp [disc]
    linear_combination -4*h

def graph (σ : F →+* F) : SimpleGraph (Mat (F := F) ⊕ Mat (F := F)) where
  Adj p q := match p,q with
    | .inl X,.inr Y => ¬IsSquare (disc X) ∧ ¬IsSquare (disc Y) ∧ value σ X Y=1
    | .inr Y,.inl X => ¬IsSquare (disc X) ∧ ¬IsSquare (disc Y) ∧ value σ X Y=1
    | _,_ => False
  symm := by intro p q; cases p <;> cases q <;> simp_all
  loopless := by intro p; cases p <;> simp

omit [CharP F 3] in
lemma negative_square (hns : ¬IsSquare (-1:F)) {x : F}
    (hx : x ≠ 0) (hs : IsSquare x) : ¬IsSquare (-x) := by
  intro h
  have hh := h.div hs
  apply hns
  simpa [hx] using hh

omit [CharP F 3] in
lemma negative_square_ne_zero (hns : ¬IsSquare (-1:F)) {x : F}
    (hx : x ≠ 0) (hs : IsSquare (-x)) : ¬IsSquare x := by
  have h := negative_square hns (neg_ne_zero.mpr hx) hs
  simpa using h

/-- The Tits identity makes t ↦ t²/σ(t) invertible on nonzero elements. -/
def twist (σ : F →+* F) (t : F) : F := t^2*σ t

omit [CharP F 3] in
lemma twist_equation (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3) (t : F) :
    (twist σ t)^2=t*σ (twist σ t) := by
  simp only [twist,map_mul,map_pow,hσ]
  ring

omit [CharP F 3] in
lemma twist_ne_zero (σ : F →+* F) {t : F} (ht : t ≠ 0) : twist σ t ≠ 0 := by
  exact mul_ne_zero (pow_ne_zero _ ht) ((map_ne_zero σ).mpr ht)

omit [CharP F 3] in
lemma twist_injective (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3) :
    Function.Injective (twist σ) := by
  intro t u h
  by_cases ht : t=0
  · subst t
    have hu : u=0 := by
      by_contra hu
      exact twist_ne_zero σ hu (by simpa [twist] using h.symm)
    exact hu.symm
  have he := twist_equation σ hσ t
  rw [h,twist_equation σ hσ u] at he
  exact (mul_right_cancel₀ ((map_ne_zero σ).mpr (twist_ne_zero σ ht))
    (by simpa [←h] using he.symm))

omit [CharP F 3] in
lemma twist_sigma_nonsquare (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    {t : F} (ht : t ≠ 0) (hns : ¬IsSquare t) : ¬IsSquare (σ (twist σ t)) := by
  intro hs
  have hh := hs.div (IsSquare.sq (t*σ t))
  apply hns
  convert hh using 1
  simp only [twist,map_mul,map_pow,hσ]
  field_simp [ht, (map_ne_zero σ).mpr ht]

omit [CharP F 3] in
lemma twist_discriminant_square (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    {t : F} (ht : IsSquare (-t)) (ht1 : IsSquare (-(t+1))) :
    IsSquare ((twist σ t)^2+σ (twist σ t)) := by
  have hs : IsSquare (t*(t+1)) := by
    convert ht.mul ht1 using 1
    ring
  convert (IsSquare.sq (t*σ t)).mul hs using 1
  simp only [twist,map_mul,map_pow,hσ]
  ring

omit [CharP F 3] in
lemma twist_discriminant_ne_zero (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    {t : F} (ht : t ≠ 0) (ht1 : t+1 ≠ 0) :
    (twist σ t)^2+σ (twist σ t) ≠ 0 := by
  rw [twist_equation σ hσ]
  have he : t*σ (twist σ t)+σ (twist σ t)=(t+1)*σ (twist σ t) := by ring
  rw [he]
  exact mul_ne_zero ht1 ((map_ne_zero σ).mpr (twist_ne_zero σ ht))

/-- The row parameter enters only the upper-left entry. -/
def row (a : F) : Mat (F := F) := !![a,1;-1,0]
def column (R w : F) : Mat (F := F) := !![0,R-w;-R-w,0]

lemma row_disc (a : F) : disc (row a)=a^2-1 := by
  simp [disc,row,Matrix.trace_fin_two,Matrix.det_fin_two]
  reduce_mod_char!

lemma column_disc (R w : F) : disc (column R w)=w^2-R^2 := by
  simp [disc,column,Matrix.trace_fin_two,Matrix.det_fin_two]
  ring_nf
  reduce_mod_char!

lemma column_difference (R w : F) :
    column R w 1 0-column R w 0 1=R := by
  simp [column]
  linear_combination -(CharP.cast_eq_zero F 3)*R

lemma column_sum (R w : F) : column R w 1 0+column R w 0 1=w := by
  simp [column]
  linear_combination -(CharP.cast_eq_zero F 3)*w

lemma incidence (σ : F →+* F) (a R w : F) (hw : w^2=R^2+σ R) :
    value σ (row a) (column R w)=1 := by
  simp only [value,row,column,sigmaMatrix,Matrix.det_fin_two,Matrix.trace_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.add_apply,Matrix.of_apply,
    Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,
    map_sub,map_neg,map_zero,map_one]
  have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
  linear_combination -hw-(σ R)*h3

/-- Four distinct square parameters give four admissible row matrices. -/
lemma row_parameter (hns : ¬IsSquare (-1:F)) (t : F) (ht : t ≠ 0)
    (hs : IsSquare t) : ¬IsSquare (disc (row ((t-1)/(t+1)))) := by
  have ht1 : t+1 ≠ 0 := by
    intro h
    have he : t=-1 := eq_neg_of_add_eq_zero_left h
    exact hns (he ▸ hs)
  rw [row_disc]
  have he : ((t-1)/(t+1))^2-1=-(t/(t+1)^2) := by
    field_simp
    have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
    linear_combination -t*h3
  rw [he]
  exact negative_square hns (div_ne_zero ht (pow_ne_zero _ ht1))
    (hs.div (IsSquare.sq (t+1)))

lemma row_parameter_injective (hns : ¬IsSquare (-1:F))
    {t u : F} (ht : IsSquare t) (hu : IsSquare u)
    (h : row ((t-1)/(t+1))=row ((u-1)/(u+1))) : t=u := by
  have hn {v : F} (hv : IsSquare v) : v+1 ≠ 0 := by
    intro h
    exact hns ((eq_neg_of_add_eq_zero_left h) ▸ hv)
  have he := congrArg (fun M : Mat (F := F) => M 0 0) h
  change (t-1)/(t+1)=(u-1)/(u+1) at he
  have he' := (div_eq_div_iff (hn ht) (hn hu)).mp he
  have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
  linear_combination -he'+(t-u)*h3

lemma negative_pair (hns : ¬IsSquare (-1:F)) {t : F}
    (ht : t ≠ 0) (ht1 : t+1 ≠ 0)
    (hs : IsSquare (-t)) (hs1 : IsSquare (-(t+1))) :
    let u := -t/(t+1)
    u ≠ 0 ∧ u+1 ≠ 0 ∧ IsSquare (-u) ∧ IsSquare (-(u+1)) ∧ t ≠ u := by
  dsimp only
  have hu1 : -t/(t+1)+1=1/(t+1) := by field_simp; ring
  refine ⟨div_ne_zero (neg_ne_zero.mpr ht) ht1,?_,?_,?_,?_⟩
  · rw [hu1]
    exact div_ne_zero one_ne_zero ht1
  · convert hs.div hs1 using 1
    field_simp
  · rw [hu1]
    convert (IsSquare.one : IsSquare (1:F)).div hs1 using 1
    field_simp
  · intro h
    have hh : t*(t+1)=-t := (eq_div_iff ht1).mp h
    have hz : t*(t-1)=0 := by
      have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
      linear_combination hh-t*h3
    have he : t=1 := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ht)
    exact hns (by simpa [he] using hs)

variable [Fintype F]

lemma parameters (hns : ¬IsSquare (-1:F)) (hq : 3 < Fintype.card F) :
    ∃ a : Fin 4 ↪ F, ∃ t : Fin 2 ↪ F,
      (∀ i, ¬IsSquare (disc (row (a i)))) ∧
      ∀ j, t j ≠ 0 ∧ t j+1 ≠ 0 ∧ IsSquare (-t j) ∧ IsSquare (-(t j+1)) := by
  obtain ⟨x,hx,hxm,hxp,hs,hsm,hsp⟩ :=
    Erdos714ConsecutiveSquares.exists_three_squares hns hq
  let p : Fin 4 → F := ![1,x,x-1,x+1]
  have hp (i : Fin 4) : p i ≠ 0 ∧ IsSquare (p i) := by
    fin_cases i <;> simp [p,hx,hxm,hxp,hs,hsm,hsp,IsSquare.one]
  have hx1 : x ≠ 1 := by intro h; exact hxm (by simp [h])
  have hxneg : x ≠ -1 := by intro h; exact hxp (by simp [h])
  have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
  have hpI : Function.Injective p := by
    intro i j h
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals dsimp [p] at h
    · exact False.elim (hx1 h.symm)
    · apply False.elim; apply hxneg; linear_combination -h+h3
    · apply False.elim; apply hx; linear_combination -h
    · exact False.elim (hx1 h)
    · apply False.elim; apply (one_ne_zero : (1:F) ≠ 0); linear_combination h
    · apply False.elim; apply (one_ne_zero : (1:F) ≠ 0); linear_combination -h
    · apply False.elim; apply hxneg; linear_combination h+h3
    · apply False.elim; apply (one_ne_zero : (1:F) ≠ 0); linear_combination -h
    · apply False.elim; apply (one_ne_zero : (1:F) ≠ 0); linear_combination h+h3
    · apply False.elim; apply hx; linear_combination h
    · apply False.elim; apply (one_ne_zero : (1:F) ≠ 0); linear_combination h
    · apply False.elim; apply (one_ne_zero : (1:F) ≠ 0); linear_combination -h+h3
  let aa : Fin 4 → F := fun i => (p i-1)/(p i+1)
  have haI : Function.Injective aa := by
    intro i j h
    apply hpI
    exact row_parameter_injective hns (hp i).2 (hp j).2 (congrArg row h)
  let v := -x
  have hv : v ≠ 0 := neg_ne_zero.mpr hx
  have hv1 : v+1 ≠ 0 := by dsimp [v]; intro h; exact hxm (by linear_combination -h)
  have hsv : IsSquare (-v) := by simpa [v] using hs
  have hsv1 : IsSquare (-(v+1)) := by convert hsm using 1; dsimp [v]; ring
  have hu := negative_pair hns hv hv1 hsv hsv1
  let tt : Fin 2 → F := ![v,-v/(v+1)]
  have htI : Function.Injective tt := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [tt]
  refine ⟨⟨aa,haI⟩,⟨tt,htI⟩,?_,?_⟩
  · intro i
    exact row_parameter hns (p i) (hp i).1 (hp i).2
  · intro j
    fin_cases j
    · exact ⟨hv,hv1,hsv,hsv1⟩
    · exact ⟨hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1⟩

/-- A uniform copy with nonsquare discriminants on every vertex. -/
theorem exists_copy (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hns : ¬IsSquare (-1:F)) (hq : 3 < Fintype.card F) :
    Nonempty (Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph σ)) := by
  obtain ⟨a,t,ha,ht⟩ := parameters hns hq
  have hroot (j : Fin 2) : ∃ w : F,
      w^2=(twist σ (t j))^2+σ (twist σ (t j)) ∧ w ≠ 0 := by
    obtain ⟨w,hw⟩ := twist_discriminant_square σ hσ (ht j).2.2.1 (ht j).2.2.2
    have hh : w^2=(twist σ (t j))^2+σ (twist σ (t j)) := by
      simpa only [pow_two] using hw.symm
    refine ⟨w,hh,?_⟩
    intro h
    exact twist_discriminant_ne_zero σ hσ (ht j).1 (ht j).2.1
      (by simpa [h] using hh.symm)
  choose w hw hw0 using hroot
  let W (j k : Fin 2) : F := if k=0 then w j else -w j
  have hW (j k : Fin 2) : (W j k)^2=(twist σ (t j))^2+σ (twist σ (t j)) := by
    dsimp [W]
    split_ifs <;> simp [hw]
  let C (p : Fin 2 × Fin 2) : Mat (F := F) := column (twist σ (t p.1)) (W p.1 p.2)
  have hCI : Function.Injective C := by
    rintro ⟨i,k⟩ ⟨j,l⟩ h
    have he := congrArg (fun M : Mat (F := F) => M 1 0-M 0 1) h
    change column _ _ 1 0-column _ _ 0 1=column _ _ 1 0-column _ _ 0 1 at he
    simp only [column_difference] at he
    have hij := t.injective (twist_injective σ hσ he)
    subst j
    have hew := congrArg (fun M : Mat (F := F) => M 1 0+M 0 1) h
    change column _ _ 1 0+column _ _ 0 1=column _ _ 1 0+column _ _ 0 1 at hew
    simp only [column_sum] at hew
    have hkl : k=l := by
      fin_cases k <;> fin_cases l <;> try rfl
      all_goals dsimp [W] at hew
      · apply False.elim; apply hw0 i
        have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
        linear_combination -hew+(w i)*h3
      · apply False.elim; apply hw0 i
        have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
        linear_combination hew+(w i)*h3
    exact Prod.ext rfl hkl
  have hCd (p : Fin 2 × Fin 2) : ¬IsSquare (disc (C p)) := by
    dsimp [C]
    rw [column_disc,hW]
    have he : (twist σ (t p.1))^2+σ (twist σ (t p.1))-(twist σ (t p.1))^2 =
        σ (twist σ (t p.1)) := by ring
    rw [he]
    exact twist_sigma_nonsquare σ hσ (ht p.1).1
      (negative_square_ne_zero hns (ht p.1).1 (ht p.1).2.2.1)
  let L : Fin 4 ↪ Mat (F := F) := ⟨fun i => row (a i),by
    intro i j h
    exact a.injective (congrArg (fun M : Mat (F := F) => M 0 0) h)⟩
  let R : Fin 4 ↪ Mat (F := F) :=
    finProdFinEquiv.symm.toEmbedding.trans ⟨C,hCI⟩
  have hLR (i j : Fin 4) : (graph σ).Adj (.inl (L i)) (.inr (R j)) := by
    refine ⟨ha i,hCd (finProdFinEquiv.symm j),?_⟩
    exact incidence σ (a i) _ _ (hW _ _)
  refine ⟨⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩⟩
  intro v u h
  cases v with
  | inl i =>
    cases u with
    | inl j => simp at h
    | inr j => exact hLR i j
  | inr i =>
    cases u with
    | inl j => exact (hLR j i).symm
    | inr j => simp at h

theorem not_free (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hns : ¬IsSquare (-1:F)) (hq : 3 < Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph σ) := by
  intro hf
  exact hf (exists_copy σ hσ hns hq)

/-- The explicit Frobenius family, with both field hypotheses discharged. -/
theorem finite_not_free (m : ℕ) (hm : 0 < m)
    (hcard : Fintype.card F=3^(2*m+1)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (iterateFrobenius F 3 (m+1))) := by
  apply not_free
  · intro x
    change (x^(3^(m+1)))^(3^(m+1))=x^3
    rw [←pow_mul,←pow_add]
    rw [show m+1+(m+1)=2*m+1+1 by omega,Nat.pow_succ,pow_mul,←hcard]
    rw [FiniteField.pow_card]
  · rw [FiniteField.isSquare_neg_one_iff,hcard,pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]
  · rw [hcard]
    exact (show 3^1=3 by norm_num) ▸
      Nat.pow_lt_pow_right (by decide : 1 < 3) (by omega : 1 < 2*m+1)

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- In particular the obstruction holds on an explicit unbounded field family. -/
theorem family_not_free (k : ℕ) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (iterateFrobenius (GaloisField 3 (2*k+3)) 3 (k+2))) := by
  letI : Fintype (GaloisField 3 (2*k+3)) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 3 (2*k+3))=3^(2*(k+1)+1) := by
    rw [Fintype.card_eq_nat_card,GaloisField.card 3 (2*k+3) (by omega)]
    congr 1
  exact finite_not_free (k+1) (by omega) hc

end Erdos714TernaryPolarMatrix

#print axioms Erdos714TernaryPolarMatrix.twist_injective
#print axioms Erdos714TernaryPolarMatrix.twist_sigma_nonsquare
#print axioms Erdos714TernaryPolarMatrix.twist_discriminant_square
#print axioms Erdos714TernaryPolarMatrix.parameters
#print axioms Erdos714TernaryPolarMatrix.incidence
#print axioms Erdos714TernaryPolarMatrix.exists_copy
#print axioms Erdos714TernaryPolarMatrix.not_free
#print axioms Erdos714TernaryPolarMatrix.finite_not_free

#print axioms Erdos714TernaryPolarMatrix.irreducible_charpoly
#print axioms Erdos714TernaryPolarMatrix.family_not_free
