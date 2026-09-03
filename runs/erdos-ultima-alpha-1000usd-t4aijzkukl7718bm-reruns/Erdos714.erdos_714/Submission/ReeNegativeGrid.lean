import FormalConjecturesUtil

/-!
A prime-field rectangular obstruction for the displayed Ree-style kernel,
with a uniform transfer to every negative nonzero square. No classification
of finite Ree groups is assumed. This does not settle Erdős 714.
-/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace Erdos714ReeNegative
variable {F : Type*} [Field F] [CharP F 3]
abbrev Point (F : Type*) := F × F × F

/-- The explicit root-coordinate multiplication. -/
def mul (σ : F →+* F) (u v : Point F) : Point F :=
  (u.1+v.1,u.2.1+v.2.1+σ u.1*v.1,
    u.2.2+v.2.2-u.1*v.2.1+u.2.1*v.1-u.1*σ u.1*v.1)

def inv (σ : F →+* F) (u : Point F) : Point F :=
  (-u.1,-u.2.1+u.1*σ u.1,-u.2.2)

/-- Closed formula for the original relative-coordinate argument. -/
def relative (σ : F →+* F) (u v : Point F) : Point F :=
  (v.1-u.1,v.2.1-u.2.1-σ u.1*(v.1-u.1),
    v.2.2-u.2.2+u.1*v.2.1-u.2.1*v.1)

omit [CharP F 3] in
lemma relative_eq (σ : F →+* F) (u v : Point F) :
    relative σ u v = mul σ (inv σ u) v := by
  rcases u with ⟨a,b,c⟩
  rcases v with ⟨d,e,f⟩
  apply Prod.ext _ (Prod.ext _ _) <;> simp only [relative,mul,inv,map_neg] <;> ring

/-- The polynomial/semilinear norm formula, not an unspecified group invariant. -/
def norm (σ : F →+* F) (u : Point F) : F :=
  -u.1*σ u.2.2+u.1*σ u.1*σ u.2.1-u.1^3*σ u.1*u.2.1-
    u.1^2*u.2.1^2+u.2.1*σ u.2.1+u.2.2^2-u.1^4*(σ u.1)^2

def rows : Fin 4 → Point F := ![(0,0,0),(0,0,1),(0,1,-1),(0,-1,-1)]
def columns : Fin 6 → Point F :=
  ![(1,0,1),(1,1,1),(1,-1,1),(-1,0,0),(-1,1,0),(-1,-1,0)]

lemma rows_injective : Function.Injective (rows (F := F)) := by
  have h12 : (1 : F) ≠ 2 := by
    intro h
    apply (one_ne_zero : (1 : F) ≠ 0)
    linear_combination -h
  intro i j h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals simp [rows] at h
  all_goals reduce_mod_char! at h
  all_goals first | exact False.elim (h12 h) | exact False.elim (h12.symm h)

lemma columns_injective : Function.Injective (columns (F := F)) := by
  have h12 : (1 : F) ≠ 2 := by
    intro h
    apply (one_ne_zero : (1 : F) ≠ 0)
    linear_combination -h
  intro i j h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals simp [columns] at h
  all_goals reduce_mod_char! at h
  all_goals first | exact False.elim (h12 h) | exact False.elim (h12.symm h)

/-- All twenty-four ORIGINAL relative-norm equations hold for any endomorphism. -/
lemma negative_grid (σ : F →+* F) (i : Fin 4) (j : Fin 6) :
    norm σ (relative σ (rows i) (columns j)) = -1 := by
  fin_cases i <;> fin_cases j <;>
    simp [rows,columns,relative,norm] <;> norm_num <;> reduce_mod_char!

/-- Root-coordinate scaling has three different, explicitly specified weights. -/
def scale (σ : F →+* F) (t : F) (u : Point F) : Point F :=
  (t*u.1,t*σ t*u.2.1,t^2*σ t*u.2.2)

omit [CharP F 3] in
lemma scale_injective (σ : F →+* F) {t : F} (ht : t ≠ 0) :
    Function.Injective (scale σ t) := by
  intro u v h
  have hs : σ t ≠ 0 := by simpa only [map_zero] using σ.injective.ne ht
  have ha := congrArg (fun p : Point F => p.1) h
  have hb := congrArg (fun p : Point F => p.2.1) h
  have hc := congrArg (fun p : Point F => p.2.2) h
  exact Prod.ext (mul_left_cancel₀ ht ha)
    (Prod.ext (mul_left_cancel₀ (mul_ne_zero ht hs) hb)
      (mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 ht) hs) hc))

omit [CharP F 3] in
lemma relative_scale (σ : F →+* F) (t : F) (u v : Point F) :
    relative σ (scale σ t u) (scale σ t v) = scale σ t (relative σ u v) := by
  rcases u with ⟨a,b,c⟩
  rcases v with ⟨d,e,f⟩
  apply Prod.ext _ (Prod.ext _ _) <;> simp only [scale,relative,map_mul] <;> ring

omit [CharP F 3] in
lemma norm_scale (σ : F →+* F) (t : F) (ht : σ (σ t)=t^3) (u : Point F) :
    norm σ (scale σ t u) = (t^2*σ t)^2*norm σ u := by
  simp only [norm,scale,map_mul,map_pow,ht]
  ring

/-- An explicit inverse to the scalar map t -> t² sigma(t). -/
def scalar (σ : F →+* F) (s : F) : F := s^2/σ s

omit [CharP F 3] in
lemma scalar_ne_zero (σ : F →+* F) {s : F} (hs : s ≠ 0) : scalar σ s ≠ 0 :=
  div_ne_zero (pow_ne_zero 2 hs) ((_root_.map_ne_zero σ).mpr hs)

omit [CharP F 3] in
lemma scalar_identity (σ : F →+* F) (s : F) (hs : s ≠ 0)
    (hσ : σ (σ s)=s^3) : (scalar σ s)^2*σ (scalar σ s)=s := by
  have ht : σ s ≠ 0 := (_root_.map_ne_zero σ).mpr hs
  simp only [scalar,map_div₀,map_pow,hσ]
  field_simp

/-- The configuration survives at EVERY prescribed negative nonzero square. -/
lemma scaled_grid (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (s : F) (hs : s ≠ 0) (i : Fin 4) (j : Fin 6) :
    norm σ (relative σ (scale σ (scalar σ s) (rows i))
      (scale σ (scalar σ s) (columns j))) = -s^2 := by
  rw [relative_scale,norm_scale σ _ (hσ _),scalar_identity σ s hs (hσ s),negative_grid]
  ring

/-- Arbitrary label sets and arbitrary weight operations are allowed. -/
def graph {A B : Type*} (σ : F →+* F) (W : A → B → F) :
    SimpleGraph ((Point F × A) ⊕ (Point F × B)) where
  Adj u v := match u,v with
    | .inl x,.inr y => norm σ (relative σ x.1 y.1)=W x.2 y.2
    | .inr y,.inl x => norm σ (relative σ x.1 y.1)=W x.2 y.2
    | _,_ => False
  symm := by intro u v; cases u <;> cases v <;> exact id
  loopless := by intro u; cases u <;> exact not_false

/-- This is an actual graph copy with both injections, not just norm equalities. -/
def negativeSquareCopy {A B : Type*} (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (W : A → B → F) (a : A) (b : B) (s : F) (hs : s ≠ 0) (hW : W a b = -s^2) :
    (completeBipartiteGraph (Fin 4) (Fin 6)).Copy (graph σ W) := by
  let l : Fin 4 ↪ Point F × A := ⟨fun i => (scale σ (scalar σ s) (rows i),a),by
    intro i j he
    exact rows_injective (scale_injective σ (scalar_ne_zero σ hs) (congrArg Prod.fst he))⟩
  let r : Fin 6 ↪ Point F × B := ⟨fun j => (scale σ (scalar σ s) (columns j),b),by
    intro i j he
    exact columns_injective (scale_injective σ (scalar_ne_zero σ hs) (congrArg Prod.fst he))⟩
  refine ⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩
  intro u v huv
  cases u with
  | inl i =>
    cases v with
    | inl j => simp at huv
    | inr j => exact (scaled_grid σ hσ s hs i j).trans hW.symm
  | inr j =>
    cases v with
    | inr i => simp at huv
    | inl i => exact (scaled_grid σ hσ s hs i j).trans hW.symm

/-- The negative-square entry may occur anywhere in the weight table. -/
theorem not_free_six {A B : Type*} (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (W : A → B → F) (a : A) (b : B) (s : F) (hs : s ≠ 0) (hW : W a b = -s^2) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 6)).Free (graph σ W) := by
  intro h
  exact h ⟨negativeSquareCopy σ hσ W a b s hs hW⟩

def fourOfSix {V : Type*} {G : SimpleGraph V}
    (c : (completeBipartiteGraph (Fin 4) (Fin 6)).Copy G) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy G := by
  let l : Fin 4 ↪ Fin 4 := Function.Embedding.refl _
  let r : Fin 4 ↪ Fin 6 := Fin.castLEEmb (by decide)
  refine ⟨⟨fun z => c ((l.sumMap r) z),?_⟩,c.injective.comp (l.sumMap r).injective⟩
  intro u v huv
  apply c.toHom.map_adj
  cases u <;> cases v <;> simp_all

theorem not_free_four {A B : Type*} (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (W : A → B → F) (a : A) (b : B) (s : F) (hs : s ≠ 0) (hW : W a b = -s^2) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph σ W) := by
  intro h
  exact h ⟨fourOfSix (negativeSquareCopy σ hσ W a b s hs hW)⟩

/-- Even when every label is a square unit, changing the sign of the
multiplicative norm law does not produce a free graph. -/
theorem negative_square_labels_not_free (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph σ (fun a b : {u : Fˣ // IsSquare (u : F)} => -(a.val : F)*(b.val : F))) := by
  let one : {u : Fˣ // IsSquare (u : F)} := ⟨1,by simp⟩
  exact not_free_four σ hσ _ one one 1 one_ne_zero (by simp [one])


/-- Any full row of an arbitrary label operation suffices for this obstruction. -/
theorem surjective_row_not_free {A B : Type*} (σ : F →+* F)
    (hσ : ∀ x, σ (σ x)=x^3) (W : A → B → F) (a : A)
    (hsurj : ∀ t : F, t ≠ 0 → ∃ b, W a b=t) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph σ W) := by
  obtain ⟨b,hb⟩ := hsurj (-1) (neg_ne_zero.mpr one_ne_zero)
  exact not_free_four σ hσ W a b 1 one_ne_zero (by simpa using hb)

/-- The usual nonzero multiplicative labels in particular cannot work. -/
theorem multiplicative_not_free (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph σ (fun a b : Fˣ => (a : F)*(b : F))) := by
  exact not_free_four σ hσ _ 1 (-1) 1 one_ne_zero (by simp)

/-- Mixed square/nonsquare label classes already contain the prime-field copy
when minus one is nonsquare. No larger-field existence calculation is used. -/
theorem mixed_labels_not_free (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^3)
    (hn : ¬ IsSquare (-1 : F)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph σ (fun (a : {u : Fˣ // IsSquare (u : F)})
        (b : {u : Fˣ // ¬ IsSquare (u : F)}) => (a.val : F)*(b.val : F))) := by
  let a : {u : Fˣ // IsSquare (u : F)} := ⟨1,by simp⟩
  let b : {u : Fˣ // ¬ IsSquare (u : F)} := ⟨-1,by simpa using hn⟩
  exact not_free_four σ hσ _ a b 1 one_ne_zero (by simp [a,b])


section FiniteRee
variable [Fintype F]

def reeTwist (m : ℕ) : F →+* F := iterateFrobenius F 3 (m+1)

lemma reeTwist_square (m : ℕ) (hcard : Fintype.card F=3^(2*m+1)) (x : F) :
    reeTwist (F := F) m (reeTwist m x)=x^3 := by
  change (x^(3^(m+1)))^(3^(m+1))=x^3
  rw [← pow_mul,← pow_add]
  rw [show m+1+(m+1)=2*m+1+1 by omega,Nat.pow_succ,pow_mul,← hcard]
  rw [FiniteField.pow_card]

/-- Actual Frobenius twists, including the smallest field. -/
theorem finite_negative_square_labels (m : ℕ) (hcard : Fintype.card F=3^(2*m+1)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (reeTwist m)
        (fun a b : {u : Fˣ // IsSquare (u : F)} => -(a.val : F)*(b.val : F))) :=
  negative_square_labels_not_free _ (reeTwist_square m hcard)

theorem finite_mixed_labels (m : ℕ) (hcard : Fintype.card F=3^(2*m+1)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (reeTwist m) (fun (a : {u : Fˣ // IsSquare (u : F)})
        (b : {u : Fˣ // ¬ IsSquare (u : F)}) => (a.val : F)*(b.val : F))) := by
  apply mixed_labels_not_free _ (reeTwist_square m hcard)
  intro hs
  have h := FiniteField.isSquare_neg_one_iff.mp hs
  have hm : 3^(2*m+1)%4=3 := by
    rw [pow_add,pow_mul]
    simp [Nat.mul_mod,Nat.pow_mod]
  rw [hcard,hm] at h
  exact h rfl

end FiniteRee

end Erdos714ReeNegative
#print axioms Erdos714ReeNegative.relative_eq
#print axioms Erdos714ReeNegative.negative_grid
#print axioms Erdos714ReeNegative.norm_scale
#print axioms Erdos714ReeNegative.scalar_identity
#print axioms Erdos714ReeNegative.negativeSquareCopy
#print axioms Erdos714ReeNegative.not_free_four
#print axioms Erdos714ReeNegative.negative_square_labels_not_free

#print axioms Erdos714ReeNegative.surjective_row_not_free
#print axioms Erdos714ReeNegative.multiplicative_not_free
#print axioms Erdos714ReeNegative.mixed_labels_not_free

#print axioms Erdos714ReeNegative.reeTwist_square
#print axioms Erdos714ReeNegative.finite_negative_square_labels
#print axioms Erdos714ReeNegative.finite_mixed_labels
