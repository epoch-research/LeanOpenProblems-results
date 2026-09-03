import Submission.BinaryArtinSchreier
import Submission.TranslatedNormFibers

/-!
A uniform obstruction for the full quadratic-norm-circle connection set in
length-two binary Witt coordinates. This does not settle Erdős714.
-/
noncomputable section
open Classical SimpleGraph Finset
open scoped CharTwo
set_option maxHeartbeats 2000000
namespace Erdos714WittNormCircle
variable {E : Type*} [Field E] [CharP E 2]

/-- The carry law in length-two Witt coordinates, not componentwise addition. -/
def wittAdd (p q : E × E) : E × E := (p.1+q.1,p.2+q.2+p.1*q.1)

def conjugateNorm (τ : E →+* E) (x : E) : E := x*τ x

def graph (τ : E →+* E) : SimpleGraph ((E × E) ⊕ (E × E)) :=
  Erdos714Tensor.incidence fun p q =>
    (wittAdd p q).1 ≠ 0 ∧ conjugateNorm τ (wittAdd p q).2 =
      (conjugateNorm τ (wittAdd p q).1)^2

private def bit (b : Bool) : E := if b then 1 else 0

omit [CharP E 2] in
private lemma bit_injective : Function.Injective (bit : Bool → E) := by
  intro b c h
  cases b <;> cases c <;> simp_all [bit]

omit [CharP E 2] in
private lemma bit_square (b : Bool) : (bit b : E)^2=bit b := by cases b <;> simp [bit]
omit [CharP E 2] in
private lemma bit_fixed (τ : E →+* E) (b : Bool) : τ (bit b)=bit b := by cases b <;> simp [bit]

private lemma shifted_root (Y X : E) (hY : Y^2+Y=X^4) (b : Bool) :
    (Y+bit b)^2+(Y+bit b)=X^4 := by
  rw [add_pow_char,bit_square]
  simpa [add_assoc,add_left_comm,add_comm] using hY

private lemma norm_edge (τ : E →+* E) (A B X Y : E)
    (hA : τ A=A) (hB : τ B=B) (hX : τ X=X) (hY : τ Y=Y+1)
    (hroot : Y^2+Y=X^4) (hopen : A+X ≠ 0)
    (hd : (B+A*X)^2+(B+A*X)=A^4) :
    (graph τ).Adj (.inl (A,B)) (.inr (X,Y)) := by
  refine ⟨hopen,?_⟩
  change (B+Y+A*X)*τ (B+Y+A*X)=((A+X)*τ (A+X))^2
  rw [map_add,map_add,map_mul,hA,hB,hX,hY,map_add,hA,hX]
  have hh : (B+Y+A*X)*(B+(Y+1)+A*X) = (Y^2+Y)+((B+A*X)^2+(B+A*X)) := by
    have h2 : (2:E)=0 := CharP.cast_eq_zero E 2
    ring_nf
    simp only [h2,mul_zero,add_zero]
  rw [hh,hroot,hd,← sq,show ((A+X)^2)^2=(A+X)^4 by ring,
    show (A+X)^4=A^4+X^4 from add_pow_char_pow A X 2 2]
  exact add_comm _ _

private def rows (a b : E) (i : Bool × Bool) : E × E :=
  (bit i.1*a,bit i.1*b+bit i.2)

private def columns (X Y : Bool → E) (i : Bool × Bool) : E × E :=
  (X i.1,Y i.1+bit i.2)

omit [CharP E 2] in
private lemma rows_injective (a b : E) (ha : a ≠ 0) : Function.Injective (rows a b) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  have hik : i=k := bit_injective (mul_right_cancel₀ ha (congrArg Prod.fst h))
  subst k
  have hjl : j=l := bit_injective (add_left_cancel (congrArg Prod.snd h))
  subst l
  rfl

omit [CharP E 2] in
private lemma columns_injective (X Y : Bool → E) (hX : Function.Injective X) :
    Function.Injective (columns X Y) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  have hik : i=k := hX (congrArg Prod.fst h)
  subst k
  have hjl : j=l := bit_injective (add_left_cancel (congrArg Prod.snd h))
  subst l
  rfl

/-- A symbolic four-row/two-pair template, with all open and injectivity
conditions explicit. -/
def templateCopy (τ : E →+* E) (a b : E) (X Y : Bool → E)
    (ha : a ≠ 0) (hXinj : Function.Injective X)
    (haf : τ a=a) (hbf : τ b=b) (hXf : ∀ i, τ (X i)=X i)
    (hYf : ∀ i, τ (Y i)=Y i+1) (hroot : ∀ i, (Y i)^2+Y i=(X i)^4)
    (hX0 : ∀ i, X i ≠ 0) (hXa : ∀ i, a+X i ≠ 0)
    (hd : ∀ i, (b+a*X i)^2+(b+a*X i)=a^4) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph τ) := by
  let e : Fin 4 ≃ Bool × Bool := Fintype.equivOfCardEq (by decide)
  let L : Fin 4 ↪ E × E := ⟨fun i => rows a b (e i),(rows_injective a b ha).comp e.injective⟩
  let R : Fin 4 ↪ E × E := ⟨fun i => columns X Y (e i),(columns_injective X Y hXinj).comp e.injective⟩
  have hedge (i j : Bool × Bool) : (graph τ).Adj (.inl (rows a b i)) (.inr (columns X Y j)) := by
    apply norm_edge τ
    · simp only [map_mul,bit_fixed,haf]
    · simp only [map_add,map_mul,bit_fixed,hbf]
    · exact hXf j.1
    · simp only [map_add,hYf,bit_fixed]
      ring
    · exact shifted_root _ _ (hroot j.1) j.2
    · cases hi : i.1
      · simpa [bit,hi] using hX0 j.1
      · simpa [bit,hi] using hXa j.1
    · cases hi : i.1 <;> cases hj : i.2 <;>
        simp only [bit,Bool.false_eq_true,↓reduceIte,zero_mul,one_mul,zero_add,add_zero,
          add_pow_char,one_pow] <;>
        first | simp | simpa [add_pow_char,add_assoc,add_comm,add_left_comm] using hd j.1
  refine ⟨⟨Sum.elim (fun i => Sum.inl (L i)) (fun j => Sum.inr (R j)),?_⟩,?_⟩
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => simp at hij
      | inr j => exact hedge (e i) (e j)
    | inr i =>
      cases j with
      | inl j => exact hedge (e j) (e i)
      | inr j => simp at hij
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (L.injective (Sum.inl.inj hij))
      | inr j => cases hij
    | inr i =>
      cases j with
      | inl j => cases hij
      | inr j => exact congrArg Sum.inr (R.injective (Sum.inr.inj hij))

#print axioms templateCopy
end Erdos714WittNormCircle
