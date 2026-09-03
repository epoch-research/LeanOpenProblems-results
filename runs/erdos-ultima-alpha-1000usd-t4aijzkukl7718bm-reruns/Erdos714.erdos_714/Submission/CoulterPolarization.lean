import Submission.WeightedProfiles

/-! Exact arithmetic and weighted-profile obstructions for norm polarizations.
These results do not settle Erdos714. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714CoulterPolar
section Arithmetic
variable {E : Type*} [Field E] [CharP E 3]

def polar (d : ℕ) (x y : E) : E := (x+y)^d-x^d-y^d

/-- The square/opposite-square factorization behind the point-class split. -/
lemma polar_square_neg_square (s d : ℕ) (hd : 2*d=3^s+1) (he : Even d)
    (X Y : E) :
    polar d (X^2) (-(Y^2)) = ((X+Y)^d-(X-Y)^d)^2 := by
  have h3 : (3 : E)=0 := CharP.cast_eq_zero E 3
  have hsum : ((X+Y)^d)^2 + ((X-Y)^d)^2 + X^(2*d)+Y^(2*d)=0 := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm d 2,hd,
      pow_succ,pow_succ,pow_succ,pow_succ,
      add_pow_char_pow X Y 3 s,sub_pow_char_pow X Y s]
    linear_combination (X^(3^s)*X+Y^(3^s)*Y)*h3
  have hxy : X^2-Y^2=(X+Y)*(X-Y) := by ring
  simp only [polar,he.neg_pow,← pow_mul]
  rw [← sub_eq_add_neg (X^2) (Y^2),hxy,mul_pow]
  linear_combination -hsum + ((X+Y)^d*(X-Y)^d)*h3

omit [CharP E 3] in
lemma odd_iterated_power {a : E} {k n : ℕ} (h : a^k=a⁻¹) (hn : Odd n) :
    a^(k^n)=a⁻¹ := by
  have h2 : a^(k^2)=a := by
    rw [pow_two,pow_mul,h,inv_pow,h,inv_inv]
  have hj (j : ℕ) : a^(k^(2*j))=a := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ,pow_add,pow_mul,ih,h2]
  obtain ⟨j,hj'⟩ := hn
  have hn' : n=2*j+1 := by omega
  rw [hn',pow_succ,pow_mul,hj,h]

omit [CharP E 3] in
/-- In an odd-degree ternary field, these half-Frobenius powers identify
only a point and its negative. No planarity hypothesis is needed. -/
lemma power_collision [Fintype E] (n s d : ℕ) (hn : Odd n)
    (hE : Fintype.card E=3^n) (hd : 2*d=3^s+1)
    {x y : E} (hxy : x^d=y^d) : x=y ∨ x=-y := by
  have hd0 : d≠0 := by intro h; subst d; simp at hd
  by_cases hy : y=0
  · subst y
    have hx : x=0 := (pow_eq_zero_iff hd0).mp (by simpa [hd0] using hxy)
    exact Or.inl hx
  have hx : x≠0 := by
    intro hx
    rw [hx,zero_pow hd0] at hxy
    exact hy ((pow_eq_zero_iff hd0).mp hxy.symm)
  let a := x/y
  have ha : a≠0 := div_ne_zero hx hy
  have had : a^d=1 := by simp [a,div_pow,hxy,pow_ne_zero _ hy]
  have hp : a^(3^s+1)=1 := by rw [← hd,Nat.mul_comm 2 d,pow_mul,had,one_pow]
  have hi : a^(3^s)=a⁻¹ := by
    apply (mul_right_cancel₀ ha)
    simpa [pow_succ,ha] using hp
  have ho := odd_iterated_power hi hn
  have hc : a^((3^s)^n)=a := by
    rw [← pow_mul,Nat.mul_comm s n,pow_mul,← hE]
    exact FiniteField.pow_card_pow s a
  rw [hc] at ho
  have ha2 : a^2=1^2 := by
    calc
      a^2=a*a := pow_two a
      _ = a*a⁻¹ := congrArg (a*·) ho
      _ = 1^2 := by simp [ha]
  have hor : a=1 ∨ a=-1 := by
    simpa using (sq_eq_sq_iff_eq_or_eq_neg.mp ha2)
  rcases hor with h | h
  · left
    exact (div_eq_one_iff_eq hy).mp h
  · right
    have hh := (div_eq_iff hy).mp h
    simpa only [neg_one_mul] using hh

lemma polar_square_ne_zero [Fintype E] (n s d : ℕ) (hn : Odd n)
    (hE : Fintype.card E=3^n) (hd : 2*d=3^s+1) (he : Even d)
    {X Y : E} (hX : X≠0) (hY : Y≠0) :
    polar d (X^2) (-(Y^2)) ≠ 0 := by
  rw [polar_square_neg_square s d hd he]
  apply pow_ne_zero
  intro h
  rcases power_collision n s d hn hE hd (sub_eq_zero.mp h) with h | h
  · have : Y=0 := by
      have h3 : (3 : E)=0 := CharP.cast_eq_zero E 3
      linear_combination -h + Y*h3
    exact hY this
  · have : X=0 := by
      have h3 : (3 : E)=0 := CharP.cast_eq_zero E 3
      linear_combination -h + X*h3
    exact hX this

end Arithmetic

section Squares
variable (E : Type*) [Field E] [Fintype E]

omit [Fintype E] in
lemma square_eq_range : Subgroup.square Eˣ = (powMonoidHom 2 : Eˣ →* Eˣ).range := by
  ext x
  simp only [Subgroup.mem_square,MonoidHom.mem_range,powMonoidHom_apply,pow_two,IsSquare]
  constructor <;> rintro ⟨r,hr⟩ <;> exact ⟨r,hr.symm⟩

lemma square_card (hodd : Odd (Fintype.card E)) :
    Fintype.card (Subgroup.square Eˣ)=(Fintype.card E-1)/2 := by
  rw [← Nat.card_eq_fintype_card,square_eq_range,IsCyclic.card_powMonoidHom_range]
  simp only [Nat.card_eq_fintype_card,Fintype.card_units]
  have he : Even (Fintype.card E-1) := by
    obtain ⟨k,hk⟩ := hodd
    exact ⟨k,by omega⟩
  rw [Nat.gcd_eq_right (even_iff_two_dvd.mp he)]

end Squares
section NormGraph
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  [Fintype F] [Fintype E] [CharP E 3]

abbrev Sq (K : Type*) [Field K] := Subgroup.square Kˣ

lemma square_polar (n s d : ℕ) (hn : Odd n)
    (hE : Fintype.card E=3^n) (hd : 2*d=3^s+1) (he : Even d)
    (x y : Sq E) :
    IsSquare (polar d ((x : Eˣ) : E) (-((y : Eˣ) : E))) ∧
      polar d ((x : Eˣ) : E) (-((y : Eˣ) : E)) ≠ 0 := by
  obtain ⟨u,hu⟩ := x.property.exists_sq
  obtain ⟨v,hv⟩ := y.property.exists_sq
  have hx : ((x : Eˣ) : E)=(u : E)^2 := congrArg Units.val hu
  have hy : ((y : Eˣ) : E)=(v : E)^2 := congrArg Units.val hv
  rw [hx,hy]
  refine ⟨(isSquare_iff_exists_sq _).mpr ⟨(u+v : E)^d-(u-v : E)^d,
    polar_square_neg_square s d hd he _ _⟩, ?_⟩
  exact polar_square_ne_zero n s d hn hE hd he u.ne_zero v.ne_zero

def polarUnit (n s d : ℕ) (hn : Odd n)
    (hE : Fintype.card E=3^n) (hd : 2*d=3^s+1) (he : Even d)
    (x y : Sq E) : Eˣ :=
  Units.mk0 (polar d ((x : Eˣ) : E) (-((y : Eˣ) : E)))
    (square_polar n s d hn hE hd he x y).2

lemma polarUnit_square (n s d : ℕ) (hn : Odd n)
    (hE : Fintype.card E=3^n) (hd : 2*d=3^s+1) (he : Even d)
    (x y : Sq E) : IsSquare (polarUnit n s d hn hE hd he x y) := by
  obtain ⟨z,hz⟩ := (square_polar n s d hn hE hd he x y).1.exists_sq
  have hz0 : z≠0 := by
    intro h
    apply (square_polar n s d hn hE hd he x y).2
    simpa [h] using hz
  exact (isSquare_iff_exists_sq _).mpr ⟨Units.mk0 z hz0,Units.ext hz⟩

def normValue (n s d : ℕ) (hn : Odd n)
    (hE : Fintype.card E=3^n) (hd : 2*d=3^s+1) (he : Even d)
    (x y : Sq E) : Sq F :=
  ⟨Units.map (Algebra.norm F (S := E)) (polarUnit n s d hn hE hd he x y),
    (polarUnit_square n s d hn hE hd he x y).map
      (Units.map (Algebra.norm F (S := E)))⟩

omit [Fintype F] in
lemma normValue_coe (n s d : ℕ) (hn : Odd n)
    (hE : Fintype.card E=3^n) (hd : 2*d=3^s+1) (he : Even d)
    (x y : Sq E) :
    ((normValue (F := F) n s d hn hE hd he x y : Fˣ) : F) =
      Algebra.norm F (polar d ((x : Eˣ) : E) (-((y : Eˣ) : E))) := rfl

/-- This is the original norm equation on the square/opposite-square point
component, with actual nonzero square weights, not an enlarged profile host. -/
def componentGraph (d : ℕ) (valid : Sq E → Sq E → Prop) :
    SimpleGraph ((Sq E × Sq F) ⊕ (Sq E × Sq F)) :=
  Erdos714Tensor.incidence fun p q => valid p.1 q.1 ∧
    Algebra.norm F (polar d ((p.1 : Eˣ) : E) (-((q.1 : Eˣ) : E))) =
      ((p.2 : Fˣ) : F)*((q.2 : Fˣ) : F)

omit [Fintype F] in
lemma componentGraph_eq (n s d : ℕ) (hn : Odd n)
    (hE : Fintype.card E=3^n) (hd : 2*d=3^s+1) (he : Even d)
    (valid : Sq E → Sq E → Prop) :
    componentGraph (F := F) d valid =
      Erdos714WeightedProfiles.graph (normValue (F := F) n s d hn hE hd he) valid := by
  ext a b
  cases a <;> cases b
  · rfl
  · change (_ ∧ _) ↔ (_ ∧ _)
    constructor
    · rintro ⟨hv,heq⟩
      exact ⟨hv,Subtype.ext (Units.ext heq)⟩
    · rintro ⟨hv,heq⟩
      exact ⟨hv,congrArg (fun z : Sq F => ((z : Fˣ) : F)) heq⟩
  · change (_ ∧ _) ↔ (_ ∧ _)
    constructor
    · rintro ⟨hv,heq⟩
      exact ⟨hv,Subtype.ext (Units.ext heq)⟩
    · rintro ⟨hv,heq⟩
      exact ⟨hv,congrArg (fun z : Sq F => ((z : Fˣ) : F)) heq⟩
  · rfl

/-- A uniform criterion, including arbitrary bounded deletions depending on
the row point. Planarity is not assumed or needed. -/
theorem component_not_free (n s d : ℕ) (hn : Odd n)
    (hE : Fintype.card E=3^n) (hd : 2*d=3^s+1) (he : Even d)
    (valid : Sq E → Sq E → Prop) (x : Fin 4 ↪ Sq E) (b : ℕ)
    (hbad : ∀ i, (univ.filter (fun y => ¬ valid (x i) y)).card ≤ b)
    (hcard : 3 * Fintype.card (Sq F)^3 + 4*b < Fintype.card (Sq E)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (componentGraph (F := F) d valid) := by
  rw [componentGraph_eq n s d hn hE hd he]
  exact Erdos714WeightedProfiles.not_free_of_bounded_deletions _ _ x b hbad hcard

lemma profile_budget {q b : ℕ} (hodd : Odd q) (hq : 27 ≤ q)
    (hb : b ≤ q+26) :
    3*((q-1)/2)^3+4*b < (q^3-1)/2 := by
  obtain ⟨k,rfl⟩ := hodd
  have hk : 13 ≤ k := by omega
  have hd1 : (2*k+1-1)/2=k := by omega
  have hp : (2*k+1)^3=(4*k^3+6*k^2+3*k)*2+1 := by ring
  have hd3 : ((2*k+1)^3-1)/2=4*k^3+6*k^2+3*k := by rw [hp]; omega
  rw [hd1,hd3]
  nlinarith [Nat.mul_le_mul_right k hk]

lemma half_exponent (s : ℕ) (hs : Odd s) :
    2*((3^s+1)/2)=3^s+1 ∧ Even ((3^s+1)/2) := by
  obtain ⟨k,hk⟩ := hs
  have hs' : s=2*k+1 := by omega
  have hm : 3^s%4=3 := by
    rw [hs',pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]
  exact ⟨by omega,⟨(3^s+1)/4,by omega⟩⟩

/-- Every odd ternary base field of size at least 27 fails for EVERY odd
Coulter--Matthews exponent, even without assuming the polarization is planar.
Up to q+26 forbidden column points per row can be removed first. -/
theorem odd_cubic_not_free (m s : ℕ) (hm : Odd m) (hs : Odd s)
    (hF : Fintype.card F=3^m) (hE : Fintype.card E=Fintype.card F^3)
    (hq : 27 ≤ Fintype.card F) (b : ℕ) (hb : b ≤ Fintype.card F+26)
    (valid : Sq E → Sq E → Prop)
    (hbad : ∀ x, (univ.filter (fun y => ¬ valid x y)).card ≤ b) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (componentGraph (F := F) ((3^s+1)/2) valid) := by
  have hEn : Fintype.card E=3^(3*m) := by rw [hE,hF,← pow_mul,Nat.mul_comm m 3]
  have hn : Odd (3*m) := (by decide : Odd 3).mul hm
  have hFo : Odd (Fintype.card F) := by rw [hF]; exact (by decide : Odd 3).pow
  have hEo : Odd (Fintype.card E) := by rw [hE]; exact hFo.pow
  have hcF := square_card F hFo
  have hcE := square_card E hEo
  have hq3 : 9 ≤ Fintype.card F^3 := by
    nlinarith [Nat.mul_le_mul hq hq,
      Nat.mul_le_mul_right (Fintype.card F^2) hq]
  have hfour : 4 ≤ Fintype.card (Sq E) := by rw [hcE,hE]; omega
  obtain ⟨x,_⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 4) (s := (univ : Finset (Sq E))) (by simpa using hfour)
  have hnum : 3*Fintype.card (Sq F)^3+4*b < Fintype.card (Sq E) := by
    rw [hcF,hcE,hE]
    exact profile_budget hFo hq hb
  obtain ⟨hd,he⟩ := half_exponent s hs
  exact component_not_free (F := F) (3*m) s _ hn hEn hd he valid x b
    (fun i => hbad (x i)) hnum

/-- The full graph uses the original nonzero point coordinates on both sides.
The ratio filter is independent of the square-weight labels. -/
def fullGraph (d : ℕ) (T : Finset Eˣ) :
    SimpleGraph ((Eˣ × Sq F) ⊕ (Eˣ × Sq F)) :=
  Erdos714Tensor.incidence fun p q => q.1/p.1 ∉ T ∧
    Algebra.norm F (polar d (p.1 : E) (q.1 : E)) =
      ((p.2 : Fˣ) : F)*((q.2 : Fˣ) : F)

def componentCopy (d : ℕ) (T : Finset Eˣ) :
    (componentGraph (F := F) (E := E) d (fun x y => -(y : Eˣ)/(x : Eˣ) ∉ T)).Copy
      (fullGraph (F := F) d T) := by
  let L : Sq E ↪ Eˣ := Function.Embedding.subtype _
  let R : Sq E ↪ Eˣ := ⟨fun y => -(y : Eˣ),by
    intro a b hab
    exact Subtype.ext (neg_injective hab)⟩
  let f := (L.prodMap (Function.Embedding.refl (Sq F))).sumMap
    (R.prodMap (Function.Embedding.refl (Sq F)))
  refine ⟨⟨f,?_⟩,f.injective⟩
  intro a b hab
  cases a <;> cases b
  · exact hab
  · exact hab
  · exact hab
  · exact hab

omit [Algebra F E] [Fintype F] [CharP E 3] in
lemma ratio_bad_card (T : Finset Eˣ) (x : Sq E) :
    (univ.filter (fun y : Sq E => ¬ -(y : Eˣ)/(x : Eˣ) ∉ T)).card ≤ T.card := by
  simp only [not_not]
  apply card_le_card_of_injOn (fun y : Sq E => -(y : Eˣ)/(x : Eˣ))
  · intro y hy
    exact (mem_filter.mp hy).2
  · intro a _ b _ hab
    apply Subtype.ext
    exact neg_injective (mul_right_cancel hab)

/-- Removing any q+26 prescribed point-ratio values still leaves a K44.
This includes simultaneous removal of the base-field and F27 ratios. -/
theorem full_not_free (m s : ℕ) (hm : Odd m) (hs : Odd s)
    (hF : Fintype.card F=3^m) (hE : Fintype.card E=Fintype.card F^3)
    (hq : 27 ≤ Fintype.card F) (T : Finset Eˣ) (hT : T.card ≤ Fintype.card F+26) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (fullGraph (F := F) ((3^s+1)/2) T) := by
  intro hf
  apply odd_cubic_not_free m s hm hs hF hE hq T.card hT
    (fun x y => -(y : Eˣ)/(x : Eˣ) ∉ T) (fun x => by simpa using ratio_bad_card T x)
  rintro ⟨c⟩
  exact hf ⟨(componentCopy _ T).comp c⟩

/-- These two root conditions contain every nonzero ratio from the base
field or the characteristic-three field with 27 elements. -/
def fieldRatios (q : ℕ) : Finset Eˣ :=
  univ.filter (fun t => t^(q-1)=1 ∨ t^26=1)

omit [Algebra F E] [Fintype F] [CharP E 3] in
lemma fieldRatios_card (q : ℕ) (hq : 2 ≤ q) :
    (fieldRatios (E := E) q).card ≤ q+26 := by
  have hu : fieldRatios (E := E) q =
      (univ.filter (fun t : Eˣ => t^(q-1)=1)) ∪
        (univ.filter (fun t : Eˣ => t^26=1)) := by
    ext t
    simp [fieldRatios]
  rw [hu]
  have h1 := IsCyclic.card_pow_eq_one_le (α := Eˣ) (show 0 < q-1 by omega)
  have h2 := IsCyclic.card_pow_eq_one_le (α := Eˣ) (show 0 < 26 by omega)
  have h := card_union_le (univ.filter (fun t : Eˣ => t^(q-1)=1))
    (univ.filter (fun t : Eˣ => t^26=1))
  omega

theorem filtered_full_not_free (m s : ℕ) (hm : Odd m) (hs : Odd s)
    (hF : Fintype.card F=3^m) (hE : Fintype.card E=Fintype.card F^3)
    (hq : 27 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (fullGraph (F := F) ((3^s+1)/2) (fieldRatios (E := E) (Fintype.card F))) :=
  full_not_free m s hm hs hF hE hq _ (fieldRatios_card _ (by omega))

end NormGraph
end Erdos714CoulterPolar
#print axioms Erdos714CoulterPolar.polar_square_neg_square
#print axioms Erdos714CoulterPolar.power_collision
#print axioms Erdos714CoulterPolar.polar_square_ne_zero
#print axioms Erdos714CoulterPolar.square_card
#print axioms Erdos714CoulterPolar.component_not_free
#print axioms Erdos714CoulterPolar.odd_cubic_not_free
#print axioms Erdos714CoulterPolar.full_not_free
#print axioms Erdos714CoulterPolar.filtered_full_not_free
