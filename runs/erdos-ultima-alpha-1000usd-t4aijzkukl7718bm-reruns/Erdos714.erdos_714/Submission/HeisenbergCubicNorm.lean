import Submission.CubicTraceNormPlane

/-!
A uniform obstruction to cubic-norm weighted graphs on the noncommutative
binary Heisenberg group, for EVERY linear identification with a cubic field.
This does not settle Erdős Problem 714.
-/
noncomputable section
open SimpleGraph Classical
open scoped CharTwo
set_option maxHeartbeats 4000000
namespace Erdos714HeisenbergCubicNorm

@[ext] structure Heis (F : Type*) where
  x : F
  y : F
  z : F
  deriving Fintype, DecidableEq

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The genuine noncommutative group law, with its cross term retained. -/
instance heisMul : Mul (Heis F) := ⟨fun a b => ⟨a.x+b.x,a.y+b.y,a.z+b.z+a.x*b.y⟩⟩
instance heisOne : One (Heis F) := ⟨⟨0,0,0⟩⟩
instance heisInv : Inv (Heis F) := ⟨fun a => ⟨-a.x,-a.y,-a.z+a.x*a.y⟩⟩

instance : Group (Heis F) where
  mul_assoc a b c := by
    apply Heis.ext
    · change (a.x+b.x)+c.x = a.x+(b.x+c.x); ring
    · change (a.y+b.y)+c.y = a.y+(b.y+c.y); ring
    · change (a.z+b.z+a.x*b.y)+c.z+(a.x+b.x)*c.y =
        a.z+(b.z+c.z+b.x*c.y)+a.x*(b.y+c.y)
      ring
  one_mul a := by
    apply Heis.ext
    · change 0+a.x=a.x; ring
    · change 0+a.y=a.y; ring
    · change 0+a.z+0*a.y=a.z; ring
  mul_one a := by
    apply Heis.ext
    · change a.x+0=a.x; ring
    · change a.y+0=a.y; ring
    · change a.z+0+a.x*0=a.z; ring
  inv_mul_cancel a := by
    apply Heis.ext
    · change -a.x+a.x=0; ring
    · change -a.y+a.y=0; ring
    · change (-a.z+a.x*a.y)+a.z+(-a.x)*a.y=0; ring

def coords : Heis F ≃ (F × F × F) where
  toFun a := (a.x,a.y,a.z)
  invFun a := ⟨a.1,a.2.1,a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨x,y,z⟩; rfl

variable (b : (F × F × F) ≃ₗ[F] E)

def value (a : Heis F) : E := b (coords a)
def fromE (t : E) : Heis F := coords.symm (b.symm t)

lemma value_fromE (t : E) : value b (fromE b t) = t := by simp [value,fromE]
lemma fromE_injective : Function.Injective (fromE b) := coords.symm.injective.comp b.symm.injective
lemma value_one : value b 1 = 0 := by change b 0=0; exact b.map_zero
lemma value_injective : Function.Injective (value b) := b.injective.comp coords.injective

/-- The exact point at which the noncommutative cross term vanishes. This
is asserted only for a left factor with first coordinate zero. -/
lemma value_inv_mul [CharP F 2] (a c : Heis F) (ha : a.x=0) :
    value b (a⁻¹*c) = value b a+value b c := by
  have he : coords (a⁻¹*c) = coords a+coords c := by
    change (-a.x+c.x,-a.y+c.y,(-a.z+a.x*a.y)+c.z+(-a.x)*c.y) =
      (a.x+c.x,a.y+c.y,a.z+c.z)
    simp [ha]
  exact (congrArg b he).trans (b.map_add _ _)

def relation (a c : Heis F × Fˣ) : Prop :=
  Algebra.norm F (value b (a.1⁻¹*c.1)) = (a.2:F)*(c.2:F)

def graph : SimpleGraph ((Heis F × Fˣ) ⊕ (Heis F × Fˣ)) where
  Adj a c := match a,c with
    | .inl a,.inr c => relation b a c
    | .inr c,.inl a => relation b a c
    | _,_ => False
  symm := by intro a c h; cases a <;> cases c <;> exact h
  loopless := by intro a; cases a <;> simp

/-- The coordinate hyperplane used by the abelian subgroup. -/
def firstCoordinate : E →ₗ[F] F :=
  (LinearMap.fst F F (F × F)).comp b.symm.toLinearMap

lemma fromE_first (t : E) : (fromE b t).x = firstCoordinate b t := rfl

/-- The copy uses a norm-constant plane in the actual Heisenberg relative
product; it does not replace the group law globally by addition. -/
def planeCopy [CharP F 2] [CharP E 2] (p u v : E)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hlu : firstCoordinate b u=0) (hlv : firstCoordinate b v=0)
    (hp : Algebra.norm F p ≠ 0)
    (hn : ∀ i, Algebra.norm F (p+Erdos714BinaryLift.plane u v i)=Algebra.norm F p) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph b) := by
  let P := Erdos714BinaryLift.plane u v
  have hP : Function.Injective P := Erdos714BinaryLift.plane_injective hu hv huv
  have hzero (i : Fin 4) : firstCoordinate b (P i)=0 := by
    fin_cases i <;> simp [P,Erdos714BinaryLift.plane,hlu,hlv]
  let d : Fˣ := Units.mk0 (Algebra.norm F p) hp
  let L : Fin 4 → Heis F × Fˣ := fun i => (fromE b (P i),1)
  let R : Fin 4 → Heis F × Fˣ := fun i => (fromE b (p+P i),d)
  have hL : Function.Injective L := by
    intro i j hij
    exact hP (fromE_injective b (congrArg Prod.fst hij))
  have hR : Function.Injective R := by
    intro i j hij
    exact hP (add_left_cancel (fromE_injective b (congrArg Prod.fst hij)))
  have hedge (i j : Fin 4) : relation b (L i) (R j) := by
    change Algebra.norm F (value b ((fromE b (P i))⁻¹*fromE b (p+P j))) =
      1*Algebra.norm F p
    rw [value_inv_mul b _ _ (by rw [fromE_first]; exact hzero i),
      value_fromE,value_fromE,one_mul]
    obtain ⟨k,hk⟩ := Erdos714BinaryLift.plane_closed u v i j
    rw [add_left_comm]
    exact (congrArg (fun x => Algebra.norm F (p+x)) hk).trans (hn k)
  refine ⟨⟨Sum.map L R,?_⟩,Sum.map_injective.mpr ⟨hL,hR⟩⟩
  intro a c hac
  cases a with
  | inl i => cases c with
    | inl j => simp at hac
    | inr j => exact hedge i j
  | inr i => cases c with
    | inl j => exact hedge j i
    | inr j => simp at hac

/-- No choice of cubic-field basis rescues this noncommutative weighted
norm construction in characteristic two. -/
theorem not_free [Fintype F] [Fintype E] [CharP F 2]
    (hdim : Module.finrank F E = 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph b) := by
  letI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  obtain ⟨p,u,v,hu,hv,huv,hlu,hlv,hp,hn⟩ :=
    Erdos714CubicTraceNormPlane.exists_plane_in_kernel hdim (firstCoordinate b)
  exact fun hf => hf ⟨planeCopy b p u v hu hv huv hlu hlv hp hn⟩


lemma fromE_value (a : Heis F) : fromE b (value b a)=a := by simp [fromE,value]

/-- One neighbor for every nonzero relative displacement. -/
def partner (a : Heis F × Fˣ) (z : Eˣ) : Heis F × Fˣ :=
  (a.1*fromE b z, Units.map (Algebra.norm F) z / a.2)

lemma partner_adj (a : Heis F × Fˣ) (z : Eˣ) : relation b a (partner b a z) := by
  simp only [relation,partner,inv_mul_cancel_left,value_fromE,Units.val_div_eq_div_val,Units.coe_map]
  rw [mul_comm,div_mul_cancel₀ _ a.2.ne_zero]

lemma partner_injective (a : Heis F × Fˣ) : Function.Injective (partner b a) := by
  intro z w h
  apply Units.ext
  exact fromE_injective b (mul_left_cancel (congrArg Prod.fst h))

lemma relation_partner (a c : Heis F × Fˣ) (h : relation b a c) :
    ∃ z : Eˣ, c=partner b a z := by
  letI : FiniteDimensional F E := b.finiteDimensional
  have hz : value b (a.1⁻¹*c.1) ≠ 0 := by
    apply (Algebra.norm_ne_zero_iff (R := F)).mp
    change Algebra.norm F (value b (a.1⁻¹*c.1)) ≠ 0
    rw [h]
    exact mul_ne_zero a.2.ne_zero c.2.ne_zero
  let z : Eˣ := Units.mk0 (value b (a.1⁻¹*c.1)) hz
  refine ⟨z,?_⟩
  apply Prod.ext
  · change c.1=a.1*fromE b (value b (a.1⁻¹*c.1))
    rw [fromE_value,mul_inv_cancel_left]
  · apply Units.ext
    change (c.2:F)=((Units.map (Algebra.norm F) z / a.2 : Fˣ):F)
    rw [Units.val_div_eq_div_val]
    change (c.2:F)=(Algebra.norm F (value b (a.1⁻¹*c.1)))/(a.2:F)
    rw [h,mul_div_cancel_left₀ _ a.2.ne_zero]

/-- Exact edge parametrization, with the original noncommutative relative
product and the original nonzero norm weights. -/
def edgeEquiv : ((Heis F × Fˣ) × Eˣ) ≃ (graph b).edgeSet := by
  let f : ((Heis F × Fˣ) × Eˣ) → (graph b).edgeSet := fun az =>
    ⟨s(Sum.inl az.1,Sum.inr (partner b az.1 az.2)),partner_adj b az.1 az.2⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨a,z⟩ ⟨c,w⟩ h
    have he := Sym2.eq_iff.mp (congrArg Subtype.val h)
    rcases he with ⟨ha,hc⟩ | ⟨ha,hc⟩
    · have hac : a=c := Sum.inl.inj ha
      subst c
      exact Prod.ext rfl (partner_injective b a (Sum.inr.inj hc))
    · exact False.elim (Sum.inl_ne_inr ha)
  · rintro ⟨e,he⟩
    induction e using Sym2.ind with
    | _ a c =>
      cases a with
      | inl a => cases c with
        | inl c => exact False.elim he
        | inr c =>
          obtain ⟨z,hz⟩ := relation_partner b a c he
          exact ⟨(a,z),Subtype.ext (by change s(Sum.inl a,Sum.inr (partner b a z))=s(Sum.inl a,Sum.inr c); rw [hz])⟩
      | inr a => cases c with
        | inr c => exact False.elim he
        | inl c =>
          obtain ⟨z,hz⟩ := relation_partner b c a he
          exact ⟨(c,z),Subtype.ext (by change s(Sum.inl c,Sum.inr (partner b c z))=s(Sum.inr a,Sum.inl c); rw [hz,Sym2.eq_swap])⟩

/-- The candidate has precisely the desired vertex scale. -/
theorem vertex_count [Fintype F] :
    Fintype.card ((Heis F × Fˣ) ⊕ (Heis F × Fˣ)) =
      2*(Fintype.card F)^3*(Fintype.card F-1) := by
  have hc : Fintype.card (Heis F)=(Fintype.card F)^3 := by
    rw [Fintype.card_congr (coords (F := F))]
    simp only [Fintype.card_prod]
    ring
  rw [Fintype.card_sum,Fintype.card_prod,hc,Fintype.card_units]
  ring

/-- Its edge count is also of the target order q^7; the obstruction is
freeness, not a missing density estimate. -/
theorem edge_count [Fintype F] [Fintype E] (hdim : Module.finrank F E=3) :
    (graph b).edgeFinset.card = (Fintype.card F)^3*(Fintype.card F-1)*((Fintype.card F)^3-1) := by
  have hc : Fintype.card (Heis F)=(Fintype.card F)^3 := by
    rw [Fintype.card_congr (coords (F := F))]
    simp only [Fintype.card_prod]
    ring
  rw [← SimpleGraph.card_edgeSet,← Fintype.card_congr (edgeEquiv b)]
  simp only [Fintype.card_prod,Fintype.card_units,hc,
    Module.card_eq_pow_finrank (K := F) (V := E),hdim]

#print axioms edgeEquiv
#print axioms vertex_count
#print axioms edge_count

#print axioms value_inv_mul
#print axioms planeCopy
#print axioms not_free
end Erdos714HeisenbergCubicNorm
