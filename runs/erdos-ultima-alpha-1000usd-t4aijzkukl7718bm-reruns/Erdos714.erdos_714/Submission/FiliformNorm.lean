import Submission.OddCubicNormGrid

/-! A class-three nilpotent cubic-norm construction has the critical counts,
but contains K44. This is not a disproof of Erdős 714. -/
noncomputable section
open Classical SimpleGraph
namespace Erdos714FiliformNorm

@[ext] structure Root (F : Type*) where
  x : F
  y : F
  z : F
  w : F
  deriving Fintype, DecidableEq

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

instance : Mul (Root F) := ⟨fun a b =>
  ⟨a.x+b.x,a.y+b.y,a.z+b.z+a.x*b.y,a.w+b.w+a.x*b.z+a.x^2*b.y/2⟩⟩
instance : One (Root F) := ⟨⟨0,0,0,0⟩⟩
instance : Inv (Root F) := ⟨fun a =>
  ⟨-a.x,-a.y,-a.z+a.x*a.y,-a.w+a.x*a.z-a.x^2*a.y/2⟩⟩

instance [NeZero (2 : F)] : Group (Root F) where
  mul_assoc a b c := by
    apply Root.ext
    · change (a.x+b.x)+c.x=a.x+(b.x+c.x); ring
    · change (a.y+b.y)+c.y=a.y+(b.y+c.y); ring
    · change (a.z+b.z+a.x*b.y)+c.z+(a.x+b.x)*c.y=
        a.z+(b.z+c.z+b.x*c.y)+a.x*(b.y+c.y)
      ring
    · change (a.w+b.w+a.x*b.z+a.x^2*b.y/2)+c.w+(a.x+b.x)*c.z+
        (a.x+b.x)^2*c.y/2 = a.w+(b.w+c.w+b.x*c.z+b.x^2*c.y/2)+
          a.x*(b.z+c.z+b.x*c.y)+a.x^2*(b.y+c.y)/2
      field_simp
      ring
  one_mul a := by
    apply Root.ext
    · change 0+a.x=a.x; ring
    · change 0+a.y=a.y; ring
    · change 0+a.z+0*a.y=a.z; ring
    · change 0+a.w+0*a.z+0^2*a.y/2=a.w; ring
  mul_one a := by
    apply Root.ext
    · change a.x+0=a.x; ring
    · change a.y+0=a.y; ring
    · change a.z+0+a.x*0=a.z; ring
    · change a.w+0+a.x*0+a.x^2*0/2=a.w; ring
  inv_mul_cancel a := by
    apply Root.ext
    · change -a.x+a.x=0; ring
    · change -a.y+a.y=0; ring
    · change (-a.z+a.x*a.y)+a.z+(-a.x)*a.y=0; ring
    · change (-a.w+a.x*a.z-a.x^2*a.y/2)+a.w+(-a.x)*a.z+(-a.x)^2*a.y/2=0
      ring

def coords : Root F ≃ F × F × F × F where
  toFun a := (a.x,a.y,a.z,a.w)
  invFun a := ⟨a.1,a.2.1,a.2.2.1,a.2.2.2⟩
  left_inv := by intro a; rfl
  right_inv := by intro a; rfl

variable (b : (F × F × F) ≃ₗ[F] E)

def point (g : Root F) : E := b (g.x,g.y,g.z)
def lift (e : E) (w : F) : Root F :=
  ⟨(b.symm e).1,(b.symm e).2.1,(b.symm e).2.2,w⟩

@[simp] lemma point_lift (e : E) (w : F) : point b (lift b e w) = e := by
  simp [point,lift]

@[simp] lemma lift_point (g : Root F) : lift b (point b g) g.w = g := by
  simp [point,lift]

@[simp] lemma lift_w (e : E) (w : F) : (lift b e w).w=w := rfl

lemma lift_injective (w : F) : Function.Injective (fun e => lift b e w) := by
  intro e f h
  simpa using congrArg (point b) h

def coordinate : E →ₗ[F] F := (LinearMap.fst F F (F × F)).comp b.symm.toLinearMap

/-- Only when the left first coordinate vanishes is the relative product
ordinary subtraction. Both the point and the central coordinate are retained. -/
lemma relative_in_kernel (g h : Root F) (hx : g.x=0) :
    point b (g⁻¹*h) = point b h-point b g ∧ (g⁻¹*h).w=h.w-g.w := by
  constructor
  · change b (-g.x+h.x,-g.y+h.y,-g.z+g.x*g.y+h.z+(-g.x)*h.y)=_
    change b (-g.x+h.x,-g.y+h.y,-g.z+g.x*g.y+h.z+(-g.x)*h.y)=
      b (h.x,h.y,h.z)-b (g.x,g.y,g.z)
    rw [← map_sub b]
    congr 1
    simp [hx,sub_eq_add_neg,add_comm]
  · change -g.w+g.x*g.z-g.x^2*g.y/2+h.w+(-g.x)*h.z+(-g.x)^2*h.y/2=_
    simp [hx,sub_eq_add_neg,add_comm]

def relation (g h : Root F) : Prop :=
  Algebra.norm F (point b (g⁻¹*h)) = (g⁻¹*h).w

def graph : SimpleGraph (Root F ⊕ Root F) where
  Adj p q := match p,q with
    | .inl g,.inr h => relation b g h
    | .inr h,.inl g => relation b g h
    | _,_ => False
  symm := by intro p q; cases p <;> cases q <;> simp_all
  loopless := by intro p; cases p <;> simp

/-- No basis is singled out: scaling the cubic-norm grid aligns all four
rows with the translation subgroup of this actual noncommutative group. -/
theorem not_free [Fintype F] [Fintype E]
    (hdim : Module.finrank F E=3) (h2 : (2:F)≠0) (h3 : (3:F)≠0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph b) := by
  obtain ⟨d,hd,L,R,hL,hN⟩ :=
    Erdos714OddCubicNormGrid.exists_grid_in_kernel hdim h2 h3 (coordinate b)
  let v : Fin 4 → F := ![d,d,-d,-d]
  let rows : Fin 4 → Root F := fun i => lift b (-L i) (-v i)
  let cols : Fin 4 → Root F := fun j => lift b (R j) 0
  have hx (i : Fin 4) : (rows i).x=0 := by
    change (b.symm (-L i)).1=0
    change coordinate b (-L i)=0
    rw [map_neg,hL,neg_zero]
  have hi : Function.Injective rows := by
    intro i j hij
    have he := congrArg (point b) hij
    have he' : -L i = -L j := by simpa [rows] using he
    exact L.injective (neg_injective he')
  have hj : Function.Injective cols := (lift_injective b 0).comp R.injective
  have hedge (i j : Fin 4) : relation b (rows i) (cols j) := by
    obtain ⟨he,hw⟩ := relative_in_kernel b (rows i) (cols j) (hx i)
    unfold relation
    rw [he,hw]
    simpa [rows,cols,v,add_comm] using hN i j
  let le : Fin 4 ↪ Root F := ⟨rows,hi⟩
  let re : Fin 4 ↪ Root F := ⟨cols,hj⟩
  intro hfree
  apply hfree
  refine ⟨⟨⟨le.sumMap re,?_⟩,(le.sumMap re).injective⟩⟩
  intro p q hpq
  cases p with
  | inl i => cases q with
    | inl k => simp at hpq
    | inr j => exact hedge i j
  | inr j => cases q with
    | inl i => exact hedge i j
    | inr k => simp at hpq

/-- In characteristic three the obstruction is even larger: the cubic norm
on a scalar line is additive, giving a whole q-by-q grid. -/
def charThreeCopy [CharP F 3] (hdim : Module.finrank F E=3) :
    Copy (completeBipartiteGraph F F) (graph b) := by
  let u : E := b (0,1,0)
  let g (t : F) : Root F := ⟨0,t,0,t^3*Algebra.norm F u⟩
  have hg (t : F) : point b (g t)=algebraMap F E t*u := by
    change b (0,t,0)=algebraMap F E t*b (0,1,0)
    rw [← Algebra.smul_def,← b.map_smul]
    congr 1
    simp
  have hi : Function.Injective g := fun s t h => congrArg Root.y h
  let e : F ↪ Root F := ⟨g,hi⟩
  have he (s t : F) : relation b (g s) (g t) := by
    obtain ⟨hp,hw⟩ := relative_in_kernel b (g s) (g t) rfl
    unfold relation
    rw [hp,hw,hg,hg,← sub_mul,← map_sub,map_mul,Algebra.norm_algebraMap,hdim]
    change (t-s)^3*Algebra.norm F u=t^3*Algebra.norm F u-s^3*Algebra.norm F u
    rw [sub_pow_char]
    ring
  refine ⟨⟨e.sumMap e,?_⟩,(e.sumMap e).injective⟩
  intro p q hpq
  cases p with
  | inl s => cases q with
    | inl t => simp at hpq
    | inr t => exact he s t
  | inr t => cases q with
    | inl s => exact he s t
    | inr s => simp at hpq

theorem charThree_not_free [Fintype F] [CharP F 3]
    (hdim : Module.finrank F E=3) (hq : 4 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph b) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := F) (by simpa using hq)
  let c : Copy (completeBipartiteGraph (Fin 4) (Fin 4))
      (completeBipartiteGraph F F) :=
    ⟨⟨e.sumMap e,by intro p q hpq; cases p <;> cases q <;> simp_all⟩,
      (e.sumMap e).injective⟩
  exact fun h => h ⟨(charThreeCopy b hdim).comp c⟩

variable [NeZero (2 : F)]

/-- One neighbor for each field point, including zero. -/
def partner (g : Root F) (e : E) : Root F := g*lift b e (Algebra.norm F e)

lemma partner_adj (g : Root F) (e : E) : relation b g (partner b g e) := by
  simp only [relation,partner,inv_mul_cancel_left,point_lift,lift_w]

lemma partner_injective (g : Root F) : Function.Injective (partner b g) := by
  intro e f h
  have he := mul_left_cancel h
  simpa using congrArg (point b) he

lemma relation_partner (g h : Root F) (hr : relation b g h) :
    ∃ e : E, h=partner b g e := by
  refine ⟨point b (g⁻¹*h),?_⟩
  unfold partner
  rw [show Algebra.norm F (point b (g⁻¹*h))=(g⁻¹*h).w from hr,lift_point,
    mul_inv_cancel_left]

def edgeEquiv : (Root F × E) ≃ (graph b).edgeSet := by
  let f : (Root F × E) → (graph b).edgeSet := fun ge =>
    ⟨s(Sum.inl ge.1,Sum.inr (partner b ge.1 ge.2)),partner_adj b ge.1 ge.2⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨g,e⟩ ⟨h,k⟩ he
    rcases Sym2.eq_iff.mp (congrArg Subtype.val he) with ⟨hg,hh⟩ | ⟨hg,hh⟩
    · have hgh : g=h := Sum.inl.inj hg
      subst h
      exact Prod.ext rfl (partner_injective b g (Sum.inr.inj hh))
    · exact False.elim (Sum.inl_ne_inr hg)
  · rintro ⟨e,he⟩
    induction e using Sym2.ind with
    | _ g h =>
      cases g with
      | inl g => cases h with
        | inl h => exact False.elim he
        | inr h =>
          obtain ⟨z,hz⟩ := relation_partner b g h he
          exact ⟨(g,z),Subtype.ext (by change s(Sum.inl g,Sum.inr (partner b g z))=s(Sum.inl g,Sum.inr h); rw [hz])⟩
      | inr g => cases h with
        | inr h => exact False.elim he
        | inl h =>
          obtain ⟨z,hz⟩ := relation_partner b h g he
          exact ⟨(h,z),Subtype.ext (by change s(Sum.inl h,Sum.inr (partner b h z))=s(Sum.inr g,Sum.inl h); rw [hz,Sym2.eq_swap])⟩

omit [NeZero (2 : F)] [Field F] in
lemma root_card [Fintype F] : Fintype.card (Root F)=(Fintype.card F)^4 := by
  rw [Fintype.card_congr (coords (F := F))]
  simp only [Fintype.card_prod]
  ring

omit [NeZero (2 : F)] [Field F] in
theorem vertex_count [Fintype F] :
    Fintype.card (Root F ⊕ Root F)=2*(Fintype.card F)^4 := by
  rw [Fintype.card_sum,root_card]
  ring

theorem edge_count [Fintype F] [Fintype E] (hdim : Module.finrank F E=3) :
    (graph b).edgeFinset.card=(Fintype.card F)^7 := by
  rw [← SimpleGraph.card_edgeSet,← Fintype.card_congr (edgeEquiv b)]
  simp only [Fintype.card_prod,root_card,
    Module.card_eq_pow_finrank (K := F) (V := E),hdim]
  ring

end Erdos714FiliformNorm
#print axioms Erdos714FiliformNorm.relative_in_kernel
#print axioms Erdos714FiliformNorm.not_free
#print axioms Erdos714FiliformNorm.edgeEquiv
#print axioms Erdos714FiliformNorm.vertex_count
#print axioms Erdos714FiliformNorm.edge_count

#print axioms Erdos714FiliformNorm.charThreeCopy
#print axioms Erdos714FiliformNorm.charThree_not_free
