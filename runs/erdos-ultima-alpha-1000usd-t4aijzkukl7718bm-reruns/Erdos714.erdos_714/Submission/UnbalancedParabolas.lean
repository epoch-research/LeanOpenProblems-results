import Submission.Packing

/-! A positive, but unbalanced, K44-free incidence construction.
The first chart has q^3*(q-1) parabolas. The full two-chart family has
q^4-q^2 parabolas and q^2 points; every parabola has q points. This does
not provide the balanced lower bound in Erdős 714. -/

set_option maxHeartbeats 3000000
noncomputable section
open Classical Polynomial Finset SimpleGraph
namespace Erdos714Parabolas
variable {F : Type*} [Field F]

@[ext] structure Parabola (F : Type*) [Field F] where
  m : F
  b : F
  c : F
  d : Fˣ
  deriving Fintype

/-- A chart of the family of nondegenerate affine parabolas. -/
def On (r : Parabola F) (p : F × F) : Prop :=
  (r.d : F)*p.1 = (r.m*p.1+p.2)^2-r.b*(r.m*p.1+p.2)-r.c

def parameter (r : Parabola F) (p : F × F) : F := r.m*p.1+p.2

def point (r : Parabola F) (t : F) : F × F :=
  let x := (t^2-r.b*t-r.c)/(r.d : F)
  (x,t-r.m*x)

@[simp] lemma parameter_point (r : Parabola F) (t : F) : parameter r (point r t)=t := by
  dsimp [parameter,point]; ring

lemma point_on (r : Parabola F) (t : F) : On r (point r t) := by
  change (r.d : F)*(point r t).1 = (parameter r (point r t))^2-
    r.b*parameter r (point r t)-r.c
  rw [parameter_point]
  dsimp [point]
  field_simp

lemma point_parameter (r : Parabola F) (p : F × F) (hp : On r p) :
    point r (parameter r p)=p := by
  have hx : (parameter r p^2-r.b*parameter r p-r.c)/(r.d : F)=p.1 := by
    apply (div_eq_iff (Units.ne_zero r.d)).mpr
    exact hp.symm.trans (mul_comm _ _)
  apply Prod.ext
  · exact hx
  · change parameter r p-r.m*((parameter r p^2-r.b*parameter r p-r.c)/(r.d : F))=p.2
    rw [hx]
    dsimp [parameter]; ring

lemma parameter_injective_on (r : Parabola F) {p q : F × F} (hp : On r p) (hq : On r q)
    (he : parameter r p=parameter r q) : p=q := by
  rw [←point_parameter r p hp,←point_parameter r q hq,he]

lemma cubic_coefficients (t : Fin 4 ↪ F) (a b c d : F)
    (h : ∀ i, a*t i^3+b*t i^2+c*t i+d=0) : a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  let P : F[X] := C a*X^3+C b*X^2+C c*X+C d
  have hP : P=0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P t.injective
    · intro i; simpa [P] using h i
    · have hd : P.natDegree ≤ 3 := by dsimp [P]; compute_degree!
      simpa using Nat.lt_succ_of_le hd
  have ha := congrArg (fun p : F[X] => p.coeff 3) hP
  have hb := congrArg (fun p : F[X] => p.coeff 2) hP
  have hc := congrArg (fun p : F[X] => p.coeff 1) hP
  have hd := congrArg (fun p : F[X] => p.coeff 0) hP
  simpa [P,coeff_add,coeff_C_mul_X_pow] using And.intro ha (And.intro hb (And.intro hc hd))

/-- A line cannot contain four distinct points of a nondegenerate parabola. -/
lemma linear_values_unique (r : Parabola F) (p : Fin 4 ↪ F × F)
    (hp : ∀ i, On r (p i)) (a b c : F)
    (hl : ∀ i, a*(p i).1+b*parameter r (p i)+c=0) : a=0 ∧ b=0 ∧ c=0 := by
  let t : Fin 4 ↪ F := ⟨fun i => parameter r (p i),by
    intro i j hij
    exact p.injective (parameter_injective_on r (hp i) (hp j) hij)⟩
  have hh (i : Fin 4) : (0:F)*t i^3+a*t i^2+
      ((r.d : F)*b-a*r.b)*t i+((r.d : F)*c-a*r.c)=0 := by
    have he := hp i
    change (r.d : F)*(p i).1 = parameter r (p i)^2-r.b*parameter r (p i)-r.c at he
    dsimp [t]
    linear_combination (r.d : F)*hl i-a*he
  obtain ⟨_,ha,hb,hc⟩ := cubic_coefficients t _ _ _ _ hh
  refine ⟨ha,?_,?_⟩
  · simpa [ha,Units.ne_zero r.d] using hb
  · simpa [ha,Units.ne_zero r.d] using hc

lemma same_slope_unique (r₀ r s : Parabola F) (p : Fin 4 ↪ F × F)
    (h₀ : ∀ i, On r₀ (p i)) (hr : ∀ i, On r (p i)) (hs : ∀ i, On s (p i))
    (hm : r.m=s.m) : r=s := by
  have hl (i : Fin 4) :
      (((r.d : F)-(s.d : F))+(r.b-s.b)*(r.m-r₀.m))*(p i).1+
        (r.b-s.b)*parameter r₀ (p i)+(r.c-s.c)=0 := by
    have hri := hr i
    have hsi := hs i
    dsimp [On] at hri hsi
    rw [←hm] at hsi
    dsimp [parameter]
    linear_combination hri-hsi
  obtain ⟨hd,hb,hc⟩ := linear_values_unique r₀ p h₀ _ _ _ hl
  have hb' : r.b=s.b := sub_eq_zero.mp hb
  have hc' : r.c=s.c := sub_eq_zero.mp hc
  have hd' : r.d=s.d := Units.ext (sub_eq_zero.mp (by simpa [hb'] using hd))
  exact Parabola.ext hm hb' hc' hd'

/-- Coefficients of the intersection polynomial after parametrizing the first parabola. -/
def coef (r₀ r : Parabola F) : Fin 5 → F :=
  let h := r.m-r₀.m
  let D := (r₀.d : F)
  ![h^2*r₀.c^2+r.b*D*h*r₀.c-r.c*D^2+(r.d : F)*D*r₀.c,
    -2*h*r₀.c*(D-h*r₀.b)-r.b*D*(D-h*r₀.b)+(r.d : F)*D*r₀.b,
    (D-h*r₀.b)^2-2*h^2*r₀.c-r.b*D*h-(r.d : F)*D,
    2*h*D-2*h^2*r₀.b,h^2]

lemma intersection_value (r₀ r : Parabola F) (p : F × F)
    (h₀ : On r₀ p) (hr : On r p) :
    coef r₀ r 4 * parameter r₀ p^4 + coef r₀ r 3 * parameter r₀ p^3 +
    coef r₀ r 2 * parameter r₀ p^2 + coef r₀ r 1 * parameter r₀ p + coef r₀ r 0=0 := by
  let t := parameter r₀ p
  let h := r.m-r₀.m
  let D := (r₀.d : F)
  have hx : D*p.1=t^2-r₀.b*t-r₀.c := h₀
  have ht : r.m*p.1+p.2=t+h*p.1 := by dsimp [t,h,parameter]; ring
  have hh : (D*t+h*(t^2-r₀.b*t-r₀.c))^2-
      r.b*D*(D*t+h*(t^2-r₀.b*t-r₀.c))-r.c*D^2-
      (r.d : F)*D*(t^2-r₀.b*t-r₀.c)=0 := by
    rw [←hx]
    change (r.d : F)*p.1=(r.m*p.1+p.2)^2-r.b*(r.m*p.1+p.2)-r.c at hr
    rw [ht] at hr
    linear_combination -D^2*hr
  dsimp [coef]
  dsimp [t,h,D] at hh
  linear_combination hh

/-- Apart from a chosen parabola, at most one other normalized parabola can
pass through the same four distinct points. -/
lemma other_unique (h₂ : (2:F) ≠ 0) (r₀ r s : Parabola F) (p : Fin 4 ↪ F × F)
    (h₀ : ∀ i, On r₀ (p i)) (hr : ∀ i, On r (p i)) (hs : ∀ i, On s (p i))
    (hr₀ : r ≠ r₀) (hs₀ : s ≠ r₀) : r=s := by
  have hm₁ : r.m-r₀.m ≠ 0 := by
    intro h
    exact hr₀ (same_slope_unique r₀ r r₀ p h₀ hr h₀ (sub_eq_zero.mp h))
  have hm₂ : s.m-r₀.m ≠ 0 := by
    intro h
    exact hs₀ (same_slope_unique r₀ s r₀ p h₀ hs h₀ (sub_eq_zero.mp h))
  let t : Fin 4 ↪ F := ⟨fun i => parameter r₀ (p i),by
    intro i j hij
    exact p.injective (parameter_injective_on r₀ (h₀ i) (h₀ j) hij)⟩
  let A (j : Fin 5) := (s.m-r₀.m)^2*coef r₀ r j-(r.m-r₀.m)^2*coef r₀ s j
  have hz (i : Fin 4) : A 3*t i^3+A 2*t i^2+A 1*t i+A 0=0 := by
    have hri := intersection_value r₀ r (p i) (h₀ i) (hr i)
    have hsi := intersection_value r₀ s (p i) (h₀ i) (hs i)
    have he₁ : coef r₀ r 4=(r.m-r₀.m)^2 := rfl
    have he₂ : coef r₀ s 4=(s.m-r₀.m)^2 := rfl
    rw [he₁] at hri
    rw [he₂] at hsi
    dsimp [A,t]
    linear_combination (s.m-r₀.m)^2*hri-(r.m-r₀.m)^2*hsi
  have htop := (cubic_coefficients t _ _ _ _ hz).1
  have hh : 2*(r₀.d : F)*(r.m-r₀.m)*(s.m-r₀.m)*(s.m-r.m)=0 := by
    dsimp [A,coef] at htop
    linear_combination htop
  have hn : 2*(r₀.d : F)*(r.m-r₀.m)*(s.m-r₀.m) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h₂ (Units.ne_zero r₀.d)) hm₁) hm₂
  have hm : r.m=s.m := (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hn)).symm
  exact same_slope_unique r₀ r s p h₀ hr hs hm


variable [Fintype F]

def points (r : Parabola F) : Finset (F × F) := univ.image (point r)

@[simp] lemma mem_points (r : Parabola F) (p : F × F) : p ∈ points r ↔ On r p := by
  constructor
  · intro hp
    obtain ⟨t,_,rfl⟩ := mem_image.mp hp
    exact point_on r t
  · intro hp
    exact mem_image.mpr ⟨parameter r p,mem_univ _,point_parameter r p hp⟩

lemma points_card (r : Parabola F) : (points r).card=Fintype.card F := by
  rw [points,card_image_of_injective,card_univ]
  intro a b hab
  simpa using congrArg (parameter r) hab

lemma row_card : Fintype.card (Parabola F) = Fintype.card F^3*(Fintype.card F-1) := by
  let e : Parabola F ≃ F × F × F × Fˣ :=
    ⟨fun r => (r.m,r.b,r.c,r.d), fun r => ⟨r.1,r.2.1,r.2.2.1,r.2.2.2⟩,
      by intro r; cases r; rfl,by intro r; rfl⟩
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod,Fintype.card_units]
  ring

/-- Four distinct points lie on at most two parabolas in this chart. -/
theorem four_point_bound (h₂ : (2:F) ≠ 0) (p : Fin 4 ↪ F × F) :
    (univ.filter (fun r : Parabola F => ∀ i, On r (p i))).card ≤ 2 := by
  by_contra! hcard
  obtain ⟨r₀,r,s,hr₀,hr,hs,hr₀r,hr₀s,hrs⟩ := Finset.two_lt_card_iff.mp hcard
  have h₀ := (mem_filter.mp hr₀).2
  have hr' := (mem_filter.mp hr).2
  have hs' := (mem_filter.mp hs).2
  exact hrs (other_unique h₂ r₀ r s p h₀ hr' hs' hr₀r.symm hr₀s.symm)

def graph : SimpleGraph (Parabola F ⊕ (F × F)) := Erdos714Packing.incidence points

theorem graph_free (h₂ : (2:F) ≠ 0) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F)) := by
  apply (Erdos714Packing.free_iff_no_rectangle points (by decide : 0 < 4)).mpr
  intro f p hp
  have hb := other_unique h₂ (f 0) (f 1) (f 2) p
    (fun i => (mem_points _ _).mp (hp 0 i))
    (fun i => (mem_points _ _).mp (hp 1 i))
    (fun i => (mem_points _ _).mp (hp 2 i))
    (f.injective.ne (by decide)) (f.injective.ne (by decide))
  exact (by decide : (1:Fin 4) ≠ 2) (f.injective hb)

theorem edge_count : (graph (F := F)).edgeFinset.card =
    Fintype.card F^4*(Fintype.card F-1) := by
  rw [graph,Erdos714Packing.incidence_edges]
  simp only [points_card,sum_const,card_univ,smul_eq_mul,row_card]
  ring

theorem vertex_count : Fintype.card (Parabola F ⊕ (F × F)) =
    Fintype.card F^3*(Fintype.card F-1)+Fintype.card F^2 := by
  simp only [Fintype.card_sum,Fintype.card_prod,row_card,pow_two]


/-- The remaining direction chart. -/
@[ext] structure Vertical (F : Type*) [Field F] where
  b : F
  c : F
  d : Fˣ
  deriving Fintype

def Vertical.toParabola (v : Vertical F) : Parabola F := ⟨0,v.b,v.c,v.d⟩
def VOn (v : Vertical F) (p : F × F) : Prop :=
  (v.d : F)*p.2=p.1^2-v.b*p.1-v.c

omit [Fintype F] in
lemma vOn_iff (v : Vertical F) (p : F × F) : VOn v p ↔ On v.toParabola p.swap := by
  simp [VOn,On,Vertical.toParabola]

omit [Fintype F] in
lemma vertical_unique (v w : Vertical F) (p : Fin 4 ↪ F × F)
    (hv : ∀ i, VOn v (p i)) (hw : ∀ i, VOn w (p i)) : v=w := by
  let p' := p.trans (Equiv.prodComm F F).toEmbedding
  have hv' (i) : On v.toParabola (p' i) := (vOn_iff _ _).mp (hv i)
  have hw' (i) : On w.toParabola (p' i) := (vOn_iff _ _).mp (hw i)
  have he := same_slope_unique v.toParabola v.toParabola w.toParabola p' hv' hv' hw' rfl
  exact Vertical.ext (congrArg Parabola.b he) (congrArg Parabola.c he) (congrArg Parabola.d he)

omit [Fintype F] in
lemma vertical_parameter_injective (v : Vertical F) (p : Fin 4 ↪ F × F)
    (hv : ∀ i, VOn v (p i)) : Function.Injective (fun i => (p i).1) := by
  intro i j hij
  change (p i).1=(p j).1 at hij
  apply p.injective
  apply Prod.ext hij
  apply mul_left_cancel₀ (Units.ne_zero v.d)
  rw [hv i,hv j,hij]

omit [Fintype F] in
lemma vertical_intersection (v : Vertical F) (r : Parabola F) (p : F × F)
    (hv : VOn v p) (hr : On r p) :
    (p.1^2+((v.d : F)*r.m-v.b)*p.1-v.c)^2-
    r.b*(v.d : F)*(p.1^2+((v.d : F)*r.m-v.b)*p.1-v.c)-
    r.c*(v.d : F)^2-(r.d : F)*(v.d : F)^2*p.1=0 := by
  have he : p.1^2+((v.d : F)*r.m-v.b)*p.1-v.c=(v.d : F)*(r.m*p.1+p.2) := by
    dsimp [VOn] at hv
    linear_combination -hv
  rw [he]
  dsimp [On] at hr
  linear_combination -(v.d : F)^2*hr

omit [Fintype F] in
/-- Given a vertical-chart parabola, four of its points determine at most one
parabola in the other chart. -/
lemma vertical_other_unique (h₂ : (2:F) ≠ 0) (v : Vertical F) (r s : Parabola F)
    (p : Fin 4 ↪ F × F) (hv : ∀ i, VOn v (p i))
    (hr : ∀ i, On r (p i)) (hs : ∀ i, On s (p i)) : r=s := by
  let t : Fin 4 ↪ F := ⟨fun i => (p i).1,vertical_parameter_injective v p hv⟩
  let D := (v.d : F)
  let u := D*r.m-v.b
  let w := D*s.m-v.b
  have hz (i : Fin 4) :
      (2*(u-w))*t i^3+(u^2-w^2-D*(r.b-s.b))*t i^2+
      (-2*v.c*(u-w)-D*(r.b*u-s.b*w)-D^2*((r.d : F)-(s.d : F)))*t i+
      (D*v.c*(r.b-s.b)-D^2*(r.c-s.c))=0 := by
    have hri := vertical_intersection v r (p i) (hv i) (hr i)
    have hsi := vertical_intersection v s (p i) (hv i) (hs i)
    dsimp [t,u,w,D]
    linear_combination hri-hsi
  have ha := (cubic_coefficients t _ _ _ _ hz).1
  have hm : r.m=s.m := by
    have hh : 2*(v.d : F)*(r.m-s.m)=0 := by dsimp [u,w,D] at ha; linear_combination ha
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero h₂ (Units.ne_zero v.d)))
  exact same_slope_unique r r s p hr hr hs hm

def vPoints (v : Vertical F) : Finset (F × F) :=
  (points v.toParabola).map (Equiv.prodComm F F).toEmbedding

@[simp] lemma mem_vPoints (v : Vertical F) (p : F × F) : p ∈ vPoints v ↔ VOn v p := by
  rw [vOn_iff]
  constructor
  · intro hp
    obtain ⟨q,hq,he⟩ := mem_map.mp hp
    have hq' := (mem_points _ _).mp hq
    have hh : q=p.swap := by
      have hh := congrArg Prod.swap he
      simpa using hh
    rwa [hh] at hq'
  · intro hp
    exact mem_map.mpr ⟨p.swap,(mem_points _ _).mpr hp,by simp⟩

lemma vPoints_card (v : Vertical F) : (vPoints v).card=Fintype.card F := by
  rw [vPoints,card_map,points_card]

lemma vertical_card : Fintype.card (Vertical F) = Fintype.card F^2*(Fintype.card F-1) := by
  let e : Vertical F ≃ F × F × Fˣ :=
    ⟨fun r => (r.b,r.c,r.d),fun r => ⟨r.1,r.2.1,r.2.2⟩,
      by intro r; cases r; rfl,by intro r; rfl⟩
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod,Fintype.card_units]
  ring

abbrev FullRow (F : Type*) [Field F] := Parabola F ⊕ Vertical F

def fullPoints : FullRow F → Finset (F × F) := Sum.elim points vPoints

lemma fullPoints_card (r : FullRow F) : (fullPoints r).card=Fintype.card F := by
  cases r with
  | inl r => exact points_card r
  | inr v => exact vPoints_card v

/-- The full family, including both direction charts, has at most two members
through any four distinct affine points. -/
theorem full_four_point_bound (h₂ : (2:F) ≠ 0) (p : Fin 4 ↪ F × F) :
    (univ.filter (fun r : FullRow F => ∀ i, p i ∈ fullPoints r)).card ≤ 2 := by
  let S := univ.filter (fun r : Parabola F => ∀ i, On r (p i))
  let T := univ.filter (fun v : Vertical F => ∀ i, VOn v (p i))
  have he : univ.filter (fun r : FullRow F => ∀ i, p i ∈ fullPoints r)=S.disjSum T := by
    ext r
    cases r <;> simp [S,T,fullPoints]
  rw [he,card_disjSum]
  have hT : T.card ≤ 1 := by
    apply card_le_one_iff.mpr
    intro v w hv hw
    exact vertical_unique v w p (mem_filter.mp hv).2 (mem_filter.mp hw).2
  by_cases ht : T.Nonempty
  · obtain ⟨v,hv⟩ := ht
    have hS : S.card ≤ 1 := by
      apply card_le_one_iff.mpr
      intro r s hr hs
      exact vertical_other_unique h₂ v r s p (mem_filter.mp hv).2
        (mem_filter.mp hr).2 (mem_filter.mp hs).2
    omega
  · have hT0 : T=∅ := not_nonempty_iff_eq_empty.mp ht
    rw [hT0,card_empty,add_zero]
    exact four_point_bound h₂ p

def fullGraph : SimpleGraph (FullRow F ⊕ (F × F)) := Erdos714Packing.incidence fullPoints

/-- A kernel-checked positive construction; it is unbalanced, not the conjecture. -/
theorem fullGraph_free (h₂ : (2:F) ≠ 0) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (fullGraph (F := F)) := by
  apply (Erdos714Packing.free_iff_no_rectangle fullPoints (by decide : 0 < 4)).mpr
  intro f p hp
  have hh := full_four_point_bound h₂ p
  have hs : univ.map f ⊆ univ.filter (fun r : FullRow F => ∀ i, p i ∈ fullPoints r) := by
    intro r hr
    obtain ⟨i,_,rfl⟩ := mem_map.mp hr
    exact mem_filter.mpr ⟨mem_univ _,hp i⟩
  have hcard := (card_le_card hs).trans hh
  simp at hcard

theorem full_row_card : Fintype.card (FullRow F)=
    Fintype.card F^2*(Fintype.card F+1)*(Fintype.card F-1) := by
  rw [Fintype.card_sum,row_card,vertical_card]
  ring

theorem full_edge_count : (fullGraph (F := F)).edgeFinset.card=
    Fintype.card F^3*(Fintype.card F+1)*(Fintype.card F-1) := by
  rw [fullGraph,Erdos714Packing.incidence_edges]
  simp only [fullPoints_card,sum_const,card_univ,smul_eq_mul,full_row_card]
  ring


omit [Fintype F] in
lemma quartic_leading_zero (t : Fin 5 ↪ F) (a b c d e : F)
    (h : ∀ i, a*t i^4+b*t i^3+c*t i^2+d*t i+e=0) : a=0 := by
  let P : F[X] := C a*X^4+C b*X^3+C c*X^2+C d*X+C e
  have hP : P=0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P t.injective
    · intro i; simpa [P] using h i
    · have hd : P.natDegree ≤ 4 := by dsimp [P]; compute_degree!
      simpa using Nat.lt_succ_of_le hd
  have ha := congrArg (fun p : F[X] => p.coeff 4) hP
  simpa [P,coeff_add,coeff_C_mul_X_pow] using ha

omit [Fintype F] in
lemma two_chart_five_points (r s : Parabola F) (p : Fin 5 ↪ F × F)
    (hr : ∀ i, On r (p i)) (hs : ∀ i, On s (p i)) : r=s := by
  let t : Fin 5 ↪ F := ⟨fun i => parameter r (p i),by
    intro i j hij
    exact p.injective (parameter_injective_on r (hr i) (hr j) hij)⟩
  have hh := quartic_leading_zero t (coef r s 4) (coef r s 3)
    (coef r s 2) (coef r s 1) (coef r s 0)
    (fun i => intersection_value r s (p i) (hr i) (hs i))
  have hm : r.m=s.m := (sub_eq_zero.mp (sq_eq_zero_iff.mp hh)).symm
  let p' := (Fin.castLEEmb (by decide : 4 ≤ 5)).trans p
  exact same_slope_unique r r s p' (fun i => hr _) (fun i => hr _) (fun i => hs _) hm

omit [Fintype F] in
lemma mixed_not_five_points (v : Vertical F) (r : Parabola F) (p : Fin 5 ↪ F × F)
    (hv : ∀ i, VOn v (p i)) (hr : ∀ i, On r (p i)) : False := by
  let t : Fin 5 ↪ F := ⟨fun i => (p i).1,by
    intro i j hij
    change (p i).1=(p j).1 at hij
    apply p.injective
    apply Prod.ext hij
    apply mul_left_cancel₀ (Units.ne_zero v.d)
    rw [hv i,hv j,hij]⟩
  let D := (v.d : F)
  let u := D*r.m-v.b
  have hz (i : Fin 5) : 1*t i^4+(2*u)*t i^3+(u^2-2*v.c-r.b*D)*t i^2+
      (-2*u*v.c-r.b*D*u-(r.d : F)*D^2)*t i+
      (v.c^2+r.b*D*v.c-r.c*D^2)=0 := by
    have hh := vertical_intersection v r (p i) (hv i) (hr i)
    dsimp [t,D,u]
    linear_combination hh
  exact one_ne_zero (quartic_leading_zero t 1 _ _ _ _ hz)

/-- Distinct members of the full family meet in at most four points.
Unlike K44-freeness, this statement does not require odd characteristic. -/
theorem pair_intersection_bound (r s : FullRow F) (hrs : r ≠ s) :
    (fullPoints r ∩ fullPoints s).card ≤ 4 := by
  by_contra! hcard
  obtain ⟨p : Fin 5 ↪ F × F,hp⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 5) (s := fullPoints r ∩ fullPoints s) (by simpa using hcard)
  have hpr (i : Fin 5) : p i ∈ fullPoints r := (mem_inter.mp (hp ⟨i,rfl⟩)).1
  have hps (i : Fin 5) : p i ∈ fullPoints s := (mem_inter.mp (hp ⟨i,rfl⟩)).2
  cases r with
  | inl r =>
    cases s with
    | inl s =>
      have he := two_chart_five_points r s p
        (fun i => (mem_points _ _).mp (hpr i)) (fun i => (mem_points _ _).mp (hps i))
      exact hrs (congrArg Sum.inl he)
    | inr v =>
      exact mixed_not_five_points v r p
        (fun i => (mem_vPoints _ _).mp (hps i)) (fun i => (mem_points _ _).mp (hpr i))
  | inr v =>
    cases s with
    | inl r =>
      exact mixed_not_five_points v r p
        (fun i => (mem_vPoints _ _).mp (hpr i)) (fun i => (mem_points _ _).mp (hps i))
    | inr w =>
      let p' := (Fin.castLEEmb (by decide : 4 ≤ 5)).trans p
      have he := vertical_unique v w p'
        (fun i => (mem_vPoints _ _).mp (hpr _)) (fun i => (mem_vPoints _ _).mp (hps _))
      exact hrs (congrArg Sum.inr he)

end Erdos714Parabolas
#print axioms Erdos714Parabolas.full_four_point_bound
#print axioms Erdos714Parabolas.fullGraph_free
#print axioms Erdos714Parabolas.full_edge_count
#print axioms Erdos714Parabolas.pair_intersection_bound
