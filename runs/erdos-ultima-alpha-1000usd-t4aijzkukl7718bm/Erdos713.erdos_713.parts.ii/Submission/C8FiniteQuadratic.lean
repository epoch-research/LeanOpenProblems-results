import FormalConjecturesUtil

/-! An auxiliary obstruction: quadratic two-variable potentials over finite
fields of characteristic two. This is not a settlement of Erdős 713. -/
open SimpleGraph
namespace Erdos713C8FiniteQuadratic

abbrev Vertex (F : Type*) := F × (Fin 3 → F)

variable {K : Type*} [Field K]

def Inc (Q : K → K → K) (p l : Vertex K) : Prop :=
  p.2 0 + l.2 0 = l.1*p.1 ∧
  p.2 1 + l.2 1 = l.2 0*p.1 ∧
  p.2 2 + l.2 2 = Q l.1 (l.2 0)*p.1

def Octagon (Q : K → K → K) : Prop :=
  ∃ p l : Fin 4 → Vertex K, Function.Injective p ∧ Function.Injective l ∧
    (∀ i, Inc Q (p i) (l i)) ∧ (∀ i, Inc Q (p (i+1)) (l i))

def pointShift (t : K) (p : Vertex K) : Vertex K :=
  (p.1+t, ![p.2 0, p.2 1+t*p.2 0, p.2 2])

def lineShift (Q : K → K → K) (t : K) (l : Vertex K) : Vertex K :=
  (l.1, ![l.2 0+t*l.1, l.2 1+2*t*l.2 0+t^2*l.1, l.2 2+t*Q l.1 (l.2 0)])

lemma pointShift_injective (t : K) : Function.Injective (pointShift t) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have h0 := congrArg (fun v : Vertex K => v.2 0) h
  have h1 := congrArg (fun v : Vertex K => v.2 1) h
  have h2 := congrArg (fun v : Vertex K => v.2 2) h
  dsimp [pointShift] at hx h0 h1 h2
  refine Prod.ext (by linear_combination hx) ?_
  funext i
  fin_cases i
  · exact h0
  · change p.2 1 = q.2 1
    linear_combination h1 - t*h0
  · exact h2

lemma lineShift_injective (Q : K → K → K) (t : K) :
    Function.Injective (lineShift Q t) := by
  intro l m h
  have ha := congrArg Prod.fst h
  have h0 := congrArg (fun v : Vertex K => v.2 0) h
  have h1 := congrArg (fun v : Vertex K => v.2 1) h
  have h2 := congrArg (fun v : Vertex K => v.2 2) h
  dsimp [lineShift] at ha h0 h1 h2
  have hb : l.2 0 = m.2 0 := by linear_combination h0 - t*ha
  rw [ha,hb] at h1 h2
  refine Prod.ext ha ?_
  funext i
  fin_cases i
  · exact hb
  · change l.2 1 = m.2 1
    linear_combination h1
  · change l.2 2 = m.2 2
    linear_combination h2

lemma shift_inc {Q R : K → K → K} (t : K)
    (hQ : ∀ a b, R a (b+t*a) = Q a b) {p l : Vertex K} (h : Inc Q p l) :
    Inc R (pointShift t p) (lineShift Q t l) := by
  rcases h with ⟨h0,h1,h2⟩
  dsimp [Inc,pointShift,lineShift]
  rw [hQ]
  refine ⟨?_,?_,?_⟩
  · linear_combination h0
  · linear_combination h1 + t*h0
  · linear_combination h2

lemma shift_octagon {Q R : K → K → K} (t : K)
    (hQ : ∀ a b, R a (b+t*a) = Q a b) (h : Octagon Q) : Octagon R := by
  rcases h with ⟨p,l,hp,hl,hA,hB⟩
  exact ⟨pointShift t ∘ p, lineShift Q t ∘ l,
    (pointShift_injective t).comp hp, (lineShift_injective Q t).comp hl,
    fun i => shift_inc t hQ (hA i), fun i => shift_inc t hQ (hB i)⟩

def graph (Q : K → K → K) : SimpleGraph (Vertex K ⊕ Vertex K) where
  Adj v w := match v,w with
    | .inl p,.inr l => Inc Q p l
    | .inr l,.inl p => Inc Q p l
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact id

set_option maxHeartbeats 1000000 in
lemma contains_of_octagon {Q : K → K → K} (h : Octagon Q) :
    SimpleGraph.cycleGraph 8 ⊑ graph Q := by
  rcases h with ⟨p,l,hp,hl,hA,hB⟩
  let f : Fin 8 → Vertex K ⊕ Vertex K :=
    ![Sum.inl (p 0),Sum.inr (l 0),Sum.inl (p 1),Sum.inr (l 1),
      Sum.inl (p 2),Sum.inr (l 2),Sum.inl (p 3),Sum.inr (l 3)]
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try (exfalso; revert hij; decide)
    all_goals dsimp [f,graph]
    all_goals first | exact hA 0 | exact hA 1 | exact hA 2 | exact hA 3 | exact hB 0 | exact hB 1 | exact hB 2 | exact hB 3
  · intro i j hij
    change f i = f j at hij
    fin_cases i <;> fin_cases j <;> dsimp [f] at hij
    all_goals first | rfl | (have he := hp (Sum.inl.inj hij); exfalso; revert he; decide) | (have he := hl (Sum.inr.inj hij); exfalso; revert he; decide) | cases hij

def pointLinear (D E F : K) (p : Vertex K) : Vertex K :=
  (p.1,![p.2 0,p.2 1,p.2 2+D*p.2 0+E*p.2 1+F*p.1])

def lineLinear (D E : K) (l : Vertex K) : Vertex K :=
  (l.1,![l.2 0,l.2 1,l.2 2+D*l.2 0+E*l.2 1])

lemma pointLinear_injective (D E F : K) : Function.Injective (pointLinear D E F) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have h0 := congrArg (fun v : Vertex K => v.2 0) h
  have h1 := congrArg (fun v : Vertex K => v.2 1) h
  have h2 := congrArg (fun v : Vertex K => v.2 2) h
  dsimp [pointLinear] at hx h0 h1 h2
  rw [hx,h0,h1] at h2
  refine Prod.ext hx ?_
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · change p.2 2 = q.2 2
    linear_combination h2

lemma lineLinear_injective (D E : K) : Function.Injective (lineLinear D E) := by
  intro l m h
  have ha := congrArg Prod.fst h
  have h0 := congrArg (fun v : Vertex K => v.2 0) h
  have h1 := congrArg (fun v : Vertex K => v.2 1) h
  have h2 := congrArg (fun v : Vertex K => v.2 2) h
  dsimp [lineLinear] at ha h0 h1 h2
  rw [h0,h1] at h2
  refine Prod.ext ha ?_
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · change l.2 2 = m.2 2
    linear_combination h2

lemma linear_inc {Q : K → K → K} (D E F : K) {p l : Vertex K} (h : Inc Q p l) :
    Inc (fun a b => Q a b+D*a+E*b+F) (pointLinear D E F p) (lineLinear D E l) := by
  refine ⟨h.1,h.2.1,?_⟩
  dsimp [pointLinear,lineLinear]
  linear_combination h.2.2+D*h.1+E*h.2.1

lemma linear_octagon {Q : K → K → K} (D E F : K) (h : Octagon Q) :
    Octagon (fun a b => Q a b+D*a+E*b+F) := by
  rcases h with ⟨p,l,hp,hl,hA,hB⟩
  exact ⟨pointLinear D E F ∘ p, lineLinear D E ∘ l,
    (pointLinear_injective D E F).comp hp, (lineLinear_injective D E).comp hl,
    fun i => linear_inc D E F (hA i), fun i => linear_inc D E F (hB i)⟩


def D (u v r t : K) : K := (u^2-u)*t+(v-v^2)*r
def E (u v r t : K) : K :=
  u^2*((1-v)*r-(1-u)*t)*t+(1-v)*r*(v*r-u*t)
def J (u v r t : K) : K :=
  (u*((1-v)*r-(1-u)*t))^2*t+((1-v)*r)^2*(v*r-u*t)

set_option maxHeartbeats 1000000 in
lemma quadratic_octagon_of_moments (A B C u v r t : K)
    (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hr : r ≠ 0) (ht : t ≠ 0)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0)
    (hM : A*D u v r t+B*E u v r t+C*J u v r t = 0) :
    Octagon (fun a b => A*a^2+B*a*b+C*b^2) := by
  dsimp [D,E,J] at hM
  let s := (1-v)*r-(1-u)*t
  have hs : s ≠ 0 := by
    intro he
    have hprod : t^2*(1-u)*(v-u) = 0 := by
      dsimp [s] at he
      linear_combination (1-v)*hB-v*((1-v)*r+(1-u)*t)*he
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ht) (sub_ne_zero.mpr hu1.symm))
      (sub_ne_zero.mpr huv.symm)) hprod
  have hs2 : v*r-u*t ≠ 0 := by
    intro he
    have hprod : t^2*u*(u-v) = 0 := by
      linear_combination v*hB-(1-v)*(v*r+u*t)*he
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ht) hu) (sub_ne_zero.mpr huv)) hprod
  have hut : u*t ≠ 0 := mul_ne_zero hu ht
  have hvr : v*r ≠ 0 := mul_ne_zero hv hr
  let Q : K → K → K := fun a b => A*a^2+B*a*b+C*b^2
  let p : Fin 4 → Vertex K :=
    ![(0,![0,0,0]), (s,![0,0,0]),
      (s+t,![u*t,u*s*t,Q u (u*s)*t]), (r,![v*r,0,Q v 0*r])]
  let l : Fin 4 → Vertex K :=
    ![(0,![0,0,0]), (u,![u*s,u*s^2,Q u (u*s)*s]),
      (1,![(1-v)*r,(1-v)*r*(s+t)-u*s*t,Q 1 ((1-v)*r)*(s+t)-Q u (u*s)*t]),
      (v,![0,0,0])]
  refine ⟨p,l,?_,?_,?_,?_⟩
  · intro i j hij
    have hx := congrArg (fun w : Vertex K => w.1) hij
    have hy := congrArg (fun w : Vertex K => w.2 0) hij
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [p] at hx hy
      first | exact (hs hx).elim | exact (hs hx.symm).elim |
        exact (hr hx).elim | exact (hr hx.symm).elim |
        exact (hut hy).elim | exact (hut hy.symm).elim |
        exact (hvr hy).elim | exact (hvr hy.symm).elim |
        (exfalso; apply ht; linear_combination hx) |
        (exfalso; apply ht; linear_combination -hx) |
        (exfalso; apply hs2; dsimp [s] at hx; linear_combination hx) |
        (exfalso; apply hs2; dsimp [s] at hx; linear_combination -hx))
  · intro i j hij
    have hx := congrArg (fun w : Vertex K => w.1) hij
    fin_cases i <;> fin_cases j <;> dsimp [l] at hx <;> simp_all
  · intro i
    fin_cases i <;> dsimp [Inc,p,l,s,Q]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals ring
  · intro i
    fin_cases i <;> dsimp [Inc,p,l,s,Q]
    all_goals refine ⟨?_,?_,?_⟩
    all_goals solve | ring | linear_combination hB | linear_combination -hB | linear_combination hM | linear_combination -hM


lemma scaled_sheared_octagon (A B C u v r t z τ : K)
    (hu : u ≠ 0) (hv : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hr : r ≠ 0) (ht : t ≠ 0) (hz : z ≠ 0)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0)
    (hM : (A+B*τ+C*τ^2)*D u v r t +
      (B+2*C*τ)*z*E u v r t+C*z^2*J u v r t = 0) :
    Octagon (fun a b => A*a^2+B*a*b+C*b^2) := by
  apply shift_octagon τ (Q := fun a b =>
    (A+B*τ+C*τ^2)*a^2+(B+2*C*τ)*a*b+C*b^2)
  · intro a b; ring
  apply quadratic_octagon_of_moments _ _ _ u v (r*z) (t*z)
    hu hv hu1 hv1 huv (mul_ne_zero hr hz) (mul_ne_zero ht hz)
  · linear_combination z^2*hB
  · dsimp [D,E,J] at hM ⊢
    linear_combination z*hM

lemma discriminant_char_two [CharP K 2] (u v r t : K)
    (hB : r^2*v*(1-v)-t^2*u*(1-u) = 0) :
    D u v r t*J u v r t+(E u v r t)^2 = t^4*u^2*(u+v)*(u+1)^2 := by
  dsimp [D,E,J]
  linear_combination (norm := ring_nf) v*(r^2*v*(v+1)+r*t*u*(u+1)*(v+1)+t^2*u*(u+1))*hB
  have h4 : (4:K) = 0 := by linear_combination 2*(CharTwo.two_eq_zero (R := K))
  have h6 : (6:K) = 0 := by linear_combination 3*(CharTwo.two_eq_zero (R := K))
  have h8 : (8:K) = 0 := by linear_combination 4*(CharTwo.two_eq_zero (R := K))
  have h10 : (10:K) = 0 := by linear_combination 5*(CharTwo.two_eq_zero (R := K))
  have h12 : (12:K) = 0 := by linear_combination 6*(CharTwo.two_eq_zero (R := K))
  simp [CharTwo.two_eq_zero,h4,h6,h8,h10,h12]

lemma parameters_char_two [Fintype K] [CharP K 2] (hq : 4 < Fintype.card K) :
    ∃ u v r t : K,
      u ≠ 0 ∧ v ≠ 0 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ r ≠ 0 ∧ t ≠ 0 ∧
      r^2*v*(1-v)-t^2*u*(1-u) = 0 ∧
      D u v r t ≠ 0 ∧ D u v r t*J u v r t+(E u v r t)^2 ≠ 0 := by
  classical
  have hSq : Function.Surjective (fun z : K => z^2) :=
    Finite.surjective_of_injective (frobenius_inj K 2)
  have hcard2 : ({0,1} : Finset K).card ≤ 2 := by
    simpa using List.toFinset_card_le ([0,1] : List K)
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0,1} : Finset K)) (t := Finset.univ) (by
      simpa only [Finset.card_univ] using hcard2.trans_lt (show 2 < Fintype.card K by omega))
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hu
  have hcard4 : ({0,1,u,1-u} : Finset K).card ≤ 4 := by
    simpa using List.toFinset_card_le ([0,1,u,1-u] : List K)
  obtain ⟨v,_,hv⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0,1,u,1-u} : Finset K)) (t := Finset.univ) (by
      simpa only [Finset.card_univ] using hcard4.trans_lt hq)
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv
  obtain ⟨r,hr⟩ := hSq (u*(1-u))
  obtain ⟨t,ht⟩ := hSq (v*(1-v))
  change r^2 = u*(1-u) at hr
  change t^2 = v*(1-v) at ht
  have hr0 : r ≠ 0 := by
    intro he; rw [he,zero_pow (by decide : 2 ≠ 0)] at hr
    exact (mul_ne_zero hu.1 (sub_ne_zero.mpr (Ne.symm hu.2))) hr.symm
  have ht0 : t ≠ 0 := by
    intro he; rw [he,zero_pow (by decide : 2 ≠ 0)] at ht
    exact (mul_ne_zero hv.1 (sub_ne_zero.mpr (Ne.symm hv.2.1))) ht.symm
  have hrt : r ≠ t := by
    intro he
    have hh : (v-u)*(v-(1-u)) = 0 := by
      rw [he] at hr
      linear_combination ht-hr
    exact (mul_ne_zero (sub_ne_zero.mpr hv.2.2.1) (sub_ne_zero.mpr hv.2.2.2)) hh
  have hB : r^2*v*(1-v)-t^2*u*(1-u) = 0 := by rw [hr,ht]; ring
  have hD : D u v r t ≠ 0 := by
    have he : D u v r t = r*t*(t-r) := by
      dsimp [D]
      linear_combination t*hr-r*ht
    rw [he]
    exact mul_ne_zero (mul_ne_zero hr0 ht0) (sub_ne_zero.mpr hrt.symm)
  refine ⟨u,v,r,t,hu.1,hv.1,hu.2,hv.2.1,(Ne.symm hv.2.2.1),hr0,ht0,hB,hD,?_⟩
  rw [discriminant_char_two u v r t hB]
  have huv : u+v ≠ 0 := by
    rw [← CharTwo.sub_eq_add]
    exact sub_ne_zero.mpr (Ne.symm hv.2.2.1)
  have hu1 : u+1 ≠ 0 := by
    rw [← CharTwo.sub_eq_add]
    exact sub_ne_zero.mpr hu.2
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ht0)
    (pow_ne_zero _ hu.1)) huv) (pow_ne_zero _ hu1)


lemma solve_coefficients_char_two [CharP K 2] (A B C d e j w : K)
    (hd : d ≠ 0) (hdisc : d*j+e^2 ≠ 0) (hBC : B ≠ 0 ∨ C ≠ 0)
    (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hSq : Function.Surjective (fun z : K => z^2)) :
    ∃ z τ : K, z ≠ 0 ∧ (A+B*τ+C*τ^2)*d+B*z*e+C*z^2*j = 0 := by
  by_cases hC : C = 0
  · subst C
    have hB : B ≠ 0 := hBC.resolve_right (not_not_intro rfl)
    refine ⟨1,-A/B-e/d,one_ne_zero,?_⟩
    field_simp
    ring
  obtain ⟨μ,hμ⟩ : ∃ μ : K, A+B*μ+C*μ^2 ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 := h 0
    have h1 := h 1
    have hw := h w
    have he : C*w*(w-1) = 0 := by
      linear_combination hw-w*h1+(w-1)*h0
    exact (mul_ne_zero (mul_ne_zero hC hw0) (sub_ne_zero.mpr hw1)) he
  let k := (d*j+e^2)/d^2
  have hk : k ≠ 0 := div_ne_zero hdisc (pow_ne_zero _ hd)
  obtain ⟨z,hz⟩ := hSq (-(A+B*μ+C*μ^2)/(C*k))
  change z^2 = -(A+B*μ+C*μ^2)/(C*k) at hz
  have hz0 : z ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide : 2 ≠ 0)] at hz
    exact (div_ne_zero (neg_ne_zero.mpr hμ) (mul_ne_zero hC hk)) hz.symm
  refine ⟨z,μ-e/d*z,hz0,?_⟩
  have hzero : A+B*μ+C*μ^2+C*k*z^2 = 0 := by
    rw [hz]
    field_simp
    ring
  have hsquare : (μ-e/d*z)^2 = μ^2+(e/d*z)^2 := by
    rw [CharTwo.sub_eq_add,CharTwo.add_sq]
  calc
    _ = d*(A+B*μ+C*μ^2+C*k*z^2) := by
      rw [hsquare]
      dsimp [k]
      field_simp
      ring
    _ = 0 := by rw [hzero,mul_zero]

lemma homogeneous_quadratic_char_two [Fintype K] [CharP K 2]
    (A B C : K) (hq : 4 < Fintype.card K) :
    Octagon (fun a b => A*a^2+B*a*b+C*b^2) := by
  obtain ⟨u,v,r,t,hu,hv,hu1,hv1,huv,hr,ht,hB,hD,hdisc⟩ := parameters_char_two hq
  by_cases hBC : B ≠ 0 ∨ C ≠ 0
  · obtain ⟨z,τ,hz,hM⟩ := solve_coefficients_char_two A B C
      (D u v r t) (E u v r t) (J u v r t) u hD hdisc hBC hu hu1
      (Finite.surjective_of_injective (frobenius_inj K 2))
    apply scaled_sheared_octagon A B C u v r t z τ hu hv hu1 hv1 huv hr ht hz hB
    simpa only [CharTwo.two_eq_zero,zero_mul,add_zero] using hM
  push_neg at hBC
  rcases hBC with ⟨rfl,rfl⟩
  have huv' : u ≠ 1-u := by
    intro he
    have hh : (2:K)*u = 1 := by linear_combination he
    exact zero_ne_one (by simpa only [CharTwo.two_eq_zero,zero_mul] using hh)
  apply quadratic_octagon_of_moments A 0 0 u (1-u) 1 1 hu
    (sub_ne_zero.mpr (Ne.symm hu1)) hu1
    (by intro he; apply hu; linear_combination -he) huv' one_ne_zero one_ne_zero
  · ring
  · dsimp [D]
    ring

lemma quadratic_char_two [Fintype K] [CharP K 2]
    (A B C D E F : K) (hq : 4 < Fintype.card K) :
    cycleGraph 8 ⊑ graph (fun a b => A*a^2+B*a*b+C*b^2+D*a+E*b+F) :=
  contains_of_octagon (linear_octagon D E F (homogeneous_quadratic_char_two A B C hq))

#print axioms parameters_char_two
#print axioms solve_coefficients_char_two
#print axioms homogeneous_quadratic_char_two
#print axioms quadratic_char_two
end Erdos713C8FiniteQuadratic
