import FormalConjecturesUtil

open SimpleGraph
/-! A diagnostic only: every quadratic potential in this four-coordinate
incidence ansatz admits an octagon over the rationals. -/
namespace Erdos713C8Quadratic

abbrev Vertex := ℚ × (Fin 3 → ℚ)

def Inc (Q : ℚ → ℚ → ℚ) (p l : Vertex) : Prop :=
  p.2 0 + l.2 0 = l.1*p.1 ∧
  p.2 1 + l.2 1 = l.2 0*p.1 ∧
  p.2 2 + l.2 2 = Q l.1 (l.2 0)*p.1

def Octagon (Q : ℚ → ℚ → ℚ) : Prop :=
  ∃ p l : Fin 4 → Vertex, Function.Injective p ∧ Function.Injective l ∧
    (∀ i, Inc Q (p i) (l i)) ∧ (∀ i, Inc Q (p (i+1)) (l i))

def pointShift (t : ℚ) (p : Vertex) : Vertex :=
  (p.1+t, ![p.2 0, p.2 1+t*p.2 0, p.2 2])

def lineShift (Q : ℚ → ℚ → ℚ) (t : ℚ) (l : Vertex) : Vertex :=
  (l.1, ![l.2 0+t*l.1, l.2 1+2*t*l.2 0+t^2*l.1, l.2 2+t*Q l.1 (l.2 0)])

lemma pointShift_injective (t : ℚ) : Function.Injective (pointShift t) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have h0 := congrArg (fun v : Vertex => v.2 0) h
  have h1 := congrArg (fun v : Vertex => v.2 1) h
  have h2 := congrArg (fun v : Vertex => v.2 2) h
  dsimp [pointShift] at hx h0 h1 h2
  refine Prod.ext (by linarith) ?_
  funext i
  fin_cases i
  · exact h0
  · change p.2 1 = q.2 1
    linear_combination h1 - t*h0
  · exact h2

lemma lineShift_injective (Q : ℚ → ℚ → ℚ) (t : ℚ) :
    Function.Injective (lineShift Q t) := by
  intro l m h
  have ha := congrArg Prod.fst h
  have h0 := congrArg (fun v : Vertex => v.2 0) h
  have h1 := congrArg (fun v : Vertex => v.2 1) h
  have h2 := congrArg (fun v : Vertex => v.2 2) h
  dsimp [lineShift] at ha h0 h1 h2
  have hb : l.2 0 = m.2 0 := by linear_combination h0 - t*ha
  rw [ha,hb] at h1 h2
  refine Prod.ext ha ?_
  funext i
  fin_cases i
  · exact hb
  · change l.2 1 = m.2 1
    linarith
  · change l.2 2 = m.2 2
    linarith

lemma shift_inc {Q R : ℚ → ℚ → ℚ} (t : ℚ)
    (hQ : ∀ a b, R a (b+t*a) = Q a b) {p l : Vertex} (h : Inc Q p l) :
    Inc R (pointShift t p) (lineShift Q t l) := by
  rcases h with ⟨h0,h1,h2⟩
  dsimp [Inc,pointShift,lineShift]
  rw [hQ]
  refine ⟨?_,?_,?_⟩
  · linear_combination h0
  · linear_combination h1 + t*h0
  · linear_combination h2

lemma shift_octagon {Q R : ℚ → ℚ → ℚ} (t : ℚ)
    (hQ : ∀ a b, R a (b+t*a) = Q a b) (h : Octagon Q) : Octagon R := by
  rcases h with ⟨p,l,hp,hl,hA,hB⟩
  exact ⟨pointShift t ∘ p, lineShift Q t ∘ l,
    (pointShift_injective t).comp hp, (lineShift_injective Q t).comp hl,
    fun i => shift_inc t hQ (hA i), fun i => shift_inc t hQ (hB i)⟩

def diagP (A C : ℚ) : Fin 4 → Vertex :=
  ![(-2,![0,0,0]), (-1,![0,0,0]),
    (2,![6,-6,12*A+12*C]), (1,![3,-6,3*A+12*C])]

def diagL (A C : ℚ) : Fin 4 → Vertex :=
  ![(0,![0,0,0]), (2,![-2,2,-4*A-4*C]),
    (3,![0,6,6*A-12*C]), (1,![-2,4,-2*A-8*C])]

lemma diagonal_octagon (A C : ℚ) : Octagon (fun a b => A*a^2+C*b^2) := by
  refine ⟨diagP A C,diagL A C,?_,?_,?_,?_⟩
  · intro i j hij
    have hx := congrArg Prod.fst hij
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num [diagP] at hx
  · intro i j hij
    have hx := congrArg Prod.fst hij
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num [diagL] at hx
  · intro i
    fin_cases i <;> dsimp [Inc,diagP,diagL]
    all_goals refine ⟨?_,?_,?_⟩ <;> ring
  · intro i
    fin_cases i <;> dsimp [Inc,diagP,diagL]
    all_goals refine ⟨?_,?_,?_⟩ <;> ring

def mixedP (B : ℚ) : Fin 4 → Vertex :=
  ![(0,![0,0,0]), (1,![0,0,0]), (2,![3,3,-9*B/2]), (3,![3,0,-9*B/2])]

def mixedL (B : ℚ) : Fin 4 → Vertex :=
  ![(0,![0,0,0]), (3,![3,3,-9*B/2]), (0,![-3,-9,9*B/2]), (1,![0,0,0])]

lemma mixed_octagon (B : ℚ) : Octagon (fun a b => (-3*B/2)*a^2+B*a*b) := by
  refine ⟨mixedP B,mixedL B,?_,?_,?_,?_⟩
  · intro i j hij
    have hx := congrArg Prod.fst hij
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num [mixedP] at hx
  · intro i j hij
    have ha := congrArg Prod.fst hij
    have hb := congrArg (fun v : Vertex => v.2 0) hij
    fin_cases i <;> fin_cases j <;> first | rfl | (norm_num [mixedL] at ha <;> norm_num [mixedL] at hb)
  · intro i
    fin_cases i <;> dsimp [Inc,mixedP,mixedL]
    all_goals refine ⟨?_,?_,?_⟩ <;> ring
  · intro i
    fin_cases i <;> dsimp [Inc,mixedP,mixedL]
    all_goals refine ⟨?_,?_,?_⟩ <;> ring

lemma homogeneous_quadratic_octagon (A B C : ℚ) :
    Octagon (fun a b => A*a^2+B*a*b+C*b^2) := by
  by_cases hC : C = 0
  · subst C
    by_cases hB : B = 0
    · subst B
      simpa using diagonal_octagon A 0
    · apply shift_octagon (t := -3/2-A/B) (Q := fun a b => (-3*B/2)*a^2+B*a*b)
      · intro a b
        field_simp
        <;> ring
      · exact mixed_octagon B
  · apply shift_octagon (t := -B/(2*C)) (Q := fun a b => (A-B^2/(4*C))*a^2+C*b^2)
    · intro a b
      field_simp
      <;> ring
    · exact diagonal_octagon (A-B^2/(4*C)) C

def pointLinear (D E F : ℚ) (p : Vertex) : Vertex :=
  (p.1,![p.2 0,p.2 1,p.2 2+D*p.2 0+E*p.2 1+F*p.1])

def lineLinear (D E : ℚ) (l : Vertex) : Vertex :=
  (l.1,![l.2 0,l.2 1,l.2 2+D*l.2 0+E*l.2 1])

lemma pointLinear_injective (D E F : ℚ) : Function.Injective (pointLinear D E F) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have h0 := congrArg (fun v : Vertex => v.2 0) h
  have h1 := congrArg (fun v : Vertex => v.2 1) h
  have h2 := congrArg (fun v : Vertex => v.2 2) h
  dsimp [pointLinear] at hx h0 h1 h2
  rw [hx,h0,h1] at h2
  refine Prod.ext hx ?_
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · change p.2 2 = q.2 2
    linarith

lemma lineLinear_injective (D E : ℚ) : Function.Injective (lineLinear D E) := by
  intro l m h
  have ha := congrArg Prod.fst h
  have h0 := congrArg (fun v : Vertex => v.2 0) h
  have h1 := congrArg (fun v : Vertex => v.2 1) h
  have h2 := congrArg (fun v : Vertex => v.2 2) h
  dsimp [lineLinear] at ha h0 h1 h2
  rw [h0,h1] at h2
  refine Prod.ext ha ?_
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · change l.2 2 = m.2 2
    linarith

lemma linear_inc {Q : ℚ → ℚ → ℚ} (D E F : ℚ) {p l : Vertex} (h : Inc Q p l) :
    Inc (fun a b => Q a b+D*a+E*b+F) (pointLinear D E F p) (lineLinear D E l) := by
  refine ⟨h.1,h.2.1,?_⟩
  dsimp [pointLinear,lineLinear]
  linear_combination h.2.2+D*h.1+E*h.2.1

lemma linear_octagon {Q : ℚ → ℚ → ℚ} (D E F : ℚ) (h : Octagon Q) :
    Octagon (fun a b => Q a b+D*a+E*b+F) := by
  rcases h with ⟨p,l,hp,hl,hA,hB⟩
  exact ⟨pointLinear D E F ∘ p, lineLinear D E ∘ l,
    (pointLinear_injective D E F).comp hp, (lineLinear_injective D E).comp hl,
    fun i => linear_inc D E F (hA i), fun i => linear_inc D E F (hB i)⟩

lemma quadratic_octagon (A B C D E F : ℚ) :
    Octagon (fun a b => A*a^2+B*a*b+C*b^2+D*a+E*b+F) :=
  linear_octagon D E F (homogeneous_quadratic_octagon A B C)

def graph (Q : ℚ → ℚ → ℚ) : SimpleGraph (Vertex ⊕ Vertex) where
  Adj v w := match v,w with
    | .inl p,.inr l => Inc Q p l
    | .inr l,.inl p => Inc Q p l
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact id

set_option maxHeartbeats 1000000 in
lemma contains_of_octagon {Q : ℚ → ℚ → ℚ} (h : Octagon Q) :
    SimpleGraph.cycleGraph 8 ⊑ graph Q := by
  rcases h with ⟨p,l,hp,hl,hA,hB⟩
  let f : Fin 8 → Vertex ⊕ Vertex :=
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

lemma contains_quadratic (A B C D E F : ℚ) :
    SimpleGraph.cycleGraph 8 ⊑ graph (fun a b => A*a^2+B*a*b+C*b^2+D*a+E*b+F) :=
  contains_of_octagon (quadratic_octagon A B C D E F)

#print axioms homogeneous_quadratic_octagon
#print axioms contains_quadratic
end Erdos713C8Quadratic
