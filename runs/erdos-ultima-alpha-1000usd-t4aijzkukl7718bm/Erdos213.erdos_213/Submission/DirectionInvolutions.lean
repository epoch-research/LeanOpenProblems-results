import FormalConjecturesUtil

/-! Rational projective involutions on direction supports. These are
structural lemmas for a construction route, not an Erdős 213 settlement. -/
namespace Erdos213.DirectionInvolutions
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

@[ext] structure Coeff where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving DecidableEq

@[ext] structure Vec where
  u : ℚ
  v : ℚ
  deriving DecidableEq

def zeroCoeff : Coeff := ⟨0,0,0⟩
def scale (s : ℚ) (m : Coeff) : Coeff := ⟨s*m.a,s*m.b,s*m.c⟩
def multiplier (m : Coeff) : ℚ := m.a^2+m.b*m.c
def act (m : Coeff) (p : Vec) : Vec := ⟨m.a*p.u+m.b*p.v,m.c*p.u-m.a*p.v⟩
def wedge (p q : Vec) : ℚ := p.u*q.v-p.v*q.u
def pair (m : Coeff) (p q : Vec) : ℚ := wedge (act m p) q

def form (x r : ℚ) (p : Vec) : ℚ := p.u^2-2*x*p.u*p.v+r*p.v^2

lemma act_twice (m : Coeff) (p : Vec) :
    act m (act m p)=⟨multiplier m*p.u,multiplier m*p.v⟩ := by
  apply Vec.ext <;> dsimp [act,multiplier] <;> ring

lemma form_identity (x r : ℚ) (m : Coeff) (p : Vec) :
    form x r (act m p) = multiplier m*form x r p +
      (m.c*r-2*m.a*x-m.b)*(m.c*p.u^2-2*m.a*p.u*p.v-m.b*p.v^2) := by
  dsimp [form,act,multiplier]
  ring

lemma form_pos {x r : ℚ} (hr : x^2<r) (p : Vec) (hp : p.u≠0 ∨ p.v≠0) :
    0<form x r p := by
  have he : form x r p=(p.u-x*p.v)^2+(r-x^2)*p.v^2 := by
    dsimp [form]
    ring
  rw [he]
  by_cases hv : p.v=0
  · have hu : p.u≠0 := hp.resolve_right (by simpa using hv)
    simpa [hv] using sq_pos_of_ne_zero hu
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
      (mul_pos (sub_pos.mpr hr) (sq_pos_of_ne_zero hv))

/-- An invariant positive norm form cannot have two rational-length directions
paired by an involution with nonsquare multiplier. -/
lemma multiplier_square {x r : ℚ} (hr : x^2<r) (m : Coeff)
    (hphase : m.c*r-2*m.a*x-m.b=0) (p : Vec) (hp : p.u≠0 ∨ p.v≠0)
    (h0 : IsSquare (form x r p)) (h1 : IsSquare (form x r (act m p))) :
    IsSquare (multiplier m) := by
  have hn : form x r p≠0 := ne_of_gt (form_pos hr p hp)
  have he := form_identity x r m p
  rw [hphase,zero_mul,add_zero] at he
  have hh := h1.div h0
  rw [he,mul_div_cancel_right₀ _ hn] at hh
  exact hh

/-- Reciprocal completion is the split involution r ↦ R/r. -/
lemma reciprocal_identity (x r s : ℚ) (hs : s≠0) :
    (r/s)^2-2*x*(r/s)+r = (r/s^2)*(s^2-2*x*s+r) := by
  field_simp
  ring

lemma reciprocal_square (x r s : ℚ) (hs : s≠0)
    (hr : IsSquare r) (hf : IsSquare (s^2-2*x*s+r)) :
    IsSquare ((r/s)^2-2*x*(r/s)+r) := by
  rw [reciprocal_identity x r s hs]
  exact (hr.div (IsSquare.sq s)).mul hf

def dot (a b : Coeff) : ℚ := a.a*b.a+a.b*b.b+a.c*b.c
def cross (a b : Coeff) : Coeff :=
  ⟨a.b*b.c-a.c*b.b,a.c*b.a-a.a*b.c,a.a*b.b-a.b*b.a⟩
def pairRow (p q : Vec) : Coeff := ⟨p.u*q.v+p.v*q.u,p.v*q.v,-p.u*q.u⟩

lemma pair_eq_dot (m : Coeff) (p q : Vec) : pair m p q=dot (pairRow p q) m := by
  dsimp [pair,wedge,act,pairRow,dot]
  ring

lemma proportional_of_two_rows (a b m : Coeff)
    (ha : dot a m=0) (hb : dot b m=0) (hne : cross a b≠zeroCoeff) :
    ∃ s : ℚ, m=scale s (cross a b) := by
  let c := cross a b
  have h₁ : c.a*m.b-c.b*m.a=0 := by
    dsimp [c,cross,dot] at *
    linear_combination b.c*ha-a.c*hb
  have h₂ : c.a*m.c-c.c*m.a=0 := by
    dsimp [c,cross,dot] at *
    linear_combination a.b*hb-b.b*ha
  have h₃ : c.b*m.c-c.c*m.b=0 := by
    dsimp [c,cross,dot] at *
    linear_combination b.a*ha-a.a*hb
  by_cases hca : c.a=0
  · by_cases hcb : c.b=0
    · have hcc : c.c≠0 := by
        intro he
        apply hne
        apply Coeff.ext <;> assumption
      refine ⟨m.c/c.c,?_⟩
      apply Coeff.ext <;> dsimp [scale]
      · field_simp [hcc]
        nlinarith [h₂]
      · field_simp [hcc]
        nlinarith [h₃]
      · field_simp [hcc]
        rfl
    · refine ⟨m.b/c.b,?_⟩
      apply Coeff.ext <;> dsimp [scale]
      · field_simp [hcb]
        nlinarith [h₁]
      · field_simp [hcb]
        rfl
      · field_simp [hcb]
        nlinarith [h₃]
  · refine ⟨m.a/c.a,?_⟩
    apply Coeff.ext <;> dsimp [scale]
    · field_simp [hca]
      rfl
    · field_simp [hca]
      nlinarith [h₁]
    · field_simp [hca]
      nlinarith [h₂]

/-- Homogeneous representatives of ∞,0,-1,1,-1/2,-2. -/
def oldRoot : Fin 6 → Vec := ![⟨1,0⟩,⟨0,1⟩,⟨-1,1⟩,⟨1,1⟩,⟨-1,2⟩,⟨-2,1⟩]
def twoPairs (i j k l : Fin 6) : Coeff :=
  cross (pairRow (oldRoot i) (oldRoot j)) (pairRow (oldRoot k) (oldRoot l))

/-- Exact finite certificate for all pairs of disjoint old pairs. -/
lemma finite_split_certificate : ∀ i j k l : Fin 6,
    i≠j → i≠k → i≠l → j≠k → j≠l → k≠l →
    twoPairs i j k l≠zeroCoeff ∧
      (IsSquare (multiplier (twoPairs i j k l)) →
        ∃ s : Fin 6, pair (twoPairs i j k l) (oldRoot s) (oldRoot s)=0) := by
  decide +kernel

lemma multiplier_scale (s : ℚ) (m : Coeff) :
    multiplier (scale s m)=s^2*multiplier m := by
  dsimp [multiplier,scale]
  ring

lemma pair_scale (s : ℚ) (m : Coeff) (p q : Vec) :
    pair (scale s m) p q=s*pair m p q := by
  dsimp [pair,wedge,act,scale]
  ring

/-- Every rational split involution pairing two disjoint old direction pairs
fixes an old direction. This is a universal coefficient statement, not just
a check of one arithmetic parameter. -/
theorem two_old_pairs_force_fixed (m : Coeff) (hm : multiplier m≠0)
    (hsq : IsSquare (multiplier m)) (i j k l : Fin 6)
    (hij : i≠j) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (hkl : k≠l)
    (hij' : pair m (oldRoot i) (oldRoot j)=0)
    (hkl' : pair m (oldRoot k) (oldRoot l)=0) :
    ∃ s : Fin 6, pair m (oldRoot s) (oldRoot s)=0 := by
  obtain ⟨hne,hcert⟩ := finite_split_certificate i j k l hij hik hil hjk hjl hkl
  rw [pair_eq_dot] at hij' hkl'
  obtain ⟨v,hv⟩ := proportional_of_two_rows _ _ m hij' hkl' hne
  change m=scale v (twoPairs i j k l) at hv
  have he : multiplier m=v^2*multiplier (twoPairs i j k l) := by
    rw [hv,multiplier_scale]
  have hv0 : v≠0 := by
    intro h
    apply hm
    rw [he,h]
    ring
  have hc : IsSquare (multiplier (twoPairs i j k l)) := by
    have hh := hsq.div (IsSquare.sq v)
    rw [he,mul_div_cancel_left₀ _ (pow_ne_zero 2 hv0)] at hh
    exact hh
  obtain ⟨s,hs⟩ := hcert hc
  refine ⟨s,?_⟩
  rw [hv,pair_scale,hs,mul_zero]

/-- A fixed-point-free involution on at most nine elements has two disjoint
pairs inside any embedded six-element set. -/
lemma two_pairs_of_card_le_nine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ι) (hf : Function.Involutive f) (hfree : ∀ a, f a≠a)
    (e : Fin 6 ↪ ι) (hcard : Fintype.card ι≤9) :
    ∃ i j k l : Fin 6,
      i≠j ∧ i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ k≠l ∧
      f (e i)=e j ∧ f (e k)=e l := by
  classical
  let A : Finset ι := Finset.univ.image e
  let I := A∩A.image f
  have hA : A.card=6 := by
    rw [Finset.card_image_of_injective _ e.injective]
    simp
  have hB : (A.image f).card=6 := by
    rw [Finset.card_image_of_injective _ hf.injective,hA]
  have hU : (A∪A.image f).card≤9 :=
    (Finset.card_le_univ _).trans hcard
  have hI : 3≤I.card := by
    have hh := Finset.card_union_add_card_inter A (A.image f)
    change (A∪A.image f).card+I.card=A.card+(A.image f).card at hh
    omega
  have partner (a : ι) (ha : a∈I) : a∈A ∧ f a∈A := by
    obtain ⟨ha,ha'⟩ := Finset.mem_inter.mp ha
    obtain ⟨b,hb,hba⟩ := Finset.mem_image.mp ha'
    refine ⟨ha,?_⟩
    simpa [← hba,hf b] using hb
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<I.card by omega)
  have hsmall : ({a,f a} : Finset ι).card<I.card := by
    have hh : ({a,f a} : Finset ι).card≤2 := Finset.card_le_two
    omega
  obtain ⟨c,hc,hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hca : c≠a := fun he => hcn (by simp [he])
  have hcf : c≠f a := fun he => hcn (by simp [he])
  have hac : a≠c := hca.symm
  have hafc : a≠f c := by
    intro hh
    have he := congrArg f hh
    rw [hf] at he
    exact hcf he.symm
  have hfac : f a≠f c := fun hh => hac (hf.injective hh)
  obtain ⟨haA,hfaA⟩ := partner a ha
  obtain ⟨hcA,hfcA⟩ := partner c hc
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp haA
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hfaA
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hcA
  obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hfcA
  refine ⟨i,j,k,l,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro h; have hh := congrArg e h; rw [hi,hj] at hh; exact hfree a hh.symm
  · intro h; have hh := congrArg e h; rw [hi,hk] at hh; exact hac hh
  · intro h; have hh := congrArg e h; rw [hi,hl] at hh; exact hafc hh
  · intro h; have hh := congrArg e h; rw [hj,hk] at hh; exact hcf hh.symm
  · intro h; have hh := congrArg e h; rw [hj,hl] at hh; exact hfac hh
  · intro h; have hh := congrArg e h; rw [hk,hl] at hh; exact hfree c hh.symm
  · rw [hi,hj]
  · rw [hk,hl]

/-- A faithful fixed-point-free split-involution completion of the six old
projective directions has at least ten elements. The projective action is
specified by its exact homogeneous incidence relation. -/
theorem ten_le_card_of_free_split_completion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : Coeff) (hm : multiplier m≠0) (hsq : IsSquare (multiplier m))
    (p : ι → Vec) (e : Fin 6 ↪ ι) (he : ∀ i, p (e i)=oldRoot i)
    (f : ι → ι) (hf : Function.Involutive f) (hfree : ∀ a, f a≠a)
    (hact : ∀ i j, pair m (p i) (p j)=0 ↔ f i=j) :
    10≤Fintype.card ι := by
  by_contra h
  have hcard : Fintype.card ι≤9 := by omega
  obtain ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,hij',hkl'⟩ :=
    two_pairs_of_card_le_nine f hf hfree e hcard
  have hp₁ : pair m (oldRoot i) (oldRoot j)=0 := by
    simpa only [he] using (hact (e i) (e j)).mpr hij'
  have hp₂ : pair m (oldRoot k) (oldRoot l)=0 := by
    simpa only [he] using (hact (e k) (e l)).mpr hkl'
  obtain ⟨s,hs⟩ := two_old_pairs_force_fixed m hm hsq i j k l hij hik hil hjk hjl hkl hp₁ hp₂
  have hh : pair m (p (e s)) (p (e s))=0 := by simpa only [he] using hs
  exact hfree (e s) ((hact _ _).mp hh)

lemma square_form_of_wedge (x r : ℚ) (p q : Vec) (hq : q.u≠0 ∨ q.v≠0)
    (hw : wedge p q=0) (hsq : IsSquare (form x r q)) : IsSquare (form x r p) := by
  by_cases hv : q.v=0
  · have hu : q.u≠0 := hq.resolve_right (by simpa using hv)
    have hh : p.v*q.u=0 := by simpa [wedge,hv] using hw
    have hpv : p.v=0 := (mul_eq_zero.mp hh).resolve_right hu
    simpa [form,hpv] using IsSquare.sq p.u
  · have hu : p.u=p.v*q.u/q.v := by
      apply (eq_div_iff hv).mpr
      dsimp [wedge] at hw
      linarith
    have he : form x r p=(p.v/q.v)^2*form x r q := by
      dsimp [form]
      rw [hu]
      field_simp
    rw [he]
    exact (IsSquare.sq _).mul hsq

/-- The same lower bound with the arithmetic hypotheses, instead of assuming
that the involution multiplier is a square. This still concerns direction
supports, not arbitrary rational-distance point configurations. -/
theorem ten_le_card_of_free_norm_completion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x r : ℚ) (hr : x^2<r) (m : Coeff) (hm : multiplier m≠0)
    (hphase : m.c*r-2*m.a*x-m.b=0)
    (p : ι → Vec) (hp : ∀ i, (p i).u≠0 ∨ (p i).v≠0)
    (hsq : ∀ i, IsSquare (form x r (p i)))
    (e : Fin 6 ↪ ι) (he : ∀ i, p (e i)=oldRoot i)
    (f : ι → ι) (hf : Function.Involutive f) (hfree : ∀ a, f a≠a)
    (hact : ∀ i j, pair m (p i) (p j)=0 ↔ f i=j) :
    10≤Fintype.card ι := by
  have hw : wedge (act m (p (e 0))) (p (f (e 0)))=0 :=
    (hact (e 0) (f (e 0))).mpr rfl
  have hmapped := square_form_of_wedge x r _ _ (hp (f (e 0))) hw (hsq (f (e 0)))
  have hmult := multiplier_square hr m hphase (p (e 0)) (hp (e 0)) (hsq (e 0)) hmapped
  exact ten_le_card_of_free_split_completion m hm hmult p e he f hf hfree hact

namespace Control

def x : ℚ := -29493/41905
def r : ℚ := 7569/7225
def matrix : Coeff := ⟨0,r,1⟩
def point : Fin 10 → Vec :=
  ![⟨1,0⟩,⟨0,1⟩,⟨-1,1⟩,⟨1,1⟩,⟨-1,2⟩,⟨-2,1⟩,
    ⟨-r,1⟩,⟨r,1⟩,⟨-2*r,1⟩,⟨-r,2⟩]
def permutation : Fin 10 → Fin 10 := ![1,0,6,7,8,9,2,3,4,5]

/-- The lower bound is attained by an actual positive rational norm form.
These ten projective directions are not asserted to be ten GP points. -/
lemma ten_direction_control :
    x^2<r ∧ multiplier matrix≠0 ∧
    matrix.c*r-2*matrix.a*x-matrix.b=0 ∧
    (∀ i, ((point i).u≠0 ∨ (point i).v≠0) ∧ IsSquare (form x r (point i))) ∧
    (∀ i : Fin 6, point (i.castLE (by decide))=oldRoot i) ∧
    Function.Involutive permutation ∧ (∀ i, permutation i≠i) ∧
    (∀ i j, pair matrix (point i) (point j)=0 ↔ permutation i=j) := by
  unfold Function.Involutive
  decide +kernel

end Control

#print axioms multiplier_square
#print axioms reciprocal_square
#print axioms proportional_of_two_rows
#print axioms finite_split_certificate
#print axioms two_old_pairs_force_fixed
#print axioms two_pairs_of_card_le_nine
#print axioms ten_le_card_of_free_split_completion
#print axioms ten_le_card_of_free_norm_completion
#print axioms Control.ten_direction_control
end
end Erdos213.DirectionInvolutions
