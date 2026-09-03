import Submission.QuarticCircleTrace

/-!
An explicit affine F9-plane in a trace-one filtered fourth-power trace fiber.
The abstract endomorphism hypotheses are stated, not inferred from a field model.
-/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714TernaryGoldPlane
variable {E : Type*} [Field E] [CharP E 3]

lemma two_ne : (2:E)≠0 := by
  intro h
  have h3 : (3:E)=0 := CharP.cast_eq_zero E 3
  have h1 : (1:E)=0 := by linear_combination h3-h
  exact one_ne_zero h1

def trace4 (τ : E →+* E) (z : E) : E := z+τ z+τ (τ z)+τ (τ (τ z))
omit [CharP E 3] in
lemma trace4_add (τ : E →+* E) (z w : E) : trace4 τ (z+w)=trace4 τ z+trace4 τ w := by
  simp only [trace4,map_add]
  ring
omit [CharP E 3] in
lemma trace4_half (τ : E →+* E) (z : E) : trace4 τ z=(z+τ (τ z))+τ (z+τ (τ z)) := by
  simp only [trace4,map_add]
  ring
omit [CharP E 3] in
lemma trace4_anti (τ : E →+* E) {z : E} (hz : τ (τ z)= -z) : trace4 τ z=0 := by
  rw [trace4_half,hz,add_neg_cancel,map_zero,zero_add]

lemma fourth_pair (z v : E) : (z+v)^4+(z-v)^4= -(z^4+v^4) := by
  have h3 : (3:E)=0 := CharP.cast_eq_zero E 3
  linear_combination (z^4+4*z^2*v^2+v^4)*h3

lemma trace4_mixed (τ : E →+* E) {z v : E}
    (hz : τ (τ z)=z) (hv : τ (τ v)= -v) :
    trace4 τ ((z+v)^4)=trace4 τ (z^4)+trace4 τ (v^4) := by
  have h₁ : trace4 τ ((z+v)^4)= -(z^4+v^4)-((τ z)^4+(τ v)^4) := by
    rw [trace4_half]
    have hh : (z+v)^4+τ (τ ((z+v)^4))= -(z^4+v^4) := by
      simp only [map_pow,map_add,hz,hv]
      simpa only [sub_eq_add_neg] using fourth_pair z v
    rw [hh]
    simp only [map_neg,map_add,map_pow]
    ring
  have h₂ : trace4 τ (z^4)=2*(z^4+(τ z)^4) := by
    simp only [trace4,map_pow,hz]
    ring
  have h₃ : trace4 τ (v^4)=2*(v^4+(τ v)^4) := by
    simp only [trace4,map_pow,hv,map_neg]
    ring
  rw [h₁,h₂,h₃]
  have h3 : (3:E)=0 := CharP.cast_eq_zero E 3
  linear_combination -(z^4+v^4+(τ z)^4+(τ v)^4)*h3

omit [CharP E 3] in
lemma prime_fixed (ι : ZMod 3 →+* E) (τ : E →+* E) (s : ZMod 3) : τ (ι s)=ι s := by
  have h : τ.comp ι=ι := Subsingleton.elim _ _
  exact DFunLike.congr_fun h s

lemma coefficient_fourth (ι : ZMod 3 →+* E) {i : E} (hi : i^2= -1) (s t : ZMod 3) :
    (ι s+ι t*i)^4=(ι s)^2+(ι t)^2 := by
  have hs : (ι s)^3=ι s := by rw [← map_pow]; congr 1; exact ZMod.pow_card s
  have ht : (ι t)^3=ι t := by rw [← map_pow]; congr 1; exact ZMod.pow_card t
  have h3 : (3:E)=0 := CharP.cast_eq_zero E 3
  linear_combination (ι s)*hs + (ι t)*i^4*ht +
    (ι t)^2*(i^2-1)*hi + (ι t)*i*hs + (ι s)*i^3*ht +
    (ι s)*(ι t)*i*hi +
    ((ι s)^3*(ι t)*i+2*(ι s)^2*(ι t)^2*i^2+(ι s)*(ι t)^3*i^3)*h3

lemma center_trace (τ : E →+* E) {i a b : E} (hi : i^2= -1)
    (hti : τ i= -i) (ha : τ a=a) (hb : τ b=b) :
    trace4 τ ((a+b*i)^4)=a^4+b^4 := by
  simp only [trace4,map_pow,map_add,map_mul,map_neg,ha,hb,hti,neg_neg]
  have h3 : (3:E)=0 := CharP.cast_eq_zero E 3
  linear_combination 4*b^4*(i^2-1)*hi + (a^4+b^4+8*a^2*b^2*i^2)*h3

omit [CharP E 3] in
lemma trace_anti (τ : E →+* E) (L : E →+ ZMod 3) (hL : ∀ x,L (τ x)=L x)
    {z : E} (hz : τ z= -z) : L z=0 := by
  have h := hL z
  rw [hz,map_neg] at h
  have hh : (2:ZMod 3)*L z=0 := by linear_combination -h
  exact (mul_eq_zero.mp hh).resolve_left (by decide)

omit [CharP E 3] in
lemma trace_anti2 (τ : E →+* E) (L : E →+ ZMod 3) (hL : ∀ x,L (τ x)=L x)
    {z : E} (hz : τ (τ z)= -z) : L z=0 := by
  apply trace_anti (τ.comp τ) L (fun x => by simp only [RingHom.comp_apply,hL]) hz

def point (ι : ZMod 3 →+* E) (i u : E) (p : ZMod 3 × ZMod 3) : E := (ι p.1+ι p.2*i)*u

lemma point_injective (ι : ZMod 3 →+* E) (τ : E →+* E) {i u : E}
    (hi0 : i≠0) (hu0 : u≠0) (hti : τ i= -i) : Function.Injective (point ι i u) := by
  intro p r h
  have h₁ : ι p.1+ι p.2*i=ι r.1+ι r.2*i := mul_right_cancel₀ hu0 h
  have h₂ := congrArg τ h₁
  simp only [map_add,map_mul,prime_fixed,hti] at h₂
  have hm : ((2:E)*i)*(ι p.2-ι r.2)=0 := by linear_combination h₁-h₂
  have hb : ι p.2=ι r.2 := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (mul_ne_zero two_ne hi0))
  have ha : ι p.1=ι r.1 := by rw [hb] at h₁; exact add_right_cancel h₁
  exact Prod.ext (ι.injective ha) (ι.injective hb)

/-- Every point in the displayed affine plane satisfies BOTH original filters. -/
theorem plane_incidence (ι : ZMod 3 →+* E) (τ : E →+* E) (L : E →+ ZMod 3)
    (hL : ∀ x,L (τ x)=L x) {i u a b : E}
    (hi : i^2= -1) (hu : u^4=i) (hti : τ i= -i) (htu : τ (τ u)= -u)
    (ha : τ a=a) (hb : τ b=b) (hab : a^4+b^4=1) (hLa : L a=1)
    (p : ZMod 3 × ZMod 3) :
    trace4 τ ((a+b*i+point ι i u p)^4)=1 ∧ L (a+b*i+point ι i u p)=1 := by
  let z := a+b*i
  let v := point ι i u p
  have hz : τ (τ z)=z := by simp only [z,map_add,map_mul,map_neg,ha,hb,hti,neg_neg]
  have hv : τ (τ v)= -v := by
    simp only [v,point,map_mul,map_add,map_neg,prime_fixed,hti,htu,neg_neg]
    ring
  have hv4 : v^4=((ι p.1)^2+(ι p.2)^2)*i := by
    dsimp [v,point]
    rw [mul_pow,hu,coefficient_fourth ι hi]
  have htv : τ (v^4)= -(v^4) := by
    rw [hv4]
    simp only [map_mul,map_add,map_pow,prime_fixed,hti]
    ring
  have hz4 := center_trace τ hi hti ha hb
  have hLv : L v=0 := trace_anti2 τ L hL hv
  have hLbi : L (b*i)=0 := trace_anti τ L hL (by rw [map_mul,hb,hti,mul_neg])
  constructor
  · rw [trace4_mixed τ hz hv,hz4,hab]
    have hzero : trace4 τ (v^4)=0 := by
      simp only [trace4,htv,map_neg]
      ring
    rw [hzero,add_zero]
  · change L (z+v)=1
    simp only [z,map_add,hLa,hLbi,hLv,add_zero]

omit [CharP E 3] in
lemma point_add (ι : ZMod 3 →+* E) (i u : E) (p r : ZMod 3 × ZMod 3) :
    point ι i u (p+r)=point ι i u p+point ι i u r := by
  simp only [point,Prod.fst_add,Prod.snd_add,map_add]
  ring

def graph (τ : E →+* E) (L : E →+ ZMod 3) : SimpleGraph (E ⊕ E) where
  Adj x y := match x,y with
    | .inl a,.inr b => trace4 τ ((a+b)^4)=1 ∧ L (a+b)=1
    | .inr b,.inl a => trace4 τ ((a+b)^4)=1 ∧ L (a+b)=1
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

/-- A complete nine-by-nine graph, not just a diagnostic list of equations. -/
def planeCopy (ι : ZMod 3 →+* E) (τ : E →+* E) (L : E →+ ZMod 3)
    (hL : ∀ x,L (τ x)=L x) {i u a b : E}
    (hi : i^2= -1) (hu : u^4=i) (hti : τ i= -i) (htu : τ (τ u)= -u)
    (ha : τ a=a) (hb : τ b=b) (hab : a^4+b^4=1) (hLa : L a=1) :
    (completeBipartiteGraph (ZMod 3 × ZMod 3) (ZMod 3 × ZMod 3)).Copy (graph τ L) := by
  have hi0 : i≠0 := by intro h; rw [h,zero_pow (by decide)] at hi; exact neg_ne_zero.mpr one_ne_zero hi.symm
  have hu0 : u≠0 := by intro h; rw [h,zero_pow (by decide)] at hu; exact hi0 hu.symm
  let left : ZMod 3 × ZMod 3 ↪ E := ⟨point ι i u,point_injective ι τ hi0 hu0 hti⟩
  let right : ZMod 3 × ZMod 3 ↪ E := ⟨fun p => a+b*i+point ι i u p,
    fun p r h => left.injective (add_left_cancel h)⟩
  have hedge (p r : ZMod 3 × ZMod 3) : (graph τ L).Adj (.inl (left p)) (.inr (right r)) := by
    have h := plane_incidence ι τ L hL hi hu hti htu ha hb hab hLa (p+r)
    have he : left p+right r=a+b*i+point ι i u (p+r) := by
      dsimp [left,right]
      rw [point_add]
      ring
    change trace4 τ ((left p+right r)^4)=1 ∧ L (left p+right r)=1
    rw [he]
    exact h
  refine ⟨⟨left.sumMap right,?_⟩,(left.sumMap right).injective⟩
  intro p r h
  cases p <;> cases r
  · simp at h
  · exact hedge _ _
  · exact (hedge _ _).symm
  · simp at h

theorem not_free_four (ι : ZMod 3 →+* E) (τ : E →+* E) (L : E →+ ZMod 3)
    (hL : ∀ x,L (τ x)=L x) {i u a b : E}
    (hi : i^2= -1) (hu : u^4=i) (hti : τ i= -i) (htu : τ (τ u)= -u)
    (ha : τ a=a) (hb : τ b=b) (hab : a^4+b^4=1) (hLa : L a=1) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph τ L) := by
  let e : Fin 4 ↪ ZMod 3 × ZMod 3 := (Function.Embedding.nonempty_of_card_le (by decide)).some
  let f : (completeBipartiteGraph (Fin 4) (Fin 4)).Copy
      (completeBipartiteGraph (ZMod 3 × ZMod 3) (ZMod 3 × ZMod 3)) :=
    ⟨⟨e.sumMap e,by intro p r h; cases p <;> cases r <;> simp_all⟩,(e.sumMap e).injective⟩
  intro hf
  exact hf ⟨(planeCopy ι τ L hL hi hu hti htu ha hb hab hLa).comp f⟩

#print axioms plane_incidence
#print axioms point_injective
#print axioms planeCopy
#print axioms not_free_four
end Erdos714TernaryGoldPlane
