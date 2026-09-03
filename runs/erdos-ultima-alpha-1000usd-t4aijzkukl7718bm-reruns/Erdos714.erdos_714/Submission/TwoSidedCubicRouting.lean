import Submission.CubicRouting
import Submission.CoordinateCircuits

/-!
Two-sided cubic routing of affine-plane fibers. The additional reciprocal
terms remove the affine-coordinate obstruction to one-sided routing.
The results here concern this construction, not the full Erdos714 conjecture.
-/

noncomputable section
open Classical SimpleGraph Finset
set_option maxHeartbeats 3000000
namespace Erdos714TwoSidedRouting
variable {F : Type*} [Field F]

abbrev Row (F : Type*) := ((F × F) × F) × F
abbrev Coord (F : Type*) := (F × F) × F
abbrev Column (F : Type*) := Coord F × F

def code (H : (F × F) → (F × F) → F) (r : Row F) (z : Coord F) : F :=
  r.1.2*z.2+r.1.2^2*z.1.1+r.1.2^3*z.1.2+
  r.1.1.1*z.2^2+r.1.1.2*z.2^3+H r.1.1 z.1-r.2

def sites : Fin 4 → F := ![0,1,-1,2]

lemma sites_injective (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    Function.Injective (sites (F := F)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals dsimp [sites] at h
  all_goals first
    | exact False.elim (h2 (by linear_combination h))
    | exact False.elim (h2 (by linear_combination -h))
    | exact False.elim (h3 (by linear_combination h))
    | exact False.elim (h3 (by linear_combination -h))
    | exact False.elim (one_ne_zero (by linear_combination h : (1 : F)=0))
    | exact False.elim (one_ne_zero (by linear_combination -h : (1 : F)=0))

/-- The third divided difference, with denominators cleared. -/
def delta (H : (F × F) → (F × F) → F) (u : F × F) : F :=
  H u (2,0)-3*H u (1,0)-H u (-1,0)+3*H u (0,0)

def A (h : F → F) : F := (h 2-3*h 1-h (-1)+3*h 0)/6
def B (h : F → F) : F := (h 1+h (-1)-2*h 0)/2
def C (h : F → F) : F := (h 1-h (-1))/2-A h

lemma six_ne_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) : (6 : F) ≠ 0 := by
  convert mul_ne_zero h2 h3 using 1; norm_num

lemma interpolate (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (h : F → F) (i : Fin 4) :
    h (sites i)=A h*sites i^3+B h*sites i^2+C h*sites i+h 0 := by
  have h6 := six_ne_zero h2 h3
  fin_cases i <;> dsimp [sites,A,B,C] <;> field_simp <;> ring

lemma delta_pair (H : (F × F) → (F × F) → F)
    (hn : ¬∀ u v, delta H u=delta H v) :
    ∃ u v : F × F, u.2 ≠ v.2 ∧ delta H u ≠ delta H v := by
  push_neg at hn
  obtain ⟨u,v,huv⟩ := hn
  by_cases hs : u.2=v.2
  · let w : F × F := (0,u.2+1)
    have hw : u.2 ≠ w.2 := by
      dsimp [w]
      exact fun h => one_ne_zero (by linear_combination -h)
    by_cases hd : delta H u=delta H w
    · exact ⟨w,v,by simpa only [←hs] using hw.symm,fun he => huv (hd.trans he)⟩
    · exact ⟨u,w,hw,hd⟩
  · exact ⟨u,v,hs,huv⟩

variable [Fintype F]

/-- More than five elements suffice to represent any scalar as a difference
of squares with both square roots nonzero. -/
lemma difference_nonzero_squares (h2 : (2 : F) ≠ 0)
    (hq : 5 < Fintype.card F) (k : F) :
    ∃ x y : F, x ≠ 0 ∧ y ≠ 0 ∧ x^2-y^2=k := by
  let S : Finset F := {0} ∪ (Polynomial.nthRoots 2 k).toFinset ∪
    (Polynomial.nthRoots 2 (-k)).toFinset
  have hS : S.card ≤ 5 := by
    have h1 : ((Polynomial.nthRoots 2 k).toFinset).card ≤ 2 :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 2 k)
    have h2' : ((Polynomial.nthRoots 2 (-k)).toFinset).card ≤ 2 :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 2 (-k))
    have hu := card_union_le ({0} ∪ (Polynomial.nthRoots 2 k).toFinset)
      (Polynomial.nthRoots 2 (-k)).toFinset
    have hv := card_union_le ({0} : Finset F) (Polynomial.nthRoots 2 k).toFinset
    simp only [card_singleton] at hv
    change ({0} ∪ (Polynomial.nthRoots 2 k).toFinset ∪
      (Polynomial.nthRoots 2 (-k)).toFinset).card ≤ 5
    omega
  have hn : ¬ (univ : Finset F) ⊆ S := by
    intro he
    have hh := card_le_card he
    simp only [card_univ] at hh
    omega
  obtain ⟨z,_,hz⟩ := not_subset.mp hn
  have hz0 : z ≠ 0 := by
    intro he
    apply hz
    simp [S,he]
  have hzk : z^2 ≠ k := by
    intro he
    apply hz
    apply mem_union_left
    apply mem_union_right
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots (by decide : 0<2)).mpr he)
  have hznk : z^2 ≠ -k := by
    intro he
    apply hz
    apply mem_union_right
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots (by decide : 0<2)).mpr he)
  have hzdiv : (k/z)*z=k := div_mul_cancel₀ k hz0
  have hp : z+k/z ≠ 0 := by
    intro he
    apply hznk
    linear_combination z*he-hzdiv
  have hm : z-k/z ≠ 0 := by
    intro he
    apply hzk
    linear_combination z*he+hzdiv
  refine ⟨(z+k/z)/2,(z-k/z)/2,div_ne_zero hp h2,div_ne_zero hm h2,?_⟩
  field_simp
  ring

def graph (H : (F × F) → (F × F) → F) : SimpleGraph (Row F ⊕ Column F) :=
  Erdos714Coding.graph (code H)

lemma adj_iff (H : (F × F) → (F × F) → F) (r : Row F) (y : Column F) :
    (graph H).Adj (.inl r) (.inr y) ↔ code H r y.1=y.2 := by
  rcases y with ⟨z,d⟩
  exact Erdos714Coding.mem_symbols (code H) r z d

/-- A constant third divided difference gives a common coordinate circuit
for all q^4 messages. -/
theorem not_free_of_constant_delta (H : (F × F) → (F × F) → F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hq : 3 < Fintype.card F)
    (hd : ∀ u v, delta H u=delta H v) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph H) := by
  intro hf
  let e : Fin 4 ↪ Coord F := ⟨fun i => ((sites i,0),0),by
    intro i j he
    exact sites_injective h2 h3 (congrArg (fun z : Coord F => z.1.1) he)⟩
  have hc (r : Row F) : code H r (e 3)=
      3*code H r (e 1)+code H r (e 2)-3*code H r (e 0)+delta H (0,0) := by
    have he := hd r.1.1 (0,0)
    dsimp [delta] at he
    dsimp [e,code,sites,delta]
    linear_combination he
  have hb := Erdos714CoordinateCircuits.three_coordinate_bound (code H) e
    (fun x y z => 3*y+z-3*x+delta H (0,0)) hc hf
  have hb' : Fintype.card F^3*Fintype.card F ≤ Fintype.card F^3*3 := by
    simpa only [Row,Fintype.card_prod,mul_comm,mul_left_comm,mul_assoc,pow_succ,pow_zero,one_mul,mul_one]
      using hb
  have hh := Nat.le_of_mul_le_mul_left hb' (pow_pos Fintype.card_pos 3)
  omega


private def sign (b : Bool) : F := if b then -1 else 1

omit [Fintype F] in
private lemma sign_injective (h2 : (2 : F) ≠ 0) :
    Function.Injective (sign (F := F)) := by
  intro i j he
  cases i <;> cases j <;> try rfl
  all_goals dsimp [sign] at he
  · exact False.elim (h2 (by linear_combination he))
  · exact False.elim (h2 (by linear_combination -he))

/-- Four roots of the derived one-variable compatibility equation give
an actual K44, with two rows in each of two different fibers. -/
def two_fiber_copy (H : (F × F) → (F × F) → F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (u v : F × F) (huv : u ≠ v) (m x y b K : F) (hx : x ≠ 0) (hy : y ≠ 0)
    (hc : ∀ i : Fin 4,
      H u (sites i,0)-H v (sites i,0)+
      (u.1-v.1)*(b-2*m*sites i)^2+(u.2-v.2)*(b-2*m*sites i)^3+
      (x^2-y^2)*sites i=K) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph H) := by
  let label (g : Bool) : F × F := if g then v else u
  let radius (g : Bool) : F := if g then y else x
  let offset (g : Bool) : F := if g then 0 else K
  have hl : Function.Injective label := by
    intro i j he
    cases i <;> cases j <;> simp_all [label]
  have hr (g : Bool) : radius g ≠ 0 := by cases g <;> assumption
  let L₀ : Bool × Bool ↪ Row F := ⟨fun i =>
    ((label i.1,m+sign i.2*radius i.1),(m+sign i.2*radius i.1)*b+offset i.1),by
      rintro ⟨g,s⟩ ⟨g',s'⟩ he
      have hg : g=g' := hl (congrArg (fun r : Row F => r.1.1) he)
      subst g'
      have ha := congrArg (fun r : Row F => r.1.2) he
      have hs : sign s=sign s' :=
        mul_right_cancel₀ (hr g) (add_left_cancel ha)
      exact Prod.ext rfl (sign_injective h2 hs)⟩
  let d (t : F) : F := (y^2-m^2)*t+v.1*(b-2*m*t)^2+
    v.2*(b-2*m*t)^3+H v (t,0)
  let R : Fin 4 ↪ Column F := ⟨fun i =>
    (((sites i,0),b-2*m*sites i),d (sites i)),by
      intro i j he
      exact sites_injective h2 h3 (congrArg (fun z : Column F => z.1.1.1) he)⟩
  have hedge (i : Bool × Bool) (j : Fin 4) :
      (graph H).Adj (.inl (L₀ i)) (.inr (R j)) := by
    rw [adj_iff]
    rcases i with ⟨g,s⟩
    have hh := hc j
    cases g <;> cases s
    all_goals dsimp [L₀,R,code,label,radius,offset,sign,d]
    · linear_combination hh
    · linear_combination hh
    · ring
    · ring
  let e : Fin 4 ≃ Bool × Bool :=
    (finCongr (by simp : 4=Fintype.card (Bool × Bool))).trans
      (Fintype.equivFin (Bool × Bool)).symm
  let L : Fin 4 ↪ Row F := e.toEmbedding.trans L₀
  refine ⟨⟨L.sumMap R,?_⟩,(L.sumMap R).injective⟩
  intro z w hij
  cases z with
  | inl i =>
    cases w with
    | inl j => simp at hij
    | inr j => exact hedge (e i) j
  | inr j =>
    cases w with
    | inr i => simp at hij
    | inl i => exact (hedge (e i) j).symm

/-- Cubing surjective lets us match the nonzero cubic coefficient. The
quadratic coefficient fixes the line intercept, leaving a difference of
nonzero squares to supply the arbitrary linear coefficient. -/
theorem copy_of_nonconstant_delta (H : (F × F) → (F × F) → F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hq : 5 < Fintype.card F)
    (hcube : Function.Surjective (fun x : F => x^3))
    (u v : F × F) (huv : u.2 ≠ v.2) (hdelta : delta H u ≠ delta H v) :
    Nonempty ((completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph H)) := by
  let h (s : F) : F := H u (s,0)-H v (s,0)
  let d₁ := u.1-v.1
  let d₂ := u.2-v.2
  have hd₂ : d₂ ≠ 0 := sub_ne_zero.mpr huv
  have h6 := six_ne_zero h2 h3
  have hAeq : A h=(delta H u-delta H v)/6 := by
    dsimp [A,h,delta]
    ring
  have hA : A h ≠ 0 := by
    rw [hAeq]
    exact div_ne_zero (sub_ne_zero.mpr hdelta) h6
  obtain ⟨p,hp⟩ := hcube (-A h/d₂)
  change p^3 = -A h/d₂ at hp
  have hp0 : p ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide : 3 ≠ 0)] at hp
    exact (div_ne_zero (neg_ne_zero.mpr hA) hd₂) hp.symm
  have hlead : d₂*p^3 = -A h := by
    rw [hp]
    field_simp
  let b := (-B h-d₁*p^2)/(3*d₂*p^2)
  have hb : b*(3*d₂*p^2) = -B h-d₁*p^2 :=
    div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero h3 hd₂) (pow_ne_zero 2 hp0))
  have hquad : (d₁+3*d₂*b)*p^2 = -B h := by linear_combination hb
  let L := -C h-2*d₁*b*p-3*d₂*b^2*p
  obtain ⟨x,y,hx,hy,hxy⟩ := difference_nonzero_squares h2 hq L
  let m := -p/2
  let K := h 0+d₁*b^2+d₂*b^3
  have hm (s : F) : b-2*m*s=b+p*s := by dsimp [m]; field_simp; ring
  have hcompat (i : Fin 4) :
      H u (sites i,0)-H v (sites i,0)+
      (u.1-v.1)*(b-2*m*sites i)^2+(u.2-v.2)*(b-2*m*sites i)^3+
      (x^2-y^2)*sites i=K := by
    change h (sites i)+d₁*(b-2*m*sites i)^2+d₂*(b-2*m*sites i)^3+
      (x^2-y^2)*sites i=K
    rw [hm,interpolate h2 h3 h i,hxy]
    dsimp [L,K]
    linear_combination (sites i)^3*hlead+(sites i)^2*hquad
  exact ⟨two_fiber_copy H h2 h3 u v
    (fun he => huv (congrArg Prod.snd he)) m x y b K hx hy hcompat⟩

/-- All gluing data fail over odd fields larger than five with cubing
bijective and characteristic different from three. -/
theorem not_free (H : (F × F) → (F × F) → F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hq : 5 < Fintype.card F)
    (hcube : Function.Surjective (fun x : F => x^3)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph H) := by
  by_cases hd : ∀ u v, delta H u=delta H v
  · exact not_free_of_constant_delta H h2 h3 (by omega) hd
  · obtain ⟨u,v,huv,hdelta⟩ := delta_pair H hd
    exact fun hf => hf (copy_of_nonconstant_delta H h2 h3 hq hcube u v huv hdelta)

lemma cube_surjective_of_card_mod (hq : Fintype.card F % 3=2) :
    Function.Surjective (fun x : F => x^3) := by
  intro x
  by_cases hx : x=0
  · subst x
    exact ⟨0,by simp⟩
  let k := Fintype.card F/3
  have he : (2*k+1)*3=(Fintype.card F-1)*2+1 := by
    have hd := Nat.mod_add_div (Fintype.card F) 3
    dsimp [k]
    omega
  refine ⟨x^(2*k+1),?_⟩
  change (x^(2*k+1))^3=x
  rw [←pow_mul,he,pow_add,pow_mul,FiniteField.pow_card_sub_one_eq_one x hx]
  simp

theorem not_free_of_card_mod (H : (F × F) → (F × F) → F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hq : 5 < Fintype.card F) (hmod : Fintype.card F % 3=2) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph H) :=
  not_free H h2 h3 hq (cube_surjective_of_card_mod hmod)

/-- A version with only field-order conditions: every q>5 with q=5 mod 6. -/
theorem not_free_of_card_mod_six (H : (F × F) → (F × F) → F)
    (hq : 5 < Fintype.card F) (hmod : Fintype.card F % 6=5) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph H) := by
  have h2 : (2 : F) ≠ 0 := by
    intro he
    have hc := CharP.ringChar_of_prime_eq_zero (by decide : Nat.Prime 2) he
    have hm := FiniteField.even_card_of_char_two hc
    omega
  have h3 : (3 : F) ≠ 0 := by
    intro he
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hc := CharP.ringChar_of_prime_eq_zero (by decide : Nat.Prime 3) he
    have hd : 3 ∣ Fintype.card F :=
      (prime_dvd_char_iff_dvd_card (R := F) 3).mp (by rw [hc])
    have hm := Nat.mod_eq_zero_of_dvd hd
    omega
  exact not_free_of_card_mod H h2 h3 hq (by omega)

theorem edge_count (H : (F × F) → (F × F) → F) :
    (graph H).edgeFinset.card=Fintype.card F^7 := by
  rw [graph,Erdos714Coding.edge_count]
  simp only [Row,Coord,Fintype.card_prod]
  ring

omit [Field F] in
theorem vertex_count : Fintype.card (Row F ⊕ Column F)=2*Fintype.card F^4 := by
  simp only [Row,Coord,Column,Fintype.card_sum,Fintype.card_prod]
  ring

end Erdos714TwoSidedRouting

#print axioms Erdos714TwoSidedRouting.difference_nonzero_squares
#print axioms Erdos714TwoSidedRouting.not_free_of_constant_delta
#print axioms Erdos714TwoSidedRouting.two_fiber_copy
#print axioms Erdos714TwoSidedRouting.copy_of_nonconstant_delta
#print axioms Erdos714TwoSidedRouting.not_free
#print axioms Erdos714TwoSidedRouting.not_free_of_card_mod
#print axioms Erdos714TwoSidedRouting.not_free_of_card_mod_six
#print axioms Erdos714TwoSidedRouting.edge_count
#print axioms Erdos714TwoSidedRouting.vertex_count
