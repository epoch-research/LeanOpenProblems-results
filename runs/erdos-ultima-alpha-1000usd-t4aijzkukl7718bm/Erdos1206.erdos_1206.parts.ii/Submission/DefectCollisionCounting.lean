import Submission.NegativePellCount
import Submission.DivisorPowerBound

/-! Uniform bounds for strictly ordered cubic collisions with small root-sum
defect. This file is auxiliary to the original density conjecture. -/
namespace Erdos1206.DefectCollisionCounting
open scoped Classical

@[ext] structure Collision where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  hab : a<b
  hbc : b<c
  hcd : c<d
  equation : a^3+d^3=b^3+c^3

namespace Collision

def defect (e : Collision) : ℕ := ConicHeightProduct.defect e.a e.b e.c e.d
def gap (e : Collision) : ℕ := e.b-e.a
def secondGap (e : Collision) : ℕ := e.c-e.a
def ordinate (e : Collision) : ℕ := 2*e.secondGap-e.defect
def abscissa (e : Collision) : ℕ := 3*(e.b^2+e.c^2-(e.a^2+e.d^2))

lemma defect_pos (e : Collision) : 0<e.defect :=
  ConicHeightProduct.defect_pos e.hab e.hbc e.hcd e.equation

lemma defect_lt_gap (e : Collision) : e.defect<e.gap := by
  have hh := ConicHeightProduct.adjacent_gap_difference e.hab e.hbc e.hcd e.equation
  have := e.hcd
  change e.gap=(e.d-e.c)+e.defect at hh
  omega

lemma gap_lt_secondGap (e : Collision) : e.gap<e.secondGap := by
  have := e.hab
  have := e.hbc
  dsimp [gap,secondGap]
  omega

lemma ordinate_pos (e : Collision) : 0<e.ordinate := by
  have := e.defect_lt_gap
  have := e.gap_lt_secondGap
  dsimp [ordinate]
  omega

lemma ordinate_le (e : Collision) : e.ordinate≤2*e.d := by
  have := e.hcd
  dsimp [ordinate,secondGap]
  omega

/-- For equal sums of cubes, the inner pair has the larger sum of squares. -/
lemma square_sum_lt (e : Collision) : e.a^2+e.d^2<e.b^2+e.c^2 := by
  have hab := e.hab
  have hbc := e.hbc
  have hcd := e.hcd
  have he := e.equation
  have h1 : 2*(e.b^3-e.a^3)≤3*e.b*(e.b^2-e.a^2) := by
    have ha2 := Nat.sub_add_cancel (Nat.pow_le_pow_left hab.le 2)
    have ha3 := Nat.sub_add_cancel (Nat.pow_le_pow_left hab.le 3)
    have hp : 0≤((e.b:ℤ)-e.a)^2*((e.b:ℤ)+2*e.a) := by positivity
    have hpN : 3*e.b*e.a^2+2*e.b^3≤3*e.b^3+2*e.a^3 := by exact_mod_cast (by nlinarith only [hp] : (3:ℤ)*e.b*e.a^2+2*e.b^3≤3*e.b^3+2*e.a^3)
    nlinarith
  have h2 : 3*e.c*(e.d^2-e.c^2)<2*(e.d^3-e.c^3) := by
    have hc2 := Nat.sub_add_cancel (Nat.pow_le_pow_left hcd.le 2)
    have hc3 := Nat.sub_add_cancel (Nat.pow_le_pow_left hcd.le 3)
    have hp : 0<((e.d:ℤ)-e.c)^2*(2*(e.d:ℤ)+e.c) := by
      have hd : 0<(e.d:ℤ)-e.c := by
        have hh : (e.c:ℤ)<e.d := by exact_mod_cast hcd
        omega
      have hdpos : 0<(e.d:ℤ) := by exact_mod_cast (show 0<e.d by omega)
      positivity
    have hpN : 3*e.c*e.d^2+2*e.c^3<2*e.d^3+3*e.c^3 := by exact_mod_cast (by nlinarith only [hp] : (3:ℤ)*e.c*e.d^2+2*e.c^3<2*e.d^3+3*e.c^3)
    nlinarith
  have h3 := Nat.mul_le_mul_right (e.d^2-e.c^2) (Nat.mul_le_mul_left 3 hbc.le)
  have hdiff : e.b^3-e.a^3=e.d^3-e.c^3 := by omega
  rw [←hdiff] at h2
  have hgap : e.d^2-e.c^2<e.b^2-e.a^2 := by
    by_contra hh
    have h4 := Nat.mul_le_mul_left (3*e.b) (show e.b^2-e.a^2≤e.d^2-e.c^2 by omega)
    omega
  have ha2 := Nat.sub_add_cancel (Nat.pow_le_pow_left hab.le 2)
  have hc2 := Nat.sub_add_cancel (Nat.pow_le_pow_left hcd.le 2)
  omega

lemma abscissa_relation (e : Collision) :
    e.abscissa+6*e.gap*e.secondGap=6*e.defect*e.d+3*e.defect^2 := by
  have hk := ConicHeightProduct.root_sum_lt e.hab e.hbc e.hcd e.equation
  have hs := e.square_sum_lt
  have hcast : (e.abscissa:ℤ)+6*e.gap*e.secondGap=6*e.defect*e.d+3*(e.defect:ℤ)^2 := by
    simp only [abscissa,gap,secondGap,defect,ConicHeightProduct.defect,
      Nat.cast_mul,Nat.cast_sub hs.le,Nat.cast_add,Nat.cast_pow,Nat.cast_sub e.hab.le,
      Nat.cast_sub (e.hab.trans e.hbc).le,Nat.cast_sub hk.le,Nat.cast_ofNat]
    ring
  exact_mod_cast hcast

lemma norm_equation (e : Collision) :
    e.abscissa^2+3*e.defect^2*(3*e.gap*(e.gap-e.defect)+e.defect^2)=
      (9*e.gap*(e.gap-e.defect))*e.ordinate^2 := by
  have hh := DefectPellSeparation.collision_pell_equation e.hab e.hbc e.hcd e.equation
  have hgap := e.defect_lt_gap
  have hsgap := e.gap_lt_secondGap
  have hrel := e.abscissa_relation
  have hrelI : (e.abscissa:ℤ)+6*e.gap*e.secondGap=6*e.defect*e.d+3*(e.defect:ℤ)^2 := by exact_mod_cast hrel
  have haI : 3*(2*(e.gap:ℤ)*e.secondGap-2*e.defect*e.d-(e.defect:ℤ)^2)=-(e.abscissa:ℤ) := by linarith
  have hgapI : (e.gap:ℤ)=(e.b:ℤ)-e.a := by simp only [gap,Nat.cast_sub e.hab.le]
  have hsgapI : (e.secondGap:ℤ)=(e.c:ℤ)-e.a := by simp only [secondGap,Nat.cast_sub (e.hab.trans e.hbc).le]
  change (3*(2*((e.b:ℤ)-e.a)*((e.c:ℤ)-e.a)-2*e.defect*e.d-(e.defect:ℤ)^2))^2-
    9*((e.b:ℤ)-e.a)*((e.b:ℤ)-e.a-e.defect)*(2*((e.c:ℤ)-e.a)-e.defect)^2=
      -(3*(e.defect:ℤ)^2*(3*((e.b:ℤ)-e.a)*((e.b:ℤ)-e.a-e.defect)+(e.defect:ℤ)^2)) at hh
  rw [←hgapI,←hsgapI,haI,neg_sq] at hh
  have hY : (e.ordinate:ℤ)=2*(e.secondGap:ℤ)-e.defect := by
    simp only [ordinate,Nat.cast_sub (show e.defect≤2*e.secondGap by omega),Nat.cast_mul,Nat.cast_ofNat]
  have hX : ((e.gap-e.defect:ℕ):ℤ)=(e.gap:ℤ)-e.defect := Nat.cast_sub hgap.le
  zify
  rw [hX,hY]
  linarith

/-- The defect, first adjacent gap, and Pell ordinate uniquely determine an
ordered collision. Positivity selects one sign of the norm equation. -/
lemma eq_of_coordinates {e f : Collision}
    (hk : e.defect=f.defect) (hx : e.gap=f.gap) (hy : e.ordinate=f.ordinate) : e=f := by
  have hy' : e.secondGap=f.secondGap := by
    have he1 := e.defect_lt_gap
    have he2 := e.gap_lt_secondGap
    have hf1 := f.defect_lt_gap
    have hf2 := f.gap_lt_secondGap
    dsimp [ordinate] at hy
    omega
  have he := e.norm_equation
  have hf := f.norm_equation
  rw [hk,hx,hy] at he
  have ha : e.abscissa=f.abscissa := by nlinarith
  have hr := e.abscissa_relation
  rw [hk,hx,hy',ha] at hr
  have hr' := f.abscissa_relation
  have hd : e.d=f.d := by nlinarith [f.defect_pos]
  have hegap : e.a+e.gap=e.b := Nat.add_sub_of_le e.hab.le
  have hesgap : e.a+e.secondGap=e.c := Nat.add_sub_of_le (e.hab.trans e.hbc).le
  have hfgap : f.a+f.gap=f.b := Nat.add_sub_of_le f.hab.le
  have hfsgap : f.a+f.secondGap=f.c := Nat.add_sub_of_le (f.hab.trans f.hbc).le
  have hek := ConicHeightProduct.root_sum_lt e.hab e.hbc e.hcd e.equation
  have hfk := ConicHeightProduct.root_sum_lt f.hab f.hbc f.hcd f.equation
  change e.b+e.c-(e.a+e.d)=f.b+f.c-(f.a+f.d) at hk
  apply Collision.ext <;> omega

end Collision

open Finset

def discriminant (k x : ℕ) : ℕ := 9*x*(x-k)
def norm (k x : ℕ) : ℕ := 3*k^2*(3*x*(x-k)+k^2)

lemma norm_pos {k x : ℕ} (hk : 0<k) : 0<norm k x := by
  dsimp [norm]
  positivity

lemma discriminant_pos {k x : ℕ} (hk : 0<k) (hkx : k<x) :
    0<discriminant k x := by
  dsimp [discriminant]
  have hx : 0<x := lt_trans hk hkx
  have hxk : 0<x-k := Nat.sub_pos_of_lt hkx
  positivity

lemma gcd_norm_discriminant_le {k x : ℕ} (hk : 0<k) :
    Nat.gcd (norm k x) (discriminant k x) ≤ 3*k^4 := by
  have he : norm k x = k^2*discriminant k x+3*k^4 := by
    dsimp [norm,discriminant]
    ring
  have h1 : Nat.gcd (norm k x) (discriminant k x) ∣ k^2*discriminant k x :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
  have h2 := Nat.gcd_dvd_left (norm k x) (discriminant k x)
  conv_rhs at h2 => rw [he]
  have hh : Nat.gcd (norm k x) (discriminant k x) ∣ 3*k^4 :=
    (Nat.dvd_add_iff_right h1).mpr h2
  exact Nat.le_of_dvd (by positivity) hh

lemma norm_le {k x : ℕ} (hkx : k≤x) : norm k x ≤ 12*k^2*x^2 := by
  have h1 : x*(x-k)≤x^2 := by nlinarith [Nat.sub_le x k]
  have h2 := Nat.pow_le_pow_left hkx 2
  have hh : 3*x*(x-k)+k^2≤4*x^2 := by nlinarith
  have ht := Nat.mul_le_mul_left (3*k^2) hh
  dsimp [norm]
  nlinarith only [ht]

/-- Uniform counting on one fixed-defect, fixed-gap slice. -/
theorem fixed_slice_card_le {k x N : ℕ} {s : Finset Collision}
    (hk : 0<k) (hkx : k<x)
    (hs : ∀ e∈s, e.defect=k ∧ e.gap=x ∧ e.d≤N) :
    s.card ≤ 6*k^4*(norm k x).divisors.card^2*(Nat.log 2 (2*N)+1) := by
  have hinj : Set.InjOn Collision.ordinate (s : Set Collision) := by
    intro e he f hf hy
    exact Collision.eq_of_coordinates ((hs e he).1.trans (hs f hf).1.symm)
      ((hs e he).2.1.trans (hs f hf).2.1.symm) hy
  have hcard := card_image_iff.mpr hinj
  have hcount := NegativePellCount.all_card_le (discriminant_pos hk hkx) (norm_pos hk)
    (s := s.image Collision.ordinate) (N := 2*N) (by
      intro y hy
      obtain ⟨e,he,rfl⟩ := mem_image.mp hy
      obtain ⟨hek,hex,hed⟩ := hs e he
      refine ⟨e.ordinate_pos,e.ordinate_le.trans (Nat.mul_le_mul_left 2 hed),e.abscissa,?_⟩
      have hh := e.norm_equation
      rw [hek,hex] at hh
      exact hh)
  rw [hcard] at hcount
  have hgc := gcd_norm_discriminant_le (x := x) hk
  calc
    s.card ≤ 2*Nat.gcd (norm k x) (discriminant k x)*
      (norm k x).divisors.card^2*(Nat.log 2 (2*N)+1) := hcount
    _ ≤ 2*(3*k^4)*(norm k x).divisors.card^2*(Nat.log 2 (2*N)+1) := by gcongr
    _ = _ := by ring

private lemma exists_divisor_coefficient :
    ∃ C : ℕ, ∀ m : ℕ, 0 < m → m.divisors.card^80≤C*m :=
  ⟨DivisorPowerBound.constant 80, fun _ hm => DivisorPowerBound.card_divisors_pow_le 80 hm⟩

/-- A divisor-function coefficient, kept abstract to avoid evaluating an
enormous closed natural-number expression during kernel reduction. -/
noncomputable def divisorCoefficient : ℕ := exists_divisor_coefficient.choose

lemma divisorCoefficient_spec {m : ℕ} (hm : 0 < m) :
    m.divisors.card^80≤divisorCoefficient*m :=
  exists_divisor_coefficient.choose_spec m hm

noncomputable def countConstant : ℕ := 588*divisorCoefficient+1

private lemma square_bound_of_power_bound {T C m j : ℕ}
    (hpow : T^80≤C*m) (hbound : m≤588*2^(36*j)) :
    T^2 ≤ (588*C+1)*2^j := by
  have hc : 588*C≤(588*C+1)^40 :=
    (Nat.le_add_right _ 1).trans (Nat.le_self_pow (by decide : 40≠0) (588*C+1))
  apply (Nat.pow_le_pow_iff_left (by decide : 40≠0)).mp
  calc
    (T^2)^40 = T^80 := by rw [←pow_mul]
    _ ≤ C*m := hpow
    _ ≤ C*(588*2^(36*j)) := Nat.mul_le_mul_left _ hbound
    _ ≤ (588*C+1)^40*2^(40*j) := by
      have hh := Nat.pow_le_pow_right (by decide : 0<2) (show 36*j≤40*j by omega)
      nlinarith [Nat.mul_le_mul hc hh]
    _ = ((588*C+1)*2^j)^40 := by rw [mul_pow,←pow_mul]; congr 2; omega

lemma divisors_sq_at_cutoff {m j : ℕ} (hm : 0 < m) (hbound : m≤588*2^(36*j)) :
    m.divisors.card^2 ≤ countConstant*2^j :=
  square_bound_of_power_bound (divisorCoefficient_spec hm) hbound

lemma gap_at_cutoff {e : Collision} {j : ℕ}
    (hk : e.defect≤2^j) (hd : e.d≤2^(32*j)) : e.gap≤7*2^(17*j) := by
  have hh := ConicHeightProduct.adjacent_gap_sq_bound e.hab e.hbc e.hcd e.equation
  change 3*e.gap^2≤7*e.defect*e.d at hh
  have hmul := Nat.mul_le_mul hk hd
  have hp : 2^j*2^(32*j)≤2^(34*j) := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide : 0<2) (by omega)
  have hb : e.gap^2≤(7*2^(17*j))^2 := by
    have hle := hmul.trans hp
    rw [mul_pow,←pow_mul]
    norm_num
    have he : 17*j*2=34*j := by omega
    rw [he]
    nlinarith
  exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp hb

lemma norm_at_cutoff {k x j : ℕ} (hkx : k≤x)
    (hk : k≤2^j) (hx : x≤7*2^(17*j)) : norm k x≤588*2^(36*j) := by
  have hh := norm_le hkx
  have hkk := Nat.pow_le_pow_left hk 2
  have hxx := Nat.pow_le_pow_left hx 2
  calc
    norm k x ≤ 12*k^2*x^2 := hh
    _ ≤ 12*(2^j)^2*(7*2^(17*j))^2 := by gcongr
    _ = 588*2^(36*j) := by
      rw [mul_pow,←pow_mul,←pow_mul]
      ring

lemma log_at_cutoff (j : ℕ) : Nat.log 2 (2*2^(32*j))+1≤34*2^j := by
  have hlog : Nat.log 2 (2*2^(32*j))+1=32*j+2 := by
    rw [Nat.mul_comm 2 (2^(32*j)),Nat.log_mul_base (by decide) (by positivity),
      Nat.log_pow (by decide)]
  rw [hlog]
  have hh := Nat.lt_two_pow_self (n := j)
  omega

/-- Every finite family of collisions in the simultaneous cutoff box has
an explicit sublinear cardinality bound in the maximum-root cutoff. -/
theorem box_card_le {j : ℕ} {s : Finset Collision}
    (hs : ∀ e∈s, e.defect≤2^j ∧ e.d≤2^(32*j)) :
    s.card ≤ 1428*countConstant*2^(24*j) := by
  let I := (Icc 1 (2^j)) ×ˢ (Icc 1 (7*2^(17*j)))
  let T (p : ℕ × ℕ) := s.filter (fun e => e.defect=p.1 ∧ e.gap=p.2)
  have hsub : s ⊆ I.biUnion T := by
    intro e he
    obtain ⟨hk,hd⟩ := hs e he
    apply mem_biUnion.mpr
    refine ⟨(e.defect,e.gap),?_,mem_filter.mpr ⟨he,rfl,rfl⟩⟩
    apply mem_product.mpr
    exact ⟨mem_Icc.mpr ⟨e.defect_pos,hk⟩,
      mem_Icc.mpr ⟨by have := e.defect_pos; have := e.defect_lt_gap; omega,gap_at_cutoff hk hd⟩⟩
  have hT (p : ℕ × ℕ) (hp : p∈I) : (T p).card≤204*countConstant*2^(6*j) := by
    obtain ⟨hkpos,hk⟩ := mem_Icc.mp (mem_product.mp hp).1
    obtain ⟨_,hx⟩ := mem_Icc.mp (mem_product.mp hp).2
    by_cases hn : (T p).Nonempty
    · obtain ⟨e,he⟩ := hn
      obtain ⟨_,hek,hex⟩ := mem_filter.mp he
      have hkx : p.1<p.2 := by rw [←hek,←hex]; exact e.defect_lt_gap
      have hcount := fixed_slice_card_le hkpos hkx (s := T p) (N := 2^(32*j)) (by
        intro f hf
        obtain ⟨hfs,hfk,hfx⟩ := mem_filter.mp hf
        exact ⟨hfk,hfx,(hs f hfs).2⟩)
      have hdvd := divisors_sq_at_cutoff (norm_pos hkpos) (norm_at_cutoff hkx.le hk hx)
      have hlog := log_at_cutoff j
      calc
        (T p).card ≤ 6*p.1^4*(norm p.1 p.2).divisors.card^2*
          (Nat.log 2 (2*2^(32*j))+1) := hcount
        _ ≤ 6*(2^j)^4*(countConstant*2^j)*(34*2^j) := by gcongr
        _ = 204*countConstant*2^(6*j) := by
          rw [←pow_mul]
          ring
    · simp only [not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.zero_le]
  calc
    s.card ≤ (I.biUnion T).card := card_le_card hsub
    _ ≤ ∑p∈I,(T p).card := card_biUnion_le
    _ ≤ ∑_p∈I,(204*countConstant*2^(6*j)) := sum_le_sum hT
    _ = I.card*(204*countConstant*2^(6*j)) := by simp
    _ = 1428*countConstant*2^(24*j) := by
      simp only [I,card_product,Nat.card_Icc,Nat.add_sub_cancel]
      ring

#print axioms Collision.square_sum_lt
#print axioms Collision.norm_equation
#print axioms Collision.eq_of_coordinates
#print axioms box_card_le
end Erdos1206.DefectCollisionCounting
