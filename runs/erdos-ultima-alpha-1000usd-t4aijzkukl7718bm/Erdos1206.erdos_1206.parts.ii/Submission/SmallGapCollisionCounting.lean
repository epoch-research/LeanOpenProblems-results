import Submission.DefectCollisionCounting
import Submission.PositivePellCount

/-! Uniform cubic-collision counts with a small upper adjacent gap. -/
namespace Erdos1206.DefectCollisionCounting.Collision
open scoped Classical

def smallGap (e : Collision) : ℕ := e.d-e.c
def gapOrdinate (e : Collision) : ℕ := e.a+e.b
def gapAbscissa (e : Collision) : ℕ := 3*e.smallGap*(e.c+e.d)

lemma smallGap_pos (e : Collision) : 0<e.smallGap := Nat.sub_pos_of_lt e.hcd

lemma smallGap_lt_gap (e : Collision) : e.smallGap<e.gap := by
  have hh := ConicHeightProduct.adjacent_gap_difference e.hab e.hbc e.hcd e.equation
  change e.gap=e.smallGap+e.defect at hh
  have := e.defect_pos
  omega

lemma gapOrdinate_pos (e : Collision) : 0<e.gapOrdinate := by
  have := e.hab
  dsimp [gapOrdinate]
  omega

lemma gapOrdinate_le (e : Collision) : e.gapOrdinate≤2*e.d := by
  have := e.hab
  have := e.hbc
  have := e.hcd
  dsimp [gapOrdinate]
  omega

lemma gap_cube_bound (e : Collision) : e.gap^3≤3*e.smallGap*e.d^2 := by
  have hx : e.a+e.gap=e.b := Nat.add_sub_of_le e.hab.le
  have hh : e.c+e.smallGap=e.d := Nat.add_sub_of_le e.hcd.le
  have he := e.equation
  have hlow : e.gap^3+e.a^3≤e.b^3 := by
    rw [←hx]
    nlinarith [Nat.zero_le (e.a^2*e.gap),Nat.zero_le (e.a*e.gap^2)]
  have hup : e.d^3≤3*e.smallGap*e.d^2+e.c^3 := by
    rw [←hh]
    nlinarith [Nat.zero_le (e.c*e.smallGap^2),Nat.zero_le (e.smallGap^3)]
  omega

lemma gap_norm_equation (e : Collision) :
    e.gapAbscissa^2=(9*e.gap*e.smallGap)*e.gapOrdinate^2+
      3*e.smallGap*(e.gap^3-e.smallGap^3) := by
  have hx : e.a+e.gap=e.b := Nat.add_sub_of_le e.hab.le
  have hh : e.c+e.smallGap=e.d := Nat.add_sub_of_le e.hcd.le
  have he := e.equation
  rw [←hx,←hh] at he
  have he' : (3*e.smallGap*(e.c+(e.c+e.smallGap)))^2+3*e.smallGap*e.smallGap^3=
      (9*e.gap*e.smallGap)*(e.a+(e.a+e.gap))^2+3*e.smallGap*e.gap^3 := by
    linear_combination 12*e.smallGap*he
  have ht := Nat.sub_add_cancel (Nat.pow_le_pow_left e.smallGap_lt_gap.le 3)
  have hm := congrArg (fun n : ℕ => 3*e.smallGap*n) ht
  dsimp [gapAbscissa,gapOrdinate]
  rw [←hx,←hh]
  nlinarith only [he',hm]

lemma eq_of_gap_coordinates {e f : Collision}
    (hx : e.gap=f.gap) (hh : e.smallGap=f.smallGap)
    (hy : e.gapOrdinate=f.gapOrdinate) : e=f := by
  have hea : e.a+e.gap=e.b := Nat.add_sub_of_le e.hab.le
  have hfa : f.a+f.gap=f.b := Nat.add_sub_of_le f.hab.le
  have ha : e.a=f.a := by dsimp [gapOrdinate] at hy; omega
  have hb : e.b=f.b := by omega
  have hen := e.gap_norm_equation
  have hfn := f.gap_norm_equation
  rw [hx,hh,hy] at hen
  have hX : e.gapAbscissa=f.gapAbscissa := by nlinarith
  have hsum : e.c+e.d=f.c+f.d := by
    dsimp [gapAbscissa] at hX
    rw [hh] at hX
    nlinarith [f.smallGap_pos]
  have hec : e.c+e.smallGap=e.d := Nat.add_sub_of_le e.hcd.le
  have hfc : f.c+f.smallGap=f.d := Nat.add_sub_of_le f.hcd.le
  apply DefectCollisionCounting.Collision.ext <;> omega

end Erdos1206.DefectCollisionCounting.Collision

namespace Erdos1206.SmallGapCollisionCounting
open DefectCollisionCounting Finset
open scoped Classical

def discriminant (h x : ℕ) : ℕ := 9*x*h
def norm (h x : ℕ) : ℕ := 3*h*(x^3-h^3)

lemma discriminant_pos {h x : ℕ} (hh : 0<h) (hhx : h<x) :
    0<discriminant h x := by
  have hx : 0<x := lt_trans hh hhx
  dsimp [discriminant]
  positivity

lemma norm_pos {h x : ℕ} (hh : 0<h) (hhx : h<x) : 0<norm h x := by
  have hp := Nat.pow_lt_pow_left hhx (by decide : 3≠0)
  have hs : 0<x^3-h^3 := Nat.sub_pos_of_lt hp
  dsimp [norm]
  positivity

lemma gcd_norm_discriminant_le {h x : ℕ} (hh : 0<h) (hhx : h≤x) :
    Nat.gcd (norm h x) (discriminant h x)≤9*h^4 := by
  let g := Nat.gcd (norm h x) (discriminant h x)
  have h1 : g∣9*h*x^3 := by
    have hd := dvd_mul_of_dvd_left (Nat.gcd_dvd_right (norm h x) (discriminant h x)) (x^2)
    convert hd using 1
    dsimp [discriminant,g]
    ring
  have h2 : g∣3*norm h x := dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) 3
  have hid : 3*norm h x+9*h^4=9*h*x^3 := by
    have hp := Nat.sub_add_cancel (Nat.pow_le_pow_left hhx 3)
    dsimp [norm]
    nlinarith only [congrArg (fun n : ℕ => 9*h*n) hp]
  have h3 : g∣9*h^4 := (Nat.dvd_add_iff_right h2).mpr (hid ▸ h1)
  exact Nat.le_of_dvd (by positivity) h3

lemma norm_le (h x : ℕ) : norm h x≤3*h*x^3 := by
  dsimp [norm]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- Uniform counting with both adjacent gaps fixed. -/
theorem fixed_slice_card_le {h x N : ℕ} {s : Finset Collision}
    (hh : 0<h) (hhx : h<x)
    (hs : ∀e∈s,e.smallGap=h ∧ e.gap=x ∧ e.d≤N) :
    s.card≤18*h^4*(norm h x).divisors.card^2*(Nat.log 2 (2*N)+1) := by
  have hinj : Set.InjOn Collision.gapOrdinate (s : Set Collision) := by
    intro e he f hf hy
    exact Collision.eq_of_gap_coordinates ((hs e he).2.1.trans (hs f hf).2.1.symm)
      ((hs e he).1.trans (hs f hf).1.symm) hy
  have hcard := card_image_iff.mpr hinj
  have hcount := PositivePellCount.all_card_le (discriminant_pos hh hhx) (norm_pos hh hhx)
    (s := s.image Collision.gapOrdinate) (N := 2*N) (by
      intro y hy
      obtain ⟨e,he,rfl⟩ := mem_image.mp hy
      obtain ⟨heh,hex,hed⟩ := hs e he
      refine ⟨e.gapOrdinate_pos,e.gapOrdinate_le.trans (Nat.mul_le_mul_left 2 hed),e.gapAbscissa,?_⟩
      have ht := e.gap_norm_equation
      rw [heh,hex] at ht
      exact ht)
  rw [hcard] at hcount
  have hgc := gcd_norm_discriminant_le hh hhx.le
  calc
    s.card≤2*Nat.gcd (norm h x) (discriminant h x)*
      (norm h x).divisors.card^2*(Nat.log 2 (2*N)+1) := hcount
    _ ≤ 2*(9*h^4)*(norm h x).divisors.card^2*(Nat.log 2 (2*N)+1) := by gcongr
    _ = _ := by ring

private lemma exists_divisor_coefficient :
    ∃ C : ℕ, ∀ m : ℕ, 0 < m → m.divisors.card^240≤C*m :=
  ⟨DivisorPowerBound.constant 240, fun _ hm => DivisorPowerBound.card_divisors_pow_le 240 hm⟩

noncomputable def divisorCoefficient : ℕ := exists_divisor_coefficient.choose

lemma divisorCoefficient_spec {m : ℕ} (hm : 0 < m) :
    m.divisors.card^240≤divisorCoefficient*m :=
  exists_divisor_coefficient.choose_spec m hm

noncomputable def countConstant : ℕ := 81*divisorCoefficient+1

private lemma square_bound_of_power_bound {T C m j : ℕ}
    (hpow : T^240≤C*m) (hbound : m≤81*2^(100*j)) :
    T^2 ≤ (81*C+1)*2^j := by
  have hc : 81*C≤(81*C+1)^120 :=
    (Nat.le_add_right _ 1).trans (Nat.le_self_pow (by decide : 120≠0) (81*C+1))
  apply (Nat.pow_le_pow_iff_left (by decide : 120≠0)).mp
  calc
    (T^2)^120 = T^240 := by rw [←pow_mul]
    _ ≤ C*m := hpow
    _ ≤ C*(81*2^(100*j)) := Nat.mul_le_mul_left _ hbound
    _ ≤ (81*C+1)^120*2^(120*j) := by
      have hh := Nat.pow_le_pow_right (by decide : 0<2) (show 100*j≤120*j by omega)
      nlinarith [Nat.mul_le_mul hc hh]
    _ = ((81*C+1)*2^j)^120 := by rw [mul_pow,←pow_mul]; congr 2; omega

lemma divisors_sq_at_cutoff {m j : ℕ} (hm : 0 < m) (hbound : m≤81*2^(100*j)) :
    m.divisors.card^2≤countConstant*2^j :=
  square_bound_of_power_bound (divisorCoefficient_spec hm) hbound

lemma gap_at_cutoff {e : Collision} {j : ℕ}
    (hh : e.smallGap≤2^j) (hd : e.d≤2^(48*j)) : e.gap≤3*2^(33*j) := by
  have hc := e.gap_cube_bound
  have hmul := Nat.mul_le_mul hh (Nat.pow_le_pow_left hd 2)
  have hp : 2^j*(2^(48*j))^2≤2^(99*j) := by
    rw [←pow_mul,←pow_add]
    exact Nat.pow_le_pow_right (by decide : 0<2) (by omega)
  have hb : e.gap^3≤(3*2^(33*j))^3 := by
    have hle := hmul.trans hp
    rw [mul_pow,←pow_mul]
    norm_num
    have he : 33*j*3=99*j := by omega
    rw [he]
    nlinarith
  exact (Nat.pow_le_pow_iff_left (by decide : 3≠0)).mp hb

lemma norm_at_cutoff {h x j : ℕ}
    (hh : h≤2^j) (hx : x≤3*2^(33*j)) : norm h x≤81*2^(100*j) := by
  calc
    norm h x≤3*h*x^3 := norm_le h x
    _ ≤ 3*(2^j)*(3*2^(33*j))^3 := by gcongr
    _ = 81*2^(100*j) := by
      rw [mul_pow,←pow_mul]
      ring

lemma log_at_cutoff (j : ℕ) : Nat.log 2 (2*2^(48*j))+1≤50*2^j := by
  have hlog : Nat.log 2 (2*2^(48*j))+1=48*j+2 := by
    rw [Nat.mul_comm 2 (2^(48*j)),Nat.log_mul_base (by decide) (by positivity),
      Nat.log_pow (by decide)]
  rw [hlog]
  have hh := Nat.lt_two_pow_self (n := j)
  omega

/-- A simultaneous cutoff estimate for all small-upper-gap collisions. -/
theorem box_card_le {j : ℕ} {s : Finset Collision}
    (hs : ∀e∈s,e.smallGap≤2^j ∧ e.d≤2^(48*j)) :
    s.card≤2700*countConstant*2^(40*j) := by
  let I := (Icc 1 (2^j)) ×ˢ (Icc 1 (3*2^(33*j)))
  let T (p : ℕ × ℕ) := s.filter (fun e => e.smallGap=p.1 ∧ e.gap=p.2)
  have hsub : s ⊆ I.biUnion T := by
    intro e he
    obtain ⟨hh,hd⟩ := hs e he
    apply mem_biUnion.mpr
    refine ⟨(e.smallGap,e.gap),?_,mem_filter.mpr ⟨he,rfl,rfl⟩⟩
    apply mem_product.mpr
    exact ⟨mem_Icc.mpr ⟨e.smallGap_pos,hh⟩,
      mem_Icc.mpr ⟨by have := e.smallGap_pos; have := e.smallGap_lt_gap; omega,gap_at_cutoff hh hd⟩⟩
  have hT (p : ℕ × ℕ) (hp : p∈I) : (T p).card≤900*countConstant*2^(6*j) := by
    obtain ⟨hhpos,hh⟩ := mem_Icc.mp (mem_product.mp hp).1
    obtain ⟨_,hx⟩ := mem_Icc.mp (mem_product.mp hp).2
    by_cases hn : (T p).Nonempty
    · obtain ⟨e,he⟩ := hn
      obtain ⟨_,heh,hex⟩ := mem_filter.mp he
      have hhx : p.1<p.2 := by rw [←heh,←hex]; exact e.smallGap_lt_gap
      have hcount := fixed_slice_card_le hhpos hhx (s := T p) (N := 2^(48*j)) (by
        intro f hf
        obtain ⟨hfs,hfh,hfx⟩ := mem_filter.mp hf
        exact ⟨hfh,hfx,(hs f hfs).2⟩)
      have hdvd := divisors_sq_at_cutoff (norm_pos hhpos hhx) (norm_at_cutoff hh hx)
      have hlog := log_at_cutoff j
      calc
        (T p).card≤18*p.1^4*(norm p.1 p.2).divisors.card^2*
          (Nat.log 2 (2*2^(48*j))+1) := hcount
        _ ≤ 18*(2^j)^4*(countConstant*2^j)*(50*2^j) := by gcongr
        _ = 900*countConstant*2^(6*j) := by rw [←pow_mul]; ring
    · simp only [not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.zero_le]
  calc
    s.card≤(I.biUnion T).card := card_le_card hsub
    _ ≤ ∑p∈I,(T p).card := card_biUnion_le
    _ ≤ ∑_p∈I,(900*countConstant*2^(6*j)) := sum_le_sum hT
    _ = I.card*(900*countConstant*2^(6*j)) := by simp
    _ = 2700*countConstant*2^(40*j) := by
      simp only [I,card_product,Nat.card_Icc,Nat.add_sub_cancel]
      ring

#print axioms Collision.gap_cube_bound
#print axioms Collision.gap_norm_equation
#print axioms fixed_slice_card_le
#print axioms box_card_le
end Erdos1206.SmallGapCollisionCounting
