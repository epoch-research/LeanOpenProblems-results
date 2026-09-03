import Submission.PositivePellSeparation
import Submission.NegativePellCount

/-! Uniform counting for positive-norm Pell equations using modular classes.
These are auxiliary counting results, not a solution of the Sidon conjecture. -/
namespace Erdos1206.PositivePellCount
open Finset
open scoped Classical

/-- One residue class has only logarithmically many possible positive
second coordinates. -/
theorem residue_card_le {D m r N : ℕ} {s : Finset ℕ}
    (hD : 0 < D) (hm : 0 < m) (hr : Nat.ModEq m (r^2) D)
    (hs : ∀ y∈s, 0<y ∧ y≤N ∧ ∃ x : ℕ,
      x^2=D*y^2+m ∧ Nat.ModEq m x (r*y)) :
    s.card ≤ Nat.log 2 N+1 := by
  apply NegativePellCount.doubling_card_le (fun y hy => (hs y hy).1) (fun y hy => (hs y hy).2.1)
  intro y hy z hz hyz
  obtain ⟨hypos,_,x,he,hx⟩ := hs y hy
  obtain ⟨_,_,x',he',hx'⟩ := hs z hz
  have heI : (x:ℤ)^2-(D:ℤ)*y^2=(m:ℤ) := by
    have hh : (x:ℤ)^2=(D:ℤ)*y^2+m := by exact_mod_cast he
    linarith
  have heI' : (x':ℤ)^2-(D:ℤ)*z^2=(m:ℤ) := by
    have hh : (x':ℤ)^2=(D:ℤ)*z^2+m := by exact_mod_cast he'
    linarith
  have hxI : (m:ℤ) ∣ (x:ℤ)-(r:ℤ)*y := by
    have hh := Nat.modEq_iff_dvd.mp hx.symm
    simpa only [Nat.cast_mul] using hh
  have hxI' : (m:ℤ) ∣ (x':ℤ)-(r:ℤ)*z := by
    have hh := Nat.modEq_iff_dvd.mp hx'.symm
    simpa only [Nat.cast_mul] using hh
  have hrI : (m:ℤ) ∣ (r:ℤ)^2-D := by
    simpa only [Nat.cast_pow] using Nat.modEq_iff_dvd.mp hr.symm
  have hxp : 0 < x := by nlinarith
  have hxp' : 0 < x' := by nlinarith
  have hh := PositivePellSeparation.pell_residue_doubling
    (by exact_mod_cast hD) (by exact_mod_cast hm)
    (by exact_mod_cast hxp) (by exact_mod_cast hxp') (by exact_mod_cast hypos)
    (by exact_mod_cast hyz) heI heI' hxI hxI' hrI
  exact_mod_cast hh

lemma coprime_second_coordinate {D m x y : ℕ}
    (he : x^2=D*y^2+m) (hc : x.Coprime y) : y.Coprime m := by
  let g := Nat.gcd y m
  have hgy : g∣y := Nat.gcd_dvd_left _ _
  have hgm : g∣m := Nat.gcd_dvd_right _ _
  have hgx : g∣x^2 := by
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_pow hgy (by decide : 2≠0)) _) hgm
  have hg1 : g∣1 := by
    have hh := Nat.dvd_gcd hgx hgy
    rwa [(hc.pow_left 2).gcd_eq_one] at hh
  exact Nat.dvd_one.mp hg1

/-- Primitive solutions admit a projective square-root residue modulo the
absolute norm. -/
theorem exists_root_residue {D m x y : ℕ} (hm : 0 < m)
    (he : x^2=D*y^2+m) (hc : x.Coprime y) :
    ∃ r∈ModularSquareRootBound.roots m D, Nat.ModEq m x (r*y) := by
  letI : NeZero m := ⟨hm.ne'⟩
  have hcy := coprime_second_coordinate he hc
  let u := ZMod.unitOfCoprime y hcy
  let z : ZMod m := (x : ZMod m)*↑u⁻¹
  have hu : (u : ZMod m)=y := ZMod.coe_unitOfCoprime _ _
  have hz : z*(y : ZMod m)=x := by
    dsimp [z]
    rw [←hu,mul_assoc,Units.inv_mul, mul_one]
  have heZ : (x:ZMod m)^2=(D:ZMod m)*y^2 := by
    have hh := congrArg (fun n : ℕ => (n:ZMod m)) he
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,ZMod.natCast_self,add_zero] using hh
  have hz2 : z^2=(D:ZMod m) := by
    dsimp [z]
    rw [mul_pow,heZ,←hu]
    calc
      (D : ZMod m)*↑u^2*(↑u⁻¹)^2 = (D:ZMod m)*(↑u*↑u⁻¹)^2 := by ring
      _ = (D:ZMod m) := by simp
  refine ⟨z.val,mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt z),?_⟩,?_⟩
  · apply (ZMod.natCast_eq_natCast_iff _ _ m).mp
    push_cast
    simpa only [ZMod.natCast_zmod_val] using hz2
  · apply (ZMod.natCast_eq_natCast_iff _ _ m).mp
    push_cast
    simpa only [ZMod.natCast_zmod_val] using hz.symm

/-- Uniform primitive-solution bound. Only the divisor count, a gcd, and a
logarithm remain; there is no discriminant-dependent implicit constant. -/
theorem primitive_card_le {D m N : ℕ} {s : Finset ℕ}
    (hD : 0 < D) (hm : 0 < m)
    (hs : ∀ y∈s, 0<y ∧ y≤N ∧ ∃ x : ℕ,
      x^2=D*y^2+m ∧ x.Coprime y) :
    s.card ≤ 2*Nat.gcd m D*m.divisors.card*(Nat.log 2 N+1) := by
  let R := ModularSquareRootBound.roots m D
  have hex (y : ℕ) (hy : y∈s) : ∃ r∈R, ∃ x : ℕ,
      x^2=D*y^2+m ∧ Nat.ModEq m x (r*y) := by
    obtain ⟨_,_,x,he,hc⟩ := hs y hy
    obtain ⟨r,hr,hres⟩ := exists_root_residue hm he hc
    exact ⟨r,hr,x,he,hres⟩
  let T (r : ℕ) := s.filter (fun y => ∃ x : ℕ, x^2=D*y^2+m ∧ Nat.ModEq m x (r*y))
  have hsub : s ⊆ R.biUnion T := by
    intro y hy
    obtain ⟨r,hr,hx⟩ := hex y hy
    exact mem_biUnion.mpr ⟨r,hr,mem_filter.mpr ⟨hy,hx⟩⟩
  calc
    s.card ≤ (R.biUnion T).card := card_le_card hsub
    _ ≤ ∑r∈R,(T r).card := card_biUnion_le
    _ ≤ ∑_r∈R,(Nat.log 2 N+1) := by
      apply sum_le_sum
      intro r hr
      apply residue_card_le hD hm (mem_filter.mp hr).2
      intro y hy
      obtain ⟨hys,hres⟩ := mem_filter.mp hy
      exact ⟨(hs y hys).1,(hs y hys).2.1,hres⟩
    _ = R.card*(Nat.log 2 N+1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (ModularSquareRootBound.roots_card_le hm)

/-- Divide a solution by the gcd of its coordinates. The norm acquires the
square of this gcd, and the remaining solution is primitive. -/
lemma normalize_solution {D m x y : ℕ} (hy : 0<y)
    (he : x^2=D*y^2+m) :
    let g := Nat.gcd x y
    0<g ∧ g^2∣m ∧ (x/g)^2=D*(y/g)^2+m/g^2 ∧
      (x/g).Coprime (y/g) ∧ 0<y/g := by
  let g := Nat.gcd x y
  have hg : 0<g := Nat.gcd_pos_of_pos_right _ hy
  have hgx : g∣x := Nat.gcd_dvd_left _ _
  have hgy : g∣y := Nat.gcd_dvd_right _ _
  have hxid : x=g*(x/g) := (Nat.mul_div_cancel' hgx).symm
  have hyid : y=g*(y/g) := (Nat.mul_div_cancel' hgy).symm
  have hgm : g^2∣m := by
    have h1 : g^2∣x^2 := pow_dvd_pow_of_dvd hgx 2
    have h2 : g^2∣D*y^2 := dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hgy 2) D
    rw [he] at h1
    exact (Nat.dvd_add_iff_right h2).mpr h1
  have hnorm : (x/g)^2=D*(y/g)^2+m/g^2 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hg 2)
    calc
      g^2*(x/g)^2 = (g*(x/g))^2 := by rw [mul_pow]
      _ = D*(g*(y/g))^2+m := by rw [←hxid,←hyid,he]
      _ = g^2*(D*(y/g)^2+m/g^2) := by
        rw [mul_add,Nat.mul_div_cancel' hgm,mul_pow]
        ring
  exact ⟨hg,hgm,hnorm,Nat.coprime_div_gcd_div_gcd hg,
    Nat.div_pos (Nat.le_of_dvd hy hgy) hg⟩

/-- All solutions, including imprimitive ones, satisfy a uniform bound
with the square of the divisor count. -/
theorem all_card_le {D m N : ℕ} {s : Finset ℕ}
    (hD : 0 < D) (hm : 0 < m)
    (hs : ∀ y∈s, 0<y ∧ y≤N ∧ ∃ x : ℕ, x^2=D*y^2+m) :
    s.card ≤ 2*Nat.gcd m D*m.divisors.card^2*(Nat.log 2 N+1) := by
  let G := m.divisors.filter (fun g => g^2∣m)
  let T (g : ℕ) := (range (N+1)).filter (fun y =>
    0<y ∧ ∃ x : ℕ, x^2=D*y^2+m/g^2 ∧ x.Coprime y)
  have hT (g : ℕ) (hg : g∈G) :
      (T g).card ≤ 2*Nat.gcd m D*m.divisors.card*(Nat.log 2 N+1) := by
    have hg2 : g^2∣m := (mem_filter.mp hg).2
    have hgm : g∣m := (Nat.mem_divisors.mp (mem_filter.mp hg).1).1
    have hgpos : 0<g := Nat.pos_of_dvd_of_pos hgm hm
    have hm' : 0 < m/g^2 := Nat.div_pos (Nat.le_of_dvd hm hg2) (pow_pos hgpos 2)
    have hdiv : m/g^2∣m := Nat.div_dvd_of_dvd hg2
    have hcount := primitive_card_le hD hm' (s := T g) (N := N) (by
      intro y hy
      obtain ⟨hyN,hypos,hx⟩ := mem_filter.mp hy
      exact ⟨hypos,by have := mem_range.mp hyN; omega,hx⟩)
    have hgc : Nat.gcd (m/g^2) D ≤ Nat.gcd m D :=
      Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hm) (Nat.gcd_dvd_gcd_of_dvd_left D hdiv)
    have hdc : (m/g^2).divisors.card ≤ m.divisors.card :=
      card_le_card (Nat.divisors_subset_of_dvd hm.ne' hdiv)
    exact hcount.trans (by gcongr)
  have hsub : s ⊆ G.biUnion (fun g => (T g).image (fun y => g*y)) := by
    intro y hy
    obtain ⟨hypos,hyN,x,he⟩ := hs y hy
    let g := Nat.gcd x y
    obtain ⟨hgpos,hg2,hnorm,hcop,hy'⟩ := normalize_solution hypos he
    have hgm : g∣m := (dvd_pow_self g (by decide : 2≠0)).trans hg2
    have hgG : g∈G := mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hgm,hm.ne'⟩,hg2⟩
    apply mem_biUnion.mpr
    refine ⟨g,hgG,mem_image.mpr ⟨y/g,?_,?_⟩⟩
    · apply mem_filter.mpr
      exact ⟨mem_range.mpr (by have := Nat.div_le_self y g; omega),hy',x/g,hnorm,hcop⟩
    · exact Nat.mul_div_cancel' (Nat.gcd_dvd_right x y)
  calc
    s.card ≤ (G.biUnion (fun g => (T g).image (fun y => g*y))).card := card_le_card hsub
    _ ≤ ∑g∈G,((T g).image (fun y => g*y)).card := card_biUnion_le
    _ ≤ ∑g∈G,(2*Nat.gcd m D*m.divisors.card*(Nat.log 2 N+1)) :=
      sum_le_sum fun g hg => (card_image_le).trans (hT g hg)
    _ = G.card*(2*Nat.gcd m D*m.divisors.card*(Nat.log 2 N+1)) := by simp
    _ ≤ m.divisors.card*(2*Nat.gcd m D*m.divisors.card*(Nat.log 2 N+1)) := by
      exact Nat.mul_le_mul_right _ (card_filter_le _ _)
    _ = _ := by ring

#print axioms residue_card_le
#print axioms exists_root_residue
#print axioms primitive_card_le
#print axioms all_card_le
end Erdos1206.PositivePellCount
