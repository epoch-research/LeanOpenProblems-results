import Submission.QuadraticLatticeLines
import Submission.QuadraticLocalAdmissibility

/-!
Two-dimensional root-lattice estimates for irreducible binary quadratics.
This module is auxiliary and does not construct a cube-Sidon root set.
-/
namespace Erdos1206.QuadraticRootLattice
open Finset QuadraticLatticeLines
open scoped Classical
set_option maxHeartbeats 1000000

/-- A convenient natural-number coefficient bound. -/
def mass (a b c : ℤ) : ℕ := a.natAbs+b.natAbs+c.natAbs+1

lemma mass_pos (a b c : ℤ) : 0 < mass a b c := by
  dsimp [mass]
  omega

lemma form_abs_le (a b c : ℤ) (x : Vec) :
    |form a b c x| ≤ (mass a b c : ℤ)*(ht x)^2 := by
  have hH := ht_nonneg x
  have hx : |x.1| ≤ ht x := le_max_left _ _
  have hy : |x.2| ≤ ht x := le_max_right _ _
  have hx2 : |x.1|^2 ≤ (ht x)^2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 : |x.2|^2 ≤ (ht x)^2 := pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hxy : |x.1| * |x.2| ≤ (ht x)^2 := by
    simpa only [pow_two] using mul_le_mul hx hy (abs_nonneg _) hH
  have hm : (mass a b c : ℤ)=|a| + |b| + |c| + 1 := by
    simp [mass]
  calc
    |form a b c x| ≤ |a*x.1^2| + |b*x.1*x.2| + |c*x.2^2| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |a| * |x.1|^2+|b| * (|x.1| * |x.2|)+|c| * |x.2|^2 := by
      simp only [abs_mul,abs_pow]
      ring
    _ ≤ |a| * (ht x)^2+|b| * (ht x)^2+|c| * (ht x)^2 := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hx2 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hxy (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hy2 (abs_nonneg _))
    _ ≤ (mass a b c : ℤ)*(ht x)^2 := by
      rw [hm]
      nlinarith [sq_nonneg (ht x)]

/-- The only property of irreducibility used by the packing argument. -/
def Anisotropic (a b c : ℤ) : Prop := ∀ x : Vec, x ≠ 0 → form a b c x ≠ 0

/-- A nonsquare discriminant supplies the nonvanishing hypothesis over the
integers, including for indefinite forms. -/
lemma anisotropic_of_nonsquare_discriminant {a b c : ℤ}
    (hD : ¬ IsSquare (b^2-4*a*c)) : Anisotropic a b c := by
  have ha : a ≠ 0 := by
    intro hz
    apply hD
    rw [hz,mul_zero,zero_mul,sub_zero]
    exact ⟨b,by ring⟩
  intro x hx he
  have hy : x.2 ≠ 0 := by
    intro hy
    have hh : a*x.1^2=0 := by
      simpa only [form,hy,mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero] using he
    have hx1 : x.1=0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hh).resolve_left ha)
    exact hx (Prod.ext hx1 hy)
  have hid : (2*a*x.1+b*x.2)^2=(b^2-4*a*c)*x.2^2 := by
    dsimp only [form] at he
    linear_combination 4*a*he
  apply hD
  apply Rat.isSquare_intCast_iff.mp
  refine ⟨((2*a*x.1+b*x.2:ℤ):ℚ)/(x.2:ℚ),?_⟩
  rw [←pow_two,div_pow]
  have hyQ : (x.2:ℚ) ≠ 0 := by exact_mod_cast hy
  apply (eq_div_iff (pow_ne_zero 2 hyQ)).mpr
  exact_mod_cast hid.symm

lemma divisor_lower {p : ℕ} {z : ℤ} (hz : z ≠ 0) (hdiv : (p:ℤ) ∣ z) :
    (p:ℤ) ≤ |z| := by
  have hh := Int.natAbs_le_of_dvd_ne_zero hdiv hz
  simpa only [Int.natAbs_natCast,Int.natCast_natAbs] using
    (show ((p:ℤ).natAbs:ℤ) ≤ (z.natAbs:ℤ) by exact_mod_cast hh)

/-- Binning both coordinates bounds a set whose differences belong to a
quadratic root lattice. No definiteness hypothesis is needed. -/
lemma root_lattice_card {a b c : ℤ} (hQ : Anisotropic a b c)
    (S : Finset Vec) (N p H D : ℕ) (hH : 0 < H)
    (hsmall : mass a b c*(H-1)^2 < p) (hD : 2*N ≤ D*H)
    (hbox : S ⊆ QuadraticLatticeLines.box N)
    (hdiv : ∀ x∈S, ∀ y∈S, (p:ℤ) ∣ form a b c (x-y)) :
    S.card ≤ (D+1)^2 := by
  let f (x : Vec) : Vec := ((x.1+N)/(H:ℤ),(x.2+N)/(H:ℤ))
  have hHZ : (0:ℤ) < H := by exact_mod_cast hH
  have hDZ : (2:ℤ)*N ≤ (D:ℤ)*H := by exact_mod_cast hD
  have hmem : ∀ x∈S, f x ∈ Icc (0:ℤ) D ×ˢ Icc (0:ℤ) D := by
    intro x hx
    have hh := mem_box_iff.mp (hbox hx)
    have h₁ := abs_le.mp ((le_max_left |x.1| |x.2|).trans hh)
    have h₂ := abs_le.mp ((le_max_right |x.1| |x.2|).trans hh)
    apply mem_product.mpr
    constructor <;> apply mem_Icc.mpr
    · exact ⟨Int.ediv_nonneg (by omega) hHZ.le,
        Int.ediv_le_of_le_mul hHZ (by omega)⟩
    · exact ⟨Int.ediv_nonneg (by omega) hHZ.le,
        Int.ediv_le_of_le_mul hHZ (by omega)⟩
  have hinj : Set.InjOn f S := by
    intro x hx y hy he
    by_contra hxy
    have h₁ := equal_quotients_distance hHZ (congrArg Prod.fst he)
    have h₂ := equal_quotients_distance hHZ (congrArg Prod.snd he)
    change |(x.1+N)-(y.1+N)| < (H:ℤ) at h₁
    change |(x.2+N)-(y.2+N)| < (H:ℤ) at h₂
    have hht : ht (x-y) ≤ (H:ℤ)-1 := by
      dsimp [ht]
      simp only [add_sub_add_right_eq_sub] at h₁ h₂
      exact max_le (by omega) (by omega)
    have hsq := pow_le_pow_left₀ (ht_nonneg (x-y)) hht 2
    have hb := form_abs_le a b c (x-y)
    have hm : (0:ℤ) ≤ mass a b c := by positivity
    have hh := mul_le_mul_of_nonneg_left hsq hm
    have hlow := divisor_lower (hQ (x-y) (sub_ne_zero.mpr hxy)) (hdiv x hx y hy)
    have hsmallZ : (mass a b c:ℤ)*((H:ℤ)-1)^2 < p := by
      have hh' : (mass a b c:ℤ)*((H-1:ℕ):ℤ)^2 < (p:ℤ) := by exact_mod_cast hsmall
      simpa only [Nat.cast_sub hH,Nat.cast_one] using hh'
    linarith
  have hh := card_le_card_of_injOn (s := S)
    (t := Icc (0:ℤ) D ×ˢ Icc (0:ℤ) D) f hmem hinj
  simpa only [card_product,Int.card_Icc,sub_zero,Int.toNat_natCast,
    ←Nat.cast_add,Nat.cast_one,pow_two] using hh



/-- Integral mesh parameters with no square-root error term in the final bound. -/
lemma mesh_parameters {C N p : ℕ} (hC : 0 < C) (hp : 0 < p)
    (hsize : p ≤ C*N^2) :
    ∃ H D : ℕ, 0 < H ∧ C*(H-1)^2 < p ∧ 2*N ≤ D*H ∧
      p ≤ C*H^2 ∧ (D+1)*H ≤ 4*N := by
  let q := (p-1)/C
  let H := Nat.sqrt q+1
  let D := 2*N/H+1
  have hH : 0 < H := by dsimp [H]; omega
  have hsmall : C*(H-1)^2 < p := by
    have h₁ := Nat.mul_le_mul_left C (Nat.sqrt_le' q)
    have h₂ := Nat.mul_div_le (p-1) C
    dsimp [H,q] at *
    omega
  have hN : H ≤ N := by
    have hq : q < N^2 := by
      apply (Nat.div_lt_iff_lt_mul hC).mpr
      have hpred : p-1 < p := by omega
      nlinarith
    exact Nat.sqrt_lt'.mpr hq
  have hpH : p ≤ C*H^2 := by
    have h₁ := Nat.lt_mul_div_succ (p-1) hC
    have h₂ : q+1 ≤ H^2 := by
      have hh : q < (Nat.sqrt q+1)^2 := by
        simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' q
      exact Nat.succ_le_of_lt hh
    have hh := Nat.mul_le_mul_left C h₂
    dsimp only [q] at hh
    omega
  have hD : 2*N ≤ D*H := by
    have hh := Nat.lt_mul_div_succ (2*N) hH
    dsimp only [D]
    nlinarith
  have hDH : (D+1)*H ≤ 4*N := by
    have hh := Nat.div_mul_le_self (2*N) H
    dsimp only [D]
    nlinarith
  exact ⟨H,D,hH,hsmall,hD,hpH,hDH⟩

/-- The root-lattice estimate, multiplied by the modulus to avoid division. -/
theorem root_lattice_mass_bound {a b c : ℤ} (hQ : Anisotropic a b c)
    (S : Finset Vec) (N p : ℕ) (hp : 0 < p)
    (hsize : p ≤ mass a b c*N^2)
    (hbox : S ⊆ QuadraticLatticeLines.box N)
    (hdiv : ∀ x∈S, ∀ y∈S, (p:ℤ) ∣ form a b c (x-y)) :
    p*S.card ≤ 16*mass a b c*N^2 := by
  obtain ⟨H,D,hH,hsmall,hD,hpH,hDH⟩ := mesh_parameters (mass_pos a b c) hp hsize
  have hc := root_lattice_card hQ S N p H D hH hsmall hD hbox hdiv
  calc
    p*S.card ≤ p*(D+1)^2 := Nat.mul_le_mul_left p hc
    _ ≤ (mass a b c*H^2)*(D+1)^2 := Nat.mul_le_mul_right _ hpH
    _ = mass a b c*((D+1)*H)^2 := by ring
    _ ≤ mass a b c*(4*N)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hDH 2)
    _ = 16*mass a b c*N^2 := by ring

#print axioms anisotropic_of_nonsquare_discriminant
#print axioms root_lattice_mass_bound

end Erdos1206.QuadraticRootLattice
