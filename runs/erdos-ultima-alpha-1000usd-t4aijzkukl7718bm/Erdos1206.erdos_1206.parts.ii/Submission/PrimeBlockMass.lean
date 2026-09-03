import Submission.PrimitiveCollisionMass

/-! Prime-indexed quadratic-height families: excluding one affine bad residue
per prime still leaves divergent reciprocal height mass. -/
namespace Erdos1206.PrimeBlockMass
open PrimitiveCollisionMass (LargePrime large_prime_reciprocals_not_summable)

/-- A general block-counting lemma with an arbitrary fixed positive constant. -/
lemma height_not_summable {I : LargePrime → Type*} [∀ p, Fintype (I p)]
    (height : ((p : LargePrime) × I p) → ℕ)
    (hpos : ∀ x, 0<height x) (K C : ℝ) (hK : 0<K) (hC : 0<C)
    (hcard : ∀ p : LargePrime, (p.val:ℝ) ≤ C*Fintype.card (I p))
    (hbound : ∀ x, (height x:ℝ) ≤ K*(x.1.val:ℝ)^2) :
    ¬ Summable (fun x => (1:ℝ)/height x) := by
  intro hs
  let block : LargePrime → ℝ := fun p => ∑ j : I p, (1:ℝ)/height ⟨p,j⟩
  have hblocks := ((summable_sigma_of_nonneg
    (fun x => (by positivity : (0:ℝ) ≤ 1/height x))).mp hs).2
  have hsum : Summable block := by simpa only [block,tsum_fintype] using hblocks
  have hlower (p : LargePrime) : (1:ℝ)/(C*K*p.val) ≤ block p := by
    have hp : (0:ℝ)<p.val := by exact_mod_cast p.property.1.pos
    have hc := hcard p
    calc
      _ ≤ (Fintype.card (I p):ℝ)/(K*(p.val:ℝ)^2) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_right hc (show (0:ℝ) ≤ K*p.val by positivity)]
      _ = ∑ _j : I p, (1:ℝ)/(K*(p.val:ℝ)^2) := by simp [div_eq_mul_inv]
      _ ≤ block p := by
        apply Finset.sum_le_sum
        intro j hj
        exact one_div_le_one_div_of_le (by exact_mod_cast hpos ⟨p,j⟩) (hbound _)
  have hsmall : Summable (fun p : LargePrime => (1:ℝ)/(C*K*p.val)) :=
    hsum.of_nonneg_of_le (fun _ => by positivity) hlower
  apply large_prime_reciprocals_not_summable
  convert hsmall.mul_left (C*K) using 1
  funext p
  have hp : (p.val:ℝ) ≠ 0 := by exact_mod_cast p.property.1.ne_zero
  field_simp

/-- At most one small parameter has a numerator divisible by its prime
homogeneous denominator. -/
lemma bad_affine_unique (L : ℕ) (p : LargePrime) {i j : Fin (p.val/12)}
    (hi : p.val ∣ 1+L*i.val) (hj : p.val ∣ 1+L*j.val) : i=j := by
  have hcop : Nat.Coprime p.val L := by
    apply p.property.1.coprime_iff_not_dvd.mpr
    intro hpL
    have hprod : p.val ∣ L*i.val := dvd_mul_of_dvd_left hpL i.val
    have h1 : p.val ∣ 1 := (Nat.dvd_add_iff_right hprod).mpr (by simpa [add_comm] using hi)
    exact p.property.1.ne_one (Nat.dvd_one.mp h1)
  have he : Nat.ModEq p.val (1+L*i.val) (1+L*j.val) := by
    simp only [Nat.ModEq,Nat.mod_eq_zero_of_dvd hi,Nat.mod_eq_zero_of_dvd hj]
  have hh := Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one
    ((Nat.ModEq.refl 1).add_left_cancel he)
  exact Fin.ext (hh.eq_of_lt_of_lt (i.isLt.trans_le (Nat.div_le_self _ _))
    (j.isLt.trans_le (Nat.div_le_self _ _)))

abbrev Good (L : ℕ) (p : LargePrime) := {j : Fin (p.val/12) // ¬ p.val ∣ 1+L*j.val}
abbrev Index (L : ℕ) := (p : LargePrime) × Good L p

lemma good_card (L : ℕ) (p : LargePrime) : p.val ≤ 48*Fintype.card (Good L p) := by
  have hbad : Fintype.card {j : Fin (p.val/12) // p.val ∣ 1+L*j.val} ≤ 1 := by
    apply Fintype.card_le_one_iff.mpr
    intro i j
    exact Subtype.ext (bad_affine_unique L p i.property j.property)
  have hc := Fintype.card_subtype_compl (fun j : Fin (p.val/12) => p.val ∣ 1+L*j.val)
  simp only [Fintype.card_fin] at hc
  change Fintype.card (Good L p)=p.val/12-Fintype.card {j : Fin (p.val/12) // p.val ∣ 1+L*j.val} at hc
  have hp := p.property.2
  omega

lemma good_height_not_summable (L : ℕ) (height : Index L → ℕ)
    (hpos : ∀ x, 0<height x) (K : ℝ) (hK : 0<K)
    (hbound : ∀ x, (height x:ℝ) ≤ K*(x.1.val:ℝ)^2) :
    ¬ Summable (fun x => (1:ℝ)/height x) :=
  height_not_summable height hpos K 48 hK (by norm_num)
    (fun p => by exact_mod_cast good_card L p) hbound

#print axioms height_not_summable
#print axioms good_card
#print axioms good_height_not_summable
end Erdos1206.PrimeBlockMass
