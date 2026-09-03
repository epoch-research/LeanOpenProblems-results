import Submission.AllowedAlphabetSwapRigidity

/-! Two exact residue constraints on the allowed full-alphabet carrier, and
necessary divisibility for a rational rotation. No Sidon conclusion is assumed
or deduced from these necessary conditions alone. -/
namespace Erdos773.AllowedAlphabetRotationDivisibility
open Finset AllowedAlphabetCandidate AllowedAlphabetSwapRigidity
noncomputable section
set_option maxHeartbeats 2000000

def digitSum (h : ℕ) : ℤ := 3*((h:ℤ)+1)*((h:ℤ)+2)+1

def modulus (h : ℕ) : ℤ := (base h : ℤ)*((base h : ℤ)-1)

lemma two_sum_labels (h : ℕ) :
    2*(∑ i : Fin h, (i.val+2 : ℤ)) = (h:ℤ)*((h:ℤ)+3) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
    rw [mul_add, ih]
    ring

lemma digit_sum_formula (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    7+6*(∑ i : Fin h, ((σ i).val+2 : ℤ)) = digitSum h := by
  rw [Equiv.sum_comp σ (fun i : Fin h => (i.val+2 : ℤ))]
  have hh := two_sum_labels h
  dsimp [digitSum]
  nlinarith

lemma root_mod_base_sub_one (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    (root h σ : ℤ) ≡ digitSum h [ZMOD (base h : ℤ)-1] := by
  have hb : (base h : ℤ) ≡ 1 [ZMOD (base h : ℤ)-1] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-1, by ring⟩
  have hs : (∑ i : Fin h, ((σ i).val+2 : ℤ)*(base h : ℤ)^i.val) ≡
      (∑ i : Fin h, ((σ i).val+2 : ℤ)*1) [ZMOD (base h : ℤ)-1] := by
    apply Int.ModEq.sum
    intro i _
    simpa only [one_pow] using (Int.ModEq.refl ((σ i).val+2 : ℤ)).mul (hb.pow i.val)
  have hh := ((Int.ModEq.refl 6).add (hb.pow (h+1))).add
    (((Int.ModEq.refl 6).mul hb).mul hs)
  rw [root_sum]
  convert hh using 1
  simp only [one_pow, mul_one]
  rw [show (6:ℤ)+1=7 by norm_num, digit_sum_formula]

lemma digit_sum_odd (h : ℕ) : digitSum h % 2 = 1 := by
  have hh : (h:ℤ)%2=0 ∨ (h:ℤ)%2=1 := by omega
  rcases hh with hh | hh <;>
    simp [digitSum, Int.add_emod, Int.mul_emod, hh]

lemma digit_sum_coprime (h : ℕ) : IsCoprime ((base h : ℤ)-1) (digitSum h) := by
  have hsmall : IsCoprime (digitSum h) (3*((h:ℤ)+1)) := by
    refine ⟨1,-((h:ℤ)+2),?_⟩
    dsimp [digitSum]
    ring
  have htwo : IsCoprime (digitSum h) 2 := by
    refine ⟨1,-(digitSum h/2),?_⟩
    have hh := digit_sum_odd h
    omega
  have hh := (htwo.mul_right hsmall).symm
  convert hh using 1; simp only [base, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]; ring

lemma coprime_of_congr {Q r c : ℤ} (hcop : IsCoprime Q c)
    (hc : r ≡ c [ZMOD Q]) : IsCoprime Q r := by
  obtain ⟨u,v,huv⟩ := hcop
  obtain ⟨k,hk⟩ := hc.dvd
  refine ⟨u+v*k,v,?_⟩
  linear_combination huv-v*hk

lemma root_unit (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    IsCoprime (modulus h) (root h σ : ℤ) := by
  have hb : IsCoprime (base h : ℤ) 6 := by
    refine ⟨1,-((h:ℤ)+1),?_⟩
    simp only [base, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  exact (coprime_of_congr hb (constant_residue h σ)).mul_left
    (coprime_of_congr (digit_sum_coprime h) (root_mod_base_sub_one h σ))

lemma common_residue (h : ℕ) (σ τ : Equiv.Perm (Fin h)) :
    (root h σ : ℤ) ≡ (root h τ : ℤ) [ZMOD modulus h] := by
  have hcop : IsCoprime (base h : ℤ) ((base h : ℤ)-1) := ⟨1,-1,by ring⟩
  have hb := ((constant_residue h σ).trans (constant_residue h τ).symm).dvd
  have hm := ((root_mod_base_sub_one h σ).trans (root_mod_base_sub_one h τ).symm).dvd
  exact Int.modEq_iff_dvd.mpr (hcop.mul_dvd hb hm)

/-- If four roots have one common unit residue, the sine numerator and the
cosine defect of a rational rotation become divisible by the modulus after multiplication by two. -/
lemma rotation_coefficients {Q x y z w p s q : ℤ}
    (hcop : IsCoprime Q x)
    (hxy : x ≡ y [ZMOD Q]) (hxz : x ≡ z [ZMOD Q]) (hxw : x ≡ w [ZMOD Q])
    (hrow : q*z=p*x+s*y) (hrow' : q*w= -s*x+p*y) :
    Q ∣ 2*s ∧ Q ∣ 2*(q-p) := by
  have h1 : q*x ≡ (p+s)*x [ZMOD Q] := by
    apply ((Int.ModEq.refl q).mul hxz).trans
    rw [hrow]
    convert (Int.ModEq.refl (p*x)).add ((Int.ModEq.refl s).mul hxy.symm) using 1; ring
  have h2 : q*x ≡ (p-s)*x [ZMOD Q] := by
    apply ((Int.ModEq.refl q).mul hxw).trans
    rw [hrow']
    convert (Int.ModEq.refl (-s*x)).add ((Int.ModEq.refl p).mul hxy.symm) using 1; ring
  have hsub := dvd_sub h1.dvd h2.dvd
  have hadd := dvd_add h1.dvd h2.dvd
  constructor
  · apply hcop.dvd_of_dvd_mul_left
    convert hsub using 1; ring
  · apply hcop.dvd_of_dvd_mul_left
    have hh := dvd_neg.mpr hadd
    convert hh using 1; ring

/-- The primitive half-angle parameter of such a rotation satisfies Q | 4n.
This statement retains both actual rotation equations as hypotheses. -/
lemma rotation_parameter {Q x y z w m n : ℤ}
    (hcop : IsCoprime Q x) (hmn : IsCoprime m n)
    (hxy : x ≡ y [ZMOD Q]) (hxz : x ≡ z [ZMOD Q]) (hxw : x ≡ w [ZMOD Q])
    (hrow : (m^2+n^2)*z=(m^2-n^2)*x+(2*m*n)*y)
    (hrow' : (m^2+n^2)*w= -(2*m*n)*x+(m^2-n^2)*y) : Q ∣ 4*n := by
  obtain ⟨hs,hc⟩ := rotation_coefficients hcop hxy hxz hxw hrow hrow'
  have hm : Q ∣ (4*n)*m := by convert hs using 1; ring
  have hn : Q ∣ (4*n)*n := by convert hc using 1; ring
  obtain ⟨a,b,hab⟩ := hmn
  have hh := dvd_add (dvd_mul_of_dvd_left hm a) (dvd_mul_of_dvd_left hn b)
  convert hh using 1
  linear_combination -(4*n)*hab

/-- Necessary divisibility for every primitive rational rotation between four
members of the full allowed-digit permutation carrier. -/
theorem candidate_rotation_parameter (h : ℕ) (σ τ υ ω : Equiv.Perm (Fin h))
    (m n : ℤ) (hmn : IsCoprime m n)
    (hrow : (m^2+n^2)*(root h υ : ℤ)=
      (m^2-n^2)*(root h σ : ℤ)+(2*m*n)*(root h τ : ℤ))
    (hrow' : (m^2+n^2)*(root h ω : ℤ)=
      -(2*m*n)*(root h σ : ℤ)+(m^2-n^2)*(root h τ : ℤ)) :
    modulus h ∣ 4*n :=
  rotation_parameter (root_unit h σ) hmn (common_residue h σ τ)
    (common_residue h σ υ) (common_residue h σ ω) hrow hrow'

/-- The exact common divisor of all differences, when h>=2. -/
def strongModulus (h : ℕ) : ℤ := 6*(base h : ℤ)*((base h : ℤ)-1)

lemma root_mod_six (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    (root h σ : ℤ) ≡ 1 [ZMOD 6] := by
  have hb : (base h : ℤ) ≡ 1 [ZMOD 6] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-((h:ℤ)+1),?_⟩
    simp only [base, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hr : (root h σ : ℤ) ≡ (base h : ℤ)^(h+1) [ZMOD 6] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(1+(base h : ℤ)*(∑ i : Fin h, ((σ i).val+2 : ℤ)*(base h : ℤ)^i.val)),?_⟩
    rw [root_sum]
    ring
  exact hr.trans (by simpa only [one_pow] using hb.pow (h+1))

lemma root_strong_unit (h : ℕ) (σ : Equiv.Perm (Fin h)) :
    IsCoprime (strongModulus h) (root h σ : ℤ) := by
  have hs := coprime_of_congr (show IsCoprime (6:ℤ) 1 from ⟨0,1,by norm_num⟩) (root_mod_six h σ)
  convert hs.mul_left (root_unit h σ) using 1
  dsimp [strongModulus,modulus]
  ring

lemma strong_common_residue (h : ℕ) (σ τ : Equiv.Perm (Fin h)) :
    (root h σ : ℤ) ≡ (root h τ : ℤ) [ZMOD strongModulus h] := by
  have hb : (base h : ℤ) ≡ 1 [ZMOD (base h : ℤ)-1] :=
    Int.modEq_iff_dvd.mpr ⟨-1,by ring⟩
  have hs (ρ : Equiv.Perm (Fin h)) :
      (∑ i : Fin h, ((ρ i).val+2 : ℤ)*(base h : ℤ)^i.val) ≡
        (∑ i : Fin h, (i.val+2 : ℤ)) [ZMOD (base h : ℤ)-1] := by
    have hh : (∑ i : Fin h, ((ρ i).val+2 : ℤ)*(base h : ℤ)^i.val) ≡
        (∑ i : Fin h, ((ρ i).val+2 : ℤ)) [ZMOD (base h : ℤ)-1] := by
      apply Int.ModEq.sum
      intro i _
      simpa only [one_pow,mul_one] using
        (Int.ModEq.refl ((ρ i).val+2 : ℤ)).mul (hb.pow i.val)
    simpa only [Equiv.sum_comp ρ (fun i : Fin h => (i.val+2 : ℤ))] using hh
  obtain ⟨k,hk⟩ := ((hs σ).trans (hs τ).symm).dvd
  apply Int.modEq_iff_dvd.mpr
  refine ⟨k,?_⟩
  rw [root_sum,root_sum]
  dsimp [strongModulus]
  linear_combination 6*(base h : ℤ)*hk

/-- The common modulus cannot be enlarged: an adjacent swap already realizes
exactly strongModulus as a root difference. -/
theorem common_modulus_iff {h : ℕ} (hh : 2 ≤ h) (Q : ℤ) :
    (∀ σ τ : Equiv.Perm (Fin h), (root h σ : ℤ) ≡ (root h τ : ℤ) [ZMOD Q]) ↔
      Q ∣ strongModulus h := by
  constructor
  · intro hc
    let a : Fin h := ⟨0,by omega⟩
    let b : Fin h := ⟨1,by omega⟩
    let σ : Equiv.Perm (Fin h) := Equiv.refl _
    have hd : (root h σ : ℤ)-root h (σ * Equiv.swap a b) = strongModulus h := by
      have hh := transposition_difference σ a b (by change (0:ℕ)<1; norm_num : a<b)
      simpa only [σ,a,b,Equiv.refl_apply, Nat.cast_zero, Nat.cast_one,
        sub_zero, zero_add, Nat.sub_zero, pow_one, mul_one, strongModulus] using hh
    have hx := (hc (σ * Equiv.swap a b) σ).dvd
    rwa [hd] at hx
  · intro hd σ τ
    exact Int.modEq_iff_dvd.mpr (hd.trans (strong_common_residue h σ τ).dvd)

lemma parameter_size {Q m n : ℤ} (hQ : 0 ≤ Q) (hn : n ≠ 0) (hd : Q ∣ 4*n) :
    Q ≤ 4*|n| ∧ Q^2 ≤ 16*(m^2+n^2) := by
  have hn' : 0 < |4*n| := abs_pos.mpr (mul_ne_zero (by norm_num) hn)
  have hle := Int.le_of_dvd hn' ((dvd_abs _ _).mpr hd)
  have hb : Q ≤ 4*|n| := by simpa only [abs_mul, abs_of_pos (by norm_num : (0:ℤ)<4)] using hle
  refine ⟨hb,?_⟩
  have hh := mul_self_le_mul_self hQ hb
  nlinarith [sq_nonneg m, sq_abs n]

/-- A primitive nontrivial half-angle rotation between candidate roots has
parameter denominator at least strongModulus(h)^2/16. The actual two rotation
rows remain explicit; this is not a universal small-factor transfer claim. -/
theorem candidate_rotation_lower (h : ℕ) (σ τ υ ω : Equiv.Perm (Fin h))
    (m n : ℤ) (hmn : IsCoprime m n) (hn : n ≠ 0)
    (hrow : (m^2+n^2)*(root h υ : ℤ)=
      (m^2-n^2)*(root h σ : ℤ)+(2*m*n)*(root h τ : ℤ))
    (hrow' : (m^2+n^2)*(root h ω : ℤ)=
      -(2*m*n)*(root h σ : ℤ)+(m^2-n^2)*(root h τ : ℤ)) :
    strongModulus h ∣ 4*n ∧ strongModulus h ≤ 4*|n| ∧
      (strongModulus h)^2 ≤ 16*(m^2+n^2) := by
  have hd := rotation_parameter (root_strong_unit h σ) hmn (strong_common_residue h σ τ)
    (strong_common_residue h σ υ) (strong_common_residue h σ ω) hrow hrow'
  have hQ : 0 ≤ strongModulus h := by
    have hb : (1:ℤ) < base h := by exact_mod_cast base_gt_one h
    dsimp [strongModulus]
    exact mul_nonneg (mul_nonneg (by norm_num) (by omega)) (by omega)
  exact ⟨hd,parameter_size hQ hn hd⟩

#print axioms root_mod_base_sub_one
#print axioms digit_sum_coprime
#print axioms root_unit
#print axioms common_residue
#print axioms rotation_parameter
#print axioms candidate_rotation_parameter
#print axioms common_modulus_iff
#print axioms candidate_rotation_lower
end
end Erdos773.AllowedAlphabetRotationDivisibility
