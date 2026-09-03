import Submission.EisensteinIntegers

/-! Split primes and separating residue maps for Eisenstein integers. -/
namespace Erdos322Research.EisensteinSplitting
open EisensteinIntegers QuadraticAlgebra
set_option Elab.async false

lemma exists_third_root (p : ℕ) [Fact p.Prime] (hd : 3 ∣ p-1) :
    ∃ z : ZMod p, z^2+z+1=0 ∧ z≠1 := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hg' : orderOf g=p-1 := by
    simpa only [Nat.card_eq_fintype_card,ZMod.card_units] using hg
  let u : (ZMod p)ˣ := g^(orderOf g/3)
  have hu : orderOf u=3 := orderOf_pow_orderOf_div
    (by rw [hg']; have := (Fact.out : p.Prime).two_le; omega) (by simpa only [hg'] using hd)
  have hcube : (u : ZMod p)^3=1 := by
    have h : u^3=1 := by rw [← hu]; exact pow_orderOf_eq_one u
    exact congrArg Units.val h
  have hne : (u : ZMod p)≠1 := by
    intro h
    have he : u=1 := Units.ext h
    simp [he] at hu
  refine ⟨u,?_,hne⟩
  have hprod : ((u : ZMod p)-1)*((u : ZMod p)^2+u+1)=0 := by
    linear_combination hcube
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)

private lemma int_dvd_im {p : ℕ} {z : E} (h : (p : E) ∣ z) : (p : ℤ) ∣ z.im := by
  obtain ⟨w,hw⟩ := h
  refine ⟨w.im,?_⟩
  have hi := congrArg QuadraticAlgebra.im hw
  simpa using hi

lemma not_irreducible (p : ℕ) [Fact p.Prime] (hd : 3 ∣ p-1) :
    ¬Irreducible (p : E) := by
  intro hirr
  have hp : Prime (p : E) := irreducible_iff_prime.mp hirr
  obtain ⟨z,hz,_⟩ := exists_third_root p hd
  let a : ℤ := z.val
  let w : E := ⟨0,1⟩
  have hz' : (p : ℤ) ∣ a^2+a+1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa [a] using hz
  have he : (w-(a : E))*(star w-(a : E))=(a^2+a+1 : ℤ) := by
    ext <;> simp [w,pow_two]
    ring
  have hd' : (p : E) ∣ (w-(a : E))*(star w-(a : E)) := by
    rw [he]
    exact map_dvd (Int.castRingHom E) hz'
  have hn : ¬(p : ℤ) ∣ (1 : ℤ) := by
    exact_mod_cast (Fact.out : p.Prime).not_dvd_one
  rcases hp.dvd_or_dvd hd' with h | h
  · apply hn
    simpa [w] using int_dvd_im h
  · apply hn
    simpa [w] using (int_dvd_im h).neg_right

private lemma norm_abs_one_iff (z : E) : z.norm.natAbs=1 ↔ IsUnit z := by
  have h : z.norm.natAbs=1 ↔ z.norm=1 := by
    rw [← Int.natCast_inj]
    simp [abs_of_nonneg (EisensteinIntegers.norm_nonneg z)]
  exact h.trans EisensteinIntegers.norm_eq_one_iff

/-- Every prime equal to one modulo three is an Eisenstein norm. -/
theorem exists_prime_norm (p : ℕ) [Fact p.Prime] (hd : 3 ∣ p-1) :
    ∃ z : E, z.norm=(p : ℤ) := by
  have hpu : ¬IsUnit (p : E) := by
    intro h
    have hn := EisensteinIntegers.norm_eq_one_iff.mpr h
    rw [QuadraticAlgebra.norm_natCast] at hn
    have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    nlinarith
  have hab : ∃ a b : E, (p : E)=a*b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    have hpi := not_irreducible p hd
    simpa [irreducible_iff,hpu,not_forall,not_or] using hpi
  obtain ⟨a,b,hab,ha,hb⟩ := hab
  have hmul : a.norm.natAbs*b.norm.natAbs=p^2 := by
    rw [← Int.natAbs_mul,← map_mul,← hab,QuadraticAlgebra.norm_natCast]
    simp
  have hn := ((Fact.out : p.Prime).mul_eq_prime_sq_iff
    ((norm_abs_one_iff a).not.mpr ha) ((norm_abs_one_iff b).not.mpr hb)).mp hmul
  refine ⟨a,?_⟩
  have hh := congrArg (fun n : ℕ ↦ (n : ℤ)) hn.1
  simpa [Int.natCast_natAbs,abs_of_nonneg (EisensteinIntegers.norm_nonneg a)] using hh



/-- Evaluation at a root of the third cyclotomic polynomial. -/
def residue (p : ℕ) (z : ZMod p) (hz : z^2+z+1=0) : E →+* ZMod p :=
  (QuadraticAlgebra.lift ⟨z,by
    change z*z=(-1 : ℤ) • (1 : ZMod p)+(-1 : ℤ) • z
    simp only [neg_smul,one_smul]
    linear_combination hz⟩).toRingHom

lemma residue_apply (p : ℕ) (z : ZMod p) (hz : z^2+z+1=0) (v : E) :
    residue p z hz v=(v.re : ZMod p)+(v.im : ZMod p)*z := by
  change v.re • (1 : ZMod p)+v.im • z=_
  simp [zsmul_eq_mul]

lemma mapped_norm {p : ℕ} (f : E →+* ZMod p) (v : E) :
    (v.norm : ZMod p)=f v*f (star v) := by
  have h := congrArg f (QuadraticAlgebra.algebraMap_norm_eq_mul_star v)
  simpa using h

/-- A norm-p element cannot have both coefficients divisible by p. -/
lemma coefficients_not_both_dvd (p : ℕ) [Fact p.Prime] (v : E)
    (hv : v.norm=(p : ℤ)) : ¬((p : ℤ) ∣ v.re ∧ (p : ℤ) ∣ v.im) := by
  rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
  have hd : (p : ℤ)^2 ∣ v.norm := by
    refine ⟨a^2-a*b+b^2,?_⟩
    rw [EisensteinIntegers.norm_formula,ha,hb]
    ring
  rw [hv] at hd
  have hdN : p^2 ∣ p := by exact_mod_cast hd
  have hle := Nat.le_of_dvd (Fact.out : p.Prime).pos hdN
  have hp := (Fact.out : p.Prime).two_le
  nlinarith

lemma residue_not_both_zero (p : ℕ) [Fact p.Prime] (hp3 : p≠3)
    (z : ZMod p) (hz : z^2+z+1=0) (v : E) (hv : v.norm=(p : ℤ)) :
    ¬(residue p z hz v=0 ∧ residue p z hz (star v)=0) := by
  rintro ⟨h,hbar⟩
  have hthree : (3 : ZMod p)≠0 := by
    intro hzero
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
    exact hp3 ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd |>.resolve_left
      (Fact.out : p.Prime).ne_one)
  have hzn : 2*z+1≠0 := by
    intro hzero
    apply hthree
    linear_combination 4*hz-(2*z+1)*hzero
  rw [residue_apply] at h hbar
  simp only [QuadraticAlgebra.re_star,QuadraticAlgebra.im_star] at hbar
  push_cast at hbar
  have hprod : (v.im : ZMod p)*(2*z+1)=0 := by linear_combination h-hbar
  have him : (v.im : ZMod p)=0 := (mul_eq_zero.mp hprod).resolve_right hzn
  have hre : (v.re : ZMod p)=0 := by simpa [him] using h
  exact coefficients_not_both_dvd p v hv
    ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hre,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp him⟩

/-- Choose the orientation of a split prime so that one residue map kills
it but does not kill its conjugate. -/
theorem exists_separating_prime (p : ℕ) [Fact p.Prime] (hd : 3 ∣ p-1) :
    ∃ (v : E) (f : E →+* ZMod p), v.norm=(p : ℤ) ∧ f v=0 ∧ f (star v)≠0 := by
  obtain ⟨z,hz,_⟩ := exists_third_root p hd
  obtain ⟨v,hv⟩ := exists_prime_norm p hd
  let f := residue p z hz
  have hp3 : p≠3 := by intro h; subst p; norm_num at hd
  have hnot := residue_not_both_zero p hp3 z hz v hv
  have hprod : f v*f (star v)=0 := by
    rw [← mapped_norm f v,hv]
    simp
  rcases mul_eq_zero.mp hprod with h | h
  · exact ⟨v,f,hv,h,fun hh ↦ hnot ⟨h,hh⟩⟩
  · refine ⟨star v,f,?_,h,?_⟩
    · simpa using hv
    · simpa using (show f v≠0 from fun hh ↦ hnot ⟨hh,h⟩)

/-- A separating residue map is nonzero on every element whose norm is
not divisible by its prime. -/
theorem residue_nonzero_of_norm (p m : ℕ) [Fact p.Prime] (f : E →+* ZMod p)
    (v : E) (hv : v.norm=(m : ℤ)) (hpm : ¬p ∣ m) : f v≠0 := by
  intro h
  have hn : (m : ZMod p)=0 := by
    have hh := mapped_norm f v
    rw [hv,h,zero_mul] at hh
    simpa using hh
  exact hpm ((ZMod.natCast_eq_zero_iff m p).mp hn)

end Erdos322Research.EisensteinSplitting
