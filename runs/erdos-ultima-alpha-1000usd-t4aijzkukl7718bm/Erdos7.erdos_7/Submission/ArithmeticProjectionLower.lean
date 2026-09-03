import Submission.ArithmeticReduction
import Submission.PureProjectionLower

/-! Arithmetic specialization of the lower projection bound for a present
mixed modulus. This remains a necessary condition, not a solution of Erdős7. -/
namespace Erdos7ArithmeticProjectionLower
open scoped BigOperators
open Erdos7PureProjectionLower Erdos7Reduction
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def cylinder (p E a : ℕ) [NeZero p] (r : ℤ) : Finset (ZMod (p^E)) :=
  Finset.univ.filter (fun x => (x.val : ZMod (p^a)) = (r : ZMod (p^a)))

noncomputable def uniform (p E : ℕ) [NeZero p] (_ : ZMod (p^E)) : ℝ := 1/(p:ℝ)^E

lemma uniform_nonneg (p E : ℕ) [NeZero p] (x : ZMod (p^E)) : 0 ≤ uniform p E x := by
  unfold uniform
  positivity

lemma uniform_mass (p E : ℕ) [NeZero p] : (∑ x, uniform p E x) = 1 := by
  simp only [uniform,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,Nat.cast_pow]
  have hp : (p:ℝ)^E ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  field_simp

lemma mem_cylinder (p E a : ℕ) [NeZero p] (r : ℤ) (x : ZMod (p^E)) :
    x ∈ cylinder p E a r ↔ ((p^a:ℕ):ℤ) ∣ (x.val:ℤ)-r := by
  simp only [cylinder,Finset.mem_filter,Finset.mem_univ,true_and]
  have hh := ZMod.intCast_eq_intCast_iff_dvd_sub r (x.val:ℤ) (p^a)
  simpa only [Int.cast_natCast,eq_comm] using hh

lemma cylinder_mass (p E a : ℕ) [NeZero p] (r : ℤ) (ha : a ≤ E) :
    mass (uniform p E) (cylinder p E a r) = ((p:ℝ)⁻¹)^a := by
  let f := ZMod.castHom (pow_dvd_pow p ha) (ZMod (p^a))
  have hset : cylinder p E a r = Finset.univ.filter (fun x => f x = (r:ZMod (p^a))) := by
    ext x
    simp only [cylinder,Finset.mem_filter,Finset.mem_univ,true_and,
      f,ZMod.castHom_apply,ZMod.cast_eq_val]
  have hh := Erdos7StarSieve.surjective_fiber_card_rat f.toAddMonoidHom
    (ZMod.castHom_surjective (pow_dvd_pow p ha)) (r:ZMod (p^a))
  change ((Finset.univ.filter (fun x => f x = (r:ZMod (p^a)))).card:ℚ) = _ at hh
  rw [← hset] at hh
  have hc : ((cylinder p E a r).card:ℝ) = (p:ℝ)^E/(p:ℝ)^a := by
    have hcast := congrArg (fun q : ℚ => (q:ℝ)) hh
    simpa only [ZMod.card,Rat.cast_natCast,Rat.cast_div,Rat.cast_pow,Nat.cast_pow] using hcast
  simp only [mass,uniform,Finset.sum_const,nsmul_eq_mul,hc,inv_pow]
  have hp : (p:ℝ)^E ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  field_simp

lemma cylinder_disjoint (p E a b : ℕ) [NeZero p] (r s : ℤ) (hab : a ≤ b)
    (hsep : ¬ ((p^a:ℕ):ℤ) ∣ s-r) :
    Disjoint (cylinder p E a r) (cylinder p E b s) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' := (mem_cylinder p E a r x).mp hx
  have hy' := (mem_cylinder p E b s x).mp hy
  have hd : ((p^a:ℕ):ℤ) ∣ ((p^b:ℕ):ℤ) := by exact_mod_cast pow_dvd_pow p hab
  have hh := dvd_sub hx' (hd.trans hy')
  apply hsep
  convert hh using 1 <;> ring

lemma geom_succ (r : ℝ) (E : ℕ) : geom r (E+1) = r+r*geom r E := by
  unfold geom
  rw [Finset.sum_range_succ',Finset.mul_sum]
  simp only [Nat.zero_add,pow_one]
  have hh : (∑ k ∈ Finset.range E, r^(k+1+1)) = ∑ k ∈ Finset.range E, r*r^(k+1) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ,mul_comm]
  rw [hh,add_comm]

lemma geom_le_half (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1/3) (E : ℕ) :
    geom r E ≤ 1/2 := by
  induction E with
  | zero => norm_num [geom]
  | succ E ih =>
    rw [geom_succ]
    have hh := mul_le_mul_of_nonneg_left ih hr
    nlinarith

lemma inv_le_third (p : ℕ) (hp : 3 ≤ p) : (p:ℝ)⁻¹ ≤ 1/3 := by
  have hpr : (3:ℝ) ≤ p := by exact_mod_cast hp
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) hpr

/-- Irredundance gives all the concrete disjointness hypotheses needed by
conditioning on the pure-power complement. -/
theorem pure_family_disjoint {ι : Type*} (m : ι → ℕ) (a : ι → ℤ)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j:ℤ) ∣ x-a j)
    (hc : ∀ x : ℤ, ∃ i, (m i:ℤ) ∣ x-a i)
    (p E : ℕ) [NeZero p] (hp : 2 ≤ p) (pure : ℕ → ι)
    (hpure : ∀ j, 1 ≤ j → j ≤ E → m (pure j) = p^j) :
    ∀ i j, 1 ≤ i → i ≤ E → 1 ≤ j → j ≤ E → i ≠ j →
      Disjoint (cylinder p E i (a (pure i))) (cylinder p E j (a (pure j))) := by
  have hcase (i j : ℕ) (hi : 1 ≤ i) (hiE : i ≤ E) (hj : 1 ≤ j) (hjE : j ≤ E)
      (hij : i < j) :
      Disjoint (cylinder p E i (a (pure i))) (cylinder p E j (a (pure j))) := by
    have hne : pure i ≠ pure j := by
      intro he
      have hpow : p^i = p^j := by rw [← hpure i hi hiE,← hpure j hj hjE,he]
      exact (ne_of_lt hij) (Nat.pow_right_injective hp hpow)
    have hd : m (pure i) ∣ m (pure j) := by
      rw [hpure i hi hiE,hpure j hj hjE]
      exact pow_dvd_pow p hij.le
    have hs := residue_not_congruent_of_proper_modulus_divisor m a hpriv hc hne hd
    rw [hpure i hi hiE] at hs
    exact cylinder_disjoint p E i j _ _ hij.le hs
  intro i j hi hiE hj hjE hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hcase i j hi hiE hj hjE hlt
  · exact (hcase j i hj hjE hi hiE hgt).symm

lemma mixed_cylinder_disjoint {ι : Type*} (m : ι → ℕ) (a : ι → ℤ)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j:ℤ) ∣ x-a j)
    (hc : ∀ x : ℤ, ∃ i, (m i:ℤ) ∣ x-a i)
    (p E : ℕ) [NeZero p] (pure : ℕ → ι)
    (hpure : ∀ j, 1 ≤ j → j ≤ E → m (pure j) = p^j)
    (k : ι) (v : ℕ) (hvE : v ≤ E) (hd : p^v ∣ m k)
    (hmixed : ∀ j, 1 ≤ j → j ≤ v → m k ≠ p^j)
    (j : ℕ) (hj : 1 ≤ j) (hjv : j ≤ v) :
    Disjoint (cylinder p E v (a k)) (cylinder p E j (a (pure j))) := by
  have hjE := hjv.trans hvE
  have hne : pure j ≠ k := by
    intro he
    exact hmixed j hj hjv (by rw [← he,hpure j hj hjE])
  have hjd : m (pure j) ∣ m k := by
    rw [hpure j hj hjE]
    exact (pow_dvd_pow p hjv).trans hd
  have hs := residue_not_congruent_of_proper_modulus_divisor m a hpriv hc hne hjd
  rw [hpure j hj hjE] at hs
  exact (cylinder_disjoint p E j v _ _ hjv hs).symm

/-- Actual congruence-class projection bound. The selected modulus is present,
contains p^v, and is not one of the pure p-powers through v. All pure powers
through the ambient cap E are assumed present in the irredundant cover. -/
theorem arithmetic_conditional_projection {ι : Type*} (m : ι → ℕ) (a : ι → ℤ)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j:ℤ) ∣ x-a j)
    (hc : ∀ x : ℤ, ∃ i, (m i:ℤ) ∣ x-a i)
    (p E : ℕ) [NeZero p] (hp : 3 ≤ p) (pure : ℕ → ι)
    (hpure : ∀ j, 1 ≤ j → j ≤ E → m (pure j) = p^j)
    (k : ι) (v : ℕ) (hvE : v ≤ E) (hd : p^v ∣ m k)
    (hmixed : ∀ j, 1 ≤ j → j ≤ v → m k ≠ p^j) :
    let B := fun j => cylinder p E j (a (pure j))
    let U := Finset.univ \ pureUnion B E
    0 < mass (uniform p E) U ∧
      ((p:ℝ)⁻¹)^v ≤ mass (uniform p E) (cylinder p E v (a k) ∩ U) /
        mass (uniform p E) U := by
  dsimp only
  let B := fun j => cylinder p E j (a (pure j))
  have hB : ∀ j, 1 ≤ j → j ≤ E → mass (uniform p E) (B j) = ((p:ℝ)⁻¹)^j := by
    intro j _ hj
    exact cylinder_mass p E j _ hj
  have hdis := pure_family_disjoint m a hpriv hc p E (by omega) pure hpure
  have havoid : ∀ j, 1 ≤ j → j ≤ v → Disjoint (cylinder p E v (a k)) (B j) := by
    exact fun j hj hjv => mixed_cylinder_disjoint m a hpriv hc p E pure hpure
      k v hvE hd hmixed j hj hjv
  have hU : 0 < mass (uniform p E) (Finset.univ \ pureUnion B E) := by
    rw [pure_complement_mass _ (uniform_mass p E) B E _ hB hdis]
    have hg := geom_le_half ((p:ℝ)⁻¹) (by positivity) (inv_le_third p hp) E
    linarith
  exact ⟨hU,conditional_cylinder_lower_bound (uniform p E) (uniform_nonneg p E)
    (uniform_mass p E) B E v hvE ((p:ℝ)⁻¹) (by positivity) hB hdis
    (cylinder p E v (a k)) (cylinder_mass p E v (a k) hvE) havoid hU⟩

/-- Finite exponent caps give a strict lower bound for positive exponents.
No exponent-independent positive gap is claimed. -/
theorem arithmetic_conditional_projection_strict {ι : Type*} (m : ι → ℕ) (a : ι → ℤ)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j:ℤ) ∣ x-a j)
    (hc : ∀ x : ℤ, ∃ i, (m i:ℤ) ∣ x-a i)
    (p E : ℕ) [NeZero p] (hp : 3 ≤ p) (pure : ℕ → ι)
    (hpure : ∀ j, 1 ≤ j → j ≤ E → m (pure j) = p^j)
    (k : ι) (v : ℕ) (hv : 0 < v) (hvE : v ≤ E) (hd : p^v ∣ m k)
    (hmixed : ∀ j, 1 ≤ j → j ≤ v → m k ≠ p^j) :
    let B := fun j => cylinder p E j (a (pure j))
    let U := Finset.univ \ pureUnion B E
    ((p:ℝ)⁻¹)^v < mass (uniform p E) (cylinder p E v (a k) ∩ U) /
      mass (uniform p E) U := by
  dsimp only
  let B := fun j => cylinder p E j (a (pure j))
  have hB : ∀ j, 1 ≤ j → j ≤ E → mass (uniform p E) (B j) = ((p:ℝ)⁻¹)^j := by
    intro j _ hj
    exact cylinder_mass p E j _ hj
  have hdis := pure_family_disjoint m a hpriv hc p E (by omega) pure hpure
  have hU := (arithmetic_conditional_projection m a hpriv hc p E hp pure hpure
    k v hvE hd hmixed).1
  have hr : 0 < (p:ℝ)⁻¹ := by
    apply inv_pos.mpr
    exact_mod_cast (by omega : 0 < p)
  exact conditional_cylinder_strict_lower_bound (uniform p E) (uniform_nonneg p E)
    (uniform_mass p E) B E v hv hvE ((p:ℝ)⁻¹) hr hB hdis
    (cylinder p E v (a k)) (cylinder_mass p E v (a k) hvE)
    (fun j hj hjv => mixed_cylinder_disjoint m a hpriv hc p E pure hpure
      k v hvE hd hmixed j hj hjv) hU

#print axioms cylinder_mass
#print axioms pure_family_disjoint
#print axioms arithmetic_conditional_projection
#print axioms arithmetic_conditional_projection_strict
end Erdos7ArithmeticProjectionLower
