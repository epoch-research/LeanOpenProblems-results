import FormalConjecturesUtil

/-!
A quadratic family of primitive cubic collisions with divergent reciprocal
height mass. This concerns counting collisions, not the existence conjecture.
-/

namespace Erdos1206
namespace PrimitiveCollisionMass
open Finset
open scoped Classical

def A (t u : ℕ) := 7*t^2 + 13*t*u + 3*u^2
def B (t u : ℕ) := 63*t^2 + 29*t*u + 3*u^2
def C (t u : ℕ) := 70*t^2 + 40*t*u + 6*u^2
def D (t u : ℕ) := 84*t^2 + 44*t*u + 6*u^2

lemma identity (t u : ℕ) : A t u ^ 3 + D t u ^ 3 = B t u ^ 3 + C t u ^ 3 := by
  dsimp [A,B,C,D]
  ring

/-- A single divisor already meets this entire family, despite divergence
of its per-collision reciprocal mass. -/
lemma two_dvd_C (t u : ℕ) : 2 ∣ C t u := by
  refine ⟨35*t^2 + 20*t*u + 3*u^2, ?_⟩
  dsimp [C]
  ring

lemma ordered {t : ℕ} (ht : 0 < t) (u : ℕ) :
    0 < A t u ∧ A t u < B t u ∧ B t u < C t u ∧ C t u < D t u := by
  have hsq : 0 < t^2 := pow_pos ht _
  dsimp [A,B,C,D]
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma parameter_injective {t u t' u' : ℕ}
    (ha : A t u = A t' u') (hb : B t u = B t' u')
    (hc : C t u = C t' u') (hd : D t u = D t' u') : t=t' ∧ u=u' := by
  have htu : t*u = t'*u' := by dsimp [A,B,C] at ha hb hc; nlinarith only [ha,hb,hc]
  have htt : t^2 = t'^2 := by dsimp [C,D] at hc hd; nlinarith only [hc,hd,htu]
  have huu : u^2 = u'^2 := by dsimp [A] at ha; nlinarith only [ha,htu,htt]
  exact ⟨Nat.pow_left_injective (by decide : 2 ≠ 0) htt,
    Nat.pow_left_injective (by decide : 2 ≠ 0) huu⟩

lemma gcd_one {p j : ℕ} (hp : p.Prime) (hp29 : 29 ≤ p) (hj : 6*j+1 < p) :
    Nat.gcd (Nat.gcd (A (6*j+1) p) (B (6*j+1) p))
      (Nat.gcd (C (6*j+1) p) (D (6*j+1) p)) = 1 := by
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro q hq hqg
  let t := 6*j+1
  have hqa : q ∣ A t p := hqg.trans ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
  have hqb : q ∣ B t p := hqg.trans ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
  have hqc : q ∣ C t p := hqg.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
  have hqd : q ∣ D t p := hqg.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
  have hi₁ : A t p + B t p = C t p + 2*t*p := by dsimp [A,B,C]; ring
  have hi₂ : D t p = C t p + 2*(2*t*p) + 14*t^2 := by dsimp [C,D]; ring
  have hi₃ : 2 * A t p = 14*t^2 + 13*(2*t*p) + 6*p^2 := by dsimp [A]; ring
  have hqu : q ∣ 2*t*p := by
    apply (Nat.dvd_add_iff_right hqc).mpr
    rw [← hi₁]
    exact dvd_add hqa hqb
  have hqt : q ∣ 14*t^2 := by
    apply (Nat.dvd_add_iff_right (dvd_add hqc (dvd_mul_of_dvd_right hqu 2))).mpr
    rw [← hi₂]
    exact hqd
  have hqp : q ∣ 6*p^2 := by
    apply (Nat.dvd_add_iff_right (dvd_add hqt (dvd_mul_of_dvd_right hqu 13))).mpr
    rw [← hi₃]
    exact dvd_mul_of_dvd_right hqa 2
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left (by omega)
  have hq2 : q ≠ 2 := by
    intro he
    subst q
    have hmod : A t p % 2 = 1 := by
      simp [A,t,Nat.add_mod,Nat.mul_mod,Nat.pow_mod,hpodd]
    have := Nat.mod_eq_zero_of_dvd hqa
    omega
  have hq3t : ¬ 3 ∣ t := by
    intro hh
    have := Nat.mod_eq_zero_of_dvd hh
    simp [t,Nat.add_mod,Nat.mul_mod] at this
  have hqp' : q ∣ t ∨ q ∣ p := by
    rcases hq.dvd_mul.mp hqu with h | h
    · rcases hq.dvd_mul.mp h with h | h
      · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
        exact (hq2 he).elim
      · exact Or.inl h
    · exact Or.inr h
  rcases hqp' with hqdt | hqdp
  · have hnotp : ¬ q ∣ p := by
      intro h
      have he : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp h
      subst q
      have := Nat.le_of_dvd (show 0 < t by dsimp [t]; omega) hqdt
      change t < p at hj
      omega
    have hq6 : q ∣ 6 := (hq.dvd_mul.mp hqp).resolve_right
      (fun hh => hnotp (hq.dvd_of_dvd_pow hh))
    have hq23 : q=2 ∨ q=3 := by
      have hh : q ∣ 2*3 := hq6
      rcases hq.dvd_mul.mp hh with hh | hh
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hh)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hh)
    rcases hq23 with h | h
    · exact hq2 h
    · exact hq3t (h ▸ hqdt)
  · have he : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqdp
    subst q
    have hnot : ¬ p ∣ t := by
      intro h
      have := Nat.le_of_dvd (show 0 < t by dsimp [t]; omega) h
      change t < p at hj
      omega
    have hd14 : p ∣ 14 := (hp.dvd_mul.mp hqt).resolve_right
      (fun hh => hnot (hp.dvd_of_dvd_pow hh))
    have := Nat.le_of_dvd (by decide : 0 < 14) hd14
    omega

abbrev LargePrime := {p : ℕ // p.Prime ∧ 29 ≤ p}
abbrev Index := (p : LargePrime) × Fin (p.val / 12)

lemma index_t_lt (x : Index) : 6*x.2.val+1 < x.1.val := by
  have h := x.2.isLt
  have := x.1.property.2
  omega

lemma index_gcd_one (x : Index) :
    Nat.gcd (Nat.gcd (A (6*x.2.val+1) x.1.val) (B (6*x.2.val+1) x.1.val))
      (Nat.gcd (C (6*x.2.val+1) x.1.val) (D (6*x.2.val+1) x.1.val)) = 1 :=
  gcd_one x.1.property.1 x.1.property.2 (index_t_lt x)

lemma height_bound (x : Index) : D (6*x.2.val+1) x.1.val ≤ 134*x.1.val^2 := by
  have ht := (index_t_lt x).le
  have hs := Nat.pow_le_pow_left ht 2
  have hm := Nat.mul_le_mul_right x.1.val ht
  dsimp [D]
  nlinarith

#print axioms index_gcd_one

lemma large_prime_reciprocals_not_summable :
    ¬ Summable (fun p : LargePrime => (1 : ℝ) / p.val) := by
  intro hs
  have hi : Summable (({p : ℕ | p.Prime ∧ 29 ≤ p} : Set ℕ).indicator
      (fun p : ℕ => (1 : ℝ) / p)) := summable_subtype_iff_indicator.mp hs
  apply not_summable_one_div_on_primes
  apply hi.congr_cofinite
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Filter.eventually_ge_atTop 29] with p hp
  by_cases hprime : p.Prime <;> simp [hprime,hp]

noncomputable def blockMass (p : LargePrime) : ℝ :=
  ∑ j : Fin (p.val / 12), (1 : ℝ) / D (6*j.val+1) p.val

lemma block_mass_lower (p : LargePrime) :
    1 / (3216 * (p.val : ℝ)) ≤ blockMass p := by
  have hp : (0 : ℝ) < p.val := by exact_mod_cast p.property.1.pos
  have hc : (p.val : ℝ) ≤ 24 * (p.val / 12 : ℕ) := by
    exact_mod_cast (show p.val ≤ 24 * (p.val / 12) by
      have := p.property.2
      omega)
  have hden : (0 : ℝ) < 134 * (p.val : ℝ)^2 := by positivity
  calc
    _ ≤ ((p.val / 12 : ℕ) : ℝ) / (134 * (p.val : ℝ)^2) := by
      apply (div_le_div_iff₀ (by positivity) hden).mpr
      nlinarith [mul_le_mul_of_nonneg_right hc
        (by positivity : (0 : ℝ) ≤ 134 * (p.val : ℝ))]
    _ = ∑ _j : Fin (p.val / 12), (1 : ℝ) / (134 * (p.val : ℝ)^2) := by
      simp [div_eq_mul_inv]
    _ ≤ blockMass p := by
      apply Finset.sum_le_sum
      intro j hj
      have hb : (D (6*j.val+1) p.val : ℝ) ≤ 134 * (p.val : ℝ)^2 := by
        exact_mod_cast height_bound (⟨p,j⟩ : Index)
      have hD : (0 : ℝ) < D (6*j.val+1) p.val := by
        dsimp [D]
        positivity
      exact one_div_le_one_div_of_le hD hb

/-- Even this single fixed-gap-ratio family has divergent reciprocal height
mass after restricting to distinct primitive collisions. -/
lemma index_reciprocal_heights_not_summable :
    ¬ Summable (fun x : Index => (1 : ℝ) / D (6*x.2.val+1) x.1.val) := by
  intro hs
  have hblocks := ((summable_sigma_of_nonneg
    (fun x : Index => (by positivity : 0 ≤ (1 : ℝ) / D (6*x.2.val+1) x.1.val))).mp hs).2
  have hB : Summable blockMass := by
    simpa only [blockMass, tsum_fintype] using hblocks
  have hsmall : Summable (fun p : LargePrime => (1 : ℝ) / (3216 * (p.val : ℝ))) :=
    hB.of_nonneg_of_le (fun _ => by positivity) block_mass_lower
  apply large_prime_reciprocals_not_summable
  convert hsmall.mul_left 3216 using 1
  funext p
  have hp : (p.val : ℝ) ≠ 0 := by exact_mod_cast p.property.1.ne_zero
  field_simp

/-- Ordered, positive, primitive integer cubic collisions, each counted once. -/
abbrev Collision := {e : ℕ × ℕ × ℕ × ℕ //
  0 < e.1 ∧ e.1 < e.2.1 ∧ e.2.1 < e.2.2.1 ∧ e.2.2.1 < e.2.2.2 ∧
  e.1^3 + e.2.2.2^3 = e.2.1^3 + e.2.2.1^3 ∧
  Nat.gcd (Nat.gcd e.1 e.2.1) (Nat.gcd e.2.2.1 e.2.2.2) = 1}

def collision (x : Index) : Collision :=
  ⟨(A (6*x.2.val+1) x.1.val, B (6*x.2.val+1) x.1.val,
    C (6*x.2.val+1) x.1.val, D (6*x.2.val+1) x.1.val),
    (ordered (by omega : 0 < 6*x.2.val+1) x.1.val).1,
    (ordered (by omega : 0 < 6*x.2.val+1) x.1.val).2.1,
    (ordered (by omega : 0 < 6*x.2.val+1) x.1.val).2.2.1,
    (ordered (by omega : 0 < 6*x.2.val+1) x.1.val).2.2.2,
    identity _ _, index_gcd_one x⟩

lemma collision_injective : Function.Injective collision := by
  rintro ⟨p,j⟩ ⟨p',j'⟩ he
  have ha := congrArg (fun e : Collision => e.val.1) he
  have hb := congrArg (fun e : Collision => e.val.2.1) he
  have hc := congrArg (fun e : Collision => e.val.2.2.1) he
  have hd := congrArg (fun e : Collision => e.val.2.2.2) he
  obtain ⟨ht,hu⟩ := parameter_injective ha hb hc hd
  change 6*j.val+1 = 6*j'.val+1 at ht
  change p.val = p'.val at hu
  have hpp : p=p' := Subtype.ext hu
  subst p'
  have hjj : j=j' := Fin.ext (by omega)
  subst j'
  rfl

set_option maxHeartbeats 1000000 in
theorem primitive_reciprocal_heights_not_summable :
    ¬ Summable (fun e : Collision => (1 : ℝ) / e.val.2.2.2) := by
  intro hs
  apply index_reciprocal_heights_not_summable
  have hh := hs.comp_injective collision_injective
  exact hh.congr (fun _ => rfl)

#print axioms primitive_reciprocal_heights_not_summable


end PrimitiveCollisionMass
end Erdos1206
