import Submission.GapRatioResidues

/-! An infinite class of gap ratios excluded by one positive-density progression.
This does not exclude all cubic collisions. -/
namespace Erdos1206.GapDifferenceSource

private lemma cofactor_mod_three_mul {a b m : ℕ} (hm : 1 < m) (hm3 : 3 ∣ m)
    (ha : Nat.ModEq m a 1) (hb : Nat.ModEq m b 1) :
    Nat.ModEq (3*m) (a^2+a*b+b^2) 3 := by
  have ha' : a=1+m*(a/m) := by
    have h := Nat.mod_add_div a m
    have hr : a%m=1 := by simpa only [Nat.ModEq,Nat.mod_eq_of_lt hm] using ha
    omega
  have hb' : b=1+m*(b/m) := by
    have h := Nat.mod_add_div b m
    have hr : b%m=1 := by simpa only [Nat.ModEq,Nat.mod_eq_of_lt hm] using hb
    omega
  let x := a/m
  let y := b/m
  obtain ⟨k,hk⟩ := hm3
  have he : a^2+a*b+b^2=3+(3*m)*(x+y+k*(x^2+x*y+y^2)) := by
    change a=1+m*x at ha'
    change b=1+m*y at hb'
    rw [ha',hb',hk]
    ring
  rw [he]
  simp [Nat.ModEq,Nat.add_mod]

/-- The reduced-gap congruence also holds when the modulus is divisible by
three. In that case lift the cofactor congruence to modulus `3*m` first. -/
theorem progression_gap_congruence {a c g u v m : ℕ} (hm : 1 < m) (hg : 0 < g)
    (ha : Nat.ModEq m a 1) (hb : Nat.ModEq m (a+g*u) 1)
    (hc : Nat.ModEq m c 1) (hd : Nat.ModEq m (c+g*v) 1)
    (he : (a+g*u)^3+c^3=a^3+(c+g*v)^3) : Nat.ModEq m u v := by
  by_cases hm3 : 3 ∣ m
  · have h := cube_collision_cancel_common_gap hg he
    have hQ₁ := cofactor_mod_three_mul hm hm3 hb ha
    have hQ₂ := cofactor_mod_three_mul hm hm3 hd hc
    have heq : Nat.ModEq (3*m)
        (u*((a+g*u)^2+(a+g*u)*a+a^2))
        (v*((c+g*v)^2+(c+g*v)*c+c^2)) := by rw [h]
    have h3 : Nat.ModEq (3*m) (u*3) (v*3) :=
      (hQ₁.mul_left u).symm.trans (heq.trans (hQ₂.mul_left v))
    apply Nat.ModEq.mul_right_cancel' (by norm_num : 3 ≠ 0)
    simpa only [Nat.mul_comm m 3] using h3
  · apply cube_collision_gap_ratio_modEq hg _ ha hb hc hd he
    exact Nat.coprime_comm.mpr (Nat.prime_three.coprime_iff_not_dvd.mpr hm3)

/-- Numerators need not be bounded: it is enough that their positive
difference is smaller than the modulus. -/
theorem no_small_gap_difference {a c g u v m : ℕ} (hm : 1 < m) (hg : 0 < g)
    (hvu : v < u) (hsmall : u-v < m)
    (ha : Nat.ModEq m a 1) (hb : Nat.ModEq m (a+g*u) 1)
    (hc : Nat.ModEq m c 1) (hd : Nat.ModEq m (c+g*v) 1) :
    (a+g*u)^3+c^3 ≠ a^3+(c+g*v)^3 := by
  intro he
  have h := progression_gap_congruence hm hg ha hb hc hd he
  have hdvd : m ∣ u-v := (Nat.modEq_iff_dvd' hvu.le).mp h.symm
  have hle := Nat.le_of_dvd (by omega : 0 < u-v) hdvd
  omega

/-- One progression of positive lower density excludes all gap ratios `u/v`
with `0 < u-v ≤ K`, including infinitely many ratios converging to one. -/
theorem positive_density_avoids_small_gap_difference (K : ℕ) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      ∀ a c g u v : ℕ, 0 < g → v < u → u-v ≤ K →
        a ∈ A → a+g*u ∈ A → c ∈ A → c+g*v ∈ A →
        (a+g*u)^3+c^3 ≠ a^3+(c+g*v)^3 := by
  let m := K+2
  let A : Set ℕ := {n | Nat.ModEq m n 1}
  have hm : 1 < m := by dsimp [m]; omega
  have hden : 0 < A.lowerDensity := one_residue_positive_lowerDensity hm
  refine ⟨A,?_,hden,?_⟩
  · by_contra hfin
    have hz := (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hfin)).liminf_eq
    change A.lowerDensity=0 at hz
    linarith
  · intro a c g u v hg hvu hsmall ha hb hc hd
    exact no_small_gap_difference hm hg hvu (by dsimp [m]; omega) ha hb hc hd

#print axioms progression_gap_congruence
#print axioms no_small_gap_difference
#print axioms positive_density_avoids_small_gap_difference
end Erdos1206.GapDifferenceSource
