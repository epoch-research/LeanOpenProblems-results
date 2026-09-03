import Submission.CubicParametrization

/-! Completeness with a possibly repeated middle root. This avoids needing
an independent theorem about arithmetic progressions of rational cubes.
No density assertion is made here. -/

namespace Erdos1206

private lemma weak_ordered_cube_collision_gap_lt {a b c d : ℚ}
    (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (he : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) : d - c < b - a := by
  have hb : 0 < b := ha.trans_lt hab
  have hc : 0 < c := hb.trans_le hbc
  have hd : 0 < d := hc.trans hcd
  have hQ₁ : 0 ≤ b ^ 2 + b * a + a ^ 2 := by positivity
  have hQ₂ : b ^ 2 + b * a + a ^ 2 < d ^ 2 + d * c + c ^ 2 := by
    have h₁ : b ^ 2 < d ^ 2 := (sq_lt_sq₀ hb.le hd.le).mpr (hbc.trans_lt hcd)
    have h₂ : a ^ 2 < c ^ 2 := (sq_lt_sq₀ ha hc.le).mpr (hab.trans_le hbc)
    have h₃ : b * a ≤ d * c := mul_le_mul (hbc.trans_lt hcd).le
      (hab.trans_le hbc).le ha hd.le
    linarith
  have hprod : (d - c) * (d ^ 2 + d * c + c ^ 2) =
      (b - a) * (b ^ 2 + b * a + a ^ 2) := by
    nlinarith only [he]
  by_contra hn
  have hle : b - a ≤ d - c := le_of_not_gt hn
  have hlt := mul_lt_mul_of_pos_left hQ₂ (sub_pos.mpr hab)
  have hle' := mul_le_mul_of_nonneg_right hle (hQ₁.trans hQ₂.le)
  linarith

/-- The nontrivial ordered positive part of the Fermat cubic surface is
parametrized by a rational quadratic norm relation and a positive scale. -/
theorem weak_ordered_cube_collision_normal_form {a b c d : ℚ}
    (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (he : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    ∃ q u v t : ℚ,
      0 < q ∧ q < 1 ∧ 0 < t ∧ u < v ∧
      u ^ 2 + u * v + v ^ 2 = 3 * q ∧
      a = t * (q ^ 2 + u) ∧ b = t * (q ^ 2 + v) ∧
      c = t * (q * u + 1) ∧ d = t * (q * v + 1) := by
  let q := (d - c) / (b - a)
  have hba : 0 < b - a := sub_pos.mpr hab
  have hq : 0 < q := div_pos (sub_pos.mpr hcd) hba
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one hba).mpr (weak_ordered_cube_collision_gap_lt ha hab hbc hcd he)
  have hq3 : q ^ 3 < 1 := by nlinarith [sq_nonneg (q - 1)]
  have hden : q ^ 3 - 1 ≠ 0 := by linarith
  have hgap : q * (b - a) = d - c := by
    dsimp [q]
    exact div_mul_cancel₀ _ hba.ne'
  have hnum : q * a - c < 0 := by
    have hqa := mul_le_mul_of_nonneg_right hq1.le ha
    linarith
  let t := (q * a - c) / (q ^ 3 - 1)
  have ht : 0 < t := div_pos_of_neg_of_neg hnum (by linarith)
  have htn : t ≠ 0 := ht.ne'
  have hscale : t * (q ^ 3 - 1) = q * a - c := by
    dsimp [t]
    exact div_mul_cancel₀ _ hden
  let u := a / t - q ^ 2
  let v := b / t - q ^ 2
  have ha' : a = t * (q ^ 2 + u) := by
    dsimp [u]
    field_simp
    ring
  have hb' : b = t * (q ^ 2 + v) := by
    dsimp [v]
    field_simp
    ring
  have hc' : c = t * (q * u + 1) := by
    nlinarith only [hscale, congrArg (fun x : ℚ => q * x) ha']
  have hd' : d = t * (q * v + 1) := by
    nlinarith only [hgap, hc', congrArg (fun x : ℚ => q * x) ha',
      congrArg (fun x : ℚ => q * x) hb']
  have huv : u < v := by
    have hlt : t * (q ^ 2 + u) < t * (q ^ 2 + v) := by
      rw [← ha', ← hb']; exact hab
    have hh := (mul_lt_mul_iff_right₀ ht).mp hlt
    linarith
  have he' : (q ^ 2 + u) ^ 3 + (q * v + 1) ^ 3 =
      (q ^ 2 + v) ^ 3 + (q * u + 1) ^ 3 := by
    rw [ha', hb', hc', hd'] at he
    simp only [mul_pow] at he
    have hh : t ^ 3 * ((q ^ 2 + u) ^ 3 + (q * v + 1) ^ 3) =
        t ^ 3 * ((q ^ 2 + v) ^ 3 + (q * u + 1) ^ 3) := by
      simpa only [mul_add] using he
    exact mul_left_cancel₀ (pow_ne_zero _ htn) hh
  have hz : (u - v) * (q ^ 3 - 1) * (3 * q - (u ^ 2 + u * v + v ^ 2)) = 0 := by
    rw [← cube_normal_form_identity]
    linarith
  have hnorm : u ^ 2 + u * v + v ^ 2 = 3 * q := by
    have hzero := (mul_eq_zero.mp hz).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr huv.ne) hden)
    linarith
  exact ⟨q, u, v, t, hq, hq1, ht, huv, hnorm, ha', hb', hc', hd'⟩


/-- Every nontrivial ordered nonnegative rational collision is a positive
rational dilate of this fixed quartic parametrization. -/
theorem weak_ordered_cube_collision_quartic_parametrization {a b c d : ℚ}
    (ha : 0 ≤ a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    (he : a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3) :
    ∃ r s t : ℚ, 0 < s ∧ 0 < t ∧
      0 < cubeParamNorm r s ∧ cubeParamNorm r s < 1 ∧
      a = t * cubeParamA r s ∧ b = t * cubeParamB r s ∧
      c = t * cubeParamC r s ∧ d = t * cubeParamD r s := by
  obtain ⟨q, u, v, t, hq, hq1, ht, huv, hnorm, ha', hb', hc', hd'⟩ :=
    weak_ordered_cube_collision_normal_form ha hab hbc hcd he
  let r := (u + 2 * v) / 3
  let s := (v - u) / 3
  have hs : 0 < s := div_pos (sub_pos.mpr huv) (by norm_num)
  have hN : cubeParamNorm r s = q := by
    dsimp [cubeParamNorm, r, s]
    nlinarith only [hnorm]
  have hu : r - 2 * s = u := by dsimp [r, s]; ring
  have hv : r + s = v := by dsimp [r, s]; ring
  refine ⟨r, s, t, hs, ht, hN ▸ hq, hN ▸ hq1, ?_, ?_, ?_, ?_⟩
  · simpa only [cubeParamA, hN, add_sub_assoc, hu] using ha'
  · simpa only [cubeParamB, hN, add_assoc, hv] using hb'
  · simpa only [cubeParamC, hN, hu] using hc'
  · simpa only [cubeParamD, hN, hv] using hd'


namespace CubicParametrization

/-- Every ordered positive rational cubic collision is a positive rational
dilate of these fixed cubic forms (in the affine chart t=1). -/
theorem complete_weak_order {x y z w : ℚ}
    (hx : 0 ≤ x) (hxy : x < y) (hyz : y ≤ z) (hzw : z < w)
    (he : x^3+w^3=y^3+z^3) :
    ∃ a b k : ℚ, 0 < b ∧ 0 < k ∧
      x = k*A a b 1 ∧ y = k*B a b 1 ∧
      z = k*C a b 1 ∧ w = k*D a b 1 := by
  obtain ⟨r,s,t,hs,ht,hN0,hN1,hx',hy',hz',hw'⟩ :=
    weak_ordered_cube_collision_quartic_parametrization hx hxy hyz hzw he
  have hden := cayleyDen_pos (r := r) hs
  obtain ⟨ha,hb,hc,hd⟩ := cayley_identities hden.ne'
  refine ⟨cayleyA r s,cayleyB r s,t*(cayleyDen r s)^2/8,?_,by positivity,?_,?_,?_,?_⟩
  · dsimp [cayleyB]
    positivity
  · rw [hx']
    nlinarith only [congrArg (fun q : ℚ => t*q) ha]
  · rw [hy']
    nlinarith only [congrArg (fun q : ℚ => t*q) hb]
  · rw [hz']
    nlinarith only [congrArg (fun q : ℚ => t*q) hc]
  · rw [hw']
    nlinarith only [congrArg (fun q : ℚ => t*q) hd]


#print axioms complete_weak_order

end CubicParametrization

/-- The exact ordered obstruction to Sidon cubes, including the case `y = z`. -/
def NoWeakOrderedCubeCollision (S : Set ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ w ∈ S,
    x < y → y ≤ z → z < w → x^3+w^3 ≠ y^3+z^3

private lemma sorted_cube_pairs_eq {S : Set ℕ}
    (h : NoWeakOrderedCubeCollision S) {a b c d : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≤ b) (hcd : c ≤ d) (he : a^3+b^3=c^3+d^3) :
    a = c ∧ b = d := by
  rcases lt_trichotomy a c with hac | hac | hca
  · have hdb : d < b := by
      by_contra! hbd
      have h₁ := Nat.pow_lt_pow_left hac (by decide : 3 ≠ 0)
      have h₂ := Nat.pow_le_pow_left hbd 3
      omega
    exact (h a ha c hc d hd b hb hac hcd hdb he).elim
  · subst c
    have he' : b^3=d^3 := Nat.add_left_cancel he
    exact ⟨rfl, Nat.pow_left_injective (by decide : 3 ≠ 0) he'⟩
  · have hbd : b < d := by
      by_contra! hdb
      have h₁ := Nat.pow_lt_pow_left hca (by decide : 3 ≠ 0)
      have h₂ := Nat.pow_le_pow_left hdb 3
      omega
    exact (h c hc a ha b hb d hd hca hab hbd he.symm).elim

theorem cubeSidon_iff_no_weak_ordered (S : Set ℕ) :
    IsSidon ((fun n : ℕ => n^3) '' S) ↔ NoWeakOrderedCubeCollision S := by
  constructor
  · intro h x hx y hy z hz w hw hxy hyz hzw he
    have h₁ := Nat.pow_lt_pow_left hxy (by decide : 3 ≠ 0)
    have h₂ := Nat.pow_le_pow_left hyz 3
    rcases h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ _ ⟨w,hw,rfl⟩ _ ⟨z,hz,rfl⟩ he
      with h | h <;> dsimp only at h <;> omega
  · intro h
    rintro _ ⟨a,ha,rfl⟩ _ ⟨c,hc,rfl⟩ _ ⟨b,hb,rfl⟩ _ ⟨d,hd,rfl⟩ he
    change a^3+b^3=c^3+d^3 at he
    rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
    · obtain ⟨rfl,rfl⟩ := sorted_cube_pairs_eq h ha hb hc hd hab hcd he
      exact Or.inl ⟨rfl,rfl⟩
    · have he' : a^3+b^3=d^3+c^3 := by omega
      obtain ⟨rfl,rfl⟩ := sorted_cube_pairs_eq h ha hb hd hc hab hdc he'
      exact Or.inr ⟨rfl,rfl⟩
    · have he' : b^3+a^3=c^3+d^3 := by omega
      obtain ⟨rfl,rfl⟩ := sorted_cube_pairs_eq h hb ha hc hd hba hcd he'
      exact Or.inr ⟨rfl,rfl⟩
    · have he' : b^3+a^3=d^3+c^3 := by omega
      obtain ⟨rfl,rfl⟩ := sorted_cube_pairs_eq h hb ha hd hc hba hdc he'
      exact Or.inl ⟨rfl,rfl⟩

/-- A failure of the Sidon condition has a witness in the cubic parametrization;
its two middle roots need not be assumed distinct. -/
theorem not_cubeSidon_iff_parametrized_collision (S : Set ℕ) :
    ¬ IsSidon ((fun n : ℕ => n^3) '' S) ↔
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, ∃ w ∈ S,
      x < y ∧ y ≤ z ∧ z < w ∧ ∃ a b k : ℚ, 0 < b ∧ 0 < k ∧
        (x : ℚ) = k*CubicParametrization.A a b 1 ∧
        (y : ℚ) = k*CubicParametrization.B a b 1 ∧
        (z : ℚ) = k*CubicParametrization.C a b 1 ∧
        (w : ℚ) = k*CubicParametrization.D a b 1 := by
  rw [cubeSidon_iff_no_weak_ordered]
  constructor
  · intro h
    simp only [NoWeakOrderedCubeCollision, not_forall, not_not, exists_prop] at h
    obtain ⟨x,hx,y,hy,z,hz,w,hw,hxy,hyz,hzw,he⟩ := h
    refine ⟨x,hx,y,hy,z,hz,w,hw,hxy,hyz,hzw,?_⟩
    apply CubicParametrization.complete_weak_order
    · positivity
    · exact_mod_cast hxy
    · exact_mod_cast hyz
    · exact_mod_cast hzw
    · exact_mod_cast he
  · rintro ⟨x,hx,y,hy,z,hz,w,hw,hxy,hyz,hzw,a,b,k,hb,hk,hx',hy',hz',hw'⟩ h
    have heQ : (x : ℚ)^3+(w : ℚ)^3=(y : ℚ)^3+(z : ℚ)^3 := by
      rw [hx',hy',hz',hw']
      simp only [mul_pow, ← mul_add, CubicParametrization.identity]
    exact h x hx y hy z hz w hw hxy hyz hzw (by exact_mod_cast heQ)

#print axioms cubeSidon_iff_no_weak_ordered
#print axioms not_cubeSidon_iff_parametrized_collision

end Erdos1206
