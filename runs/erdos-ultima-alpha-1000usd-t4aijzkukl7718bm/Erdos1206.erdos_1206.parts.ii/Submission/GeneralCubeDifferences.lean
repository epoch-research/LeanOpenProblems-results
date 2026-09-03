import FormalConjecturesUtil

/-! General repeated cubic differences. No density conclusion is asserted. -/

namespace Erdos1206.GeneralCubeDifferences

structure Seed where
  a : ℤ
  b : ℤ
  c : ℤ
  D : ℤ
  D_pos : 0 < D
  c_ne_zero : c ≠ 0
  identity : a^3-b^3=D*c^3
  mod_four : (a%4=1 ∧ b%4=1) ∨ (a%4=3 ∧ b%4=3)

variable (s : Seed)

/-- Homogeneous tangent construction. -/
def tangent (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (v.1 * (v.1^3 - 2*v.2.1^3),
   -v.2.1 * (2*v.1^3-v.2.1^3),
   v.2.2 * (v.1^3+v.2.1^3))

def orbit : ℕ → ℤ × ℤ × ℤ
  | 0 => (s.a,s.b,s.c)
  | n+1 => tangent (orbit n)

abbrev numA (n : ℕ) : ℤ := ((orbit s) n).1
abbrev numB (n : ℕ) : ℤ := ((orbit s) n).2.1
abbrev denom (n : ℕ) : ℤ := ((orbit s) n).2.2

lemma tangent_identity (a b : ℤ) :
    (a*(a^3-2*b^3))^3 - (-b*(2*a^3-b^3))^3 =
      (a^3-b^3)*(a^3+b^3)^3 := by ring

lemma orbit_identity (n : ℕ) : (numA s) n ^ 3 - (numB s) n ^ 3 = s.D * (denom s) n ^ 3 := by
  induction n with
  | zero => exact s.identity
  | succ n ih =>
    change ((numA s) n * ((numA s) n ^ 3 - 2 * (numB s) n ^ 3)) ^ 3 -
      (-(numB s) n * (2 * (numA s) n ^ 3 - (numB s) n ^ 3)) ^ 3 =
      s.D * ((denom s) n * ((numA s) n ^ 3 + (numB s) n ^ 3)) ^ 3
    rw [tangent_identity, ih]
    ring

lemma orbit_mod_four (n : ℕ) :
    ((numA s) n % 4 = 1 ∧ (numB s) n % 4 = 1) ∨
      ((numA s) n % 4 = 3 ∧ (numB s) n % 4 = 3) := by
  induction n with
  | zero => exact s.mod_four
  | succ n ih =>
    right
    change ((numA s) n * ((numA s) n ^ 3 - 2 * (numB s) n ^ 3)) % 4 = 3 ∧
      (-(numB s) n * (2 * (numA s) n ^ 3 - (numB s) n ^ 3)) % 4 = 3
    rcases ih with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · have ha' : (numA s) n ≡ 1 [ZMOD 4] := ha
      have hb' : (numB s) n ≡ 1 [ZMOD 4] := hb
      have hA := ha'.mul ((ha'.pow 3).sub ((Int.ModEq.refl 2).mul (hb'.pow 3)))
      have hB := hb'.neg.mul (((Int.ModEq.refl 2).mul (ha'.pow 3)).sub (hb'.pow 3))
      exact ⟨by simpa [Int.ModEq] using hA, by simpa [Int.ModEq] using hB⟩
    · have ha' : (numA s) n ≡ 3 [ZMOD 4] := ha
      have hb' : (numB s) n ≡ 3 [ZMOD 4] := hb
      have hA := ha'.mul ((ha'.pow 3).sub ((Int.ModEq.refl 2).mul (hb'.pow 3)))
      have hB := hb'.neg.mul (((Int.ModEq.refl 2).mul (ha'.pow 3)).sub (hb'.pow 3))
      exact ⟨by simpa [Int.ModEq] using hA, by simpa [Int.ModEq] using hB⟩

lemma nums_odd (n : ℕ) : (numA s) n % 2 = 1 ∧ (numB s) n % 2 = 1 := by
  rcases (orbit_mod_four s) n with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> omega

lemma tangent_den_mod_four (n : ℕ) :
    ((numA s) n ^ 3 + (numB s) n ^ 3) % 4 = 2 := by
  rcases (orbit_mod_four s) n with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    norm_num [Int.add_emod, pow_succ, Int.mul_emod, ha, hb]

lemma denom_ne_zero (n : ℕ) : (denom s) n ≠ 0 := by
  induction n with
  | zero => exact s.c_ne_zero
  | succ n ih =>
    change (denom s) n * ((numA s) n ^ 3 + (numB s) n ^ 3) ≠ 0
    apply mul_ne_zero ih
    have := (tangent_den_mod_four s) n
    intro h
    rw [h] at this
    norm_num at this

lemma denom_dvd_succ (n : ℕ) : (denom s) n ∣ (denom s) (n+1) := by
  change (denom s) n ∣ (denom s) n * _
  exact dvd_mul_right _ _

lemma twice_denom_dvd_succ (n : ℕ) : 2 * (denom s) n ∣ (denom s) (n+1) := by
  have he : 2 ∣ (numA s) n ^ 3 + (numB s) n ^ 3 := by
    apply Int.dvd_of_emod_eq_zero
    have := (tangent_den_mod_four s) n
    omega
  obtain ⟨k,hk⟩ := he
  refine ⟨k, ?_⟩
  change (denom s) n * ((numA s) n ^ 3 + (numB s) n ^ 3) = 2 * (denom s) n * k
  rw [hk]
  ring

lemma denom_dvd_of_le {i j : ℕ} (hij : i ≤ j) : (denom s) i ∣ (denom s) j := by
  induction j, hij using Nat.le_induction with
  | base => exact dvd_refl _
  | succ j hij ih => exact ih.trans ((denom_dvd_succ s) j)

lemma twice_denom_dvd_of_lt {i j : ℕ} (hij : i < j) : 2 * (denom s) i ∣ (denom s) j :=
  ((twice_denom_dvd_succ s) i).trans ((denom_dvd_of_le s) hij)

def rootA (n : ℕ) : ℚ := ((numA s) n : ℚ) / (denom s) n

def rootB (n : ℕ) : ℚ := ((numB s) n : ℚ) / (denom s) n

lemma rational_identity (n : ℕ) : (rootA s) n ^ 3 - (rootB s) n ^ 3 = s.D := by
  have hc : ((denom s) n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ((denom_ne_zero s) n)
  have hi : ((numA s) n : ℚ) ^ 3 - ((numB s) n : ℚ) ^ 3 = s.D * ((denom s) n : ℚ) ^ 3 := by
    exact_mod_cast (orbit_identity s) n
  dsimp only [rootA, rootB]
  field_simp
  simpa [mul_comm] using hi

lemma odd_fraction_ne {a b c d k : ℤ} (hc : c ≠ 0) (hd : d ≠ 0)
    (hb : b % 2 = 1) (hdk : d = 2*c*k) :
    (a : ℚ) / c ≠ (b : ℚ) / d := by
  intro he
  have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hdQ : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have he' : a*d=b*c := by
    exact_mod_cast (div_eq_div_iff hcQ hdQ).mp he
  rw [hdk] at he'
  have he'' : c*(2*a*k)=c*b := by nlinarith only [he']
  have heq : 2*a*k=b := mul_left_cancel₀ hc he''
  have hdvd : 2 ∣ b := by rw [← heq]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hz := Int.emod_eq_zero_of_dvd hdvd
  omega

lemma rootA_injective : Function.Injective (rootA s) := by
  intro i j he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨k,hk⟩ := (twice_denom_dvd_of_lt s) h
    exact odd_fraction_ne ((denom_ne_zero s) i) ((denom_ne_zero s) j) ((nums_odd s) j).1 hk he
  · obtain ⟨k,hk⟩ := (twice_denom_dvd_of_lt s) h
    exact odd_fraction_ne ((denom_ne_zero s) j) ((denom_ne_zero s) i) ((nums_odd s) i).1 hk he.symm

lemma rootB_injective : Function.Injective (rootB s) := by
  intro i j he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨k,hk⟩ := (twice_denom_dvd_of_lt s) h
    exact odd_fraction_ne ((denom_ne_zero s) i) ((denom_ne_zero s) j) ((nums_odd s) j).2 hk he
  · obtain ⟨k,hk⟩ := (twice_denom_dvd_of_lt s) h
    exact odd_fraction_ne ((denom_ne_zero s) j) ((denom_ne_zero s) i) ((nums_odd s) i).2 hk he.symm

lemma rootA_ne_zero (n : ℕ) : (rootA s) n ≠ 0 := by
  apply div_ne_zero
  · apply Int.cast_ne_zero.mpr
    have := ((nums_odd s) n).1
    intro h
    rw [h] at this
    norm_num at this
  · exact Int.cast_ne_zero.mpr ((denom_ne_zero s) n)

lemma rootB_ne_zero (n : ℕ) : (rootB s) n ≠ 0 := by
  apply div_ne_zero
  · apply Int.cast_ne_zero.mpr
    have := ((nums_odd s) n).2
    intro h
    rw [h] at this
    norm_num at this
  · exact Int.cast_ne_zero.mpr ((denom_ne_zero s) n)

lemma rootB_lt_rootA (n : ℕ) : (rootB s) n < (rootA s) n := by
  apply (Odd.pow_lt_pow (by decide : Odd 3)).mp
  have hD : (0 : ℚ) < s.D := by exact_mod_cast s.D_pos
  linarith [(rational_identity s) n]

lemma root_cube_sum_ne_zero (n : ℕ) : (rootA s) n ^ 3 + (rootB s) n ^ 3 ≠ 0 := by
  have hs : (numA s) n ^ 3 + (numB s) n ^ 3 ≠ 0 := by
    have := (tangent_den_mod_four s) n
    intro h
    rw [h] at this
    norm_num at this
  have hc : ((denom s) n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ((denom_ne_zero s) n)
  have hsQ : ((numA s) n : ℚ)^3 + ((numB s) n : ℚ)^3 ≠ 0 := by exact_mod_cast hs
  dsimp only [rootA, rootB]
  rw [div_pow, div_pow, ← add_div]
  exact div_ne_zero hsQ (pow_ne_zero _ hc)

lemma rootA_succ (n : ℕ) : (rootA s) (n+1) =
    (rootA s) n * ((rootA s) n^3-2*(rootB s) n^3) / ((rootA s) n^3+(rootB s) n^3) := by
  have hc : ((denom s) n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ((denom_ne_zero s) n)
  have hs : ((numA s) n : ℚ)^3+((numB s) n : ℚ)^3 ≠ 0 := by
    have h := (root_cube_sum_ne_zero s) n
    dsimp only [rootA, rootB] at h
    rw [div_pow, div_pow, ← add_div] at h
    exact (div_ne_zero_iff.mp h).1
  change (((numA s) n * ((numA s) n^3-2*(numB s) n^3) : ℤ) : ℚ) /
    ↑((denom s) n * ((numA s) n^3+(numB s) n^3)) = _
  dsimp only [rootA, rootB]
  push_cast
  field_simp

lemma rootB_succ (n : ℕ) : (rootB s) (n+1) =
    -(rootB s) n * (2*(rootA s) n^3-(rootB s) n^3) / ((rootA s) n^3+(rootB s) n^3) := by
  have hc : ((denom s) n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ((denom_ne_zero s) n)
  have hs : ((numA s) n : ℚ)^3+((numB s) n : ℚ)^3 ≠ 0 := by
    have h := (root_cube_sum_ne_zero s) n
    dsimp only [rootA, rootB] at h
    rw [div_pow, div_pow, ← add_div] at h
    exact (div_ne_zero_iff.mp h).1
  change ((-(numB s) n * (2*(numA s) n^3-(numB s) n^3) : ℤ) : ℚ) /
    ↑((denom s) n * ((numA s) n^3+(numB s) n^3)) = _
  dsimp only [rootA, rootB]
  push_cast
  field_simp

lemma same_sign_or_succ (n : ℕ) :
    0 < (rootA s) n * (rootB s) n ∨ 0 < (rootA s) (n+1) * (rootB s) (n+1) := by
  by_cases h : 0 < (rootA s) n * (rootB s) n
  · exact Or.inl h
  right
  have hlt := (rootB_lt_rootA s) n
  have hprod : (rootA s) n * (rootB s) n < 0 :=
    lt_of_le_of_ne (le_of_not_gt h) (mul_ne_zero ((rootA_ne_zero s) n) ((rootB_ne_zero s) n))
  have ha : 0 < (rootA s) n := by
    rcases mul_neg_iff.mp hprod with h | h
    · exact h.1
    · linarith [h.1, h.2]
  have hb : (rootB s) n < 0 := (mul_neg_iff.mp hprod).resolve_right (by rintro ⟨h,_⟩; linarith)
    |>.2
  have ha3 : 0 < (rootA s) n^3 := pow_pos ha 3
  have hb3 : (rootB s) n^3 < 0 := (Odd.pow_neg_iff (by decide : Odd 3)).mpr hb
  rw [(rootA_succ s), (rootB_succ s), div_mul_div_comm]
  apply div_pos
  · exact mul_pos (mul_pos ha (by linarith)) (mul_pos (neg_pos.mpr hb) (by linarith))
  · exact mul_self_pos.mpr ((root_cube_sum_ne_zero s) n)

/-- The two-adic seed gives infinitely many positive rational representations. -/
theorem infinite_positive_cube_difference :
    {b : ℚ | 0 < b ∧ ∃ a : ℚ, 0 < a ∧ a^3-b^3=(s.D : ℚ)}.Infinite := by
  let P : Set ℕ := {n | 0 < (rootB s) n}
  let Q : Set ℕ := {n | (rootA s) n < 0}
  have hun : (P ∪ Q).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro N
    have hmem (n : ℕ) (h : 0 < (rootA s) n * (rootB s) n) : n ∈ P ∪ Q := by
      rcases mul_pos_iff.mp h with h | h
      · exact Or.inl h.2
      · exact Or.inr h.1
    rcases (same_sign_or_succ s) (N+1) with h | h
    · exact ⟨N+1, hmem _ h, by omega⟩
    · exact ⟨N+2, hmem _ h, by omega⟩
  rcases Set.infinite_union.mp hun with hp | hq
  · have him : ((rootB s) '' P).Infinite := hp.image (rootB_injective s).injOn
    apply him.mono
    rintro b ⟨n, hn, rfl⟩
    exact ⟨hn, (rootA s) n, lt_trans hn ((rootB_lt_rootA s) n), (rational_identity s) n⟩
  · have hinj : Function.Injective (fun n => -(rootA s) n) :=
      neg_injective.comp (rootA_injective s)
    have him : ((fun n => -(rootA s) n) '' Q).Infinite := hq.image hinj.injOn
    apply him.mono
    rintro b ⟨n, hn, rfl⟩
    refine ⟨neg_pos.mpr hn, -(rootB s) n, neg_pos.mpr (lt_trans ((rootB_lt_rootA s) n) hn), ?_⟩
    have := (rational_identity s) n
    nlinarith



/-- Numerators and denominator of the chord construction for a triple. -/
def tripleA (a b : ℤ) : ℤ := a^9+3*a^6*b^3-6*a^3*b^6+b^9
def tripleB (a b : ℤ) : ℤ := a^9-6*a^6*b^3+3*a^3*b^6+b^9
def tripleC (a b : ℤ) : ℤ := 3*a*b*(a^6-a^3*b^3+b^6)

lemma triple_identity (a b : ℤ) :
    (tripleA a b)^3-(tripleB a b)^3=(a^3-b^3)*(tripleC a b)^3 := by
  simp only [tripleA,tripleB,tripleC]
  ring

lemma tangent_mod_four {a b : ℤ} (ha : a%2=1) (hb : b%2=1) :
    (a*(a^3-2*b^3))%4=3 ∧ (-b*(2*a^3-b^3))%4=3 := by
  have ha4 : a%4=1 ∨ a%4=3 := by omega
  have hb4 : b%4=1 ∨ b%4=3 := by omega
  have hneg : -b*(2*a^3-b^3)=b^4-2*a^3*b := by ring
  rw [hneg]
  rcases ha4 with ha4 | ha4 <;> rcases hb4 with hb4 | hb4 <;>
    norm_num [Int.add_emod,Int.sub_emod,pow_succ,Int.mul_emod,ha4,hb4]

lemma triple_mod_four {a b : ℤ}
    (h : (a%2=0 ∧ b%2=1) ∨ (a%2=1 ∧ b%2=0)) :
    (tripleA a b%4=1 ∧ tripleB a b%4=1) ∨
      (tripleA a b%4=3 ∧ tripleB a b%4=3) := by
  have ha4 : a%4=0 ∨ a%4=1 ∨ a%4=2 ∨ a%4=3 := by omega
  have hb4 : b%4=0 ∨ b%4=1 ∨ b%4=2 ∨ b%4=3 := by omega
  rcases ha4 with ha4 | ha4 | ha4 | ha4 <;>
    rcases hb4 with hb4 | hb4 | hb4 | hb4 <;>
    first | omega | norm_num [tripleA,tripleB,Int.add_emod,Int.sub_emod,
      pow_succ,Int.mul_emod,ha4,hb4]

lemma seed_exists {a b : ℤ} (hb : 0<b) (hab : b<a)
    (hpar : a%2=1 ∨ b%2=1) : ∃ s : Seed, s.D=a^3-b^3 := by
  have ha : 0<a := hb.trans hab
  have hD : 0<a^3-b^3 := sub_pos.mpr
    ((Odd.strictMono_pow (by decide : Odd 3)) hab)
  by_cases hboth : a%2=1 ∧ b%2=1
  · refine ⟨⟨a*(a^3-2*b^3),-b*(2*a^3-b^3),a^3+b^3,
      a^3-b^3,hD,?_,tangent_identity a b,Or.inr (tangent_mod_four hboth.1 hboth.2)⟩,rfl⟩
    exact ne_of_gt (by positivity)
  · have hpar' : (a%2=0 ∧ b%2=1) ∨ (a%2=1 ∧ b%2=0) := by omega
    refine ⟨⟨tripleA a b,tripleB a b,tripleC a b,a^3-b^3,hD,?_,
      triple_identity a b,triple_mod_four hpar'⟩,rfl⟩
    have hpos : 0<a^3*b^3 := mul_pos (pow_pos ha _) (pow_pos hb _)
    have hnorm : 0<a^6-a^3*b^3+b^6 := by
      nlinarith [sq_nonneg (a^3-b^3)]
    exact ne_of_gt (by dsimp [tripleC]; positivity)


/-- Every positive difference of two positive integer cubes has infinitely
many positive rational representations as a difference of cubes. -/
theorem infinite_nat_difference {a b : ℕ} (hb : 0<b) (hab : b<a) :
    {y : ℚ | 0<y ∧ ∃ x : ℚ, 0<x ∧ x^3-y^3=(a : ℚ)^3-b^3}.Infinite := by
  let g := Nat.gcd a b
  let u := a/g
  let v := b/g
  have hg : 0<g := Nat.gcd_pos_of_pos_right a hb
  have hv : 0<v := Nat.div_gcd_pos_of_pos_right a hb
  have hau : a=g*u := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have hbv : b=g*v := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
  have huv : v<u := by nlinarith
  have hcop : Nat.Coprime u v := Nat.coprime_div_gcd_div_gcd hg
  have hpar : u%2=1 ∨ v%2=1 := by
    by_contra h
    have hu2 : 2 ∣ u := Nat.dvd_of_mod_eq_zero (by omega)
    have hv2 : 2 ∣ v := Nat.dvd_of_mod_eq_zero (by omega)
    have hd := Nat.dvd_gcd hu2 hv2
    rw [hcop.gcd_eq_one] at hd
    norm_num at hd
  obtain ⟨s,hs⟩ := seed_exists (a := (u : ℤ)) (b := (v : ℤ))
    (by exact_mod_cast hv) (by exact_mod_cast huv) (by exact_mod_cast hpar)
  have hi := infinite_positive_cube_difference s
  have hsq : (s.D : ℚ)=(u : ℚ)^3-v^3 := by exact_mod_cast hs
  rw [hsq] at hi
  have hgQ : (0 : ℚ)<g := by exact_mod_cast hg
  have hinj : Function.Injective (fun y : ℚ => (g : ℚ)*y) :=
    mul_right_injective₀ hgQ.ne'
  have him := hi.image hinj.injOn
  apply him.mono
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨hy,x,hx,he⟩ := hy
  refine ⟨mul_pos hgQ hy,(g : ℚ)*x,mul_pos hgQ hx,?_⟩
  have hauQ : (a : ℚ)=(g : ℚ)*u := by exact_mod_cast hau
  have hbvQ : (b : ℚ)=(g : ℚ)*v := by exact_mod_cast hbv
  rw [hauQ,hbvQ]
  linear_combination (g : ℚ)^3*he

#print axioms seed_exists
#print axioms infinite_nat_difference

/-- The representation theorem also applies to rational initial roots. -/
theorem infinite_rational_difference {a b : ℚ} (hb : 0<b) (hab : b<a) :
    {y : ℚ | 0<y ∧ ∃ x : ℚ, 0<x ∧ x^3-y^3=a^3-b^3}.Infinite := by
  have ha := hb.trans hab
  let M := a.den*b.den
  let A := a.num.toNat*b.den
  let B := b.num.toNat*a.den
  have hM : 0<M := Nat.mul_pos a.den_pos b.den_pos
  have hMQ : (0 : ℚ)<M := by exact_mod_cast hM
  have hna : (a.num.toNat : ℚ)=a.num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr ha.le)
  have hnb : (b.num.toNat : ℚ)=b.num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hb.le)
  have hA : (A : ℚ)=(M : ℚ)*a := by
    dsimp [A,M]
    push_cast
    rw [hna,← a.mul_den_eq_num]
    ring
  have hB : (B : ℚ)=(M : ℚ)*b := by
    dsimp [B,M]
    push_cast
    rw [hnb,← b.mul_den_eq_num]
    ring
  have hBpos : 0<B := by exact_mod_cast (hB ▸ mul_pos hMQ hb : (0 : ℚ)<B)
  have hBA : B<A := by
    have hh : (B : ℚ)<A := by rw [hA,hB]; exact mul_lt_mul_of_pos_left hab hMQ
    exact_mod_cast hh
  have hi := infinite_nat_difference hBpos hBA
  have hinj : Function.Injective (fun y : ℚ => y/(M : ℚ)) := by
    intro x y he
    exact (div_left_inj' hMQ.ne').mp he
  apply (hi.image hinj.injOn).mono
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨hy,x,hx,he⟩ := hy
  refine ⟨div_pos hy hMQ,x/(M : ℚ),div_pos hx hMQ,?_⟩
  rw [hA,hB] at he
  rw [div_pow,div_pow,← sub_div]
  apply (div_eq_iff (pow_ne_zero 3 hMQ.ne')).mpr
  linear_combination he

#print axioms infinite_rational_difference
end Erdos1206.GeneralCubeDifferences
