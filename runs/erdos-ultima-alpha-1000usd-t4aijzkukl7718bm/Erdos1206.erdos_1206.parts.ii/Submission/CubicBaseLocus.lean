import Submission.InertPrimeCubes

/-!
The common-zero locus of the cubic parametrization, and a restriction on
cancellation primes. These are algebraic auxiliary results, not a density
construction or a disproof of Erdős 1206.
-/

namespace Erdos1206.CubicBaseLocus

variable {K : Type*} [CommRing K]

def Q (a b : K) : K := a^2-a*b+b^2

def A (a b t : K) : K :=
  t^3+(a-2*b)*t^2+3*a^2*t+3*Q a b*(a-b)
def B (a b t : K) : K :=
  t^3+(a+b)*t^2+3*(a-b)^2*t+3*a*Q a b
def C (a b t : K) : K :=
  t^3-(a+b)*t^2+3*(a-b)^2*t-3*a*Q a b
def D (a b t : K) : K :=
  t^3-(a-2*b)*t^2+3*a^2*t-3*Q a b*(a-b)

lemma sum_outer (a b t : K) :
    A a b t + D a b t = 2*t*(t^2+3*a^2) := by
  dsimp [A,D]
  ring

lemma pair_sum_difference (a b t : K) :
    A a b t + D a b t - B a b t - C a b t = 6*b*t*(2*a-b) := by
  dsimp [A,B,C,D]
  ring

lemma zero_b_factorization (a t : K) :
    A a 0 t = (t+a)*(t^2+3*a^2) ∧
    B a 0 t = (t+a)*(t^2+3*a^2) ∧
    C a 0 t = (t-a)*(t^2+3*a^2) ∧
    D a 0 t = (t-a)*(t^2+3*a^2) := by
  dsimp [A,B,C,D,Q]
  constructor; ring
  constructor; ring
  constructor <;> ring

lemma double_a_factorization (a t : K) :
    A a (2*a) t = (t-3*a)*(t^2+3*a^2) ∧
    B a (2*a) t = (t+3*a)*(t^2+3*a^2) ∧
    C a (2*a) t = (t-3*a)*(t^2+3*a^2) ∧
    D a (2*a) t = (t+3*a)*(t^2+3*a^2) := by
  dsimp [A,B,C,D,Q]
  constructor; ring
  constructor; ring
  constructor <;> ring

section Field
variable {F : Type*} [Field F]

/-- The six geometric base points are grouped into three quadratic loci. -/
theorem common_zero_iff (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (a b t : F) :
    (A a b t = 0 ∧ B a b t = 0 ∧ C a b t = 0 ∧ D a b t = 0) ↔
      (t = 0 ∧ Q a b = 0) ∨
      (b = 0 ∧ t^2+3*a^2 = 0) ∨
      (b = 2*a ∧ t^2+3*a^2 = 0) := by
  constructor
  · rintro ⟨ha,hb,hc,hd⟩
    by_cases ht : t = 0
    · left
      refine ⟨ht, ?_⟩
      by_contra hq
      have hpa : 3*a*Q a b = 0 := by simpa [B,ht] using hb
      have ha0 : a = 0 := (mul_eq_zero.mp ((mul_eq_zero.mp hpa).resolve_right hq)).resolve_left h3
      have hab : 3*Q a b*(a-b) = 0 := by simpa [A,ht] using ha
      have hab0 : a-b = 0 := (mul_eq_zero.mp hab).resolve_left (mul_ne_zero h3 hq)
      have hb0 : b = 0 := by rw [ha0] at hab0; simpa using hab0
      exact hq (by simp [Q,ha0,hb0])
    · right
      have hs : 2*t*(t^2+3*a^2) = 0 := by rw [← sum_outer,ha,hd]; simp
      have hn : t^2+3*a^2 = 0 := (mul_eq_zero.mp hs).resolve_left (mul_ne_zero h2 ht)
      have hg : 6*b*t*(2*a-b) = 0 := by
        rw [← pair_sum_difference,ha,hb,hc,hd]
        simp
      have h6 : (6 : F) ≠ 0 := by
        convert mul_ne_zero h2 h3 using 1 <;> norm_num
      by_cases hb0 : b = 0
      · exact Or.inl ⟨hb0,hn⟩
      · exact Or.inr ⟨(sub_eq_zero.mp ((mul_eq_zero.mp hg).resolve_left
          (mul_ne_zero (mul_ne_zero h6 hb0) ht))).symm, hn⟩
  · rintro (⟨ht,hq⟩ | ⟨hb,hn⟩ | ⟨hb,hn⟩)
    · simp [A,B,C,D,ht,hq]
    · subst b
      obtain ⟨ha,hb,hc,hd⟩ := zero_b_factorization a t
      simp [ha,hb,hc,hd,hn]
    · subst b
      obtain ⟨ha,hb,hc,hd⟩ := double_a_factorization a t
      simp [ha,hb,hc,hd,hn]

end Field

private lemma norm_anisotropic {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
    {x y : ZMod p} (h : x^2+x*y+y^2 = 0) : x = 0 ∧ y = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hcube : x^3 = y^3 := by
    apply sub_eq_zero.mp
    calc
      _ = (x-y)*(x^2+x*y+y^2) := by ring
      _ = 0 := by rw [h]; ring
  have he := Erdos1206.cube_injective_zmod_of_mod_three_eq_two hp hp3 hcube
  have h3 : (3 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 3 p).not.mpr
    intro hd
    have heq := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp hd
    omega
  have hz : (3 : ZMod p)*x^2 = 0 := by rw [← he] at h; linear_combination h
  have hx : x = 0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz).resolve_left h3)
  exact ⟨hx, he ▸ hx⟩

/-- At an odd inert prime the only common zero is the zero parameter vector. -/
theorem common_zero_inert {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
    (hp2 : p ≠ 2) (a b t : ZMod p)
    (h : A a b t = 0 ∧ B a b t = 0 ∧ C a b t = 0 ∧ D a b t = 0) :
    a = 0 ∧ b = 0 ∧ t = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 2 p).not.mpr
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)
  have h3 : (3 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 3 p).not.mpr
    intro hd
    have heq := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).mp hd
    omega
  rcases (common_zero_iff h2 h3 a b t).mp h with ⟨ht,hq⟩ | ⟨hb,hn⟩ | ⟨hb,hn⟩
  · have hh : a^2+a*(-b)+(-b)^2 = 0 := by
      dsimp [Q] at hq
      linear_combination hq
    obtain ⟨ha,hb⟩ := norm_anisotropic hp hp3 hh
    exact ⟨ha,neg_eq_zero.mp hb,ht⟩
  all_goals
    have hh : (t+a)^2+(t+a)*(-2*a)+(-2*a)^2 = 0 := by linear_combination hn
    obtain ⟨hta,ha⟩ := norm_anisotropic hp hp3 hh
    have ha0 : a = 0 := (mul_eq_zero.mp ha).resolve_left (neg_ne_zero.mpr h2)
    have ht0 : t = 0 := by simpa [ha0] using hta
    exact ⟨ha0,by simp_all,ht0⟩

/-- Consequently, common cancellation of primitive integral parameters can
only occur at 2, 3, or primes congruent to 1 modulo 3. -/
theorem common_prime_split_or_small {p : ℕ} (hp : p.Prime) {a b t : ℤ}
    (hprimitive : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ t))
    (hA : (p : ℤ) ∣ A a b t) (hB : (p : ℤ) ∣ B a b t)
    (hC : (p : ℤ) ∣ C a b t) (hD : (p : ℤ) ∣ D a b t) :
    p = 2 ∨ p = 3 ∨ p % 3 = 1 := by
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  by_cases hp3 : p = 3
  · exact Or.inr (Or.inl hp3)
  right; right
  have hpmod : p % 3 ≠ 0 := by
    intro hh
    have hdiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero hh
    have heq := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 3) hp).mp hdiv
    exact hp3 heq.symm
  by_contra hn
  have hpmod2 : p % 3 = 2 := by omega
  have hcommon : A (a : ZMod p) b t = 0 ∧ B (a : ZMod p) b t = 0 ∧
      C (a : ZMod p) b t = 0 ∧ D (a : ZMod p) b t = 0 := by
    constructor
    · simpa [A,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (A a b t) p).mpr hA
    constructor
    · simpa [B,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (B a b t) p).mpr hB
    constructor
    · simpa [C,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (C a b t) p).mpr hC
    · simpa [D,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (D a b t) p).mpr hD
  obtain ⟨ha,hb,ht⟩ := common_zero_inert hp hpmod2 hp2 (a : ZMod p) b t hcommon
  exact hprimitive ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha,
    (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb,
    (ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp ht⟩

#print axioms common_zero_iff
#print axioms common_zero_inert
#print axioms common_prime_split_or_small

end Erdos1206.CubicBaseLocus
