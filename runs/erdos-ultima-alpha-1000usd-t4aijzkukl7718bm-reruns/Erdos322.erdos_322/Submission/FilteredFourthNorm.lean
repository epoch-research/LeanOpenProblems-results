import Submission.HomogeneousTopComponents
import Submission.QuarticFormalSpecialization

/-! A filtered-algebra leading-term criterion for constant fourth-power norms.
No integral-domain assumption is imposed on the filtered algebra. -/
namespace Erdos322Research.FilteredFourthNorm
noncomputable section
open QuarticFormalSpecialization
set_option Elab.async false
set_option maxHeartbeats 0

/-- Integer indices allow zero elements in negative filtration degrees. -/
structure LeadingSystem (R S : Type*) [CommRing R] [CommRing S] where
  bounded : ℤ → R → Prop
  top : ℤ → R →+ S
  zero_bounded : ∀ n, bounded n 0
  mono : ∀ {m n x}, m ≤ n → bounded m x → bounded n x
  add_bounded : ∀ {n x y}, bounded n x → bounded n y → bounded n (x+y)
  mul_bounded : ∀ {m n x y}, bounded m x → bounded n y → bounded (m+n) (x*y)
  exists_bound : ∀ x, ∃ n : ℕ, bounded n x
  top_mul : ∀ {m n x y}, bounded m x → bounded n y →
    top (m+n) (x*y) = top m x * top n y
  top_above : ∀ {m n x}, bounded m x → m < n → top n x = 0
  lower : ∀ {n x}, bounded n x → top n x = 0 → bounded (n-1) x

variable {R S : Type*} [CommRing R] [CommRing S]
namespace LeadingSystem
variable (F : LeadingSystem R S)

lemma pow_bounded {n : ℤ} {x : R} (h : F.bounded n x) (k : ℕ) (hk : 0 < k) :
    F.bounded (k*n) (x^k) := by
  induction k, hk using Nat.le_induction with
  | base => simpa using h
  | succ k hk ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
      F.mul_bounded ih h

lemma top_pow {n : ℤ} {x : R} (h : F.bounded n x) (k : ℕ) (hk : 0 < k) :
    F.top (k*n) (x^k) = F.top n x ^ k := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      F.top_mul (F.pow_bounded h k hk) h, ih, pow_succ]

/-- An anisotropic leading algebra prevents cancellation at positive degree. -/
theorem constant_norm_bounded_zero (hS : FourthAnisotropic S) (p : Fin 4 → R)
    (h : F.bounded 0 (∑ i, p i^4)) : ∀ i, F.bounded 0 (p i) := by
  classical
  choose d hd using F.exists_bound
  let D := Finset.univ.sup (fun i : Fin 4 ↦ d (p i))
  have hp (i : Fin 4) : F.bounded D (p i) :=
    F.mono (by exact_mod_cast (Finset.le_sup (f := fun i : Fin 4 ↦ d (p i))
      (Finset.mem_univ i))) (hd (p i))
  suffices ∀ N : ℕ, (∀ i, F.bounded N (p i)) → ∀ i, F.bounded 0 (p i) from this D hp
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    intro hN
    have ht : (∑ i, F.top (N+1) (p i)^4) = 0 := by
      have he := F.top_above h (show (0:ℤ) < 4*(N+1) by omega)
      rw [map_sum] at he
      have hNi (i) : F.bounded ((N:ℤ)+1) (p i) := by simpa using hN i
      have hpow (i) := F.top_pow (hNi i) 4 (by decide)
      norm_num only [Nat.cast_ofNat] at hpow
      simp_rw [hpow] at he
      exact he
    have hz := hS (fun i ↦ F.top (N+1) (p i)) ht
    apply ih
    intro i
    have hl := F.lower (hN i) (hz i)
    simpa using hl

end LeadingSystem

section Polynomial
open MvPolynomial HomogeneousTopComponents
variable {σ : Type*}

private def polyBound (n : ℤ) (p : MvPolynomial σ R) : Prop :=
  p = 0 ∨ (p.totalDegree : ℤ) ≤ n

private def polyTop (n : ℤ) : MvPolynomial σ R →+ MvPolynomial σ R :=
  if 0 ≤ n then (homogeneousComponent n.toNat).toAddMonoidHom else 0

private lemma polyTop_nat (n : ℕ) (p : MvPolynomial σ R) :
    polyTop (n : ℤ) p = homogeneousComponent n p := by simp [polyTop]

private lemma polyBound_mul {m n : ℤ} {p q : MvPolynomial σ R}
    (hp : polyBound m p) (hq : polyBound n q) : polyBound (m+n) (p*q) := by
  rcases hp with rfl | hp
  · exact Or.inl (zero_mul _)
  rcases hq with rfl | hq
  · exact Or.inl (mul_zero _)
  right
  have hd := totalDegree_mul p q
  have hd' : ((p*q).totalDegree : ℤ) ≤ (p.totalDegree : ℤ)+q.totalDegree := by exact_mod_cast hd
  exact hd'.trans (add_le_add hp hq)

private lemma polyTop_mul {m n : ℤ} {p q : MvPolynomial σ R}
    (hp : polyBound m p) (hq : polyBound n q) :
    polyTop (m+n) (p*q) = polyTop m p * polyTop n q := by
  rcases hp with rfl | hp
  · simp
  rcases hq with rfl | hq
  · simp
  have hm : 0 ≤ m := (Int.natCast_nonneg _).trans hp
  have hn : 0 ≤ n := (Int.natCast_nonneg _).trans hq
  lift m to ℕ using hm
  lift n to ℕ using hn
  rw [← Nat.cast_add, polyTop_nat, polyTop_nat, polyTop_nat]
  exact top_mul p q _ _ (by exact_mod_cast hp) (by exact_mod_cast hq)

private lemma polyTop_above {m n : ℤ} {p : MvPolynomial σ R}
    (hp : polyBound m p) (hmn : m < n) : polyTop n p = 0 := by
  rcases hp with rfl | hp
  · simp
  have hn : 0 ≤ n := le_of_lt ((Int.natCast_nonneg _).trans_lt (hp.trans_lt hmn))
  lift n to ℕ using hn
  rw [polyTop_nat]
  exact homogeneousComponent_eq_zero _ _ (by exact_mod_cast hp.trans_lt hmn)

private lemma polyBound_lower {n : ℤ} {p : MvPolynomial σ R}
    (hp : polyBound n p) (ht : polyTop n p = 0) : polyBound (n-1) p := by
  rcases hp with rfl | hp
  · exact Or.inl rfl
  have hn : 0 ≤ n := (Int.natCast_nonneg _).trans hp
  lift n to ℕ using hn
  rw [polyTop_nat] at ht
  have hd : p.totalDegree ≤ n := by exact_mod_cast hp
  rcases n with _ | n
  · left
    have he := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hd)
    rw [homogeneousComponent_zero] at ht
    exact he.trans ht
  · right
    have hl := sub_top_degree_lt p (n+1) (by omega) hd
    rw [ht, sub_zero] at hl
    have hh : (p.totalDegree : ℤ) ≤ n := by exact_mod_cast (show p.totalDegree ≤ n by omega)
    omega

/-- The ordinary total-degree filtration, including negative indices. -/
def polynomialSystem : LeadingSystem (MvPolynomial σ R) (MvPolynomial σ R) where
  bounded := polyBound
  top := polyTop
  zero_bounded _ := Or.inl rfl
  mono h hp := hp.imp_right (fun hh ↦ hh.trans h)
  add_bounded := by
    intro n p q hp hq
    rcases hp with rfl | hp
    · simpa using hq
    rcases hq with rfl | hq
    · exact Or.inr (by simpa using hp)
    right
    have hd := totalDegree_add p q
    have hd' : ((p+q).totalDegree : ℤ) ≤ max (p.totalDegree : ℤ) q.totalDegree := by exact_mod_cast hd
    exact hd'.trans (max_le hp hq)
  mul_bounded := polyBound_mul
  exists_bound p := ⟨p.totalDegree,Or.inr le_rfl⟩
  top_mul := polyTop_mul
  top_above := polyTop_above
  lower := polyBound_lower

lemma polynomial_bounded_iff (n : ℤ) (p : MvPolynomial σ R) :
    polynomialSystem.bounded n p ↔ p = 0 ∨ (p.totalDegree : ℤ) ≤ n := Iff.rfl

lemma polynomial_top_nat (n : ℕ) (p : MvPolynomial σ R) :
    polynomialSystem.top (n : ℤ) p = homogeneousComponent n p := polyTop_nat _ _

lemma polynomial_bound_C (c : R) : polynomialSystem.bounded 0 (C c : MvPolynomial σ R) :=
  Or.inr (by simp)

lemma polynomial_bound_negative {n : ℤ} (hn : n < 0) (p : MvPolynomial σ R)
    (h : polynomialSystem.bounded n p) : p = 0 := by
  rcases h with h | h
  · exact h
  · have := Int.natCast_nonneg p.totalDegree
    omega

lemma polynomial_bound_zero (p : MvPolynomial σ R) (h : polynomialSystem.bounded 0 p) :
    p = C (coeff 0 p) := by
  rcases h with rfl | h
  · simp
  · exact totalDegree_eq_zero_iff_eq_C.mp (by omega)

end Polynomial
end
end Erdos322Research.FilteredFourthNorm
