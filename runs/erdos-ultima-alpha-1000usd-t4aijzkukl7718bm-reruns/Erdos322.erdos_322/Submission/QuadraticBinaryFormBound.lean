import Submission.UniformBinaryNorm
import Submission.PositiveBinaryFormCoercivity

/-! Coefficient-uniform bounds for positive monic binary quadratic forms,
including forms with a signed mixed coefficient. These are fiber bounds,
not bounds for the full quartic representation count. -/
namespace Erdos322Research.QuadraticBinaryFormBound

open Polynomial Finset PositiveBinaryFormBound UniformBinaryNorm
set_option Elab.async false

/-- Homogeneous monic binary quadratic form. -/
def quadraticValue (B C : ℤ) (a b : ℕ) : ℤ :=
  (a : ℤ)^2+B*(a : ℤ)*(b : ℤ)+C*(b : ℤ)^2

private def shifted (B : ℤ) (a : ℕ × ℕ) : ℤ := 2*(a.1 : ℤ)+B*(a.2 : ℤ)

/-- Completing the square gives a bound independent of both coefficients.
Neither primitivity nor a separate coordinate box is needed. -/
theorem quadratic_fiber_divisor_bound (B C : ℤ) (hD : 0 < 4*C-B^2)
    (n : ℕ) (hn : 0 < n) (S : Finset (ℕ × ℕ))
    (hS : ∀ a ∈ S, quadraticValue B C a.1 a.2 = (n : ℤ)) :
    S.card ≤ 8*(4*n).divisors.card^2 := by
  classical
  let d : ℕ := (4*C-B^2).toNat
  have hd : 0 < d := by dsimp [d]; omega
  have hdc : (d : ℤ)=4*C-B^2 := Int.toNat_of_nonneg hD.le
  let tag : (ℕ × ℕ) → ((ℕ × ℕ) × Bool) := fun a =>
    ((shifted B a |>.natAbs, a.2), decide (0 ≤ shifted B a))
  have hnorm (a : ℕ × ℕ) (ha : a ∈ S) :
      (shifted B a).natAbs^2+d*a.2^2=4*n := by
    have he : ((shifted B a).natAbs : ℤ)^2+(d : ℤ)*(a.2 : ℤ)^2=4*(n : ℤ) := by
      rw [Int.natCast_natAbs, sq_abs, hdc]
      calc
        shifted B a^2+(4*C-B^2)*(a.2 : ℤ)^2 =
            4*quadraticValue B C a.1 a.2 := by simp only [shifted,quadraticValue]; ring
        _ = 4*(n : ℤ) := by rw [hS a ha]
    exact_mod_cast he
  have hcard : S.card ≤ ((binaryNormSolutions d (4*n)) ×ˢ
      (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn tag
    · intro a ha
      exact Finset.mem_product.mpr ⟨(mem_binaryNormSolutions hd _).mpr (hnorm a ha),
        Finset.mem_univ _⟩
    · intro a ha b hb he
      have habs : (shifted B a).natAbs=(shifted B b).natAbs :=
        congrArg (fun x : ((ℕ × ℕ) × Bool) => x.1.1) he
      have hab : a.2=b.2 := congrArg (fun x : ((ℕ × ℕ) × Bool) => x.1.2) he
      have hsign : 0 ≤ shifted B a ↔ 0 ≤ shifted B b :=
        decide_eq_decide.mp (congrArg Prod.snd he)
      have hs : shifted B a=shifted B b := by
        have hh := congrArg (fun x : ℕ => (x : ℤ)) habs
        simp only [Int.natCast_natAbs] at hh
        by_cases hpa : 0 ≤ shifted B a
        · simpa only [abs_of_nonneg hpa, abs_of_nonneg (hsign.mp hpa)] using hh
        · have hpb : shifted B b ≤ 0 := le_of_not_ge (fun h => hpa (hsign.mpr h))
          rw [abs_of_nonpos (le_of_not_ge hpa), abs_of_nonpos hpb] at hh
          linarith
      have hx : a.1=b.1 := by
        simp only [shifted,hab] at hs
        have hz : (a.1 : ℤ)=(b.1 : ℤ) := by omega
        exact_mod_cast hz
      exact Prod.ext hx hab
  have hn4 : 0 < 4*n := by omega
  have hb := binary_norm_count_uniform hd hn4
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hcard
  omega

/-- Every positive monic binary quadratic fiber is uniformly subpolynomial,
even when its coefficients depend on the target. -/
theorem quadratic_fibers_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (B C : ℤ), 0 < 4*C-B^2 →
      ∀ (n : ℕ), 0 < n → ∀ S : Finset (ℕ × ℕ),
      (∀ a ∈ S, quadraticValue B C a.1 a.2=(n : ℤ)) →
      (S.card : ℝ) ≤ K*(n : ℝ)^ε := by
  obtain ⟨K,hK,hdiv⟩ := divisor_count_subpolynomial (ε/2) (by linarith)
  refine ⟨8*K^2*(4 : ℝ)^ε, by positivity, ?_⟩
  intro B C hD n hn S hS
  have hn4 : 0 < 4*n := by omega
  have hp : (((4*n : ℕ) : ℝ)^(ε/2))^2 = (4 : ℝ)^ε*(n : ℝ)^ε := by
    rw [pow_two, ← Real.rpow_add (by exact_mod_cast hn4)]
    rw [show ε/2+ε/2=ε by ring, Nat.cast_mul, Nat.cast_ofNat,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg n)]
  calc
    (S.card : ℝ) ≤ 8*((4*n).divisors.card : ℝ)^2 := by
      exact_mod_cast quadratic_fiber_divisor_bound B C hD n hn S hS
    _ ≤ 8*(K*(((4*n : ℕ) : ℝ)^(ε/2)))^2 := by
      gcongr
      exact hdiv (4*n) hn4
    _ = (8*K^2*(4 : ℝ)^ε)*(n : ℝ)^ε := by rw [mul_pow,hp]; ring

/-- A uniform bound on all fibers whose positive values divide one common
scale. The number of fibers is explicitly included. -/
theorem quadratic_divisor_bound (B C : ℤ) (hD : 0 < 4*C-B^2)
    (L : ℕ) (hL : 0 < L) (S : Finset (ℕ × ℕ))
    (hpos : ∀ a ∈ S, 0 < quadraticValue B C a.1 a.2)
    (hdvd : ∀ a ∈ S, (quadraticValue B C a.1 a.2).toNat ∣ L) :
    S.card ≤ L.divisors.card*(8*(4*L).divisors.card^2) := by
  classical
  let value : (ℕ × ℕ) → ℕ := fun a => (quadraticValue B C a.1 a.2).toNat
  let I := S.image value
  have hsub : I ⊆ L.divisors := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    exact Nat.mem_divisors.mpr ⟨hdvd a ha,hL.ne'⟩
  have hfib (n : ℕ) (hn : n ∈ I) :
      (S.filter fun a => value a=n).card ≤ 8*(4*L).divisors.card^2 := by
    obtain ⟨a,ha,hav⟩ := Finset.mem_image.mp hn
    have hnpos : 0 < n := by
      rw [← hav]
      have hh := hpos a ha
      change 0 < (quadraticValue B C a.1 a.2).toNat
      omega
    have hnL : n ∣ L := by rw [← hav]; exact hdvd a ha
    have hb := quadratic_fiber_divisor_bound B C hD n hnpos
      (S.filter fun a => value a=n) (by
        intro b hb
        obtain ⟨hbs,hbv⟩ := Finset.mem_filter.mp hb
        have he := Int.toNat_of_nonneg (hpos b hbs).le
        change ((value b : ℕ) : ℤ)=_ at he
        rw [hbv] at he
        exact he.symm)
    have hi : (4*n).divisors.card ≤ (4*L).divisors.card :=
      Finset.card_le_card (Nat.divisors_subset_of_dvd (by omega)
        (Nat.mul_dvd_mul_left 4 hnL))
    exact hb.trans (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hi 2))
  calc
    S.card = ∑ n ∈ I, (S.filter fun a => value a=n).card :=
      Finset.card_eq_sum_card_image value S
    _ ≤ ∑ _n ∈ I, 8*(4*L).divisors.card^2 := Finset.sum_le_sum hfib
    _ = I.card*(8*(4*L).divisors.card^2) := by simp
    _ ≤ L.divisors.card*(8*(4*L).divisors.card^2) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hsub)

/-- The divisor-fiber union is uniformly subpolynomial in the common scale. -/
theorem quadratic_divisor_fibers_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (B C : ℤ), 0 < 4*C-B^2 →
      ∀ (S : Finset (ℕ × ℕ)) (L : ℕ), 0 < L →
      (∀ a ∈ S, 0 < quadraticValue B C a.1 a.2) →
      (∀ a ∈ S, (quadraticValue B C a.1 a.2).toNat ∣ L) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  obtain ⟨K,hK,hdiv⟩ := divisor_count_subpolynomial (ε/3) (by linarith)
  refine ⟨8*K^3*((4 : ℝ)^(ε/3))^2, by positivity, ?_⟩
  intro B C hD S L hL hpos hdvd
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hdivL := hdiv L hL
  have hdiv4 := hdiv (4*L) (by omega)
  rw [Nat.cast_mul, Nat.cast_ofNat,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hLr.le] at hdiv4
  have hp : ((L : ℝ)^(ε/3))^3=(L : ℝ)^ε := by
    rw [pow_succ, pow_two, ← Real.rpow_add hLr, ← Real.rpow_add hLr]
    congr 1
    ring
  calc
    (S.card : ℝ) ≤ (L.divisors.card : ℝ)*(8*((4*L).divisors.card : ℝ)^2) := by
      exact_mod_cast quadratic_divisor_bound B C hD L hL S hpos hdvd
    _ ≤ (K*(L : ℝ)^(ε/3))*(8*(K*((4 : ℝ)^(ε/3)*(L : ℝ)^(ε/3)))^2) := by
      gcongr
    _ = (8*K^3*((4 : ℝ)^(ε/3))^2)*(L : ℝ)^ε := by
      calc
        _ = (8*K^3*((4 : ℝ)^(ε/3))^2)*((L : ℝ)^(ε/3))^3 := by ring
        _ = _ := by rw [hp]

end Erdos322Research.QuadraticBinaryFormBound
