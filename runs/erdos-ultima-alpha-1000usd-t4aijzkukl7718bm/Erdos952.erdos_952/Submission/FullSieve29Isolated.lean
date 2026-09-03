import Submission.FullSieve29Result
import Submission.FiniteSievePerturbation

/-! The cutoff-29 candidate graph has an infinite component but also
arbitrarily large isolated Gaussian-prime vertices. This illustrates why an
unspecified infinite component does not give infinitude at a specified seed. -/
namespace Erdos952Investigation.FullSieve29Isolated
open FiniteSieveReduction ExceptionSieveReduction FiniteSievePerturbation
set_option maxHeartbeats 0
set_option maxRecDepth 3000

lemma offset_certificate : ∀ a b : Fin 5,
    (a.val ≠ 2 ∨ b.val ≠ 2) → ((a : ℤ)-2)^2+((b : ℤ)-2)^2 < 9 →
    ∃ p : Fin 30, p.val.Prime ∧ p.val ∣ 384540 ∧
      ((372391+(a : ℤ)-2)^2+((b : ℤ)-2)^2)%(p.val : ℤ) = 0 := by
  decide +kernel

lemma no_candidate_neighbors (q : ℕ) (hq : 32 < q) (hmod : q ≡ 372391 [MOD 384540]) :
    ∀ w : GaussianInt, ¬ (candidateGraph 9 29).Adj (q : GaussianInt) w := by
  intro w hw
  have hn := hw.2.2.2
  have hr : -2 ≤ w.re-(q : ℤ) ∧ w.re-(q : ℤ) ≤ 2 := by
    simp only [gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub,Zsqrtd.re_natCast,
      Zsqrtd.im_natCast,sub_zero] at hn
    constructor <;> nlinarith [sq_nonneg w.im]
  have hi : -2 ≤ w.im ∧ w.im ≤ 2 := by
    simp only [gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub,Zsqrtd.re_natCast,
      Zsqrtd.im_natCast,sub_zero] at hn
    constructor <;> nlinarith [sq_nonneg (w.re-(q : ℤ))]
  let a : Fin 5 := ⟨(w.re-(q : ℤ)+2).toNat,by omega⟩
  let b : Fin 5 := ⟨(w.im+2).toNat,by omega⟩
  have ha : (a : ℤ)-2 = w.re-(q : ℤ) := by dsimp [a]; omega
  have hb : (b : ℤ)-2 = w.im := by dsimp [b]; omega
  have hab : a.val ≠ 2 ∨ b.val ≠ 2 := by
    by_contra! h
    have har : (a : ℤ) = 2 := by exact_mod_cast h.1
    have hbi : (b : ℤ) = 2 := by exact_mod_cast h.2
    apply hw.2.2.1
    apply Zsqrtd.ext <;> dsimp <;> omega
  have hd : ((a : ℤ)-2)^2+((b : ℤ)-2)^2 < 9 := by
    rw [ha,hb]
    simpa only [gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub,Zsqrtd.re_natCast,
      Zsqrtd.im_natCast,sub_zero] using hn
  obtain ⟨p,hp,hpM,hzero⟩ := offset_certificate a b hab hd
  have hqp : (q : ℤ)%(p.val : ℤ) = (372391 : ℤ)%(p.val : ℤ) :=
    Int.natCast_modEq_iff.mpr (hmod.of_dvd hpM)
  have hwre : w.re = (q : ℤ)+(a : ℤ)-2 := by omega
  have hnorm : w.norm%(p.val : ℤ) = 0 := by
    rw [gaussian_norm_sq,hwre,← hb]
    simpa only [Int.add_emod,Int.sub_emod,pow_two,Int.mul_emod,Int.emod_emod,hqp] using hzero
  have hlarge : (29 : ℤ)^2 < w.norm := by
    have hq' : (32 : ℤ) < q := by exact_mod_cast hq
    rw [gaussian_norm_sq]
    nlinarith [sq_nonneg w.im]
  have ha := (candidate_iff_allowed_of_large (N := 29) hlarge).mp hw.2.1
  exact ha p.val (by have := p.isLt; omega) hp (Int.dvd_of_emod_eq_zero hnorm)

lemma singleton_component {G : SimpleGraph GaussianInt} {q : GaussianInt}
    (h : ∀ w, ¬ G.Adj q w) : {w | G.Reachable q w} = {q} := by
  ext w
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => simp
    | cons hab p => exact (h _ hab).elim
  · intro hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact SimpleGraph.Reachable.refl _

/-- The same finite cutoff isolates arbitrarily large actual Gaussian primes. -/
theorem arbitrarily_large_isolated_candidate_primes (M : ℕ) :
    ∃ q : ℕ, M < q ∧ Prime (q : GaussianInt) ∧
      {w | (candidateGraph 9 29).Reachable (q : GaussianInt) w} = {(q : GaussianInt)} := by
  obtain ⟨q,hq,hp,hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (M+33)
    (by decide : 384540 ≠ 0) (by decide : Nat.Coprime 372391 384540)
  have hp4 : q%4 = 3 := by
    have hh := hmod.of_dvd (by decide : 4 ∣ 384540)
    exact hh
  letI : Fact q.Prime := ⟨hp⟩
  exact ⟨q,by omega,(GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime q).mpr hp4,
    singleton_component (no_candidate_neighbors q (by omega) hmod)⟩

theorem explicit_isolated_prime : Prime (1910551 : GaussianInt) ∧
    {w | (candidateGraph 9 29).Reachable (1910551 : GaussianInt) w} = {(1910551 : GaussianInt)} := by
  have hp : Nat.Prime 1910551 := by norm_num
  letI : Fact (Nat.Prime 1910551) := ⟨hp⟩
  refine ⟨(GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 1910551).mpr (by decide),?_⟩
  exact singleton_component (no_candidate_neighbors 1910551 (by decide) (by decide))

/-- The isolated vertices coexist with an infinite component at exactly the
same jump bound and cutoff. This does not assert anything about seed `3`. -/
theorem isolated_primes_and_infinite_component :
    (∃ z : GaussianInt, {w | (candidateGraph 9 29).Reachable z w}.Infinite) ∧
    ∀ M : ℕ, ∃ q : ℕ, M < q ∧ Prime (q : GaussianInt) ∧
      {w | (candidateGraph 9 29).Reachable (q : GaussianInt) w} = {(q : GaussianInt)} :=
  ⟨(candidate_has_infinite_iff_sieve_ray 9 29).mpr FullSieve29.full_cutoff29_ray,
    arbitrarily_large_isolated_candidate_primes⟩

#print axioms arbitrarily_large_isolated_candidate_primes
#print axioms explicit_isolated_prime
#print axioms isolated_primes_and_infinite_component
end Erdos952Investigation.FullSieve29Isolated
