import Submission.RecurrentIncrementObstruction
import Submission.PeriodicIncrementObstruction
import Submission.StripObstruction

/-! Finite congruence information cannot determine the successor increments
of an injective Gaussian-prime sequence. Uniformly congruence-continuous
successor rules are excluded for bounded-step prime orbits. These conclusions
do not constrain an arbitrary rule to have the required continuity. -/
namespace Erdos952Investigation
namespace ModularSuccessorObstruction
open RecurrentIncrementObstruction (residue)
set_option maxHeartbeats 0

abbrev increment (x : ℕ → GaussianInt) (n : ℕ) := x (n+1)-x n

lemma finite_state_increments_periodic {α : Type*} [Finite α]
    (x : ℕ → GaussianInt) (s : ℕ → α)
    (hs : ∀ i j, s i = s j → s (i+1) = s (j+1))
    (hd : ∀ i j, s i = s j → increment x i = increment x j) :
    ∃ N k : ℕ, 0 < k ∧ ∀ n ≥ N,
      x (n+k+1)-x (n+k) = x (n+1)-x n := by
  have hrep : ∃ a b : ℕ, a < b ∧ s a = s b := by
    obtain ⟨a,b,hab,he⟩ := Finite.exists_ne_map_eq_of_infinite s
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact ⟨a,b,hlt,he⟩
    · exact ⟨b,a,hgt,he.symm⟩
  obtain ⟨a,b,hab,he⟩ := hrep
  have hsame (i : ℕ) : s (a+i) = s (b+i) := by
    induction i with
    | zero => simpa using he
    | succ i ih => simpa only [Nat.add_succ] using hs (a+i) (b+i) ih
  refine ⟨a,b-a,by omega,?_⟩
  intro n hn
  have hh := (hd (a+(n-a)) (b+(n-a)) (hsame (n-a))).symm
  have he1 : a+(n-a) = n := by omega
  have he2 : b+(n-a) = n+(b-a) := by omega
  simpa only [he1,he2,increment] using hh

/-- No finite-state machine can emit the successive increments of an
injective Gaussian-prime sequence. Its state transition must be deterministic. -/
theorem no_finite_state_increment_rule {α : Type*} [Finite α]
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (s : ℕ → α) (hs : ∀ i j, s i = s j → s (i+1) = s (j+1)) :
    ¬ ∀ i j, s i = s j → increment x i = increment x j := by
  intro hd
  exact prime_walk_increments_not_eventually_periodic x hx hp
    (finite_state_increments_periodic x s hs hd)

theorem no_modular_increment_rule (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n)) (M : ℕ) (hM : 0 < M) :
    ¬ ∀ i j, residue M (x i) = residue M (x j) → increment x i = increment x j := by
  intro hd
  letI : NeZero M := ⟨hM.ne'⟩
  have hs : ∀ i j, residue M (x i) = residue M (x j) →
      residue M (x (i+1)) = residue M (x (j+1)) := by
    intro i j hij
    have hdi := congrArg (residue M) (hd i j hij)
    simp only [increment,map_sub,hij] at hdi
    exact sub_left_injective hdi
  exact no_finite_state_increment_rule x hx hp (fun n => residue M (x n)) hs hd

/-- Every tail contains congruent positions with different next increments,
for every positive modulus. This conclusion needs no step bound. -/
theorem modular_ambiguity_on_every_tail (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (M K : ℕ) (hM : 0 < M) :
    ∃ i ≥ K, ∃ j ≥ K, residue M (x i) = residue M (x j) ∧
      increment x i ≠ increment x j := by
  have hy : Function.Injective (fun n => x (K+n)) := by
    intro i j he
    exact Nat.add_left_cancel (hx he)
  have hh := no_modular_increment_rule (fun n => x (K+n)) hy (fun n => hp (K+n)) M hM
  push_neg at hh
  obtain ⟨i,j,hres,hne⟩ := hh
  refine ⟨K+i,by omega,K+j,by omega,hres,?_⟩
  simpa only [increment,Nat.add_assoc] using hne

lemma residue_eq_iff_dvd (M : ℕ) (z w : GaussianInt) :
    residue M z = residue M w ↔
      (M : ℤ) ∣ (z-w).re ∧ (M : ℤ) ∣ (z-w).im := by
  constructor
  · intro h
    have hr := congrArg Prod.fst h
    have hi := congrArg Prod.snd h
    constructor
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
      change ((z.re-w.re : ℤ) : ZMod M) = 0
      change (z.re : ZMod M) = w.re at hr
      simp only [Int.cast_sub,hr,sub_self]
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
      change ((z.im-w.im : ℤ) : ZMod M) = 0
      change (z.im : ZMod M) = w.im at hi
      simp only [Int.cast_sub,hi,sub_self]
  · rintro ⟨hr,hi⟩
    apply Prod.ext
    · change (z.re : ZMod M) = w.re
      apply sub_eq_zero.mp
      rw [← Int.cast_sub]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hr
    · change (z.im : ZMod M) = w.im
      apply sub_eq_zero.mp
      rw [← Int.cast_sub]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr hi

lemma residue_eq_of_dvd {M N : ℕ} (hMN : M ∣ N) {z w : GaussianInt}
    (h : residue N z = residue N w) : residue M z = residue M w := by
  have hd : (M : ℤ) ∣ N := by exact_mod_cast hMN
  obtain ⟨hr,hi⟩ := (residue_eq_iff_dvd N z w).mp h
  exact (residue_eq_iff_dvd M z w).mpr ⟨hd.trans hr,hd.trans hi⟩

lemma abs_im_le_norm (z : GaussianInt) : |z.im| ≤ z.norm := by
  have hs := Int.le_self_sq |z.im|
  rw [gaussian_norm_sq]
  nlinarith [sq_abs z.im,sq_nonneg z.re]

lemma bounded_residue_injective (B : ℕ) {z w : GaussianInt}
    (hz : z.norm ≤ (B : ℤ)) (hw : w.norm ≤ (B : ℤ))
    (hres : residue (2*B+1) z = residue (2*B+1) w) : z = w := by
  obtain ⟨hr,hi⟩ := (residue_eq_iff_dvd _ z w).mp hres
  have hzr := abs_le.mp ((abs_re_le_gaussian_norm z).trans hz)
  have hwr := abs_le.mp ((abs_re_le_gaussian_norm w).trans hw)
  have hzi := abs_le.mp ((abs_im_le_norm z).trans hz)
  have hwi := abs_le.mp ((abs_im_le_norm w).trans hw)
  have her : (z-w).re = 0 := Int.eq_zero_of_abs_lt_dvd hr (by
    rw [Zsqrtd.re_sub]
    apply abs_lt.mpr
    push_cast
    constructor <;> omega)
  have hei : (z-w).im = 0 := Int.eq_zero_of_abs_lt_dvd hi (by
    rw [Zsqrtd.im_sub]
    apply abs_lt.mpr
    push_cast
    constructor <;> omega)
  apply Zsqrtd.ext <;> simp only [Zsqrtd.re_sub,Zsqrtd.im_sub] at her hei <;> omega

/-- Uniform continuity for the coordinate congruence uniformity. The input
modulus is allowed to depend on the desired output modulus. -/
def UniformlyCongruenceContinuous (F : GaussianInt → GaussianInt) : Prop :=
  ∀ M : ℕ, 0 < M → ∃ N : ℕ, 0 < N ∧ ∀ z w,
    residue N z = residue N w → residue M (F z) = residue M (F w)

lemma uniformlyCongruenceContinuous_sub_id {F : GaussianInt → GaussianInt}
    (hF : UniformlyCongruenceContinuous F) :
    UniformlyCongruenceContinuous (fun z => F z-z) := by
  intro M hM
  obtain ⟨N,hN,hf⟩ := hF M hM
  refine ⟨N*M,Nat.mul_pos hN hM,?_⟩
  intro z w hzw
  have hNzw := residue_eq_of_dvd (dvd_mul_right N M) hzw
  have hMzw := residue_eq_of_dvd (dvd_mul_left M N) hzw
  rw [map_sub,map_sub,hf z w hNzw,hMzw]

/-- A bounded-step prime orbit cannot be generated by any globally uniformly
congruence-continuous successor map. No global prime-preservation is assumed. -/
theorem no_uniformly_congruence_continuous_orbit (F : GaussianInt → GaussianInt)
    (hF : UniformlyCongruenceContinuous F) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) (C : ℤ)
    (hs : ∀ n, (increment x n).norm < C)
    (horbit : ∀ n, x (n+1) = F (x n)) : False := by
  let B := C.natAbs
  have hB : C ≤ (B : ℤ) := by dsimp [B]; exact Int.le_natAbs
  have hbound (n : ℕ) : (F (x n)-x n).norm ≤ (B : ℤ) := by
    rw [← horbit n]
    exact (hs n).le.trans hB
  obtain ⟨M,hM,hg⟩ := uniformlyCongruenceContinuous_sub_id hF (2*B+1) (by omega)
  apply no_modular_increment_rule x hx hp M hM
  intro i j hij
  have he := bounded_residue_injective B (hbound i) (hbound j) (hg (x i) (x j) hij)
  simpa only [increment,horbit] using he

#print axioms modular_ambiguity_on_every_tail
#print axioms no_uniformly_congruence_continuous_orbit
end ModularSuccessorObstruction
end Erdos952Investigation
