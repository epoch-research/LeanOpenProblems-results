import Submission.InverseTotientMoments
import Submission.SquarefreeInput

/-!
# Removing common factors from squarefree totient collisions

For exponents above one half, the common divisor of a pair contributes a
convergent factor. The unresolved divergence in Erdős 821 must therefore
already occur among coprime squarefree collision pairs. No such divergence
for every subcritical exponent is asserted here.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821
namespace PrimitiveCollisions

/-- Ordered pairs of squarefree inputs with equal totient. -/
def Collision := {ab : ℕ × ℕ //
  Squarefree ab.1 ∧ Squarefree ab.2 ∧ Nat.totient ab.1 = Nat.totient ab.2}

/-- The pairs left after removing their common divisor. -/
def Primitive := {ab : Collision // Nat.Coprime ab.val.1 ab.val.2}

lemma totient_divisor_factor {a d : ℕ} (ha : Squarefree a) (hd : d ∣ a) :
    Nat.totient a = Nat.totient d * Nat.totient (a / d) := by
  have hc : Nat.Coprime d (a / d) := Nat.coprime_of_squarefree_mul
    (by rwa [Nat.mul_div_cancel' hd])
  simpa only [Nat.mul_div_cancel' hd] using Nat.totient_mul hc

/-- Division by the gcd preserves the totient collision for squarefree inputs. -/
def primitivePart (c : Collision) : Primitive := by
  let d := Nat.gcd c.val.1 c.val.2
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero c.property.1.ne_zero)
  have heq : Nat.totient (c.val.1 / d) = Nat.totient (c.val.2 / d) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr hd)
    rw [← totient_divisor_factor c.property.1 (Nat.gcd_dvd_left _ _),
      ← totient_divisor_factor c.property.2.1 (Nat.gcd_dvd_right _ _)]
    exact c.property.2.2
  exact ⟨⟨(c.val.1 / d, c.val.2 / d),
    c.property.1.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)),
    c.property.2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)),
    heq⟩, Nat.coprime_div_gcd_div_gcd hd⟩

@[simp] lemma primitivePart_fst (c : Collision) :
    (primitivePart c).val.val.1 = c.val.1 / Nat.gcd c.val.1 c.val.2 := rfl

@[simp] lemma primitivePart_snd (c : Collision) :
    (primitivePart c).val.val.2 = c.val.2 / Nat.gcd c.val.1 c.val.2 := rfl

/-- The gcd and the primitive pair determine the original ordered pair. -/
def split (c : Collision) : ℕ × Primitive :=
  (Nat.gcd c.val.1 c.val.2, primitivePart c)

lemma split_injective : Function.Injective split := by
  intro a b h
  have hd : Nat.gcd a.val.1 a.val.2 = Nat.gcd b.val.1 b.val.2 := congrArg Prod.fst h
  have hp : primitivePart a = primitivePart b := congrArg Prod.snd h
  have h1 := congrArg (fun p : Primitive => p.val.val.1) hp
  have h2 := congrArg (fun p : Primitive => p.val.val.2) hp
  simp only [primitivePart_fst, primitivePart_snd] at h1 h2
  apply Subtype.ext
  apply Prod.ext
  · calc
      a.val.1 = Nat.gcd a.val.1 a.val.2 *
          (a.val.1 / Nat.gcd a.val.1 a.val.2) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
      _ = Nat.gcd b.val.1 b.val.2 *
          (b.val.1 / Nat.gcd b.val.1 b.val.2) := by rw [h1, hd]
      _ = b.val.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  · calc
      a.val.2 = Nat.gcd a.val.1 a.val.2 *
          (a.val.2 / Nat.gcd a.val.1 a.val.2) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
      _ = Nat.gcd b.val.1 b.val.2 *
          (b.val.2 / Nat.gcd b.val.1 b.val.2) := by rw [h2, hd]
      _ = b.val.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)

lemma weight_split (s : ℝ) (c : Collision) :
    (Nat.totient c.val.1 : ℝ) ^ (-(2*s)) =
      (Nat.totient (split c).1 : ℝ) ^ (-(2*s)) *
        (Nat.totient (split c).2.val.val.1 : ℝ) ^ (-(2*s)) := by
  change (Nat.totient c.val.1 : ℝ) ^ (-(2*s)) =
    (Nat.totient (Nat.gcd c.val.1 c.val.2) : ℝ) ^ (-(2*s)) *
      (Nat.totient (c.val.1 / Nat.gcd c.val.1 c.val.2) : ℝ) ^ (-(2*s))
  rw [totient_divisor_factor c.property.1 (Nat.gcd_dvd_left _ _), Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

/-- Above the half line, summability of all squarefree collision pairs is
exactly summability of the primitive pairs. The common-divisor contribution
is bounded by the unconditional convergent first-moment input series. -/
theorem summable_collision_iff_primitive (s : ℝ) (hs : 1/2 < s) :
    Summable (fun c : Collision => (Nat.totient c.val.1 : ℝ) ^ (-(2*s))) ↔
      Summable (fun p : Primitive => (Nat.totient p.val.val.1 : ℝ) ^ (-(2*s))) := by
  constructor
  · intro H
    exact H.subtype _
  · intro H
    have Hd := summable_totient_neg_rpow (2*s) (by linarith)
    have Hprod := Hd.mul_of_nonneg H
      (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact (Hprod.comp_injective split_injective).congr (fun c => (weight_split s c).symm)

/-- A quantitative upper comparison; this is a bound on the actual collision
series, not on an unrelated majorant. -/
lemma collision_tsum_le (s : ℝ) (hs : 1/2 < s)
    (H : Summable (fun p : Primitive => (Nat.totient p.val.val.1 : ℝ)^(-(2*s)))) :
    (∑' c : Collision, (Nat.totient c.val.1 : ℝ)^(-(2*s))) ≤
      (∑' d : ℕ, (Nat.totient d : ℝ)^(-(2*s))) *
        ∑' p : Primitive, (Nat.totient p.val.val.1 : ℝ)^(-(2*s)) := by
  have Hd := summable_totient_neg_rpow (2*s) (by linarith)
  have Hprod := Hd.mul_of_nonneg H
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [Hd.tsum_mul_tsum H Hprod]
  exact Summable.tsum_le_tsum_of_inj split split_injective
    (fun c _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun c => (weight_split s c).le)
    ((summable_collision_iff_primitive s hs).mpr H) Hprod

/-- Primitive pairs already form a subfamily of all collision pairs. -/
lemma primitive_tsum_le (s : ℝ)
    (H : Summable (fun c : Collision => (Nat.totient c.val.1 : ℝ)^(-(2*s)))) :
    (∑' p : Primitive, (Nat.totient p.val.val.1 : ℝ)^(-(2*s))) ≤
      ∑' c : Collision, (Nat.totient c.val.1 : ℝ)^(-(2*s)) :=
  Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
    (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun _ => le_rfl)
    (H.subtype _) H

/-- A fiber of the squarefree collision space is a product of two ordinary
squarefree totient fibers. -/
def fiberEquiv (n : ℕ) :
    {c : Collision // Nat.totient c.val.1 = n} ≃
      {a : ℕ // Squarefree a ∧ Nat.totient a = n} ×
      {a : ℕ // Squarefree a ∧ Nat.totient a = n} where
  toFun c := (⟨c.val.val.1, c.val.property.1, c.property⟩,
    ⟨c.val.val.2, c.val.property.2.1, c.val.property.2.2.symm.trans c.property⟩)
  invFun ab := ⟨⟨(ab.1.val, ab.2.val), ab.1.property.1, ab.2.property.1,
    ab.1.property.2.trans ab.2.property.2.symm⟩, ab.1.property.2⟩
  left_inv c := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv ab := by rfl

lemma fiber_card (n : ℕ) :
    Nat.card {c : Collision // Nat.totient c.val.1 = n} = gSquarefree n ^ 2 := by
  have hc : Nat.card {a : ℕ // Squarefree a ∧ Nat.totient a = n} = gSquarefree n := by
    change Nat.card ↑({a : ℕ | Squarefree a ∧ Nat.totient a = n}) = _
    rw [Nat.card_coe_set_eq]
    rfl
  rw [Nat.card_congr (fiberEquiv n), Nat.card_prod, hc, pow_two]

lemma fiber_tsum (w : ℕ → ℝ) (n : ℕ) :
    (∑' c : {c : Collision // Nat.totient c.val.1 = n},
      w (Nat.totient c.val.val.1)) = (gSquarefree n : ℝ)^2 * w n := by
  have heq : (fun c : {c : Collision // Nat.totient c.val.1 = n} =>
      w (Nat.totient c.val.val.1)) = (fun _ => w n) :=
    funext (fun c => congrArg w c.property)
  rw [heq, tsum_const, nsmul_eq_mul, fiber_card, Nat.cast_pow]

lemma summable_collision_weight_iff (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    Summable (fun c : Collision => w (Nat.totient c.val.1)) ↔
      Summable (fun n : ℕ => (gSquarefree n : ℝ)^2 * w n) := by
  have H := summable_partition
    (f := fun c : Collision => w (Nat.totient c.val.1))
    (s := fun n : ℕ => {c : Collision | Nat.totient c.val.1 = n})
    (fun c => hw _) (by intro c; exact ⟨_, rfl, fun n hn => hn.symm⟩)
  constructor
  · intro h
    exact (H.mp h).2.congr (fiber_tsum w)
  · intro h
    apply H.mpr
    refine ⟨?_, h.congr (fun n => (fiber_tsum w n).symm)⟩
    intro n
    letI : Fintype {a : ℕ // Squarefree a ∧ Nat.totient a = n} :=
      (finite_squarefree_totient_fiber n).fintype
    letI : Fintype {c : Collision // Nat.totient c.val.1 = n} :=
      Fintype.ofEquiv _ (fiberEquiv n).symm
    change Summable (fun c : {c : Collision // Nat.totient c.val.1 = n} =>
      w (Nat.totient c.val.val.1))
    exact summable_of_finite_support (Set.toFinite _)

/-- Exact analytic removal of the common divisor from the second moment. -/
theorem summable_squarefree_second_moment_iff (s : ℝ) (hs : 1/2 < s) :
    Summable (fun n : ℕ => (gSquarefree n : ℝ)^2 * (n : ℝ)^(-(2*s))) ↔
      Summable (fun p : Primitive => (Nat.totient p.val.val.1 : ℝ)^(-(2*s))) := by
  rw [← summable_collision_weight_iff (fun n => (n : ℝ)^(-(2*s)))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact summable_collision_iff_primitive s hs

lemma not_summable_square_moment_of_infinite (f : ℕ → ℝ) (s : ℝ)
    (H : {n : ℕ | (n : ℝ)^s < f n}.Infinite) :
    ¬Summable (fun n : ℕ => (f n)^2 * (n : ℝ)^(-(2*s))) := by
  intro hsum
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hsum.tendsto_atTop_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n, hn, hnN⟩ := H.exists_gt (max N 0)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (le_max_right N 0) hnN)
  have hnpow : 0 < (n : ℝ)^s := Real.rpow_pos_of_pos hn0 s
  have hg : (n : ℝ)^s < f n := hn
  have hsq : ((n : ℝ)^s)^2 < (f n)^2 := by nlinarith
  have hbase : ((n : ℝ)^s)^2 * (n : ℝ)^(-(2*s)) = 1 := by
    rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add hn0]
    push_cast
    rw [show s * 2 + -(2*s) = (0 : ℝ) by ring, Real.rpow_zero]
  have hlo : 1 < (f n)^2 * (n : ℝ)^(-(2*s)) := by
    rw [← hbase]
    exact mul_lt_mul_of_pos_right hsq (Real.rpow_pos_of_pos hn0 _)
  exact (not_lt_of_ge hlo.le) (hN n ((le_max_left N 0).trans hnN.le))

/-- An exact primitive-collision criterion. The right hand side remains
unproved for general subcritical exponents. -/
theorem erdos_821_iff_primitive_collision_divergence :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite) ↔
      ∀ s : ℝ, 1/2 < s → s < 1 →
        ¬Summable (fun p : Primitive => (Nat.totient p.val.val.1 : ℝ)^(-(2*s))) := by
  constructor
  · intro H s hs hs1 hsum
    have Hsf := erdos_821_iff_squarefree_inputs.mp H (1-s) (by linarith)
    simp only [sub_sub_cancel] at Hsf
    exact not_summable_square_moment_of_infinite (fun n => (gSquarefree n : ℝ)) s Hsf
      ((summable_squarefree_second_moment_iff s hs).mpr hsum)
  · intro H
    by_contra Hneg
    obtain ⟨ε, h⟩ := not_forall.mp Hneg
    obtain ⟨hε, hfin⟩ := _root_.not_imp.mp h
    obtain ⟨B, hB⟩ := (Set.not_infinite.mp hfin).bddAbove
    have hbound : ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (n : ℝ)^(1-ε) := by
      filter_upwards [eventually_gt_atTop B] with n hn
      exact le_of_not_gt (fun hg => (not_le_of_gt hn) (hB hg))
    let e := min ε 1
    have he : 0 < e := lt_min hε (by norm_num)
    have heε : e ≤ ε := min_le_left _ _
    have he1 : e ≤ 1 := min_le_right _ _
    have hs : 1/2 < 1-e/4 := by linarith
    have hs1 : 1-e/4 < 1 := by linarith
    have Hfull := summable_inverse_totient_second_moment_of_power_bound
      (1-ε) (1-e/4) (by linarith) hbound
    have Hsf : Summable (fun n : ℕ => (gSquarefree n : ℝ)^2 *
        (n : ℝ)^(-(2*(1-e/4)))) := by
      apply Hfull.of_nonneg_of_le (fun n => by positivity)
      intro n
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _
      exact_mod_cast gSquarefree_le_g n
    exact H (1-e/4) hs hs1 ((summable_squarefree_second_moment_iff _ hs).mp Hsf)

/-- Primitive collisions with genuinely distinct inputs. -/
def Distinct := {p : Primitive // p.val.val.1 ≠ p.val.val.2}

/-- The only diagonal primitive pair. -/
def diagonal : Primitive := ⟨⟨(1, 1), squarefree_one, squarefree_one, rfl⟩, by decide⟩

lemma eq_diagonal_of_eq (p : Primitive) (h : p.val.val.1 = p.val.val.2) :
    p = diagonal := by
  have hc := p.property
  rw [h, Nat.coprime_self] at hc
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (h.trans hc) hc

lemma finite_diagonal_complement :
    ({p : Primitive | p.val.val.1 ≠ p.val.val.2}ᶜ).Finite := by
  apply (Set.finite_singleton diagonal).subset
  intro p hp
  exact eq_diagonal_of_eq p (not_not.mp hp)

/-- The one diagonal primitive pair cannot cause divergence. -/
lemma summable_primitive_iff_distinct (s : ℝ) :
    Summable (fun p : Primitive => (Nat.totient p.val.val.1 : ℝ)^(-(2*s))) ↔
      Summable (fun p : Distinct => (Nat.totient p.val.val.val.1 : ℝ)^(-(2*s))) := by
  let S : Set Primitive := {p | p.val.val.1 ≠ p.val.val.2}
  have Hc : Summable (fun p : ↑Sᶜ => (Nat.totient p.val.val.val.1 : ℝ)^(-(2*s))) := by
    letI := finite_diagonal_complement.fintype
    exact summable_of_finite_support (Set.toFinite _)
  have H := summable_subtype_and_compl
    (f := fun p : Primitive => (Nat.totient p.val.val.1 : ℝ)^(-(2*s))) (s := S)
  exact ⟨fun h => (H.mpr h).1, fun h => H.mp ⟨h, Hc⟩⟩

/-- Final exact criterion involving only distinct, coprime, squarefree
preimages. Its divergence assertion is not supplied unconditionally. -/
theorem erdos_821_iff_distinct_primitive_divergence :
    (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite) ↔
      ∀ s : ℝ, 1/2 < s → s < 1 →
        ¬Summable (fun p : Distinct => (Nat.totient p.val.val.val.1 : ℝ)^(-(2*s))) := by
  rw [erdos_821_iff_primitive_collision_divergence]
  simp only [← summable_primitive_iff_distinct]

end PrimitiveCollisions
end Erdos821
