import Submission.GraphBlockGeometryExplore
import Submission.OuterCarryProfileExplore

/-! A limitation of coordinatewise limits of the literal, unshifted digit
encoding. This does not address arbitrary sets of natural numbers. -/
namespace Erdos66LiteralTemplateLimit
open Filter Erdos66GraphBlockGeometry Erdos66IntegerBlock Erdos66CyclicThickening
  Erdos66OuterCarryProfile Erdos66OriginRepair
open scoped Classical

lemma parabola_zero_row (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p))
    (hU : ∀ u ∈ U, u ≠ 0) (x : ZMod p)
    (hx : (x,0) ∈ parabolaSet U) : x = 0 := by
  obtain ⟨u,hu,he⟩ := (Finset.mem_filter.mp hx).2
  have hz : x^2=0 := (div_eq_zero_iff.mp he.symm).resolve_right (hU u hu)
  exact eq_zero_of_pow_eq_zero hz

lemma template_small_mem (p K J : ℕ) [Fact p.Prime] [NeZero K] [NeZero J]
    (B : ℕ → Finset (ZMod p × ZMod p))
    (hB : ∀ i, B i=∅ ∨ ∃ U : Finset (ZMod p), (∀ u ∈ U, u ≠ 0) ∧ B i=parabolaSet U)
    (n : ℕ) (hn : n < p)
    (ha : n ∈ blockSet (((p*K)^2)*J)
      (fun i ↦ outerLift ((p*K)^2) J (thickenedSet p K (B i)))) : n=0 := by
  have hpK : p ≤ p*K := Nat.le_mul_of_pos_right p (NeZero.pos K)
  have hnK : n < p*K := hn.trans_le hpK
  change (n : ZMod (((p*K)^2)*J)) ∈ outerLift ((p*K)^2) J
    (thickenedSet p K (B (n/(((p*K)^2)*J)))) at ha
  rw [mem_outerLift, map_natCast, thickenedSet_nat_mem,
    Nat.div_eq_of_lt hnK, Nat.cast_zero] at ha
  rcases hB (n/(((p*K)^2)*J)) with he | ⟨U,hU,he⟩
  · simpa [he] using ha
  · rw [he] at ha
    have hz := parabola_zero_row p U hU (n : ZMod p) ha
    have hv := congrArg ZMod.val hz
    simpa only [ZMod.val_natCast_of_lt hn, ZMod.val_zero] using hv

/-- Any eventual coordinatewise limit of these unshifted templates, as the
prime tends to infinity, is supported at zero. -/
theorem limit_subset_zero (p K J : ℕ → ℕ)
    [∀ k, Fact (p k).Prime] [∀ k, NeZero (K k)] [∀ k, NeZero (J k)]
    (B : (k : ℕ) → ℕ → Finset (ZMod (p k) × ZMod (p k)))
    (hB : ∀ k i, B k i=∅ ∨ ∃ U : Finset (ZMod (p k)),
      (∀ u ∈ U, u ≠ 0) ∧ B k i=parabolaSet U)
    (hp : Tendsto p atTop atTop) (A : Set ℕ)
    (hA : ∀ n, ∀ᶠ k in atTop, n ∈ A ↔
      n ∈ blockSet (((p k*K k)^2)*J k)
        (fun i ↦ outerLift ((p k*K k)^2) (J k) (thickenedSet (p k) (K k) (B k i)))) :
    A ⊆ {0} := by
  intro n hn
  have he : ∀ᶠ k : ℕ in atTop, n=0 := by
    filter_upwards [hA n,hp.eventually_gt_atTop n] with k hk hpk
    exact template_small_mem (p k) (K k) (J k) (B k) (hB k) n hpk (hk.mp hn)
  exact he.exists.choose_spec

end Erdos66LiteralTemplateLimit
