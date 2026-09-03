import Submission.RationalCurveLocal
import Submission.RepeatedCubeDifferences

/-!
A limitation of uniform oriented-score constructions. This does not rule out
squarefree score constructions, general colorings, or the conjectured set.
-/
namespace Erdos1206.OrientedScoreObstruction
open scoped Classical
set_option maxHeartbeats 1000000

/-- A rational representation can be inserted strictly between two nested
positive representations of the same cube sum. -/
lemma insert_representation {a b c d : ℚ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∃ u v : ℚ, a < u ∧ u < b ∧ c < v ∧ v < d ∧
      a^3+d^3=u^3+v^3 := by
  have had : a < d := hab.trans (hbc.trans hcd)
  have hd : 0 < d := ha.trans had
  have hD : 0 < a^3+d^3 := by positivity
  have hbase : d^3-(-a)^3=a^3+d^3 := by ring
  have heps : 0 < min (b-a) (d-c) := lt_min (sub_pos.mpr hab) (sub_pos.mpr hcd)
  obtain ⟨x,y,hyL,hyU,hxL,hxU,he⟩ :=
    RationalCurveLocal.near_below_of_unbounded hD hd.ne' hbase heps
      (RationalCurveLocal.sum_unbounded ha had)
  refine ⟨-y,x,by linarith,?_,?_,hxU,by nlinarith⟩
  · have hh := min_le_left (b-a) (d-c)
    linarith
  · have hh := min_le_right (b-a) (d-c)
    linarith

/-- Even an arbitrary real score on positive rationals cannot have a uniform
positive oriented contrast on every strict cubic collision. -/
theorem no_rational_uniform_gap (g : ℚ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ¬ (∀ a b c d : ℚ, 0 < a → a < b → b < c → c < d →
      a^3+d^3=b^3+c^3 → ε ≤ g b+g c-g a-g d) := by
  intro hgap
  have hmany : ∀ n : ℕ, ∀ a b c d : ℚ, 0 < a → a < b → b < c → c < d →
      a^3+d^3=b^3+c^3 → (n : ℝ)*ε ≤ g b+g c-g a-g d := by
    intro n
    induction n with
    | zero =>
        intro a b c d ha hab hbc hcd he
        simpa using hε.le.trans (hgap a b c d ha hab hbc hcd he)
    | succ n ih =>
        intro a b c d ha hab hbc hcd he
        obtain ⟨u,v,hau,hub,hcv,hvd,huv⟩ := insert_representation ha hab hbc hcd
        have h₁ := ih a u v d ha hau (hub.trans (hbc.trans hcv)) hvd huv
        have h₂ := hgap u b c v (ha.trans hau) hub hbc hcv (huv.symm.trans he)
        push_cast
        nlinarith
  obtain ⟨n,hn⟩ := exists_nat_gt ((g 9+g 10-g 1-g 12)/ε)
  have hh := hmany n 1 9 10 12 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hlt := (div_lt_iff₀ hε).mp hn
  linarith

/-- Extension of a completely additive score to positive rational arguments.
Values at nonpositive rationals are irrelevant. -/
def rationalScore (f : ℕ → ℝ) (q : ℚ) : ℝ :=
  f q.num.toNat-f q.den

lemma score_of_denominator (f : ℕ → ℝ)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → f (a*b)=f a+f b)
    {q : ℚ} (hq : 0 < q) {D t : ℕ} (hD : 0 < D) (ht : 0 < t)
    (he : (t : ℚ)=(D : ℚ)*q) :
    f t=f D+rationalScore f q := by
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hnat : 0 < q.num.toNat := by omega
  have hn : (q.num.toNat : ℚ)=q.num := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have heq : t*q.den=D*q.num.toNat := by
    have hh : (t : ℚ)*q.den=(D : ℚ)*q.num.toNat := by
      rw [he,hn]
      calc
        (D : ℚ)*q*q.den=(D : ℚ)*(q.den*q) := by ring
        _ = (D : ℚ)*q.num := by rw [Rat.den_mul_eq_num]
    exact_mod_cast hh
  have hh := congrArg f heq
  rw [hmul t q.den ht (Rat.den_pos q),hmul D q.num.toNat hD hnat] at hh
  dsimp only [rationalScore]
  linarith

/-- Clearing denominators preserves oriented score contrasts. -/
lemma rational_gap_of_natural (f : ℕ → ℝ)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → f (a*b)=f a+f b)
    {ε : ℝ}
    (hgap : ∀ a b c d : ℕ, 0 < a → a < b → b < c → c < d →
      a^3+d^3=b^3+c^3 → ε ≤ f b+f c-f a-f d) :
    ∀ a b c d : ℚ, 0 < a → a < b → b < c → c < d →
      a^3+d^3=b^3+c^3 →
      ε ≤ rationalScore f b+rationalScore f c-rationalScore f a-rationalScore f d := by
  intro a b c d ha hab hbc hcd he
  let r : Fin 4 → ℚ := ![a,b,c,d]
  have hr : ∀ i, 0 < r i := by
    intro i
    fin_cases i
    · exact ha
    · exact ha.trans hab
    · exact ha.trans (hab.trans hbc)
    · exact ha.trans (hab.trans (hbc.trans hcd))
  obtain ⟨D,hD,t,ht,hcast⟩ := RepeatedCubeDifferences.common_positive_denominator r hr
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hlt (i j : Fin 4) (h : r i < r j) : t i < t j := by
    have hh : (t i : ℚ) < t j := by
      rw [hcast,hcast]
      exact mul_lt_mul_of_pos_left h hDQ
    exact_mod_cast hh
  have hid : (t 0)^3+(t 3)^3=(t 1)^3+(t 2)^3 := by
    have hh : (t 0 : ℚ)^3+(t 3 : ℚ)^3=(t 1 : ℚ)^3+(t 2 : ℚ)^3 := by
      rw [hcast,hcast,hcast,hcast]
      change ((D : ℚ)*a)^3+((D : ℚ)*d)^3=((D : ℚ)*b)^3+((D : ℚ)*c)^3
      linear_combination (D : ℚ)^3*he
    exact_mod_cast hh
  have hscore (i : Fin 4) := score_of_denominator f hmul (hr i) hD (ht i) (hcast i)
  have hh := hgap (t 0) (t 1) (t 2) (t 3) (ht 0)
    (hlt 0 1 hab) (hlt 1 2 hbc) (hlt 2 3 hcd) hid
  rw [hscore,hscore,hscore,hscore] at hh
  change ε ≤ (f D+rationalScore f b)+(f D+rationalScore f c)-
    (f D+rationalScore f a)-(f D+rationalScore f d) at hh
  linarith

/-- No completely additive real score has a uniform positive oriented gap
on all positive integer cube collisions. Squarefree-only hypotheses are not
covered, since clearing denominators does not preserve squarefreeness. -/
theorem no_completely_additive_uniform_gap (f : ℕ → ℝ)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → f (a*b)=f a+f b)
    {ε : ℝ} (hε : 0 < ε) :
    ¬ (∀ a b c d : ℕ, 0 < a → a < b → b < c → c < d →
      a^3+d^3=b^3+c^3 → ε ≤ f b+f c-f a-f d) := by
  intro hgap
  exact no_rational_uniform_gap (rationalScore f) hε
    (rational_gap_of_natural f hmul hgap)

#print axioms no_rational_uniform_gap
#print axioms no_completely_additive_uniform_gap
end Erdos1206.OrientedScoreObstruction
