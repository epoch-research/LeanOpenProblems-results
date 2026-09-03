import Submission.PrimeCoverNecessity

/-!
A necessary prime-cover condition for a cube-Sidon source containing a fixed
small-score band on the primes. This does not assume divisor closure.
No such prime cover or cube-Sidon source is constructed.
-/
namespace Erdos1206.ScorePrimeCover
open scoped Classical
set_option maxHeartbeats 1000000

/-- A fixed positive threshold has reciprocally summable prime outliers
whenever the score has finite reciprocal-prime square energy. -/
theorem summable_prime_outliers (f : ℕ → ℝ) {t : ℝ} (ht : 0 < t)
    (hs : Summable (fun p : ℕ => if p.Prime then (f p)^2/p else 0)) :
    Summable (fun p : ℕ => if p.Prime ∧ t ≤ |f p| then (1:ℝ)/p else 0) := by
  apply Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity)
    (fun p => ?_) (hs.mul_left (1/t^2))
  by_cases hp : p.Prime ∧ t ≤ |f p|
  · simp only [if_pos hp,if_pos hp.1]
    have hsq : t^2 ≤ (f p)^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ ht.le (abs_nonneg (f p))).mpr hp.2
    have ht2 : 0 < t^2 := sq_pos_of_pos ht
    have hone : (1:ℝ) ≤ (f p)^2/t^2 := (le_div_iff₀ ht2).mpr (by simpa using hsq)
    have hh := div_le_div_of_nonneg_right hone (Nat.cast_nonneg p)
    convert hh using 1
    ring
  · rw [if_neg hp]
    split_ifs <;> positivity

/-- A Sidon source containing every low-score prime forces a summable cover
of all prime-root cube collisions. Unlike the divisor-closed criterion, this
uses no divisor closure or density assumption on the source. -/
theorem summable_prime_cover_of_score_band {A : Set ℕ} (f : ℕ → ℝ)
    {t : ℝ} (ht : 0 < t)
    (henergy : Summable (fun p : ℕ => if p.Prime then (f p)^2/p else 0))
    (hinclude : ∀ p : ℕ, p.Prime → |f p| < t → p ∈ A)
    (hsidon : IsSidon ((fun n : ℕ => n^3) '' A)) :
    ∃ P : Set ℕ, (∀ p ∈ P, p.Prime) ∧ IsPrimeCubeCover P ∧
      Summable (fun p : ℕ => if p ∈ P then (1:ℝ)/p else 0) := by
  let P : Set ℕ := {p | p.Prime ∧ t ≤ |f p|}
  have hexcluded : {p : ℕ | p.Prime ∧ p ∉ A} ⊆ P := by
    rintro p ⟨hp,hpA⟩
    exact ⟨hp,le_of_not_gt (fun h => hpA (hinclude p hp h))⟩
  refine ⟨P,fun _ hp => hp.1,?_,?_⟩
  swap
  · apply (summable_prime_outliers f ht henergy).congr
    intro p
    by_cases hp : p.Prime ∧ t ≤ |f p| <;> simp [P,hp]
  intro a b c d ha hb hc hd he hac had
  rcases prime_cover_of_cube_sidon hsidon a b c d ha hb hc hd he hac had with h | h | h | h
  · exact Or.inl (hexcluded h)
  · exact Or.inr (Or.inl (hexcluded h))
  · exact Or.inr (Or.inr (Or.inl (hexcluded h)))
  · exact Or.inr (Or.inr (Or.inr (hexcluded h)))

/-- Even if the band excludes the primes themselves, any one point strictly
inside a nonempty additive-score band transports small-score primes into it.
Finite reciprocal-prime energy therefore still forces a summable prime cover.
This statement concerns a fixed open band, not arbitrary moving centers. -/
theorem summable_prime_cover_of_nonempty_additive_band (f : ℕ → ℝ)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → f (a*b)=f a+f b)
    (henergy : Summable (fun p : ℕ => if p.Prime then (f p)^2/p else 0))
    (μ t : ℝ) (q : ℕ) (hqsf : Squarefree q) (hqband : |f q-μ| < t)
    (hsidon : IsSidon ((fun n : ℕ => n^3) '' {n | Squarefree n ∧ |f n-μ| < t})) :
    ∃ P : Set ℕ, (∀ p ∈ P, p.Prime) ∧ IsPrimeCubeCover P ∧
      Summable (fun p : ℕ => if p ∈ P then (1:ℝ)/p else 0) := by
  have hq : 0 < q := Nat.pos_of_ne_zero hqsf.ne_zero
  let ε := t-|f q-μ|
  have hε : 0 < ε := sub_pos.mpr hqband
  let g : ℕ → ℝ := fun p => if p ∣ q then ε else f p
  have hgenergy : Summable (fun p : ℕ => if p.Prime then (g p)^2/p else 0) := by
    apply henergy.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [Filter.eventually_gt_atTop q] with p hp
    have hnd : ¬ p ∣ q := by
      intro hd
      exact (not_le_of_gt hp) (Nat.le_of_dvd hq hd)
    simp only [g,if_neg hnd]
  let B : Set ℕ := {n | Squarefree (q*n) ∧ |f (q*n)-μ| < t}
  have hB : IsSidon ((fun n : ℕ => n^3) '' B) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ _ ⟨c,hc,rfl⟩ _ ⟨d,hd,rfl⟩ he
    have he' : (q*a)^3+(q*c)^3=(q*b)^3+(q*d)^3 := by
      simpa only [mul_pow,←mul_add] using congrArg (fun n : ℕ => q^3*n) he
    have hh := hsidon _ ⟨q*a,ha,rfl⟩ _ ⟨q*b,hb,rfl⟩
      _ ⟨q*c,hc,rfl⟩ _ ⟨q*d,hd,rfl⟩ he'
    simp only [mul_pow] at hh
    have hq3 : 0 < q^3 := pow_pos hq _
    rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨Nat.eq_of_mul_eq_mul_left hq3 h₁,Nat.eq_of_mul_eq_mul_left hq3 h₂⟩
    · exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left hq3 h₁,Nat.eq_of_mul_eq_mul_left hq3 h₂⟩
  apply summable_prime_cover_of_score_band g hε hgenergy _ hB
  intro p hp hgp
  have hnd : ¬ p ∣ q := by
    intro hd
    have hh : |ε| < ε := by simpa only [g,if_pos hd] using hgp
    rw [abs_of_pos hε] at hh
    exact (lt_irrefl ε) hh
  have hfp : |f p| < ε := by simpa only [g,if_neg hnd] using hgp
  refine ⟨(Nat.squarefree_mul (hp.coprime_iff_not_dvd.mpr hnd).symm).mpr
    ⟨hqsf,hp.squarefree⟩,?_⟩
  calc
    |f (q*p)-μ| = |(f q-μ)+f p| := by rw [hmul q p hq hp.pos]; congr 1; ring
    _ ≤ |f q-μ|+|f p| := abs_add_le _ _
    _ < |f q-μ|+ε := by linarith
    _ = t := by dsimp only [ε]; ring

#print axioms summable_prime_cover_of_nonempty_additive_band


#print axioms summable_prime_outliers
#print axioms summable_prime_cover_of_score_band
end Erdos1206.ScorePrimeCover
