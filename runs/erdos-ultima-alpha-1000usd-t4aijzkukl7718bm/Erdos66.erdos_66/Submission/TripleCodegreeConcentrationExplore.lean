import Submission.TripleCodegreeMeanExplore

/-! Uniform codegree concentration with an explicit potential that can be
combined with the signed and unsigned representation tests. -/
namespace Erdos66TripleCodegreeConcentration
open Erdos66TripleCodegreeGeometry Erdos66TripleCodegreeMean Erdos66FiniteBernoulli
  Erdos66BernoulliMatching Erdos66RandomConstantProfile Erdos66SignedRepBernoulli
  Erdos66ExceptionalPairDeletion
open scoped Classical
set_option maxHeartbeats 1800000

lemma shifted_codegree_mgf (μ : ℝ) (s L b q : ℕ) (hμ : 0 ≤ μ)
    (hs : μ ≤ (s : ℝ)+1) (hbq : b≠q) (t : ℝ) (ht : 0 ≤ t) :
    expect (probability μ s L) (fun ω ↦ Real.exp (t*(codegree (selectedFinset L ω) b q : ℝ))) ≤
      Real.exp (2*t+(Real.exp (9*t)-1)*(μ*Real.sqrt μ*Erdos66ConstantProfile.b s)) := by
  have hp := probability_bounds μ s L hμ hs
  have hcmp (ω : Fin (L+1) → Bool) :
      Real.exp (t*(codegree (selectedFinset L ω) b q : ℝ)) ≤
        Real.exp (2*t)*Real.exp (t*(realized (tripleEvents L b q) tripleSupport ω).card) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hc : (codegree (selectedFinset L ω) b q : ℝ) ≤
        (realized (tripleEvents L b q) tripleSupport ω).card+2 := by
      exact_mod_cast codegree_le_realized_add_two L b q hbq ω
    nlinarith
  have hmgf := expect_exp_realized_le (probability μ s L) hp (tripleEvents L b q) tripleSupport 9
    (fun x _ ↦ tripleSupport_nonempty x) (fun x _ ↦ conflict_card_le_nine L b q x) t ht
  have hm := shifted_triple_mass μ s L b q hμ
  have hex : 0 ≤ Real.exp (9*t)-1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  calc
    _ ≤ expect (probability μ s L) (fun ω ↦
        Real.exp (2*t)*Real.exp (t*(realized (tripleEvents L b q) tripleSupport ω).card)) :=
      expect_mono _ hp _ _ hcmp
    _ = Real.exp (2*t)*expect (probability μ s L)
        (fun ω ↦ Real.exp (t*(realized (tripleEvents L b q) tripleSupport ω).card)) := expect_const_mul _ _ _
    _ ≤ Real.exp (2*t)*Real.exp ((Real.exp (9*t)-1)*
        (∑ x∈tripleEvents L b q, ∏ i∈tripleSupport x, probability μ s L i)) := by
      exact mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ ≤ Real.exp (2*t)*Real.exp ((Real.exp (9*t)-1)*(μ*Real.sqrt μ*Erdos66ConstantProfile.b s)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hm hex)) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

noncomputable def targetPairs (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (Q+1)) ×ˢ (Finset.range (Q+1))).filter (fun x ↦ x.1≠x.2)

lemma mem_targetPairs {Q : ℕ} {x : ℕ × ℕ} :
    x∈targetPairs Q ↔ x.1 ≤ Q ∧ x.2 ≤ Q ∧ x.1≠x.2 := by
  simp only [targetPairs,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
  omega

lemma targetPairs_card (Q : ℕ) : (targetPairs Q).card ≤ (Q+1)^2 := by
  have hh := Finset.card_le_card (Finset.filter_subset (fun x : ℕ × ℕ ↦ x.1≠x.2)
    ((Finset.range (Q+1)) ×ˢ (Finset.range (Q+1))))
  simpa only [Finset.card_product,Finset.card_range,pow_two,targetPairs] using hh

noncomputable def codegreePotential (L Q R : ℕ) (t : ℝ) (ω : Fin (L+1) → Bool) : ℝ :=
  ∑ x∈targetPairs Q, Real.exp (t*((codegree (selectedFinset L ω) x.1 x.2 : ℝ)-R))

lemma codegreePotential_nonneg (L Q R : ℕ) (t : ℝ) (ω : Fin (L+1) → Bool) :
    0 ≤ codegreePotential L Q R t ω := Finset.sum_nonneg (fun _ _ ↦ (Real.exp_pos _).le)

lemma expect_codegreePotential (μ : ℝ) (s L Q R : ℕ) (hμ : 0 ≤ μ)
    (hs : μ ≤ (s : ℝ)+1) (t : ℝ) (ht : 0 ≤ t) :
    expect (probability μ s L) (codegreePotential L Q R t) ≤
      ((Q : ℝ)+1)^2 * Real.exp ((2-(R : ℝ))*t+
        (Real.exp (9*t)-1)*(μ*Real.sqrt μ*Erdos66ConstantProfile.b s)) := by
  unfold codegreePotential
  rw [expect_sum]
  have he (x : ℕ × ℕ) (hx : x∈targetPairs Q) :
      expect (probability μ s L) (fun ω ↦
        Real.exp (t*((codegree (selectedFinset L ω) x.1 x.2 : ℝ)-R))) ≤
        Real.exp ((2-(R : ℝ))*t+(Real.exp (9*t)-1)*(μ*Real.sqrt μ*Erdos66ConstantProfile.b s)) := by
    have hsplit (ω : Fin (L+1) → Bool) :
        Real.exp (t*((codegree (selectedFinset L ω) x.1 x.2 : ℝ)-R)) =
          Real.exp (-t*R)*Real.exp (t*(codegree (selectedFinset L ω) x.1 x.2 : ℝ)) := by
      rw [←Real.exp_add]; congr 1; ring
    simp_rw [hsplit]
    rw [expect_const_mul]
    have hh := mul_le_mul_of_nonneg_left
      (shifted_codegree_mgf μ s L x.1 x.2 hμ hs (mem_targetPairs.mp hx).2.2 t ht) (Real.exp_pos (-t*R)).le
    convert hh using 1
    rw [←Real.exp_add]; congr 1; ring
  have hh := Finset.sum_le_sum he
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  have hc : ((targetPairs Q).card : ℝ) ≤ ((Q : ℝ)+1)^2 := by exact_mod_cast targetPairs_card Q
  exact hh.trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le)

lemma codegrees_of_potential_lt (L Q R : ℕ) (t : ℝ) (ht : 0<t) (ω : Fin (L+1) → Bool)
    (hω : codegreePotential L Q R t ω < 1) :
    ∀ b ≤ Q, ∀ q ≤ Q, b≠q → codegree (selectedFinset L ω) b q ≤ R := by
  intro b hb q hq hbq
  have he : Real.exp (t*((codegree (selectedFinset L ω) b q : ℝ)-R)) ≤ codegreePotential L Q R t ω :=
    Finset.single_le_sum (a := (b,q)) (f := fun x : ℕ × ℕ ↦ Real.exp (t*((codegree (selectedFinset L ω) x.1 x.2 : ℝ)-R)))
      (fun _ _ ↦ (Real.exp_pos _).le) (mem_targetPairs.mpr (show (b,q).1 ≤ Q ∧ (b,q).2 ≤ Q ∧ (b,q).1≠(b,q).2 from ⟨hb,hq,hbq⟩))
  have hh := Real.exp_lt_one_iff.mp (he.trans_lt hω)
  have hc : (codegree (selectedFinset L ω) b q : ℝ) ≤ R := by nlinarith
  exact_mod_cast hc

/-- One realization simultaneously satisfies the signed, unsigned, and
all off-diagonal codegree tests. -/
theorem exists_unsigned_signed_codegree (L Q R s : ℕ) (μ δ t : ℝ)
    (hμ : 0 ≤ μ) (hs : μ ≤ (s : ℝ)+1) (hδ : 0<δ) (hδ1 : δ ≤ 1) (ht : 0<t)
    (σ : ℕ → ℝ) (hσ : ∀ i, |σ i| ≤ 1)
    (hsmall : 6*((Q : ℝ)+1)*Real.exp (-δ^2*(μ+1)/8) +
      ((Q : ℝ)+1)^2*Real.exp ((2-(R : ℝ))*t+
        (Real.exp (9*t)-1)*(μ*Real.sqrt μ*Erdos66ConstantProfile.b s)) < 1) :
    ∃ ω : Fin (L+1) → Bool,
      (∀ q ≤ Q, |(AdditiveCombinatorics.sumRep (Erdos66FiniteRepBernoulli.selected L ω) q : ℝ)-
        Erdos66FiniteRepBernoulli.repMean L q (probability μ s L)| < δ*(μ+1) ∧
        |signedRep L q σ ω-signedMean L q σ (probability μ s L)| < 2*δ*(μ+1)) ∧
      ∀ b ≤ Q, ∀ q ≤ Q, b≠q → codegree (selectedFinset L ω) b q ≤ R := by
  have hbudget : 6*((Q : ℝ)+1)*Real.exp (-δ^2*(μ+1)/8) +
      expect (probability μ s L) (codegreePotential L Q R t) < 1 := by
    have hh := expect_codegreePotential μ s L Q R hμ hs t ht.le
    linarith
  obtain ⟨ω,hω,hc⟩ := exists_unsigned_signed_bound_with_potential L Q σ hσ (probability μ s L)
    (probability_bounds μ s L hμ hs) (μ+1) δ (by linarith) hδ hδ1
    (fun q _ ↦ mean_upper μ s L q hμ hs) (codegreePotential L Q R t)
    (codegreePotential_nonneg L Q R t) hbudget
  exact ⟨ω,hω,codegrees_of_potential_lt L Q R t ht ω hc⟩

end Erdos66TripleCodegreeConcentration
