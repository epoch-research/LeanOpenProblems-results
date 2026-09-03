import Submission.Exploration

/-!
# Closed exceptional sets for the prime-pair problem

These are auxiliary results, not a proof or a disproof of Erdős 972.
- Each slope greater than one has at most one prime-pair endpoint.
- Apart from these endpoints, successful pairs are an open condition.
- Slopes with finitely many successful primes form a countable union of
  closed exceptional sets, relative to the interval `(1, ∞)`.
- A counterexample is equivalent to a bounded sequence of rational finite-window
  gap witnesses eventually staying a fixed positive distance from each rational.
  No sequence satisfying this criterion has been constructed.
-/

namespace Explore972

/-- Successful pairs at the left endpoint of a floor interval. -/
def endpointPrimeSet (α : ℝ) : Set ℕ :=
  {p | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ α * p = q}

/-- Successful pairs strictly inside a floor interval. -/
def strictPrimeSet (α : ℝ) : Set ℕ :=
  {p | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ (q : ℝ) < α * p ∧ α * p < q + 1}

lemma endpointPrimeSet_subsingleton {α : ℝ} (hα : 1 < α) :
    (endpointPrimeSet α).Subsingleton := by
  rintro p ⟨hp, q, hq, hpq⟩ r ⟨hr, s, hs, hrs⟩
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpq_lt : p < q := by
    exact_mod_cast (show (p : ℝ) < q by nlinarith)
  have hcrossR : (q : ℝ) * r = (s : ℝ) * p := by
    rw [← hpq, ← hrs]
    ring
  have hcross : q * r = s * p := by exact_mod_cast hcrossR
  have hdiv : p ∣ q * r := by
    rw [hcross]
    exact dvd_mul_left p s
  rcases hp.dvd_mul.mp hdiv with hdiv | hdiv
  · have heq := (Nat.prime_dvd_prime_iff_eq hp hq).mp hdiv
    omega
  · exact (Nat.prime_dvd_prime_iff_eq hp hr).mp hdiv

lemma endpointPrimeSet_finite {α : ℝ} (hα : 1 < α) :
    (endpointPrimeSet α).Finite := (endpointPrimeSet_subsingleton hα).finite

lemma primeSet_eq_strict_union_endpoint {α : ℝ} (hα : 1 < α) :
    primeSet α = strictPrimeSet α ∪ endpointPrimeSet α := by
  ext p
  constructor
  · rintro ⟨hp, hq⟩
    have hlo := Nat.floor_le (mul_nonneg (by linarith : 0 ≤ α) (Nat.cast_nonneg p))
    rcases hlo.lt_or_eq with hlo | hlo
    · exact Or.inl ⟨hp, _, hq, hlo, Nat.lt_floor_add_one _⟩
    · exact Or.inr ⟨hp, _, hq, hlo.symm⟩
  · rintro (⟨hp, q, hq, hlo, hhi⟩ | ⟨hp, q, hq, heq⟩)
    · refine ⟨hp, ?_⟩
      have hf := (Nat.floor_eq_iff' hq.ne_zero).mpr ⟨hlo.le, hhi⟩
      rwa [hf]
    · refine ⟨hp, ?_⟩
      rwa [heq, Nat.floor_natCast]

/-- A closed set excluding all strict prime-pair witnesses beyond `N`. -/
def tailExceptional (N : ℕ) : Set ℝ :=
  (⋃ (p : ℕ) (_ : N < p) (_ : p.Prime) (q : ℕ) (_ : q.Prime),
    {α : ℝ | (q : ℝ) < α * p ∧ α * p < q + 1})ᶜ

lemma isClosed_tailExceptional (N : ℕ) : IsClosed (tailExceptional N) := by
  apply IsOpen.isClosed_compl
  apply isOpen_iUnion
  intro p
  apply isOpen_iUnion
  intro _
  apply isOpen_iUnion
  intro _
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro _
  exact (isOpen_lt continuous_const (continuous_id.mul continuous_const)).inter
    (isOpen_lt (continuous_id.mul continuous_const) continuous_const)

lemma mem_tailExceptional {α : ℝ} {N : ℕ} :
    α ∈ tailExceptional N ↔ ∀ p : ℕ, N < p → p ∉ strictPrimeSet α := by
  simp only [tailExceptional, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq,
    strictPrimeSet]
  aesop

/-- The endpoint issue costs at most one successful prime, so irrationality
is not needed for this finite-set characterization. -/
theorem finite_primeSet_iff_mem_tailExceptional {α : ℝ} (hα : 1 < α) :
    (primeSet α).Finite ↔ ∃ N : ℕ, α ∈ tailExceptional N := by
  rw [primeSet_eq_strict_union_endpoint hα, Set.finite_union]
  constructor
  · rintro ⟨hf, _⟩
    obtain ⟨N, hN⟩ := hf.bddAbove
    refine ⟨N, mem_tailExceptional.mpr ?_⟩
    intro p hNp hp
    exact (not_le_of_gt hNp) (hN hp)
  · rintro ⟨N, hN⟩
    refine ⟨(Set.finite_Iic N).subset ?_, endpointPrimeSet_finite hα⟩
    intro p hp
    exact le_of_not_gt (fun hNp => mem_tailExceptional.mp hN p hNp hp)

open Filter in
open scoped Topology in
/-- A uniformly bounded prime-free tail in finite windows remains finite at
any limit greater than one, whether that limit is rational or irrational. -/
theorem finite_primeSet_of_limit {α : ℝ} {a : ℕ → ℝ}
    (hα : 1 < α) (hlim : Tendsto a atTop (𝓝 α))
    (B : ℕ) (hgap : ∀ n p : ℕ, B < p → p ≤ n → p ∉ primeSet (a n)) :
    (primeSet α).Finite := by
  apply (finite_primeSet_iff_mem_tailExceptional hα).mpr
  refine ⟨B, mem_tailExceptional.mpr ?_⟩
  rintro p hBp ⟨hp, q, hq, hlo, hhi⟩
  have ht := hlim.mul_const (p : ℝ)
  obtain ⟨n, hnlo, hnhi, hpn⟩ :=
    ((ht.eventually_const_lt hlo).and
      ((ht.eventually_lt_const hhi).and (eventually_ge_atTop p))).exists
  apply hgap n p hBp hpn
  refine ⟨hp, ?_⟩
  have hf := (Nat.floor_eq_iff' hq.ne_zero).mpr ⟨hnlo.le, hnhi⟩
  rwa [hf]


/-- An explicit countable closed-set description of finite-pair slopes,
relative to the domain `α > 1`. -/
theorem finite_slopes_eq_union_closed :
    {α : ℝ | 1 < α ∧ (primeSet α).Finite} =
      Set.Ioi 1 ∩ ⋃ N : ℕ, tailExceptional N := by
  ext α
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion]
  constructor
  · rintro ⟨hα, hf⟩
    exact ⟨hα, (finite_primeSet_iff_mem_tailExceptional hα).mp hf⟩
  · rintro ⟨hα, hf⟩
    exact ⟨hα, (finite_primeSet_iff_mem_tailExceptional hα).mpr hf⟩

lemma isOpen_strict_success (p : ℕ) :
    IsOpen {α : ℝ | p ∈ strictPrimeSet α} := by
  have heq : {α : ℝ | p ∈ strictPrimeSet α} =
      ⋃ (_ : p.Prime) (q : ℕ) (_ : q.Prime),
        {α : ℝ | (q : ℝ) < α * p ∧ α * p < q + 1} := by
    ext α
    simp only [strictPrimeSet, Set.mem_setOf_eq, Set.mem_iUnion]
    aesop
  rw [heq]
  apply isOpen_iUnion
  intro _
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro _
  exact (isOpen_lt continuous_const (continuous_id.mul continuous_const)).inter
    (isOpen_lt (continuous_id.mul continuous_const) continuous_const)

/-- Pointwise infinitude on a compact set gives a uniform bound for the next
successful prime. This theorem does not assume irrationality. -/
theorem compact_uniform_prime_bound {K : Set ℝ} (hK : IsCompact K)
    (hpos : ∀ α ∈ K, 1 < α)
    (hinf : ∀ α ∈ K, (primeSet α).Infinite) (N : ℕ) :
    ∃ P : ℕ, ∀ α ∈ K, ∃ p : ℕ,
      N < p ∧ p ≤ P ∧ p ∈ primeSet α := by
  classical
  let U : ℕ → Set ℝ := fun p => if N < p then {α | p ∈ strictPrimeSet α} else ∅
  have hU : ∀ p, IsOpen (U p) := by
    intro p
    dsimp [U]
    split_ifs
    · exact isOpen_strict_success p
    · exact isOpen_empty
  have hcover : K ⊆ ⋃ p, U p := by
    intro α hα
    have hi := hinf α hα
    rw [primeSet_eq_strict_union_endpoint (hpos α hα), Set.infinite_union] at hi
    have hi' := hi.resolve_right (endpointPrimeSet_finite (hpos α hα)).not_infinite
    obtain ⟨p, hp, hNp⟩ := hi'.exists_gt N
    exact Set.mem_iUnion.mpr ⟨p, by simpa [U, hNp] using hp⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU hcover
  refine ⟨s.sup id, ?_⟩
  intro α hα
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hs hα)
  obtain ⟨hps, hpU⟩ := Set.mem_iUnion.mp hp
  have hNp : N < p := by
    by_contra h
    simp [U, h] at hpU
  have hpstrict : p ∈ strictPrimeSet α := by simpa [U, hNp] using hpU
  refine ⟨p, hNp, Finset.le_sup (f := id) hps, ?_⟩
  rw [primeSet_eq_strict_union_endpoint (hpos α hα)]
  exact Or.inl hpstrict

/-- Compactness would turn finite-window gaps into an irrational counterexample
if all the witnesses stayed in one compact set containing only admissible
irrational slopes. No such compact set is constructed here. -/
theorem compact_counterexample_criterion {K : Set ℝ} (hK : IsCompact K)
    (hKirr : ∀ α ∈ K, 1 < α ∧ Irrational α)
    (B : ℕ) (hgap : ∀ P : ℕ, ∃ α ∈ K, ∀ p : ℕ,
      B < p → p ≤ P → p ∉ primeSet α) :
    ¬ ∀ α > 1, Irrational α → (primeSet α).Infinite := by
  intro h
  obtain ⟨P, hP⟩ := compact_uniform_prime_bound hK
    (fun α hα => (hKirr α hα).1)
    (fun α hα => h α (hKirr α hα).1 (hKirr α hα).2) B
  obtain ⟨α, hα, hαgap⟩ := hgap P
  obtain ⟨p, hBp, hpP, hp⟩ := hP α hα
  exact hαgap p hBp hpP hp


open Filter in
open scoped Topology in
/-- Eventual positive separation from every rational is preserved in a limit.
The separation may depend on the rational, but not on the sequence index. -/
theorem irrational_of_tendsto_separated {a : ℕ → ℝ} {α : ℝ}
    (hlim : Tendsto a atTop (𝓝 α))
    (hsep : ∀ q : ℚ, ∃ δ > 0, ∀ᶠ n in atTop, δ ≤ dist (a n) (q : ℝ)) :
    Irrational α := by
  rintro ⟨q, hq⟩
  obtain ⟨δ, hδ, hsep⟩ := hsep q
  have hle : δ ≤ dist α (q : ℝ) :=
    ge_of_tendsto (hlim.dist tendsto_const_nhds) hsep
  rw [hq, dist_self] at hle
  exact (not_le_of_gt hδ) hle

open Filter in
open scoped Topology in
/-- A bounded finite-window gap sequence gives a counterexample if it stays
uniformly away from each rational eventually. The sequence need not converge:
a convergent subsequence suffices. This is a criterion, not a construction. -/
theorem separated_gap_sequence_counterexample {a : ℕ → ℝ} {L U : ℝ}
    (hL : 1 < L) (hbdd : ∀ n, a n ∈ Set.Icc L U)
    (hsep : ∀ q : ℚ, ∃ δ > 0, ∀ᶠ n in atTop, δ ≤ dist (a n) (q : ℝ))
    (B : ℕ) (hgap : ∀ n p : ℕ, B < p → p ≤ n → p ∉ primeSet (a n)) :
    ¬ ∀ α > 1, Irrational α → (primeSet α).Infinite := by
  obtain ⟨α, hα, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hbdd
  have hi : Irrational α := irrational_of_tendsto_separated hlim (by
    intro q
    obtain ⟨δ, hδ, hsep⟩ := hsep q
    exact ⟨δ, hδ, hφ.tendsto_atTop.eventually hsep⟩)
  have hα1 : 1 < α := hL.trans_le hα.1
  have hf : (primeSet α).Finite := finite_primeSet_of_limit hα1 hlim B (by
    intro n p hBp hpn
    exact hgap (φ n) p hBp (hpn.trans (hφ.id_le n)))
  intro h
  exact hf.not_infinite (h α hα1 hi)

open Filter in
open scoped Topology in
/-- The rational-separation criterion is also necessary. In particular, just
having irrational finite-window witnesses, without uniform separation, is not
a replacement for this condition. -/
theorem negation_iff_separated_gap_sequence :
    (¬ ∀ α > 1, Irrational α → (primeSet α).Infinite) ↔
      ∃ (a : ℕ → ℝ) (L U : ℝ), 1 < L ∧
        (∀ n, a n ∈ Set.Icc L U) ∧
        (∀ q : ℚ, ∃ δ > 0, ∀ᶠ n in atTop, δ ≤ dist (a n) (q : ℝ)) ∧
        ∃ B : ℕ, ∀ n p : ℕ, B < p → p ≤ n → p ∉ primeSet (a n) := by
  constructor
  · intro h
    obtain ⟨α, hα, hi, B, hB⟩ := negation_iff_bounded_counterexample.mp h
    refine ⟨fun _ => α, α, α, hα, fun _ => ⟨le_rfl, le_rfl⟩, ?_, B, ?_⟩
    · intro q
      exact ⟨dist α (q : ℝ), dist_pos.mpr (hi.ne_rat q),
        Eventually.of_forall (fun _ => le_rfl)⟩
    · rintro n p hBp _ ⟨hp, hq⟩
      exact hB p hBp hp hq
  · rintro ⟨a, L, U, hL, hbdd, hsep, B, hgap⟩
    exact separated_gap_sequence_counterexample hL hbdd hsep B hgap

open Filter in
open scoped Topology in
/-- A rational slope can match any finite list of the floor values at an
irrational slope. This gives finite rational certificates, not an infinite
prime-free tail at one rational slope. -/
theorem exists_rat_finite_floor_agreement {α : ℝ} (hα : 1 < α)
    (hi : Irrational α) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℚ, dist (r : ℝ) α < ε ∧ ∀ p : ℕ, p ≤ N → p.Prime →
      ⌊((r : ℝ) * p)⌋₊ = ⌊(α * p)⌋₊ := by
  have hevent : ∀ᶠ β : ℝ in 𝓝 α, ∀ p ∈ Finset.range (N + 1), p.Prime →
      ⌊(β * p)⌋₊ = ⌊(α * p)⌋₊ := by
    apply (eventually_all_finset _).mpr
    intro p _
    by_cases hp : p.Prime
    · have ht : Continuous (fun β : ℝ => β * p) :=
        continuous_id.mul continuous_const
      have hlo : (⌊(α * p)⌋₊ : ℝ) < α * p := by
        exact lt_of_le_of_ne
          (Nat.floor_le (mul_nonneg (by linarith) (Nat.cast_nonneg p)))
          ((hi.mul_natCast hp.ne_zero).ne_nat _).symm
      filter_upwards [ht.continuousAt.eventually_const_lt hlo,
        ht.continuousAt.eventually_lt_const (Nat.lt_floor_add_one (α * p))] with β hβlo hβhi
      intro _
      exact (Nat.floor_eq_iff ((Nat.cast_nonneg _).trans hβlo.le)).mpr ⟨hβlo.le, hβhi⟩
    · exact Eventually.of_forall (fun _ h => (hp h).elim)
  have hnear : ∀ᶠ β : ℝ in 𝓝 α, dist β α < ε := Metric.ball_mem_nhds α hε
  obtain ⟨r, hr, hfloor⟩ := Rat.denseRange_cast.mem_nhds (hnear.and hevent)
  exact ⟨r, hr, fun p hp => hfloor p (Finset.mem_range.mpr (by omega))⟩

open Filter in
open scoped Topology in
/-- Any counterexample would admit rational approximations with finite-window
gaps, bounded in an interval above one, and eventually separated from every
fixed rational. Conversely these finite certificates would suffice. -/
theorem negation_iff_rational_separated_gap_sequence :
    (¬ ∀ α > 1, Irrational α → (primeSet α).Infinite) ↔
      ∃ (a : ℕ → ℚ) (L U : ℝ), 1 < L ∧
        (∀ n, (a n : ℝ) ∈ Set.Icc L U) ∧
        (∀ q : ℚ, ∃ δ > 0, ∀ᶠ n in atTop, δ ≤ dist (a n : ℝ) (q : ℝ)) ∧
        ∃ B : ℕ, ∀ n p : ℕ, B < p → p ≤ n → p ∉ primeSet (a n : ℝ) := by
  constructor
  · intro h
    obtain ⟨α, hα, hi, B, hB⟩ := negation_iff_bounded_counterexample.mp h
    have heps (n : ℕ) : 0 < min ((α - 1) / 2) (1 / ((n : ℝ) + 1)) :=
      lt_min (by linarith) (by positivity)
    choose a ha hfloor using fun n => exists_rat_finite_floor_agreement hα hi n (heps n)
    have hlim : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 α) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun _ => dist_nonneg)
        (fun n => (ha n).le.trans (min_le_right _ _))
        tendsto_one_div_add_atTop_nhds_zero_nat
    refine ⟨a, (α + 1) / 2, (3 * α - 1) / 2, by linarith, ?_, ?_, B, ?_⟩
    · intro n
      have hn : |(a n : ℝ) - α| < (α - 1) / 2 :=
        (ha n).trans_le (min_le_left _ _)
      have := abs_lt.mp hn
      constructor <;> linarith
    · intro q
      have hd : 0 < dist α (q : ℝ) := dist_pos.mpr (hi.ne_rat q)
      refine ⟨dist α (q : ℝ) / 2, by positivity, ?_⟩
      exact ((hlim.dist tendsto_const_nhds).eventually_const_lt
        (show dist α (q : ℝ) / 2 < dist α (q : ℝ) by linarith)).mono
        (fun _ hn => hn.le)
    · rintro n p hBp hpn ⟨hp, hq⟩
      exact hB p hBp hp (by simpa only [hfloor n p hpn hp] using hq)
  · rintro ⟨a, L, U, hL, hbdd, hsep, B, hgap⟩
    exact separated_gap_sequence_counterexample hL hbdd hsep B hgap

#print axioms isClosed_tailExceptional
#print axioms irrational_of_tendsto_separated
#print axioms separated_gap_sequence_counterexample
#print axioms negation_iff_separated_gap_sequence
#print axioms exists_rat_finite_floor_agreement
#print axioms negation_iff_rational_separated_gap_sequence


#print axioms compact_uniform_prime_bound
#print axioms compact_counterexample_criterion

#print axioms endpointPrimeSet_subsingleton
#print axioms finite_primeSet_iff_mem_tailExceptional
#print axioms finite_primeSet_of_limit

end Explore972
