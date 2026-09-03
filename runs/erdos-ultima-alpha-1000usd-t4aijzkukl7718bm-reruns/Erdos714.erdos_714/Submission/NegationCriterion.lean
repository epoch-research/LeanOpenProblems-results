import Submission.Spec

/-!
# Exact finite and subsequential criteria for the negation of Erdős 714

These are equivalences, not proofs that the conjecture or its negation holds.
No result below depends on the unfinished `Erdos714.erdos_714` declaration.
-/

open Filter SimpleGraph

namespace Erdos714Negation

/-- Negating a uniform eventual integer lower bound permits a diagonal choice
of the constant and the lower threshold. -/
theorem not_eventual_iff_diagonal (f T : ℕ → ℕ) :
    (¬ ∃ C : ℕ, 0 < C ∧ ∀ᶠ k : ℕ in atTop, T k ≤ C * f k) ↔
      ∀ D : ℕ, ∃ k : ℕ, D ≤ k ∧ (D + 1) * f k < T k := by
  classical
  constructor
  · intro h D
    by_contra! hn
    apply h
    refine ⟨D + 1, by omega, eventually_atTop.mpr ⟨D, ?_⟩⟩
    exact hn
  · rintro h ⟨C, _, hC⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp hC
    obtain ⟨k, hk, hlt⟩ := h (max N C)
    have hNk : N ≤ k := (le_max_left N C).trans hk
    have hCm : C ≤ max N C + 1 := by omega
    exact (not_lt_of_ge ((hN k hNk).trans (Nat.mul_le_mul_right (f k) hCm))) hlt

/-- The diagonal upper estimates can be realized on a strictly increasing
sequence, with a coefficient tending to infinity. -/
theorem diagonal_iff_strictMono (f T : ℕ → ℕ) :
    (∀ D : ℕ, ∃ k : ℕ, D ≤ k ∧ (D + 1) * f k < T k) ↔
      ∃ a : ℕ → ℕ, StrictMono a ∧ ∀ D, (D + 1) * f (a D) < T (a D) := by
  classical
  constructor
  · intro h
    choose a ha hbound using h
    have hatop : Tendsto a atTop atTop := tendsto_atTop_mono ha tendsto_id
    obtain ⟨b, hb, hab⟩ := strictMono_subseq_of_tendsto_atTop hatop
    refine ⟨a ∘ b, hab, fun D => ?_⟩
    exact (Nat.mul_le_mul_right (f (a (b D)))
      (Nat.add_le_add_right (hb.id_le D) 1)).trans_lt (hbound (b D))
  · rintro ⟨a, ha, hbound⟩ D
    exact ⟨a D, ha.id_le D, hbound D⟩

/-- An equivalent analytic formulation: the normalized extremal counts tend
to zero along some strictly increasing sequence. -/
theorem diagonal_iff_zero_subsequence (f T : ℕ → ℕ) (hT : ∀ k, 0 < T k) :
    (∀ D : ℕ, ∃ k : ℕ, D ≤ k ∧ (D + 1) * f k < T k) ↔
      ∃ a : ℕ → ℕ, StrictMono a ∧
        Tendsto (fun D => (f (a D) : ℝ) / (T (a D) : ℝ)) atTop (nhds 0) := by
  constructor
  · intro h
    obtain ⟨a, ha, hbound⟩ := (diagonal_iff_strictMono f T).mp h
    refine ⟨a, ha, squeeze_zero (fun D => by positivity) (fun D => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat⟩
    have hpos : (0 : ℝ) < T (a D) := Nat.cast_pos.mpr (hT _)
    have hD : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    apply le_of_lt
    apply (div_lt_div_iff₀ hpos hD).mpr
    have hcast : ((D : ℝ) + 1) * (f (a D) : ℝ) < (T (a D) : ℝ) := by
      exact_mod_cast hbound D
    simpa only [one_mul, mul_one, mul_comm] using hcast
  · rintro ⟨a, ha, hlim⟩ D
    have hD : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    have hsmall := hlim.eventually_lt_const
      (show (0 : ℝ) < 1 / ((D : ℝ) + 1) by positivity)
    obtain ⟨j, hj, hlt⟩ := ((eventually_ge_atTop D).and hsmall).exists
    refine ⟨a j, hj.trans (ha.id_le j), ?_⟩
    have hpos : (0 : ℝ) < T (a j) := Nat.cast_pos.mpr (hT _)
    have hcast := (div_lt_div_iff₀ hpos hD).mp hlt
    have hcast' : ((D : ℝ) + 1) * (f (a j) : ℝ) < (T (a j) : ℝ) := by
      simpa only [one_mul, mul_one, mul_comm] using hcast
    exact_mod_cast hcast'

/-- Strict bounds for the maximum edge count are exactly universal strict
bounds for all free graphs, including all choices of adjacency decidability. -/
theorem mul_extremal_lt_iff {W : Type*} (H : SimpleGraph W) (hH : H ≠ ⊥)
    (n C T : ℕ) :
    C * extremalNumber n H < T ↔
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        H.Free G → C * G.edgeFinset.card < T := by
  constructor
  · intro h G _ hG
    have he : G.edgeFinset.card ≤ extremalNumber n H := by
      simpa only [Fintype.card_fin] using card_edgeFinset_le_extremalNumber hG
    exact (Nat.mul_le_mul_left C he).trans_lt h
  · intro h
    obtain ⟨G, inst, hG⟩ := exists_isExtremal_free (V := Fin n) hH
    have hb := h G hG.prop
    rw [card_edgeFinset_of_isExtremal_free hG] at hb
    simpa only [Fintype.card_fin] using hb

/-- Exact integer formulation of failure of one instance. -/
theorem instance_iff_diagonal (r : ℕ) (hr : 2 ≤ r) :
    (¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) ↔
    ∀ D : ℕ, ∃ k : ℕ, D ≤ k ∧
      (D + 1) * extremalNumber ((2 ^ k) ^ r)
        (completeBipartiteGraph (Fin r) (Fin r)) < (2 ^ k) ^ (2 * r - 1) := by
  rw [Erdos714Criterion.erdos_integer_criterion r hr]
  exact not_eventual_iff_diagonal _ _

/-- The negation of the entire original conjecture is equivalent to these
universal finite upper estimates for some fixed `r ≥ 4`. -/
theorem conjecture_negation_iff_finite :
    (¬ (∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n
          (completeBipartiteGraph (Fin r) (Fin r)) : ℝ))) ↔
    ∃ r : ℕ, 4 ≤ r ∧ ∀ D : ℕ, ∃ k : ℕ, D ≤ k ∧
      ∀ (G : SimpleGraph (Fin ((2 ^ k) ^ r))) [DecidableRel G.Adj],
        (completeBipartiteGraph (Fin r) (Fin r)).Free G →
          (D + 1) * G.edgeFinset.card < (2 ^ k) ^ (2 * r - 1) := by
  classical
  rw [Erdos714Progress.conjecture_iff_large_cases]
  simp only [not_forall, not_exists, not_and, exists_prop]
  apply exists_congr
  intro r
  apply and_congr_right
  intro hr
  have hi := instance_iff_diagonal r (by omega)
  simp only [not_exists, not_and] at hi
  rw [hi]
  have hH : completeBipartiteGraph (Fin r) (Fin r) ≠ ⊥ := by
    intro h
    let i : Fin r := ⟨0, by omega⟩
    have he : (completeBipartiteGraph (Fin r) (Fin r)).Adj (Sum.inl i) (Sum.inr i) :=
      by simp
    rw [h] at he
    exact he
  exact forall_congr' fun D => exists_congr fun k =>
    and_congr_right fun _ => mul_extremal_lt_iff _ hH _ _ _

/-- The same negation is equivalent to a zero subsequential limit at geometric
orders. The existence of this subsequence is not asserted. -/
theorem conjecture_negation_iff_zero_subsequence :
    (¬ (∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n
          (completeBipartiteGraph (Fin r) (Fin r)) : ℝ))) ↔
    ∃ r : ℕ, 4 ≤ r ∧ ∃ a : ℕ → ℕ, StrictMono a ∧
      Tendsto (fun D =>
        (extremalNumber ((2 ^ (a D)) ^ r)
          (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) /
            (((2 ^ (a D)) ^ (2 * r - 1) : ℕ) : ℝ)) atTop (nhds 0) := by
  classical
  rw [Erdos714Progress.conjecture_iff_large_cases]
  simp only [not_forall, not_exists, not_and, exists_prop]
  apply exists_congr
  intro r
  apply and_congr_right
  intro hr
  have hi := instance_iff_diagonal r (by omega)
  simp only [not_exists, not_and] at hi
  rw [hi]
  exact diagonal_iff_zero_subsequence _ _ (fun k => by positivity)

end Erdos714Negation

#print axioms Erdos714Negation.not_eventual_iff_diagonal
#print axioms Erdos714Negation.diagonal_iff_strictMono
#print axioms Erdos714Negation.diagonal_iff_zero_subsequence
#print axioms Erdos714Negation.mul_extremal_lt_iff
#print axioms Erdos714Negation.instance_iff_diagonal
#print axioms Erdos714Negation.conjecture_negation_iff_finite
#print axioms Erdos714Negation.conjecture_negation_iff_zero_subsequence
