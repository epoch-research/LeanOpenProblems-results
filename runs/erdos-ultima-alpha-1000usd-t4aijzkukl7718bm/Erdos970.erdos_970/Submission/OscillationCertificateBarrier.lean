import Submission.PopulationOscillationEntropy
import Submission.ParityExactScaledQuadratic

/-! Exact-quadratic obstruction to a uniform worst-case oscillation
certificate. This does not assert a covered interval. -/
namespace Erdos970.FiniteGibbs
open Finset Real GapAverages Resampling ParityDiscrepancy
set_option maxHeartbeats 2000000

lemma log_phase_card_ge_half (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (P.card : ℝ)/2 ≤ log (Fintype.card (Phase P) : ℝ) := by
  classical
  have hc : 2^P.card ≤ Fintype.card (Phase P) := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    have hh := prod_le_prod (s := (univ : Finset P)) (f := fun _ => (2 : ℕ))
      (fun _ _ => by omega) (fun p _ => (hP p.val p.property).two_le)
    simpa only [prod_const,card_univ,Fintype.card_coe] using hh
  have hcR : (2 : ℝ)^P.card ≤ Fintype.card (Phase P) := by exact_mod_cast hc
  have hl : (1/2 : ℝ) ≤ log 2 := by
    have hh := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hh := log_le_log (by positivity : (0 : ℝ) < 2^P.card) hcR
  rw [log_pow] at hh
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg P.card : (0 : ℝ) ≤ P.card)
  nlinarith only [hh,hm]

/-- Meeting the cost inequality forces a linear constraint on the prime-two
oscillation cap. The statement does not assume that any such cap exists. -/
lemma cost_forces_two_cap (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (h2 : 2 ∈ P) (B : ℕ → ℝ) (T : ℝ) (hT : 0 < T)
    (hB : ∀ p ∈ P, 0 ≤ B p)
    (hcost : log (Fintype.card (Phase P) : ℝ) <
      (S.card : ℝ)*density P*T/(1+entropyCapBudget P B T*T)) :
    (P.card : ℝ)*B 2 < 2*S.card := by
  let L := log (Fintype.card (Phase P) : ℝ)
  let D := entropyCapBudget P B T
  have hL : (P.card : ℝ)/2 ≤ L := log_phase_card_ge_half P hP
  have hL0 : 0 ≤ L := (by positivity : (0 : ℝ) ≤ (P.card : ℝ)/2).trans hL
  have hD0 : 0 ≤ D := entropyCapBudget_nonneg P B T hB
  have hD : B 2 ≤ D := by
    have hh := single_le_sum (s := P) (f := fun p => (1+exp (T*B p))*B p/(p : ℝ))
      (fun p hp => div_nonneg (mul_nonneg (by positivity) (hB p hp)) (by positivity)) h2
    have he : 1 ≤ exp (T*B 2) := one_le_exp (mul_nonneg hT.le (hB 2 h2))
    have hm := mul_le_mul_of_nonneg_right he (hB 2 h2)
    dsimp only [D,entropyCapBudget]
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith only [hh,hm]
  have hden : 0 < 1+D*T := by positivity
  have hh : L*(1+D*T) < (S.card : ℝ)*density P*T := (lt_div_iff₀ hden).mp hcost
  have hc := mul_le_mul hL hD (hB 2 h2) hL0
  have hct := mul_le_mul_of_nonneg_right hc hT.le
  have hdens := mul_le_mul_of_nonneg_left (GapAverages.density_le_one P hP)
    (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  have hdt := mul_le_mul_of_nonneg_right hdens hT.le
  have hout : ((P.card : ℝ)*B 2)*T < (2*S.card)*T := by
    nlinarith only [hh,hct,hdt,hL0]
  exact (mul_lt_mul_iff_left₀ hT).mp hout

lemma dvd_succ_iff_remainder (p j : ℕ) (hp : 0 < p) :
    p ∣ 1+j ↔ j%p = p-1 := by
  have hm := Nat.mod_lt j hp
  have he := Nat.mod_add_mod j p 1
  constructor
  · intro hd
    have hz : (j+1)%p = 0 := Nat.mod_eq_zero_of_dvd (by simpa only [Nat.add_comm] using hd)
    rw [hz] at he
    by_contra hne
    have hlt : j%p+1 < p := by omega
    rw [Nat.mod_eq_of_lt hlt] at he
    omega
  · intro h
    have heq : j%p+1 = p := by omega
    rw [heq,Nat.mod_self] at he
    exact Nat.dvd_of_mod_eq_zero (by simpa only [Nat.add_comm] using he.symm)

noncomputable def shiftedZeroPhase (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : Phase P :=
  fun p => ⟨p.val-1,Nat.sub_lt (hP p.val p.property).pos (by omega)⟩

lemma shifted_zero_avoidance (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (j : ℕ) :
    (∀ p : P, j%p.val ≠ (shiftedZeroPhase P hP p).val) ↔
      ∀ p ∈ P, ¬p ∣ 1+j := by
  simp only [shiftedZeroPhase]
  constructor
  · intro h p hp hd
    exact h ⟨p,hp⟩ ((dvd_succ_iff_remainder p j (hP p hp).pos).mp hd)
  · intro h p hm
    exact h p.val p.property ((dvd_succ_iff_remainder p.val j (hP p.val p.property).pos).mpr hm)

/-- The older parity obstruction is the actual difference of two residue
rows of a conditional population in the present phase model. -/
lemma alternatingCount_eq_shifted_row_difference (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    (alternatingCount P 1 m : ℝ) =
      classHits (populationSurvivors (range m) P (shiftedZeroPhase P hP)) 2 0-
        classHits (populationSurvivors (range m) P (shiftedZeroPhase P hP)) 2 1 := by
  rw [alternatingCount_eq_card_difference]
  push_cast
  rw [classHits_card,classHits_card]
  congr 1 <;> congr 1 <;> congr 1 <;> ext j <;>
    simp only [populationSurvivors,mem_filter,Fin.val_zero,Fin.val_one,
      shifted_zero_avoidance,Nat.even_iff,Nat.odd_iff] <;> tauto

/-- A uniform certificate at every exact quadratic interval length would
force the already-refuted uniform linear parity-discrepancy bound. -/
theorem no_uniform_quadratic_oscillation_certificate (C K : ℕ) (hC : 0 < C) :
    ¬∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → K ≤ P.card →
      ∃ B : ℕ → ℝ, ∃ T : ℝ, 0 < T ∧ (∀ p ∈ P, 0 ≤ B p) ∧
        PopulationOscillationBound P (range (C*P.card^2)) B ∧
        log (Fintype.card (Phase P) : ℝ) <
          ((C*P.card^2 : ℕ) : ℝ)*density P*T/(1+entropyCapBudget P B T*T) := by
  classical
  intro hcert
  obtain ⟨Q,hQ,hK,hk,hlarge⟩ := unbounded_parity_at_exact_quadratic (8*C) C (K+1) hC
  have h2 : 2 ∉ Q := fun h => oddPrime_ne_two (hQ 2 h).2 rfl
  let P := insert 2 Q
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact Nat.prime_two
    · exact (hQ p hp).1
  have hcard : P.card = Q.card+1 := card_insert_of_notMem h2
  obtain ⟨B,T,hT,hB,hosc,hcost⟩ := hcert P hP (by omega)
  have hcap := cost_forces_two_cap P (range (C*P.card^2)) hP (mem_insert_self 2 Q) B T hT hB
    (by simpa only [card_range] using hcost)
  rw [card_range,hcard] at hcap
  push_cast at hcap
  have hcpos : (0 : ℝ) < Q.card+1 := by positivity
  have hb : B 2 < 2*C*(Q.card+1 : ℝ) := by
    apply (mul_lt_mul_iff_right₀ hcpos).mp
    nlinarith only [hcap]
  have ho := hosc Q (subset_insert 2 Q) 2 (mem_insert_self 2 Q) h2
    (shiftedZeroPhase Q (fun p hp => (hQ p hp).1)) 0 1
  rw [← alternatingCount_eq_shifted_row_difference] at ho
  rw [hcard] at ho
  have hlen : C*Q.card^2 ≤ C*(Q.card+1)^2 := Nat.mul_le_mul_left C (by nlinarith)
  have hpref := abs_alternatingCount_prefix Q 1 (C*Q.card^2) (C*(Q.card+1)^2) hlen
  have hgap : C*(Q.card+1)^2-C*Q.card^2 = C*(2*Q.card+1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [hgap] at hpref
  have hpreal : |(alternatingCount Q 1 (C*Q.card^2) : ℝ)| ≤
      |(alternatingCount Q 1 (C*(Q.card+1)^2) : ℝ)|+(C : ℝ)*(2*Q.card+1) := by
    exact_mod_cast hpref
  have hl : (8*C : ℝ)*Q.card < |(alternatingCount Q 1 (C*Q.card^2) : ℝ)| := by
    exact_mod_cast hlarge
  have hkR : (1 : ℝ) ≤ Q.card := by exact_mod_cast hk
  have hCR : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hm := mul_le_mul_of_nonneg_left hkR hCR
  nlinarith only [hl,hpreal,ho,hb,hm]

#print axioms alternatingCount_eq_shifted_row_difference
#print axioms no_uniform_quadratic_oscillation_certificate
end Erdos970.FiniteGibbs
