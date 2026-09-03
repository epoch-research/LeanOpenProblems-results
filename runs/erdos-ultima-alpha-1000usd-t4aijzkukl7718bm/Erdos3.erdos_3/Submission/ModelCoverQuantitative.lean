import Submission.FreimanModelCase

/-! Quantitative obstruction to covering integer AP-free sets by characteristic-three
Freiman-modelable pieces. This is not a disproof of Erdős 3. -/
namespace Erdos3ModelCoverQuantitative

open Finset Filter Erdos3FreimanModelCase
set_option maxHeartbeats 1000000

/-- The polynomial counting bound also controls a finite union of model pieces. -/
lemma model_cover_card_bound {S : Finset ℕ} {N r : ℕ} (C : ℕ → Fin r)
    (hN : ∀ x ∈ S, x < N)
    (hC : ∀ c, HasThreeModel (S.filter (fun x ↦ C x = c))) :
    S.card^43 ≤ r^43 * (3^29 * 2^42) * N^42 := by
  classical
  let f : Fin r → ℕ := fun c ↦ (S.filter (fun x ↦ C x = c)).card
  let m := univ.sup f
  have hm : m^43 ≤ (3^29 * 2^42) * N^42 := by
    apply Finset.sup_induction (p := fun t : ℕ ↦ t^43 ≤ (3^29 * 2^42) * N^42)
    · simp
    · intro a ha b hb
      rcases le_total a b with h | h
      · simpa only [sup_eq_right.mpr h] using hb
      · simpa only [sup_eq_left.mpr h] using ha
    · intro c _
      exact modeled_card_in_range (hC c) (fun x hx ↦ hN x (mem_filter.mp hx).1)
  have hc : S.card ≤ r*m := by
    calc
      S.card = ∑ c : Fin r, f c := card_eq_sum_card_fiberwise (f := C) (t := univ) (by intro x hx; simp)
      _ ≤ ∑ _c : Fin r, m := sum_le_sum (fun c hc ↦ le_sup hc)
      _ = r*m := by simp
  calc
    S.card^43 ≤ (r*m)^43 := Nat.pow_le_pow_left hc _
    _ = r^43*m^43 := mul_pow _ _ _
    _ ≤ r^43*((3^29 * 2^42)*N^42) := Nat.mul_le_mul_left _ hm
    _ = _ := by ring

/-- Behrend sets eventually beat every fixed polynomial saving in cardinality. -/
lemma eventually_roth_power_lower (q : ℕ) :
    ∀ᶠ N : ℕ in atTop, N^q ≤ (rothNumberNat N)^(q+1) := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    ((4*((q : ℝ)+1))^2)
  filter_upwards [hlog, eventually_ge_atTop 1] with N hN hpos
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 ≤ Real.log (N : ℝ) := le_trans (sq_nonneg _) hN
  have hs : 4*((q : ℝ)+1) ≤ Real.sqrt (Real.log (N : ℝ)) :=
    Real.le_sqrt_of_sq_le hN
  have hs2 := Real.sq_sqrt hl
  have hprod := mul_nonneg (sub_nonneg.mpr hs) (Real.sqrt_nonneg (Real.log (N : ℝ)))
  have hexp : (q : ℝ)*Real.log (N : ℝ) ≤
      ((q+1 : ℕ) : ℝ)*(Real.log (N : ℝ) + -4*Real.sqrt (Real.log (N : ℝ))) := by
    push_cast
    nlinarith
  have hreal : (N : ℝ)^q ≤ (rothNumberNat N : ℝ)^(q+1) := by
    calc
      (N : ℝ)^q = Real.exp ((q : ℝ)*Real.log (N : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hNp]
      _ ≤ Real.exp (((q+1 : ℕ) : ℝ)*(Real.log (N : ℝ) + -4*Real.sqrt (Real.log (N : ℝ)))) :=
        Real.exp_le_exp.mpr hexp
      _ = ((N : ℝ)*Real.exp (-4*Real.sqrt (Real.log (N : ℝ))))^(q+1) := by
        rw [Real.exp_nat_mul, Real.exp_add, Real.exp_log hNp]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) Behrend.roth_lower_bound _
  exact_mod_cast hreal

/-- For all sufficiently large N, some 3-AP-free set below N requires at least
polynomially many characteristic-three model pieces: N ≤ K² r⁸⁶. -/
theorem eventually_polynomial_model_cover_obstruction :
    ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
      S ⊆ range N ∧ ThreeAPFree (S : Set ℕ) ∧
      ∀ r : ℕ, ∀ C : ℕ → Fin r,
        (∀ c, HasThreeModel (S.filter (fun x ↦ C x = c))) →
        N ≤ (3^29 * 2^42)^2 * r^86 := by
  filter_upwards [eventually_roth_power_lower 85, eventually_ge_atTop 1] with N hl hp
  obtain ⟨S, hS, hc, hf⟩ := rothNumberNat_spec N
  refine ⟨S, hS, hf, fun r C hC ↦ ?_⟩
  have hb := model_cover_card_bound C (fun x hx ↦ mem_range.mp (hS hx)) hC
  have hlow : N^85 ≤ S.card^86 := by simpa [hc] using hl
  have hu : S.card^86 ≤ ((3^29 * 2^42)^2*r^86) * N^84 := by
    calc
      S.card^86 = (S.card^43)^2 := by rw [← pow_mul]
      _ ≤ (r^43*(3^29 * 2^42)*N^42)^2 := Nat.pow_le_pow_left hb 2
      _ = _ := by ring
  have hmul : N*N^84 ≤ ((3^29 * 2^42)^2*r^86)*N^84 := by
    simpa only [← pow_succ'] using hlow.trans hu
  exact Nat.le_of_mul_le_mul_right hmul (by positivity)

#print axioms model_cover_card_bound
#print axioms eventually_roth_power_lower
#print axioms eventually_polynomial_model_cover_obstruction
end Erdos3ModelCoverQuantitative
