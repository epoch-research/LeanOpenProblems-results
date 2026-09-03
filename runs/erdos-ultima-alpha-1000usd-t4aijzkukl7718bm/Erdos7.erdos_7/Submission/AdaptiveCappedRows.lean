import Submission.CappedRetentionRows

/-!
Count-dependent caps for the FULL positive retained mixture. A cap can drop
only after a plateau's zero-loss threshold. Auxiliary comparison lemmas only;
no scalar certificate or covering-system obstruction is asserted here.
-/
namespace Erdos7AdaptiveCappedRows
open Erdos7CappedRetentionRows Erdos7CappedFiberMixture

lemma coefficient_scale (h c : ℝ) (hc : 0 ≤ c) (r : ℕ → ℝ)
    (R : ℕ) (d : Option (Fin R)) :
    coefficient (c*h) (fun j => c*r j) R d = c*coefficient h r R d := by
  cases d <;> simp only [coefficient, ← mul_min_of_nonneg _ _ hc, mul_sub]

lemma coefficient_zero (c : ℝ) (hc : 0 ≤ c) (r : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (R : ℕ) (d : Option (Fin R)) :
    coefficient 0 (fun j => c*r j) R d = 0 := by
  cases d <;> simp only [coefficient, min_eq_left (mul_nonneg hc (hr _)), sub_self]

lemma retained_eq_of_active (q c K k : ℝ) (hkK : k ≤ K)
    (hkq : k ≤ q) (hq : 0 < q) (hc : 0 ≤ c)
    (ha : c*(1-k/q) ≤ 1) :
    retained q c K k = c*(1-k/q) := by
  have hr : 0 ≤ 1-k/q := sub_nonneg.mpr ((div_le_one hq).mpr hkq)
  simp only [retained, if_pos hkK, min_eq_right ha, max_eq_right (mul_nonneg hc hr)]

/-- Within the active-loss region, every capped-mixture coefficient is
antitone when both the count increases and the cap decreases. -/
theorem active_coefficient_order (q K ck cl k l : ℝ)
    (hq : 0 < q) (hK : K ≤ q) (hcl : 0 ≤ cl) (hcap : cl ≤ ck)
    (hkl : k ≤ l) (hlK : l ≤ K) (ha : ck*(1-k/q) ≤ 1)
    (r : ℕ → ℝ) (hr : ∀ j, r (j+1) ≤ r j) (R : ℕ) (d : Option (Fin R)) :
    coefficient (retained q cl K l) (fun j => cl*r j) R d ≤
      coefficient (retained q ck K k) (fun j => ck*r j) R d := by
  have hck : 0 ≤ ck := hcl.trans hcap
  have hkK := hkl.trans hlK
  have hlq := hlK.trans hK
  have hkq := hkK.trans hK
  have hlr : 0 ≤ 1-l/q := sub_nonneg.mpr ((div_le_one hq).mpr hlq)
  have hrl : 1-l/q ≤ 1-k/q := sub_le_sub_left (div_le_div_of_nonneg_right hkl hq.le) 1
  have hal : cl*(1-l/q) ≤ 1 :=
    ((mul_le_mul_of_nonneg_right hcap hlr).trans
      (mul_le_mul_of_nonneg_left hrl hck)).trans ha
  rw [retained_eq_of_active q cl K l hlK hlq hq hcl hal,
      retained_eq_of_active q ck K k hkK hkq hq hck ha,
      coefficient_scale _ cl hcl, coefficient_scale _ ck hck]
  have hzero : 0 ≤ coefficient (1-l/q) r R d := coefficient_nonneg _ r R hr d
  have hmono := coefficient_monotone r R hr d hrl
  exact (mul_le_mul_of_nonneg_right hcap hzero).trans (mul_le_mul_of_nonneg_left hmono hck)

/-- Full-mixture analogue of the old uncapped baseline-order theorem. The
cutoff may extend to q; it is not restricted to q*(1-1/p). -/
theorem plateau_coefficients_antitoneOn (q K t c₀ : ℝ) (T : Set ℝ) (c : ℝ → ℝ)
    (hq : 0 < q) (hK : K ≤ q) (hc₀ : 0 ≤ c₀)
    (hc0 : ∀ k ∈ T, 0 ≤ c k) (hc : AntitoneOn c T)
    (hupper : ∀ k ∈ T, c k ≤ c₀)
    (hplateau : ∀ k ∈ T, k ≤ t → c k=c₀)
    (hthreshold : c₀*(1-t/q) ≤ 1)
    (r : ℕ → ℝ) (hr0 : ∀ j, 0 ≤ r j) (hr : ∀ j, r (j+1) ≤ r j)
    (R : ℕ) (d : Option (Fin R)) :
    AntitoneOn (fun k => coefficient (retained q (c k) K k) (fun j => c k*r j) R d) T := by
  intro k hk l hl hkl
  dsimp only
  have htail : ∀ j, c₀*r (j+1) ≤ c₀*r j := fun j => mul_le_mul_of_nonneg_left (hr j) hc₀
  by_cases hlK : l ≤ K
  · by_cases hlt : l ≤ t
    · rw [hplateau k hk (hkl.trans hlt), hplateau l hl hlt]
      exact capped_rows_antitone q c₀ K hq hc₀ (fun j => c₀*r j) R htail d hkl
    by_cases hkt : k ≤ t
    · rw [hplateau k hk hkt]
      have htl : t ≤ l := le_of_lt (lt_of_not_ge hlt)
      calc
        _ ≤ coefficient (retained q c₀ K t) (fun j => c₀*r j) R d :=
          active_coefficient_order q K c₀ (c l) t l hq hK (hc0 l hl)
            (hupper l hl) htl hlK hthreshold r hr R d
        _ ≤ _ := capped_rows_antitone q c₀ K hq hc₀ (fun j => c₀*r j) R htail d hkt
    · have htk : t ≤ k := le_of_lt (lt_of_not_ge hkt)
      have hkr : 0 ≤ 1-k/q := sub_nonneg.mpr ((div_le_one hq).mpr ((hkl.trans hlK).trans hK))
      have hrt : 1-k/q ≤ 1-t/q := sub_le_sub_left (div_le_div_of_nonneg_right htk hq.le) 1
      have ha : c k*(1-k/q) ≤ 1 :=
        ((mul_le_mul_of_nonneg_right (hupper k hk) hkr).trans
          (mul_le_mul_of_nonneg_left hrt hc₀)).trans hthreshold
      exact active_coefficient_order q K (c k) (c l) k l hq hK (hc0 l hl)
        (hc hk hl hkl) hkl hlK ha r hr R d
  · rw [show retained q (c l) K l = 0 by simp [retained, hlK],
      coefficient_zero (c l) (hc0 l hl) r hr0 R d]
    exact coefficient_nonneg _ _ _ (fun j => mul_le_mul_of_nonneg_left (hr j) (hc0 k hk)) d

#print axioms coefficient_scale
#print axioms active_coefficient_order
#print axioms plateau_coefficients_antitoneOn
end Erdos7AdaptiveCappedRows
