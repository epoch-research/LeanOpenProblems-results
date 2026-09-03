import Submission.QuarticProgressionPeaks
import Submission.QuarticScaledRationalProduct

/-! Fixed-scale multiplication fails at arbitrarily large exact quartic
multiplicities, without any assumption that outputs come from a formula. -/
namespace Erdos322Research.HighCountProductFailure
noncomputable section
open Finset QuarticFiberBasic QuarticProgressionPeaks QuarticSquareMultiplier
open QuarticScaledRationalProduct
set_option Elab.async false

private def smallSeed (r : Fin 4) : Fin 4 → Fin 16 :=
  ![if 1 ≤ r.val then 1 else 0, if 2 ≤ r.val then 1 else 0,
    if 3 ≤ r.val then 1 else 0, 0]

lemma small_residue_represented (r : Fin 4) : 0 < fiberCount 16 r.val := by
  have hs : (∑ i, (smallSeed r i : ℕ)^4) ≡ r.val [MOD 16] := by
    fin_cases r <;> norm_num [smallSeed,Fin.sum_univ_succ,Nat.ModEq]
  haveI : Nonempty (Fiber 16 r.val) := ⟨⟨smallSeed r,hs⟩⟩
  exact Fintype.card_pos

private lemma residue_factors (c : Fin 16) (hc : c.val ≠ 0) :
    ∃ a b : Fin 4, 0 < a.val ∧ 0 < b.val ∧ 4 < (c.val*a.val*b.val)%16 := by
  revert c
  decide

/-- For every positive fixed natural scale, arbitrarily large counts occur
at two targets whose scaled product has NO rational quartic representation.
The targets may be different. No polynomial-formula hypothesis is used. -/
theorem high_count_product_failure (C M N : ℕ) (hC : 0 < C) :
    ∃ m n : ℕ,
      M < Erdos322.representationCount 4 m ∧
      N < Erdos322.representationCount 4 n ∧ ¬ Represented (C*m*n) := by
  induction C using Nat.strong_induction_on with
  | h C ih =>
    by_cases hd : 16 ∣ C
    · have hp : 0 < C/16 := Nat.div_pos (Nat.le_of_dvd hC hd) (by decide)
      have hs : C/16 < C := Nat.div_lt_self hC (by decide)
      have he : 16*(C/16)=C := Nat.mul_div_cancel' hd
      obtain ⟨m,n,hm,hn,hbad⟩ := ih (C/16) hs hp
      refine ⟨m,n,hm,hn,?_⟩
      intro hh
      apply hbad
      apply represented_strip_sixteen
      convert hh using 1
      calc
        16*(C/16*m*n) = (16*(C/16))*m*n := by ring
        _ = C*m*n := by rw [he]
    · have hc : C%16 ≠ 0 := fun hh ↦ hd (Nat.dvd_of_mod_eq_zero hh)
      obtain ⟨a,b,ha,hb,hab⟩ := residue_factors ⟨C%16,Nat.mod_lt _ (by decide)⟩ hc
      obtain ⟨m,hm,hmcount⟩ := count_unbounded_in_represented_progression 16 a.val M
        (by decide) (small_residue_represented a)
      obtain ⟨n,hn,hncount⟩ := count_unbounded_in_represented_progression 16 b.val N
        (by decide) (small_residue_represented b)
      refine ⟨m,n,hmcount,hncount,?_⟩
      intro hh
      have hmod := represented_mod_sixteen hh
      have he : (C*m*n)%16=((C%16)*a.val*b.val)%16 := by
        have hma : m%16=a.val%16 := hm
        have hnb : n%16=b.val%16 := hn
        simp only [Nat.mul_mod,hma,hnb,Nat.mod_mod]
      rw [he] at hmod
      change 4 < ((C%16)*a.val*b.val)%16 at hab
      exact Nat.not_lt_of_ge hmod hab

/-- Clearing a fourth-power denominator gives the same failure for every
positive rational scale. Thus no arbitrary universally applicable choice
rule can multiply all high-count targets with a fixed positive scale. -/
theorem high_count_rational_product_failure (C : ℚ) (hC : 0 < C) (M N : ℕ) :
    ∃ m n : ℕ,
      M < Erdos322.representationCount 4 m ∧
      N < Erdos322.representationCount 4 n ∧
      ¬ (∃ a : Fin 4 → ℚ, ∑ i, a i^4=C*(m : ℚ)*(n : ℚ)) := by
  obtain ⟨d,K,hd,hK,hscale⟩ := natural_fourth_multiple C hC
  obtain ⟨m,n,hm,hn,hbad⟩ := high_count_product_failure K M N hK
  refine ⟨m,n,hm,hn,?_⟩
  rintro ⟨a,ha⟩
  apply hbad
  refine ⟨fun i ↦ (d : ℚ)*a i,?_⟩
  simp only [mul_pow,← Finset.mul_sum,ha,Nat.cast_mul,hscale]
  ring

end
end Erdos322Research.HighCountProductFailure
