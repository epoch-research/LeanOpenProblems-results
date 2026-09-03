import Submission.BoundedPrimeRectangleSupply

/-!
# Near-full-power prime output counts together with levels below 4/7

The prime count and the congruence mean hold for the same bounded input.
The predecessor smoothness cutoff tends to a HALF power of the ambient
range, not to zero. Thus this does not settle Erdos 821 or improve the
previously established multiplicity exponent.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open Erdos821.Kloosterman
set_option maxHeartbeats 3000000

lemma exists_parametric_joint_levels (θ β : ℝ) (hθ : θ < 4/7) (hβ : β < 1) :
    ∃ k : ℕ, 5 ≤ k ∧ θ < (8*(k : ℝ)+4)/(14*(k : ℝ)+16) ∧
      β*(14*(k : ℝ)+16) < 14*(k : ℝ)+10 := by
  have hdθ : 0 < 8-14*θ := by linarith
  have hdβ : 0 < 14-14*β := by linarith
  obtain ⟨k,hk⟩ := exists_nat_gt
    (max 5 (max ((16*θ-4)/(8-14*θ)) ((16*β-10)/(14-14*β))))
  have hk5 : (5 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hmid := (le_max_right _ _).trans_lt hk
  have hθk := (div_lt_iff₀ hdθ).mp ((le_max_left _ _).trans_lt hmid)
  have hβk := (div_lt_iff₀ hdβ).mp ((le_max_right _ _).trans_lt hmid)
  refine ⟨k,by exact_mod_cast hk5.le,?_,by nlinarith⟩
  apply (lt_div_iff₀ (by positivity)).mpr
  nlinarith

lemma parametric_supply_power_gt_rpow (k M : ℕ) (hM : 1 ≤ M) (β : ℝ)
    (hβ : β*(14*(k : ℝ)+16) < 14*(k : ℝ)+10) :
    (parametricAmbient k M : ℝ)^β < ((2^((14*k+10)*M) : ℕ) : ℝ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  simp only [parametricAmbient,Nat.cast_pow,Nat.cast_ofNat]
  rw [← Real.rpow_natCast_mul (by norm_num),← Real.rpow_natCast]
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
  have hh := mul_lt_mul_of_pos_right hβ hMR
  push_cast
  nlinarith only [hh]

/-- For each theta<4/7 and beta<1, one fixed parameter yields a bounded
input prime with more than A^beta DISTINCT prime successors, and with the
logarithmically saving congruence mean beyond A^theta. This still retains
two unrestricted cofactor intervals and only their stated smoothness bound. -/
theorem exists_prime_rectangle_supply_above_levels (θ β : ℝ)
    (hθ : θ < 4/7) (hβ : β < 1) :
    ∃ k : ℕ, 5 ≤ k ∧ ∀ d : ℕ, ∀ η : ℝ, 0 < η →
      ∀ᶠ m : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ 2^(64*m) < p ∧ p ≤ 2^(128*m) ∧
        (parametricAmbient k (64*m) : ℝ)^θ < parametricModulus k (64*m) ∧
        (parametricAmbient k (64*m) : ℝ)^β <
          (rectanglePrimeOutputs p (parametricInterval k (64*m))).card ∧
        (∀ R ∈ rectanglePrimeOutputs p (parametricInterval k (64*m)),
          R ≤ parametricAmbient k (64*m)+1 ∧
          R-1 ∈ Nat.smoothNumbers (parametricInterval k (64*m)+1)) ∧
        parametricAmbient k (64*m)+1 < parametricModulus k (64*m)^2 ∧
        ∀ P : Finset ℕ, (∀ q ∈ P, Squarefree q ∧ q ≤ parametricModulus k (64*m)) →
        (1+Real.log (parametricAmbient k (64*m) : ℝ))^d*
          (∑ q ∈ P, |(∑ i ∈ range (parametricInterval k (64*m)),
            ∑ j ∈ range (parametricInterval k (64*m)),
              if q ∣ (i+1)*(j+1)*p+1 then (1 : ℝ) else 0)-
            (parametricInterval k (64*m) : ℝ)^2*q.totient/(q : ℝ)^2|) ≤
          η*(parametricInterval k (64*m) : ℝ)^2 := by
  obtain ⟨k,hk,hlevel,hpower⟩ := exists_parametric_joint_levels θ β hθ hβ
  refine ⟨k,hk,?_⟩
  intro d η hη
  filter_upwards [eventually_bounded_prime_supply_and_mean k hk d η hη,
    eventually_ge_atTop 1] with m Hm hm
  obtain ⟨p,hp,hlo,hhi,hcount,hout,hhalf,hmean⟩ := Hm
  refine ⟨p,hp,hlo,hhi,parametric_modulus_gt_rpow k (64*m) (by omega) θ hlevel,
    ?_,hout,hhalf,hmean⟩
  exact (parametric_supply_power_gt_rpow k (64*m) (by omega) β hpower).trans
    (by exact_mod_cast hcount)

end Erdos821.AnalyticSieve
