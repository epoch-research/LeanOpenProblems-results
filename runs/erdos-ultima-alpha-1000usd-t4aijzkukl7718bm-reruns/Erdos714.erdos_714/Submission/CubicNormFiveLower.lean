import Submission.CubicNormFive

/-!
A genuine7/4 lower exponent for K55 and all larger balanced bicliques,
obtained from cubic norm graphs. This remains below the conjectured exponent.
-/
noncomputable section
open Classical SimpleGraph Filter
namespace Erdos714CubicNormLower

abbrev Forbidden := completeBipartiteGraph (Fin 5) (Fin 5)

theorem extremal_mono : Monotone (fun n => extremalNumber n Forbidden) := by
  apply Erdos714Reduction.extremalNumber_monotone_of_no_isolated
  intro v
  cases v with
  | inl v => exact ⟨Sum.inr 0,by simp [Forbidden]⟩
  | inr v => exact ⟨Sum.inl 0,by simp [Forbidden]⟩

/-- The precise finite graph construction bound. -/
theorem finite_lower (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Fintype F] [Fintype E] (hdim : Module.finrank F E = 3) :
    Fintype.card F^3*(Fintype.card F-1)*(Fintype.card F^3-1) ≤
      extremalNumber (2*(Fintype.card F^3*(Fintype.card F-1))) Forbidden := by
  have h := card_edgeFinset_le_extremalNumber (Erdos714CubicSegre.normGraph_free hdim)
  rw [Erdos714CubicSegre.normGraph_edges hdim] at h
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_units,
    Module.card_eq_pow_finrank (K := F) (V := E),hdim,two_mul] using h

/-- Cubic extensions over fields of order2^k exist at every positive k. -/
theorem dyadic_lower (k : ℕ) (hk : k ≠ 0) :
    (2^k)^3*(2^k-1)*((2^k)^3-1) ≤
      extremalNumber (2*((2^k)^3*(2^k-1))) Forbidden := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 k
  let E := FiniteField.Extension F 2 3
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype E := Fintype.ofFinite E
  have hc : Fintype.card F = 2^k := by
    rw [Fintype.card_eq_nat_card,GaloisField.card 2 k hk]
  have hd : Module.finrank F E = 3 := FiniteField.finrank_extension F 2 3
  simpa only [hc] using finite_lower F E hd

lemma count_lower (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ)^7/4 ≤ ((q^3*(q-1)*(q^3-1) : ℕ) : ℝ) := by
  have hq₁ : 1 ≤ q := by omega
  have hq₃ : 1 ≤ q^3 := Nat.one_le_pow 3 q hq₁
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hc : (2 : ℝ) ≤ (q : ℝ)^3 := by
    calc
      _ ≤ (2 : ℝ)^3 := by norm_num
      _ ≤ (q : ℝ)^3 := by gcongr
  norm_num only [Nat.cast_mul,Nat.cast_sub hq₁,Nat.cast_sub hq₃,Nat.cast_pow,Nat.cast_one]
  have h₁ : (q : ℝ)/2 ≤ (q : ℝ)-1 := by linarith
  have h₂ : (q : ℝ)^3/2 ≤ (q : ℝ)^3-1 := by linarith
  have hh := mul_le_mul h₁ h₂ (by positivity : (0 : ℝ) ≤ (q : ℝ)^3/2)
    (by linarith : (0 : ℝ) ≤ (q : ℝ)-1)
  have hh' := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ (q : ℝ)^3)
  nlinarith only [hh']

lemma fourth_power_rpow (q : ℝ) (hq : 0 ≤ q) :
    (2*q^4)^((7 : ℝ)/4) ≤ 4*q^7 := by
  rw [Real.mul_rpow (by norm_num) (by positivity),← Real.rpow_natCast_mul hq]
  norm_num
  have h : (2 : ℝ)^((7 : ℝ)/4) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- A bound at a geometric sequence with a constant independent of k. -/
theorem geometric_lower (k : ℕ) :
    (1/16 : ℝ)*((32*16^k : ℕ) : ℝ)^((7 : ℝ)/4) ≤
      (extremalNumber (32*16^k) Forbidden : ℝ) := by
  let q := 2^(k+1)
  have hq : 2 ≤ q := by
    have h : 1 ≤ (2 : ℕ)^k := Nat.one_le_pow k 2 (by norm_num)
    dsimp [q]
    rw [pow_succ]
    omega
  have hp : ((2 : ℕ)^k)^4 = 16^k := by
    rw [← pow_mul,Nat.mul_comm k 4,pow_mul]
    norm_num
  have hsize : 2*q^4 = 32*16^k := by
    dsimp [q]
    rw [pow_succ 2 k,mul_pow,hp]
    ring
  have hsmall : 2*(q^3*(q-1)) ≤ 2*q^4 := by
    calc
      _ ≤ 2*(q^3*q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le q 1))
      _ = _ := by ring
  have hn := (dyadic_lower (k+1) (by omega)).trans (extremal_mono hsmall)
  have he : ((q^3*(q-1)*(q^3-1) : ℕ) : ℝ) ≤
      (extremalNumber (2*q^4) Forbidden : ℝ) := by exact_mod_cast hn
  have hlo := (count_lower q hq).trans he
  have hup := fourth_power_rpow (q : ℝ) (by positivity)
  rw [← hsize]
  norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  nlinarith only [hlo,hup]

/-- Positive eventual7/4 exponent for K55. This is weaker than9/5. -/
theorem fifth_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c*(n : ℝ)^((7 : ℝ)/4) ≤ (extremalNumber n Forbidden : ℝ) := by
  have hm : Monotone (fun n : ℕ => (extremalNumber n Forbidden : ℝ)) := by
    intro n m hnm
    exact Nat.cast_le.mpr (extremal_mono hnm)
  exact Erdos714Reduction.lower_bound_from_scaled_sizes _ hm ((7 : ℝ)/4)
    (by norm_num) 32 16 (by norm_num) (by norm_num) (1/16) (by norm_num) geometric_lower

/-- The same7/4 exponent holds for every r at least five. -/
theorem larger_lower (r : ℕ) (hr : 5 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c*(n : ℝ)^((7 : ℝ)/4) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  let e : Fin 5 ↪ Fin r := Fin.castLEEmb hr
  have hc : Forbidden ⊑ completeBipartiteGraph (Fin r) (Fin r) := by
    refine ⟨⟨⟨Sum.map e e,?_⟩,Sum.map_injective.mpr ⟨e.injective,e.injective⟩⟩⟩
    intro x y hxy
    cases x <;> cases y <;> simp_all [Forbidden]
  obtain ⟨c,hc₀,hn⟩ := fifth_lower
  refine ⟨c,hc₀,?_⟩
  filter_upwards [hn] with n hn
  exact hn.trans (Nat.cast_le.mpr hc.extremalNumber_le)

#print axioms finite_lower
#print axioms dyadic_lower
#print axioms fifth_lower
#print axioms larger_lower
end Erdos714CubicNormLower
