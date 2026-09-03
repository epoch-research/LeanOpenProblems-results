import FormalConjecturesUtil

/-! Necessary two-adic conditions on a universal fixed multiplier for squaring
quartic targets. These conditions do not assert that any multiplier works. -/
namespace Erdos322Research.QuarticSquareMultiplier

/-- Rational representability by four fourth powers. -/
def Represented (n : ℕ) : Prop := ∃ a : Fin 4 → ℚ, ∑ i, a i^4 = (n : ℚ)

private lemma fourth_mod_sixteen (x : ℕ) : x^4%16 ≤ 1 := by
  have h : ∀ r : Fin 16, (r.val^4)%16 ≤ 1 := by decide
  rw [Nat.pow_mod]
  exact h ⟨x%16,Nat.mod_lt _ (by decide)⟩

private lemma sum_fourth_mod_sixteen (a : Fin 4 → ℕ) : (∑ i, a i^4)%16 ≤ 4 := by
  have h0 := fourth_mod_sixteen (a 0)
  have h1 := fourth_mod_sixteen (a 1)
  have h2 := fourth_mod_sixteen (a 2)
  have h3 := fourth_mod_sixteen (a 3)
  simp only [Fin.sum_univ_four]
  omega

private lemma even_all {a : Fin 4 → ℕ} (h : 16 ∣ ∑ i, a i^4) : ∀ i, 2 ∣ a i := by
  have h0 := fourth_mod_sixteen (a 0)
  have h1 := fourth_mod_sixteen (a 1)
  have h2 := fourth_mod_sixteen (a 2)
  have h3 := fourth_mod_sixteen (a 3)
  have hs : (a 0)^4%16+(a 1)^4%16+(a 2)^4%16+(a 3)^4%16 = 0 := by
    have hh := Nat.mod_eq_zero_of_dvd h
    simp only [Fin.sum_univ_four] at hh
    omega
  intro i
  have hi : (a i)^4%16 = 0 := by
    fin_cases i
    · change (a 0)^4%16 = 0
      omega
    · change (a 1)^4%16 = 0
      omega
    · change (a 2)^4%16 = 0
      omega
    · change (a 3)^4%16 = 0
      omega
  have hd : 2 ∣ (a i)^4 := dvd_trans (by norm_num : 2 ∣ 16) (Nat.dvd_of_mod_eq_zero hi)
  exact Nat.prime_two.dvd_of_dvd_pow hd

private theorem no_scaled_representation {n : ℕ} (hn : 4 < n%16) :
    ∀ d : ℕ, 0 < d → ∀ a : Fin 4 → ℕ, ∑ i, a i^4 ≠ n*d^4 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd a he
    by_cases heven : 2 ∣ d
    · have h16 : 16 ∣ n*d^4 := by
        obtain ⟨e,rfl⟩ := heven
        refine ⟨n*e^4,?_⟩
        ring
      have ha := even_all (he ▸ h16)
      have hsmall : d/2 < d := Nat.div_lt_self hd (by decide)
      have hd' : 0 < d/2 := by
        have h2 : 2 ≤ d := Nat.le_of_dvd hd heven
        omega
      apply ih (d/2) hsmall hd' (fun i ↦ a i/2)
      have had (i : Fin 4) : 2*(a i/2)=a i := Nat.mul_div_cancel' (ha i)
      have hdd : 2*(d/2)=d := Nat.mul_div_cancel' heven
      have hh : 16*(∑ i, (a i/2)^4) = 16*(n*(d/2)^4) := by
        calc
          16*(∑ i, (a i/2)^4) = ∑ i, (2*(a i/2))^4 := by
            simp only [Fin.sum_univ_four]
            ring
          _ = ∑ i, a i^4 := by simp only [had]
          _ = n*d^4 := he
          _ = 16*(n*(d/2)^4) := by
            conv_lhs => rw [← hdd]
            ring
      omega
    · have hpow : d^4%16=1 := by
        have hmod : d%16 < 16 := Nat.mod_lt _ (by decide)
        have hodd : d%2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using heven
        have hodd' : (d%16)%2 ≠ 0 := by omega
        rw [Nat.pow_mod]
        interval_cases d%16 <;> norm_num at *
      have h := sum_fourth_mod_sixteen a
      rw [he,Nat.mul_mod,hpow] at h
      omega

private lemma rational_common_denominator (a : Fin 4 → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ b : Fin 4 → ℤ, ∀ i, (b i : ℚ) = d*a i := by
  let d := ∏ i, (a i).den
  have hd : 0 < d := Finset.prod_pos (fun i _ ↦ (a i).den_pos)
  refine ⟨d,hd,fun i ↦ (a i).num * (d/(a i).den),?_⟩
  intro i
  have hdiv : (a i).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hmul : (a i).den*(d/(a i).den)=d := Nat.mul_div_cancel' hdiv
  have hm : ((a i).den : ℚ)*(d/(a i).den : ℕ)=d := by exact_mod_cast hmul
  push_cast
  calc
    ((a i).num : ℚ)*(d/(a i).den : ℕ) =
        (a i * (a i).den)*(d/(a i).den : ℕ) := by rw [Rat.mul_den_eq_num]
    _ = (d : ℚ)*a i := by rw [mul_assoc,hm,mul_comm]

theorem represented_mod_sixteen {n : ℕ} (hn : Represented n) : n%16 ≤ 4 := by
  by_contra hh
  have hbad : 4 < n%16 := by omega
  obtain ⟨a,he⟩ := hn
  obtain ⟨d,hd,b,hb⟩ := rational_common_denominator a
  have hq : ∑ i, (b i : ℚ)^4 = (n : ℚ)*d^4 := by
    simp_rw [hb,mul_pow]
    rw [← Finset.mul_sum,he,mul_comm]
  have hz : ∑ i, (b i)^4 = (n : ℤ)*d^4 := by exact_mod_cast hq
  have hnabs : ∑ i, (b i).natAbs^4 = n*d^4 := by
    have hpow (i : Fin 4) : ((b i).natAbs : ℤ)^4 = (b i)^4 := by
      rw [Int.natCast_natAbs,← abs_pow,abs_of_nonneg (by positivity)]
    have hh : ∑ i, ((b i).natAbs : ℤ)^4 = (n : ℤ)*d^4 := by simpa only [hpow] using hz
    exact_mod_cast hh
  exact no_scaled_representation hbad d hd (fun i ↦ (b i).natAbs) hnabs

theorem represented_strip_sixteen {n : ℕ} (h : Represented (16*n)) : Represented n := by
  obtain ⟨a,ha⟩ := h
  refine ⟨fun i ↦ a i/2,?_⟩
  simp only [div_pow, ← Finset.sum_div]
  rw [ha]
  push_cast
  ring

private lemma residue_test (r : Fin 16) : r.val ≤ 4 → (4*r.val)%16 ≤ 4 →
    (9*r.val)%16 ≤ 4 → r.val=0 ∨ r.val=4 := by
  revert r
  decide

/-- Testing only the input norms `1`, `2`, and `3` already forces this residue. -/
theorem multiplier_mod_sixteen {C : ℕ} (h1 : Represented C)
    (h2 : Represented (4*C)) (h3 : Represented (9*C)) : C%16=0 ∨ C%16=4 := by
  apply residue_test ⟨C%16,Nat.mod_lt _ (by decide)⟩ (represented_mod_sixteen h1)
  · simpa only [Nat.mul_mod, Nat.mod_mod, Nat.reduceMod] using represented_mod_sixteen h2
  · simpa only [Nat.mul_mod, Nat.mod_mod, Nat.reduceMod] using represented_mod_sixteen h3

private theorem multiplier_mod_sixty_four {C : ℕ} (h1 : Represented C)
    (h2 : Represented (4*C)) (h3 : Represented (9*C)) (h16 : ¬16 ∣ C) : C%64=4 := by
  have hc : C%16=4 := (multiplier_mod_sixteen h1 h2 h3).resolve_left
    (fun hh ↦ h16 (Nat.dvd_of_mod_eq_zero hh))
  have h4 : 4 ∣ C := by omega
  have hquot : Represented (C/4) := by
    apply represented_strip_sixteen
    convert h2 using 1
    have hh := Nat.mul_div_cancel' h4
    omega
  have hh := represented_mod_sixteen hquot
  omega

/-- A necessary shape for any fixed multiplier that works on even these three
input norms. This theorem does not claim that multipliers of this shape work. -/
theorem necessary_multiplier_shape (C : ℕ) (hC : 0 < C)
    (h1 : Represented C) (h2 : Represented (4*C)) (h3 : Represented (9*C)) :
    ∃ m u : ℕ, C=16^m*u ∧ u%64=4 := by
  induction C using Nat.strong_induction_on with
  | h C ih =>
    by_cases hd : 16 ∣ C
    · have hp : 0 < C/16 := Nat.div_pos (Nat.le_of_dvd hC hd) (by decide)
      have hs : C/16 < C := Nat.div_lt_self hC (by decide)
      have hc : 16*(C/16)=C := Nat.mul_div_cancel' hd
      have hg (v : ℕ) (hv : Represented (v*C)) : Represented (v*(C/16)) := by
        apply represented_strip_sixteen
        convert hv using 1
        nlinarith [hc]
      obtain ⟨m,u,hu,hr⟩ := ih (C/16) hs hp
        (by simpa only [one_mul] using hg 1 (by simpa only [one_mul] using h1))
        (hg 4 h2) (hg 9 h3)
      refine ⟨m+1,u,?_,hr⟩
      rw [pow_succ']
      nlinarith [hc,hu]
    · exact ⟨0,C,by simp,multiplier_mod_sixty_four h1 h2 h3 hd⟩

/-- The level four is not restricted to its obvious equal-coordinate point. -/
theorem nontrivial_level_four_point :
    (13/27 : ℚ)^4+(13/27 : ℚ)^4+(21/27 : ℚ)^4+(37/27 : ℚ)^4=4 := by
  norm_num


/-- In particular, failure of integral representation at level `36` is not a
rational obstruction to a square multiplier equal to `4`. -/
theorem nontrivial_level_thirty_six_point :
    (1843/1489 : ℚ)^4+(2195/1489 : ℚ)^4+
      (3435/1489 : ℚ)^4+(1315/1489 : ℚ)^4=36 := by
  norm_num

/-- This is a proposed amplification property, not an established fact. -/
def UniversalSquareMultiplier (C : ℕ) : Prop :=
  ∀ n : ℕ, Represented n → Represented (C*n^2)

theorem universal_multiplier_shape {C : ℕ} (hC : 0 < C) (h : UniversalSquareMultiplier C) :
    ∃ m u : ℕ, C=16^m*u ∧ u%64=4 := by
  have h1 : Represented 1 := ⟨![1,0,0,0],by norm_num [Fin.sum_univ_succ]⟩
  have h2 : Represented 2 := ⟨![1,1,0,0],by norm_num [Fin.sum_univ_succ]⟩
  have h3 : Represented 3 := ⟨![1,1,1,0],by norm_num [Fin.sum_univ_succ]⟩
  apply necessary_multiplier_shape C hC
  · simpa only [one_pow, mul_one] using h 1 h1
  · simpa only [show (2 : ℕ)^2=4 by norm_num, mul_comm C 4] using h 2 h2
  · simpa only [show (3 : ℕ)^2=9 by norm_num, mul_comm C 9] using h 3 h3

end Erdos322Research.QuarticSquareMultiplier
