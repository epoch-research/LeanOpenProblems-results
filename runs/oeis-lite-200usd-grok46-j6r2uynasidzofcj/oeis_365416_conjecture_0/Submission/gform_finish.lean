import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

open Int

/-! Finish `gForm = ±1` via the (93,26)-identity and a cubic-form lower bound. -/

def G (k c : ℤ) : ℤ := k ^ 3 + 108 * k * c ^ 2 - 432 * c ^ 3

lemma G_93_26 : G 93 26 = 1269 := by native_decide

lemma G_identity (k c : ℤ) :
    (26 : ℤ) ^ 3 * G k c - 1269 * c ^ 3 =
      (26 * k - 93 * c) * (98955 * c ^ 2 + 279 * c * (26 * k - 93 * c) +
        (26 * k - 93 * c) ^ 2) := by
  simp [G]; ring

/-- The auxiliary form appearing after the substitution `c = 78m - t`. -/
def J (m c : ℤ) : ℤ := m ^ 3 - 279 * c * m ^ 2 + 98955 * c ^ 2 * m - 1269 * c ^ 3

lemma J_pos_c1 {m : ℤ} (hm : 1 ≤ m) : 97408 ≤ J m 1 := by
  have h1 : J 1 1 = 97408 := by native_decide
  have hinter : ∀ t : ℤ, 0 ≤ t → J (1 + t) 1 - J 1 1 =
      t * (3 * t ^ 2 + (6 - 558) * t + (3 - 558 + 98955)) := by
    intro t _; simp [J]; ring
  -- Direct: derivative of f(m)=m^3-279m^2+98955m-1269 is always positive.
  have hf' : ∀ m : ℤ, 0 < 3 * m ^ 2 - 558 * m + 98955 := by
    intro m
    nlinarith [sq_nonneg (m - 93), sq_nonneg (m : ℤ)]
  -- Compare to m=1 by telescoping via the identity
  -- f(m)-f(1)=(m-1)(m^2-278m+98677)
  have hdiff : J m 1 - J 1 1 = (m - 1) * (m ^ 2 - 278 * m + 98677) := by
    simp [J]; ring
  have hquad : 0 ≤ m ^ 2 - 278 * m + 98677 := by
    nlinarith [sq_nonneg (m - 139)]
  have : 0 ≤ J m 1 - J 1 1 := by
    have : 0 ≤ m - 1 := by omega
    nlinarith
  linarith

lemma J_m1_small_c {c : ℤ} (hc : 1 ≤ c) (hc77 : c ≤ 77) : 97408 ≤ J 1 c := by
  -- Check c = 1..77 by a computable predicate.
  have hrange : ∀ n : ℕ, 1 ≤ n → n ≤ 77 → 97408 ≤ J 1 n := by
    intro n hn1 hn77
    have : n ≤ 77 := hn77
    interval_cases n <;> native_decide
  have hcN : (c.toNat : ℤ) = c := Int.toNat_of_nonneg (by omega)
  have h1 : 1 ≤ c.toNat := by omega
  have h77 : c.toNat ≤ 77 := by omega
  simpa [hcN] using hrange c.toNat h1 h77

lemma J_m1_large_c {c : ℤ} (hc : 78 ≤ c) : J 1 c ≤ -186029 := by
  have hdiff : J 1 c - J 1 78 = (c - 78) * (-1269 * (c ^ 2 + 78 * c + 78 ^ 2) +
      98955 * (c + 78) - 279) := by
    simp [J]; ring
  have h78 : J 1 78 = -186029 := by native_decide
  have hneg : -1269 * (c ^ 2 + 78 * c + 78 ^ 2) + 98955 * (c + 78) - 279 ≤ 0 := by
    have hc2 : (78 : ℤ) ≤ c := hc
    nlinarith [sq_nonneg (c - 78), sq_nonneg c]
  have : J 1 c ≤ J 1 78 := by
    have : 0 ≤ c - 78 := by omega
    nlinarith
  linarith

lemma abs_J_m1 {c : ℤ} (hc : 1 ≤ c) : 97408 ≤ |J 1 c| := by
  rcases le_or_gt c 77 with h | h
  · have := J_m1_small_c hc h
    have : 0 ≤ J 1 c := by linarith
    rwa [abs_of_nonneg this]
  · have : 78 ≤ c := by omega
    have := J_m1_large_c this
    have : J 1 c ≤ 0 := by linarith
    rw [abs_of_nonpos this]
    linarith

/-- Crude lower bound: `|J m c| ≥ 97408` for positive `m, c`. -/
lemma abs_J_ge {m c : ℤ} (hm : 1 ≤ m) (hc : 1 ≤ c) : 97408 ≤ |J m c| := by
  rcases eq_or_ne m 1 with rfl | hm1
  · exact abs_J_m1 hc
  rcases eq_or_ne c 1 with rfl | hc1
  · have := J_pos_c1 hm
    have : 0 ≤ J m 1 := by linarith
    rwa [abs_of_nonneg this]
  -- m ≥ 2, c ≥ 2
  have hm2 : 2 ≤ m := by omega
  have hc2 : 2 ≤ c := by omega
  -- Factor out gcd later if needed. Direct estimate via homogeniety:
  -- |J| / c^3 = |z^3 - 279 z^2 + 98955 z - 1269| with z = m/c ≥ 2/c > 0.
  -- Use integer comparison: if m ≥ 2c then z ≥ 2, j(2) is huge.
  by_cases hge : 2 * c ≤ m
  · have hJ : J m c = m * (m ^ 2 - 279 * c * m + 98955 * c ^ 2) - 1269 * c ^ 3 := by
      simp [J]; ring
    have hquad : 0 ≤ m ^ 2 - 279 * c * m + 98955 * c ^ 2 := by
      nlinarith [sq_nonneg (m - 140 * c)]
    have : (2 : ℤ) ^ 3 * c ^ 3 ≤ m ^ 3 := by
      have : (2 * c) ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ (by nlinarith) hge 3
      have : (2 * c) ^ 3 = 8 * c ^ 3 := by ring
      linarith
    -- J ≥ 8c^3 - 279 c (something wait): lower-bound by dropping positive m^3 term carefully
    -- J = m^3 - 279 c m^2 + 98955 c^2 m - 1269 c^3
    --   ≥ m^2 (m - 279 c) + 98955 c^2 m - 1269 c^3
    have : 97408 ≤ |J m c| := by
      -- For m ≥ 2c ≥ 4, the dominant term is m^3.
      -- m - 279c could be negative if m < 279c. Since m can be 2c, this is negative.
      -- Use |J| ≥ 1269 c^3 - m^3 - 279 c m^2 - 98955 c^2 m if J negative, etc.
      -- Check a compact box with native_decide is not possible for unbounded.
      -- Instead: write J = c^3 j(m/c) and use that the only real root is near 1/78,
      -- so for z ≥ 2/c ≥ 2/∞ = 0 but z ≥ 2/c, for c ≥ 2, z ≥ 1? No z ≥ 2c/c = 2.
      -- YES: this branch is m ≥ 2c so z ≥ 2.
      have hz : (2 : ℤ) ≤ m / c ∨ True := by omega
      have hlower : (0 : ℤ) ≤ J m c := by
        -- j(2) = 8 - 1116 + 197910 - 1269 > 0 and j increasing on [2,∞)
        have : (0 : ℤ) ≤ m ^ 3 + 98955 * c ^ 2 * m - 279 * c * m ^ 2 - 1269 * c ^ 3 := by
          nlinarith [sq_nonneg (m - 2 * c), sq_nonneg m, sq_nonneg c,
            pow_nonneg (by omega : (0 : ℤ) ≤ m) 3, pow_nonneg (by omega : (0 : ℤ) ≤ c) 3]
        simpa [J] using this
      have hbig : 97408 ≤ J m c := by
        -- J ≥ j(2) c^3 = (8 - 1116 + 197910 - 1269) c^3 = 196533 c^3
        have : (196533 : ℤ) * c ^ 3 ≤ J m c := by
          have hm' : (2 : ℤ) * c ≤ m := hge
          nlinarith [sq_nonneg (m - 2 * c), sq_nonneg m, sq_nonneg c]
        have : (196533 : ℤ) * 4 ≤ 196533 * c ^ 3 := by
          have : (4 : ℤ) ≤ c ^ 3 := by
            have : (2 : ℤ) ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ (by omega) hc2 3
            simpa using this
          nlinarith
        linarith
      rwa [abs_of_nonneg hlower]
    exact this
  · -- m < 2c, m ≥ 2, c ≥ 2
    -- The dangerous region is m/c ≈ 1/78. Then m = 1 for c < 156.
    have hlt : m ≤ 2 * c - 1 := by omega
    -- For c ≤ 200 we brute-force via a reduction to ℕ.
    -- For c ≥ 79, if m ≤ c/77 then z ≤ 1/77? We'll split.
    by_cases hc200 : c ≤ 200
    · -- Finite check: 2 ≤ m ≤ 2c-1, 2 ≤ c ≤ 200. Too many for interval_cases.
      -- Use that |78m - c| ≥ 1 when (m,c) ≠ k(1,78), and estimate.
      have : 97408 ≤ |J m c| := by
        -- Fall back to a direct estimate using 78m vs c.
        have hne : ¬ (m = 1 ∧ c = 78) := by omega
        -- We'll prove a weaker computable bound in the next lemma; for now use nlinarith
        -- on the homogenized polynomial when |78m-c|≥1.
        set d := 78 * m - c
        have hJ' : J m c = d * (m ^ 2 - 201 * m * c + 1269 * c ^ 2) + (-186029 + 186029) * m ^ 3
            + J m c - d * (m ^ 2 - 201 * m * c + 1269 * c ^ 2) := by ring
        -- Direct expansion: J(m,c) - J(m, 78m) wait c vs 78m.
        -- J(m,c) = m^3 - 279 c m^2 + 98955 c^2 m - 1269 c^3
        -- J(m, 78m) doesn't make sense (second arg 78m).
        -- Compare to J(1,78)*m^3 when c=78m: J(m,78m)= m^3 J(1,78)= -186029 m^3
        -- Write c = 78m - d, then J(m, 78m-d) = H-related.
        -- Here d = 78m - c, J(m,c) = J(m, 78m - d).
        have hexp : J m (78 * m - d) =
            -186029 * m ^ 3 + 7725087 * m ^ 2 * d - 197991 * m * d ^ 2 + 1269 * d ^ 3 := by
          simp [J, d]; ring
        have hddef : 78 * m - d = c := by omega
        rw [← hddef, hexp]
        -- d = 78m - c, |d| ≥ 1 (if d=0 then c=78m, gcd ≥ m ≥ 2, J = -186029 m^3)
        by_cases hd0 : d = 0
        · subst hd0
          have : J m (78 * m) = -186029 * m ^ 3 := by simp [J]; ring
          -- but we rewrote already
          have : (-186029 : ℤ) * m ^ 3 ≤ -186029 * 8 := by
            have : (8 : ℤ) ≤ m ^ 3 := by
              have : (2 : ℤ) ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ (by omega) hm2 3
              simpa using this
            nlinarith
          have hneg : (-186029 : ℤ) * m ^ 3 ≤ 0 := by
            nlinarith [pow_nonneg (by omega : (0 : ℤ) ≤ m) 3]
          rw [abs_of_nonpos]
          · nlinarith
          · nlinarith
        · have hdabs : 1 ≤ |d| := abs_pos.mpr hd0 ▸ (by omega : (0 : ℤ) < 1 ∨ True) |> fun _ =>
            Int.one_le_abs hd0
          -- For |d|≥1 and m≥2, the value is large; check d small vs large
          -- Use | -186029 m^3 + O(m^2 d) | ≥ 97408
          have : 97408 ≤ | -186029 * m ^ 3 + 7725087 * m ^ 2 * d
              - 197991 * m * d ^ 2 + 1269 * d ^ 3 | := by
            -- Bound by cases on |d| vs m
            by_cases hdb : |d| ≤ 77 * m
            · -- then c = 78m-d ≥ m, still large cubic
              -- native-style: the polynomial in (m,d) has min 97408 on this region
              -- for 2 ≤ m, 1 ≤ |d| ≤ 77m and c=78m-d ∈ [2,200]
              have hc' : 1 ≤ 78 * m - d := by
                have : c = 78 * m - d := hddef.symm
                omega
              -- Since c ≤ 200 in this branch:
              have hdc_bound : |d| ≤ 78 * m - 2 := by
                have : 2 ≤ c := hc2
                have : c = 78 * m - d := hddef.symm
                have : 2 ≤ 78 * m - d := by omega
                omega
              -- Finite: m ≤ (c+ |d|)/78 ≤ (200+77m)/78 so m ≤ 200/1 = 200
              have hmbound : m ≤ 200 := by
                have : c ≤ 200 := hc200
                have : c = 78 * m - d := hddef.symm
                -- m = (c+d)/78 ≤ (200 + 77m)/78
                -- 78m ≤ 200 + 77m ⇒ m ≤ 200
                have : 78 * m = c + d := by omega
                nlinarith [abs_le.mp hdb, abs_nonneg d]
              -- Now m ∈ [2,200], c ∈ [2,200]: use a decidable sweep via ℕ
              have hmN : m.toNat ≤ 200 := by omega
              have hcN : c.toNat ≤ 200 := by omega
              have hm2N : 2 ≤ m.toNat := by omega
              have hc2N : 2 ≤ c.toNat := by omega
              have heqm : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (by omega)
              have heqc : (c.toNat : ℤ) = c := Int.toNat_of_nonneg (by omega)
              -- Prove by computing a Bool checker
              have hcheck : ∀ a b : ℕ, 2 ≤ a → a ≤ 200 → 2 ≤ b → b ≤ 200 →
                  97408 ≤ |(J a b : ℤ)| := by
                intro a b ha2 ha200 hb2 hb200
                -- Too large to interval_cases both. Use a coarser bound.
                -- |J| ≥ 1 is trivial; we need 97408.
                -- Evaluate the homogeneous form lower bound using
                -- |78a - b| ≥ 1 and a≥2.
                set dd : ℤ := 78 * (a : ℤ) - (b : ℤ)
                have hne' : dd ≠ 0 := by
                  intro h0
                  have : (b : ℤ) = 78 * (a : ℤ) := by omega
                  have : b = 78 * a := by exact_mod_cast this
                  have : 200 < b := by
                    have : 2 ≤ a := ha2
                    nlinarith
                  omega
                have : 97408 ≤ |J (a : ℤ) (b : ℤ)| := by
                  -- last resort for the finite box: this will be replaced
                  -- by a compiled checker. For compilation we use a dummy
                  -- that we'll prove properly below.
                  have ha' := ha2
                  have hb' := hb2
                  -- Use that for a≥2,b≥2, |J| is at least J(2,2)
                  have h22 : |J 2 2| = 195533 := by native_decide
                  -- Not always J(2,2) is the min. J(2,156)=8*(-186029)? 
                  -- b≤200, 78*2=156, J(2,156)=8*J(1,78)=-1488232
                  -- Still ≥97408.
                  -- We'll prove |J a b| ≥ 97408 for this box by noting
                  -- the only small values are near (1,78) which is excluded.
                  omega -- PLACEHOLDER, will not work
                exact this
              simpa [heqm, heqc] using
                hcheck m.toNat c.toNat hm2N hmN hc2N hcN
            · -- |d| ≥ 77m+1, then c = 78m-d ≤ m-1, and z = m/c ≥ m/(m-1) ≥ 1
              have : 97408 ≤ | -186029 * m ^ 3 + 7725087 * m ^ 2 * d
                  - 197991 * m * d ^ 2 + 1269 * d ^ 3 | := by
                omega -- placeholder
              exact this
          simpa using this
        exact this
      exact this
    · -- c ≥ 201, m ≥ 2, m ≤ 2c-1
      have : 97408 ≤ |J m c| := by
        omega -- placeholder
      exact this
