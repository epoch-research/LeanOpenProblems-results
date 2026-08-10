import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 4000000

namespace DC

/-- centered rounding for integers: there is `a` with `2*(p - a*t)` in `(-t, t]`. -/
theorem centered (p t : ℤ) (ht : 0 < t) :
    ∃ a : ℤ, -t < 2*(p - t*a) ∧ 2*(p - t*a) ≤ t := by
  have hr : 0 ≤ p % t := Int.emod_nonneg p (ne_of_gt ht)
  have hr2 : p % t < t := Int.emod_lt_of_pos p ht
  have hdm : t * (p / t) + p % t = p := Int.ediv_add_emod p t
  by_cases h : 2 * (p % t) ≤ t
  · exact ⟨p / t, by omega⟩
  · exact ⟨p / t + 1, by constructor <;> nlinarith [hr, hr2, hdm, h]⟩

/-- Core Davenport–Cassels descent for three squares. -/
theorem core : ∀ T : ℕ, ∀ p q r n : ℤ, p^2 + q^2 + r^2 = n * (T:ℤ)^2 → 0 < T →
    ∃ x y z : ℤ, x^2 + y^2 + z^2 = n := by
  intro T
  induction T using Nat.strong_induction_on with
  | _ T ih =>
    intro p q r n hpqr hT
    rcases Nat.lt_or_ge T 2 with hlt | hge
    · -- T = 1
      have : T = 1 := by omega
      subst this
      exact ⟨p, q, r, by simpa using hpqr⟩
    · -- T ≥ 2
      set t : ℤ := (T:ℤ) with htdef
      have ht : 0 < t := by positivity
      obtain ⟨a, ha1, ha2⟩ := centered p t ht
      obtain ⟨b, hb1, hb2⟩ := centered q t ht
      obtain ⟨c, hc1, hc2⟩ := centered r t ht
      set A : ℤ := p - t*a with hA
      set B : ℤ := q - t*b with hB
      set C : ℤ := r - t*c with hC
      set S : ℤ := A^2 + B^2 + C^2 with hS
      -- t ∣ S
      have hdvd : t ∣ S := by
        have : S = (p^2+q^2+r^2) - 2*t*(a*p+b*q+c*r) + t^2*(a^2+b^2+c^2) := by
          rw [hS, hA, hB, hC]; ring
        rw [this, hpqr]
        have : n * t^2 - 2*t*(a*p+b*q+c*r) + t^2*(a^2+b^2+c^2)
             = t * (n*t - 2*(a*p+b*q+c*r) + t*(a^2+b^2+c^2)) := by ring
        rw [this]; exact Dvd.intro _ rfl
      obtain ⟨M, hM⟩ := hdvd
      -- bounds: 4*A^2 ≤ t^2 etc
      have hAb : 4*A^2 ≤ t^2 := by rw [hA]; nlinarith [ha1, ha2]
      have hBb : 4*B^2 ≤ t^2 := by rw [hB]; nlinarith [hb1, hb2]
      have hCb : 4*C^2 ≤ t^2 := by rw [hC]; nlinarith [hc1, hc2]
      have hSle : 4*S ≤ 3*t^2 := by rw [hS]; linarith
      have hSnn : 0 ≤ S := by rw [hS]; positivity
      rcases eq_or_lt_of_le hSnn with hS0 | hSpos
      · -- S = 0 → A=B=C=0 → (a,b,c) is the rep
        have hA0 : A = 0 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, hS]
        have hB0 : B = 0 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, hS]
        have hC0 : C = 0 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, hS]
        refine ⟨a, b, c, ?_⟩
        have hp : p = t*a := by linarith [hA, hA0]
        have hq : q = t*b := by linarith [hB, hB0]
        have hr : r = t*c := by linarith [hC, hC0]
        have : t^2*(a^2+b^2+c^2) = n*t^2 := by rw [← hpqr, hp, hq, hr]; ring
        have ht2 : (0:ℤ) < t^2 := by positivity
        nlinarith [this, ht2]
      · -- S > 0, M = S/t, 0 < M < T
        have hMpos : 0 < M := by
          by_contra hcon
          push_neg at hcon
          nlinarith [hM, hSpos, mul_nonpos_of_nonneg_of_nonpos ht.le hcon]
        have hMlt : M < t := by nlinarith [hM, hSle, ht, hMpos]
        -- new representation
        set N : ℤ := a^2 + b^2 + c^2 - n with hN
        set p' : ℤ := a*M + N*A with hp'
        set q' : ℤ := b*M + N*B with hq'
        set r' : ℤ := c*M + N*C with hr'
        have key : (t^2) * (p'^2 + q'^2 + r'^2) = (t^2) * (n * M^2) := by
          have e1 : t*p' = a*S + N*A*t := by rw [hp', hM]; ring
          have e2 : t*q' = b*S + N*B*t := by rw [hq', hM]; ring
          have e3 : t*r' = c*S + N*C*t := by rw [hr', hM]; ring
          have hSMt : S = t*M := hM
          -- identity: (a S + N A t)^2 + ... = n S^2 + (p^2+q^2+r^2 - n t^2) N S
          have hid : (a*S+N*A*t)^2 + (b*S+N*B*t)^2 + (c*S+N*C*t)^2
                   = n*S^2 + (p^2+q^2+r^2 - n*t^2)*N*S := by
            rw [hS, hA, hB, hC, hN]; ring
          have : t^2*(p'^2+q'^2+r'^2) = (t*p')^2+(t*q')^2+(t*r')^2 := by ring
          rw [this, e1, e2, e3, hid, hpqr]
          rw [hSMt]; ring
        have ht2 : (0:ℤ) < t^2 := by positivity
        have hfin : p'^2 + q'^2 + r'^2 = n * M^2 := by
          have := mul_left_cancel₀ (ne_of_gt ht2) key
          exact this
        -- M as a natural number < T
        have hMnat : M.toNat < T := by
          have : M < (T:ℤ) := hMlt
          omega
        have hMeq : ((M.toNat : ℤ)) = M := Int.toNat_of_nonneg hMpos.le
        exact ih M.toNat hMnat p' q' r' n (by rw [hMeq]; exact hfin) (by omega)

end DC
