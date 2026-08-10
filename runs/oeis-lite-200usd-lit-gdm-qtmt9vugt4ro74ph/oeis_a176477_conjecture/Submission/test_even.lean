import FormalConjectures.Util.ProblemImports

open Nat

lemma P_M_pow4_sub_D_K_even (k : ℤ) (M : ℤ) :
  ∃ z : ℤ, (21 * (k+2)^3 + 22 * (k+2)^2 + 8 * (k+2) + 1) * M^4 - (2 * k + 5)^3 * (k + 3) * M = 2 * z := by
  have hk : k = 2 * (k / 2) + k % 2 := by omega
  have hM : M = 2 * (M / 2) + M % 2 := by omega
  have hk_mod : k % 2 = 0 ∨ k % 2 = 1 := by omega
  have hM_mod : M % 2 = 0 ∨ M % 2 = 1 := by omega
  generalize hk_div : k / 2 = k_div
  generalize hM_div : M / 2 = M_div
  rcases hk_mod with hk0 | hk1
  · rcases hM_mod with hM0 | hM1
    · use 1344*M_div^4*k_div^3+4736*M_div^4*k_div^2+5568*M_div^4*k_div+2184*M_div^4-128*M_div*k_div^4-672*M_div*k_div^3-1320*M_div*k_div^2-1150*M_div*k_div-375*M_div
      rw [hk, hM, hk0, hM0, hk_div, hM_div]
      ring
    · use 1344*M_div^4*k_div^3+4736*M_div^4*k_div^2+5568*M_div^4*k_div+2184*M_div^4+2688*M_div^3*k_div^3+9472*M_div^3*k_div^2+11136*M_div^3*k_div+4368*M_div^3+2016*M_div^2*k_div^3+7104*M_div^2*k_div^2+8352*M_div^2*k_div+3276*M_div^2-128*M_div*k_div^4+1048*M_div*k_div^2+1634*M_div*k_div+717*M_div-64*k_div^4-252*k_div^3-364*k_div^2-227*k_div-51
      rw [hk, hM, hk0, hM1, hk_div, hM_div]
      ring
  · rcases hM_mod with hM0 | hM1
    · use 1344*M_div^4*k_div^3+6752*M_div^4*k_div^2+11312*M_div^4*k_div+6320*M_div^4-128*M_div*k_div^4-928*M_div*k_div^3-2520*M_div*k_div^2-3038*M_div*k_div-1372*M_div
      rw [hk, hM, hk1, hM0, hk_div, hM_div]
      ring
    · use 1344*M_div^4*k_div^3+6752*M_div^4*k_div^2+11312*M_div^4*k_div+6320*M_div^4+2688*M_div^3*k_div^3+13504*M_div^3*k_div^2+22624*M_div^3*k_div+12640*M_div^3+2016*M_div^2*k_div^3+10128*M_div^2*k_div^2+16968*M_div^2*k_div+9480*M_div^2-128*M_div*k_div^4-256*M_div*k_div^3+856*M_div*k_div^2+2618*M_div*k_div+1788*M_div-64*k_div^4-380*k_div^3-838*k_div^2-812*k_div-291
      rw [hk, hM, hk1, hM1, hk_div, hM_div]
      ring
