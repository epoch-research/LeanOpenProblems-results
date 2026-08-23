import Submission.Isogeny

open Set Filter MeasureTheory
namespace Elliptic
local notation "r3" => Real.sqrt 3
local notation "r5" => Real.sqrt 5
local notation "r15" => Real.sqrt 15

lemma radical_bounds :
    (17320508/10000000 : ℝ) < r3 ∧ r3 < 17320509/10000000 ∧
    (22360679/10000000 : ℝ) < r5 ∧ r5 < 22360680/10000000 ∧
    (38729833/10000000 : ℝ) < r15 ∧ r15 < 38729834/10000000 := by
  have h3 : r3 ^ 2 = (3:ℝ) := by norm_num
  have h5 : r5 ^ 2 = (5:ℝ) := by norm_num
  have h15 : r15 ^ 2 = (15:ℝ) := by norm_num
  have hn3 : 0 ≤ r3 := Real.sqrt_nonneg _
  have hn5 : 0 ≤ r5 := Real.sqrt_nonneg _
  have hn15 : 0 ≤ r15 := Real.sqrt_nonneg _
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

noncomputable def cubC : ℝ := -8*r3/3 - 2*r5 + 5 + 4*r15/3
noncomputable def cubA : ℝ := -216 - 96*r5 + 124*r3 + 56*r15
noncomputable def cubB : ℝ := -2*r5 - 2 + 4*r3/3 + 4*r15/3
noncomputable def cubS (t : ℝ) : ℝ := cubC * t * (t^2+cubA)/(t^2+cubB)

lemma cub_constants_pos : 0 < cubC ∧ 0 < cubA ∧ 0 < cubB ∧ 0 < 3*cubB-cubA := by
  rcases radical_bounds with ⟨h3l,h3u,h5l,h5u,h15l,h15u⟩
  dsimp [cubC, cubA, cubB]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma cubS_deriv (t : ℝ) : HasDerivAt cubS
    (cubC * (t^4 + (3*cubB-cubA)*t^2 + cubA*cubB) / (t^2+cubB)^2) t := by
  have hb : t^2 + cubB ≠ 0 := by nlinarith [cub_constants_pos.2.2.1, sq_nonneg t]
  convert (((hasDerivAt_const t cubC).mul (hasDerivAt_id t)).mul
    (((hasDerivAt_id t).pow 2).add_const cubA)).div
      (((hasDerivAt_id t).pow 2).add_const cubB) hb using 1 <;>
    simp only [cubS, id_eq, Pi.mul_apply, Pi.add_apply, Pi.pow_apply] <;>
    field_simp [hb] <;> ring

lemma cubS_strictMono : StrictMono cubS := by
  apply strictMono_of_deriv_pos
  intro t
  rw [show deriv cubS t = cubC * (t^4 + (3*cubB-cubA)*t^2 + cubA*cubB) /
      (t^2+cubB)^2 from (cubS_deriv t).deriv]
  rcases cub_constants_pos with ⟨hc,ha,hb,hd⟩
  have hn : 0 < t^4 + (3*cubB-cubA)*t^2 + cubA*cubB := by
    have : 0 < cubA*cubB := mul_pos ha hb
    nlinarith [sq_nonneg t, sq_nonneg (t^2)]
  positivity

end Elliptic

namespace Elliptic
local notation "r3" => Real.sqrt 3
local notation "r5" => Real.sqrt 5
local notation "r15" => Real.sqrt 15

noncomputable def mm1 : ℝ := (16-7*r3-r15)/32
noncomputable def mm2 : ℝ := (16-7*r3+r15)/32
noncomputable def cubD (t : ℝ) : ℝ :=
  cubC * (t^4 + (3*cubB-cubA)*t^2 + cubA*cubB) / (t^2+cubB)^2
noncomputable def cubMul : ℝ := (r15-r3)/2

lemma radical_relations : r3^2 = 3 ∧ r5^2 = 5 ∧ r15 = r3*r5 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    norm_num

lemma test_hc0 : cubA^2*cubB^2*cubC^2 - cubB^4*cubMul^2 = 0 := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  dsimp [cubA, cubB, cubC, cubMul]
  rw [h15]
  have h33 : r3^3 = 3*r3 := by
    calc r3^3 = r3^2*r3 := by ring
         _ = 3*r3 := by rw [h3]
  have h34 : r3^4 = 9 := by
    calc r3^4 = (r3^2)^2 := by ring
         _ = 9 := by rw [h3]; norm_num
  have h35 : r3^5 = 9*r3 := by
    calc r3^5 = r3^4*r3 := by ring
         _ = 9*r3 := by rw [h34]
  have h36 : r3^6 = 27 := by
    calc r3^6 = (r3^2)^3 := by ring
         _ = 27 := by rw [h3]; norm_num
  have h53 : r5^3 = 5*r5 := by
    calc r5^3 = r5^2*r5 := by ring
         _ = 5*r5 := by rw [h5]
  have h54 : r5^4 = 25 := by
    calc r5^4 = (r5^2)^2 := by ring
         _ = 25 := by rw [h5]; norm_num
  have h55 : r5^5 = 25*r5 := by
    calc r5^5 = r5^4*r5 := by ring
         _ = 25*r5 := by rw [h54]
  have h56 : r5^6 = 125 := by
    calc r5^6 = (r5^2)^3 := by ring
         _ = 125 := by rw [h5]; norm_num
  ring_nf
  rw [h36, h35, h34, h33, h3, h56, h55, h54, h53, h5]
  ring


set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma cub_radicand_identity (t : ℝ) :
    cubD t ^ 2 * ((1+t^2)*(1+(1-mm1)*t^2)) =
      cubMul^2 * ((1+(cubS t)^2)*(1+(1-mm2)*(cubS t)^2)) := by
  rcases radical_relations with ⟨h3,h5,h15⟩
  have hcs : cubA^2*cubB^2*cubC^2 - cubB^4*cubMul^2 = 0 ∧
      -cubA^2*cubB^2*cubC^2*mm1 + cubA^2*cubB^2*cubC^2*mm2*cubMul^2 - 2*cubA^2*cubB^2*cubC^2*cubMul^2 + 2*cubA^2*cubB^2*cubC^2 - 2*cubA^2*cubB*cubC^2 + 6*cubA*cubB^2*cubC^2 - 4*cubB^3*cubMul^2 = 0 ∧
      cubA^4*cubC^4*mm2*cubMul^2 - cubA^4*cubC^4*cubMul^2 - cubA^2*cubB^2*cubC^2*mm1 + cubA^2*cubB^2*cubC^2 + 2*cubA^2*cubB*cubC^2*mm1 + 2*cubA^2*cubB*cubC^2*mm2*cubMul^2 - 4*cubA^2*cubB*cubC^2*cubMul^2 - 4*cubA^2*cubB*cubC^2 + cubA^2*cubC^2 - 6*cubA*cubB^2*cubC^2*mm1 + 2*cubA*cubB^2*cubC^2*mm2*cubMul^2 - 4*cubA*cubB^2*cubC^2*cubMul^2 + 12*cubA*cubB^2*cubC^2 - 4*cubA*cubB*cubC^2 + 9*cubB^2*cubC^2 - 6*cubB^2*cubMul^2 = 0 ∧
      4*cubA^3*cubC^4*mm2*cubMul^2 - 4*cubA^3*cubC^4*cubMul^2 + 2*cubA^2*cubB*cubC^2*mm1 - 2*cubA^2*cubB*cubC^2 - cubA^2*cubC^2*mm1 + cubA^2*cubC^2*mm2*cubMul^2 - 2*cubA^2*cubC^2*cubMul^2 + 2*cubA^2*cubC^2 - 6*cubA*cubB^2*cubC^2*mm1 + 6*cubA*cubB^2*cubC^2 + 4*cubA*cubB*cubC^2*mm1 + 4*cubA*cubB*cubC^2*mm2*cubMul^2 - 8*cubA*cubB*cubC^2*cubMul^2 - 8*cubA*cubB*cubC^2 - 2*cubA*cubC^2 - 9*cubB^2*cubC^2*mm1 + cubB^2*cubC^2*mm2*cubMul^2 - 2*cubB^2*cubC^2*cubMul^2 + 18*cubB^2*cubC^2 + 6*cubB*cubC^2 - 4*cubB*cubMul^2 = 0 ∧
      6*cubA^2*cubC^4*mm2*cubMul^2 - 6*cubA^2*cubC^4*cubMul^2 - cubA^2*cubC^2*mm1 + cubA^2*cubC^2 + 4*cubA*cubB*cubC^2*mm1 - 4*cubA*cubB*cubC^2 + 2*cubA*cubC^2*mm1 + 2*cubA*cubC^2*mm2*cubMul^2 - 4*cubA*cubC^2*cubMul^2 - 4*cubA*cubC^2 - 9*cubB^2*cubC^2*mm1 + 9*cubB^2*cubC^2 - 6*cubB*cubC^2*mm1 + 2*cubB*cubC^2*mm2*cubMul^2 - 4*cubB*cubC^2*cubMul^2 + 12*cubB*cubC^2 + cubC^2 - cubMul^2 = 0 ∧
      4*cubA*cubC^4*mm2*cubMul^2 - 4*cubA*cubC^4*cubMul^2 + 2*cubA*cubC^2*mm1 - 2*cubA*cubC^2 - 6*cubB*cubC^2*mm1 + 6*cubB*cubC^2 - cubC^2*mm1 + cubC^2*mm2*cubMul^2 - 2*cubC^2*cubMul^2 + 2*cubC^2 = 0 ∧
      cubC^4*mm2*cubMul^2 - cubC^4*cubMul^2 - cubC^2*mm1 + cubC^2 = 0 := by
    repeat' apply And.intro
    all_goals
      dsimp [cubA, cubB, cubC, cubMul, mm1, mm2]
      rw [h15]
      have h33 : r3^3 = 3*r3 := by
        calc r3^3 = r3^2*r3 := by ring
             _ = 3*r3 := by rw [h3]
      have h34 : r3^4 = 9 := by
        calc r3^4 = (r3^2)^2 := by ring
             _ = 9 := by rw [h3]; norm_num
      have h35 : r3^5 = 9*r3 := by
        calc r3^5 = r3^4*r3 := by ring
             _ = 9*r3 := by rw [h34]
      have h36 : r3^6 = 27 := by
        calc r3^6 = (r3^2)^3 := by ring
             _ = 27 := by rw [h3]; norm_num
      have h53 : r5^3 = 5*r5 := by
        calc r5^3 = r5^2*r5 := by ring
             _ = 5*r5 := by rw [h5]
      have h54 : r5^4 = 25 := by
        calc r5^4 = (r5^2)^2 := by ring
             _ = 25 := by rw [h5]; norm_num
      have h55 : r5^5 = 25*r5 := by
        calc r5^5 = r5^4*r5 := by ring
             _ = 25*r5 := by rw [h54]
      have h56 : r5^6 = 125 := by
        calc r5^6 = (r5^2)^3 := by ring
             _ = 125 := by rw [h5]; norm_num
      have h37 : r3^7 = 27*r3 := by
        calc r3^7 = r3^5*r3^2 := by ring
             _ = 27*r3 := by rw [h35, h3]; ring
      have h38 : r3^8 = 81 := by
        calc r3^8 = r3^6*r3^2 := by ring
             _ = 81 := by rw [h36, h3]; norm_num
      have h39 : r3^9 = 81*r3 := by
        calc r3^9 = r3^7*r3^2 := by ring
             _ = 81*r3 := by rw [h37, h3]; ring
      have h310 : r3^10 = 243 := by
        calc r3^10 = r3^8*r3^2 := by ring
             _ = 243 := by rw [h38, h3]; norm_num
      have h311 : r3^11 = 243*r3 := by
        calc r3^11 = r3^9*r3^2 := by ring
             _ = 243*r3 := by rw [h39, h3]; ring
      have h57 : r5^7 = 125*r5 := by
        calc r5^7 = r5^5*r5^2 := by ring
             _ = 125*r5 := by rw [h55, h5]; ring
      have h58 : r5^8 = 625 := by
        calc r5^8 = r5^6*r5^2 := by ring
             _ = 625 := by rw [h56, h5]; norm_num
      have h59 : r5^9 = 625*r5 := by
        calc r5^9 = r5^7*r5^2 := by ring
             _ = 625*r5 := by rw [h57, h5]; ring
      have h510 : r5^10 = 3125 := by
        calc r5^10 = r5^8*r5^2 := by ring
             _ = 3125 := by rw [h58, h5]; norm_num
      have h511 : r5^11 = 3125*r5 := by
        calc r5^11 = r5^9*r5^2 := by ring
             _ = 3125*r5 := by rw [h59, h5]; ring

      ring_nf
      simp only [h311, h310, h39, h38, h37, h36, h35, h34, h33, h3,
        h511, h510, h59, h58, h57, h56, h55, h54, h53, h5]
      ring
  rcases hcs with ⟨hc0,hc1,hc2,hc3,hc4,hc5,hc6⟩
  have hpoly :
      cubC^2 * (t^4+(3*cubB-cubA)*t^2+cubA*cubB)^2 *
          (1+t^2)*(1+(1-mm1)*t^2) =
        cubMul^2 * (((t^2+cubB)^2+cubC^2*t^2*(t^2+cubA)^2) *
          ((t^2+cubB)^2+(1-mm2)*cubC^2*t^2*(t^2+cubA)^2)) := by
    linear_combination hc0 + hc1*t^2 + hc2*t^4 + hc3*t^6 +
      hc4*t^8 + hc5*t^10 + hc6*t^12
  have hb : t^2+cubB ≠ 0 := by nlinarith [cub_constants_pos.2.2.1, sq_nonneg t]
  dsimp [cubD, cubS]
  field_simp [hb]
  convert hpoly using 1 <;> ring

lemma mm_bounds : 0 ≤ mm1 ∧ mm1 < 1 ∧ 0 ≤ mm2 ∧ mm2 < 1 := by
  rcases radical_bounds with ⟨h3l,h3u,h5l,h5u,h15l,h15u⟩
  dsimp [mm1, mm2]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma cubMul_pos : 0 < cubMul := by
  rcases radical_bounds with ⟨h3l,h3u,h5l,h5u,h15l,h15u⟩
  dsimp [cubMul]
  linarith

lemma cubD_pos (t : ℝ) : 0 < cubD t := by
  rcases cub_constants_pos with ⟨hc,ha,hb,hd⟩
  have hn : 0 < t^4 + (3*cubB-cubA)*t^2 + cubA*cubB := by
    have hab : 0 < cubA*cubB := mul_pos ha hb
    nlinarith [sq_nonneg t, sq_nonneg (t^2)]
  dsimp [cubD]
  positivity

lemma cub_pullback (t : ℝ) :
    (Real.sqrt ((1+(cubS t)^2)*(1+(1-mm2)*(cubS t)^2)))⁻¹ * cubD t =
      cubMul * (Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2)))⁻¹ := by
  have hm1 := mm_bounds.2.1
  have hm2 := mm_bounds.2.2.2
  have hr1 : 0 < (1+t^2)*(1+(1-mm1)*t^2) := by
    apply mul_pos <;> nlinarith [sq_nonneg t, mul_nonneg (sub_pos.mpr hm1).le (sq_nonneg t)]
  have hr2 : 0 < (1+(cubS t)^2)*(1+(1-mm2)*(cubS t)^2) := by
    apply mul_pos <;> nlinarith [sq_nonneg (cubS t),
      mul_nonneg (sub_pos.mpr hm2).le (sq_nonneg (cubS t))]
  let s1 := Real.sqrt ((1+t^2)*(1+(1-mm1)*t^2))
  let s2 := Real.sqrt ((1+(cubS t)^2)*(1+(1-mm2)*(cubS t)^2))
  have hs1 : 0 < s1 := Real.sqrt_pos.2 hr1
  have hs2 : 0 < s2 := Real.sqrt_pos.2 hr2
  have hs1sq : s1^2 = (1+t^2)*(1+(1-mm1)*t^2) := Real.sq_sqrt hr1.le
  have hs2sq : s2^2 = (1+(cubS t)^2)*(1+(1-mm2)*(cubS t)^2) := Real.sq_sqrt hr2.le
  have heq : cubD t * s1 = cubMul * s2 := by
    have hsq : (cubD t * s1)^2 = (cubMul*s2)^2 := by
      rw [mul_pow, mul_pow, hs1sq, hs2sq]
      exact cub_radicand_identity t
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have hp1 : 0 < cubD t * s1 := mul_pos (cubD_pos t) hs1
      have hp2 : 0 < cubMul * s2 := mul_pos cubMul_pos hs2
      nlinarith
  change s2⁻¹ * cubD t = cubMul * s1⁻¹
  field_simp [hs1.ne', hs2.ne']
  simpa [mul_comm] using heq

lemma cubS_lower {x : ℝ} (hx : 0 ≤ x) (hxb : cubB ≤ x^2) :
    cubC*x/2 ≤ cubS x := by
  rcases cub_constants_pos with ⟨hc,ha,hb,hd⟩
  have hden : 0 < x^2+cubB := by nlinarith
  dsimp [cubS]
  apply (le_div_iff₀ hden).2
  have hcx : 0 ≤ cubC*x := mul_nonneg hc.le hx
  nlinarith [mul_nonneg hcx ha.le]

lemma cubS_tendsto : Tendsto cubS atTop atTop := by
  apply Monotone.tendsto_atTop_atTop cubS_strictMono.monotone
  intro b
  let x := cubB + 1 + 2 * max b 0 / cubC
  have hc := cub_constants_pos.1
  have hb := cub_constants_pos.2.2.1
  have hfrac : 0 ≤ 2 * max b 0 / cubC := div_nonneg (by positivity) hc.le
  have hx : 0 ≤ x := by dsimp [x]; nlinarith
  have hxb : cubB ≤ x^2 := by
    have hx1 : cubB + 1 ≤ x := by dsimp [x]; linarith
    nlinarith [sq_nonneg x]
  have hl := cubS_lower hx hxb
  have hcalc : b ≤ cubC*x/2 := by
    have hmax : b ≤ max b 0 := le_max_left _ _
    have hcancel : cubC * (2 * max b 0 / cubC) / 2 = max b 0 := by
      field_simp [hc.ne']
    dsimp [x]
    rw [mul_add, mul_add, add_div, add_div, hcancel]
    have : 0 ≤ cubC * cubB / 2 + cubC * 1 / 2 := by positivity
    linarith
  exact ⟨x, hcalc.trans hl⟩

lemma cubS_continuous : Continuous cubS := by
  apply Continuous.div₀
  · fun_prop
  · fun_prop
  · intro x
    have hb := cub_constants_pos.2.2.1
    exact (by nlinarith [sq_nonneg x] : x^2+cubB ≠ 0)

lemma Ki_cubic_isogeny : Ki mm2 = cubMul * Ki mm1 := by
  let g : ℝ → ℝ := fun u =>
    (Real.sqrt ((1+u^2)*(1+(1-mm2)*u^2)))⁻¹
  have hsub := MeasureTheory.integral_comp_mul_deriv_Ioi
    (f := cubS) (f' := cubD) (g := g) (a := 0)
    cubS_continuous.continuousOn cubS_tendsto
    (by
      intro x hx
      simpa [cubD] using (cubS_deriv x).hasDerivWithinAt)
    (tangent_K_integrand_continuous mm_bounds.2.2.2).continuousOn
    (by
      have hi : IntegrableOn g (Ici 0) :=
        (integrableOn_Ici_iff_integrableOn_Ioi).2 (by
          simpa [g] using integrableOn_Ki mm_bounds.2.2.1 mm_bounds.2.2.2)
      apply hi.mono_set
      rintro y ⟨x,hx,rfl⟩
      have hs0 : cubS 0 = 0 := by simp [cubS]
      calc 0 = cubS 0 := hs0.symm
           _ ≤ cubS x := cubS_strictMono.monotone hx)
    (by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      have hi := (integrableOn_Ki mm_bounds.1 mm_bounds.2.1).const_mul cubMul
      exact (integrableOn_congr_fun (fun x hx => by
        simpa [g, Function.comp_def, mul_comm] using cub_pullback x)
        measurableSet_Ioi).2 hi)
  have hs0 : cubS 0 = 0 := by simp [cubS]
  rw [hs0] at hsub
  have hleft : (∫ x in Ioi (0:ℝ), (g ∘ cubS) x * cubD x) =
      cubMul * Ki mm1 := by
    calc
      _ = ∫ x in Ioi (0:ℝ), cubMul *
          (Real.sqrt ((1+x^2)*(1+(1-mm1)*x^2)))⁻¹ := by
            apply integral_congr_ae
            filter_upwards [] with x
            simpa [g, Function.comp_def, mul_comm] using cub_pullback x
      _ = cubMul * Ki mm1 := by
        rw [MeasureTheory.integral_const_mul]
        rfl
  rw [hleft] at hsub
  simpa [Ki, g] using hsub.symm

lemma H_cubic_isogeny : H mm2 = cubMul * H mm1 := by
  rw [H, H, K_eq_Ki mm_bounds.2.2.1 mm_bounds.2.2.2,
    K_eq_Ki mm_bounds.1 mm_bounds.2.1, Ki_cubic_isogeny]
  ring




end Elliptic
