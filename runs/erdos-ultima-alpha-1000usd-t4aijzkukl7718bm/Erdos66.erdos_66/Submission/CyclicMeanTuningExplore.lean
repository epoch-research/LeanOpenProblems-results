import Submission.EveryPrimeCyclicFamilyExplore
import Submission.CyclicDensityTransferExplore

/-! Finite cyclic templates with a freely prescribed large, sparse mean.
This remains a finite theorem and imposes no compatible-prefix condition. -/
namespace Erdos66CyclicMeanTuning
open Erdos66EveryPrimeCyclicFamily Erdos66CyclicDensityTransfer
open scoped Classical
set_option maxHeartbeats 1000000

lemma fourth_power_error (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (1+u)^4 ≤ 1+15*u := by
  have h₂ : u^2 ≤ u := by nlinarith
  have h₃ : u^3 ≤ u := by nlinarith [mul_le_mul_of_nonneg_right h₂ hu]
  have h₄ : u^4 ≤ u := by nlinarith [mul_le_mul_of_nonneg_right h₃ hu]
  nlinarith

lemma rounding_square_distortion (H D i x t p : ℝ)
    (hH : 1 ≤ H) (hD : 0 ≤ D) (hi : H ≤ i) (hx : H ≤ x)
    (htlo : x ≤ t) (hthi : t ≤ x+1)
    (hplo : 2*D*i*t ≤ p) (hphi : p ≤ 2*D*(i+1)*t) :
    (2*D*i*x)^2 ≤ p^2 ∧ p^2 ≤ (1+15/H)*(2*D*i*x)^2 := by
  have hH0 : 0 < H := by linarith
  have hi0 : 0 ≤ i := by linarith
  have hx0 : 0 ≤ x := by linarith
  have ht0 : 0 ≤ t := hx0.trans htlo
  have hu : 0 ≤ 1/H := by positivity
  have hu1 : 1/H ≤ 1 := (div_le_one hH0).mpr hH
  have hi' : i+1 ≤ i*(1+1/H) := by
    have hh : 1 ≤ i/H := (le_div_iff₀ hH0).mpr (by simpa using hi)
    nlinarith [show i*(1/H)=i/H by ring]
  have ht' : t ≤ x*(1+1/H) := by
    have hh : 1 ≤ x/H := (le_div_iff₀ hH0).mpr (by simpa using hx)
    nlinarith [show x*(1/H)=x/H by ring]
  have hl : 2*D*i*x ≤ p := (mul_le_mul_of_nonneg_left htlo (by positivity)).trans hplo
  have h0 : 0 ≤ 2*D*i*x := by positivity
  have hp0 := h0.trans hl
  have hr : p ≤ (2*D*i*x)*(1+1/H)^2 := by
    calc
      p ≤ 2*D*(i+1)*t := hphi
      _ ≤ 2*D*(i*(1+1/H))*(x*(1+1/H)) := by gcongr
      _ = _ := by ring
  refine ⟨pow_le_pow_left₀ h0 hl 2,?_⟩
  calc
    p^2 ≤ ((2*D*i*x)*(1+1/H)^2)^2 := pow_le_pow_left₀ hp0 hr 2
    _ = (1+1/H)^4*(2*D*i*x)^2 := by ring
    _ ≤ (1+15/H)*(2*D*i*x)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      simpa only [div_eq_mul_inv,one_mul] using fourth_power_error (1/H) hu hu1

/-- Bertrand supplies a prime, while a density level compensates for its
factor-two uncertainty. -/
lemma prime_and_level (H D P : ℕ) (hH : 0 < H) (hD : 0 < D)
    (x : ℝ) (hx : (max H (P+1) : ℕ) ≤ x) :
    ∃ p i : ℕ, p.Prime ∧ P < p ∧ H ≤ i ∧ i ≤ 2*H ∧
      (2*(D : ℝ)*i*x)^2 ≤ (p : ℝ)^2 ∧
      (p : ℝ)^2 ≤ (1+15/(H : ℝ))*(2*(D : ℝ)*i*x)^2 := by
  let t : ℕ := ⌈x⌉₊
  have hxH : (H : ℝ) ≤ x := le_trans (by exact_mod_cast le_max_left H (P+1)) hx
  have hxP : ((P+1 : ℕ) : ℝ) ≤ x := le_trans (by exact_mod_cast le_max_right H (P+1)) hx
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hx0 : 0 ≤ x := by linarith
  have htlo : x ≤ t := Nat.le_ceil x
  have hthi : (t : ℝ) ≤ x+1 := (Nat.ceil_lt_add_one hx0).le
  have ht : 0 < t := by exact_mod_cast (show (0 : ℝ) < t by linarith)
  obtain ⟨p,hp,hplo,hphi⟩ := Nat.exists_prime_lt_and_le_two_mul (2*D*H*t) (by positivity)
  let i := p/(2*D*t)
  have hden : 0 < 2*D*t := by positivity
  have hiH : H ≤ i := (Nat.le_div_iff_mul_le hden).mpr (by nlinarith)
  have hi2H : i ≤ 2*H := by
    have hh := Nat.div_mul_le_self p (2*D*t)
    dsimp [i]
    nlinarith
  have hpP : P < p := by
    have hPt : P+1 ≤ t := by exact_mod_cast hxP.trans htlo
    have hDt : t ≤ 2*D*H*t := by nlinarith
    omega
  have hplor : 2*(D : ℝ)*i*t ≤ p := by
    have hh := Nat.div_mul_le_self p (2*D*t)
    have hh' : 2*D*i*t ≤ p := by dsimp [i]; nlinarith
    exact_mod_cast hh'
  have hphir : (p : ℝ) ≤ 2*D*((i : ℝ)+1)*t := by
    have hh := (Nat.lt_mul_div_succ p hden).le
    have hh' : p ≤ 2*D*(i+1)*t := by dsimp [i]; nlinarith
    exact_mod_cast hh'
  exact ⟨p,i,hp,hpP,hiH,hi2H,rounding_square_distortion H D i x t p hH1
    (Nat.cast_nonneg D) (by exact_mod_cast hiH) hxH htlo hthi hplor hphir⟩

/-- For each precision there is a fixed window of admissible means, valid
at every modulus: the mean must be large, and the density sufficiently small. -/
theorem prescribed_mean_thresholds (H : ℕ) (hH : 0 < H) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ N : ℕ, 0 < N → ∀ μ : ℝ,
      a ≤ μ → b*μ ≤ N →
      ∃ B : Finset (ZMod N), ∀ z : ZMod N,
        |(((B.filter (fun v ↦ z-v∈B)).card : ℝ)-μ)| ≤ (39/(H : ℝ))*μ := by
  obtain ⟨D,hD,hfamily⟩ := every_prime_cyclic_family H hH
  let P : ℕ := max (8*(D*(2*H))+2) (2*(D*(2*H))^2)
  let V : ℕ := max H (P+1)
  let a : ℝ := H*(2*(H : ℝ)*D*(2*H))^2
  let b : ℝ := (V : ℝ)^2
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hV : 0 < V := lt_of_lt_of_le hH (le_max_left _ _)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨a,b,ha,hb,fun N hN μ hμa hNμ ↦ ?_⟩
  letI : NeZero N := ⟨by omega⟩
  letI : NeZero H := ⟨by omega⟩
  have hμ : 0 < μ := ha.trans_le hμa
  let x : ℝ := Real.sqrt (N/μ)
  have hx : (V : ℝ) ≤ x := Real.le_sqrt_of_sq_le ((le_div_iff₀ hμ).mpr hNμ)
  have hxN : x^2*μ=(N : ℝ) := by
    dsimp [x]
    rw [Real.sq_sqrt (by positivity),div_mul_cancel₀ _ hμ.ne']
  obtain ⟨p,i,hp,hpP,hiH,hi2H,hslo,hshi⟩ := prime_and_level H D P hH hD x hx
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B,hB⟩ := hfamily p hp hpP
  let ν : ℝ := (2*(H : ℝ)*D*i)^2
  have hν : 0 ≤ ν := sq_nonneg _
  have hmul0 : 0 ≤ (H : ℝ)^2*μ := by positivity
  have he : (2*(D : ℝ)*i*x)^2*((H : ℝ)^2*μ)=(N : ℝ)*ν := by
    calc
      _ = (x^2*μ)*(2*(H : ℝ)*D*i)^2 := by ring
      _ = _ := by rw [hxN]
  have he' : (p : ℝ)^2*((H : ℝ)^2*μ)=((p*H : ℕ) : ℝ)^2*μ := by push_cast; ring
  have hlo : (N : ℝ)*ν ≤ (((p*H)^2 : ℕ) : ℝ)*μ := by
    have hh := mul_le_mul_of_nonneg_right hslo hmul0
    simpa only [he,he',Nat.cast_pow] using hh
  have hhi : (((p*H)^2 : ℕ) : ℝ)*μ ≤ (1+15/(H : ℝ))*N*ν := by
    have hh := mul_le_mul_of_nonneg_right hshi hmul0
    rw [he',mul_assoc,he] at hh
    simpa only [Nat.cast_pow,mul_assoc] using hh
  have hi2Hr : (i : ℝ) ≤ 2*(H : ℝ) := by exact_mod_cast hi2H
  have hνmax : ν ≤ (2*(H : ℝ)*D*(2*H))^2 := by
    dsimp [ν]
    gcongr
  have hsmall : ν ≤ μ/H := by
    apply (le_div_iff₀ hHr).mpr
    have hh := mul_le_mul_of_nonneg_left hνmax hHr.le
    dsimp [a] at hμa
    nlinarith
  exact density_transfer_small_error ((p*H)^2) N H hH (B i) μ ν hμ.le hν
    (hB i hi2H) hlo hhi hsmall

/-- Uniform finite realization of every sufficiently large, sufficiently
sparse prescribed mean. -/
theorem prescribed_mean (ε : ℝ) (hε : 0 < ε) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ N : ℕ, 0 < N → ∀ μ : ℝ,
      a ≤ μ → b*μ ≤ N →
      ∃ B : Finset (ZMod N), ∀ z : ZMod N,
        |(((B.filter (fun v ↦ z-v∈B)).card : ℝ)-μ)| ≤ ε*μ := by
  obtain ⟨H,hHbig⟩ := exists_nat_gt (max (1 : ℝ) (39/ε))
  have hH : 0 < H := by exact_mod_cast (show (0 : ℝ) < H by have := lt_of_le_of_lt (le_max_left _ _) hHbig; linarith)
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have he : 39/(H : ℝ) ≤ ε := (div_le_iff₀ hHr).mpr (by
    have hh := (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hHbig)
    linarith)
  obtain ⟨a,b,ha,hb,h⟩ := prescribed_mean_thresholds H hH
  refine ⟨a,b,ha,hb,fun N hN μ hμa hNμ ↦ ?_⟩
  obtain ⟨B,hB⟩ := h N hN μ hμa hNμ
  exact ⟨B,fun z ↦ (hB z).trans (mul_le_mul_of_nonneg_right he (ha.trans_le hμa).le)⟩

end Erdos66CyclicMeanTuning
