import FormalConjecturesUtil
import Submission.IrrationalSequenceDiagnostic

/-! Sharp linear-window backward slopes do not by themselves force
rationality. This does not identify an extremal-number function. -/
open Filter Asymptotics
namespace Erdos713IrrationalWindowDiagnostic
open Erdos713IrrationalSequenceDiagnostic
set_option maxHeartbeats 2000000

noncomputable def roundedPower (r : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ)^r⌋₊

lemma power_secant_bounds {r x s : ℝ} (hr : 1 ≤ r) (hs : 0 < s) (hsx : s ≤ x) :
    r*s*(x-s)^(r-1) ≤ x^r-(x-s)^r ∧ x^r-(x-s)^r ≤ r*s*x^(r-1) := by
  have hx : 0 ≤ x := hs.le.trans hsx
  have hy : 0 ≤ x-s := sub_nonneg.mpr hsx
  have hlt : x-s < x := by linarith
  have hlo := (convexOn_rpow hr).le_slope_of_hasDerivAt
    (show x-s ∈ Set.Ici (0 : ℝ) from hy) (show x ∈ Set.Ici (0 : ℝ) from hx)
    hlt (Real.hasDerivAt_rpow_const (Or.inr hr))
  have hhi := (convexOn_rpow hr).slope_le_of_hasDerivAt
    (show x-s ∈ Set.Ici (0 : ℝ) from hy) (show x ∈ Set.Ici (0 : ℝ) from hx)
    hlt (Real.hasDerivAt_rpow_const (Or.inr hr))
  simp only [slope_def_field,sub_sub_cancel] at hlo hhi
  have hl := (le_div_iff₀ hs).mp hlo
  have hu := (div_le_iff₀ hs).mp hhi
  constructor <;> nlinarith only [hl,hu]

lemma rounded_secant_bounds {r : ℝ} (hr : 1 ≤ r) {n s : ℕ}
    (hs : 1 ≤ s) (hsn : s ≤ n) :
    r*(s : ℝ)*((n-s : ℕ) : ℝ)^(r-1)-1 <
        (roundedPower r n : ℝ)-(roundedPower r (n-s) : ℝ) ∧
      (roundedPower r n : ℝ)-(roundedPower r (n-s) : ℝ) <
        r*(s : ℝ)*(n : ℝ)^(r-1)+1 := by
  have hsub : ((n-s : ℕ) : ℝ) = (n : ℝ)-s := Nat.cast_sub hsn
  have hp := power_secant_bounds hr (by exact_mod_cast hs : (0 : ℝ) < s)
    (by exact_mod_cast hsn : (s : ℝ) ≤ n)
  rw [← hsub] at hp
  have hloN := Nat.lt_floor_add_one ((n : ℝ)^r)
  have hloS := Nat.lt_floor_add_one (((n-s : ℕ) : ℝ)^r)
  have hhiN := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) r)
  have hhiS := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg (n-s)) r)
  dsimp only [roundedPower]
  constructor <;> linarith only [hp.1,hp.2,hloN,hloS,hhiN,hhiS]

lemma window_power_lower {r θ x s : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx : 0 ≤ x) (hs : 0 ≤ s) (hwin : s ≤ θ*x) :
    r*(1-θ)*s*x^(r-1) ≤ r*s*(x-s)^(r-1) := by
  have hbase : 0 ≤ 1-θ := sub_nonneg.mpr hθ1
  have hb : (1-θ)*x ≤ x-s := by nlinarith only [hwin]
  have hp := Real.rpow_le_rpow (mul_nonneg hbase hx) hb (by linarith : 0 ≤ r-1)
  rw [Real.mul_rpow hbase hx] at hp
  have hself := Real.self_le_rpow_of_le_one hbase (by linarith : 1-θ ≤ 1)
    (by linarith : r-1 ≤ 1)
  have hmul := mul_le_mul_of_nonneg_right hself (Real.rpow_nonneg hx (r-1))
  have hcoeff : 0 ≤ r*s := mul_nonneg (by linarith) hs
  have hh := mul_le_mul_of_nonneg_left (hmul.trans hp) hcoeff
  nlinarith only [hh]

/-- Both sides of the sharp slope hold at EVERY sufficiently large order,
uniformly over a linear window. This is stronger than selection on a
cofinal sequence, but is still a numerical diagnostic only. -/
theorem rounded_sharp_window {r : ℝ} (hr : 1 < r) (hr2 : r ≤ 2)
    (a b : ℝ) (ha : 0 < a) (har : a < r) (hrb : r < b) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ s : ℕ, 1 ≤ s → (s : ℝ) ≤ θ*n →
        a*(s : ℝ)*(n : ℝ)^(r-1) <
            (roundedPower r n : ℝ)-(roundedPower r (n-s) : ℝ) ∧
          (roundedPower r n : ℝ)-(roundedPower r (n-s) : ℝ) <
            b*(s : ℝ)*(n : ℝ)^(r-1) := by
  let θ := (r-a)/(2*r)
  have hr0 : 0 < r := by linarith
  have hθ0 : 0 < θ := div_pos (sub_pos.mpr har) (by positivity)
  have hθ1 : θ < 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*r)).mpr
    linarith
  have hgap : 0 < r*(1-θ)-a := by
    have he : 2*r*θ = r-a := by dsimp [θ]; field_simp
    nlinarith only [he,har]
  have hpow : Tendsto (fun n : ℕ => (n : ℝ)^(r-1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < r-1)).comp tendsto_natCast_atTop_atTop
  have hlow : ∀ᶠ n : ℕ in atTop, 1 < (r*(1-θ)-a)*(n : ℝ)^(r-1) :=
    (hpow.const_mul_atTop hgap).eventually_gt_atTop 1
  have hhigh : ∀ᶠ n : ℕ in atTop, 1 < (b-r)*(n : ℝ)^(r-1) :=
    (hpow.const_mul_atTop (sub_pos.mpr hrb)).eventually_gt_atTop 1
  refine ⟨θ,hθ0,hθ1,?_⟩
  filter_upwards [hlow,hhigh] with n hnlo hnhi
  intro s hs hwin
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsnR : (s : ℝ) ≤ n := hwin.trans
    (by nlinarith only [hθ1,Nat.cast_nonneg (α := ℝ) n])
  have hsn : s ≤ n := by exact_mod_cast hsnR
  have hbounds := rounded_secant_bounds hr.le hs hsn
  have hpowlo := window_power_lower hr.le hr2 hθ0.le hθ1.le
    (Nat.cast_nonneg n) (Nat.cast_nonneg s) hwin
  rw [← Nat.cast_sub hsn] at hpowlo
  have hscaleLo := mul_le_mul_of_nonneg_right hsR
    (show 0 ≤ (r*(1-θ)-a)*(n : ℝ)^(r-1) from
      mul_nonneg hgap.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hscaleHi := mul_le_mul_of_nonneg_right hsR
    (show 0 ≤ (b-r)*(n : ℝ)^(r-1) from
      mul_nonneg (sub_nonneg.mpr hrb.le) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  constructor
  · nlinarith only [hnlo,hscaleLo,hpowlo,hbounds.1]
  · nlinarith only [hnhi,hscaleHi,hbounds.2]

theorem irrational_sequence_sharp_window (a b : ℝ) (ha : 0 < a)
    (har : a < index) (hrb : index < b) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ s : ℕ, 1 ≤ s → (s : ℝ) ≤ θ*n →
        a*(s : ℝ)*(n : ℝ)^(index-1) < (seq n : ℝ)-(seq (n-s) : ℝ) ∧
          (seq n : ℝ)-(seq (n-s) : ℝ) < b*(s : ℝ)*(n : ℝ)^(index-1) := by
  exact rounded_sharp_window (by have := index_bounds.1; linarith)
    (by have := index_bounds.2; linarith) a b ha har hrb

/-- All numerical properties are realized by ONE irrational-index sequence.
No forbidden graph or graph-theoretic saturation is asserted. -/
theorem exists_irrational_sharp_sequence :
    ∃ r : ℝ, (6 : ℝ)/5 < r ∧ r < (5 : ℝ)/4 ∧ Irrational r ∧
      ∃ f : ℕ → ℕ, Monotone f ∧ (∀ m n, f m+f n ≤ f (m+n)) ∧
        IsEquivalent atTop (fun n : ℕ => (f n : ℝ)) (fun n : ℕ => (n : ℝ)^r) ∧
        ∀ a b : ℝ, 0 < a → a < r → r < b →
          ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ᶠ n : ℕ in atTop,
            ∀ s : ℕ, 1 ≤ s → (s : ℝ) ≤ θ*n →
              a*(s : ℝ)*(n : ℝ)^(r-1) < (f n : ℝ)-(f (n-s) : ℝ) ∧
                (f n : ℝ)-(f (n-s) : ℝ) < b*(s : ℝ)*(n : ℝ)^(r-1) :=
  ⟨index,index_bounds.1,index_bounds.2,index_irrational,seq,seq_monotone,
    seq_superadditive,seq_asymptotic,irrational_sequence_sharp_window⟩

#print axioms rounded_sharp_window
#print axioms irrational_sequence_sharp_window
#print axioms exists_irrational_sharp_sequence
end Erdos713IrrationalWindowDiagnostic
