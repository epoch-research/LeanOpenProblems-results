import Submission.EveryPrimeRelativeFamilyExplore
import Submission.CyclicThickeningExplore

/-! Cyclic self-flat templates at every sufficiently large prime square,
with a discrete family of density levels. No infinite compatibility is
asserted. -/
namespace Erdos66EveryPrimeCyclicFamily
open Erdos66EveryPrimeRelativeFamily Erdos66CyclicThickening Erdos66OriginRepair
open scoped Classical

/-- With coordinate thickness H, level i has mean (2*H*D*i)^2 and
relative cyclic error at most 5/H. -/
theorem every_prime_cyclic_family (H : ℕ) (hH : 0 < H) :
    ∃ D : ℕ, 0 < D ∧ ∀ p : ℕ, ∀ hp : p.Prime,
      max (8*(D*(2*H))+2) (2*(D*(2*H))^2) < p →
      ∃ B : ℕ → Finset (ZMod ((p*H)^2)), ∀ i : ℕ, i ≤ 2*H →
        ∀ z : ZMod ((p*H)^2),
          |(((B i).filter (fun a ↦ z-a∈B i)).card : ℝ)-(2*(H : ℝ)*D*i)^2| ≤
            (5/(H : ℝ))*(2*(H : ℝ)*D*i)^2 := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  obtain ⟨D,hD,hfamily⟩ := every_prime_relative_family (1/(H : ℝ)) (by positivity) (2*H)
  refine ⟨D,hD,fun p hp hprime ↦ ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero H := ⟨by omega⟩
  obtain ⟨B,hB0,hBmono,hB⟩ := hfamily p hp hprime
  refine ⟨fun i ↦ thickenedSet p H (B i),fun i hi z ↦ ?_⟩
  have hf : ∀ t s : ZMod p,
      |((sumFiber p (B i) t s).card : ℝ)-4*(D : ℝ)^2*i*i| ≤
        (1/(H : ℝ))*(4*(D : ℝ)^2*i*i) := by
    intro t s
    exact (hB i hi i hi).1 (t,s)
  have hh := thickenedSet_error p H (B i) (4*(D : ℝ)^2*i*i)
    ((1/(H : ℝ))*(4*(D : ℝ)^2*i*i)) hf z
  have he : (H : ℝ)^2*(4*(D : ℝ)^2*i*i)=(2*(H : ℝ)*D*i)^2 := by ring
  rw [he] at hh
  apply hh.trans
  have hb : (1/(H : ℝ)) ≤ 1 := (div_le_one hHr).mpr hH1
  calc
    _ ≤ (H : ℝ)^2*((1/(H : ℝ))*(4*(D : ℝ)^2*i*i))+
        2*H*(2*(4*(D : ℝ)^2*i*i)) := by
      gcongr
      nlinarith [mul_le_mul_of_nonneg_right hb (show (0 : ℝ) ≤ 4*(D : ℝ)^2*i*i by positivity)]
    _ = (5/(H : ℝ))*(2*(H : ℝ)*D*i)^2 := by field_simp; ring

end Erdos66EveryPrimeCyclicFamily
