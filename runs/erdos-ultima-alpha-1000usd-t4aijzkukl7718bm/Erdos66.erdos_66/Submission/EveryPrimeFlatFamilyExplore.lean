import Submission.TranslatedMixedFiberExplore
import Submission.AbstractSumDifferenceFamilyExplore

/-! Nested mixed-sum and off-zero mixed-difference flat families in every
sufficiently large prime plane. The prime has an explicit polynomial lower
threshold; no CRT or Dirichlet sign realization is used in the proof. -/
namespace Erdos66EveryPrimeFlatFamily
open Erdos66CharacterTranslateSelection Erdos66TranslatedCharacterEnergy
  Erdos66TranslatedMixedFiber Erdos66AbstractSumDifferenceFamily
  Erdos66OriginRepair Erdos66CrossGraph
open scoped Classical
set_option maxHeartbeats 1000000

/-- The integer spacing `D` reduces relative error while `H` specifies how
many nested levels must be controlled simultaneously. -/
theorem every_prime_flat_family (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (D H : ℕ) (hD : 0 < D) (hp₁ : 8*(D*H)+1 < p) (hp₂ : 2*(D*H)^2 < p) :
    ∃ B : ℕ → Finset (ZMod p × ZMod p), Monotone B ∧
      ∃ E : ℕ → ℕ → ℝ, ∀ i, 0 < i → i ≤ H → ∀ j, 0 < j → j ≤ H →
        0 ≤ E i j ∧
        (E i j)^2 ≤ 32*(H+1)*(2*D*i)*(2*D*j)*(2*D*i+2*D*j+1) ∧
        (∀ z, |(pairCount (B i) (B j) z : ℝ)-4*(D : ℝ)^2*i*j| ≤
          E i j+12*D*i+12*D*j+8) ∧
        ∀ z, z ≠ 0 →
          |(pairCount (B i) ((B j).image Neg.neg) z : ℝ)-4*(D : ℝ)^2*i*j| ≤
            E i j+12*D*i+12*D*j+8 := by
  obtain ⟨a,hzero,hopp,henergy⟩ := exists_admissible_interval_translates p hp (2*(D*H)) (by omega)
    (Finset.range (H+1)) (fun i ↦ 2*(D*i)) (fun i hi ↦ by
      have hh : i ≤ H := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left D hh))
  let U := intervalTranslate p a
  have hcard (h : ℕ) (hh : h ≤ 2*(D*H)) : (U h).card=h :=
    intervalTranslate_card p a (by omega)
  obtain ⟨B,hB,E,hEdef,hE⟩ := repair_parameter_family p hp (D*H) hp₂ (by omega)
    U (intervalTranslate_mono p a) hcard hzero hopp
  refine ⟨fun i ↦ B (D*i),fun i j hij ↦ hB (Nat.mul_le_mul_left D hij),
    fun i j ↦ (E (D*i) (D*j) : ℝ),?_⟩
  intro i hi hiH j hj hjH
  dsimp only
  obtain ⟨he0,hes,hed⟩ := hE (D*i) (Nat.mul_pos hD hi) (Nat.mul_le_mul_left D hiH)
    (D*j) (Nat.mul_pos hD hj) (Nat.mul_le_mul_left D hjH)
  refine ⟨by exact_mod_cast he0,?_,?_,?_⟩
  · have hei := henergy i (Finset.mem_range.mpr (by omega))
    have hej := henergy j (Finset.mem_range.mpr (by omega))
    simp only [Finset.card_range,Nat.cast_add,Nat.cast_one] at hei hej
    obtain ⟨hbs,hbd⟩ := interval_mixed_l1_sq a (2*(D*i)) (2*(D*j)) (8*(H+1))
      (by positivity) hei hej
    let es : ℝ := ∑ z : ZMod p, |(crossCharFiber (U (2*(D*i))) (U (2*(D*j))) z : ℝ)|
    let ed : ℝ := ∑ z : ZMod p, |(crossCharFiber (U (2*(D*i))) ((U (2*(D*j))).image Neg.neg) z : ℝ)|
    have heq : (E (D*i) (D*j) : ℝ) = es+ed := by
      rw [hEdef]
      simp only [Int.cast_add,Int.cast_sum,Int.cast_abs,es,ed]
    rw [heq]
    change es^2 ≤ _ at hbs
    change ed^2 ≤ _ at hbd
    push_cast at hbs hbd ⊢
    have hpos : 0 ≤ 8*((H : ℝ)+1)*(2*((D : ℝ)*i))*(2*((D : ℝ)*j)) := by positivity
    nlinarith [sq_nonneg (es-ed)]
  · intro z
    have hh : |(pairCount (B (D*i)) (B (D*j)) z : ℝ)-4*(D*i)*(D*j)| ≤
        (E (D*i) (D*j) : ℝ)+12*(D*i)+12*(D*j)+8 := by exact_mod_cast hes z
    convert hh using 2 <;> ring
  · intro z hz
    have hh : |(pairCount (B (D*i)) ((B (D*j)).image Neg.neg) z : ℝ)-4*(D*i)*(D*j)| ≤
        (E (D*i) (D*j) : ℝ)+12*(D*i)+12*(D*j)+8 := by exact_mod_cast hed z hz
    convert hh using 2 <;> ring

end Erdos66EveryPrimeFlatFamily
