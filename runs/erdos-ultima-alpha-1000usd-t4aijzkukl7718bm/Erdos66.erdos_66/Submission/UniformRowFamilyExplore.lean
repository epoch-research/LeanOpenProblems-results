import Submission.FiniteTaperExplore
import Submission.FlatRowFamilyExplore
import Submission.GraphBlockGeometryExplore

/-! A uniform mixed-count family, with the prime selected before the digit
thickness. This packages the algebraic estimate independently of any taper. -/
namespace Erdos66UniformRowFamily
open Erdos66FiniteTaper Erdos66GraphBlockGeometry Erdos66GraphRowGeometry Erdos66RowSparsePrefix
  Erdos66IntegerBlock
open scoped Classical

theorem exists_uniform_row_family (T N : ℕ) :
    ∃ p : ℕ, ∃ hp : p.Prime, N < p ∧ ∀ K : ℕ, 0 < K →
      ∃ C : ℕ → Finset (ZMod ((p * K) ^ 2)), Monotone C ∧
        RowSparse (blockSet ((p*K)^2) (fun _ ↦ C (T^2))) (p*K) (K*(4*T^2+4)) ∧
        ∀ i : ℕ, 0 < i → i ≤ T ^ 2 → ∀ j : ℕ, 0 < j → j ≤ T ^ 2 →
          ∀ z : ZMod ((p * K) ^ 2),
            |(((C i).filter (fun a ↦ z - a ∈ C j)).card : ℝ) -
              4 * (K : ℝ) ^ 2 * i * j| ≤ carryError T K := by
  obtain ⟨p, hp, hpN, hp8, B, hmono, hrows, E, hB⟩ :=
    Erdos66FlatRowFamily.exists_mixed_flat_prime_family_with_rows (T ^ 2) N
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hpN, fun K hK ↦ ?_⟩
  letI : NeZero K := ⟨by omega⟩
  let M := (p * K) ^ 2
  let C : ℕ → Finset (ZMod M) := fun i ↦
    Erdos66CyclicThickening.thickenedSet p K (B i)
  have hrowC : RowSparse (blockSet M (fun _ ↦ C (T^2))) (p*K) (K*(4*T^2+4)) :=
    thickened_block_rowSparse p K (fun _ ↦ B (T^2)) (4*T^2+4) (fun _ s ↦ hrows _ le_rfl s)
  refine ⟨C, fun i j hij ↦ Erdos66MixedCyclicThickening.thickenedSet_mono p K (hmono hij), hrowC, ?_⟩
  intro i hip hi j hjp hj z
  obtain ⟨hE0, hEsq, hcounts⟩ := hB i hip hi j hjp hj
  have hui : (i : ℝ) ≤ (T : ℝ) ^ 2 := by exact_mod_cast hi
  have huj : (j : ℝ) ≤ (T : ℝ) ^ 2 := by exact_mod_cast hj
  let e : ℝ := E i j
  have he0 : 0 ≤ e := by dsimp [e]; exact_mod_cast hE0
  have hesq : e ^ 2 ≤ 16 * (i : ℝ) * j *
      (i + j) := by dsimp [e]; exact_mod_cast hEsq
  have hepoly : 16 * (i : ℝ) * j *
      (i + j) ≤ 32 * (T : ℝ) ^ 6 := by
    calc
      _ ≤ 16 * (T : ℝ) ^ 2 * (T : ℝ) ^ 2 * ((T : ℝ) ^ 2 + (T : ℝ) ^ 2) := by gcongr
      _ = _ := by ring
  have he : e ≤ 6 * (T : ℝ) ^ 3 := by
    have hnon : 0 ≤ 6 * (T : ℝ) ^ 3 := by positivity
    apply (sq_le_sq₀ he0 hnon).mp
    nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) T) 6]
  have hμ : 4 * (i : ℝ) * j ≤ 4 * (T : ℝ) ^ 4 := by
    calc
      _ ≤ 4 * (T : ℝ) ^ 2 * (T : ℝ) ^ 2 := by gcongr
      _ = _ := by ring
  have hErr : e + 10 * (i : ℝ) + 10 * j + 8 ≤ algebraError T := by
    dsimp [algebraError]
    linarith
  have hbase : ∀ x y : ZMod p,
      |((Erdos66MixedCyclicThickening.mixedFiber p (B i)
        (B j) x y).card : ℝ) -
        4 * (i : ℝ) * j| ≤
          e + 10 * (i : ℝ) + 10 * j + 8 := by
    intro x y
    have hh := hcounts (x, y)
    change |((Erdos66MixedCyclicThickening.mixedFiber p (B i)
      (B j) x y).card : ℤ) -
      4 * i * j| ≤ _ at hh
    dsimp [e]
    exact_mod_cast hh
  have hh := Erdos66MixedCyclicThickening.thickenedSet_error p K
    (B i) (B j)
    (4 * (i : ℝ) * j)
    (e + 10 * (i : ℝ) + 10 * j + 8) hbase z
  have hbig : (K : ℝ) ^ 2 * (e + 10 * (i : ℝ) + 10 * j + 8) +
      2 * K * (4 * (i : ℝ) * j +
        (e + 10 * (i : ℝ) + 10 * j + 8)) ≤ carryError T K := by
    dsimp [carryError]
    gcongr
  dsimp only [C]
  convert hh.trans hbig using 2 <;> ring

end Erdos66UniformRowFamily
