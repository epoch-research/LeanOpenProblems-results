import FormalConjecturesUtil

/-! An obstruction to reducing longer APs to 3-APs by bounded finite coloring.
This does not prove or disprove the original conjecture. -/

namespace Erdos3ColorReductionCheck

open Finset

variable {n : ℕ}

def code (v : Fin n → Fin 3) : ℕ :=
  Behrend.map 5 (fun i ↦ (v i : ℕ))

def cube (n : ℕ) : Set ℕ := Set.range (@code n)

theorem code_injective : Function.Injective (@code n) := by
  intro x y h
  have heq : (fun i ↦ (x i : ℕ)) = (fun i ↦ (y i : ℕ)) :=
    Behrend.map_injOn (fun i ↦ by have := (x i).isLt; omega)
      (fun i ↦ by have := (y i).isLt; omega) h
  funext i
  exact Fin.ext (congr_fun heq i)

theorem code_pair_eq (w x y z : Fin n → Fin 3)
    (h : code w + code x = code y + code z) :
    ∀ i, (w i : ℕ) + (x i : ℕ) = (y i : ℕ) + (z i : ℕ) := by
  have heq : ((fun i ↦ (w i : ℕ)) + (fun i ↦ (x i : ℕ))) =
      ((fun i ↦ (y i : ℕ)) + (fun i ↦ (z i : ℕ))) := by
    apply Behrend.map_injOn (d := 5)
    · intro i
      change (w i : ℕ) + (x i : ℕ) < 5
      have := (w i).isLt
      have := (x i).isLt
      omega
    · intro i
      change (y i : ℕ) + (z i : ℕ) < 5
      have := (y i).isLt
      have := (z i).isLt
      omega
    · simpa only [map_add, code] using h
  exact fun i ↦ congr_fun heq i

theorem cube_no_four {a d : ℕ}
    (h : ∀ i < 4, a + i * d ∈ cube n) : d = 0 := by
  obtain ⟨v0, hv0⟩ := h 0 (by omega)
  obtain ⟨v1, hv1⟩ := h 1 (by omega)
  obtain ⟨v2, hv2⟩ := h 2 (by omega)
  obtain ⟨v3, hv3⟩ := h 3 (by omega)
  have heq1 := code_pair_eq v0 v2 v1 v1 (by omega)
  have heq2 := code_pair_eq v1 v3 v2 v2 (by omega)
  have h01 : v0 = v1 := by
    funext i
    apply Fin.ext
    have := heq1 i
    have := heq2 i
    have := (v0 i).isLt
    have := (v1 i).isLt
    have := (v2 i).isLt
    have := (v3 i).isLt
    omega
  have : code v0 = code v1 := congrArg code h01
  omega

theorem cube_four_free (n : ℕ) : (cube n).IsAPOfLengthFree 4 := by
  intro S hS hAP
  obtain ⟨a, d, hd⟩ := hAP
  have hz : d = 0 := cube_no_four (a := a) (n := n) (by
    intro i hi
    apply hS
    rw [hd.eq]
    exact ⟨i, by exact_mod_cast hi, by simp⟩)
  have hsub : S ⊆ {a} := by
    rw [hd.eq]
    rintro x ⟨i, hi, rfl⟩
    simp [hz]
  have hcard : ENat.card S ≤ 1 := by
    change S.encard ≤ 1
    exact (Set.encard_le_encard hsub).trans (by simp)
  rw [hd.card] at hcard
  norm_num at hcard

theorem code_line_eq (l : Combinatorics.Subspace Unit (Fin 3) (Fin n)) :
    code (l (fun _ ↦ 0)) + code (l (fun _ ↦ 2)) =
      code (l (fun _ ↦ 1)) + code (l (fun _ ↦ 1)) := by
  simp only [code, ← map_add]
  congr 1
  funext i
  change (l (fun _ ↦ 0) i : ℕ) + (l (fun _ ↦ 2) i : ℕ) =
    (l (fun _ ↦ 1) i : ℕ) + (l (fun _ ↦ 1) i : ℕ)
  cases h : l.idxFun i <;> simp [Combinatorics.Subspace.coe_apply, h]

theorem code_line_ne (l : Combinatorics.Subspace Unit (Fin 3) (Fin n)) :
    code (l (fun _ ↦ 0)) ≠ code (l (fun _ ↦ 1)) := by
  intro h
  have heq := code_injective h
  obtain ⟨i, hi⟩ := l.proper ()
  have := congr_fun heq i
  simp [Combinatorics.Subspace.coe_apply, hi] at this

/-- For each number of colors there is a finite 4-AP-free set whose every coloring
has a monochromatic nontrivial 3-AP. -/
theorem no_bounded_color_reduction (r : ℕ) :
    ∃ A : Set ℕ, A.Finite ∧ A.IsAPOfLengthFree 4 ∧
      ¬ (∃ C : ℕ → Fin r, ∀ c, ThreeAPFree (A ∩ C ⁻¹' {c})) := by
  classical
  obtain ⟨n, hn⟩ :=
    Combinatorics.Subspace.exists_mono_in_high_dimension_fin (Fin 3) (Fin r) Unit
  refine ⟨cube n, Set.finite_range _, cube_four_free n, ?_⟩
  rintro ⟨C, hC⟩
  obtain ⟨l, c, hc⟩ := hn (fun v ↦ C (code v))
  have hmem (v : Unit → Fin 3) : code (l v) ∈ cube n ∩ C ⁻¹' {c} :=
    ⟨⟨l v, rfl⟩, hc v⟩
  exact code_line_ne l (hC c (hmem (fun _ ↦ 0)) (hmem (fun _ ↦ 1))
    (hmem (fun _ ↦ 2)) (code_line_eq l))

#print axioms no_bounded_color_reduction

end Erdos3ColorReductionCheck
