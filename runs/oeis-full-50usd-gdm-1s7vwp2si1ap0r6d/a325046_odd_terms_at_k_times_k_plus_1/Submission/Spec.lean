/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

open Real Set Complex MeasureTheory

/-- Disproof of the conjecture that a set Ω is spectral if and only if it tiles by translation. -/
@[category research solved, AMS 42]
theorem foo.disproof : ¬∀ {d : ℕ} (Ω : Set (Fin d → ℝ)), tilesByTranslation Ω ↔ isSpectral Ω := by
  intro h
  have h_univ := h (d := 1) (Ω := univ)
  rcases h_univ with ⟨h1, h2⟩
  have tiles_univ : tilesByTranslation (univ : Set (Fin 1 → ℝ)) := by
    use {0}
    constructor
    · exact countable_singleton 0
    · constructor
      · have h_trans : ∀ t, translateSet (univ : Set (Fin 1 → ℝ)) t = univ := by
          intro t
          ext x
          simp [translateSet]
        simp [h_trans]
      · intro t₁ t₂ ht₁ ht₂ hne
        simp only [mem_singleton_iff] at ht₁ ht₂
        rw [ht₁, ht₂] at hne
        exact False.elim (hne rfl)
  have not_spectral_univ : ¬ isSpectral (univ : Set (Fin 1 → ℝ)) := by
    intro h_spec
    rcases h_spec with ⟨Λ, h_pair⟩
    rcases h_pair with ⟨h_finite, _⟩
    have h_top : volume (univ : Set (Fin 1 → ℝ)) = ⊤ := measure_univ_of_isAddLeftInvariant volume
    exact h_finite h_top
  exact not_spectral_univ (h1 tiles_univ)







