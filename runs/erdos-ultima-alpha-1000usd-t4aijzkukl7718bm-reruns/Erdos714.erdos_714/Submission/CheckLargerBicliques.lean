import Submission.Spec

open Filter SimpleGraph

namespace Erdos714ProgressTest

/-- Increasing both parts of the forbidden biclique increases the extremal number. -/
theorem extremal_biclique_mono (s r n : ℕ) (hsr : s ≤ r) :
    extremalNumber n (completeBipartiteGraph (Fin s) (Fin s)) ≤
      extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) := by
  let e : Fin s ↪ Fin r := Fin.castLEEmb hsr
  have hcopy : (completeBipartiteGraph (Fin s) (Fin s)) ⊑
      (completeBipartiteGraph (Fin r) (Fin r)) := by
    refine ⟨⟨⟨Sum.map e e, ?_⟩, Sum.map_injective.mpr ⟨e.injective, e.injective⟩⟩⟩
    intro x y hxy
    cases x <;> cases y <;> simp_all
  exact hcopy.extremalNumber_le

/-- The known third-case exponent also applies to every larger balanced biclique. -/
theorem third_exponent_for_larger_bicliques (r : ℕ) (hr : 3 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ)^((5 : ℝ)/3) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) := by
  obtain ⟨c, hc, hn⟩ := Erdos714Norm.third_instance
  refine ⟨c, hc, ?_⟩
  filter_upwards [hn] with n hn
  have he : (extremalNumber n (completeBipartiteGraph (Fin 3) (Fin 3)) : ℝ) ≤
      (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ) :=
    Nat.cast_le.mpr (extremal_biclique_mono 3 r n hr)
  have hpow : (2 : ℝ)-1/(3 : ℝ) = 5/3 := by norm_num
  rw [hpow] at hn
  exact hn.trans he

#print axioms extremal_biclique_mono
#print axioms third_exponent_for_larger_bicliques

end Erdos714ProgressTest
