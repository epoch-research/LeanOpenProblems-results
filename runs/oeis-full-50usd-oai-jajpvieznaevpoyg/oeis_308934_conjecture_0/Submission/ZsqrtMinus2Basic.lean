import FormalConjectures.Util.ProblemImports

open Zsqrtd
local notation "ℤ√-2" => Zsqrtd (-2)

lemma zsqrtM2_norm_mk (a b : ℤ) : Zsqrtd.norm (⟨a,b⟩ : ℤ√-2) = a^2 + 2*b^2 := by
  simp [Zsqrtd.norm]
  ring

lemma int_natAbs_sq (a : ℤ) : (a.natAbs : ℤ)^2 = a^2 := by
  simp [sq]

lemma zsqrtM2_natAbs_norm_mk (a b : ℤ) :
    (Zsqrtd.norm (⟨a,b⟩ : ℤ√-2)).natAbs = a.natAbs^2 + 2*b.natAbs^2 := by
  rw [zsqrtM2_norm_mk]
  rw [← Int.ofNat_inj]
  rw [Int.natAbs_of_nonneg]
  · push_cast
    simp [int_natAbs_sq]
  · nlinarith [sq_nonneg a, sq_nonneg b]

lemma nat_rep_of_zsqrtM2_norm {n : ℕ} {z : ℤ√-2} (h : z.norm.natAbs = n) :
    ∃ x y : ℕ, n = x^2 + 2*y^2 := by
  rcases z with ⟨a,b⟩
  refine ⟨a.natAbs, b.natAbs, ?_⟩
  rw [← h]
  exact zsqrtM2_natAbs_norm_mk a b

lemma zsqrtM2_norm_mul_natAbs (z w : ℤ√-2) :
    (Zsqrtd.norm (z*w)).natAbs = z.norm.natAbs * w.norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]

#check nat_rep_of_zsqrtM2_norm
