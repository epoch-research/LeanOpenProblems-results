import Submission.RationalFractionalPartition

/-! Power-of-two multicover certificates. The conversion uses an arbitrary
integral partition only as a bounded remainder, not as a linear-cost partition. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalCycles
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

/-- Encode any existing pure-cycle partition by natural multiplicities. -/
lemma exists_unit_multicover (G : SimpleGraph V) (hG : ∀ x, Even (G.degree x)) :
    ∃ k : CyclePiece G → ℕ,
      ∀ e ∈ G.edgeSet, (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then k H else 0) = 1 := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G hG
  let k : CyclePiece G → ℕ := fun H => if H.val ∈ D then 1 else 0
  refine ⟨k,?_⟩
  intro e he
  rw [← hd.2] at he
  obtain ⟨H,hHD,heH⟩ := Set.mem_iUnion₂.mp he
  let J : CyclePiece G := ⟨H,hc H hHD⟩
  rw [Finset.sum_eq_single J]
  · simp [J,k,hHD,heH]
  · intro K _ hK
    by_cases hKD : K.val ∈ D
    · have heK : e ∉ K.val.edgeSet := by
        intro heK
        have hKH : K.val ≠ H := fun h => hK (Subtype.ext h)
        exact Set.disjoint_left.mp (hd.1 hKD hHD hKH) heK heH
      simp [heK]
    · simp [k,hKD]
  · simp

/-- Exact power-of-two coverage at average cost at most 2*n+1. The exponent
can be enormous; this theorem does not assert any rounding to multiplicity one. -/
lemma exists_dyadic_multicover_linear (G : SimpleGraph V)
    (hG : ∀ x, Even (G.degree x)) :
    ∃ (r : ℕ) (k : CyclePiece G → ℕ),
      (∀ e ∈ G.edgeSet, (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then k H else 0) = 2^r) ∧
      (∑ H, k H) ≤ (2 * Fintype.card V + 1) * 2^r := by
  obtain ⟨m,u,hm,hu,hbu⟩ := exists_uniform_multicover_linear G hG
  obtain ⟨w,hw⟩ := exists_unit_multicover G hG
  let L := ∑ H, w H
  let r := m * L
  let s := 2^r
  let a := s / m
  let b := s % m
  let k : CyclePiece G → ℕ := fun H => a * u H + b * w H
  have hab : a*m+b = s := by
    simpa only [a,b,Nat.mul_comm] using Nat.div_add_mod s m
  have hb : b ≤ m := (Nat.mod_lt s hm).le
  have hlarge : m*L ≤ s := Nat.lt_two_pow_self.le
  have ham : a*m ≤ s := Nat.div_mul_le_self s m
  refine ⟨r,k,?_,?_⟩
  · intro e he
    have hsum : (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then k H else 0) =
        a * (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then u H else 0) +
        b * (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then w H else 0) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro H _
      by_cases heH : e ∈ H.val.edgeSet <;> simp [heH,k]
    rw [hsum,hu e he,hw e he,Nat.mul_one]
    exact hab
  · have hk : (∑ H, k H) = a * (∑ H, u H) + b * L := by
      simp only [k,Finset.sum_add_distrib,← Finset.mul_sum,L]
    rw [hk]
    have h₁ := Nat.mul_le_mul_left a hbu
    have h₂ := Nat.mul_le_mul_right L hb
    have h₃ := Nat.mul_le_mul_left (2 * Fintype.card V) ham
    change a * (∑ H, u H) + b * L ≤ (2 * Fintype.card V + 1) * s
    nlinarith

end Erdos184.FractionalCycles
