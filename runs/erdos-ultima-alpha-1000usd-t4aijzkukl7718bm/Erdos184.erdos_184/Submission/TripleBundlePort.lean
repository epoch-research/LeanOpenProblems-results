import Submission.TripleBundleCode

/-! A distinguished closing-edge coordinate for the three-bundle obstruction.
This concerns circuit-code contraction and does not disprove Erdős 184. -/
open scoped Classical symmDiff
namespace Erdos184Serial.TripleBundle.Port
open BinaryExtension
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {A : Type*} [DecidableEq A]

lemma eraseNone_sdiff (s t : Finset (Option (Edge A))) :
    (s \ t).eraseNone = s.eraseNone \ t.eraseNone := by
  ext e
  simp

/-- A chain of three bundles with one edge joining the ends. -/
def code : Code (Option (Edge A)) where
  valid s := ∀ i, count s.eraseNone i % 2 = if none ∈ s then 1 else 0
  empty := by intro i; simp [count, row]
  diff := by
    intro s t hs ht hts i
    have hsub : t.eraseNone ⊆ s.eraseNone := by
      intro e he
      exact Finset.mem_eraseNone.mpr (hts (Finset.mem_eraseNone.mp he))
    have hc := count_sdiff_add hsub i
    have hi := hs i
    have hj := ht i
    rw [eraseNone_sdiff]
    by_cases hn : none ∈ t
    · have hn' := hts hn
      simp only [hn, hn', if_true, Finset.mem_sdiff, not_true_eq_false, and_false,
        if_false] at hi hj ⊢
      omega
    · by_cases hn' : none ∈ s
      · simp only [hn, hn', if_false, if_true, Finset.mem_sdiff, not_false_eq_true,
          and_self] at hi hj ⊢
        omega
      · simp only [hn, hn', if_false, Finset.mem_sdiff, false_and] at hi hj ⊢
        omega

lemma eraseNone_symmDiff (s t : Finset (Option (Edge A))) :
    (s ∆ t).eraseNone = s.eraseNone ∆ t.eraseNone := by
  ext e
  simp only [Finset.mem_eraseNone, Finset.mem_symmDiff]

lemma code_xorClosed : XorClosed (code (A := A)) := by
  intro s t hs ht i
  rw [eraseNone_symmDiff, count_mod_symmDiff, Nat.add_mod, hs i, ht i]
  by_cases h1 : none ∈ s <;> by_cases h2 : none ∈ t <;>
    simp [Finset.mem_symmDiff, h1, h2]

lemma lift_pair_valid (i : Fin 3) {a b : A} (hab : a ≠ b) :
    code.valid (({(i, a), (i, b)} : Finset (Edge A)).map Function.Embedding.some) := by
  intro j
  rw [Finset.eraseNone_map_some]
  have hn : none ∉ (({(i, a), (i, b)} : Finset (Edge A)).map Function.Embedding.some) := by simp
  rw [if_neg hn]
  exact pair_source_valid i hab j

lemma circuit_card_of_not_mem {s : Finset (Option (Edge A))} (hs : Circuit code s)
    (hn : none ∉ s) : s.card = 2 := by
  obtain ⟨e, he⟩ := hs.2.1
  cases e with
  | none => exact (hn he).elim
  | some e =>
    have he' := Finset.mem_eraseNone.mpr he
    have hp := count_pos_of_mem he'
    have hv := hs.1 e.1
    rw [if_neg hn] at hv
    have htwo : 2 ≤ count s.eraseNone e.1 := by omega
    obtain ⟨a, b, hab, ha, hb⟩ := exists_row_pair htwo
    let p : Finset (Option (Edge A)) :=
      ({(e.1, a), (e.1, b)} : Finset (Edge A)).map Function.Embedding.some
    have hsub : p ⊆ s := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_eraseNone.mp ha
      · exact Finset.mem_eraseNone.mp hb
    have hvp : code.valid p := lift_pair_valid e.1 hab
    have hne : p.Nonempty := by simp [p]
    have heq := hs.2.2 p hsub hvp hne
    have hpair : (e.1, a) ≠ (e.1, b) := by
      intro hh
      exact hab (Prod.mk.inj hh).2
    rw [← heq, Finset.card_map, Finset.card_pair hpair]

lemma circuit_card_of_mem {s : Finset (Option (Edge A))} (hs : Circuit code s)
    (hn : none ∈ s) : s.card = 4 := by
  have hle (i : Fin 3) : count s.eraseNone i ≤ 1 := by
    by_contra hh
    have htwo : 2 ≤ count s.eraseNone i := by omega
    obtain ⟨a, b, hab, ha, hb⟩ := exists_row_pair htwo
    let p : Finset (Option (Edge A)) :=
      ({(i, a), (i, b)} : Finset (Edge A)).map Function.Embedding.some
    have hsub : p ⊆ s := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_eraseNone.mp ha
      · exact Finset.mem_eraseNone.mp hb
    have hvp : code.valid p := lift_pair_valid i hab
    have heq := hs.2.2 p hsub hvp (by simp [p])
    have hnp : none ∉ p := by simp [p]
    exact hnp (heq.symm ▸ hn)
  have hc (i : Fin 3) : count s.eraseNone i = 1 := by
    have h1 := hle i
    have h2 := hs.1 i
    rw [if_pos hn] at h2
    omega
  have hsum := count_sum s.eraseNone
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one] at hsum
  have hcard := Finset.card_eraseNone_of_mem hn
  have hpos := Finset.card_pos.mpr ⟨none, hn⟩
  omega

lemma partition_card_of_mem {s : Finset (Option (Edge A))}
    {D : Finset (Finset (Option (Edge A)))} (hD : Partition code s D)
    (hn : none ∈ s) : 2 * D.card + 2 = s.card := by
  have hn' := hn
  rw [← hD.2.2] at hn'
  obtain ⟨p, hp, hnp⟩ := Finset.mem_biUnion.mp hn'
  change none ∈ p at hnp
  have hpc : p.card = 4 := circuit_card_of_mem (hD.1 p hp) hnp
  have hother (q) (hq : q ∈ D.erase p) : q.card = 2 := by
    have hqm := Finset.mem_of_mem_erase hq
    apply circuit_card_of_not_mem (hD.1 q hqm)
    intro hnq
    exact Finset.disjoint_left.mp (hD.2.1 hqm hp (Finset.ne_of_mem_erase hq)) hnq hnp
  have hsum : s.card = ∑ q ∈ D, q.card := by
    have hh := Finset.card_biUnion (s := D) (t := id) hD.2.1
    rw [hD.2.2] at hh
    exact hh
  have he : ∑ q ∈ D.erase p, q.card = 2 * (D.card - 1) := by
    calc
      _ = ∑ q ∈ D.erase p, 2 := Finset.sum_congr rfl hother
      _ = _ := by simp [Finset.card_erase_of_mem hp, mul_comm]
  have hs := Finset.sum_erase_add D (fun q => q.card) hp
  change (∑ q ∈ D.erase p, q.card) + p.card = ∑ q ∈ D, q.card at hs
  rw [he, hpc, ← hsum] at hs
  have hpos := Finset.card_pos.mpr ⟨p, hp⟩
  omega

lemma full_valid (r : ℕ) :
    (code (A := Fin (2 * r + 1))).valid Finset.univ := by
  intro i
  have he : (Finset.univ : Finset (Option (Edge (Fin (2 * r + 1))))).eraseNone =
      Finset.univ := by ext e; simp
  rw [he, count_univ, Fintype.card_fin, if_pos (Finset.mem_univ _)]
  omega

lemma full_rigid (r : ℕ) :
    Rigid (code (A := Fin (2 * r + 1))) Finset.univ (3 * r + 1) := by
  intro D hD
  have hc := partition_card_of_mem hD (Finset.mem_univ none)
  simp only [Finset.card_univ, Fintype.card_option, Fintype.card_prod,
    Fintype.card_fin] at hc
  omega

lemma full_minimalCore (r : ℕ) :
    MinimalCore (code (A := Fin (2 * r + 1))) Finset.univ (3 * r + 1) :=
  minimalCore_of_rigid (full_valid r) (full_rigid r)

/-- Erasing the distinguished edge coordinate gives exactly the triangle-bundle
code, the circuit-code operation corresponding to edge contraction. -/
lemma projection_valid_iff (s : Finset (Edge A)) :
    target.valid s ↔ ∃ t, code.valid t ∧ t.eraseNone = s := by
  constructor
  · intro hs
    by_cases h0 : count s 0 % 2 = 0
    · refine ⟨s.map Function.Embedding.some, ?_, Finset.eraseNone_map_some s⟩
      intro i
      rw [Finset.eraseNone_map_some]
      have hn : none ∉ s.map Function.Embedding.some := by simp
      rw [if_neg hn]
      exact (hs i 0).trans h0
    · refine ⟨s.insertNone, ?_, Finset.eraseNone_insertNone s⟩
      intro i
      rw [Finset.eraseNone_insertNone, if_pos (Finset.none_mem_insertNone (s := s))]
      have hi := hs i 0
      omega
  · rintro ⟨t, ht, rfl⟩
    exact fun i j => (ht i).trans (ht j).symm

/-- Unbounded loss under puncturing one coordinate, even on rigid minimal cores. -/
theorem unbounded_contraction_hull_loss (c : ℕ) :
    ∃ (C : Code (Option (Edge (Fin (2 * (c + 1) + 1)))) )
      (B : Code (Edge (Fin (2 * (c + 1) + 1)))) ,
      XorClosed C ∧ XorClosed B ∧
      (∀ s, B.valid s ↔ ∃ t, C.valid t ∧ t.eraseNone = s) ∧
      MinimalCore C Finset.univ (3 * (c + 1) + 1) ∧
      HullBound B (2 * (c + 1) + 1) ∧
      2 * (c + 1) + 1 + c < 3 * (c + 1) + 1 := by
  refine ⟨code, target, code_xorClosed, target_xorClosed, projection_valid_iff,
    full_minimalCore (c + 1), ?_, by omega⟩
  simpa only [Fintype.card_fin] using target_hullBound (A := Fin (2 * (c + 1) + 1))

#print axioms code_xorClosed
#print axioms full_minimalCore
#print axioms projection_valid_iff
#print axioms unbounded_contraction_hull_loss
end Erdos184Serial.TripleBundle.Port
