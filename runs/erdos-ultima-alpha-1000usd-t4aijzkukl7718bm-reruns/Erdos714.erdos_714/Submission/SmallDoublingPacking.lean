import Submission.EnergyThinning

/-!
Small-doubling neighborhoods cannot attain the fourth-case Zarankiewicz scale.
These are necessary conditions on a construction, not a proof or disproof of Erdős 714.
-/

open Finset SimpleGraph
open scoped Pointwise
open Classical

set_option maxHeartbeats 1000000

namespace Erdos714SmallDoubling

variable {V Y : Type*} [AddCommGroup V] [Fintype V] [Fintype Y]

omit [Fintype V] in
/-- Small doubling forces a cubic, rather than merely quartic, energy lower bound. -/
lemma cubic_energy (S : Finset V) (K : ℕ) (hS : (S + S).card ≤ K * S.card) :
    S.card ^ 3 ≤ K * S.addEnergy S := by
  by_cases hz : S.card = 0
  · simp [hz]
  have hp : 0 < S.card := Nat.pos_of_ne_zero hz
  have he := (le_card_add_mul_addEnergy S S).trans
    (Nat.mul_le_mul_right (S.addEnergy S) hS)
  apply (Nat.mul_le_mul_left_iff hp).mp
  calc
    S.card * S.card ^ 3 = S.card ^ 2 * S.card ^ 2 := by ring
    _ ≤ K * S.card * S.addEnergy S := he
    _ = S.card * (K * S.addEnergy S) := by ring

/-- A cubic edge bound valid for any indexed family of small-doubling sets. -/
theorem cubic_incidence_bound (N : Y → Finset V) (K : ℕ)
    (hN : ∀ y, (N y + N y).card ≤ K * (N y).card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Packing.incidence N)) :
    (∑ y : Y, (N y).card) ^ 3 ≤ Fintype.card Y ^ 2 * K *
      (3 * Fintype.card V ^ 3 + 4 * Fintype.card V * ∑ y : Y, (N y).card) := by
  have hm := pow_sum_le_card_mul_sum_pow
    (s := (univ : Finset Y)) (f := fun y => (N y).card) (by intros; omega) 2
  simp only [card_univ] at hm
  calc
    _ ≤ Fintype.card Y ^ 2 * ∑ y : Y, (N y).card ^ 3 := hm
    _ ≤ Fintype.card Y ^ 2 * ∑ y : Y, K * (N y).addEnergy (N y) :=
      Nat.mul_le_mul_left _ (sum_le_sum (fun y _ => cubic_energy (N y) K (hN y)))
    _ = Fintype.card Y ^ 2 * K * ∑ y : Y, (N y).addEnergy (N y) := by
      rw [← mul_sum, ← mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _
      (Erdos714EnergyThinning.neighborhood_energy_bound N hfree)

/-- At most `q^4` rows and exactly `q^4` points imply `e^3 ≤ 7 K q^20`. -/
theorem critical_cubic_bound (N : Y → Finset V) (q K : ℕ)
    (hV : Fintype.card V = q ^ 4) (hY : Fintype.card Y ≤ q ^ 4)
    (hN : ∀ y, (N y + N y).card ≤ K * (N y).card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Packing.incidence N)) :
    (∑ y : Y, (N y).card) ^ 3 ≤ 7 * K * q ^ 20 := by
  have he : (∑ y : Y, (N y).card) ≤ q ^ 8 := by
    calc
      _ ≤ ∑ _ : Y, Fintype.card V := sum_le_sum (fun y _ => card_le_univ _)
      _ = Fintype.card Y * Fintype.card V := by simp
      _ ≤ q ^ 4 * q ^ 4 := by rw [hV]; gcongr
      _ = q ^ 8 := by ring
  calc
    _ ≤ Fintype.card Y ^ 2 * K *
        (3 * Fintype.card V ^ 3 + 4 * Fintype.card V * ∑ y : Y, (N y).card) :=
      cubic_incidence_bound N K hN hfree
    _ ≤ (q ^ 4) ^ 2 * K * (3 * (q ^ 4) ^ 3 + 4 * q ^ 4 * q ^ 8) := by
      rw [hV]
      gcongr
    _ = _ := by ring

/-- A critical-size construction must have doubling constant at least linear in `q`. -/
theorem required_doubling (N : Y → Finset V) (q K C : ℕ) (hq : 0 < q)
    (hV : Fintype.card V = q ^ 4) (hY : Fintype.card Y ≤ q ^ 4)
    (hN : ∀ y, (N y + N y).card ≤ K * (N y).card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Packing.incidence N))
    (he : q ^ 7 ≤ C * ∑ y : Y, (N y).card) :
    q ≤ 7 * K * C ^ 3 := by
  have hcube := critical_cubic_bound N q K hV hY hN hfree
  have hb : q ^ 20 * q ≤ q ^ 20 * (7 * K * C ^ 3) := by
    calc
      _ = (q ^ 7) ^ 3 := by ring
      _ ≤ (C * ∑ y : Y, (N y).card) ^ 3 := Nat.pow_le_pow_left he 3
      _ = C ^ 3 * (∑ y : Y, (N y).card) ^ 3 := by ring
      _ ≤ C ^ 3 * (7 * K * q ^ 20) := Nat.mul_le_mul_left _ hcube
      _ = _ := by ring
  exact (Nat.mul_le_mul_left_iff (pow_pos hq 20)).mp hb

/-- A positive fraction of the edges must lie in neighborhoods with large doubling.

No homogeneity, linearity, translation invariance, or regularity of the graph is assumed.
-/
theorem large_doubling_edges (N : Y → Finset V) (q K C : ℕ) (hq : 0 < q)
    (hV : Fintype.card V = q ^ 4) (hY : Fintype.card Y ≤ q ^ 4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Packing.incidence N))
    (he : q ^ 7 ≤ C * ∑ y : Y, (N y).card) (hK : 56 * K * C ^ 3 < q) :
    q ^ 7 ≤ 2 * C * ∑ y : Y,
      if K * (N y).card < (N y + N y).card then (N y).card else 0 := by
  let L : Y → Finset V := fun y =>
    if K * (N y).card < (N y + N y).card then ∅ else N y
  have hsub (y : Y) : L y ⊆ N y := by
    dsimp [L]
    split_ifs <;> simp
  have hL (y : Y) : (L y + L y).card ≤ K * (L y).card := by
    dsimp [L]
    split_ifs with hy
    · simp
    · omega
  have hfL : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Packing.incidence L) := by
    apply (Erdos714Packing.free_iff_no_rectangle L (by decide)).mpr
    intro f g hfg
    exact (Erdos714Packing.free_iff_no_rectangle N (by decide)).mp hfree f g
      (fun i j => hsub _ (hfg i j))
  have hsmall : ¬ q ^ 7 ≤ (2 * C) * ∑ y : Y, (L y).card := by
    intro hh
    have hq' := required_doubling L q K (2 * C) hq hV hY hL hfL hh
    have hid : 7 * K * (2 * C) ^ 3 = 56 * K * C ^ 3 := by ring
    rw [hid] at hq'
    omega
  have hsum : (∑ y : Y, (L y).card) +
      (∑ y : Y, if K * (N y).card < (N y + N y).card then (N y).card else 0) =
      ∑ y : Y, (N y).card := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro y _
    dsimp [L]
    split_ifs <;> simp
  nlinarith

end Erdos714SmallDoubling

#print axioms Erdos714SmallDoubling.cubic_energy
#print axioms Erdos714SmallDoubling.cubic_incidence_bound
#print axioms Erdos714SmallDoubling.critical_cubic_bound
#print axioms Erdos714SmallDoubling.required_doubling

#print axioms Erdos714SmallDoubling.large_doubling_edges
