import FormalConjecturesUtil
import Submission.CompactSupportAudit

/-! Lower rooted thresholds localize to actual blocks without an attained
rooted upper bound. This yields an ordinary-block-rate or genuine polynomial
root-gap dichotomy, not rationality of either threshold. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713RootBlocks
open Erdos713Blocks Erdos713Rate Erdos713RootPower Erdos713Gluing
universe u

/-- A lower threshold for rooted power bounds; no upper bound is asserted. -/
def RootLower {W : Type*} (H : SimpleGraph W) (x : W) (r : ℝ) : Prop :=
  ∀ a : ℝ, 1 ≤ a → RootPowerBound H x a → r ≤ a

lemma RootLower.of_reachable {W : Type*} {H : SimpleGraph W} {x y : W} {r : ℝ}
    (h : RootLower H x r) (hxy : H.Reachable x y) : RootLower H y r :=
  fun a ha hu => h a ha (hu.of_reachable hxy.symm)

lemma root_lower_of_rate {W : Type*} {H : SimpleGraph W} {r : ℝ}
    (h : HasRate H r) (x : W) : RootLower H x r :=
  fun a ha hu => h.lower a ha hu.upper

/-- Finite extraction needs a lower threshold only. The selected block need
not have a rooted upper bound at r. -/
lemma exists_block_root_lower {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {x : W} {r : ℝ} (hr : 1 < r) (hR : RootLower G x r) :
    ∃ S : Set W, IsBlock G S ∧ 3 ≤ Nat.card S ∧ ∀ y, RootLower (G.induce S) y r := by
  classical
  by_contra hn
  push_neg at hn
  have hEach (S : Set W) : ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
      (IsBlock G S → 3 ≤ Nat.card S → ∀ y, RootPowerBound (G.induce S) y a) := by
    by_cases hS : IsBlock G S ∧ 3 ≤ Nat.card S
    · obtain ⟨y,hy⟩ := hn S hS.1 hS.2
      change ¬ ∀ a : ℝ, 1 ≤ a → RootPowerBound (G.induce S) y a → r ≤ a at hy
      push_neg at hy
      obtain ⟨a,ha,hroot,har⟩ := hy
      exact ⟨a,ha,har,fun _ _ z => hroot.of_reachable (hS.1.connected y z)⟩
    · exact ⟨1,le_rfl,hr,fun hBlock hc => (hS ⟨hBlock,hc⟩).elim⟩
  choose a ha har hEach using hEach
  obtain ⟨S₀,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Set W)) a
    ⟨∅,Finset.mem_univ _⟩
  have hBound : BlockUpper G (a S₀) := by
    intro S hS hc y
    exact (hEach S hS hc y).mono (hmax S (Finset.mem_univ _))
  exact (not_lt_of_ge (hR (a S₀) (ha S₀)
    (root_bound_of_blocks G hG (ha S₀) hBound x))) (har S₀)

/-- The same selected cyclic block either has the ordinary rate r, or has an
ordinary upper bound strictly below r while all rooted upper exponents are
at least r. Thus the second alternative is not merely a logarithmic gap. -/
lemma ordinary_block_or_strict_root_gap {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {r : ℝ} (hr : 1 < r) (hR : HasRate G r) :
    ∃ S : Set W, IsBlock G S ∧ 3 ≤ Nat.card S ∧
      (∀ y, RootLower (G.induce S) y r) ∧
      (HasRate (G.induce S) r ∨ ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
        (fun n : ℕ => (extremalNumber n (G.induce S) : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ)^a)) := by
  classical
  obtain ⟨x⟩ := hG.nonempty
  obtain ⟨S,hS,hc,hLower⟩ := exists_block_root_lower G hG hr (root_lower_of_rate hR x)
  refine ⟨S,hS,hc,hLower,?_⟩
  by_cases hRate : HasRate (G.induce S) r
  · exact Or.inl hRate
  · right
    have hupper : (fun n : ℕ => (extremalNumber n (G.induce S) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^r) :=
      (extremal_mono_bigO ⟨Copy.induce G S⟩).trans hR.upper
    have hNoLower : ¬ ∀ a : ℝ, 1 ≤ a →
        ((fun n : ℕ => (extremalNumber n (G.induce S) : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ)^a)) → r ≤ a :=
      fun hh => hRate ⟨hr.le,hupper,hh⟩
    push_neg at hNoLower
    obtain ⟨a,ha,hu,har⟩ := hNoLower
    exact ⟨a,ha,har,hu⟩

lemma RootLower.not_opposite_upper {W : Type*} {H : SimpleGraph W} {x y : W}
    {r a : ℝ} (h : RootLower H x r) (hxy : H.Adj x y) (ha : 1 ≤ a) (har : a < r) :
    ¬ (fun n : ℕ => (extremalNumber n (wedge H x H y) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^a) := by
  intro hu
  exact (not_lt_of_ge (h a ha (of_opposite_wedge_upper H hxy (by linarith) hu))) har

/-- A genuine root gap contains a positive rational-width gap. No upper rate
or exact asymptotic is inferred for the opposite-root doubles. -/
lemma rational_bracket_of_strict_root_gap {W : Type*} (H : SimpleGraph W)
    {r a : ℝ} (ha : 1 ≤ a) (har : a < r)
    (hu : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^a)) (hLower : ∀ x, RootLower H x r) :
    ∃ p q : ℚ, 1 ≤ p ∧ p < q ∧ (q : ℝ) < r ∧
      (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^(p : ℝ)) ∧
      ∀ x y, H.Adj x y →
        ¬ (fun n : ℕ => (extremalNumber n (wedge H x H y) : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ)^(q : ℝ)) := by
  obtain ⟨p,hap,hpr⟩ := exists_rat_btwn har
  obtain ⟨q,hpq,hqr⟩ := exists_rat_btwn hpr
  have hp : (1 : ℝ) ≤ p := ha.trans hap.le
  have hq : (1 : ℝ) ≤ q := hp.trans hpq.le
  refine ⟨p,q,by exact_mod_cast hp,by exact_mod_cast hpq,hqr,
    hu.trans (rpow_mono_bigO hap.le),?_⟩
  intro x y hxy
  exact (hLower x).not_opposite_upper hxy hq hqr

/-- One root-shifting self-copy per actual cyclic block suffices to localize
an attained ordinary exponent. No rationality of the block rates is assumed. -/
lemma exists_block_ordinary_rate_of_shifts {W : Type u} [Fintype W]
    (G : SimpleGraph W) (hG : G.Connected) {r : ℝ} (hr : 1 < r) (hR : HasRate G r)
    (hShift : ∀ S : Set W, IsBlock G S → 3 ≤ Nat.card S →
      ∃ x : S, ∃ e : (G.induce S).Copy (G.induce S), (G.induce S).Adj x (e x)) :
    ∃ S : Set W, IsBlock G S ∧ 3 ≤ Nat.card S ∧ HasRate (G.induce S) r := by
  obtain ⟨S,hS,hc,hLower,hAlt⟩ := ordinary_block_or_strict_root_gap G hG hr hR
  refine ⟨S,hS,hc,?_⟩
  rcases hAlt with hRate | ⟨a,ha,har,hu⟩
  · exact hRate
  · obtain ⟨x,e,he⟩ := hShift S hS hc
    exact ((not_lt_of_ge (hLower x a ha
      (of_root_shift (G.induce S) x e he (by linarith) hu))) har).elim


/-- At an irrational ordinary rate, the SAME block from the rate-or-gap
alternative is outside the completed small-shore/C10 families. -/
lemma remaining_block_with_rate_or_gap {W : Type u} [Fintype W]
    (G : SimpleGraph W) (hG : G.Connected) (hB : G.IsBipartite)
    {r : ℝ} (hr : 1 < r) (hR : HasRate G r)
    (hIrr : r ∉ Set.range ((↑) : ℚ → ℝ)) :
    ∃ S : Set W, IsBlock G S ∧ (G.induce S).IsBipartite ∧ 8 ≤ Nat.card S ∧
      (∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v)) ∧
      (∀ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ → 4 ≤ Nat.card A) ∧
      ¬ G.induce S ⊑ Erdos713C10.C10 ∧
      ¬ Erdos713ActualBlocks.RootedRate (G.induce S) ∧
      (∀ y, RootLower (G.induce S) y r) ∧
      (HasRate (G.induce S) r ∨ ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
        (fun n : ℕ => (extremalNumber n (G.induce S) : ℝ)) =O[atTop]
          (fun n : ℕ => (n : ℝ)^a)) := by
  classical
  obtain ⟨S,hS,hc,hLower,hAlt⟩ := ordinary_block_or_strict_root_gap G hG hr hR
  haveI : Nonempty S := hS.connected.nonempty
  have hd := hS.noCut.min_degree hS.connected (by
    simpa only [Fintype.card_eq_nat_card] using hc)
  have hu : (fun n : ℕ => (extremalNumber n (G.induce S) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r) :=
    (extremal_mono_bigO ⟨Copy.induce G S⟩).trans hR.upper
  have hNoRoot : ¬ Erdos713ActualBlocks.RootedRate (G.induce S) := by
    rintro ⟨q,hq,hRoot⟩
    let x : S := Classical.arbitrary S
    exact hIrr ⟨q,le_antisymm (hq.lower r hr.le hu) (hLower x q hq.one_le (hRoot x))⟩
  have hPiece : ¬ Erdos713CycleAssembly.Piece (G.induce S) :=
    fun hp => hNoRoot (hp.rooted_rate hd)
  have hSmall : ¬ ∃ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ ∧ Nat.card A ≤ 3 :=
    fun hh => hPiece (Or.inl hh)
  push_neg at hSmall
  have hSB : (G.induce S).IsBipartite := Colorable.of_hom (Copy.induce G S).toHom hB
  have hc' : 8 ≤ Nat.card S := by
    by_contra hc'
    obtain ⟨A,hA,hcard⟩ := Erdos713ThreeSide.small_bipartition_of_card_le_seven (G.induce S) hSB
      (by simpa only [Fintype.card_eq_nat_card] using (show Nat.card S ≤ 7 by omega))
    exact (not_lt_of_ge hcard) (hSmall A hA)
  exact ⟨S,hS,hSB,hc',hd,fun A hA => hSmall A hA,
    fun hh => hPiece (Or.inr hh),hNoRoot,hLower,hAlt⟩

#print axioms exists_block_root_lower
#print axioms ordinary_block_or_strict_root_gap
#print axioms RootLower.not_opposite_upper
#print axioms rational_bracket_of_strict_root_gap
#print axioms exists_block_ordinary_rate_of_shifts
#print axioms remaining_block_with_rate_or_gap
end Erdos713RootBlocks
