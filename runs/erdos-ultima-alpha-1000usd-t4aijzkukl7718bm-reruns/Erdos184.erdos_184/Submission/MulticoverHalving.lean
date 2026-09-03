import Submission.DyadicFractionalPartition

/-! An explicit conditional reduction from uniform additive multicover halving
 to Erdős 184. The halving hypothesis is not proved here. -/
open SimpleGraph Filter
open scoped Classical BigOperators
namespace Erdos184.FractionalCycles
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V]

/-- Natural multiplicities on ordinary simple cycles; no parallel digons. -/
def Covers (G : SimpleGraph V) (m : ℕ) (k : CyclePiece G → ℕ) : Prop :=
  ∀ e ∈ G.edgeSet, (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then k H else 0) = m

/-- Exact multiplicity one is an actual edge-disjoint decomposition. -/
lemma decomposition_of_unit_multicover (G : SimpleGraph V) (k : CyclePiece G → ℕ)
    (hk : Covers G 1 k) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ ∑ H, k H := by
  let S : Finset (CyclePiece G) := Finset.univ.filter (fun H => 0 < k H)
  let D : Finset G.Subgraph := S.image Subtype.val
  have hdis (H K : CyclePiece G) (hH : H ∈ S) (hK : K ∈ S) (hne : H ≠ K) :
      Disjoint H.val.edgeSet K.val.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heH heK
    have hh := hk e (H.val.edgeSet_subset heH)
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({H,K} : Finset (CyclePiece G)) ⊆ Finset.univ from Finset.subset_univ _)
      (f := fun J : CyclePiece G => if e ∈ J.val.edgeSet then k J else 0)
      (fun _ _ _ => Nat.zero_le _)
    simp only [Finset.sum_pair hne,if_pos heH,if_pos heK,hh] at hsum
    have hHp := (Finset.mem_filter.mp hH).2
    have hKp := (Finset.mem_filter.mp hK).2
    omega
  refine ⟨D,?_,⟨?_,?_⟩,?_⟩
  · intro H hH
    obtain ⟨J,_,rfl⟩ := Finset.mem_image.mp hH
    exact J.property
  · intro H hH K hK hne
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hK
    exact hdis J L hJ hL (fun h => hne (congrArg Subtype.val h))
  · ext e
    constructor
    · intro he
      obtain ⟨H,_,heH⟩ := Set.mem_iUnion₂.mp he
      exact H.edgeSet_subset heH
    · intro he
      have hpos : 0 < ∑ H : CyclePiece G, if e ∈ H.val.edgeSet then k H else 0 := by rw [hk e he]; decide
      obtain ⟨H,_,hH⟩ := Finset.sum_pos_iff.mp hpos
      have heH : e ∈ H.val.edgeSet := by by_contra hn; simp [hn] at hH
      have hkH : 0 < k H := by simpa only [if_pos heH] using hH
      exact Set.mem_iUnion₂.mpr ⟨H.val,Finset.mem_image.mpr
        ⟨H,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkH⟩,rfl⟩,heH⟩
  · calc
      D.card ≤ S.card := Finset.card_image_le
      _ = ∑ H ∈ S, (1 : ℕ) := by simp
      _ ≤ ∑ H ∈ S, k H := Finset.sum_le_sum (fun H hH => (Finset.mem_filter.mp hH).2)
      _ ≤ ∑ H, k H := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)

/-- The accumulated halving error is geometric, rather than one full error
per level. This is a numerical consequence of the displayed hypothesis. -/
lemma iterate_halving (G : SimpleGraph V) (B : ℕ)
    (hh : ∀ r (k : CyclePiece G → ℕ), Covers G (2^(r+1)) k →
      ∃ l : CyclePiece G → ℕ, Covers G (2^r) l ∧ 2 * (∑ H, l H) ≤ (∑ H, k H) + B)
    (r : ℕ) (k : CyclePiece G → ℕ) (hk : Covers G (2^r) k) :
    ∃ l : CyclePiece G → ℕ, Covers G 1 l ∧
      2^r * (∑ H, l H) ≤ (∑ H, k H) + B * (2^r-1) := by
  induction r generalizing k with
  | zero => exact ⟨k,by simpa using hk,by simp⟩
  | succ r ih =>
    obtain ⟨q,hq,hbq⟩ := hh r k hk
    obtain ⟨l,hl,hbl⟩ := ih q hq
    refine ⟨l,hl,?_⟩
    have hp : 0 < (2:ℕ)^r := pow_pos (by decide) r
    have he : 2^r-1+1 = (2:ℕ)^r := by omega
    rw [Nat.pow_succ]
    have he' : (2:ℕ)^r*2-1 = 2*(2^r-1)+1 := by omega
    rw [he']
    nlinarith

lemma bound_of_halving (G : SimpleGraph V) (hG : ∀ v, Even (G.degree v)) (B : ℕ)
    (hh : ∀ r (k : CyclePiece G → ℕ), Covers G (2^(r+1)) k →
      ∃ l : CyclePiece G → ℕ, Covers G (2^r) l ∧ 2 * (∑ H, l H) ≤ (∑ H, k H) + B) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ 2 * Fintype.card V + 1 + B := by
  obtain ⟨r,k,hk,hbk⟩ := exists_dyadic_multicover_linear G hG
  obtain ⟨l,hl,hbl⟩ := iterate_halving G B hh r k hk
  obtain ⟨D,hc,hd,hb⟩ := decomposition_of_unit_multicover G l hl
  refine ⟨D,hc,hd,?_⟩
  have hp : 0 < (2:ℕ)^r := pow_pos (by decide) r
  have hs : 2^r-1 ≤ (2:ℕ)^r := Nat.sub_le _ _
  have hmul := Nat.mul_le_mul_left B hs
  nlinarith

universe u
/-- A uniform vertex-linear halving error would settle the conjecture. The
existence of such a constant K is an explicit unproved premise. -/
lemma conjecture_of_uniform_halving (K : ℕ)
    (hh : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), (∀ v, Even (G.degree v)) →
      ∀ r (k : CyclePiece G → ℕ), Covers G (2^(r+1)) k →
      ∃ l : CyclePiece G → ℕ, Covers G (2^r) l ∧
        2 * (∑ H, l H) ≤ (∑ H, k H) + 2*K*Fintype.card V) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_cycle_bound.mpr
  refine ⟨2*K+3,?_⟩
  intro V _ _ G he
  cases isEmpty_or_nonempty V with
  | inl hV =>
    haveI := hV
    have hbot : G = ⊥ := Subsingleton.elim _ _
    subst G
    exact ⟨∅,by simp,by simp [IsDecomposition],by simp⟩
  | inr hV =>
    haveI := hV
    obtain ⟨D,hc,hd,hb⟩ := bound_of_halving G he (2*K*Fintype.card V) (hh G he)
    refine ⟨D,hc,hd,?_⟩
    have hn := Fintype.card_pos (α := V)
    have hnat : D.card ≤ (2*K+3)*Fintype.card V := by nlinarith
    exact_mod_cast hnat

end Erdos184.FractionalCycles
