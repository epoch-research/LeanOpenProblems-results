import Submission.SublogHostClippingExplore
import Submission.CertifiedSparseRestorationMenuExplore

/-! A single sparse replacement menu whose every remote restored host admits
one-target clipping, with thresholds uniform over all later deletion choices. -/
namespace Erdos66ClippableSparseRestorationMenu
open Filter AdditiveCombinatorics Erdos66Counting Erdos66Fractional
  Erdos66ClampedPrefixContinuation Erdos66SparseRankTransversal
  Erdos66UniformSparseRestorationMenu Erdos66SublogPatternInvariants
  Erdos66SublogHostClipping Erdos66OrderedPartialReplacement Erdos66Explore
open scoped Classical Topology
set_option maxHeartbeats 3000000

lemma envelope_of_sublog_change (A B : Set ℕ) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (henv : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2))
    (hinc : Tendsto (fun n : ℕ ↦ ((sumRep B n : ℝ)-sumRep A n)/Real.log ((n : ℝ)+2))
      atTop (𝓝 0)) :
    ∃ KB : ℝ, 0 ≤ KB ∧ ∀ n, (sumRep B n : ℝ) ≤ KB+(C+1)*Real.log ((n : ℝ)+2) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hinc.eventually_le_const (by norm_num : (0 : ℝ)<1))
  refine ⟨K+(N+1 : ℕ),by positivity,?_⟩
  intro n
  have hlog : 0<Real.log ((n : ℝ)+2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hNpos := Nat.cast_nonneg (α := ℝ) (N+1)
  by_cases hn : N ≤ n
  · have hh := (div_le_iff₀ hlog).mp (hN n hn)
    have ha := henv n
    nlinarith only [hh,ha,hNpos]
  · have hh : (sumRep B n : ℝ) ≤ (N+1 : ℕ) := by
      exact_mod_cast (sumRep_le_succ B n).trans (show n+1 ≤ N+1 by omega)
    have hp := mul_nonneg (show 0 ≤ C+1 by linarith) hlog.le
    linarith

/-- The existential correction at n is not required to be the same for
different n. In particular this definition does not encode an iteration. -/
def ClipsAt (B : Set ℕ) (c ε : ℝ) (n : ℕ) : Prop := ∃ D F : Finset ℕ,
    F.card=D.card ∧ Disjoint (F : Set ℕ) B ∧
    (∀ u∈D∪F, n/5 ≤ u ∧ u ≤ 2*n) ∧
    (∀ L, PrefixBrackets profile (swap B D F) L) ∧
    min (sumRep B n) (⌊c*Real.log (n : ℝ)⌋₊-1) ≤ sumRep (swap B D F) n ∧
    sumRep (swap B D F) n ≤ ⌊c*Real.log (n : ℝ)⌋₊ ∧
    ∀ z, z≠n → |(sumRep (swap B D F) z : ℝ)-sumRep B z| ≤ ε*Real.log ((z : ℝ)+2)

/-- The same replacement set precedes the deletion set E, both tolerances,
and the target. The eventual clipping threshold is independent of E. -/
theorem exists_uniformly_clippable_sparse_restoration_menu
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (henv : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2))
    (hB : SmallBoundary A) (hT : SublogCentral A)
    (D : Set ℕ) (hDA : D ⊆ A)
    (hdec : Tendsto (fun n : ℕ ↦ (count D n : ℝ)/Real.sqrt ((n : ℝ)*Real.log n)) atTop (𝓝 0)) :
    ∃ (N₀ : ℕ) (F : Set ℕ), Disjoint F A ∧
      Tendsto (fun n : ℕ ↦ ((sumRep (A∪F) n : ℝ)-sumRep A n)/Real.log ((n : ℝ)+2)) atTop (𝓝 0) ∧
      (∀ E : Set ℕ, E ⊆ D → (∀ d∈E, N₀ ≤ d) →
        ∀ L, PrefixBrackets profile (restoredFrom A hbr F E) L) ∧
      ∀ c ε : ℝ, 0<c → 0<ε → ∀ᶠ n : ℕ in atTop,
        ∀ E : Set ℕ, E ⊆ D → (∀ d∈E, N₀ ≤ d) → ClipsAt (restoredFrom A hbr F E) c ε n := by
  obtain ⟨N₀,F,hFA,himage,hinj,hloc,hFlim⟩ := exists_sparse_rank_transversal A hbr D hDA hdec
  change assignment A hbr '' F={d | d∈D ∧ N₀ ≤ d} at himage
  change Set.InjOn (assignment A hbr) F at hinj
  change ∀ u∈F, assignment A hbr u ≤ 2*u ∧ u ≤ 2*assignment A hbr u at hloc
  have hbrE (E : Set ℕ) (hED : E ⊆ D) (hEN : ∀ d∈E, N₀ ≤ d) :
      ∀ L, PrefixBrackets profile (restoredFrom A hbr F E) L := by
    apply restoredFrom_brackets A hbr F E hFA ?_ hinj (fun u hu ↦ (hloc u hu).2)
    intro d hd
    rw [himage]
    exact ⟨hED hd,hEN d hd⟩
  have hAU : A ⊆ A∪F := Set.subset_union_left
  have hBU := smallBoundary_insert A (A∪F) hAU hB hFlim
  have hTU := sublogCentral_insert A (A∪F) hAU hT hFlim
  obtain ⟨KU,hKU,henvU⟩ := envelope_of_sublog_change A (A∪F) K C hK hC henv hFlim
  refine ⟨N₀,F,hFA,hFlim,hbrE,?_⟩
  intro c ε hc hε
  filter_upwards [host_eventually_uniform_downward_clipping (A∪F) KU (C+1)
    hKU (by linarith) henvU hBU hTU c ε hc hε] with n hn
  intro E hED hEN
  apply hn (restoredFrom A hbr F E) ?_ (hbrE E hED hEN)
  intro u hu
  rcases hu with hu | hu
  · exact Or.inl hu.1
  · exact Or.inr hu.1

end Erdos66ClippableSparseRestorationMenu
