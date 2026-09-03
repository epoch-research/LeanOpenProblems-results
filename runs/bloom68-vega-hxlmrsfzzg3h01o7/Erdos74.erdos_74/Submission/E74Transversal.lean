import Submission.E74Bounds
import Submission.E74Certificate
import Submission.E74Locality
import Submission.E74Potential
import Submission.E74Buffer

/-!
# A localized independent transversal

The third-color vertices introduced at one stage lie outside a wide buffer about
all the new bad edges.  The inductive correction stays inside that buffer.
Consequently both corrections can use the same third color.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- A sufficiently small hereditary cut budget gives an independent transversal,
localized near the bad edges of any starting assignment. -/
theorem exists_localized_transversal (t : ℕ) :
    ∀ (G : SimpleGraph V) (p : V → Bool), (badEdges G p).card = t →
      SmallCuts G certificateBound →
      ∃ (I : Set V) (p' : V → Bool), Independent G I ∧ ProperOff G I p' ∧
        ∀ v ∈ I, Near G (ends (badEdges G p) : Set V) (radiusBound t) v := by
  classical
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro G p hcard hG
    by_cases ht0 : t = 0
    · have hempty : badEdges G p = ∅ := Finset.card_eq_zero.mp (hcard.trans ht0)
      refine ⟨∅, p, ?_, ?_, ?_⟩
      · intro u v _ hu _
        exact Set.notMem_empty u hu
      · intro u v huv _ _
        exact (badEdges_eq_empty_iff G p).mp hempty huv
      · intro v hv
        exact (Set.notMem_empty v hv).elim
    by_cases ht1 : t = 1
    · obtain ⟨e, he⟩ := Finset.card_eq_one.mp (hcard.trans ht1)
      induction e using Sym2.inductionOn with
      | hf u v =>
        have he_mem : s(u, v) ∈ badEdges G p := by rw [he]; simp
        refine ⟨{u}, p, ?_, ?_, ?_⟩
        · intro a b hab ha hb
          have ha' : a = u := ha
          have hb' : b = u := hb
          subst a b
          exact G.loopless u hab
        · intro a b hab ha hb hp
          have habmem := (mem_badEdges G p a b).mpr ⟨hab, hp⟩
          rw [he, Finset.mem_singleton] at habmem
          have hu : u ∈ s(a, b) := habmem.symm ▸ Sym2.mem_mk_left u v
          rcases Sym2.mem_iff.mp hu with hua | hub
          · exact ha (by simpa only [Set.mem_singleton_iff] using hua.symm)
          · exact hb (by simpa only [Set.mem_singleton_iff] using hub.symm)
        · intro a ha
          have ha' : a = u := ha
          subst a
          exact near_of_mem (mem_ends_left he_mem)
    have ht : 2 ≤ t := by omega
    obtain ⟨T, hT, hTcard⟩ := exists_shortSupport_of_smallCuts G certificateBound hG
      ht (two_le_lengthBound (by omega)) (le_refl (certificateBound t))
    obtain ⟨S, hS⟩ := exists_minimalSupport G (lengthBound t)
    have hs : S.card < t := (hS.2 T hT).trans_lt hTcard
    have hsF : S.card ≤ (badEdges G p).card := by rw [hcard]; exact hs.le
    let r := radiusBound (t - 1)
    have hlength : 16 * (badEdges G p).card * (r + 2) ≤ lengthBound t := by
      rw [hcard]
      exact le_rfl
    obtain ⟨q, hqedge, hqnear⟩ := exists_terminal_assignment p hS.1 hsF hlength
    obtain ⟨Z, p₁, hZ, hbad, hfar, hnear⟩ :=
      buffered_recolor_of_terminal_assignment p q hS.1.1 hqedge hqnear
    obtain ⟨I, p₂, hI, hproper, hloc⟩ :=
      ih S.card hs (mask G Z) p₁ (by rw [hbad]) (hG.mask Z)
    have hInear : ∀ v ∈ I, Near G (ends S : Set V) r v := by
      intro v hv
      have hn := hloc v hv
      rw [hbad] at hn
      exact near_mono_graph (mask_le G Z)
        (near_mono_radius (radiusBound_le_pred hs) hn)
    have hSW : (ends S : Set V) ⊆ (ends (badEdges G p ∪ S) : Set V) :=
      ends_mono Finset.subset_union_right
    have hIoff : ∀ v ∈ I, v ∉ Z := by
      intro v hv hz
      exact hfar v hz (near_mono_set hSW (near_mono_radius (by omega) (hInear v hv)))
    have hcross : ∀ z ∈ Z, ∀ v ∈ I, ¬ G.Adj z v := by
      intro z hz v hv hadj
      exact hfar z hz (near_mono_set hSW (near_prepend hadj (hInear v hv)))
    refine ⟨Z ∪ I, p₂, ?_, ?_, ?_⟩
    · intro u v huv hu hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact hZ huv hu hv
      · exact hcross u hu v hv huv
      · exact hcross v hv u hu huv.symm
      · exact hI ⟨huv, hIoff u hu, hIoff v hv⟩ hu hv
    · intro u v huv hu hv
      exact hproper ⟨huv, fun hz => hu (Or.inl hz), fun hz => hv (Or.inl hz)⟩
        (fun hi => hu (Or.inr hi)) (fun hi => hv (Or.inr hi))
    · intro v hv
      have hvW : Near G (ends (badEdges G p ∪ S) : Set V) (r + 3) v := by
        rcases hv with hv | hv
        · exact hnear v hv
        · exact near_mono_set hSW (near_mono_radius (by omega) (hInear v hv))
      have hW : ∀ w ∈ (ends (badEdges G p ∪ S) : Set V),
          Near G (ends (badEdges G p) : Set V) (S.card * lengthBound t) w := by
        intro w hw
        rw [ends_union, Finset.mem_coe, Finset.mem_union] at hw
        rcases hw with hw | hw
        · exact near_of_mem hw
        · exact minimalSupport_near_badEdges hS p w hw
      have hn := near_trans hvW hW
      have hbound := radiusBound_comp hs
      apply near_mono_radius (show (r + 3) + S.card * lengthBound t ≤ radiusBound t by
        dsimp [r]
        omega) hn

/-- The hereditary cut bounds force three colors, uniformly in the number of vertices. -/
theorem finite_colorable_three_of_smallCuts (G : SimpleGraph V)
    (hG : SmallCuts G certificateBound) : G.Colorable 3 := by
  obtain ⟨I, p, hI, hp, _⟩ := exists_localized_transversal
    (badEdges G (fun _ => false)).card G (fun _ => false) rfl hG
  exact colorable_three_of_independent_properOff hI hp

end E74
