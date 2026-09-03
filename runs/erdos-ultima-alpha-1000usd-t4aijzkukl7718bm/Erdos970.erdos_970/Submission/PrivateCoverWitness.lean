import Submission.OptimalCoverCore

/-! Kernel-checkable finite witness data for covers with two private positions per class. -/
namespace Erdos970.OptimalCoverCore

theorem exists_full_cover_of_private_witnesses (m k : ℕ)
    (R : List (ℕ × ℕ × ℕ × ℕ))
    (hv : 
    (∀ c ∈ R, c.1.Prime) ∧
    (∀ c ∈ R, ∀ d ∈ R, c.1 = d.1 → c = d) ∧
    (∀ i : Fin m, ∃ c ∈ R, i.val % c.1 = c.2.1) ∧
    (∀ c ∈ R,
      c.2.2.1 < m ∧ c.2.2.2 < m ∧ c.2.2.1 ≠ c.2.2.2 ∧
      c.2.2.1 % c.1 = c.2.1 ∧ c.2.2.2 % c.1 = c.2.1 ∧
      ∀ d ∈ R, d.1 ≠ c.1 →
        c.2.2.1 % d.1 ≠ d.2.1 ∧ c.2.2.2 % d.1 ≠ d.2.1))
    (hcard : R.toFinset.card = k) :
    ∃ P : Finset ℕ, ∃ r : ℕ → ℕ,
      (∀ p ∈ P, p.Prime) ∧ P.card = k ∧
      survivors m P r = ∅ ∧
      ∀ p ∈ P, 2 ≤ (privatePositions m P r p).card := by
  classical
  let K := R.toFinset
  let f : K → ℕ := fun c => c.val.1
  let g : K → ℕ := fun c => c.val.2.1
  have hf : Function.Injective f := by
    intro c d hcd
    apply Subtype.ext
    exact hv.2.1 c.val (List.mem_toFinset.mp c.property)
      d.val (List.mem_toFinset.mp d.property) hcd
  let P := K.image Prod.fst
  let r := Function.extend f g (fun _ => 0)
  have hr (c : ℕ × ℕ × ℕ × ℕ) (hc : c ∈ K) : r c.1 = c.2.1 :=
    hf.extend_apply g (fun _ => 0) ⟨c, hc⟩
  have hcP (p : ℕ) (hp : p ∈ P) : ∃ c ∈ K, c.1 = p := Finset.mem_image.mp hp
  refine ⟨P, r, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := hcP p hp
    exact hv.1 c (List.mem_toFinset.mp hc)
  · have hinj : Set.InjOn Prod.fst (↑K : Set (ℕ × ℕ × ℕ × ℕ)) := by
      intro c hc d hd hcd
      exact hv.2.1 c (List.mem_toFinset.mp hc) d (List.mem_toFinset.mp hd) hcd
    change (K.image Prod.fst).card = k
    rw [Finset.card_image_of_injOn hinj]
    exact hcard
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨him, hiP⟩ := (mem_survivors m P r i).mp hi
    obtain ⟨c, hc, hic⟩ := hv.2.2.1 ⟨i, him⟩
    have hcK : c ∈ K := List.mem_toFinset.mpr hc
    apply hiP c.1 (Finset.mem_image.mpr ⟨c, hcK, rfl⟩)
    change i % c.1 = r c.1 % c.1
    rw [hr c hcK, ← hic, Nat.mod_mod]
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := hcP p hp
    obtain ⟨hi, hj, hij, hip, hjp, hother⟩ := hv.2.2.2 c (List.mem_toFinset.mp hc)
    have hprivate (x : ℕ) (hx : x < m) (hxp : x % c.1 = c.2.1)
        (hxo : ∀ d ∈ R, d.1 ≠ c.1 → x % d.1 ≠ d.2.1) :
        x ∈ privatePositions m P r c.1 := by
      apply Finset.mem_filter.mpr
      constructor
      · apply (mem_survivors m (P.erase c.1) r x).mpr
        refine ⟨hx, ?_⟩
        intro q hq hxq
        obtain ⟨d, hd, rfl⟩ := hcP q (Finset.mem_of_mem_erase hq)
        have hne : d.1 ≠ c.1 := (Finset.mem_erase.mp hq).1
        apply hxo d (List.mem_toFinset.mp hd) hne
        have hres := hr d hd
        have hdmod : d.2.1 < d.1 := by
          have hh := hv.2.2.2 d (List.mem_toFinset.mp hd)
          rw [← hh.2.2.2.1]
          exact Nat.mod_lt _ (hv.1 d (List.mem_toFinset.mp hd)).pos
        change x % d.1 = r d.1 % d.1 at hxq
        simpa [hres, Nat.mod_eq_of_lt hdmod] using hxq
      · change x % c.1 = r c.1 % c.1
        rw [hr c hc, ← hxp, Nat.mod_mod]
    have hi' := hprivate c.2.2.1 hi hip (fun d hd hne => (hother d hd hne).1)
    have hj' := hprivate c.2.2.2 hj hjp (fun d hd hne => (hother d hd hne).2)
    have hsub : {c.2.2.1, c.2.2.2} ⊆ privatePositions m P r c.1 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi'
      · exact hj'
    have hh := Finset.card_le_card hsub
    simpa [hij] using hh


#print axioms exists_full_cover_of_private_witnesses
end Erdos970.OptimalCoverCore
