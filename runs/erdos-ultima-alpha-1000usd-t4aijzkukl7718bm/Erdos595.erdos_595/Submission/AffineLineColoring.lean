import Submission.Work

/-!
Countable fields admit countable colorings of vector spaces with no three
 distinct collinear points monochromatic. This is a conditional tool for the
 finite-field representation approach, not a settlement of Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595AffineLine

variable {I K : Type*} [LinearOrder I] [Field K]

noncomputable def code (x : I →₀ K) : List K := x.support.sort.map x

lemma code_nil (x : I →₀ K) : code x = [] ↔ x = 0 := by
  rw [code, List.map_eq_nil_iff, ← List.length_eq_zero_iff, Finset.length_sort,
    Finset.card_eq_zero, Finsupp.support_eq_empty]

lemma code_nonzero (x : I →₀ K) {a : K} (ha : a ∈ code x) : a ≠ 0 := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  exact Finsupp.mem_support_iff.mp ((Finset.mem_sort _).mp hi)

lemma code_cons (x : I →₀ K) (a : I) (ha : a ∈ x.support)
    (hmin : ∀ i ∈ x.support, a ≤ i) :
    code x = x a :: code (x.erase a) := by
  classical
  have hs : x.support.sort = a :: (x.support.erase a).sort := by
    conv_lhs => rw [← Finset.insert_erase ha]
    exact Finset.sort_insert _ (fun i hi => hmin i (Finset.mem_erase.mp hi).2)
      (Finset.notMem_erase a x.support)
  rw [code,hs,List.map_cons,code,Finsupp.support_erase]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (Finsupp.erase_ne (Finset.mem_erase.mp ((Finset.mem_sort _).mp hi)).1).symm

lemma three_scalars {d α β γ x y z : K} (hd : d ≠ 0)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hs : α + β + γ = 0)
    (hx : x = 0 ∨ x = d) (hy : y = 0 ∨ y = d) (hz : z = 0 ∨ z = d)
    (hn : ¬(x = 0 ∧ y = 0 ∧ z = 0)) (he : α*x + β*y + γ*z = 0) :
    x = d ∧ y = d ∧ z = d := by
  have hab : α + β ≠ 0 := by intro h; exact hγ (by linear_combination hs - h)
  have hac : α + γ ≠ 0 := by intro h; exact hβ (by linear_combination hs - h)
  have hbc : β + γ ≠ 0 := by intro h; exact hα (by linear_combination hs - h)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;>
    rw [hx,hy,hz] at he hn ⊢
  · exact (hn ⟨rfl,rfl,rfl⟩).elim
  · simp_all
  · simp_all
  · have h : (β + γ) * d = 0 := by linear_combination he
    exact (mul_ne_zero hbc hd h).elim
  · simp_all
  · have h : (α + γ) * d = 0 := by linear_combination he
    exact (mul_ne_zero hac hd h).elim
  · have h : (α + β) * d = 0 := by linear_combination he
    exact (mul_ne_zero hab hd h).elim
  · exact ⟨rfl,rfl,rfl⟩

lemma rigid (l : List K) (x y z : I →₀ K)
    (hx : code x = l) (hy : code y = l) (hz : code z = l)
    (α β γ : K) (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hs : α + β + γ = 0) (he : α • x + β • y + γ • z = 0) :
    x = y ∧ x = z := by
  classical
  induction l generalizing x y z with
  | nil =>
    have h0 := (code_nil x).mp hx
    exact ⟨h0.trans ((code_nil y).mp hy).symm,h0.trans ((code_nil z).mp hz).symm⟩
  | cons d l ih =>
    have hd : d ≠ 0 := code_nonzero x (hx ▸ List.mem_cons_self)
    let S := x.support ∪ y.support ∪ z.support
    have hxS : x.support ⊆ S := fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
    have hyS : y.support ⊆ S := fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h)
    have hzS : z.support ⊆ S := fun _ h => Finset.mem_union_right _ h
    have hnS : S.Nonempty := by
      have hn : x ≠ 0 := by intro h; simp [h,code] at hx
      exact (Finsupp.support_nonempty_iff.mpr hn).mono hxS
    let a := S.min' hnS
    have ha : a ∈ S := Finset.min'_mem _ _
    have hm : ∀ i ∈ S, a ≤ i := fun i hi => Finset.min'_le _ _ hi
    have step (v : I →₀ K) (hv : code v = d :: l) (hvS : v.support ⊆ S) :
        v a = 0 ∨ (v a = d ∧ code (v.erase a) = l) := by
      by_cases ha : a ∈ v.support
      · have hc := code_cons v a ha (fun i hi => hm i (hvS hi))
        have hh := List.cons.inj (hc.symm.trans hv)
        exact Or.inr hh
      · exact Or.inl (Finsupp.notMem_support_iff.mp ha)
    have px := step x hx hxS
    have py := step y hy hyS
    have pz := step z hz hzS
    have hp : α * x a + β * y a + γ * z a = 0 := by
      simpa only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,Finsupp.zero_apply]
        using congrArg (fun v : I →₀ K => v a) he
    have hn : ¬(x a = 0 ∧ y a = 0 ∧ z a = 0) := by
      rintro ⟨h1,h2,h3⟩
      simp only [S,Finset.mem_union,Finsupp.mem_support_iff] at ha
      tauto
    have hp' := three_scalars hd hα hβ hγ hs
      (px.imp_right And.left) (py.imp_right And.left) (pz.imp_right And.left) hn hp
    have hxt := (px.resolve_left (fun h => hd (hp'.1.symm.trans h))).2
    have hyt := (py.resolve_left (fun h => hd (hp'.2.1.symm.trans h))).2
    have hzt := (pz.resolve_left (fun h => hd (hp'.2.2.symm.trans h))).2
    have herase : α • x.erase a + β • y.erase a + γ • z.erase a = 0 := by
      ext i
      by_cases hi : i = a
      · subst i; simp
      · simpa [Finsupp.erase_ne hi,Finsupp.smul_apply,smul_eq_mul]
          using congrArg (fun v : I →₀ K => v i) he
    obtain ⟨hxy,hxz⟩ := ih (x.erase a) (y.erase a) (z.erase a) hxt hyt hzt herase
    have finish (v w : I →₀ K) (hv : v a = d) (hw : w a = d)
        (he : v.erase a = w.erase a) : v = w := by
      ext i
      by_cases hi : i = a
      · subst i; exact hv.trans hw.symm
      · simpa only [Finsupp.erase_ne hi] using congrArg (fun v : I →₀ K => v i) he
    exact ⟨finish x y hp'.1 hp'.2.1 hxy,finish x z hp'.1 hp'.2.2 hxz⟩

/-- The palette is countable even when the vector-space dimension is arbitrary. -/
theorem coloring (K E : Type*) [Field K] [Countable K]
    [AddCommGroup E] [Module K E] :
    ∃ c : E → ℕ, ∀ x y z : E, ∀ t : K, t ≠ 0 → t ≠ 1 →
      z = t • x + (1-t) • y → c x = c y → c x = c z → x = y := by
  classical
  let b := Module.Free.chooseBasis K E
  let I := Module.Free.ChooseBasisIndex K E
  letI : LinearOrder I := IsWellOrder.linearOrder (@WellOrderingRel I)
  obtain ⟨enc,henc⟩ := exists_injective_nat (List K)
  refine ⟨fun x => enc (code (b.repr x)),?_⟩
  intro x y z t ht0 ht1 he hxy hxz
  apply b.repr.injective
  apply (rigid (code (b.repr x)) (b.repr x) (b.repr y) (b.repr z)
    rfl (henc hxy).symm (henc hxz).symm t (1-t) (-1) ht0
    (sub_ne_zero.mpr ht1.symm) (neg_ne_zero.mpr one_ne_zero) (by ring) ?_).1
  have h := congrArg b.repr he
  simp only [map_add,map_smul] at h
  rw [h]
  module

#print axioms coloring
end Erdos595AffineLine
