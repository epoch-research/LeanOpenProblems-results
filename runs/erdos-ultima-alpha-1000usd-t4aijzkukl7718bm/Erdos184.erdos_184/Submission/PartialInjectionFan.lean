import Submission.EndpointBranches

/-! Finite fans of an injective partial self-map.  A point outside the image
cannot remain in the finite domain forever; fans from different such points
are disjoint, including their terminal points. -/
open scoped Classical
namespace Erdos184Work.PartialInjectionFan
set_option maxHeartbeats 500000
variable {V : Type*}

lemma exists_exit (S : Finset V) (f : V → V) (hi : Set.InjOn f S)
    (x : V) (hx : x ∉ S.image f) : ∃ n : ℕ, f^[n] x ∉ S := by
  by_contra! hstay
  let U := S.filter (fun y => ∃ n : ℕ, f^[n] x = y)
  have hxU : x ∈ U := Finset.mem_filter.mpr ⟨hstay 0,⟨0,rfl⟩⟩
  have hclosed (y : V) (hy : y ∈ U) : f y ∈ U := by
    obtain ⟨hyS,n,hn⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨?_,⟨n+1,?_⟩⟩
    · rw [← hn]
      simpa only [Function.iterate_succ_apply'] using hstay (n+1)
    · rw [Function.iterate_succ_apply',hn]
  let F : U → U := fun y => ⟨f y.val,hclosed y y.property⟩
  have hF : Function.Injective F := by
    intro y z hyz
    apply Subtype.ext
    exact hi (Finset.mem_filter.mp y.property).1 (Finset.mem_filter.mp z.property).1
      (congrArg Subtype.val hyz)
  obtain ⟨y,hy⟩ := Finite.surjective_of_injective hF ⟨x,hxU⟩
  apply hx
  exact Finset.mem_image.mpr ⟨y.val,(Finset.mem_filter.mp y.property).1,
    congrArg Subtype.val hy⟩

lemma first_exit_injective (S : Finset V) (f : V → V) (x : V) (n : ℕ)
    (hbefore : ∀ i < n, f^[i] x ∈ S) (hexit : f^[n] x ∉ S) :
    Function.Injective (fun i : Fin (n+1) => f^[i.val] x) := by
  have hlt (i j : ℕ) (hij : i < j) (hj : j ≤ n) : f^[i] x ≠ f^[j] x := by
    intro he
    have ht := congrArg (fun y => f^[n-j] y) he
    change f^[n-j] (f^[i] x) = f^[n-j] (f^[j] x) at ht
    rw [← Function.iterate_add_apply,← Function.iterate_add_apply,
      Nat.sub_add_cancel hj] at ht
    have hb := hbefore (n-j+i) (by omega)
    exact hexit (ht ▸ hb)
  intro i j he
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hlt i j h (by omega) he
  · exact hlt j i h (by omega) he.symm

lemma exists_first_exit (S : Finset V) (f : V → V) (hi : Set.InjOn f S)
    (x : V) (hx : x ∉ S.image f) :
    ∃ n : ℕ, n ≤ S.card ∧ (∀ i < n, f^[i] x ∈ S) ∧ f^[n] x ∉ S ∧
      Function.Injective (fun i : Fin (n+1) => f^[i.val] x) := by
  have he := exists_exit S f hi x hx
  let n := Nat.find he
  have hb : ∀ i < n, f^[i] x ∈ S := by
    intro i hi
    exact Classical.not_not.mp (Nat.find_min he hi)
  have hn : f^[n] x ∉ S := Nat.find_spec he
  have hinj := first_exit_injective S f x n hb hn
  have hc : n ≤ S.card := by
    let F : Fin n → S := fun i => ⟨f^[i.val] x,hb i.val i.isLt⟩
    have hF : Function.Injective F := by
      intro i j hij
      have he := hinj (a₁ := ⟨i.val,by omega⟩) (a₂ := ⟨j.val,by omega⟩)
        (congrArg Subtype.val hij)
      exact Fin.ext (congrArg (fun z : Fin (n+1) => z.val) he)
    simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective F hF
  exact ⟨n,hc,hb,hn,hinj⟩

lemma meeting_implies_same_start (S : Finset V) (f : V → V) (hi : Set.InjOn f S)
    (x y : V) (hx : x ∉ S.image f) (hy : y ∉ S.image f)
    (i j : ℕ) (hxi : ∀ k < i, f^[k] x ∈ S) (hyj : ∀ k < j, f^[k] y ∈ S)
    (he : f^[i] x = f^[j] y) : x = y := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => exact he
    | succ j =>
      apply False.elim
      apply hx
      exact Finset.mem_image.mpr ⟨f^[j] y,hyj j (by omega),
        by simpa only [Function.iterate_zero,id_eq,Function.iterate_succ_apply'] using he.symm⟩
  | succ i ih =>
    cases j with
    | zero =>
      apply False.elim
      apply hy
      exact Finset.mem_image.mpr ⟨f^[i] x,hxi i (by omega),
        by simpa only [Function.iterate_zero,id_eq,Function.iterate_succ_apply'] using he⟩
    | succ j =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply'] at he
      exact ih j (fun k hk => hxi k (by omega)) (fun k hk => hyj k (by omega))
        (hi (hxi i (by omega)) (hyj j (by omega)) he)

end Erdos184Work.PartialInjectionFan
#print axioms Erdos184Work.PartialInjectionFan.exists_first_exit
#print axioms Erdos184Work.PartialInjectionFan.meeting_implies_same_start
