import FormalConjecturesUtil
import Submission.CompactTenCycle

/-! Rooted power bounds from an actual root-moving self-copy. In particular,
ordinary cycle upper bounds give bounds at every designated cycle root. -/
open SimpleGraph Filter Asymptotics Finset
namespace Erdos713RootPower
open Erdos713Rate

lemma global_free_bound_of_upper {W : Type*} (H : SimpleGraph W) {r : ℝ}
    (hr : 0 ≤ r)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (G : SimpleGraph (Fin n)), H.Free G →
      (Nat.card G.edgeSet : ℝ) ≤ C*(n : ℝ)^r := by
  classical
  obtain ⟨C,hC,hbound⟩ := h.exists_pos
  obtain ⟨N,hN⟩ := eventually_atTop.mp hbound.bound
  let M : ℕ := (range N).sup (fun n => extremalNumber n H)
  refine ⟨C+M,by positivity,?_⟩
  intro n G hG
  by_cases hn : n = 0
  · subst n
    have he : G = ⊥ := Subsingleton.elim _ _
    simp only [he,edgeSet_bot,Nat.card_eq_fintype_card,Fintype.card_ofIsEmpty,Nat.cast_zero]
    positivity
  have hnp : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow : 1 ≤ (n : ℝ)^r := Real.one_le_rpow hnp hr
  have he : (Nat.card G.edgeSet : ℝ) ≤ extremalNumber n H := by
    exact_mod_cast (by simpa only [edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_fin] using
      card_edgeFinset_le_extremalNumber hG)
  apply he.trans
  by_cases hnN : N ≤ n
  · have hh := hN n hnN
    rw [Real.norm_natCast,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg M))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · have hm : (extremalNumber n H : ℝ) ≤ M := by
      exact_mod_cast (Finset.le_sup (f := fun n => extremalNumber n H) (mem_range.mpr (by omega : n < N)))
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith

lemma of_root_shift {W : Type*} (H : SimpleGraph W) (x : W) (e : H.Copy H)
    (he : H.Adj x (e x)) {r : ℝ} (hr : 0 ≤ r)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r)) : RootPowerBound H x r := by
  obtain ⟨C,hC,hbound⟩ := global_free_bound_of_upper H hr h
  refine ⟨C,hC,?_⟩
  intro n G S hB hroot
  apply hbound n G
  rintro ⟨f⟩
  have hmem : f (e x) ∈ S := hB.symm.mem_of_mem_adj (hroot f) (f.toHom.map_adj he)
  exact hroot (f.comp e) hmem

lemma cycle_of_upper {m : ℕ} (hm : 2 ≤ m) (x : Fin m) {r : ℝ} (hr : 0 ≤ r)
    (h : (fun n : ℕ => (extremalNumber n (cycleGraph m) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r)) : RootPowerBound (cycleGraph m) x r := by
  obtain ⟨k,rfl⟩ : ∃ k, m = k+2 := ⟨m-2,by omega⟩
  obtain ⟨e,he⟩ := cycle_root_move (k+2) x (x+1)
  apply of_root_shift _ x e.toCopy _ hr h
  change (cycleGraph (k+2)).Adj x (e x)
  rw [he,cycleGraph_adj]
  exact Or.inr (by simp)

lemma c10 (x : Fin 10) : RootPowerBound Erdos713C10.C10 x ((6 : ℝ)/5) :=
  cycle_of_upper (by decide) x (by norm_num) Erdos713C10.rate.upper

lemma even_cycle_upper {k : ℕ} (hk : 2 ≤ k) (x : Fin (2*k)) :
    RootPowerBound (cycleGraph (2*k)) x (((k+1 : ℕ) : ℝ)/k) :=
  cycle_of_upper (by omega) x (by positivity) (Erdos713EvenCycle.upper hk)


lemma wedge_rate_of_root_shift {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (hNoIso : ∀ v, ∃ w, H.Adj v w)
    (e : H.Copy H) (he : H.Adj x (e x))
    (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z) {a b : ℝ}
    (hH : HasRate H a) (hJ : HasRate J b) :
    HasRate (Erdos713Gluing.wedge H x J y) (max a b) :=
  wedge_rate H x hNoIso J y hy hH hJ
    (of_root_shift H x e he (le_trans (by norm_num) hH.one_le) hH.upper)

#print axioms global_free_bound_of_upper
#print axioms of_root_shift
#print axioms c10
#print axioms wedge_rate_of_root_shift
end Erdos713RootPower

namespace Erdos713CycleCore

lemma iso_of_min_degree_two_copy {W T : Type*} [Fintype W] [Nonempty W] [Fintype T]
    {H : SimpleGraph W} {G : SimpleGraph T} (f : H.Copy G)
    (hH : ∀ v, 2 ≤ Nat.card (H.neighborSet v))
    (hG : ∀ v, Nat.card (G.neighborSet v) = 2) (hConn : G.Connected) : Nonempty (H ≃g G) := by
  classical
  have hlocal (a : W) (v : T) (hav : G.Adj (f a) v) : ∃ b, H.Adj a b ∧ f b = v := by
    let g : H.neighborSet a → G.neighborSet (f a) := fun b => ⟨f b.val,f.toHom.map_adj b.prop⟩
    have hinj : Function.Injective g := by
      intro b c he
      exact Subtype.ext (f.injective (congrArg (fun q : G.neighborSet (f a) => q.val) he))
    have hcard : Fintype.card (H.neighborSet a) = Fintype.card (G.neighborSet (f a)) := by
      have hle := Fintype.card_le_of_injective g hinj
      have hlow := hH a
      have htwo := hG (f a)
      simp only [Fintype.card_eq_nat_card] at hle ⊢
      omega
    have hsurj := ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hinj,hcard⟩).2
    obtain ⟨b,hb⟩ := hsurj ⟨v,hav⟩
    exact ⟨b.val,b.prop,congrArg (fun q : G.neighborSet (f a) => q.val) hb⟩
  have hclosed : ∀ a ∈ Set.range f, ∀ b, G.Adj a b → b ∈ Set.range f := by
    rintro a ⟨a,rfl⟩ b hab
    obtain ⟨c,_,hc⟩ := hlocal a b hab
    exact ⟨c,hc⟩
  have hsurj : Function.Surjective f := by
    let a : W := Classical.arbitrary W
    intro v
    exact Erdos713Blocks.mem_of_reachable_closed hclosed ⟨a,rfl⟩ (hConn (f a) v)
  refine ⟨⟨Equiv.ofBijective f ⟨f.injective,hsurj⟩,?_⟩⟩
  intro a b
  change G.Adj (f a) (f b) ↔ H.Adj a b
  constructor
  · intro hab
    obtain ⟨c,hac,hcb⟩ := hlocal a (f b) hab
    exact f.injective hcb ▸ hac
  · exact f.toHom.map_adj

lemma contained_c10 {W : Type*} [Fintype W] [Nonempty W] (H : SimpleGraph W)
    (hd : ∀ v, 2 ≤ Nat.card (H.neighborSet v)) (hH : H ⊑ Erdos713C10.C10) :
    Nonempty (H ≃g Erdos713C10.C10) := by
  obtain ⟨f⟩ := hH
  apply iso_of_min_degree_two_copy f hd _ cycleGraph_connected
  intro v
  simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using
    (cycleGraph_degree_three_le (n := 7) (v := v))

#print axioms iso_of_min_degree_two_copy
#print axioms contained_c10
end Erdos713CycleCore
