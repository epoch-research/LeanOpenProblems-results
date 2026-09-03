import FormalConjecturesUtil
import Submission.OrientedAnchors

/-! Polynomial edge bounds when a designated forbidden root is excluded
from one prescribed shore of a bipartite host. -/
open SimpleGraph Filter Asymptotics Finset
namespace Erdos713RootPower
open Erdos713Rate Erdos713KST Erdos713C6 Erdos713Anchors Erdos713ThreeSide

/-- Host graphs use Fin n, which suffices for extremal-number bounds. -/
def RootPowerBound {W : Type*} (H : SimpleGraph W) (x : W) (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ S : Set (Fin n),
    G.IsBipartiteWith S Sᶜ → (∀ f : H.Copy G, f x ∉ S) →
      (Nat.card G.edgeSet : ℝ) ≤ C*(n : ℝ)^r

lemma RootPowerBound.of_copy {A B : Type*} {H : SimpleGraph A} {J : SimpleGraph B}
    (f : H.Copy J) (x : A) {r : ℝ} (h : RootPowerBound J (f x) r) : RootPowerBound H x r := by
  obtain ⟨C,hC,hbound⟩ := h
  refine ⟨C,hC,?_⟩
  intro n G S hB hroot
  exact hbound n G S hB (fun g => hroot (g.comp f))

lemma kst {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) (x : Fin s ⊕ Fin t) :
    RootPowerBound (Kst s t) x (((s-1+s : ℕ) : ℝ)/s) := by
  classical
  refine ⟨((s+1)^s*(t+1) : ℕ),by positivity,?_⟩
  intro n G S hB hroot
  have hp := Erdos713OrientedKST.edge_pow_le_of_root_excluded G S hB hs ht x hroot
  have hb := Erdos713KstGluing.real_bound_of_power hs (Nat.succ_le_of_lt (by positivity)) hp
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_fin] using hb

lemma augmented {A B : Type*} [Fintype A] [Fintype B] (R : A → B → Prop)
    (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v) (x : A ⊕ (Fin 2 ⊕ B)) :
    RootPowerBound (bipGraph (Erdos713Anchors.augmented R)) x ((3 : ℝ)/2) := by
  classical
  refine ⟨(Fintype.card A+(Fintype.card A+Fintype.card B+2)^2+1 : ℕ),by positivity,?_⟩
  intro n G S hB hroot
  have hp := Erdos713OrientedAnchors.edge_sq_le_of_root_excluded R G S hB hR x hroot
  have hb := Erdos713KstGluing.real_bound_of_power (by decide : 1 ≤ 2)
    (Nat.succ_le_of_lt (by positivity)) hp
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_fin,Nat.cast_ofNat] using hb

lemma exceptional_columns {A B W : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) (E : Set B) (hE : Nat.card E ≤ 2)
    (hR : ∀ b ∉ E, Nat.card {a // R a b} ≤ 2) {H : SimpleGraph W}
    (hhi : H ⊑ bipGraph R) (x : W) : RootPowerBound H x ((3 : ℝ)/2) := by
  classical
  let R' : A → ↥(Eᶜ) → Prop := fun a b => R a b.val
  have hR' (b : ↥(Eᶜ)) : Fintype.card {a // R' a b} ≤ 2 := by
    simpa only [R',Nat.card_eq_fintype_card] using hR b.val b.prop
  obtain ⟨f⟩ := hhi.trans (contained_in_augmented R E hE)
  exact (augmented R' (Erdos713DRC.pair_cover_of_degree_two R' hR') (f x)).of_copy f x

lemma cycle_root_move (n : ℕ) (x a : Fin n) :
    ∃ e : cycleGraph n ≃g cycleGraph n, e x = a := by
  cases n with
  | zero => exact x.elim0
  | succ n =>
    let e : cycleGraph (n+1) ≃g cycleGraph (n+1) :=
      ⟨Equiv.addRight (a-x),by intro u v; exact circulantGraph_adj_translate⟩
    refine ⟨e,?_⟩
    change x+(a-x) = a
    abel

lemma c6 (x : Fin 6) : RootPowerBound C6 x ((4 : ℝ)/3) := by
  classical
  refine ⟨(512*(24^3+1) : ℕ),by positivity,?_⟩
  intro n G S hB hroot
  have hfree : C6.Free G := by
    rintro ⟨f⟩
    have hx : f x ∈ Sᶜ := hroot f
    have hadj : C6.Adj x (x+1) := by rw [cycleGraph_adj]; exact Or.inr (by simp)
    have hmem : f (x+1) ∈ S := hB.symm.mem_of_mem_adj hx (f.toHom.map_adj hadj)
    obtain ⟨e,he⟩ := cycle_root_move 6 x (x+1)
    have hh := hroot (f.comp e.toCopy)
    change f (e x) ∉ S at hh
    exact hh (he ▸ hmem)
  have hb := Erdos713KstGluing.real_bound_of_power (by decide : 1 ≤ 3)
    (by norm_num : 1 ≤ 512*(24^3+1)) (Erdos713C6.edge_cube_le G hfree)
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_fin,Nat.cast_ofNat] using hb

lemma matrix_core {B : Type*} [Fintype B] (R : Fin 3 → B → Prop)
    (hd : ∀ v, 2 ≤ Nat.card ((bipGraph R).neighborSet v)) :
    ∃ r : ℚ, HasRate (bipGraph R) (r : ℝ) ∧
      ∀ x, RootPowerBound (bipGraph R) x (r : ℝ) := by
  classical
  by_cases hFull : 3 ≤ Nat.card {b // ∀ i, R i b}
  · have hBcard : 1 ≤ Fintype.card B := by
      have hh := Fintype.card_subtype_le (fun b : B => ∀ i, R i b)
      simp only [Fintype.card_eq_nat_card] at hh ⊢
      omega
    obtain ⟨f⟩ := matrix_contained_K3t R
    refine ⟨5/3,by simpa using k3t_rate (contains_K33_of_three_full_columns R hFull) ⟨f⟩,?_⟩
    intro x
    simpa using (kst (s := 3) (by decide) hBcard (f x)).of_copy f x
  by_cases hC4 : Erdos713C4.K22 ⊑ bipGraph R
  · have hE : Nat.card {b // ∀ i, R i b} ≤ 2 := by omega
    have hr := two_exception_columns_rate R {b | ∀ i, R i b}
      hE (fun b hb => nonfull_column_small R b hb) hC4 (.refl _)
    refine ⟨3/2,by simpa using hr,?_⟩
    intro x
    simpa using exceptional_columns R {b | ∀ i, R i b} hE
      (fun b hb => nonfull_column_small R b hb) (.refl _) x
  obtain ⟨e⟩ := matrix_iso_C6_of_no_rectangle R hd hC4
  refine ⟨4/3,by simpa using c6_rate ⟨e.symm.toCopy⟩ ⟨e.toCopy⟩,?_⟩
  intro x
  simpa using (c6 (e x)).of_copy e.toCopy x

lemma small_core {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) (S : Set W) (hB : H.IsBipartiteWith S Sᶜ)
    (hS : Nat.card S ≤ 3) (hd : ∀ v, 2 ≤ Nat.card (H.neighborSet v)) :
    ∃ r : ℚ, HasRate H (r : ℝ) ∧ ∀ x, RootPowerBound H x (r : ℝ) := by
  classical
  by_cases hS2 : Nat.card S ≤ 2
  · have hhi := Erdos713SmallCore.contained_of_small_bipartition H S hS2 hB
    have hd' : ∀ v, 2 ≤ H.degree v := by
      intro v
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hd v
    have hlo := Erdos713SmallCore.contains_K22_of_degree_two H hd' hhi
    obtain ⟨f⟩ := hhi
    refine ⟨3/2,by simpa using k2t_rate hlo ⟨f⟩,?_⟩
    intro x
    simpa using (kst (s := 2) (by decide) (Nat.succ_le_of_lt Fintype.card_pos) (f x)).of_copy f x
  obtain ⟨R,⟨e⟩⟩ := exists_matrix_iso H S hB (by omega)
  have hd' : ∀ v, 2 ≤ Nat.card ((bipGraph R).neighborSet v) := by
    intro v
    rw [Nat.card_congr (e.symm.mapNeighborSet v)]
    exact hd (e.symm v)
  obtain ⟨r,hr,hroot⟩ := matrix_core R hd'
  exact ⟨r,iso_rate e hr,fun x => (hroot (e x)).of_copy e.toCopy x⟩

#print axioms exceptional_columns
#print axioms c6
#print axioms small_core
end Erdos713RootPower
