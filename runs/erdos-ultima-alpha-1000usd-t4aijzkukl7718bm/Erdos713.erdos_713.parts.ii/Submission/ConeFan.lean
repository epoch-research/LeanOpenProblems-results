import FormalConjecturesUtil
import Submission.UpToEightCore

/-! A restricted two-root fan bound. This file does not assume the main conjecture. -/

open Filter SimpleGraph Asymptotics Finset

namespace Erdos713ConeFan
set_option maxHeartbeats 2000000

abbrev Base := Erdos713C6.bipGraph
  (fun (i : Fin 3) (j : Option (Fin 3)) => j.elim True (fun j => i ≠ j))
abbrev leftRoot : Fin 3 ⊕ Option (Fin 3) := Sum.inl 0
abbrev rightRoot : Fin 3 ⊕ Option (Fin 3) := Sum.inl 1
abbrev Fan (t : ℕ) := Erdos713EdgeFan.fan Base leftRoot rightRoot t

private def first : Fin 3 → Fin 3 := ![1, 0, 0]
private def second : Fin 3 → Fin 3 := ![2, 2, 1]
private lemma first_ne_second (j : Fin 3) : first j ≠ second j := by
  fin_cases j <;> decide
private lemma pair_cover (i j : Fin 3) (h : i ≠ j) : i = first j ∨ i = second j := by
  fin_cases i <;> fin_cases j <;> simp_all [first, second]

lemma rooted_copy_of_heavy {V : Type*} [Fintype V] (G : SimpleGraph V)
    (B : Finset V) (f : Fin 3 → V) (hf : Function.Injective f) (w : V)
    (hw : ∀ i, G.Adj w (f i)) (hwB : w ∉ B) (hfB : ∀ i, f i ∉ B)
    (hh : ∀ i j, i ≠ j → B.card + 7 ≤ Nat.card (G.commonNeighbors (f i) (f j))) :
    ∃ e : Base.Copy G, (∀ i, e (Sum.inl i) = f i) ∧ e (Sum.inr none) = w ∧
      ∀ a, e a ∉ B := by
  classical
  let L := B ∪ insert w (univ.image f)
  have hL : L.card ≤ B.card + 4 := by
    have h1 := card_union_le B (insert w (univ.image f))
    have h2 := card_insert_le w (univ.image f)
    have h3 : (univ.image f).card ≤ 3 := (card_image_le).trans (by simp)
    dsimp only [L]
    omega
  let S : Fin 3 → Finset V := fun j =>
    (G.commonNeighbors (f (first j)) (f (second j))).toFinset \ L
  have hS (j : Fin 3) : 3 ≤ (S j).card := by
    have h := hh _ _ (first_ne_second j)
    have h' := card_le_card_sdiff_add_card
      (s := (G.commonNeighbors (f (first j)) (f (second j))).toFinset) (t := L)
    rw [Set.toFinset_card, Fintype.card_eq_nat_card] at h'
    dsimp only [S]
    omega
  have hHall (T : Finset (Fin 3)) : T.card ≤ (T.biUnion S).card := by
    rcases T.eq_empty_or_nonempty with rfl | ⟨j,hj⟩
    · simp
    exact (card_le_univ T).trans ((show Fintype.card (Fin 3) ≤ (S j).card by simpa using hS j).trans
      (card_le_card (subset_biUnion_of_mem S hj)))
  obtain ⟨g,hg,hgS⟩ := (all_card_le_biUnion_card_iff_exists_injective S).mp hHall
  have hgL (j) : g j ∉ L := (mem_sdiff.mp (hgS j)).2
  have hgf (i j) : f i ≠ g j := by
    intro h
    exact hgL j (h ▸ mem_union_right B (mem_insert_of_mem (mem_image_of_mem f (mem_univ i))))
  have hgw (j) : w ≠ g j := by
    intro h
    exact hgL j (h ▸ mem_union_right B (mem_insert_self _ _))
  have hgB (j) : g j ∉ B := fun h => hgL j (mem_union_left _ h)
  have hAdj (i j : Fin 3) (hij : i ≠ j) : G.Adj (f i) (g j) := by
    have ht := (mem_sdiff.mp (hgS j)).1
    simp only [Set.mem_toFinset, mem_commonNeighbors] at ht
    rcases pair_cover i j hij with rfl | rfl
    · exact ht.1
    · exact ht.2
  let m : Fin 3 ⊕ Option (Fin 3) → V := Sum.elim f (fun j => j.elim w g)
  have hm : Function.Injective m := by
    rintro (i | (_ | j)) (i' | (_ | j')) he
    · exact congrArg Sum.inl (hf he)
    · exact ((hw i).ne (show w = f i from he.symm)).elim
    · exact (hgf i j' he).elim
    · exact ((hw i').ne he).elim
    · rfl
    · exact (hgw j' he).elim
    · exact (hgf i' j he.symm).elim
    · exact (hgw j he.symm).elim
    · exact congrArg (Sum.inr ∘ some) (hg he)
  let e : Base.Copy G := ⟨⟨m, by
    rintro (i | (_ | j)) (i' | (_ | j')) he
    · exact he.elim
    · exact (hw i).symm
    · exact hAdj i j' he
    · exact hw i'
    · exact he.elim
    · exact he.elim
    · exact (hAdj i' j he).symm
    · exact he.elim
    · exact he.elim⟩, hm⟩
  refine ⟨e,fun _ => rfl,rfl,?_⟩
  rintro (i | (_ | j))
  · exact hfB i
  · exact hwB
  · exact hgB j

lemma heavy_star_blocked {V : Type*} [Fintype V] (G : SimpleGraph V)
    (B : V → V → Finset V) {k : ℕ}
    (hsize : ∀ u v, (B u v).card ≤ k)
    (hroots : ∀ u v, u ∉ B u v ∧ v ∉ B u v)
    (hblock : ∀ u v, ∀ e : Base.Copy G, e leftRoot = u → e rightRoot = v →
      ∃ a, (a ≠ leftRoot ∧ a ≠ rightRoot) ∧ e a ∈ B u v)
    (w u v z : V) (hwu : G.Adj w u) (hwv : G.Adj w v) (hwz : G.Adj w z)
    (huv : u ≠ v) (huz : u ≠ z) (hvz : v ≠ z)
    (huvH : k+7 ≤ Nat.card (G.commonNeighbors u v))
    (huzH : k+7 ≤ Nat.card (G.commonNeighbors u z))
    (hvzH : k+7 ≤ Nat.card (G.commonNeighbors v z)) :
    w ∈ B u v ∨ z ∈ B u v := by
  classical
  by_contra h
  push_neg at h
  let f : Fin 3 → V := ![u,v,z]
  have hf : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have ha (i : Fin 3) : G.Adj w (f i) := by
    fin_cases i <;> assumption
  have hb (i : Fin 3) : f i ∉ B u v := by
    fin_cases i
    · exact (hroots u v).1
    · exact (hroots u v).2
    · exact h.2
  have hh (i j : Fin 3) (hij : i ≠ j) :
      (B u v).card + 7 ≤ Nat.card (G.commonNeighbors (f i) (f j)) := by
    have hab := Nat.add_le_add_right (hsize u v) 7
    have huv' := hab.trans huvH
    have huz' := hab.trans huzH
    have hvz' := hab.trans hvzH
    fin_cases i <;> fin_cases j <;>
      simp_all [f, commonNeighbors_symm]
  obtain ⟨e,he,heW,heB⟩ := rooted_copy_of_heavy G (B u v) f hf w ha h.1 hb hh
  obtain ⟨a,_,haB⟩ := hblock u v e (he 0) (he 1)
  exact heB a haB


noncomputable def quadCount {V : Type*} [Fintype V] (P : V → V → V → V → Prop) : ℕ := by
  classical
  exact ∑ w, ∑ u, ∑ v, ∑ z, if P w u v z then 1 else 0

lemma quadCount_mono {V : Type*} [Fintype V] {P Q : V → V → V → V → Prop}
    (h : ∀ w u v z, P w u v z → Q w u v z) : quadCount P ≤ quadCount Q := by
  classical
  unfold quadCount
  apply sum_le_sum; intro w _
  apply sum_le_sum; intro u _
  apply sum_le_sum; intro v _
  apply sum_le_sum; intro z _
  split_ifs with hp hq
  · rfl
  · exact (hq (h w u v z hp)).elim
  · exact Nat.zero_le _
  · rfl

lemma quadCount_or {V : Type*} [Fintype V] (P Q : V → V → V → V → Prop) :
    quadCount (fun w u v z => P w u v z ∨ Q w u v z) ≤ quadCount P + quadCount Q := by
  classical
  unfold quadCount
  simp only [← sum_add_distrib]
  apply sum_le_sum; intro w _
  apply sum_le_sum; intro u _
  apply sum_le_sum; intro v _
  apply sum_le_sum; intro z _
  by_cases hp : P w u v z <;> by_cases hq : Q w u v z <;> simp [hp,hq]

lemma quadCount_swap_uv {V : Type*} [Fintype V] (P : V → V → V → V → Prop) :
    quadCount (fun w u v z => P w v u z) = quadCount P := by
  classical
  unfold quadCount
  apply sum_congr rfl; intro w _
  rw [sum_comm]

lemma quadCount_swap_vz {V : Type*} [Fintype V] (P : V → V → V → V → Prop) :
    quadCount (fun w u v z => P w u z v) = quadCount P := by
  classical
  unfold quadCount
  apply sum_congr rfl; intro w _
  apply sum_congr rfl; intro u _
  rw [sum_comm]

def Star {V : Type*} (G : SimpleGraph V) (w u v z : V) : Prop :=
  G.Adj w u ∧ G.Adj w v ∧ G.Adj w z

lemma star_leaf_swap_uv {V : Type*} (G : SimpleGraph V) (w u v z : V) :
    Star G w v u z ↔ Star G w u v z := by unfold Star; tauto
lemma star_leaf_swap_vz {V : Type*} (G : SimpleGraph V) (w u v z : V) :
    Star G w u z v ↔ Star G w u v z := by unfold Star; tauto

lemma star_count {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    quadCount (Star G) = ∑ w, G.degree w ^ 3 := by
  classical
  have hc (w : V) : (∑ u : V, if G.Adj w u then 1 else 0 : ℕ) = G.degree w := by
    simpa only [sum_boole, Nat.cast_id, ← G.neighborFinset_eq_filter] using
      (G.card_neighborFinset_eq_degree w)
  unfold quadCount Star
  have hbool : ∀ (a b c : Prop) [Decidable a] [Decidable b] [Decidable c]
      [Decidable (a ∧ b ∧ c)], (if a ∧ b ∧ c then 1 else 0 : ℕ) =
    (if a then 1 else 0) * (if b then 1 else 0) * (if c then 1 else 0) := by
      intros; split_ifs <;> simp_all
  simp_rw [hbool]
  simp only [← mul_sum, ← sum_mul, hc, pow_succ, pow_zero, one_mul]

lemma diagonal_count {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    quadCount (fun w u v z => Star G w u v z ∧ u = v) = ∑ w, G.degree w ^ 2 := by
  classical
  have hc (w : V) : (∑ u : V, if G.Adj w u then 1 else 0 : ℕ) = G.degree w := by
    simpa only [sum_boole, Nat.cast_id, ← G.neighborFinset_eq_filter] using
      (G.card_neighborFinset_eq_degree w)
  unfold quadCount
  apply sum_congr rfl; intro w _
  have hbool : ∀ (u v z : V) [Decidable (Star G w u v z ∧ u = v)],
      (if Star G w u v z ∧ u = v then 1 else 0 : ℕ) =
    if v = u then (if G.Adj w u then 1 else 0) * (if G.Adj w z then 1 else 0) else 0 := by
      intros; unfold Star; split_ifs <;> simp_all
  simp_rw [hbool]
  simp_rw [sum_ite_irrel, sum_const_zero, ← mul_sum, hc]
  simp only [sum_ite_eq', mem_univ, ite_true]
  rw [← sum_mul, hc, pow_two]


private lemma and_indicator (a b : Prop) [Decidable a] [Decidable b] [Decidable (a ∧ b)] :
    (if a ∧ b then 1 else 0 : ℕ) = if a then (if b then 1 else 0) else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha,hb]

lemma center_count_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : V → V → Finset V) (k D : ℕ) (hS : ∀ u v, (S u v).card ≤ k)
    (hD : ∀ w, G.degree w ≤ D) :
    quadCount (fun w u v z => Star G w u v z ∧ w ∈ S u v) ≤
      k * Fintype.card V ^ 2 * D := by
  classical
  have hc (w : V) : (∑ u : V, if G.Adj w u then 1 else 0 : ℕ) = G.degree w := by
    simpa only [sum_boole, Nat.cast_id, ← G.neighborFinset_eq_filter] using
      (G.card_neighborFinset_eq_degree w)
  apply (quadCount_mono (Q := fun w u v z => w ∈ S u v ∧ G.Adj w z)
    (fun _ _ _ _ h => ⟨h.2,h.1.2.2⟩)).trans
  unfold quadCount
  rw [sum_comm]
  trans ∑ u : V, ∑ v : V, k * D
  · apply sum_le_sum; intro u _
    rw [sum_comm]
    apply sum_le_sum; intro v _
    simp only [and_indicator, sum_ite_irrel, hc, sum_const_zero]
    calc
      _ ≤ ∑ w : V, if w ∈ S u v then D else 0 := by
        apply sum_le_sum; intro w _
        split_ifs
        · exact hD _
        · rfl
      _ = (S u v).card * D := by simp [sum_ite_mem]
      _ ≤ k * D := Nat.mul_le_mul_right D (hS u v)
  · simp only [sum_const, card_univ, smul_eq_mul]; apply le_of_eq; ring

lemma end_count_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : V → V → Finset V) (k D : ℕ) (hS : ∀ u v, (S u v).card ≤ k)
    (hD : ∀ w, G.degree w ≤ D) :
    quadCount (fun w u v z => Star G w u v z ∧ z ∈ S u v) ≤
      k * Fintype.card V ^ 2 * D := by
  classical
  have hc (z : V) : (∑ w : V, if G.Adj w z then 1 else 0 : ℕ) = G.degree z := by
    simpa only [G.adj_comm, sum_boole, Nat.cast_id, ← G.neighborFinset_eq_filter] using
      (G.card_neighborFinset_eq_degree z)
  apply (quadCount_mono (Q := fun w u v z => z ∈ S u v ∧ G.Adj w z)
    (fun _ _ _ _ h => ⟨h.2,h.1.2.2⟩)).trans
  unfold quadCount
  rw [sum_comm]
  trans ∑ u : V, ∑ v : V, k * D
  · apply sum_le_sum; intro u _
    rw [sum_comm]
    apply sum_le_sum; intro v _
    rw [sum_comm]
    simp only [and_indicator, sum_ite_irrel, hc, sum_const_zero]
    calc
      _ ≤ ∑ z : V, if z ∈ S u v then D else 0 := by
        apply sum_le_sum; intro z _
        split_ifs
        · exact hD _
        · rfl
      _ = (S u v).card * D := by simp [sum_ite_mem]
      _ ≤ k * D := Nat.mul_le_mul_right D (hS u v)
  · simp only [sum_const, card_univ, smul_eq_mul]; apply le_of_eq; ring

lemma light_count_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h D : ℕ) (hD : ∀ w, G.degree w ≤ D) :
    quadCount (fun w u v z => Star G w u v z ∧ Nat.card (G.commonNeighbors u v) < h) ≤
      h * Fintype.card V ^ 2 * D := by
  classical
  let S : V → V → Finset V := fun u v =>
    if Nat.card (G.commonNeighbors u v) < h then (G.commonNeighbors u v).toFinset else ∅
  have hS (u v : V) : (S u v).card ≤ h := by
    dsimp [S]
    split_ifs with hh
    · simpa only [Set.toFinset_card, Fintype.card_eq_nat_card] using hh.le
    · simp
  apply (quadCount_mono (Q := fun w u v z => Star G w u v z ∧ w ∈ S u v) ?_).trans
    (center_count_le G S h D hS hD)
  intro w u v z hh
  refine ⟨hh.1,?_⟩
  simp only [S, if_pos hh.2, Set.mem_toFinset, mem_commonNeighbors]
  exact ⟨hh.1.1.symm,hh.1.2.1.symm⟩

lemma diagonal_count_le {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀ w, G.degree w ≤ D) :
    quadCount (fun w u v z => Star G w u v z ∧ u = v) ≤ Fintype.card V ^ 2 * D := by
  classical
  rw [diagonal_count]
  calc
    _ ≤ ∑ _ : V, Fintype.card V * D := by
      apply sum_le_sum; intro w _
      rw [pow_two]
      exact Nat.mul_le_mul (G.degree_lt_card_verts w).le (hD w)
    _ = _ := by simp [pow_two, mul_assoc]


lemma star_count_le_of_blockers {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : V → V → Finset V) (k D : ℕ)
    (hD : ∀ w, G.degree w ≤ D) (hsize : ∀ u v, (B u v).card ≤ k)
    (hroots : ∀ u v, u ∉ B u v ∧ v ∉ B u v)
    (hblock : ∀ u v, ∀ e : Base.Copy G, e leftRoot = u → e rightRoot = v →
      ∃ a, (a ≠ leftRoot ∧ a ≠ rightRoot) ∧ e a ∈ B u v) :
    ∑ w, G.degree w ^ 3 ≤ (3 + 3 * (k+7) + 2*k) * Fintype.card V ^ 2 * D := by
  classical
  let P0 : V → V → V → V → Prop := fun w u v z => Star G w u v z ∧ u = v
  let P1 : V → V → V → V → Prop := fun w u v z => Star G w u v z ∧ u = z
  let P2 : V → V → V → V → Prop := fun w u v z => Star G w u v z ∧ v = z
  let P3 : V → V → V → V → Prop := fun w u v z => Star G w u v z ∧ Nat.card (G.commonNeighbors u v) < k+7
  let P4 : V → V → V → V → Prop := fun w u v z => Star G w u v z ∧ Nat.card (G.commonNeighbors u z) < k+7
  let P5 : V → V → V → V → Prop := fun w u v z => Star G w u v z ∧ Nat.card (G.commonNeighbors v z) < k+7
  let P6 : V → V → V → V → Prop := fun w u v z => Star G w u v z ∧ w ∈ B u v
  let P7 : V → V → V → V → Prop := fun w u v z => Star G w u v z ∧ z ∈ B u v
  have h0 : quadCount P0 ≤ Fintype.card V ^ 2 * D := diagonal_count_le G D hD
  have he1 : quadCount P1 = quadCount P0 := by
    simpa only [P0,P1,star_leaf_swap_vz] using quadCount_swap_vz P0
  have he2 : quadCount P2 = quadCount P1 := by
    simpa only [P1,P2,star_leaf_swap_uv] using quadCount_swap_uv P1
  have h1 : quadCount P1 ≤ Fintype.card V ^ 2 * D := he1.trans_le h0
  have h2 : quadCount P2 ≤ Fintype.card V ^ 2 * D := he2.trans_le h1
  have h3 : quadCount P3 ≤ (k+7) * Fintype.card V ^ 2 * D := light_count_le G (k+7) D hD
  have he4 : quadCount P4 = quadCount P3 := by
    simpa only [P3,P4,star_leaf_swap_vz] using quadCount_swap_vz P3
  have he5 : quadCount P5 = quadCount P4 := by
    simpa only [P4,P5,star_leaf_swap_uv] using quadCount_swap_uv P4
  have h4 : quadCount P4 ≤ (k+7) * Fintype.card V ^ 2 * D := he4.trans_le h3
  have h5 : quadCount P5 ≤ (k+7) * Fintype.card V ^ 2 * D := he5.trans_le h4
  have h6 : quadCount P6 ≤ k * Fintype.card V ^ 2 * D := center_count_le G B k D hsize hD
  have h7 : quadCount P7 ≤ k * Fintype.card V ^ 2 * D := end_count_le G B k D hsize hD
  have hc : quadCount (Star G) ≤ quadCount (fun w u v z => P0 w u v z ∨ P1 w u v z ∨ P2 w u v z ∨ P3 w u v z ∨ P4 w u v z ∨ P5 w u v z ∨ P6 w u v z ∨ P7 w u v z) := by
    apply quadCount_mono
    intro w u v z hstar
    have hcover : u = v ∨ u = z ∨ v = z ∨
        Nat.card (G.commonNeighbors u v) < k+7 ∨
        Nat.card (G.commonNeighbors u z) < k+7 ∨
        Nat.card (G.commonNeighbors v z) < k+7 ∨ w ∈ B u v ∨ z ∈ B u v := by
      by_contra hh
      push_neg at hh
      obtain ⟨huv,huz,hvz,hhuv,hhuz,hhvz,hw,hz⟩ := hh
      exact (heavy_star_blocked G B hsize hroots hblock w u v z
        hstar.1 hstar.2.1 hstar.2.2 huv huz hvz hhuv hhuz hhvz).elim hw hz
    dsimp only [P0,P1,P2,P3,P4,P5,P6,P7]
    tauto
  have hs0 := quadCount_or P0 (fun w u v z => P1 w u v z ∨ P2 w u v z ∨ P3 w u v z ∨ P4 w u v z ∨ P5 w u v z ∨ P6 w u v z ∨ P7 w u v z)
  have hs1 := quadCount_or P1 (fun w u v z => P2 w u v z ∨ P3 w u v z ∨ P4 w u v z ∨ P5 w u v z ∨ P6 w u v z ∨ P7 w u v z)
  have hs2 := quadCount_or P2 (fun w u v z => P3 w u v z ∨ P4 w u v z ∨ P5 w u v z ∨ P6 w u v z ∨ P7 w u v z)
  have hs3 := quadCount_or P3 (fun w u v z => P4 w u v z ∨ P5 w u v z ∨ P6 w u v z ∨ P7 w u v z)
  have hs4 := quadCount_or P4 (fun w u v z => P5 w u v z ∨ P6 w u v z ∨ P7 w u v z)
  have hs5 := quadCount_or P5 (fun w u v z => P6 w u v z ∨ P7 w u v z)
  have hs6 := quadCount_or P6 P7
  rw [← star_count]
  calc
    _ ≤ quadCount P0 + quadCount P1 + quadCount P2 + quadCount P3 + quadCount P4 + quadCount P5 + quadCount P6 + quadCount P7 := by omega
    _ ≤ Fintype.card V ^ 2 * D + Fintype.card V ^ 2 * D +
      Fintype.card V ^ 2 * D + (k+7) * Fintype.card V ^ 2 * D + (k+7) * Fintype.card V ^ 2 * D +
      (k+7) * Fintype.card V ^ 2 * D + k * Fintype.card V ^ 2 * D + k * Fintype.card V ^ 2 * D := by omega
    _ = _ := by ring


lemma free_star_count_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {t : ℕ} (ht : 1 ≤ t) (hfree : (Fan t).Free G) :
    ∑ w, G.degree w ^ 3 ≤ (24 + 35*t) * Fintype.card V ^ 2 * G.maxDegree := by
  classical
  choose B hu hv hc hb using Erdos713EdgeFan.blockers_of_free Base G
    (by decide : leftRoot ≠ rightRoot) ht hfree
  have hc' (u v) : (B u v).card ≤ 7*t := by
    simpa [mul_comm] using hc u v
  have hh := star_count_le_of_blockers G B (7*t) G.maxDegree G.degree_le_maxDegree
    hc' (fun u v => ⟨hu u v,hv u v⟩) hb
  convert hh using 1; ring

lemma almost_regular_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    {t : ℕ} (ht : 1 ≤ t) (hfree : (Fan t).Free G) (hn : 0 < Fintype.card V)
    {R d : ℝ} (hd : 0 < d)
    (hdeg : ∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
      (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) :
    d^2 ≤ (24 + 35*(t : ℝ)) * R * Fintype.card V := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp hn
  have hdeg' (v : V) : d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ R*d := by
    simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hdeg v
  have hmax : (G.maxDegree : ℝ) ≤ R*d := by
    obtain ⟨v,hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    exact (hdeg' v).2
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  apply (mul_le_mul_iff_left₀ (mul_pos hnR hd)).mp
  calc
    d^2 * ((Fintype.card V : ℝ) * d) = (Fintype.card V : ℝ) * d^3 := by ring
    _ ≤ ∑ v : V, (G.degree v : ℝ)^3 := by
      simpa only [sum_const, card_univ, nsmul_eq_mul] using
        (sum_le_sum (s := (univ : Finset V)) (fun v _ => pow_le_pow_left₀ hd.le (hdeg' v).1 3))
    _ ≤ (24 + 35*(t : ℝ)) * (Fintype.card V : ℝ)^2 * G.maxDegree := by
      exact_mod_cast free_star_count_le G ht hfree
    _ ≤ (24 + 35*(t : ℝ)) * (Fintype.card V : ℝ)^2 * (R*d) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = ((24 + 35*(t : ℝ)) * R * (Fintype.card V : ℝ)) * ((Fintype.card V : ℝ) * d) := by ring

lemma upper (t : ℕ) (ht : 1 ≤ t) :
    (fun n : ℕ => (extremalNumber n (Fan t) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((3 : ℝ)/2)) := by
  classical
  by_contra hO
  have hLarge : ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      C * (n : ℝ)^((3 : ℝ)/2) < (extremalNumber n (Fan t) : ℝ) := by
    intro C N
    by_contra hh
    push_neg at hh
    apply hO
    apply IsBigO.of_bound C
    refine eventually_atTop.mpr ⟨N,fun n hn => ?_⟩
    change |(extremalNumber n (Fan t) : ℝ)| ≤ C * |(n : ℝ)^((3 : ℝ)/2)|
    rw [abs_of_nonneg (show (0 : ℝ) ≤ extremalNumber n (Fan t) from Nat.cast_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact hh n hn
  obtain ⟨R,hR,hRegular⟩ := Erdos713RateRegularization.exists_almost_regular_below
    (Fan t) (by norm_num : (1 : ℝ) < 3/2) hLarge
  let C : ℝ := (24 + 35*(t : ℝ))*R
  have hC : 0 < C := mul_pos (by positivity) hR
  obtain ⟨V,_,G,d,_,hn,hfree,_,_,hd,hdLower,hdeg⟩ := hRegular (C+1) (by linarith) 1
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hsq : ((Fintype.card V : ℝ)^((3 : ℝ)/2-1))^2 = (Fintype.card V : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    norm_num
  have hLow := pow_le_pow_left₀ (by positivity : 0 ≤ (C+1)*(Fintype.card V : ℝ)^((3 : ℝ)/2-1)) hdLower 2
  rw [mul_pow, hsq] at hLow
  have hHigh := almost_regular_bound G ht hfree hn hd hdeg
  have hh : (C+1)^2 ≤ C := (mul_le_mul_iff_left₀ hnR).mp (by
    nlinarith [hLow.trans hHigh])
  nlinarith

lemma base_contains_C4 : Erdos713C4.K22 ⊑ Base := by
  classical
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨{Sum.inl 0, Sum.inl 1}, {Sum.inr none, Sum.inr (some 2)}, by decide, by decide, ?_⟩
  intro x hx y hy
  simp only [mem_coe, mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [Base, Erdos713C6.bipGraph]

lemma rate (t : ℕ) (ht : 1 ≤ t) : Erdos713Rate.HasRate (Fan t) ((3 : ℝ)/2) := by
  apply Erdos713Rate.rate_of_C4_upper _ (upper t ht)
  exact base_contains_C4.trans ⟨Erdos713EdgeFan.petalCopy Base (by decide)
    (⟨0,by omega⟩ : Fin t)⟩


lemma sandwich_rate {W : Type*} {H : SimpleGraph W} {t : ℕ} (ht : 1 ≤ t)
    (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ Fan t) :
    Erdos713Rate.HasRate H ((3 : ℝ)/2) :=
  Erdos713Rate.rate_of_C4_upper hlo ((Erdos713Rate.extremal_mono_bigO hhi).trans (upper t ht))

lemma rational_of_sandwich {W : Type*} {H : SimpleGraph W} {t : ℕ} (ht : 1 ≤ t)
    (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ Fan t) {α : ℝ}
    (hRate : Erdos713Rate.HasRate H α) : α ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨3/2,?_⟩
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    Erdos713Rate.rate_unique (sandwich_rate ht hlo hhi) hRate

end Erdos713ConeFan
