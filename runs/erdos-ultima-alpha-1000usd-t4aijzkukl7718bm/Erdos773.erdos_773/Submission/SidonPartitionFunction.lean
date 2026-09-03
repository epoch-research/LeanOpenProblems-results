import FormalConjecturesUtil

/-! A finite weighted branching bound for graph independent sets. This is
an auxiliary counting tool, not a theorem about the square-Sidon maximum. -/
namespace Erdos773.SidonPartitionFunction
open Finset
set_option maxHeartbeats 2000000
noncomputable section
variable {α : Type*} [DecidableEq α]

def Independent (G : α → α → Prop) (I : Finset α) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬G u v

def indSets (G : α → α → Prop) (W : Finset α) : Finset (Finset α) := by
  classical
  exact W.powerset.filter (Independent G)

def Z (G : α → α → Prop) (W : Finset α) (z : ℝ) : ℝ :=
  ∑ I ∈ indSets G W, z^I.card

def neighbors (G : α → α → Prop) (W : Finset α) (v : α) : Finset α := by
  classical
  exact W.filter (G v)

def rest (G : α → α → Prop) (W : Finset α) (v : α) : Finset α :=
  W\insert v (neighbors G W v)

omit [DecidableEq α] in
lemma mem_indSets {G : α → α → Prop} {W I : Finset α} :
    I ∈ indSets G W ↔ I ⊆ W ∧ Independent G I := by
  classical
  simp only [indSets,mem_filter,mem_powerset]

omit [DecidableEq α] in
lemma independent_mono {G : α → α → Prop} {I J : Finset α} (hI : Independent G I) (hJI : J ⊆ I) :
    Independent G J := fun u hu v hv => hI u (hJI hu) v (hJI hv)

lemma rest_subset_erase (G : α → α → Prop) (W : Finset α) (v : α) : rest G W v ⊆ W.erase v := by
  intro x hx
  obtain ⟨hx,hn⟩ := mem_sdiff.mp hx
  refine mem_erase.mpr ⟨?_,hx⟩
  intro he
  subst x
  exact hn (mem_insert_self v _)

lemma rest_card {G : α → α → Prop} (hirr : ∀ v, ¬G v v) {W : Finset α} {v : α} (hv : v ∈ W) :
    (rest G W v).card+(neighbors G W v).card+1=W.card := by
  classical
  have hn : v ∉ neighbors G W v := by simp [neighbors,hirr v]
  have hs : insert v (neighbors G W v) ⊆ W := insert_subset hv (filter_subset _ _)
  have hh := card_sdiff_add_card_eq_card hs
  rw [card_insert_of_notMem hn] at hh
  exact (by simpa only [rest,Nat.add_assoc] using hh)

lemma independent_insert {G : α → α → Prop} (hsymm : ∀ u v, G u v → G v u) (hirr : ∀ v, ¬G v v)
    {W I : Finset α} {v : α} (hI : I ∈ indSets G (rest G W v)) : Independent G (insert v I) := by
  classical
  obtain ⟨hIW,hind⟩ := mem_indSets.mp hI
  have hvI : ∀ x ∈ I, ¬G v x := by
    intro x hx hh
    have hn := (mem_sdiff.mp (hIW hx)).2
    exact hn (mem_insert_of_mem (mem_filter.mpr ⟨(mem_sdiff.mp (hIW hx)).1,hh⟩))
  intro a ha b hb
  rcases mem_insert.mp ha with rfl | haI
  · rcases mem_insert.mp hb with rfl | hbI
    · exact hirr _
    · exact hvI _ hbI
  · rcases mem_insert.mp hb with rfl | hbI
    · exact fun hh => hvI _ haI (hsymm _ _ hh)
    · exact hind a haI b hbI

lemma indSets_branch {G : α → α → Prop} (hsymm : ∀ u v, G u v → G v u) (hirr : ∀ v, ¬G v v)
    {W : Finset α} {v : α} (hv : v ∈ W) :
    indSets G W = indSets G (W.erase v) ∪ (indSets G (rest G W v)).image (insert v) := by
  classical
  ext I
  constructor
  · intro hI
    obtain ⟨hIW,hind⟩ := mem_indSets.mp hI
    by_cases hvi : v ∈ I
    · apply mem_union_right
      refine mem_image.mpr ⟨I.erase v,mem_indSets.mpr ⟨?_,independent_mono hind (erase_subset _ _)⟩,
        insert_erase hvi⟩
      intro x hx
      obtain ⟨hxv,hx⟩ := mem_erase.mp hx
      apply mem_sdiff.mpr
      refine ⟨hIW hx,?_⟩
      intro hn
      rcases mem_insert.mp hn with hn | hn
      · exact hxv hn
      · exact hind v hvi x hx (mem_filter.mp hn).2
    · apply mem_union_left
      exact mem_indSets.mpr ⟨fun x hx => mem_erase.mpr ⟨fun h => hvi (h ▸ hx),hIW hx⟩,hind⟩
  · intro hI
    rcases mem_union.mp hI with hI | hI
    · obtain ⟨hsub,hind⟩ := mem_indSets.mp hI
      exact mem_indSets.mpr ⟨hsub.trans (erase_subset _ _),hind⟩
    · obtain ⟨J,hJ,rfl⟩ := mem_image.mp hI
      exact mem_indSets.mpr ⟨insert_subset hv ((mem_indSets.mp hJ).1.trans sdiff_subset),
        independent_insert hsymm hirr hJ⟩

lemma Z_branch {G : α → α → Prop} (hsymm : ∀ u v, G u v → G v u) (hirr : ∀ v, ¬G v v)
    {W : Finset α} {v : α} (hv : v ∈ W) (z : ℝ) :
    Z G W z = Z G (W.erase v) z+z*Z G (rest G W v) z := by
  classical
  have hn {I : Finset α} (hI : I ∈ indSets G (rest G W v)) : v ∉ I := by
    intro h
    exact notMem_erase v W (rest_subset_erase G W v ((mem_indSets.mp hI).1 h))
  have hd : Disjoint (indSets G (W.erase v)) ((indSets G (rest G W v)).image (insert v)) := by
    apply disjoint_left.mpr
    intro I hI hJ
    obtain ⟨J,hJ,rfl⟩ := mem_image.mp hJ
    exact notMem_erase v W ((mem_indSets.mp hI).1 (mem_insert_self v J))
  unfold Z
  rw [indSets_branch hsymm hirr hv,sum_union hd,sum_image]
  · rw [mul_sum]
    congr 1
    apply sum_congr rfl
    intro I hI
    rw [card_insert_of_notMem (hn hI),pow_succ,mul_comm]
  · intro I hI J hJ he
    have hh := congrArg (fun S : Finset α => S.erase v) he
    simpa [hn hI,hn hJ] using hh

omit [DecidableEq α] in
lemma powerset_weight (W : Finset α) (z : ℝ) :
    (∑ I ∈ W.powerset, z^I.card)=(1+z)^W.card := by
  rw [sum_powerset_apply_card]
  rw [show (1+z)^W.card=(z+1)^W.card by rw [add_comm],add_pow]
  apply sum_congr rfl
  intro i hi
  simp only [one_pow,mul_one,nsmul_eq_mul]
  ring

omit [DecidableEq α] in
lemma Z_trivial (G : α → α → Prop) (W : Finset α) {z : ℝ} (hz : 0 ≤ z) :
    Z G W z ≤ (1+z)^W.card := by
  classical
  rw [← powerset_weight]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun I hI _ => pow_nonneg hz _)

/-- A weighted version of the graph-container branching estimate. Every
    large induced carrier only needs to have ONE vertex of degree at least D. -/
theorem partition_bound (G : α → α → Prop) (hsymm : ∀ u v, G u v → G v u) (hirr : ∀ v, ¬G v v)
    (A : Finset α) (w D : ℕ) (z c : ℝ) (hz : 0 ≤ z) (hc : 1 ≤ c)
    (hbranch : z ≤ (c-1)*c^D)
    (hdense : ∀ W ⊆ A, w<W.card → ∃ v ∈ W, D ≤ (neighbors G W v).card) :
    Z G A z ≤ c^A.card*(1+z)^w := by
  have hc0 : 0 ≤ c := by linarith only [hc]
  have hc1 : 0 ≤ c-1 := by linarith only [hc]
  have hw : 0 ≤ (1+z)^w := by positivity
  suffices ∀ W ⊆ A, Z G W z ≤ c^W.card*(1+z)^w from this A (Subset.refl A)
  intro W
  induction W using Finset.strongInductionOn
  rename_i W ih
  intro hWA
  by_cases hW : W.card ≤ w
  · have hb := (Z_trivial G W hz).trans (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1+z) hW)
    have hm := mul_le_mul_of_nonneg_right (one_le_pow₀ hc (n := W.card)) hw
    simp only [one_mul] at hm
    exact hb.trans hm
  · obtain ⟨v,hv,hD⟩ := hdense W hWA (by omega)
    have hrest : rest G W v ⊂ W := (rest_subset_erase G W v).trans_ssubset (erase_ssubset hv)
    have he := ih (W.erase v) (erase_ssubset hv) ((erase_subset _ _).trans hWA)
    have hr := ih (rest G W v) hrest (hrest.subset.trans hWA)
    have hb := hbranch.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc hD) hc1)
    have hcard := rest_card hirr hv
    have herase : (W.erase v).card=(rest G W v).card+(neighbors G W v).card := by
      rw [card_erase_of_mem hv]
      omega
    have hWcard : W.card=(W.erase v).card+1 := by rw [card_erase_of_mem hv]; have := card_pos.mpr ⟨v,hv⟩; omega
    rw [Z_branch hsymm hirr hv]
    calc
      _ ≤ c^(W.erase v).card*(1+z)^w+z*(c^(rest G W v).card*(1+z)^w) :=
        add_le_add he (mul_le_mul_of_nonneg_left hr hz)
      _ ≤ c^(W.erase v).card*(1+z)^w+((c-1)*c^(neighbors G W v).card)*(c^(rest G W v).card*(1+z)^w) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hb (by positivity))
      _ = _ := by rw [hWcard,pow_succ,herase,pow_add]; ring

#print axioms Z_branch
#print axioms powerset_weight
#print axioms partition_bound
end
end Erdos773.SidonPartitionFunction
