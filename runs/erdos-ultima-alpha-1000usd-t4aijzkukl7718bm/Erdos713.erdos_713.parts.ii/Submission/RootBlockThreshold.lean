import FormalConjecturesUtil
import Submission.CompactRootedWedgeAudit

/-! Rooted upper bounds and attained superlinear rooted thresholds localize to
actual cyclic blocks of a finite connected graph. No rationality is assumed. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713RootBlocks
open Erdos713Blocks Erdos713Rate Erdos713RootPower Erdos713Gluing
universe u

lemma root_bound_small {W : Type*} [Fintype W] (G : SimpleGraph W)
    (hc : Nat.card W ≤ 2) (x : W) : RootPowerBound G x 1 := by
  classical
  have he : Nonempty (W ↪ (Fin 1 ⊕ Fin 1)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using hc
  obtain ⟨e⟩ := he
  let f : G.Copy (Erdos713KST.Kst 1 1) := ⟨⟨e,by
    intro a b hab
    have hne := e.injective.ne hab.ne
    cases ha : e a with
    | inl v =>
      cases hb : e b with
      | inl w => exact (hne (ha.trans ((congrArg Sum.inl (Subsingleton.elim v w)).trans hb.symm))).elim
      | inr w => simp [Erdos713KST.Kst,completeBipartiteGraph]
    | inr v =>
      cases hb : e b with
      | inl w => simp [Erdos713KST.Kst,completeBipartiteGraph]
      | inr w => exact (hne (ha.trans ((congrArg Sum.inr (Subsingleton.elim v w)).trans hb.symm))).elim⟩,
    e.injective⟩
  simpa using (kst (s := 1) (t := 1) (by decide) (by decide) (f x)).of_copy f x

lemma Lobe.no_isolates {W : Type*} [Fintype W] {G : SimpleGraph W}
    {S : Set W} {x : W} (hL : Lobe G S x) (hG : G.Connected) :
    ∀ v, ∃ w, (G.induce S).Adj v w := by
  classical
  obtain ⟨u,hu,hux⟩ := hL.other
  haveI : Nontrivial S := ⟨⟨⟨u,hu⟩,⟨x,hL.root_mem⟩,
    fun he => hux (congrArg Subtype.val he)⟩⟩
  intro v
  exact ((G.induce S).degree_pos_iff_exists_adj v).mp
    ((hL.connected hG).preconnected.degree_pos_of_nontrivial v)

/-- No data is needed for bridge edges or isolated singleton blocks. -/
def BlockUpper {W : Type u} (G : SimpleGraph W) (r : ℝ) : Prop :=
  ∀ S : Set W, IsBlock G S → 3 ≤ Nat.card S → ∀ x, RootPowerBound (G.induce S) x r

lemma BlockUpper.lobe {W : Type u} [Fintype W] {G : SimpleGraph W} {r : ℝ}
    (h : BlockUpper G r) {T : Set W} {x : W} (hL : Lobe G T x) : BlockUpper (G.induce T) r := by
  intro U hU hc y
  let e := induceImageIso G T U
  have hc' : 3 ≤ Nat.card ↥(Subtype.val '' U) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hc
  exact (h _ (hU.lift_lobe hL (by omega)) hc' (e y)).of_copy e.toCopy y

/-- The rooted upper bound of a finite connected graph is determined by its
actual cyclic blocks. This direction assembles bounds at one fixed exponent. -/
lemma root_bound_of_blocks {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {r : ℝ} (hr : 1 ≤ r) (h : BlockUpper G r) :
    ∀ x, RootPowerBound G x r := by
  classical
  suffices hh : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] (G : SimpleGraph W),
      Fintype.card W = n → G.Connected → BlockUpper G r → ∀ x, RootPowerBound G x r from
    hh _ W G rfl hG h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ G hc hG h z
    by_cases hsmall : Nat.card W ≤ 2
    · exact (root_bound_small G hsmall z).mono hr
    haveI : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp
      (by simpa only [Fintype.card_eq_nat_card] using (show 1 < Nat.card W by omega))
    obtain ⟨x⟩ := hG.nonempty
    obtain ⟨y,hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (hG.preconnected.degree_pos_of_nontrivial x)
    obtain ⟨S,x,hL,hNC⟩ := exists_minimal_lobe (G := G)
      ⟨Set.univ,x,Set.mem_univ x,⟨y,Set.mem_univ y,hxy.ne.symm⟩,by simp⟩
    have hSC := hL.connected hG
    have hSRoot : ∀ w, RootPowerBound (G.induce S) w r := by
      by_cases hSCard : 3 ≤ Nat.card S
      · exact h S (hL.isBlock hSC hNC) hSCard
      · intro w
        exact (root_bound_small (G.induce S) (by omega) w).mono hr
    by_cases hS : S = Set.univ
    · subst S
      exact (hSRoot ((induceUnivIso G).symm z)).of_copy (induceUnivIso G).symm.toCopy z
    let T : Set W := insert x Sᶜ
    have hT := hL.complement hS
    have hTsmall : Fintype.card T < n := by
      obtain ⟨v,hv,hvx⟩ := hL.other
      have hn : v ∉ T := by
        simpa only [T,Set.mem_insert_iff,Set.mem_compl_iff,not_or,not_not] using ⟨hvx,hv⟩
      exact (Fintype.card_subtype_lt (x := v) hn).trans_eq hc
    have hTConn := hT.connected hG
    have hTRoot := ih _ hTsmall T (G.induce T) rfl hTConn (h.lobe hT)
    have hRoot := (hSRoot ⟨x,hL.root_mem⟩).wedge (hTRoot ⟨x,hT.root_mem⟩) hr (Lobe.no_isolates hL hG)
    let e := lobeWedgeIso hL
    have hWConn := wedge_connected hSC hTConn ⟨x,hL.root_mem⟩ ⟨x,hT.root_mem⟩
    exact (hRoot.of_reachable (hWConn _ (e.symm z))).of_copy e.symm.toCopy z

lemma blockUpper_of_root_bound {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {r : ℝ} {x : W} (h : RootPowerBound G x r) : BlockUpper G r := by
  intro S hS hc y
  exact (h.of_reachable (hG x y.val)).of_copy (Copy.induce G S) y

lemma root_bound_iff_blocks {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {r : ℝ} (hr : 1 ≤ r) (x : W) :
    RootPowerBound G x r ↔ BlockUpper G r :=
  ⟨blockUpper_of_root_bound G hG,fun h => root_bound_of_blocks G hG hr h x⟩

/-- Any attained superlinear rooted threshold is attained by an actual cyclic
block. This transfers the threshold, not an exact asymptotic. -/
lemma exists_block_root_rate {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) {x : W} {r : ℝ} (hr : 1 < r) (hR : HasRootRate G x r) :
    ∃ S : Set W, IsBlock G S ∧ 3 ≤ Nat.card S ∧ ∀ y, HasRootRate (G.induce S) y r := by
  classical
  by_contra hn
  push_neg at hn
  have hu := blockUpper_of_root_bound G hG hR.upper
  have hEach (S : Set W) : ∃ a : ℝ, 1 ≤ a ∧ a < r ∧
      (IsBlock G S → 3 ≤ Nat.card S → ∀ y, RootPowerBound (G.induce S) y a) := by
    by_cases hS : IsBlock G S ∧ 3 ≤ Nat.card S
    · obtain ⟨y,hy⟩ := hn S hS.1 hS.2
      have hl : ¬ ∀ a : ℝ, 1 ≤ a → RootPowerBound (G.induce S) y a → r ≤ a :=
        fun hl => hy ⟨hr.le,hu S hS.1 hS.2 y,hl⟩
      push_neg at hl
      obtain ⟨a,ha,hroot,har⟩ := hl
      exact ⟨a,ha,har,fun _ _ z => hroot.of_reachable (hS.1.connected y z)⟩
    · exact ⟨1,le_rfl,hr,fun hBlock hc => (hS ⟨hBlock,hc⟩).elim⟩
  choose a ha har hEach using hEach
  obtain ⟨S₀,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Set W)) a
    ⟨∅,Finset.mem_univ _⟩
  have hBound : BlockUpper G (a S₀) := by
    intro S hS hc y
    exact (hEach S hS hc y).mono (hmax S (Finset.mem_univ _))
  exact (not_lt_of_ge (hR.lower (a S₀) (ha S₀)
    (root_bound_of_blocks G hG (ha S₀) hBound x))) (har S₀)

lemma hasRootRate_of_matched {W : Type*} {G : SimpleGraph W} {x : W} {r : ℝ}
    (hR : HasRate G r) (hRoot : RootPowerBound G x r) : HasRootRate G x r :=
  ⟨hR.one_le,hRoot,fun a ha hu => hR.lower a ha hu.upper⟩

/-- Either some actual cyclic block attains the original exponent as a rooted
threshold, or every opposite-root double of the connected graph fails the
original power upper bound. No exponent of a double is asserted. -/
lemma root_block_or_double_gap {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) (hNoIso : ∀ v, ∃ w, G.Adj v w) {r : ℝ}
    (hr : 1 < r) (hR : HasRate G r) :
    (∃ S : Set W, IsBlock G S ∧ 3 ≤ Nat.card S ∧ ∀ y, HasRootRate (G.induce S) y r) ∨
    (∀ x y, G.Adj x y →
      ¬ (fun n : ℕ => (extremalNumber n (wedge G x G y) : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ)^r)) := by
  classical
  obtain ⟨x⟩ := hG.nonempty
  by_cases hx : RootPowerBound G x r
  · exact Or.inl (exists_block_root_rate G hG hr (hasRootRate_of_matched hR hx))
  · refine Or.inr (fun y z hyz hu => hx ?_)
    exact ((opposite_wedge_upper_iff G hNoIso hyz hr.le).mp hu).of_reachable (hG y x)

/-- The block supplied at an irrational rooted threshold lies outside every
completed small-shore/C10 case. It carries no ordinary asymptotic claim. -/
lemma exists_remaining_root_block {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) (hB : G.IsBipartite) {x : W} {r : ℝ}
    (hr : 1 < r) (hR : HasRootRate G x r) (hIrr : r ∉ Set.range ((↑) : ℚ → ℝ)) :
    ∃ S : Set W, IsBlock G S ∧ (G.induce S).IsBipartite ∧ 8 ≤ Nat.card S ∧
      (∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v)) ∧
      (∀ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ → 4 ≤ Nat.card A) ∧
      ¬ G.induce S ⊑ Erdos713C10.C10 ∧
      (∀ y, HasRootRate (G.induce S) y r) ∧ ¬ Erdos713ActualBlocks.RootedRate (G.induce S) := by
  classical
  obtain ⟨S,hS,hc,hRate⟩ := exists_block_root_rate G hG hr hR
  haveI : Nonempty S := hS.connected.nonempty
  have hd := hS.noCut.min_degree hS.connected (by
    simpa only [Fintype.card_eq_nat_card] using hc)
  have hNoRoot : ¬ Erdos713ActualBlocks.RootedRate (G.induce S) := by
    rintro ⟨q,hq,hRoot⟩
    let y : S := Classical.arbitrary S
    exact hIrr ⟨q,(hasRootRate_of_matched hq (hRoot y)).unique (hRate y)⟩
  have hPiece : ¬ Erdos713CycleAssembly.Piece (G.induce S) :=
    fun hp => hNoRoot (hp.rooted_rate hd)
  have hSmall : ¬ ∃ A : Set S, (G.induce S).IsBipartiteWith A Aᶜ ∧ Nat.card A ≤ 3 :=
    fun hh => hPiece (Or.inl hh)
  push_neg at hSmall
  have hSB : (G.induce S).IsBipartite := Colorable.of_hom (Copy.induce G S).toHom hB
  have hc' : 8 ≤ Nat.card S := by
    by_contra hc'
    obtain ⟨A,hA,hcard⟩ := Erdos713ThreeSide.small_bipartition_of_card_le_seven (G.induce S) hSB
      (by simpa only [Fintype.card_eq_nat_card] using (show Nat.card S ≤ 7 by omega))
    exact (not_lt_of_ge hcard) (hSmall A hA)
  exact ⟨S,hS,hSB,hc',hd,fun A hA => hSmall A hA,
    fun hh => hPiece (Or.inr hh),hRate,hNoRoot⟩

/-- Rational attained rooted thresholds of the actual cyclic blocks combine
to a rational attained rooted threshold. The ordinary rates of the blocks do
not appear in this hypothesis. -/
lemma rational_root_rate_of_blocks {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected)
    (hBlocks : ∀ S : Set W, IsBlock G S → 3 ≤ Nat.card S →
      ∃ q : ℚ, ∀ y, HasRootRate (G.induce S) y (q : ℝ)) :
    ∃ q : ℚ, ∀ x, HasRootRate G x (q : ℝ) := by
  classical
  have hEach (S : Set W) : ∃ q : ℚ, 1 ≤ (q : ℝ) ∧
      ((IsBlock G S ∧ 3 ≤ Nat.card S) → ∀ y, HasRootRate (G.induce S) y (q : ℝ)) ∧
      (¬ (IsBlock G S ∧ 3 ≤ Nat.card S) → q = 1) := by
    by_cases hS : IsBlock G S ∧ 3 ≤ Nat.card S
    · obtain ⟨q,hq⟩ := hBlocks S hS.1 hS.2
      obtain ⟨y⟩ := hS.1.connected.nonempty
      exact ⟨q,(hq y).one_le,fun _ => hq,fun hn => (hn hS).elim⟩
    · exact ⟨1,by norm_num,fun hh => (hS hh).elim,fun _ => rfl⟩
  choose q hOne hRates hDefault using hEach
  obtain ⟨S₀,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Set W)) q
    ⟨∅,Finset.mem_univ _⟩
  have hBound : BlockUpper G (q S₀ : ℝ) := by
    intro S hS hc y
    exact (hRates S ⟨hS,hc⟩ y).upper.mono (by exact_mod_cast hmax S (Finset.mem_univ _))
  refine ⟨q S₀,fun x => ⟨hOne S₀,root_bound_of_blocks G hG (hOne S₀) hBound x,?_⟩⟩
  intro a ha hu
  by_cases hS : IsBlock G S₀ ∧ 3 ≤ Nat.card S₀
  · obtain ⟨y⟩ := hS.1.connected.nonempty
    exact (hRates S₀ hS y).lower a ha (blockUpper_of_root_bound G hG hu S₀ hS.1 hS.2 y)
  · simpa only [hDefault S₀ hS,Rat.cast_one] using ha

lemma opposite_double_rate_of_blocks {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hG : G.Connected) (hNoIso : ∀ v, ∃ w, G.Adj v w)
    (hBlocks : ∀ S : Set W, IsBlock G S → 3 ≤ Nat.card S →
      ∃ q : ℚ, ∀ y, HasRootRate (G.induce S) y (q : ℝ))
    {x y : W} (hxy : G.Adj x y) : ∃ q : ℚ, HasRate (wedge G x G y) (q : ℝ) := by
  obtain ⟨q,hq⟩ := rational_root_rate_of_blocks G hG hBlocks
  exact ⟨q,(opposite_wedge_rate_iff G hNoIso hxy).mpr (hq x)⟩

lemma tree_root_bound {W : Type u} [Fintype W] (G : SimpleGraph W)
    (hTree : G.IsTree) (x : W) : RootPowerBound G x 1 := by
  classical
  apply root_bound_of_blocks G hTree.isConnected le_rfl
  intro S hS hc y
  haveI : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa only [Fintype.card_eq_nat_card] using (show 1 < Nat.card S by omega))
  have ht : (G.induce S).IsTree := ⟨hS.connected,hTree.IsAcyclic.induce S⟩
  obtain ⟨v,hv⟩ := ht.exists_vert_degree_one_of_nontrivial
  have hd := hS.noCut.min_degree hS.connected
    (by simpa only [Fintype.card_eq_nat_card] using hc) v
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,hv] at hd
  omega

#print axioms root_bound_small
#print axioms root_bound_of_blocks
#print axioms root_bound_iff_blocks
#print axioms exists_block_root_rate
#print axioms root_block_or_double_gap
#print axioms exists_remaining_root_block
#print axioms rational_root_rate_of_blocks
#print axioms opposite_double_rate_of_blocks
#print axioms tree_root_bound
end Erdos713RootBlocks
