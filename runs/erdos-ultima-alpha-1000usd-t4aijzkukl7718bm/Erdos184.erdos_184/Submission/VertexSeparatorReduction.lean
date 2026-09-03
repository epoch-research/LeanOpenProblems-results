import Submission.MinimalBridgeRestoration

/-! Reduction to any fixed vertex-separator threshold. This is a conditional
reduction, not a linear bound for the terminal high-connectivity class. -/

open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.VertexSeparators
open Critical SparseCuts
universe u
set_option maxHeartbeats 600000

/-- Every separation with both sides proper and overlap at most `k` has an
edge between its two exclusive sides. Small complete graphs satisfy this
predicate too; no lower bound on the order is imposed. -/
def NoSmallSeparator {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ A B : Set V, A ∪ B = Set.univ → A ≠ Set.univ → B ≠ Set.univ →
    Nat.card (A ∩ B : Set V) ≤ k →
    ∃ x ∈ A \ B, ∃ y ∈ B \ A, G.Adj x y

variable {V : Type*} [Fintype V]

lemma number_spanning_le {S : Set V} (H : SimpleGraph S) :
    number H.spanningCoe ≤ number H := by
  obtain ⟨D,hD,hd,hc⟩ := exists_minimum H
  obtain ⟨E,hE,he,hce⟩ := lift_decomposition_spanningCoe H D hD hd
  exact (number_le E hE he).trans (hce.trans_eq hc)

lemma number_induce_support (G : SimpleGraph V) (S : Set V)
    (hs : G.support ⊆ S) : number G ≤ number (G.induce S) := by
  have he : (G.induce S).spanningCoe = G := by
    apply le_antisymm (G.spanningCoe_induce_le S)
    intro x y hxy
    exact (spanningCoe_induce_adj G S x y).mpr
      ⟨hxy, hs ⟨y,hxy⟩, hs ⟨x,hxy.symm⟩⟩
  simpa only [he] using number_spanning_le (G.induce S)

/-- Assign the overlap's edges to the first side. The second side may cease
to be induced, which is harmless because the recursive bound is for all graphs. -/
lemma split_number (G : SimpleGraph V) (A B : Set V)
    (hcover : A ∪ B = Set.univ)
    (hcross : ∀ x ∈ A \ B, ∀ y ∈ B \ A, ¬ G.Adj x y) :
    ∃ H : SimpleGraph B,
      number G ≤ number (G.induce A) + number H := by
  let K := (G.induce A).spanningCoe
  let R := G \ K
  have hsupport : R.support ⊆ B := by
    rintro x ⟨y,hxy⟩
    have hxAorB : x ∈ A ∨ x ∈ B := by
      have hx : x ∈ A ∪ B := hcover.symm ▸ Set.mem_univ x
      exact hx
    by_contra hxB
    have hxA : x ∈ A := hxAorB.resolve_right hxB
    have hyAorB : y ∈ A ∨ y ∈ B := by
      have hy : y ∈ A ∪ B := hcover.symm ▸ Set.mem_univ y
      exact hy
    have hyA : y ∉ A := by
      intro hy
      exact hxy.2 ((spanningCoe_induce_adj G A x y).mpr ⟨hxy.1,hxA,hy⟩)
    exact hcross x ⟨hxA,hxB⟩ y ⟨hyAorB.resolve_left hyA,hyA⟩ hxy.1
  refine ⟨R.induce B,?_⟩
  have h := number_sdiff_add_le G K (G.spanningCoe_induce_le A)
  have hr := number_induce_support R B hsupport
  have hk := number_spanning_le (G.induce A)
  change number G ≤ number R + number K at h
  change number K ≤ number (G.induce A) at hk
  omega

lemma number_le_square (G : SimpleGraph V) :
    number G ≤ (Fintype.card V)^2 :=
  (number_le_edges G).trans (G.card_edgeFinset_le_card_choose_two.trans
    (Nat.choose_le_pow _ _))

/-- Numerical induction budget for a genuine separation. The square bound
handles a child whose order is at most the separator threshold. -/
lemma split_budget (k C n a b q r : ℕ)
    (hC : (2*k+1)^2 ≤ C) (hn : 2*k+1 < n)
    (ha : a < n) (hb : b < n) (hs : a+b ≤ n+k)
    (hqa : q ≤ a^2) (hrb : r ≤ b^2)
    (hq : k < a → q ≤ C*(a-k)) (hr : k < b → r ≤ C*(b-k)) :
    q+r ≤ C*(n-k) := by
  by_cases hka : k < a
  · by_cases hkb : k < b
    · have hh := Nat.add_le_add (hq hka) (hr hkb)
      have hsum : (a-k)+(b-k) ≤ n-k := by omega
      exact hh.trans (by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left C hsum)
    · have hb' : b ≤ k := by omega
      have hrC : r ≤ C := by nlinarith
      have has : a-k+1 ≤ n-k := by omega
      calc
        q+r ≤ C*(a-k)+C := Nat.add_le_add (hq hka) hrC
        _ = C*(a-k+1) := by ring
        _ ≤ C*(n-k) := Nat.mul_le_mul_left C has
  · have ha' : a ≤ k := by omega
    have hqC : q ≤ C := by nlinarith
    by_cases hkb : k < b
    · have hbs : b-k+1 ≤ n-k := by omega
      calc
        q+r ≤ C+C*(b-k) := Nat.add_le_add hqC (hr hkb)
        _ = C*(b-k+1) := by ring
        _ ≤ C*(n-k) := Nat.mul_le_mul_left C hbs
    · have hb' : b ≤ k := by omega
      have hqr : q+r ≤ C := by nlinarith
      exact hqr.trans (Nat.le_mul_of_pos_right C (by omega))

/-- A uniform bound on graphs without separators of order at most `k` gives
an explicit uniform bound on every finite graph. The hypothesis is not proved. -/
lemma number_bound_of_minimal_no_small_separator (k B : ℕ)
    (hhigh : ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      EdgeHull.Minimal G → NoSmallSeparator G k → number G ≤ B * Fintype.card W) :
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      number G ≤ ((2*k+1)^2 + (k+1)*B) * Fintype.card W := by
  let C := (2*k+1)^2 + (k+1)*B
  have hCsq : (2*k+1)^2 ≤ C := Nat.le_add_right _ _
  have main : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W), Fintype.card W = n → k < n →
      number G ≤ C*(n-k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ G hW hkn
      by_cases hsmall : n ≤ 2*k+1
      · have hn := number_le_square G
        rw [hW] at hn
        have hle : number G ≤ C := by nlinarith
        exact hle.trans (Nat.le_mul_of_pos_right C (by omega))
      by_cases hz : EdgeHull.value G = 0
      · have hh := EdgeHull.number_le_value G
        rw [hz] at hh
        exact hh.trans (Nat.zero_le _)
      obtain ⟨R,hRG,hm,hr⟩ := EdgeHull.exists_minimal_maximizer G (Nat.pos_of_ne_zero hz)
      have hGR : number G ≤ number R := (EdgeHull.number_le_value G).trans_eq hr.symm
      apply hGR.trans
      by_cases hG : NoSmallSeparator R k
      · have hn := hhigh R hm hG
        rw [hW] at hn
        have hn' : n ≤ (k+1)*(n-k) := by
          have ht : 1 ≤ n-k := by omega
          have hm := Nat.mul_le_mul_left k ht
          have he := Nat.sub_add_cancel (Nat.le_of_lt hkn)
          nlinarith
        have hc : (k+1)*B ≤ C := Nat.le_add_left _ _
        calc
          number R ≤ B*n := hn
          _ ≤ B*((k+1)*(n-k)) := Nat.mul_le_mul_left B hn'
          _ = ((k+1)*B)*(n-k) := by ring
          _ ≤ C*(n-k) := Nat.mul_le_mul_right (n-k) hc
      have hsep : ∃ A B' : Set W, A ∪ B' = Set.univ ∧ A ≠ Set.univ ∧
          B' ≠ Set.univ ∧ Nat.card (A ∩ B' : Set W) ≤ k ∧
          ∀ x ∈ A \ B', ∀ y ∈ B' \ A, ¬ R.Adj x y := by
        unfold NoSmallSeparator at hG
        push_neg at hG
        exact hG
      obtain ⟨A,T,hcover,hA,hT,hint,hcross⟩ := hsep
      have ha : Fintype.card A < n := by
        obtain ⟨x,hx⟩ := Set.nonempty_compl.mpr hA
        exact (Fintype.card_subtype_lt hx).trans_eq hW
      have ht : Fintype.card T < n := by
        obtain ⟨x,hx⟩ := Set.nonempty_compl.mpr hT
        exact (Fintype.card_subtype_lt hx).trans_eq hW
      have hsum : Fintype.card A + Fintype.card T ≤ n+k := by
        have hc := Set.ncard_union_add_ncard_inter A T
        rw [hcover, Set.ncard_univ] at hc
        change Nat.card W + Nat.card (A ∩ T : Set W) = Nat.card A + Nat.card T at hc
        simp only [Nat.card_eq_fintype_card] at hc hint
        rw [hW] at hc
        omega
      obtain ⟨H,hnum⟩ := split_number R A T hcover hcross
      apply hnum.trans
      apply split_budget k C n (Fintype.card A) (Fintype.card T) _ _ hCsq
        (by omega) ha ht hsum (number_le_square _) (number_le_square _)
      · exact fun hka => ih _ ha (R.induce A) rfl hka
      · exact fun hkt => ih _ ht H rfl hkt
  intro W _ _ G
  change number G ≤ C * Fintype.card W
  by_cases hk : k < Fintype.card W
  · exact (main _ G rfl hk).trans (Nat.mul_le_mul_left C (Nat.sub_le _ _))
  · have hsq := number_le_square G
    have hWC : Fintype.card W ≤ C := by dsimp [C]; nlinarith
    exact hsq.trans (by simpa only [pow_two] using
      Nat.mul_le_mul_right (Fintype.card W) hWC)


/-- The same reduction without imposing edge-minimality on the high-connectivity
hypothesis. -/
lemma number_bound_of_no_small_separator (k B : ℕ)
    (hhigh : ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      NoSmallSeparator G k → number G ≤ B * Fintype.card W) :
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      number G ≤ ((2*k+1)^2 + (k+1)*B) * Fintype.card W :=
  number_bound_of_minimal_no_small_separator k B (fun G _ hG => hhigh G hG)

/-- Deleting at most `k` vertices leaves a preconnected graph. Preconnectedness
avoids conventions about graphs with zero remaining vertices. -/
def DeletionConnected {W : Type*} (G : SimpleGraph W) (k : ℕ) : Prop :=
  ∀ S : Set W, Nat.card S ≤ k → (G.induce Sᶜ).Preconnected

lemma NoSmallSeparator.deletionConnected {G : SimpleGraph V} {k : ℕ}
    (hG : NoSmallSeparator G k) : DeletionConnected G k := by
  intro S hS
  by_contra hn
  obtain ⟨a,b,hab⟩ := by
    simpa only [SimpleGraph.Preconnected,not_forall] using hn
  let R : Set V := {x | ∃ hx : x ∉ S, (G.induce Sᶜ).Reachable a ⟨x,hx⟩}
  have ha : a.val ∈ R := ⟨a.property, .rfl⟩
  have hb : b.val ∉ R := by
    rintro ⟨hb,hr⟩
    exact hab hr
  have hc : (S ∪ R) ∪ Rᶜ = Set.univ := by
    ext x
    simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_univ,iff_true]
    tauto
  have hA : S ∪ R ≠ Set.univ := by
    intro he
    have hm : b.val ∈ S ∪ R := he.symm ▸ Set.mem_univ _
    exact hm.elim b.property hb
  have hB : Rᶜ ≠ Set.univ := by
    intro he
    have hm : a.val ∈ Rᶜ := he.symm ▸ Set.mem_univ _
    exact hm ha
  have hi : Nat.card ((S ∪ R) ∩ Rᶜ : Set V) ≤ k := by
    have hs : (S ∪ R) ∩ Rᶜ ⊆ S := by
      intro x hx
      exact hx.1.resolve_right hx.2
    exact (Set.ncard_le_ncard hs).trans hS
  obtain ⟨x,hx,y,hy,hxy⟩ := hG (S ∪ R) Rᶜ hc hA hB hi
  have hxR : x ∈ R := by simpa only [Set.mem_compl_iff,not_not] using hx.2
  obtain ⟨hxs,hax⟩ := hxR
  have hys : y ∉ S := fun h => hy.2 (Or.inl h)
  have hyr : y ∈ R := ⟨hys,hax.trans (show (G.induce Sᶜ).Adj ⟨x,hxs⟩ ⟨y,hys⟩ from hxy).reachable⟩
  exact hy.1 hyr

lemma DeletionConnected.noSmallSeparator {G : SimpleGraph V} {k : ℕ}
    (hG : DeletionConnected G k) : NoSmallSeparator G k := by
  intro A B hcover hA hB hk
  by_contra hnone
  push_neg at hnone
  obtain ⟨x,hxB⟩ := Set.nonempty_compl.mpr hB
  obtain ⟨y,hyA⟩ := Set.nonempty_compl.mpr hA
  have hxA : x ∈ A := by
    have hx : x ∈ A ∪ B := hcover.symm ▸ Set.mem_univ x
    exact hx.resolve_right hxB
  have hyB : y ∈ B := by
    have hy : y ∈ A ∪ B := hcover.symm ▸ Set.mem_univ y
    exact hy.resolve_left hyA
  let S := A ∩ B
  let I := G.induce Sᶜ
  let a : (Sᶜ : Set V) := ⟨x,fun h => hxB h.2⟩
  let b : (Sᶜ : Set V) := ⟨y,fun h => hyA h.1⟩
  have hstep : ∀ u v : (Sᶜ : Set V), u.val ∈ A → I.Adj u v → v.val ∈ A := by
    intro u v hu huv
    by_contra hv
    have huB : u.val ∉ B := fun hub => u.property ⟨hu,hub⟩
    have hvB : v.val ∈ B := by
      have hh : v.val ∈ A ∪ B := hcover.symm ▸ Set.mem_univ _
      exact hh.resolve_left hv
    exact hnone u.val ⟨hu,huB⟩ v.val ⟨hvB,hv⟩ huv
  have hwalk : ∀ {u v : (Sᶜ : Set V)}, I.Walk u v → u.val ∈ A → v.val ∈ A := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u v w huv p ih => exact fun hu => ih (hstep u v hu huv)
  obtain ⟨p⟩ := hG S hk a b
  exact hyA (hwalk p hxA)

lemma noSmallSeparator_iff_deletionConnected {G : SimpleGraph V} {k : ℕ} :
    NoSmallSeparator G k ↔ DeletionConnected G k :=
  ⟨NoSmallSeparator.deletionConnected, DeletionConnected.noSmallSeparator⟩

lemma number_bound_of_deletion_connected (k B : ℕ)
    (hhigh : ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      DeletionConnected G k → number G ≤ B * Fintype.card W) :
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      number G ≤ ((2*k+1)^2 + (k+1)*B) * Fintype.card W :=
  number_bound_of_no_small_separator k B (fun G hG => hhigh G hG.deletionConnected)

/-- For each fixed vertex-connectivity threshold, a uniform linear bound on
that class is equivalent to the original conjecture. No such bound is supplied. -/
lemma asymptotic_iff_fixed_vertex_connectivity (k : ℕ) :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card W)) ↔
    (∃ C : ℝ, ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      DeletionConnected G k →
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ C * Fintype.card W) := by
  rw [asymptotic_iff_uniform]
  constructor
  · rintro ⟨C,hC⟩
    exact ⟨C,fun G _ => hC G⟩
  · rintro ⟨C,hC⟩
    have hnat : ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
        DeletionConnected G k → number G ≤ ⌈C⌉₊ * Fintype.card W := by
      intro W _ _ G hG
      obtain ⟨D,hD,hd,hcard⟩ := hC G hG
      have hc : (D.card : ℝ) ≤ (⌈C⌉₊ : ℝ) * Fintype.card W :=
        hcard.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg _))
      have hn : D.card ≤ ⌈C⌉₊ * Fintype.card W := by exact_mod_cast hc
      exact (number_le D hD hd).trans hn
    refine ⟨(((2*k+1)^2 + (k+1)*⌈C⌉₊ : ℕ) : ℝ), ?_⟩
    intro W _ _ G
    obtain ⟨D,hD,hd,hcard⟩ := exists_minimum G
    refine ⟨D,hD,hd,?_⟩
    have h := number_bound_of_deletion_connected k ⌈C⌉₊ hnat G
    rw [← hcard] at h
    exact_mod_cast h

#print axioms noSmallSeparator_iff_deletionConnected
#print axioms number_bound_of_deletion_connected
#print axioms asymptotic_iff_fixed_vertex_connectivity

#print axioms split_number
#print axioms number_bound_of_no_small_separator

/-- Global edge-minimality can be imposed at the same time as fixed vertex
connectivity. Extracting a minimal maximizer may destroy connectivity, so the
separator induction is performed after extraction, not before it. -/
lemma number_bound_of_minimal_deletion_connected (k B : ℕ)
    (hhigh : ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      EdgeHull.Minimal G → DeletionConnected G k → number G ≤ B * Fintype.card W) :
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      number G ≤ ((2*k+1)^2 + (k+1)*B) * Fintype.card W :=
  number_bound_of_minimal_no_small_separator k B
    (fun G hm hG => hhigh G hm hG.deletionConnected)

lemma asymptotic_iff_minimal_fixed_vertex_connectivity (k : ℕ) :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ ↦ (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card W)) ↔
    (∃ B : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      EdgeHull.Minimal G → DeletionConnected G k → number G ≤ B * Fintype.card W) := by
  rw [asymptotic_iff_uniform]
  constructor
  · rintro ⟨C,hC⟩
    refine ⟨⌈C⌉₊,?_⟩
    intro W _ _ G _ _
    obtain ⟨D,hD,hd,hcard⟩ := hC G
    have hc : (D.card : ℝ) ≤ (⌈C⌉₊ : ℝ) * Fintype.card W :=
      hcard.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg _))
    have hn : D.card ≤ ⌈C⌉₊ * Fintype.card W := by exact_mod_cast hc
    exact (number_le D hD hd).trans hn
  · rintro ⟨B,hB⟩
    refine ⟨(((2*k+1)^2 + (k+1)*B : ℕ) : ℝ), ?_⟩
    intro W _ _ G
    obtain ⟨D,hD,hd,hcard⟩ := exists_minimum G
    refine ⟨D,hD,hd,?_⟩
    have h := number_bound_of_minimal_deletion_connected k B hB G
    rw [← hcard] at h
    exact_mod_cast h

#print axioms number_bound_of_minimal_deletion_connected
#print axioms asymptotic_iff_minimal_fixed_vertex_connectivity

#print axioms number_bound_of_minimal_no_small_separator
end Erdos184Work.VertexSeparators
