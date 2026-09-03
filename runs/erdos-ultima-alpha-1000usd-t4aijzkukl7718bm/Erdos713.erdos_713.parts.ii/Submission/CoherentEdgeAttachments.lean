import FormalConjecturesUtil
import Submission.RootedEdgeFan

/-! Position-consistent edge attachments. The attached edge is identified
with the corresponding edge of a specified copy already in the old graph.
There is no edge-transitivity hypothesis and no assertion that an arbitrary
attachment has this form. -/

open SimpleGraph Filter Asymptotics
namespace Erdos713CoherentEdges
open Erdos713Rate Erdos713EdgeAttachments Erdos713RootPower

/-- Put the old host in the first petal and the fresh copy in the second.
Their only shared vertices are the endpoints of the prescribed edge. -/
noncomputable def pasteCopyFan {A W : Type*} {F : SimpleGraph A} {H : SimpleGraph W}
    (f : F.Copy H) {x y : A} (hxy : F.Adj x y) :
    (paste F x y H (f x) (f y)).Copy (Erdos713EdgeFan.fan H (f x) (f y) 2) := by
  classical
  let f₀ := Erdos713EdgeFan.petalCopy H (f.toHom.map_adj hxy).ne (0 : Fin 2)
  let f₁ := Erdos713EdgeFan.petalCopy H (f.toHom.map_adj hxy).ne (1 : Fin 2)
  apply extendCopy f₀ (f x) (f y) (f₁.comp f)
  · change Erdos713EdgeFan.petalMap (f x) (f y) 1 (f x) =
      Erdos713EdgeFan.petalMap (f x) (f y) 0 (f x)
    simp [Erdos713EdgeFan.petalMap]
  · change Erdos713EdgeFan.petalMap (f x) (f y) 1 (f y) =
      Erdos713EdgeFan.petalMap (f x) (f y) 0 (f y)
    simp [Erdos713EdgeFan.petalMap]
  · intro a w
    have ha₀ : f a.val ≠ f x := fun h => a.prop.1 (f.injective h)
    have ha₁ : f a.val ≠ f y := fun h => a.prop.2 (f.injective h)
    change Erdos713EdgeFan.petalMap (f x) (f y) 1 (f a.val) ≠
      Erdos713EdgeFan.petalMap (f x) (f y) 0 w
    simp only [Erdos713EdgeFan.petalMap,dif_neg ha₀,dif_neg ha₁]
    split_ifs <;> simp

lemma pasteCopyFan_left {A W : Type*} {F : SimpleGraph A} {H : SimpleGraph W}
    (f : F.Copy H) {x y : A} (hxy : F.Adj x y) :
    pasteCopyFan f hxy (.inl (f x)) = .inl false := by
  simp [pasteCopyFan,extendCopy,Erdos713EdgeFan.petalCopy,Erdos713EdgeFan.petalMap]

/-- Unlike arbitrary attachments, the edge roles and orientation match the
specified old copy. The roles are allowed to vary at each step. -/
inductive Built {A : Type} (F : SimpleGraph A) :
    {W : Type} → SimpleGraph W → Prop
  | base : Built F F
  | step {W : Type} [Fintype W] {H : SimpleGraph W}
      (h : Built F H) (f : F.Copy H) (x y : A) (hxy : F.Adj x y) :
      Built F (paste F x y H (f x) (f y))

lemma Built.finite {A W : Type} [Finite A] {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) : Finite W := by
  induction h with
  | base => infer_instance
  | step h f x y hxy ih => infer_instance

lemma Built.contains {A W : Type} {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) : F ⊑ H := by
  induction h with
  | base => exact .refl _
  | @step W _ H h f x y hxy ih =>
    exact ih.trans ⟨oldCopy F x y H (f x) (f y)⟩

lemma Built.connected {A W : Type} {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) (hF : F.Connected) : H.Connected := by
  induction h with
  | base => exact hF
  | step h f x y hxy ih => exact paste_connected hxy hF ih (f.toHom.map_adj hxy)

lemma Built.isBipartite {A W : Type} {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) (hF : F.IsBipartite) : H.IsBipartite := by
  induction h with
  | base => exact hF
  | step h f x y hxy ih => exact paste_isBipartite hxy hF ih (f.toHom.map_adj hxy)

/-- A uniform comparison in n. Isolated forbidden vertices are permitted;
the additive linear term accounts for them. -/
lemma Built.extremal_bound {A W : Type} [Fintype A] {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) :
    ∃ C : ℕ, ∀ n, extremalNumber n H ≤ C * (extremalNumber n F + n) := by
  induction h with
  | base => exact ⟨1,fun n => by simp⟩
  | @step W _ H h f x y hxy ih =>
    obtain ⟨C,hC⟩ := ih
    let K : ℕ := 2 ^ (2 * (2 * Fintype.card W) + 2)
    refine ⟨K * (C + Fintype.card W),fun n => ?_⟩
    calc
      extremalNumber n (paste F x y H (f x) (f y)) ≤
          extremalNumber n (Erdos713EdgeFan.fan H (f x) (f y) 2) :=
        (show paste F x y H (f x) (f y) ⊑ Erdos713EdgeFan.fan H (f x) (f y) 2 from
          ⟨pasteCopyFan f hxy⟩).extremalNumber_le
      _ ≤ K * (extremalNumber n H + Fintype.card W * n) :=
        Erdos713EdgeFan.extremal_bound H (f.toHom.map_adj hxy) (by omega) n
      _ ≤ K * ((C + Fintype.card W) * (extremalNumber n F + n)) := by
        apply Nat.mul_le_mul_left
        calc
          extremalNumber n H + Fintype.card W * n ≤
              C * (extremalNumber n F + n) + Fintype.card W * n :=
            Nat.add_le_add_right (hC n) _
          _ ≤ (C + Fintype.card W) * (extremalNumber n F + n) := by
            nlinarith
      _ = _ := (Nat.mul_assoc _ _ _).symm

lemma Built.upper {A W : Type} [Fintype A] {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) {r : ℝ} (hr : 1 ≤ r)
    (hF : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r)) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r) := by
  obtain ⟨C,hC⟩ := h.extremal_bound
  have hlin := cast_linear_bigO hr 1
  simp only [one_mul] at hlin
  apply IsBigO.trans _ ((hF.add hlin).const_mul_left (C : ℝ))
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast,Real.norm_of_nonneg (by positivity),one_mul]
  exact_mod_cast hC n

lemma Built.upper_iff {A W : Type} [Fintype A] {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) {r : ℝ} (hr : 1 ≤ r) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r) ↔
    (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)^r) :=
  ⟨fun hH => (extremal_mono_bigO h.contains).trans hH,h.upper hr⟩

lemma Built.rate_iff {A W : Type} [Fintype A] {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) {r : ℝ} : HasRate H r ↔ HasRate F r := by
  constructor
  · intro hH
    refine ⟨hH.one_le,(h.upper_iff hH.one_le).mp hH.upper,?_⟩
    intro a ha hA
    exact hH.lower a ha (h.upper ha hA)
  · intro hF
    refine ⟨hF.one_le,h.upper hF.one_le hF.upper,?_⟩
    intro a ha hA
    exact hF.lower a ha ((h.upper_iff ha).mp hA)

/-- Both containments are required: arbitrary subgraphs of a coherent
construction need not retain the base exponent. -/
lemma sandwich_rate_iff {A W T : Type} [Fintype A] {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) {J : SimpleGraph T}
    (hlo : F ⊑ J) (hhi : J ⊑ H) {r : ℝ} : HasRate J r ↔ HasRate F r := by
  constructor
  · intro hJ
    refine ⟨hJ.one_le,(extremal_mono_bigO hlo).trans hJ.upper,?_⟩
    intro a ha hA
    exact hJ.lower a ha ((extremal_mono_bigO hhi).trans (h.upper ha hA))
  · intro hF
    refine ⟨hF.one_le,(extremal_mono_bigO hhi).trans (h.upper hF.one_le hF.upper),?_⟩
    intro a ha hA
    exact hF.lower a ha ((extremal_mono_bigO hlo).trans hA)

lemma rational_of_sandwich {A W T : Type} [Fintype A] {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) {J : SimpleGraph T}
    (hlo : F ⊑ J) (hhi : J ⊑ H) {r : ℚ} (hF : HasRate F (r : ℝ))
    {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (hAsymptotic : IsEquivalent atTop (fun n : ℕ => (extremalNumber n J : ℝ))
      (fun n : ℕ => c * (n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) := by
  exact ⟨r,((sandwich_rate_iff h hlo hhi).mpr hF).unique
    (rate_of_asymptotic hα hc hAsymptotic)⟩

/-- Coherent pasting preserves rooted bounds when they are known for the
base. Connectivity moves the retained root to all vertices of the new graph. -/
lemma Built.root_bounds {A W : Type} [Fintype A] {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) (hF : F.Connected) {r : ℝ}
    (hRoots : ∀ x, RootPowerBound F x r) : ∀ z, RootPowerBound H z r := by
  induction h with
  | base => exact hRoots
  | @step W _ H h f x y hxy ih =>
    intro z
    have hH := h.connected hF
    letI : Nontrivial W := ⟨⟨f x,f y,(f.toHom.map_adj hxy).ne⟩⟩
    have hNoIso : ∀ a, ∃ b, H.Adj a b := hH.preconnected.exists_adj_of_nontrivial
    have hfan := Erdos713EdgeFan.root_bound H hNoIso (f.toHom.map_adj hxy)
      (t := 2) (by omega) (ih (f x))
    have hfan' : RootPowerBound (Erdos713EdgeFan.fan H (f x) (f y) 2)
        (pasteCopyFan f hxy (.inl (f x))) r := by
      simpa only [pasteCopyFan_left] using hfan
    have hpaste := hfan'.of_copy (pasteCopyFan f hxy) (.inl (f x))
    exact hpaste.of_reachable ((paste_connected hxy hF hH (f.toHom.map_adj hxy)) _ z)

lemma Built.root_bounds_iff {A W : Type} [Fintype A] {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) (hF : F.Connected) {r : ℝ} :
    (∀ z, RootPowerBound H z r) ↔ (∀ x, RootPowerBound F x r) := by
  refine ⟨?_,h.root_bounds hF⟩
  obtain ⟨f⟩ := h.contains
  exact fun hh x => (hh (f x)).of_copy f x

lemma sandwich_rooted_rate_iff {A W T : Type} [Fintype A] {F : SimpleGraph A}
    {H : SimpleGraph W} (h : Built F H) (hF : F.Connected) {J : SimpleGraph T}
    (hlo : F ⊑ J) (hhi : J ⊑ H) :
    Erdos713ActualBlocks.RootedRate J ↔ Erdos713ActualBlocks.RootedRate F := by
  constructor
  · rintro ⟨r,hr,hRoots⟩
    obtain ⟨f⟩ := hlo
    exact ⟨r,(sandwich_rate_iff h ⟨f⟩ hhi).mp hr,fun x => (hRoots (f x)).of_copy f x⟩
  · rintro ⟨r,hr,hRoots⟩
    obtain ⟨f⟩ := hhi
    exact ⟨r,(sandwich_rate_iff h hlo ⟨f⟩).mpr hr,
      fun z => (h.root_bounds hF hRoots (f z)).of_copy f z⟩

/-- The host may contain additional edges: both arrows denote copies, not
induced copies. -/
def Sandwich {A T : Type} (F : SimpleGraph A) (J : SimpleGraph T) : Prop :=
  ∃ (W : Type) (H : SimpleGraph W), Built F H ∧ F ⊑ J ∧ J ⊑ H

lemma Sandwich.rate_iff {A T : Type} [Fintype A] {F : SimpleGraph A}
    {J : SimpleGraph T} (h : Sandwich F J) {r : ℝ} : HasRate J r ↔ HasRate F r := by
  obtain ⟨W,H,h,hlo,hhi⟩ := h
  exact sandwich_rate_iff h hlo hhi

lemma Sandwich.rooted_rate_iff {A T : Type} [Fintype A] {F : SimpleGraph A}
    {J : SimpleGraph T} (h : Sandwich F J) (hF : F.Connected) :
    Erdos713ActualBlocks.RootedRate J ↔ Erdos713ActualBlocks.RootedRate F := by
  obtain ⟨W,H,h,hlo,hhi⟩ := h
  exact sandwich_rooted_rate_iff h hF hlo hhi

/-- A concrete family using the already established small-shore base rates.
The constructed host itself need not have a small bipartition shore. -/
def SmallSandwich {T : Type} (J : SimpleGraph T) : Prop :=
  ∃ (q : ℕ) (F : SimpleGraph (Fin q)) (S : Set (Fin q)),
    F.Connected ∧ F.IsBipartiteWith S Sᶜ ∧ Nat.card S ≤ 3 ∧
      (∀ v, 2 ≤ Nat.card (F.neighborSet v)) ∧ Sandwich F J

lemma SmallSandwich.rooted_rate {T : Type} {J : SimpleGraph T} (h : SmallSandwich J) :
    Erdos713ActualBlocks.RootedRate J := by
  obtain ⟨q,F,S,hF,hB,hS,hd,h⟩ := h
  letI := hF.nonempty
  exact (h.rooted_rate_iff hF).mpr (small_core F S hB hS hd)

lemma SmallSandwich.rational {T : Type} {J : SimpleGraph T} (h : SmallSandwich J)
    {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (hAsymptotic : IsEquivalent atTop (fun n : ℕ => (extremalNumber n J : ℝ))
      (fun n : ℕ => c * (n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr,_⟩ := h.rooted_rate
  exact ⟨r,hr.unique (rate_of_asymptotic hα hc hAsymptotic)⟩

lemma block_rates_of_small_sandwich_blocks {W : Type} [Fintype W] (G : SimpleGraph W)
    (h : ∀ S : Set W, Erdos713Blocks.IsBlock G S → 3 ≤ Nat.card S →
      Erdos713CycleAssembly.Piece (G.induce S) ∨ SmallSandwich (G.induce S)) :
    Erdos713ActualBlocks.BlockRates G := by
  classical
  intro S hS hCyc
  rcases h S hS hCyc with hOld | hNew
  · letI := hS.connected.nonempty
    exact hOld.rooted_rate (hS.noCut.min_degree hS.connected
      (by simpa only [Fintype.card_eq_nat_card] using hCyc))
  · exact hNew.rooted_rate

#print axioms pasteCopyFan
#print axioms Built.extremal_bound
#print axioms Built.rate_iff
#print axioms sandwich_rate_iff
#print axioms rational_of_sandwich
#print axioms Built.root_bounds_iff
#print axioms sandwich_rooted_rate_iff
#print axioms SmallSandwich.rooted_rate
#print axioms block_rates_of_small_sandwich_blocks
end Erdos713CoherentEdges
