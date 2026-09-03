import FormalConjecturesUtil
import Submission.CompactLadderAudit

/-! Iterated fresh squares attached along existing edges. Aligned embeddings
in square-extensible cores supply rooted as well as ordinary upper bounds.
This is a special family, not a resolution of the general conjecture. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713Squares
open Erdos713EdgeBlockers Erdos713Ladder Erdos713Rate Erdos713RootPower

/-- Keep the old graph and attach the path u--false--true--v. -/
def attach {W : Type*} (H : SimpleGraph W) (u v : W) : SimpleGraph (W ⊕ Bool) where
  Adj
    | .inl a, .inl b => H.Adj a b
    | .inl a, .inr false => a = u
    | .inl a, .inr true => a = v
    | .inr false, .inl b => b = u
    | .inr true, .inl b => b = v
    | .inr a, .inr b => a ≠ b
  symm := by
    rintro (a | a) (b | b) h
    · exact h.symm
    · cases b <;> exact h
    · cases a <;> exact h
    · cases a <;> cases b <;> exact h.symm
  loopless := by
    rintro (a | a) h
    · exact H.loopless a h
    · cases a <;> exact h rfl

def oldCopy {W : Type*} (H : SimpleGraph W) (u v : W) : H.Copy (attach H u v) :=
  ⟨⟨Sum.inl,fun h => h⟩,Sum.inl_injective⟩

/-- The two distinguished vertices are the original base edge, unchanged by
subsequent attachments. Finiteness instances are stored at attachment steps. -/
inductive Built : {W : Type} → SimpleGraph W → W → W → Prop
  | edge : Built (⊤ : SimpleGraph Bool) false true
  | step {W : Type} [Fintype W] {H : SimpleGraph W} {x y : W}
      (h : Built H x y) (u v : W) (huv : H.Adj u v) :
      Built (attach H u v) (.inl x) (.inl y)

lemma Built.adj {W : Type} {H : SimpleGraph W} {x y : W} (h : Built H x y) : H.Adj x y := by
  induction h with
  | edge => simp
  | step h u v huv ih => exact ih

lemma attach_connected {W : Type*} {H : SimpleGraph W} (hH : H.Connected) (u v : W) :
    (attach H u v).Connected := by
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨.inl u,?_⟩
  rintro (w | w)
  · exact (hH u w).map (oldCopy H u v).toHom
  · cases w
    · exact (show (attach H u v).Adj (.inl u) (.inr false) from rfl).reachable
    · exact ((hH u v).map (oldCopy H u v).toHom).trans
        (show (attach H u v).Adj (.inl v) (.inr true) from rfl).reachable

lemma Built.connected {W : Type} {H : SimpleGraph W} {x y : W} (h : Built H x y) :
    H.Connected := by
  induction h with
  | edge => exact connected_top
  | step h u v huv ih => exact attach_connected ih u v

noncomputable def extendCopy {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    (f : H.Copy G) (u v : W) (a b : V) (hab : G.Adj a b)
    (hua : G.Adj (f u) a) (hvb : G.Adj (f v) b)
    (ha : ∀ z, a ≠ f z) (hb : ∀ z, b ≠ f z) : (attach H u v).Copy G := by
  refine ⟨⟨Sum.elim f (fun t => if t then b else a),?_⟩,?_⟩
  · rintro (z | z) (w | w) hzw
    · exact f.toHom.map_adj hzw
    · cases w <;> dsimp only [attach] at hzw <;> subst z
      · exact hua
      · exact hvb
    · cases z <;> dsimp only [attach] at hzw <;> subst w
      · exact hua.symm
      · exact hvb.symm
    · cases z <;> cases w
      · exact (hzw rfl).elim
      · exact hab
      · exact hab.symm
      · exact (hzw rfl).elim
  · rintro (z | z) (w | w) he
    · exact congrArg Sum.inl (f.injective he)
    · cases w
      · exact (ha z he.symm).elim
      · exact (hb z he.symm).elim
    · cases z
      · exact (ha w he).elim
      · exact (hb w he).elim
    · cases z <;> cases w
      · rfl
      · exact (hab.ne he).elim
      · exact (hab.ne he.symm).elim
      · rfl

/-- Every oriented host edge can be the designated base edge. Later square
attachments do not alter the old vertex images. -/
lemma Built.aligned_embedding {W : Type} {H : SimpleGraph W} {x y : W}
    (h : Built H x y) {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hExt : Extensible Erdos713C4.K22 G k) (hk : Nat.card W ≤ k)
    {a b : V} (hab : G.Adj a b) :
    ∃ f : H.Copy G, f x = a ∧ f y = b := by
  classical
  induction h with
  | edge =>
    let f : (⊤ : SimpleGraph Bool).Copy G := ⟨⟨fun t => if t then b else a,by
      rintro (_ | _) (_ | _) h
      · exact (h rfl).elim
      · exact hab
      · exact hab.symm
      · exact (h rfl).elim⟩,by
      rintro (_ | _) (_ | _) he
      · rfl
      · exact (hab.ne he).elim
      · exact (hab.ne he.symm).elim
      · rfl⟩
    exact ⟨f,rfl,rfl⟩
  | @step W _ H x y h u v huv ih =>
    have hkOld : Nat.card W ≤ k := by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_bool] using
        (show Fintype.card W ≤ k by
          simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_bool] at hk
          omega)
    obtain ⟨f,hfx,hfy⟩ := ih hkOld
    let U : Finset V := univ.image f
    let B : Finset V := U \ {f u,f v}
    have hc : B.card ≤ k := (card_le_card sdiff_subset).trans
      (card_image_le.trans (by simpa only [card_univ,Fintype.card_eq_nat_card] using hkOld))
    obtain ⟨s⟩ := square_of_extensible hExt (f.toHom.map_adj huv) B hc (by simp [B]) (by simp [B])
    have hsa (z) : s.a ≠ f z := by
      intro he
      have hmem : s.a ∈ U := he.symm ▸ mem_image_of_mem f (mem_univ z)
      exact s.avoid_a (mem_sdiff.mpr ⟨hmem,by simpa only [mem_insert,mem_singleton,not_or] using And.intro s.au s.av⟩)
    have hsb (z) : s.b ≠ f z := by
      intro he
      have hmem : s.b ∈ U := he.symm ▸ mem_image_of_mem f (mem_univ z)
      exact s.avoid_b (mem_sdiff.mpr ⟨hmem,by simpa only [mem_insert,mem_singleton,not_or] using And.intro s.bu s.bv⟩)
    exact ⟨extendCopy f u v s.a s.b s.rung s.left s.right hsa hsb,hfx,hfy⟩

lemma Built.root_edge_bound {W : Type} {H : SimpleGraph W} {x y : W}
    (h : Built H x y) {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V)
    (hB : G.IsBipartiteWith S Sᶜ) (hroot : ∀ f : H.Copy G, f x ∉ S) :
    Nat.card G.edgeSet ≤ 2^(2*Nat.card W+2)*extremalNumber (Fintype.card V) Erdos713C4.K22 := by
  by_contra hn
  have hNoIso : ∀ a, ∃ b, Erdos713C4.K22.Adj a b := by
    rintro (i | i)
    · exact ⟨.inr 0,by simp [Erdos713C4.K22,completeBipartiteGraph]⟩
    · exact ⟨.inl 0,by simp [Erdos713C4.K22,completeBipartiteGraph]⟩
  have hEdge : ∃ a b, Erdos713C4.K22.Adj a b :=
    ⟨.inl 0,.inr 0,by simp [Erdos713C4.K22,completeBipartiteGraph]⟩
  obtain ⟨K,hKG,hne,hExt⟩ := exists_extensible_core Erdos713C4.K22 G hNoIso hEdge (Nat.lt_of_not_ge hn)
  obtain ⟨u,v,huv⟩ : ∃ u v, K.Adj u v := by
    by_contra hh
    apply hne
    ext u v
    push_neg at hh
    simp [hh u v]
  have hbad {u v : V} (huv : K.Adj u v) (hu : u ∈ S) : False := by
    obtain ⟨f,hfx,hfy⟩ := h.aligned_embedding hExt le_rfl huv
    let g : H.Copy G := (Copy.ofLE K G hKG).comp f
    apply hroot g
    change f x ∈ S
    rwa [hfx]
  rcases hB.mem_of_adj (hKG huv) with h | h
  · exact hbad huv h.1
  · exact hbad huv.symm h.2

lemma Built.root_bound_base {W : Type} {H : SimpleGraph W} {x y : W}
    (h : Built H x y) : RootPowerBound H x ((3 : ℝ)/2) := by
  refine ⟨(2^(2*Nat.card W+2) : ℕ),by positivity,?_⟩
  intro n G S hB hroot
  have hb := h.root_edge_bound G S hB hroot
  simp only [Fintype.card_fin] at hb
  have hb' : (Nat.card G.edgeSet : ℝ) ≤
      (2^(2*Nat.card W+2) : ℕ)*(extremalNumber n Erdos713C4.K22 : ℝ) := by
    exact_mod_cast hb
  exact hb'.trans (mul_le_mul_of_nonneg_left (Erdos713C4.extremal_upper n) (by positivity))

lemma Built.root_bound {W : Type} {H : SimpleGraph W} {x y : W}
    (h : Built H x y) (z : W) : RootPowerBound H z ((3 : ℝ)/2) :=
  h.root_bound_base.of_reachable (h.connected x z)

lemma Built.upper {W : Type} {H : SimpleGraph W} {x y : W} (h : Built H x y) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((3 : ℝ)/2)) := h.root_bound_base.upper

lemma rate_of_containment {W : Type} {H : SimpleGraph W} {x y : W}
    (h : Built H x y) {A : Type*} {J : SimpleGraph A}
    (hlo : Erdos713C4.K22 ⊑ J) (hhi : J ⊑ H) : HasRate J ((3 : ℝ)/2) :=
  rate_of_C4_upper hlo ((extremal_mono_bigO hhi).trans h.upper)

lemma rooted_rate_of_containment {W : Type} {H : SimpleGraph W} {x y : W}
    (h : Built H x y) {A : Type*} {J : SimpleGraph A}
    (hlo : Erdos713C4.K22 ⊑ J) (hhi : J ⊑ H) : Erdos713ActualBlocks.RootedRate J := by
  obtain ⟨f⟩ := hhi
  refine ⟨3/2,by simpa using rate_of_containment h hlo ⟨f⟩,?_⟩
  intro a
  simpa using (h.root_bound (f a)).of_copy f a

lemma Built.isBipartite {W : Type} {H : SimpleGraph W} {x y : W} (h : Built H x y) :
    H.IsBipartite := by
  induction h with
  | edge =>
    exact ⟨Coloring.mk (fun b => if b then 1 else 0) (by decide)⟩
  | @step W _ H x y h u v huv ih =>
    obtain ⟨χ⟩ := ih
    let f : W ⊕ Bool → Fin 2 := Sum.elim χ (fun b => if b then χ u else χ v)
    refine ⟨Coloring.mk f ?_⟩
    rintro (a | a) (b | b) hab
    · exact χ.valid hab
    · cases b <;> dsimp only [attach] at hab <;> subst a
      · exact χ.valid huv
      · exact (χ.valid huv).symm
    · cases a <;> dsimp only [attach] at hab <;> subst b
      · exact (χ.valid huv).symm
      · exact χ.valid huv
    · cases a <;> cases b
      · exact (hab rfl).elim
      · exact (χ.valid huv).symm
      · exact χ.valid huv
      · exact (hab rfl).elim

lemma contains_square_attach {W : Type*} (H : SimpleGraph W) (u v : W)
    (huv : H.Adj u v) : Erdos713C4.K22 ⊑ attach H u v := by
  classical
  let f : Fin 2 ⊕ Fin 2 → W ⊕ Bool := Sum.elim
    (fun i => if i = 0 then .inl u else .inr true)
    (fun i => if i = 0 then .inl v else .inr false)
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · rintro (i | i) (j | j) hij
    · simp [Erdos713C4.K22,completeBipartiteGraph] at hij
    · fin_cases i <;> fin_cases j <;> simp [f,attach,huv]
    · fin_cases i <;> fin_cases j <;> simp [f,attach,huv.symm]
    · simp [Erdos713C4.K22,completeBipartiteGraph] at hij
  · rintro (i | i) (j | j) he <;> fin_cases i <;> fin_cases j <;>
      simp_all [f,huv.ne,huv.ne.symm]

lemma step_rate {W : Type} [Fintype W] {H : SimpleGraph W} {x y : W}
    (h : Built H x y) (u v : W) (huv : H.Adj u v) :
    Erdos713ActualBlocks.RootedRate (attach H u v) :=
  rooted_rate_of_containment (h.step u v huv) (contains_square_attach H u v huv) (.refl _)

lemma Built.rooted_rate {W : Type} {H : SimpleGraph W} {x y : W}
    (h : Built H x y) : Erdos713ActualBlocks.RootedRate H := by
  cases h with
  | edge =>
    have hr (z : Bool) : RootPowerBound (⊤ : SimpleGraph Bool) z 1 :=
      Erdos713RootBlocks.root_bound_small _ (by simp [Nat.card_eq_fintype_card]) z
    refine ⟨1,?_,?_⟩
    · norm_num only [Rat.cast_one]
      exact ⟨le_rfl,(hr false).upper,fun a ha _ => ha⟩
    · simpa only [Rat.cast_one] using hr
  | step h u v huv => exact step_rate h u v huv

/-- Containment between a square and a finite square-attachment construction.
The square containment condition must not be discarded. -/
def Sandwich {A : Type*} (J : SimpleGraph A) : Prop :=
  ∃ (W : Type) (H : SimpleGraph W) (x y : W), Built H x y ∧ Erdos713C4.K22 ⊑ J ∧ J ⊑ H

lemma Sandwich.rate {A : Type*} {J : SimpleGraph A} (h : Sandwich J) : HasRate J ((3 : ℝ)/2) := by
  obtain ⟨W,H,x,y,h,hlo,hhi⟩ := h
  exact rate_of_containment h hlo hhi

lemma Sandwich.rooted_rate {A : Type*} {J : SimpleGraph A} (h : Sandwich J) :
    Erdos713ActualBlocks.RootedRate J := by
  obtain ⟨W,H,x,y,h,hlo,hhi⟩ := h
  exact rooted_rate_of_containment h hlo hhi

lemma Sandwich.rational {A : Type*} {J : SimpleGraph A} (hJ : Sandwich J)
    {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n J : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨3/2,?_⟩
  norm_num
  exact (exponent_eq hJ.rate hα hc h).symm

lemma block_rates_of_square_blocks {W : Type*} [Fintype W] (G : SimpleGraph W)
    (h : ∀ S : Set W, Erdos713Blocks.IsBlock G S → 3 ≤ Nat.card S →
      Erdos713CycleAssembly.Piece (G.induce S) ∨ Sandwich (G.induce S)) :
    Erdos713ActualBlocks.BlockRates G := by
  classical
  intro S hS hc
  rcases h S hS hc with hp | hp
  · haveI : Nonempty S := hS.connected.nonempty
    exact hp.rooted_rate (hS.noCut.min_degree hS.connected
      (by simpa only [Fintype.card_eq_nat_card] using hc))
  · exact hp.rooted_rate

#print axioms Built.rooted_rate
#print axioms Sandwich.rate
#print axioms Sandwich.rooted_rate
#print axioms Sandwich.rational
#print axioms block_rates_of_square_blocks
#print axioms contains_square_attach
#print axioms step_rate
#print axioms Built.aligned_embedding
#print axioms Built.root_edge_bound
#print axioms Built.root_bound
#print axioms rooted_rate_of_containment
#print axioms Built.isBipartite
end Erdos713Squares
