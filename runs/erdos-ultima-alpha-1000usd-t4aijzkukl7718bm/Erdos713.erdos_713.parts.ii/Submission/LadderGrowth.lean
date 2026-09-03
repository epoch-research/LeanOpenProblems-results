import FormalConjecturesUtil
import Submission.EdgeExtensionCore

/-! Fixed finite ladders have extremal exponent 3/2, via a square-extensible
edge core. This is a special case, not the general rationality conjecture. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713Ladder
open Erdos713EdgeBlockers Erdos713Rate

def graph (n : ℕ) : SimpleGraph (Fin n ⊕ Fin n) where
  Adj
    | .inl i, .inl j => i.val+1 = j.val ∨ j.val+1 = i.val
    | .inr i, .inr j => i.val+1 = j.val ∨ j.val+1 = i.val
    | .inl i, .inr j => i = j
    | .inr i, .inl j => i = j
  symm := by
    rintro (i | i) (j | j) h
    · exact h.symm
    · exact h.symm
    · exact h.symm
    · exact h.symm
  loopless := by rintro (i | i) h <;> omega

instance (n : ℕ) : DecidableRel (graph n).Adj := by
  rintro (i | i) (j | j) <;> dsimp [graph] <;> infer_instance

structure SquareExtension {V : Type*} (G : SimpleGraph V) (u v : V) (B : Finset V) where
  a : V
  b : V
  ne : a ≠ b
  au : a ≠ u
  av : a ≠ v
  bu : b ≠ u
  bv : b ≠ v
  left : G.Adj u a
  right : G.Adj v b
  rung : G.Adj a b
  avoid_a : a ∉ B
  avoid_b : b ∉ B

def SquareExtension.symm {V : Type*} {G : SimpleGraph V} {u v : V} {B : Finset V}
    (h : SquareExtension G u v B) : SquareExtension G v u B :=
  ⟨h.b,h.a,h.ne.symm,h.bv,h.bu,h.av,h.au,h.right,h.left,h.rung.symm,h.avoid_b,h.avoid_a⟩

lemma square_of_copy {V : Type*} {G : SimpleGraph V} (f : Erdos713C4.K22.Copy G)
    (i j : Fin 2) (B : Finset V) (hB : ∀ a, f a ∉ B) :
    Nonempty (SquareExtension G (f (.inl i)) (f (.inr j)) B) := by
  have hi : i+1 ≠ i := by fin_cases i <;> decide
  have hj : j+1 ≠ j := by fin_cases j <;> decide
  refine ⟨f (.inr (j+1)),f (.inl (i+1)),?_,?_,?_,?_,?_,?_,?_,?_,hB _,hB _⟩
  · exact f.injective.ne (by simp)
  · exact f.injective.ne (by simp)
  · exact f.injective.ne (by simpa using hj)
  · exact f.injective.ne (by simpa using hi)
  · exact f.injective.ne (by simp)
  · exact f.toHom.map_adj (by simp [Erdos713C4.K22,completeBipartiteGraph])
  · exact f.toHom.map_adj (by simp [Erdos713C4.K22,completeBipartiteGraph])
  · exact f.toHom.map_adj (by simp [Erdos713C4.K22,completeBipartiteGraph])

lemma square_of_extensible {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (h : Extensible Erdos713C4.K22 G k) {u v : V} (huv : G.Adj u v)
    (B : Finset V) (hc : B.card ≤ k) (hu : u ∉ B) (hv : v ∉ B) :
    Nonempty (SquareExtension G u v B) := by
  obtain ⟨f,⟨i,j,hij,he⟩,hB⟩ := h s(u,v) huv B hc (by
    intro w hw
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    · exact hu
    · exact hv)
  have hh : Nonempty (SquareExtension G (f i) (f j) B) := by
    rcases i with i | i <;> rcases j with j | j
    · simp [Erdos713C4.K22,completeBipartiteGraph] at hij
    · exact square_of_copy f i j B hB
    · obtain ⟨h⟩ := square_of_copy f j i B hB
      exact ⟨h.symm⟩
    · simp [Erdos713C4.K22,completeBipartiteGraph] at hij
  rcases Sym2.eq_iff.mp he with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · simpa only [hu,hv] using hh
  · obtain ⟨h⟩ := hh
    exact ⟨by simpa only [hu,hv] using h.symm⟩

lemma cons_rails {V : Type*} {G : SimpleGraph V} {n : ℕ} (a : V) (f : Fin (n+1) → V)
    (hnew : G.Adj a (f 0))
    (hOld : ∀ i j, i.val+1 = j.val ∨ j.val+1 = i.val → G.Adj (f i) (f j)) :
    ∀ i j : Fin (n+2), i.val+1 = j.val ∨ j.val+1 = i.val →
      G.Adj ((Fin.cons a f : Fin (n+2) → V) i) ((Fin.cons a f : Fin (n+2) → V) j) := by
  intro i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => intro h; simp at h
    | succ j =>
      intro h
      have hj : j = 0 := Fin.ext (by simp only [Fin.val_zero,Fin.val_succ] at h ⊢; omega)
      subst j
      exact hnew
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      intro h
      have hi : i = 0 := Fin.ext (by simp only [Fin.val_zero,Fin.val_succ] at h ⊢; omega)
      subst i
      exact hnew.symm
    | succ j =>
      intro h
      exact hOld i j (by simp only [Fin.val_succ] at h; omega)

noncomputable def extendCopy {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (f : (graph (n+1)).Copy G) (a b : V) (hab : G.Adj a b)
    (hleft : G.Adj a (f (.inl 0))) (hright : G.Adj b (f (.inr 0)))
    (ha : ∀ z, a ≠ f z) (hb : ∀ z, b ≠ f z) : (graph (n+2)).Copy G := by
  let L : Fin (n+2) → V := Fin.cons a (fun i => f (.inl i))
  let R : Fin (n+2) → V := Fin.cons b (fun i => f (.inr i))
  have hL : Function.Injective L := Fin.cons_injective_of_injective
    (by rintro ⟨i,hi⟩; exact ha (.inl i) hi.symm) (f.injective.comp Sum.inl_injective)
  have hR : Function.Injective R := Fin.cons_injective_of_injective
    (by rintro ⟨i,hi⟩; exact hb (.inr i) hi.symm) (f.injective.comp Sum.inr_injective)
  have hLR : ∀ i j, L i ≠ R j := by
    intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact hab.ne
      | succ j => exact ha (.inr j)
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (hb (.inl i)).symm
      | succ j => exact f.injective.ne (by simp)
  have hRailsL := cons_rails a (fun i => f (.inl i)) hleft
    (fun i j hij => f.toHom.map_adj (show (graph (n+1)).Adj (.inl i) (.inl j) from hij))
  have hRailsR := cons_rails b (fun i => f (.inr i)) hright
    (fun i j hij => f.toHom.map_adj (show (graph (n+1)).Adj (.inr i) (.inr j) from hij))
  have hRungs (i : Fin (n+2)) : G.Adj (L i) (R i) := by
    induction i using Fin.cases with
    | zero => exact hab
    | succ i => exact f.toHom.map_adj (show (graph (n+1)).Adj (.inl i) (.inr i) from rfl)
  refine ⟨⟨Sum.elim L R,?_⟩,?_⟩
  · rintro (i | i) (j | j) hij
    · exact hRailsL i j hij
    · change i = j at hij
      subst j
      exact hRungs i
    · change i = j at hij
      subst j
      exact (hRungs i).symm
    · exact hRailsR i j hij
  · rintro (i | i) (j | j) hij
    · exact congrArg Sum.inl (hL hij)
    · exact (hLR i j hij).elim
    · exact (hLR j i hij.symm).elim
    · exact congrArg Sum.inr (hR hij)

lemma contained_of_extensible {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hG : G ≠ ⊥) (hExt : Extensible Erdos713C4.K22 G k) :
    ∀ n : ℕ, 2*(n+1) ≤ k → graph (n+1) ⊑ G := by
  classical
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨u,v,huv⟩ : ∃ u v, G.Adj u v := by
      by_contra hn
      apply hG
      ext u v
      push_neg at hn
      simp [hn u v]
    refine ⟨⟨⟨Sum.elim (fun _ => u) (fun _ => v),?_⟩,?_⟩⟩
    · rintro (i | i) (j | j) hij
      · fin_cases i; fin_cases j; simp [graph] at hij
      · exact huv
      · exact huv.symm
      · fin_cases i; fin_cases j; simp [graph] at hij
    · rintro (i | i) (j | j) hij
      · exact congrArg Sum.inl (Fin.ext (by omega))
      · exact (huv.ne hij).elim
      · exact (huv.ne hij.symm).elim
      · exact congrArg Sum.inr (Fin.ext (by omega))
  | succ n ih =>
    intro hk
    obtain ⟨f⟩ := ih (by omega)
    let U : Finset V := univ.image f
    let u := f (Sum.inl 0)
    let v := f (Sum.inr 0)
    let B := U \ {u,v}
    have huv : G.Adj u v := f.toHom.map_adj (show (graph (n+1)).Adj (.inl 0) (.inr 0) from rfl)
    have hc : B.card ≤ k := by
      have hU : U.card ≤ 2*(n+1) := (card_image_le).trans_eq (by simp; omega)
      exact (card_le_card sdiff_subset).trans (hU.trans (by omega))
    obtain ⟨h⟩ := square_of_extensible hExt huv B hc (by simp [B]) (by simp [B])
    have ha (z) : h.a ≠ f z := by
      intro he
      have hmem : h.a ∈ U := he.symm ▸ mem_image_of_mem f (mem_univ z)
      exact h.avoid_a (mem_sdiff.mpr ⟨hmem,by simp [h.au,h.av]⟩)
    have hb (z) : h.b ≠ f z := by
      intro he
      have hmem : h.b ∈ U := he.symm ▸ mem_image_of_mem f (mem_univ z)
      exact h.avoid_b (mem_sdiff.mpr ⟨hmem,by simp [h.bu,h.bv]⟩)
    exact ⟨extendCopy f h.a h.b h.rung h.left.symm h.right.symm ha hb⟩

lemma free_edge_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    {m : ℕ} (hm : 1 ≤ m) (hfree : (graph m).Free G) :
    Nat.card G.edgeSet ≤ 2^(2*(2*m)+2)*extremalNumber (Fintype.card V) Erdos713C4.K22 := by
  by_contra hn
  have hNoIso : ∀ a, ∃ b, Erdos713C4.K22.Adj a b := by
    rintro (i | i)
    · exact ⟨.inr 0,by simp [Erdos713C4.K22,completeBipartiteGraph]⟩
    · exact ⟨.inl 0,by simp [Erdos713C4.K22,completeBipartiteGraph]⟩
  have hEdge : ∃ a b, Erdos713C4.K22.Adj a b :=
    ⟨.inl 0,.inr 0,by simp [Erdos713C4.K22,completeBipartiteGraph]⟩
  obtain ⟨K,hKG,hne,hExt⟩ := exists_extensible_core Erdos713C4.K22 G hNoIso hEdge (Nat.lt_of_not_ge hn)
  obtain ⟨n,rfl⟩ : ∃ n, m = n+1 := ⟨m-1,by omega⟩
  exact hfree ((contained_of_extensible hne hExt n (by omega)).mono_right hKG)

lemma extremal_bound (m n : ℕ) (hm : 1 ≤ m) :
    extremalNumber n (graph m) ≤ 2^(2*(2*m)+2)*extremalNumber n Erdos713C4.K22 := by
  classical
  rw [← Fintype.card_fin n,extremalNumber_le_iff]
  intro G _ hG
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using free_edge_bound G hm hG

lemma upper (m : ℕ) (hm : 1 ≤ m) :
    (fun n : ℕ => (extremalNumber n (graph m) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((3 : ℝ)/2)) := by
  apply IsBigO.of_bound (2^(2*(2*m)+2) : ℕ)
  filter_upwards with n
  rw [Real.norm_natCast,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  have hh : (extremalNumber n (graph m) : ℝ) ≤
      (2^(2*(2*m)+2) : ℕ)*(extremalNumber n Erdos713C4.K22 : ℝ) := by
    exact_mod_cast extremal_bound m n hm
  exact hh.trans (mul_le_mul_of_nonneg_left (Erdos713C4.extremal_upper n) (by positivity))

def monotoneCopy {m n : ℕ} (h : m ≤ n) : (graph m).Copy (graph n) := by
  let e := (Fin.castLEEmb h).sumMap (Fin.castLEEmb h)
  refine ⟨⟨e,?_⟩,e.injective⟩
  rintro (i | i) (j | j) hij
  · exact hij
  · exact congrArg (Fin.castLE h) hij
  · exact congrArg (Fin.castLE h) hij
  · exact hij

def squareMap : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 :=
  Sum.elim (fun i => if i = 0 then .inl 0 else .inr 1)
    (fun i => if i = 0 then .inr 0 else .inl 1)

def squareCopy : Erdos713C4.K22.Copy (graph 2) := by
  letI : DecidableRel Erdos713C4.K22.Adj := by
    intro a b
    dsimp [Erdos713C4.K22,completeBipartiteGraph]
    infer_instance
  exact ⟨⟨squareMap,by decide⟩,by decide⟩

lemma contains_square {m : ℕ} (hm : 2 ≤ m) : Erdos713C4.K22 ⊑ graph m :=
  ⟨(monotoneCopy hm).comp squareCopy⟩

lemma rate {m : ℕ} (hm : 2 ≤ m) : HasRate (graph m) ((3 : ℝ)/2) :=
  rate_of_C4_upper (contains_square hm) (upper m (by omega))

lemma rational {m : ℕ} (hm : 2 ≤ m) {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n (graph m) : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨3/2,?_⟩
  norm_num
  exact (exponent_eq (rate hm) hα hc h).symm

def flipIso (m : ℕ) : graph m ≃g graph m :=
  ⟨Equiv.sumComm _ _,by rintro (i | i) (j | j) <;> rfl⟩

lemma root_bound {m : ℕ} (hm : 1 ≤ m) (x : Fin m ⊕ Fin m) :
    Erdos713RootPower.RootPowerBound (graph m) x ((3 : ℝ)/2) := by
  apply Erdos713RootPower.of_root_shift (graph m) x (flipIso m).toCopy _ (by norm_num) (upper m hm)
  cases x <;> rfl

lemma rate_of_containment {W : Type*} {H : SimpleGraph W} {m : ℕ}
    (hm : 1 ≤ m) (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ graph m) :
    HasRate H ((3 : ℝ)/2) :=
  rate_of_C4_upper hlo ((extremal_mono_bigO hhi).trans (upper m hm))

lemma rooted_rate_of_containment {W : Type*} {H : SimpleGraph W} {m : ℕ}
    (hm : 1 ≤ m) (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ graph m) :
    Erdos713ActualBlocks.RootedRate H := by
  obtain ⟨f⟩ := hhi
  refine ⟨3/2,by simpa using rate_of_containment hm hlo ⟨f⟩,?_⟩
  intro x
  simpa using (root_bound hm (f x)).of_copy f x

lemma isBipartite (m : ℕ) : (graph m).IsBipartite := by
  let c : Fin m ⊕ Fin m → Fin 2 := Sum.elim
    (fun i => ⟨i.val%2,by omega⟩) (fun i => ⟨(i.val+1)%2,by omega⟩)
  refine ⟨Coloring.mk c ?_⟩
  rintro (i | i) (j | j) hij he
  · have hh := congrArg Fin.val he
    change i.val%2 = j.val%2 at hh
    change i.val+1 = j.val ∨ j.val+1 = i.val at hij
    omega
  · change i = j at hij
    subst j
    have hh := congrArg Fin.val he
    change i.val%2 = (i.val+1)%2 at hh
    omega
  · change i = j at hij
    subst j
    have hh := congrArg Fin.val he
    change (i.val+1)%2 = i.val%2 at hh
    omega
  · have hh := congrArg Fin.val he
    change (i.val+1)%2 = (j.val+1)%2 at hh
    change i.val+1 = j.val ∨ j.val+1 = i.val at hij
    omega

lemma block_rates_of_ladder_blocks {W : Type*} [Fintype W] (G : SimpleGraph W)
    (h : ∀ S : Set W, Erdos713Blocks.IsBlock G S → 3 ≤ Nat.card S →
      Erdos713CycleAssembly.Piece (G.induce S) ∨
      ∃ m : ℕ, 1 ≤ m ∧ Erdos713C4.K22 ⊑ G.induce S ∧ G.induce S ⊑ graph m) :
    Erdos713ActualBlocks.BlockRates G := by
  classical
  intro S hS hc
  rcases h S hS hc with hp | ⟨m,hm,hlo,hhi⟩
  · haveI : Nonempty S := hS.connected.nonempty
    exact hp.rooted_rate (hS.noCut.min_degree hS.connected
      (by simpa only [Fintype.card_eq_nat_card] using hc))
  · exact rooted_rate_of_containment hm hlo hhi

#print axioms square_of_extensible
#print axioms contained_of_extensible
#print axioms extremal_bound
#print axioms rate
#print axioms rational
#print axioms root_bound
#print axioms rooted_rate_of_containment
#print axioms isBipartite
#print axioms block_rates_of_ladder_blocks
end Erdos713Ladder
