import FormalConjecturesUtil
import Submission.CompactSymmRootsAudit

/-! A hub can force extensive quotient-root overlap even in bipartite
K44-free graphs of growing minimum degree. No extremality is asserted. -/
open SimpleGraph Finset
namespace Erdos713HubOverlap
open Erdos713C6

variable {A B W : Type*}

abbrev K33 := completeBipartiteGraph (Fin 3) (Fin 3)
abbrev K34 := completeBipartiteGraph (Fin 3) (Fin 4)
abbrev K44 := completeBipartiteGraph (Fin 4) (Fin 4)

def cone (R : A → B → Prop) : SimpleGraph (Option A ⊕ B) :=
  bipGraph (fun a b => a.elim True (fun a => R a b))

def hub : Option A ⊕ B := .inl none

def old (z : A ⊕ B) : Option A ⊕ B := Sum.map some id z

lemma old_injective : Function.Injective (old (A := A) (B := B)) :=
  Sum.map_injective.mpr ⟨Option.some_injective _,Function.injective_id⟩

def oldCopy (R : A → B → Prop) : (bipGraph R).Copy (cone R) :=
  ⟨⟨old,by rintro (a|b) (a'|b') h <;> exact h⟩,old_injective⟩

def strip (z : Option A ⊕ B) (hz : z ≠ hub) : A ⊕ B :=
  match z with
  | .inl none => (hz rfl).elim
  | .inl (some a) => .inl a
  | .inr b => .inr b

lemma old_strip (z : Option A ⊕ B) (hz : z ≠ hub) : old (strip z hz) = z := by
  rcases z with (_|a)|b
  · exact (hz rfl).elim
  · rfl
  · rfl

lemma strip_adj {R : A → B → Prop} {z w : Option A ⊕ B} (hz : z ≠ hub) (hw : w ≠ hub)
    (h : (cone R).Adj z w) : (bipGraph R).Adj (strip z hz) (strip w hw) := by
  rcases z with (_|a)|b <;> rcases w with (_|a')|b'
  all_goals first | exact (hz rfl).elim | exact (hw rfl).elim | exact h

def copy_avoiding {R : A → B → Prop} {H : SimpleGraph W} (f : H.Copy (cone R))
    (hf : ∀ v, f v ≠ hub) : H.Copy (bipGraph R) :=
  ⟨⟨fun v => strip (f v) (hf v),fun h => strip_adj _ _ (f.toHom.map_adj h)⟩,by
    intro u v huv
    apply f.injective
    change strip (f u) (hf u) = strip (f v) (hf v) at huv
    simpa only [old_strip] using congrArg old huv⟩

lemma three_avoiding {V : Type*} (f : Fin 4 → V) (hf : Function.Injective f) (v : V) :
    ∃ e : Fin 3 ↪ Fin 4, ∀ i, f (e i) ≠ v := by
  classical
  by_cases h : ∃ i, f i = v
  · obtain ⟨a,ha⟩ := h
    exact ⟨a.succAboveEmb,fun i hi => Fin.succAbove_ne a i (hf (hi.trans ha.symm))⟩
  · exact ⟨Fin.castSuccEmb,fun i hi => h ⟨_,hi⟩⟩

lemma cone_free_K44 {R : A → B → Prop} (hf : K33.Free (bipGraph R)) : K44.Free (cone R) := by
  rintro ⟨f⟩
  obtain ⟨L,hL⟩ := three_avoiding (fun i => f (.inl i)) (f.injective.comp Sum.inl_injective) hub
  obtain ⟨J,hJ⟩ := three_avoiding (fun i => f (.inr i)) (f.injective.comp Sum.inr_injective) hub
  let e : K33.Copy K44 := ⟨⟨Sum.map L J,by
    intro u v h
    cases u <;> cases v <;> simpa [K33,K44,completeBipartiteGraph] using h⟩,
    Sum.map_injective.mpr ⟨L.injective,J.injective⟩⟩
  let g := f.comp e
  have hg : ∀ v, g v ≠ hub := by
    rintro (i|j)
    · exact hL i
    · exact hJ j
  exact hf ⟨copy_avoiding g hg⟩

lemma K34_hits_hub {R : A → B → Prop} (hf : K33.Free (bipGraph R)) (f : K34.Copy (cone R)) :
    ∃ v, f v = hub := by
  classical
  by_contra hh
  have ha : ∀ v, f v ≠ hub := by simpa only [not_exists] using hh
  exact hf ((Erdos713K3t.contains_K33 (by decide : 3 ≤ 4)).trans ⟨copy_avoiding f ha⟩)

lemma K34_copies_intersect {R : A → B → Prop} (hf : K33.Free (bipGraph R))
    (f g : K34.Copy (cone R)) : ∃ u v, f u = g v := by
  obtain ⟨u,hu⟩ := K34_hits_hub hf f
  obtain ⟨v,hv⟩ := K34_hits_hub hf g
  exact ⟨u,v,hu.trans hv.symm⟩

lemma cone_bipartite (R : A → B → Prop) : (cone R).IsBipartite := by
  refine ⟨Coloring.mk (fun z => z.elim (fun _ => (0 : Fin 2)) (fun _ => 1)) ?_⟩
  rintro (a|b) (a'|b') h <;> first | exact h.elim | (simp only [Sum.elim_inl,Sum.elim_inr]; decide)

open scoped Classical in
noncomputable def row [Fintype B] (R : A → B → Prop) (a : A) : Finset B := univ.filter (R a)
open scoped Classical in
noncomputable def col [Fintype A] (R : A → B → Prop) (b : B) : Finset A := univ.filter (fun a => R a b)
open scoped Classical in
noncomputable def common [Fintype B] (R : A → B → Prop) (a a' : A) : Finset B :=
  univ.filter (fun b => R a b ∧ R a' b)

lemma common_diagonal [Fintype B] (R : A → B → Prop) (a : A) : common R a a = row R a := by
  classical
  ext b
  simp [common,row]

lemma common_count [Fintype A] [Fintype B] (R : A → B → Prop) (a : A) :
    (∑ b ∈ row R a, (col R b).card) = ∑ a' : A, (common R a a').card := by
  classical
  simp only [row,col,common,Finset.card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a' _
  by_cases ha : R a a' <;> simp [ha]

lemma every_row_has_common_four [Fintype A] [Fintype B] (R : A → B → Prop) {d : ℕ}
    (hrow : ∀ a, d ≤ (row R a).card) (hcol : ∀ b, d ≤ (col R b).card)
    (hlarge : 3*Fintype.card A < d*(d-1)) (a : A) :
    ∃ a', a ≠ a' ∧ 4 ≤ (common R a a').card := by
  classical
  by_contra hh
  push_neg at hh
  have hlow : d*(row R a).card ≤ ∑ b ∈ row R a, (col R b).card := by
    calc
      _ = ∑ _b ∈ row R a, d := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun b _ => hcol b)
  rw [common_count] at hlow
  have hsplit := sum_erase_add (s := (univ : Finset A)) (f := fun a' => (common R a a').card) (mem_univ a)
  dsimp only at hsplit
  rw [common_diagonal] at hsplit
  have hother : (∑ a' ∈ univ.erase a, (common R a a').card) ≤ 3*Fintype.card A := by
    calc
      _ ≤ ∑ _a' ∈ univ.erase a, 3 := sum_le_sum (fun a' ha' => by
        have hx := hh a' (mem_erase.mp ha').1.symm
        omega)
      _ ≤ 3*Fintype.card A := by simp; omega
  have hdpos : 1 ≤ d := by nlinarith
  have hd : d-1+1 = d := by omega
  have hrowa := hrow a
  have hm := Nat.mul_le_mul_left (d-1) hrowa
  nlinarith

lemma rooted_K34_of_common [Fintype B] {R : A → B → Prop} {a a' : A}
    (hne : a ≠ a') (hfour : 4 ≤ (common R a a').card) :
    ∃ f : K34.Copy (cone R), f (.inl 0) = old (.inl a) := by
  classical
  have hc : Fintype.card (Fin 4) ≤ Fintype.card (common R a a') := by simpa using hfour
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  let L : Fin 3 → Option A := ![some a, none, some a']
  have hL : Function.Injective L := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [L]
  let J : Fin 4 → B := fun j => (e j).val
  have hJ : Function.Injective J := Subtype.val_injective.comp e.injective
  have hadj (i : Fin 3) (j : Fin 4) :
      (cone R).Adj (.inl (L i)) (.inr (J j)) := by
    have hj : R a (J j) ∧ R a' (J j) := by
      simpa only [common,mem_filter,mem_univ,true_and,J] using (e j).property
    fin_cases i
    · exact hj.1
    · trivial
    · exact hj.2
  let f : K34.Copy (cone R) := ⟨⟨Sum.map L J,by
    rintro (i|j) (i'|j') h
    · simpa [K34,completeBipartiteGraph] using h
    · exact hadj i j'
    · exact (hadj i' j).symm
    · simpa [K34,completeBipartiteGraph] using h⟩, Sum.map_injective.mpr ⟨hL,hJ⟩⟩
  exact ⟨f,rfl⟩

lemma every_old_left_root [Fintype A] [Fintype B] {R : A → B → Prop} {d : ℕ}
    (hrow : ∀ a, d ≤ (row R a).card) (hcol : ∀ b, d ≤ (col R b).card)
    (hlarge : 3*Fintype.card A < d*(d-1)) (a : A) :
    ∃ f : K34.Copy (cone R), f (.inl 0) = old (.inl a) := by
  obtain ⟨a',ha',hcommon⟩ := every_row_has_common_four R hrow hcol hlarge a
  exact rooted_K34_of_common ha' hcommon

noncomputable def rowEquiv [Fintype B] (R : A → B → Prop) (a : A) :
    (row R a) ≃ (bipGraph R).neighborSet (.inl a) := by
  classical
  refine Equiv.ofBijective (fun b => ⟨.inr b.val,?_⟩) ⟨?_,?_⟩
  · simpa only [row,mem_filter,mem_univ,true_and,cone,bipGraph,Option.elim_some] using b.property
  · intro b b' hh
    exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val hh))
  · rintro ⟨a'|b,h⟩
    · exact h.elim
    · exact ⟨⟨b,by simpa [row] using h⟩,rfl⟩

noncomputable def colEquiv [Fintype A] (R : A → B → Prop) (b : B) :
    (col R b) ≃ (bipGraph R).neighborSet (.inr b) := by
  classical
  refine Equiv.ofBijective (fun a => ⟨.inl a.val,?_⟩) ⟨?_,?_⟩
  · simpa only [col,mem_filter,mem_univ,true_and,cone,bipGraph,Option.elim_some] using a.property
  · intro a a' hh
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val hh))
  · rintro ⟨a|b',h⟩
    · exact ⟨⟨a,by simpa [col] using h⟩,rfl⟩
    · exact h.elim

lemma row_card [Fintype A] [Fintype B] (R : A → B → Prop) (a : A) :
    (row R a).card = Nat.card ((bipGraph R).neighborSet (.inl a)) := by
  classical
  simpa [Nat.card_eq_fintype_card] using Fintype.card_congr (rowEquiv R a)

lemma col_card [Fintype A] [Fintype B] (R : A → B → Prop) (b : B) :
    (col R b).card = Nat.card ((bipGraph R).neighborSet (.inr b)) := by
  classical
  simpa [Nat.card_eq_fintype_card] using Fintype.card_congr (colEquiv R b)

lemma cone_min_degree [Fintype A] [Fintype B] {R : A → B → Prop} {d : ℕ}
    (hrow : ∀ a, d ≤ (row R a).card) (hcol : ∀ b, d ≤ (col R b).card)
    (hB : d ≤ Fintype.card B) (v : Option A ⊕ B) :
    d ≤ Nat.card ((cone R).neighborSet v) := by
  classical
  rcases v with (_|a)|b
  · let e : B ↪ (cone R).neighborSet (.inl none) :=
      ⟨fun b => ⟨.inr b,by trivial⟩,fun b b' hh => Sum.inr.inj (congrArg Subtype.val hh)⟩
    exact hB.trans (by simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_embedding e)
  · let e : (row R a) ↪ (cone R).neighborSet (.inl (some a)) :=
      ⟨fun b => ⟨.inr b.val,by simpa only [row,mem_filter,mem_univ,true_and,cone,bipGraph,Option.elim_some] using b.property⟩,
        fun b b' hh => Subtype.ext (Sum.inr.inj (congrArg Subtype.val hh))⟩
    exact (hrow a).trans (by simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_embedding e)
  · let e : (col R b) ↪ (cone R).neighborSet (.inr b) :=
      ⟨fun a => ⟨.inl (some a.val),by simpa only [col,mem_filter,mem_univ,true_and,cone,bipGraph,Option.elim_some] using a.property⟩,
        fun a a' hh => Subtype.ext (Option.some.inj (Sum.inl.inj (congrArg Subtype.val hh)))⟩
    exact (hcol b).trans (by simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_embedding e)

/-- The designated K34 root is precisely a single-identification root for K44. -/
lemma rooted_K34_singleFold {V : Type*} {G : SimpleGraph V} (f : K34.Copy G) :
    Erdos713Cloning.SingleFold K44 G (f (.inl 0)) := by
  let L : Fin 4 → Fin 3 := ![0,0,1,2]
  let g : K44 →g K34 := ⟨Sum.map L id,by
    rintro (i|j) (i'|j') h <;> simpa [K44,K34,completeBipartiteGraph] using h⟩
  refine ⟨.inl 0,.inl 1,by decide,by simp [K44,completeBipartiteGraph],f.toHom.comp g,rfl,rfl,?_⟩
  intro u v h
  have h' : g u = g v := f.injective h
  rcases u with i|j <;> rcases v with i'|j'
  · have hh : L i = L i' := Sum.inl.inj h'
    fin_cases i <;> fin_cases i' <;> simp_all [L]
  · simpa [g] using h'
  · simpa [g] using h'
  · exact Or.inl (congrArg Sum.inr (Sum.inr.inj h'))

section Norm
variable (K F : Type*) [Field K] [Field F] [Algebra K F]

abbrev normRelation (a b : Erdos713Norm.Vertex K F) : Prop :=
  Algebra.norm K (a.1+b.1) = (a.2 : K)*(b.2 : K)

lemma norm_graph_eq : bipGraph (normRelation K F) = Erdos713Norm.graph K F := by
  ext (a|b) (a'|b') <;> rfl

lemma norm_rows [FiniteDimensional K F] [Fintype F] [Fintype (Erdos713Norm.Vertex K F)]
    (a : Erdos713Norm.Vertex K F) :
    Fintype.card F-1 ≤ (row (normRelation K F) a).card := by
  classical
  rw [row_card,norm_graph_eq]
  have h := Nat.card_le_card_of_injective _ (Erdos713Norm.leftNeighbors K F a).injective
  simpa only [Nat.card_eq_fintype_card,Fintype.card_units] using h

lemma norm_cols [FiniteDimensional K F] [Fintype F] [Fintype (Erdos713Norm.Vertex K F)]
    (b : Erdos713Norm.Vertex K F) :
    Fintype.card F-1 ≤ (col (normRelation K F) b).card := by
  classical
  rw [col_card,norm_graph_eq]
  have h := Nat.card_le_card_of_injective _ (Erdos713Norm.rightNeighbors K F b).injective
  simpa only [Nat.card_eq_fintype_card,Fintype.card_units] using h
end Norm

lemma norm_parameters {p : ℕ} (hp : 3 ≤ p) :
    3*(p^2*(p-1)) < (p^2-1)*((p^2-1)-1) ∧ p^2-1 ≤ p^2*(p-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hp
  have he1 : 3+k-1=k+2 := by omega
  have hid : (3+k)^2=k^2+6*k+9 := by ring
  have he2 : (3+k)^2-1=k^2+6*k+8 := by omega
  have he3 : (3+k)^2-1-1=k^2+6*k+7 := by omega
  rw [he3,he2,he1,hid]
  constructor <;> nlinarith

set_option maxHeartbeats 800000 in
/-- These hosts are not asserted extremal. All quotient copies share one
vertex despite the many designated roots and growing minimum degree. -/
theorem arbitrarily_large_degree (D : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)),
      G.IsBipartite ∧ K44.Free G ∧ D ≤ n ∧
      (∀ v, D ≤ Nat.card (G.neighborSet v)) ∧
      n ≤ 3*T.card ∧
      (∀ v ∈ T, ∃ f : K34.Copy G, f (.inl 0) = v) ∧
      (∀ f g : K34.Copy G, ∃ u v, f u = g v) := by
  classical
  obtain ⟨p,hpD,hp⟩ := Nat.exists_infinite_primes (D+3)
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  let V := Erdos713Norm.Vertex (ZMod p) (GaloisField p 2)
  let R := normRelation (ZMod p) (GaloisField p 2)
  let G₀ := cone R
  have hF : Fintype.card (GaloisField p 2) = p^2 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card p 2 (by decide)
  have hV : Fintype.card V = p^2*(p-1) := by
    simp only [V,Erdos713Norm.Vertex,Fintype.card_prod,Fintype.card_units,hF,ZMod.card]
  have hparams := norm_parameters (show 3 ≤ p by omega)
  have hrows : ∀ a, p^2-1 ≤ (row R a).card := by
    intro a
    simpa only [hF] using norm_rows (ZMod p) (GaloisField p 2) a
  have hcols : ∀ b, p^2-1 ≤ (col R b).card := by
    intro b
    simpa only [hF] using norm_cols (ZMod p) (GaloisField p 2) b
  have hlarge : 3*Fintype.card V < (p^2-1)*((p^2-1)-1) := by
    simpa only [hV] using hparams.1
  have hfree : K33.Free (bipGraph R) := by
    rw [norm_graph_eq]
    exact Erdos713Norm.finite_graph_free p
  have hdD : D ≤ p^2-1 := (show D ≤ p-1 by omega).trans
    (Nat.sub_le_sub_right (by nlinarith : p ≤ p^2) 1)
  have hdeg (v : Option V ⊕ V) : D ≤ Nat.card (G₀.neighborSet v) :=
    hdD.trans (cone_min_degree hrows hcols (by change p^2-1 ≤ Fintype.card V; rw [hV]; exact hparams.2) v)
  have hroots (a : V) : ∃ f : K34.Copy G₀, f (.inl 0) = old (.inl a) :=
    every_old_left_root hrows hcols hlarge a
  let n := Fintype.card (Option V ⊕ V)
  let G : SimpleGraph (Fin n) := G₀.overFin rfl
  let e : G₀ ≃g G := G₀.overFinIso rfl
  let roots : V ↪ Fin n := ⟨fun a => e (old (.inl a)),
    e.injective.comp (old_injective.comp Sum.inl_injective)⟩
  let T := univ.map roots
  have hT : T.card = Fintype.card V := by simp only [T,card_map,card_univ]
  refine ⟨n,G,T,Colorable.of_hom e.symm.toHom (cone_bipartite R),?_,?_,?_,?_,?_,?_⟩
  · rintro ⟨f⟩
    exact cone_free_K44 hfree ⟨e.symm.toCopy.comp f⟩
  · have hn : n = 2*(p^2*(p-1))+1 := by
      simp only [n,Fintype.card_sum,Fintype.card_option,hV]
      omega
    rw [hn]
    omega
  · intro v
    have hv := hdeg (e.symm v)
    have heq := Nat.card_congr (e.mapNeighborSet (e.symm v))
    simpa only [e.apply_symm_apply] using hv.trans_eq heq
  · have hpV : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
    simp only [n,Fintype.card_sum,Fintype.card_option,hT]
    omega
  · intro v hv
    obtain ⟨a,_,ha⟩ := mem_map.mp hv
    obtain ⟨f,hf⟩ := hroots a
    refine ⟨e.toCopy.comp f,?_⟩
    change e (f (.inl 0)) = v
    rw [hf]
    exact ha
  · intro f g
    obtain ⟨u,v,h⟩ := K34_copies_intersect hfree (e.symm.toCopy.comp f) (e.symm.toCopy.comp g)
    exact ⟨u,v,e.symm.injective h⟩

/-- A positive root proportion and large minimum degree do not, on their
own, imply even two disjoint copies of this quotient. -/
theorem no_root_density_disjointness : ¬ (∃ D : ℕ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)),
      G.IsBipartite → K44.Free G → D ≤ n →
      (∀ v, D ≤ Nat.card (G.neighborSet v)) → n ≤ 3*T.card →
      (∀ v ∈ T, ∃ f : K34.Copy G, f (.inl 0) = v) →
      ∃ f g : K34.Copy G, ∀ u v, f u ≠ g v) := by
  rintro ⟨D,hD⟩
  obtain ⟨n,G,T,hB,hF,hn,hmin,hcard,hroots,hinter⟩ := arbitrarily_large_degree D
  obtain ⟨f,g,hdisj⟩ := hD n G T hB hF hn hmin hcard hroots
  obtain ⟨u,v,h⟩ := hinter f g
  exact hdisj u v h

#print axioms rooted_K34_singleFold
#print axioms no_root_density_disjointness
#print axioms cone_free_K44
#print axioms K34_copies_intersect
#print axioms every_old_left_root
#print axioms cone_min_degree
#print axioms arbitrarily_large_degree
end Erdos713HubOverlap
