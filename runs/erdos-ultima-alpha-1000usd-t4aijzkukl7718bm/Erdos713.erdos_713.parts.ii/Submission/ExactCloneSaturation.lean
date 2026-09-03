import FormalConjecturesUtil
import Submission.CloneSaturation

/-! Exact extremality under a sufficiently flat quadratic upper support.
This file does not assert rationality of an extremal exponent. -/
open SimpleGraph Finset
namespace Erdos713ExactCloneSaturation
open Erdos713Cloning Erdos713CloneSaturation Erdos713CloneSymm

variable {V W : Type*}

lemma extra_safe (H : SimpleGraph W) (G : SimpleGraph V) (k : ℕ)
    (S : Finset (V × Fin (k+1))) (hS : HasBase S)
    (hf : H.Free (subgraph G k S)) (p : S) (hp : p.val.2 ≠ 0) :
    H.Free (clone G p.val.1) := by
  let f : Option V → S
    | none => p
    | some v => ⟨(v,0),hS v⟩
  have hc : clone G p.val.1 ⊑ subgraph G k S := by
    refine ⟨⟨⟨f,?_⟩,?_⟩⟩
    · rintro (u|u) (v|v) h <;> exact h
    · rintro (u|u) (v|v) h
      · rfl
      · exact (hp (congrArg (fun y : S => y.val.2) h)).elim
      · exact (hp (congrArg (fun y : S => y.val.2) h).symm).elim
      · exact congrArg some (congrArg (fun y : S => y.val.1) h)
  exact fun h => hf (h.trans hc)

lemma bounded_extra_vertices [Fintype V] [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (G : SimpleGraph V) (hopt : CloneOptimal H G)
    (hfree : H.Free G) (hmin : ∀ v, Fintype.card W ≤ Nat.card (G.neighborSet v))
    (S : Finset (V × Fin (Fintype.card W+1))) (hS : HasBase S)
    (hf : H.Free (subgraph G (Fintype.card W) S)) :
    S.card ≤ Fintype.card V + (Fintype.card W+1)*(Fintype.card W)^2 := by
  classical
  let B : Finset (V × Fin (Fintype.card W+1)) := univ.product {0}
  let A : Finset V := univ.filter (fun v => H.Free (clone G v))
  have hs : S ⊆ B ∪ A.product univ := by
    intro p hp
    by_cases hp0 : p.2 = 0
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_product.mpr ⟨mem_univ _,mem_singleton.mpr hp0⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_product.mpr
      refine ⟨?_,mem_univ _⟩
      exact mem_filter.mpr ⟨mem_univ _,extra_safe H G _ S hS hf ⟨p,hp⟩ hp0⟩
  have hc := (card_le_card hs).trans (card_union_le B (A.product univ))
  have hA : A.card ≤ (Fintype.card W)^2 := hopt.safe_card_of_min_degree hH hfree hmin
  have hc' : S.card ≤ Fintype.card V + A.card*(Fintype.card W+1) := by
    simpa [B] using hc
  nlinarith

lemma linear_edges_lower [Fintype V] (G : SimpleGraph V) (k d : ℕ)
    (hdeg : ∀ v, d ≤ Nat.card (G.neighborSet v))
    (S : Finset (V × Fin (k+1))) (hS : HasBase S) :
    Nat.card G.edgeSet + d*(S.card-Fintype.card V) ≤
      Nat.card (subgraph G k S).edgeSet := by
  classical
  revert hS
  refine Finset.strongInductionOn S ?_
  intro S ih hS
  by_cases hzero : ∀ p ∈ S, p.2 = 0
  · have hc : S.card ≤ Fintype.card V := by
      have hsub : S ⊆ (univ : Finset V).product ({0} : Finset (Fin (k+1))) := by
        intro p hp
        exact Finset.mem_product.mpr ⟨mem_univ _,mem_singleton.mpr (hzero p hp)⟩
      simpa using card_le_card hsub
    simpa [Nat.sub_eq_zero_of_le hc] using edge_lower G k S hS
  · push_neg at hzero
    obtain ⟨p,hpS,hp0⟩ := hzero
    let T := S.erase p
    have hT : HasBase T := by
      intro v
      apply mem_erase.mpr
      refine ⟨?_,hS v⟩
      intro he
      exact hp0 (congrArg Prod.snd he).symm
    have hsmall : T ⊂ S := erase_ssubset hpS
    have hIH := ih T hsmall hT
    let x : T := ⟨(p.1,0),hT p.1⟩
    have hmissing : (x.val.1,p.2) ∉ T := by
      change p ∉ S.erase p
      simp
    have heq : insert (x.val.1,p.2) T = S := by
      change insert p (S.erase p) = S
      exact insert_erase hpS
    have he := Iso.card_edgeFinset_eq (insert_iso G k T x p.2 hmissing)
    simp only [edgeFinset_card,Fintype.card_eq_nat_card,card_edges_clone] at he
    rw [heq] at he
    have hd : d ≤ Nat.card ((subgraph G k T).neighborSet x) :=
      (hdeg p.1).trans (degree_lower G k T hT x)
    have hc : T.card+1 = S.card := by simpa [T] using card_erase_add_one hpS
    have hn := vertex_lower hT
    have hsub : S.card-Fintype.card V = (T.card-Fintype.card V)+1 := by omega
    calc
      _ = Nat.card G.edgeSet + d*(T.card-Fintype.card V)+d := by rw [hsub]; ring
      _ ≤ Nat.card (subgraph G k T).edgeSet +
          Nat.card ((subgraph G k T).neighborSet x) := Nat.add_le_add hIH hd
      _ = _ := he
/-- A quadratic upper support for a natural-valued extremal function. -/
def QuadSupport (f : ℕ → ℕ) (ε : ℝ) (n : ℕ) : Prop :=
  ∀ m : ℕ, (f m : ℝ) ≤ (f n : ℝ)+ε*((m : ℝ)^2-(n : ℝ)^2)

lemma record_degree (H : SimpleGraph W) {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hf : H.Free G)
    (he : Nat.card G.edgeSet = extremalNumber n H) {ε : ℝ}
    (hrec : QuadSupport (fun m => extremalNumber m H) ε n) (v : Fin n) :
    ε*(2*(n : ℝ)-1) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
  classical
  have hDel := card_edgeFinset_deleteIncidenceSet_le_extremalNumber hf v
  rw [card_edgeFinset_deleteIncidenceSet] at hDel
  have hNat : G.edgeFinset.card ≤ extremalNumber (n-1) H + G.degree v := by
    simp only [Fintype.card_fin] at hDel
    have hh := G.degree_le_card_edgeFinset v
    omega
  simp only [edgeFinset_card,←card_neighborSet_eq_degree,Fintype.card_eq_nat_card,he] at hNat
  have hReal : (extremalNumber n H : ℝ) ≤ (extremalNumber (n-1) H : ℝ) +
      (Nat.card (G.neighborSet v) : ℝ) := by exact_mod_cast hNat
  have hh := hrec (n-1)
  have hnm : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [hnm] at hh
  nlinarith only [hReal,hh]

lemma record_safe_degree (H : SimpleGraph W) {n : ℕ}
    (G : SimpleGraph (Fin n)) (he : Nat.card G.edgeSet = extremalNumber n H) {ε : ℝ}
    (hrec : QuadSupport (fun m => extremalNumber m H) ε n) (v : Fin n)
    (hv : H.Free (clone G v)) :
    (Nat.card (G.neighborSet v) : ℝ) ≤ ε*(2*(n : ℝ)+1) := by
  have hh := safe_clone_bound H G v hv
  simp only [Fintype.card_fin,he] at hh
  have hhR : (extremalNumber n H : ℝ) + (Nat.card (G.neighborSet v) : ℝ) ≤
      (extremalNumber (n+1) H : ℝ) := by exact_mod_cast hh
  have hr := hrec (n+1)
  push_cast at hr
  nlinarith only [hhR,hr]

/-- A sufficiently flat quadratic support permits an exactly extremal
clone-saturated host at a uniformly bounded distance in order. -/
theorem exact_at_quadratic_support [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) {n D : ℕ} (hn : 0 < n) (hQD : Fintype.card W ≤ D)
    (G : SimpleGraph (Fin n)) (hopt : OrdinaryOptimal H G)
    (he : Nat.card G.edgeSet = extremalNumber n H) {ε : ℝ} (hε : 0 < ε)
    (hrec : QuadSupport (fun m => extremalNumber m H) ε n)
    (hD : (D : ℝ) ≤ ε*(2*(n : ℝ)-1))
    (hsmall : ε*(((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)^2 +
      ((Fintype.card W+1)*(Fintype.card W)^2 : ℕ) + (2 : ℝ)) < 1) :
    ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
      n ≤ Fintype.card U ∧
      Fintype.card U ≤ n+(Fintype.card W+1)*(Fintype.card W)^2 ∧
      H.Free J ∧ Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
      (∀ x, D ≤ Nat.card (J.neighborSet x)) ∧ ∀ x, SingleFold H J x := by
  classical
  let L : ℕ := (Fintype.card W+1)*(Fintype.card W)^2
  have hsmall' : ε*((L : ℝ)^2+L+2) < 1 := by simpa [L] using hsmall
  have htwo : 2*ε < 1 := by
    have hL : 0 ≤ (L : ℝ)^2+(L : ℝ) := by positivity
    nlinarith
  have hdeg (v : Fin n) : D ≤ Nat.card (G.neighborSet v) := by
    exact_mod_cast hD.trans (record_degree H hn G hopt.free he hrec v)
  have hmin (v : Fin n) : Fintype.card W ≤ Nat.card (G.neighborSet v) := (hQD.trans (hdeg v))
  by_cases hs : ∃ v, H.Free (clone G v)
  · obtain ⟨v,hv⟩ := hs
    let d := Nat.card (G.neighborSet v)
    have hdlo : ε*(2*(n : ℝ)-1) ≤ (d : ℝ) := record_degree H hn G hopt.free he hrec v
    have hdhi : (d : ℝ) ≤ ε*(2*(n : ℝ)+1) := record_safe_degree H G he hrec v hv
    have hdmin (w : Fin n) : d ≤ Nat.card (G.neighborSet w) := by
      by_contra hbad
      have hbad' : (Nat.card (G.neighborSet w) : ℝ)+1 ≤ d := by
        exact_mod_cast (show Nat.card (G.neighborSet w)+1 ≤ d by omega)
      have hw := record_degree H hn G hopt.free he hrec w
      nlinarith only [hbad',hw,hdhi,htwo]
    obtain ⟨S,hS,hfree,_,_,hdegree,hfold⟩ := exists_saturated H hH G hopt.free hmin
    have hnS : n ≤ S.card := by simpa using vertex_lower hS
    have hSbound : S.card ≤ n+L := by
      simpa only [Fintype.card_fin] using
        bounded_extra_vertices H hH G hopt.cloneOptimal hopt.free hmin S hS hfree
    let t := S.card-n
    have ht : t ≤ L := by dsimp [t]; omega
    have hnt : S.card = n+t := by dsimp [t]; omega
    have hntR : (S.card : ℝ) = (n : ℝ)+t := by exact_mod_cast hnt
    have htR : (t : ℝ) ≤ L := by exact_mod_cast ht
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have herr : ε*((t : ℝ)^2+t) < 1 := by
      have hsq : (t : ℝ)^2 ≤ (L : ℝ)^2 := by nlinarith
      have hp := mul_le_mul_of_nonneg_left (show (t : ℝ)^2+t ≤ (L : ℝ)^2+L+2 by linarith) hε.le
      exact hp.trans_lt hsmall'
    have hupperR : (extremalNumber S.card H : ℝ) <
        (extremalNumber n H : ℝ)+(d : ℝ)*t+1 := by
      have hr := hrec S.card
      rw [hntR] at hr
      have hm := mul_le_mul_of_nonneg_right hdlo ht0
      nlinarith only [hr,hm,herr]
    have hupper : extremalNumber S.card H ≤ extremalNumber n H+d*t := by
      have hh : extremalNumber S.card H < extremalNumber n H+d*t+1 := by exact_mod_cast hupperR
      omega
    have hlower : extremalNumber n H+d*t ≤ Nat.card (subgraph G (Fintype.card W) S).edgeSet := by
      simpa only [Fintype.card_fin,he] using linear_edges_lower G _ d hdmin S hS
    have hbound : Nat.card (subgraph G (Fintype.card W) S).edgeSet ≤ extremalNumber S.card H := by
      have hh := card_edgeFinset_le_extremalNumber hfree
      simpa only [edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_eq_finsetCard] using hh
    have hEq : Nat.card (subgraph G (Fintype.card W) S).edgeSet = extremalNumber S.card H :=
      le_antisymm hbound (hupper.trans hlower)
    refine ⟨S,inferInstance,subgraph G _ S,?_,?_,hfree,?_,?_,hfold⟩
    · simpa using hnS
    · simpa using hSbound
    · simpa using hEq
    · intro x
      exact (hdeg x.val.1).trans (hdegree x)
  · push_neg at hs
    refine ⟨Fin n,inferInstance,G,by simp,by simp,hopt.free,by simpa using he,hdeg,?_⟩
    intro x
    exact fold_of_obstructed H G x hopt.free (hs x)

#print axioms bounded_extra_vertices
#print axioms linear_edges_lower
#print axioms exact_at_quadratic_support
end Erdos713ExactCloneSaturation
