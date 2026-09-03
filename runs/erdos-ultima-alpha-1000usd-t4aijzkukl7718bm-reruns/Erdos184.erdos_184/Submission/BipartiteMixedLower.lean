import Submission.MixedCritical

/-! Parameterized lower bounds for mixed decompositions of complete bipartite
graphs. These do not disprove an unspecified uniform linear bound. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.BipartiteMixedLower
open MixedCritical
set_option maxHeartbeats 1000000

abbrev V (h q : ℕ) := Fin h ⊕ Fin q
def G (h q : ℕ) : SimpleGraph (V h q) := completeBipartiteGraph (Fin h) (Fin q)

def left (h q : ℕ) : Finset (V h q) := Finset.univ.map Function.Embedding.inl
def right (h q : ℕ) : Finset (V h q) := Finset.univ.map Function.Embedding.inr

lemma degree_left (h q : ℕ) (i : Fin h) : (G h q).degree (.inl i) = q := by
  have he : (G h q).neighborFinset (.inl i) = right h q := by
    ext v
    cases v <;> simp [G,right,completeBipartiteGraph_adj]
  rw [← card_neighborFinset_eq_degree,he]
  simp [right]

lemma degree_right (h q : ℕ) (i : Fin q) : (G h q).degree (.inr i) = h := by
  have he : (G h q).neighborFinset (.inr i) = left h q := by
    ext v
    cases v <;> simp [G,left,completeBipartiteGraph_adj]
  rw [← card_neighborFinset_eq_degree,he]
  simp [left]

lemma left_independent (h q : ℕ) :
    ∀ u ∈ left h q, ∀ v ∈ left h q, ¬(G h q).Adj u v := by
  intro u hu v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hv
  simp [G,completeBipartiteGraph_adj]

lemma right_independent (h q : ℕ) :
    ∀ u ∈ right h q, ∀ v ∈ right h q, ¬(G h q).Adj u v := by
  intro u hu v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hv
  simp [G,completeBipartiteGraph_adj]

/-- Odd degree on the independent q-side forces at least q singleton edges.
Every cycle contributes at most two degree at each of the h other vertices. -/
lemma partition_lower (h q : ℕ) (hh : Odd h) (D : Finset (G h q).Subgraph)
    (hc : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition (G h q) D) :
    3*h*q ≤ 2*h*D.card + q := by
  obtain ⟨c,s,A,B,hcard,hA,hB,hBs,hdeg,heA,hcA⟩ := split_partition (G h q) D hc hd
  have hL := independent_degree_sum_le_edges B (left h q)
    (fun u hu v hv huv => left_independent h q u hu v hv (hB huv))
  have hR := independent_degree_sum_le_edges B (right h q)
    (fun u hu v hv huv => right_independent h q u hu v hv (hB huv))
  simp only [left,right,Finset.sum_map,Function.Embedding.inl_apply,
    Function.Embedding.inr_apply,hBs] at hL hR
  have hhand := B.sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type,hBs] at hhand
  have hleft : (∑ i : Fin h, B.degree (.inl i)) = s := by omega
  have hright : (∑ i : Fin q, B.degree (.inr i)) = s := by omega
  have hpos (i : Fin q) : 1 ≤ B.degree (.inr i) := by
    have hg := degree_right h q i
    have ht := hdeg (.inr i)
    obtain ⟨a,ha⟩ := heA (.inr i)
    obtain ⟨r,hr⟩ := hh
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hg ht ha ⊢
    omega
  have hs : q ≤ s := by
    calc
      q = ∑ _i : Fin q, 1 := by simp
      _ ≤ ∑ i : Fin q, B.degree (.inr i) := Finset.sum_le_sum (fun i _ => hpos i)
      _ = s := hright
  have hsum : (∑ i : Fin h, A.degree (.inl i)) ≤ 2*h*c := by
    calc
      _ ≤ ∑ _i : Fin h, 2*c := Finset.sum_le_sum (fun i _ => hcA (.inl i))
      _ = 2*h*c := by simp; ring
  have hhub : h*q ≤ 2*h*c+s := by
    calc
      h*q = ∑ i : Fin h, (G h q).degree (.inl i) := by simp [degree_left]
      _ = (∑ i : Fin h, A.degree (.inl i)) + ∑ i : Fin h, B.degree (.inl i) := by
        simp_rw [hdeg]
        rw [Finset.sum_add_distrib]
      _ ≤ 2*h*c+s := by rw [hleft]; omega
  have hp : 1 ≤ h := hh.pos
  have ht : 2*h-1+1 = 2*h := by omega
  have hmul := Nat.mul_le_mul_left (2*h-1) hs
  have htq := congrArg (fun n : ℕ => n*q) ht
  have hts := congrArg (fun n : ℕ => n*s) ht
  nlinarith

lemma number_lower (h q : ℕ) (hh : Odd h) :
    3*h*q ≤ 2*h*MixedCritical.number (G h q) + q := by
  obtain ⟨D,hc,hd,hcard⟩ := minimum_exists (G h q)
  rw [← hcard]
  exact partition_lower h q hh D hc hd

/-- The family K_(h,h²), with h odd, has asymptotic count/order ratio at
least 3/2. This is a lower bound, not a failure of a linear upper bound. -/
lemma square_partition_lower (h : ℕ) (hh : Odd h)
    (D : Finset (G h (h*h)).Subgraph)
    (hc : ∀ H ∈ D, IsCycleOrEdge H.coe) (hd : IsDecomposition (G h (h*h)) D) :
    3*h*h ≤ 2*D.card+h := by
  apply Nat.le_of_mul_le_mul_left (c := h) _ hh.pos
  have hb := partition_lower h (h*h) hh D hc hd
  convert hb using 1 <;> ring

lemma arbitrarily_large_lower (C : ℝ) (hC : C < 3/2) (N : ℕ) :
    ∃ h : ℕ, Odd h ∧ N ≤ Fintype.card (V h (h*h)) ∧
      ∀ D : Finset (G h (h*h)).Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) → IsDecomposition (G h (h*h)) D →
        C * Fintype.card (V h (h*h)) < (D.card : ℝ) := by
  have hδ : 0 < 3-2*C := by linarith
  obtain ⟨t,ht⟩ := exists_nat_gt (max ((2*C+1)/(3-2*C)) (N : ℝ))
  let h := 2*t+1
  have hh : Odd h := ⟨t,rfl⟩
  have hth : (t : ℝ) ≤ h := by exact_mod_cast (show t ≤ h by dsimp [h]; omega)
  have hratio : (2*C+1)/(3-2*C) < (h : ℝ) :=
    ((le_max_left _ _).trans_lt ht).trans_le hth
  have hgap : 2*C+1 < (h : ℝ)*(3-2*C) := (div_lt_iff₀ hδ).mp hratio
  have hNt : N < t := by exact_mod_cast ((le_max_right _ _).trans_lt ht)
  have hN : N ≤ h+h*h := by dsimp [h]; omega
  refine ⟨h,hh,by simpa [V] using hN,?_⟩
  intro D hc hd
  have hb := square_partition_lower h hh D hc hd
  have hbr : 3*(h : ℝ)*(h : ℝ) ≤ 2*(D.card : ℝ)+(h : ℝ) := by exact_mod_cast hb
  have hpos : 0 < (h : ℝ) := by exact_mod_cast hh.pos
  have hstrict := mul_pos hpos (sub_pos.mpr hgap)
  have horder : (Fintype.card (V h (h*h)) : ℝ) = (h : ℝ)+(h : ℝ)*(h : ℝ) := by
    simp [V]
  rw [horder]
  nlinarith

/-- Any PARTICULAR eventual Big-O constant for an all-graph decomposition
bound must be at least 3/2. Constants at least 3/2 remain possible. -/
lemma bigO_constant_lower (f : ℕ → ℝ) (C : ℝ)
    (hbound : ∀ {W : Type} [Fintype W] [DecidableEq W] (A : SimpleGraph W),
      ∃ D : Finset A.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition A D ∧
        (D.card : ℝ) ≤ f (Fintype.card W))
    (hO : Asymptotics.IsBigOWith C Filter.atTop f (fun n : ℕ => (n : ℝ))) :
    3/2 ≤ C := by
  by_contra! hn
  obtain ⟨N,hN⟩ := Filter.Eventually.exists_forall_of_atTop hO.bound
  obtain ⟨h,hh,hlarge,hlower⟩ := arbitrarily_large_lower C hn N
  obtain ⟨D,hc,hd,hf⟩ := hbound (G h (h*h))
  have hlow := hlower D hc hd
  have hu := hN (Fintype.card (V h (h*h))) hlarge
  simp only [Real.norm_eq_abs] at hu
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (Fintype.card (V h (h*h)) : ℝ) by positivity)] at hu
  have hle := le_abs_self (f (Fintype.card (V h (h*h))))
  linarith

end Erdos184.BipartiteMixedLower
