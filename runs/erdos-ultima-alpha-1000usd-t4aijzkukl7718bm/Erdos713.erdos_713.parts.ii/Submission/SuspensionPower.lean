import FormalConjecturesUtil
import Submission.SuspensionCount

/-! Polynomial degree estimates for forest and six-cycle suspensions. -/
open Filter SimpleGraph Asymptotics Finset
namespace Erdos713Suspension
open Erdos713ConeFan
set_option maxHeartbeats 2000000

lemma localCount_tree {W V : Type*} [Fintype W] [Fintype V] (H : SimpleGraph W)
    (c : H.Coloring Bool) (hH : H.IsTree) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hBip : G.IsBipartite) (hfree : (graph H c).Free G) (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) {u v : V} (huv : G.Adj u v) :
    localCount G u v ≤ (4 * Fintype.card W + 2)*D := by
  classical
  have hf := local_free H c hH.isConnected G hBip hfree huv
  have he := Erdos713Forest.free_tree_edge_bound H hH (G.induce (localSet G u v)) hf
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at he
  have hc := local_card_le G u v
  have hL := localCount_le G u v
  have hc' : Nat.card (localSet G u v) ≤ 2*D := by linarith [hD u,hD v]
  have he' : Nat.card ((G.induce (localSet G u v)).edgeSet) ≤ Fintype.card W * (2*D) := by
    simpa only [Fintype.card_eq_nat_card] using he.trans (Nat.mul_le_mul_left _ hc')
  nlinarith [hD u,hD v]

lemma almost_regular_tree {W V : Type*} [Fintype W] [Fintype V] (H : SimpleGraph W)
    (c : H.Coloring Bool) (hH : H.IsTree) (G : SimpleGraph V)
    (hBip : G.IsBipartite) (hfree : (graph H c).Free G) (hn : 0 < Fintype.card V)
    {R d : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hdeg : ∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
      (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) :
    d^2 ≤ (4*(Fintype.card W : ℝ)+2)*R^2*Fintype.card V := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp hn
  have hdeg' (v) : d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ R*d := by
    simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hdeg v
  have hmax : (G.maxDegree : ℝ) ≤ R*d := by
    obtain ⟨v,hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    exact (hdeg' v).2
  have hlow := closed4_lower G hn hd.le (fun v => (hdeg' v).1)
  have hhigh := closed4_upper G G.maxDegree G.degree_le_maxDegree
    ((4*(Fintype.card W : ℝ)+2)*G.maxDegree) (by positivity) (fun u v huv => by
      exact_mod_cast localCount_tree H c hH G hBip hfree G.maxDegree G.degree_le_maxDegree huv)
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp
  calc
    d^2*d^2 = d^4 := by ring
    _ ≤ (Fintype.card V : ℝ)*G.maxDegree*((4*(Fintype.card W : ℝ)+2)*G.maxDegree) :=
      hlow.trans hhigh
    _ = (4*(Fintype.card W : ℝ)+2)*Fintype.card V*(G.maxDegree : ℝ)^2 := by ring
    _ ≤ (4*(Fintype.card W : ℝ)+2)*Fintype.card V*(R*d)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hmax 2) (by positivity)
    _ = ((4*(Fintype.card W : ℝ)+2)*R^2*Fintype.card V)*d^2 := by ring

private lemma cube_double_sum (a b : ℕ) : (2*a+2*b)^3 ≤ 32*(a^3+b^3) := by
  have h : (2*(a : ℝ)+2*(b : ℝ))^3 ≤ 32*((a : ℝ)^3+(b : ℝ)^3) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (a : ℝ)+b by positivity) (sq_nonneg ((a : ℝ)-b))]
  exact_mod_cast h

lemma localCount_cube {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (c : H.Coloring Bool) (hH : H.Connected) (C : ℕ)
    (hUpper : ∀ n, extremalNumber n H ^ 3 ≤ C*n^4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hBip : G.IsBipartite)
    (hfree : (graph H c).Free G) (D : ℕ) (hDpos : 0 < D)
    (hD : ∀ v, G.degree v ≤ D) {u v : V} (huv : G.Adj u v) :
    localCount G u v ^ 3 ≤ (512*C+32)*D^4 := by
  classical
  have hf := local_free H c hH G hBip hfree huv
  have he := card_edgeFinset_le_extremalNumber hf
  have he3 := (Nat.pow_le_pow_left he 3).trans (hUpper (Fintype.card (localSet G u v)))
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at he3
  have hc := local_card_le G u v
  have hc' : Nat.card (localSet G u v) ≤ 2*D := by linarith [hD u,hD v]
  have he' : Nat.card ((G.induce (localSet G u v)).edgeSet)^3 ≤ C*(2*D)^4 :=
    he3.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hc' 4))
  have hL := localCount_le G u v
  have hL' : localCount G u v ≤ 2*Nat.card ((G.induce (localSet G u v)).edgeSet)+2*D := by
    linarith [hD u,hD v]
  have hD34 : D^3 ≤ D^4 := Nat.pow_le_pow_right hDpos (by decide)
  calc
    _ ≤ (2*Nat.card ((G.induce (localSet G u v)).edgeSet)+2*D)^3 := Nat.pow_le_pow_left hL' 3
    _ ≤ 32*(Nat.card ((G.induce (localSet G u v)).edgeSet)^3+D^3) := cube_double_sum _ _
    _ ≤ 32*(C*(2*D)^4+D^4) := Nat.mul_le_mul_left 32 (Nat.add_le_add he' hD34)
    _ = _ := by ring

lemma almost_regular_cube {W V : Type*} [Fintype V] (H : SimpleGraph W)
    (c : H.Coloring Bool) (hH : H.Connected) (C : ℕ)
    (hUpper : ∀ n, extremalNumber n H ^ 3 ≤ C*n^4)
    (G : SimpleGraph V) (hBip : G.IsBipartite) (hfree : (graph H c).Free G)
    (hn : 0 < Fintype.card V) {R d : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hdeg : ∀ v, d ≤ (Nat.card (G.neighborSet v) : ℝ) ∧
      (Nat.card (G.neighborSet v) : ℝ) ≤ R*d) :
    d^5 ≤ (512*(C : ℝ)+32)*R^7*(Fintype.card V : ℝ)^3 := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp hn
  have hdeg' (v) : d ≤ (G.degree v : ℝ) ∧ (G.degree v : ℝ) ≤ R*d := by
    simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hdeg v
  have hmax : (G.maxDegree : ℝ) ≤ R*d := by
    obtain ⟨v,hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    exact (hdeg' v).2
  have hmaxpos : 0 < G.maxDegree := by
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    have h1 : 0 < (G.degree v : ℝ) := hd.trans_le (hdeg' v).1
    exact (by exact_mod_cast h1 : 0 < G.degree v).trans_le (G.degree_le_maxDegree v)
  let f : V × V → ℕ := fun p => if G.Adj p.1 p.2 then localCount G p.1 p.2 else 0
  obtain ⟨p,_,hp⟩ := exists_max_image (univ : Finset (V × V)) f univ_nonempty
  have hM : (f p : ℝ)^3 ≤ (512*(C : ℝ)+32)*(G.maxDegree : ℝ)^4 := by
    by_cases ha : G.Adj p.1 p.2
    · dsimp only [f]
      rw [if_pos ha]
      exact_mod_cast localCount_cube H c hH C hUpper G hBip hfree G.maxDegree hmaxpos
        G.degree_le_maxDegree ha
    · simp [f,ha]; positivity
  have hlocal (u v) (huv : G.Adj u v) : (localCount G u v : ℝ) ≤ f p := by
    have hh := hp (u,v) (mem_univ _)
    simpa only [f,if_pos huv] using (Nat.cast_le.mpr hh : (f (u,v) : ℝ) ≤ f p)
  have hhigh := closed4_upper G G.maxDegree G.degree_le_maxDegree (f p) (Nat.cast_nonneg _) hlocal
  have hlow := closed4_lower G hn hd.le (fun v => (hdeg' v).1)
  apply (mul_le_mul_iff_left₀ (pow_pos hd 7)).mp
  calc
    d^5*d^7 = (d^4)^3 := by ring
    _ ≤ ((Fintype.card V : ℝ)*G.maxDegree*(f p : ℝ))^3 :=
      pow_le_pow_left₀ (by positivity) (hlow.trans hhigh) 3
    _ = (Fintype.card V : ℝ)^3*(G.maxDegree : ℝ)^3*(f p : ℝ)^3 := by ring
    _ ≤ (Fintype.card V : ℝ)^3*(G.maxDegree : ℝ)^3*((512*(C : ℝ)+32)*(G.maxDegree : ℝ)^4) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ = (512*(C : ℝ)+32)*(Fintype.card V : ℝ)^3*(G.maxDegree : ℝ)^7 := by ring
    _ ≤ (512*(C : ℝ)+32)*(Fintype.card V : ℝ)^3*(R*d)^7 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hmax 7) (by positivity)
    _ = ((512*(C : ℝ)+32)*R^7*(Fintype.card V : ℝ)^3)*d^7 := by ring

end Erdos713Suspension
