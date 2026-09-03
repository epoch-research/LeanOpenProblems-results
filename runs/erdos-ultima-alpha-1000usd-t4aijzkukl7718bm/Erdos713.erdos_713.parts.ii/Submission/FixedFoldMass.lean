import FormalConjecturesUtil
import Submission.CompactEdgeAttachmentsAudit

/-! A single smaller bipartite quotient carries quantitative cloning mass
cofinally. This does not transfer an extremal rate to that quotient. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713FixedFold
open Erdos713Cloning Erdos713BipExtremal Erdos713SwitchGluing
set_option maxHeartbeats 2000000

/-- A copy of the quotient by this specified ordered pair, with the merged
vertex at the specified host root. -/
def AtPair {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V)
    (p : W × W) (v : V) : Prop :=
  ∃ hab : p.1 ≠ p.2, ∃ hnab : ¬ H.Adj p.1 p.2,
    ∃ f : (identified H p.1 p.2 hnab).Copy G, f ⟨p.2,hab.symm⟩ = v

lemma exists_pair_of_fold {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    {v : V} (h : SingleFold H G v) : ∃ p, AtPair H G p v := by
  obtain ⟨a,b,hab,hnab,f,hf⟩ := h.identified_copy
  exact ⟨(a,b),hab,hnab,f,hf⟩

/-- Finite weighted pigeonholing, without asserting that the chosen roots
are a positive proportion of all host vertices. -/
lemma weighted_pair {W V : Type*} [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (B : Finset V) (hB : ∀ v ∈ B, SingleFold H G v) (w : V → ℝ)
    {L : ℝ} (hL : 0 < L) (hMass : L ≤ ∑ v ∈ B, w v) :
    ∃ p : W × W, ∃ F : Finset V, F ⊆ B ∧ F.Nonempty ∧
      (∀ v ∈ F, AtPair H G p v) ∧
      L ≤ (Fintype.card W : ℝ)^2 * ∑ v ∈ F, w v := by
  classical
  have hBne : B.Nonempty := by
    by_contra he
    simp only [not_nonempty_iff_eq_empty.mp he,sum_empty] at hMass
    linarith
  obtain ⟨v,hv⟩ := hBne
  obtain ⟨p₀,hp₀⟩ := exists_pair_of_fold (hB v hv)
  haveI : Nonempty (W × W) := ⟨p₀⟩
  have he : ∀ v ∈ B, ∃ p : W × W, AtPair H G p v :=
    fun v hv => exists_pair_of_fold (hB v hv)
  choose p hp using he
  let label : V → W × W := fun v => if hv : v ∈ B then p v hv else p₀
  let M : W × W → ℝ := fun i => ∑ v ∈ B.filter (fun v => label v = i), w v
  obtain ⟨i,hi,hmax⟩ := (univ : Finset (W × W)).exists_max_image M univ_nonempty
  have hsum : (∑ v ∈ B, w v) = ∑ i : W × W, M i := by
    symm
    exact sum_fiberwise_of_maps_to (g := label) (t := univ) (fun _ _ => mem_univ _) w
  have hle : (∑ i : W × W, M i) ≤ (Fintype.card W : ℝ)^2*M i := by
    calc
      _ ≤ ∑ _j : W × W, M i := sum_le_sum (fun j hj => hmax j hj)
      _ = _ := by simp [pow_two]
  let F := B.filter (fun v => label v = i)
  have hbound : L ≤ (Fintype.card W : ℝ)^2 * ∑ v ∈ F, w v := hMass.trans (hsum.le.trans hle)
  refine ⟨i,F,filter_subset _ _,?_,?_,hbound⟩
  · by_contra he
    simp only [not_nonempty_iff_eq_empty.mp he,sum_empty,mul_zero] at hbound
    linarith
  · intro v hv
    have hvB := (mem_filter.mp hv).1
    have hvi : p v hvB = i := by simpa only [label,dif_pos hvB] using (mem_filter.mp hv).2
    exact hvi ▸ hp v hvB

/-- Geometry and forward-increment control on one bipartite-class extremal
host. The exact ordinary leading constant is not asserted for this host. -/
def Joint {W : Type*} (H : SimpleGraph W) (r s : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  0 < n ∧ H.Free G ∧ G.IsBipartite ∧ Nat.card G.edgeSet = number n H ∧
    extremalNumber n H ≤ 2*Nat.card G.edgeSet ∧
    ∃ C : ℝ, 0 < C ∧ (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r ∧
      (∀ j : ℕ, j ≤ n → (number j H : ℝ) ≤ C*(j : ℝ)^r) ∧
      (∀ v, C*((n : ℝ)^r-((n-1 : ℕ) : ℝ)^r) ≤ (Nat.card (G.neighborSet v) : ℝ)) ∧
      (∀ S : Finset (Fin n), 2*S.card ≤ n →
        expansionConstant r*C*S.card*(n : ℝ)^(r-1) ≤
          (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ)) ∧
      (n : ℝ)*((number (n+1) H : ℝ)-(number n H : ℝ)) ≤ s*(number n H : ℝ)

lemma mass_witness {W : Type*} [Fintype W] (H : SimpleGraph W) {α c r s : ℝ}
    (hr : 1 < r) (hra : r < α) (has : α < s) (hs : s < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ p : W × W, ∃ n, N ≤ n ∧ ∃ G : SimpleGraph (Fin n), Joint H r s n G ∧
      ∃ F : Finset (Fin n), F.Nonempty ∧ (∀ v ∈ F, AtPair H G p v) ∧
        (2-s)*(Nat.card G.edgeSet : ℝ) ≤
          (Fintype.card W : ℝ)^2 * ∑ v ∈ F, (Nat.card (G.neighborSet v) : ℝ) := by
  obtain ⟨n,hn,hnp,C,hC,G,hfree,hB,he,hhalf,hEq,hUpper,hDeg,hCut,hinc,B,hFold,hmass⟩ :=
    joint_with_increment H hr hra has hc h N
  have hE : (0 : ℝ) < Nat.card G.edgeSet := by
    rw [hEq]
    exact mul_pos hC (Real.rpow_pos_of_pos (by exact_mod_cast hnp) r)
  obtain ⟨p,F,hFB,hFne,hF,hMF⟩ := weighted_pair H G B hFold
    (fun v => (Nat.card (G.neighborSet v) : ℝ)) (mul_pos (sub_pos.mpr hs) hE) hmass
  exact ⟨p,n,hn,G,⟨hnp,hfree,hB,he,hhalf,C,hC,hEq,hUpper,hDeg,hCut,hinc⟩,F,hFne,hF,hMF⟩

/-- The SAME ordered pair is fixed before the size threshold. Every retained
root has a quotient-copy whose merged vertex maps there, and these roots
carry a fixed positive fraction of the host's total edge mass. -/
theorem fixed_pair_mass {W : Type*} [Fintype W] (H : SimpleGraph W) {α c r s : ℝ}
    (hr : 1 < r) (hra : r < α) (has : α < s) (hs : s < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ a b : W, ∃ hab : a ≠ b, ∃ hnab : ¬ H.Adj a b,
      (identified H a b hnab).IsBipartite ∧
      ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ G : SimpleGraph (Fin n), Joint H r s n G ∧
        ∃ F : Finset (Fin n), F.Nonempty ∧
          (∀ v ∈ F, ∃ f : (identified H a b hnab).Copy G, f ⟨b,hab.symm⟩ = v) ∧
          (2-s)*(Nat.card G.edgeSet : ℝ) ≤
            (Fintype.card W : ℝ)^2 * ∑ v ∈ F, (Nat.card (G.neighborSet v) : ℝ) := by
  let P (p : W × W) (n : ℕ) : Prop := ∃ G : SimpleGraph (Fin n), Joint H r s n G ∧
    ∃ F : Finset (Fin n), F.Nonempty ∧ (∀ v ∈ F, AtPair H G p v) ∧
      (2-s)*(Nat.card G.edgeSet : ℝ) ≤
        (Fintype.card W : ℝ)^2 * ∑ v ∈ F, (Nat.card (G.neighborSet v) : ℝ)
  obtain ⟨p,hp⟩ := finite_cofinal (P := P) (mass_witness H hr hra has hs hc h)
  obtain ⟨n,_,G,hJoint,F,hFne,hF,hMass⟩ := hp 0
  obtain ⟨v,hv⟩ := hFne
  obtain ⟨hab,hnab,f,hfv⟩ := hF v hv
  refine ⟨p.1,p.2,hab,hnab,hJoint.2.2.1.of_hom f.toHom,?_⟩
  intro N
  obtain ⟨n,hn,G,hJoint,F,hFne,hF,hMass⟩ := hp N
  refine ⟨n,hn,G,hJoint,F,hFne,?_,hMass⟩
  intro v hv
  obtain ⟨hab',hnab',f,hf⟩ := hF v hv
  exact ⟨f,hf⟩

/-- Cardinality control follows from the maximum possible host degree, not
from an unproved almost-regularity condition. -/
lemma degree_mass_le {V : Type*} [Fintype V] (G : SimpleGraph V) (F : Finset V) :
    (∑ v ∈ F, (Nat.card (G.neighborSet v) : ℝ)) ≤ (Fintype.card V : ℝ)*F.card := by
  have hd (v : V) : (Nat.card (G.neighborSet v) : ℝ) ≤ (Fintype.card V : ℝ) := by
    have hh := Nat.card_le_card_of_injective
      (fun z : G.neighborSet v => z.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := V)] at hh
    exact_mod_cast hh
  calc
    _ ≤ ∑ _v ∈ F, (Fintype.card V : ℝ) := sum_le_sum (fun v _ => hd v)
    _ = _ := by simp [mul_comm]

/-- A root-mass witness retains all the joint properties on its SAME host. -/
def MassAt {W : Type*} [Fintype W] (H : SimpleGraph W) (p : W × W)
    (r s : ℝ) (n : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n), Joint H r s n G ∧
    ∃ F : Finset (Fin n), F.Nonempty ∧ (∀ v ∈ F, AtPair H G p v) ∧
      (2-s)*(Nat.card G.edgeSet : ℝ) ≤
        (Fintype.card W : ℝ)^2 * ∑ v ∈ F, (Nat.card (G.neighborSet v) : ℝ)

def NearMass {W : Type*} [Fintype W] (H : SimpleGraph W) (p : W × W)
    (α ε : ℝ) (n : ℕ) : Prop :=
  ∃ r s : ℝ, 1 < r ∧ r < α ∧ α-ε < r ∧ α < s ∧ s < 2 ∧ s < α+ε ∧ MassAt H p r s n

lemma NearMass.mono {W : Type*} [Fintype W] {H : SimpleGraph W} {p : W × W}
    {α ε δ : ℝ} {n : ℕ} (h : NearMass H p α ε n) (hεδ : ε ≤ δ) : NearMass H p α δ n := by
  obtain ⟨r,s,hr,hra,hεr,has,hs,hsε,hM⟩ := h
  exact ⟨r,s,hr,hra,by linarith,has,hs,by linarith,hM⟩

lemma near_mass_witness {W : Type*} [Fintype W] (H : SimpleGraph W) {α c ε : ℝ}
    (hα : 1 < α) (hα2 : α < 2) (hc : 0 < c) (hε : 0 < ε)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ p : W × W, ∃ n, N ≤ n ∧ NearMass H p α ε n := by
  obtain ⟨r,hr,hra⟩ := exists_between (show max 1 (α-ε) < α by
    exact max_lt hα (by linarith))
  obtain ⟨s,has,hs⟩ := exists_between (show α < min 2 (α+ε) by
    exact lt_min hα2 (by linarith))
  have hr1 : 1 < r := (le_max_left _ _).trans_lt hr
  have hrε : α-ε < r := (le_max_right _ _).trans_lt hr
  have hs2 : s < 2 := hs.trans_le (min_le_left _ _)
  have hsε : s < α+ε := hs.trans_le (min_le_right _ _)
  obtain ⟨p,n,hn,hM⟩ := mass_witness H hr1 hra has hs2 hc h N
  exact ⟨p,n,hn,r,s,hr1,hra,hrε,has,hs2,hsε,hM⟩

/-- One ordered identification pair works independently of BOTH the size
threshold and the requested accuracy of the exponents r,s around alpha. -/
theorem uniform_pair_mass {W : Type*} [Fintype W] (H : SimpleGraph W) {α c : ℝ}
    (hα : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ p : W × W, ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧ NearMass H p α ε n := by
  let P (p : W × W) (k : ℕ) : Prop := ∃ n, k ≤ n ∧ NearMass H p α (1/(k+1)) n
  have hP : ∀ N, ∃ p k, N ≤ k ∧ P p k := by
    intro N
    obtain ⟨p,n,hn,hM⟩ := near_mass_witness H hα hα2 hc
      (show (0 : ℝ) < 1/(N+1) by positivity) h N
    exact ⟨p,N,le_rfl,n,hn,hM⟩
  obtain ⟨p,hp⟩ := finite_cofinal hP
  refine ⟨p,?_⟩
  intro ε hε N
  obtain ⟨K,hK⟩ := exists_nat_one_div_lt hε
  obtain ⟨k,hk,n,hkn,hM⟩ := hp (max N K)
  have hKk : (K : ℝ)+1 ≤ (k : ℝ)+1 := by
    exact_mod_cast (Nat.add_le_add_right ((le_max_right N K).trans hk) 1)
  have hεk : (1 : ℝ)/(k+1) < ε :=
    (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < K+1) hKk).trans_lt hK
  exact ⟨n,(le_max_left N K).trans (hk.trans hkn),hM.mono hεk.le⟩

lemma MassAt.identification {W : Type*} [Fintype W] {H : SimpleGraph W} {p : W × W}
    {r s : ℝ} {n : ℕ} (h : MassAt H p r s n) :
    ∃ hab : p.1 ≠ p.2, ∃ hnab : ¬ H.Adj p.1 p.2,
      (identified H p.1 p.2 hnab).IsBipartite := by
  obtain ⟨G,hJ,F,hFne,hF,hMass⟩ := h
  obtain ⟨v,hv⟩ := hFne
  obtain ⟨hab,hnab,f,hf⟩ := hF v hv
  exact ⟨hab,hnab,hJ.2.2.1.of_hom f.toHom⟩

/-- The fixed quotient is bipartite and strictly smaller; the mass and
near-exponent witness statements still assert no rate for that quotient. -/
theorem uniform_identification_mass {W : Type*} [Fintype W] (H : SimpleGraph W) {α c : ℝ}
    (hα : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ a b : W, ∃ hab : a ≠ b, ∃ hnab : ¬ H.Adj a b,
      (identified H a b hnab).IsBipartite ∧
      Nat.card {w : W // w ≠ a}+1 = Nat.card W ∧
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n, N ≤ n ∧ NearMass H (a,b) α ε n := by
  obtain ⟨p,hp⟩ := uniform_pair_mass H hα hα2 hc h
  obtain ⟨n,hn,r,s,hr,hra,hεr,has,hs,hsε,hM⟩ := hp 1 (by norm_num) 0
  obtain ⟨hab,hnab,hB⟩ := hM.identification
  exact ⟨p.1,p.2,hab,hnab,hB,card_identified_vertices p.1,hp⟩

/-- The fixed quotient occurs at arbitrarily many DISTINCT root images in
the same joint witnesses. No disjointness of the full copies is asserted. -/
theorem uniform_identification_many_roots {W : Type*} [Fintype W] (H : SimpleGraph W) {α c : ℝ}
    (hα : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ a b : W, ∃ hab : a ≠ b, ∃ hnab : ¬ H.Adj a b,
      (identified H a b hnab).IsBipartite ∧
      ∀ ε : ℝ, 0 < ε → ∀ N K : ℕ, ∃ n, N ≤ n ∧ ∃ r s : ℝ,
        1 < r ∧ r < α ∧ α-ε < r ∧ α < s ∧ s < 2 ∧ s < α+ε ∧
        ∃ G : SimpleGraph (Fin n), Joint H r s n G ∧
          ∃ F : Finset (Fin n), K < F.card ∧
            (∀ v ∈ F, ∃ f : (identified H a b hnab).Copy G, f ⟨b,hab.symm⟩ = v) ∧
            (2-s)*(Nat.card G.edgeSet : ℝ) ≤
              (Fintype.card W : ℝ)^2 * ∑ v ∈ F, (Nat.card (G.neighborSet v) : ℝ) := by
  obtain ⟨a,b,hab,hnab,hB,hcard,hp⟩ := uniform_identification_mass H hα hα2 hc h
  refine ⟨a,b,hab,hnab,hB,?_⟩
  intro ε hε N K
  let δ : ℝ := (2-α)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hlim : Tendsto (fun n : ℕ => (number n H : ℝ)/(n : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using lower_ratio_top H hα hc h
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hlim.eventually_gt_atTop
    ((Fintype.card W : ℝ)^2*K/δ))
  obtain ⟨n,hn,r,s,hr,hra,hεr,has,hs,hsε,G,hJ,F,hFne,hF,hMass⟩ :=
    hp (min ε δ) (lt_min hε hδ) (max N L)
  have hδs : δ < 2-s := by
    have hh : s < α+δ := hsε.trans_le (add_le_add le_rfl (min_le_right ε δ))
    dsimp [δ] at hh ⊢
    linarith
  have he : (Nat.card G.edgeSet : ℝ) = (number n H : ℝ) := by exact_mod_cast hJ.2.2.2.1
  have hsmall : δ*(Nat.card G.edgeSet : ℝ) ≤
      (Fintype.card W : ℝ)^2 * ((n : ℝ)*F.card) := by
    calc
      _ ≤ (2-s)*(Nat.card G.edgeSet : ℝ) :=
        mul_le_mul_of_nonneg_right hδs.le (Nat.cast_nonneg _)
      _ ≤ _ := hMass.trans (mul_le_mul_of_nonneg_left
        (by simpa only [Fintype.card_fin] using degree_mass_le G F) (sq_nonneg _))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hJ.1
  have hlarge := hL n ((le_max_right N L).trans hn)
  have hlarge' : (Fintype.card W : ℝ)^2*K*(n : ℝ) < δ*(Nat.card G.edgeSet : ℝ) := by
    rw [he]
    have hh := (lt_div_iff₀ hnR).mp hlarge
    have hm := mul_lt_mul_of_pos_left hh hδ
    have hEq : δ*((Fintype.card W : ℝ)^2*K/δ*(n : ℝ)) =
        (Fintype.card W : ℝ)^2*K*(n : ℝ) := by field_simp
    rwa [hEq] at hm
  have hKF : K < F.card := by
    by_contra hNot
    have hle : (F.card : ℝ) ≤ K := by exact_mod_cast (le_of_not_gt hNot)
    have hh := mul_le_mul_of_nonneg_left hle (mul_nonneg (sq_nonneg (Fintype.card W : ℝ)) hnR.le)
    nlinarith
  refine ⟨n,(le_max_left N L).trans hn,r,s,hr,hra,?_,has,hs,?_,G,hJ,F,hKF,?_,hMass⟩
  · have hh := min_le_left ε δ
    linarith
  · exact hsε.trans_le (add_le_add le_rfl (min_le_left ε δ))
  · intro v hv
    obtain ⟨hab',hnab',f,hf⟩ := hF v hv
    exact ⟨f,hf⟩

#print axioms weighted_pair
#print axioms fixed_pair_mass
#print axioms uniform_pair_mass
#print axioms uniform_identification_mass
#print axioms uniform_identification_many_roots
end Erdos713FixedFold
