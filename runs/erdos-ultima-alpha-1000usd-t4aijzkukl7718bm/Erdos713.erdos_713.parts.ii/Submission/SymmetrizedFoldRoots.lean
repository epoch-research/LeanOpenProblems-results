import FormalConjecturesUtil
import Submission.CompactCloneSymmAudit

/-! Positive vertex density for one fixed bipartite identification, on
symmetrized joint extremal witnesses. No extremal rate passes to the quotient. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713SymmRoots
open Erdos713Cloning Erdos713BipExtremal Erdos713FixedFold Erdos713CloneSymm
open Erdos713SwitchGluing

lemma power_increment_average {x r : ℝ} (hx : 1 ≤ x) (hr : 1 < r) :
    x^(r-1) ≤ x^r-(x-1)^r := by
  have h0 : 0 ≤ x-1 := by linarith
  have hh := Real.rpow_le_rpow h0 (show x-1 ≤ x by linarith) (by linarith : 0 ≤ r-1)
  have hm := mul_le_mul_of_nonneg_left hh h0
  rw [rpow_factor (by linarith : 0 ≤ x) hr,rpow_factor h0 hr]
  nlinarith

lemma joint_min_average {W : Type*} {H : SimpleGraph W} {r s : ℝ} {n : ℕ}
    {G : SimpleGraph (Fin n)} (hJ : Joint H r s n G) (hr : 1 < r) (v : Fin n) :
    (Nat.card G.edgeSet : ℝ)/(n : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
  obtain ⟨hn,hf,hb,he,hhalf,C,hC,hEq,hUpper,hDeg,hCut,hInc⟩ := hJ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpred : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by rw [Nat.cast_sub hn,Nat.cast_one]
  have hlow := mul_le_mul_of_nonneg_left (power_increment_average hn1 hr) hC.le
  have hd := hDeg v
  rw [hpred] at hd
  calc
    _ = C*(n : ℝ)^(r-1) := by rw [hEq,rpow_factor hnR.le hr]; field_simp
    _ ≤ C*((n : ℝ)^r-((n : ℝ)-1)^r) := hlow
    _ ≤ _ := hd

lemma transport_joint {W : Type*} {H : SimpleGraph W} {r s : ℝ} {n : ℕ}
    {G K : SimpleGraph (Fin n)} (hJ : Joint H r s n G) (hr : 1 < r)
    (hf : H.Free K) (hb : K.IsBipartite) (he : Nat.card K.edgeSet = number n H) :
    Joint H r s n K := by
  obtain ⟨hn,hfG,hbG,heG,hhalf,C,hC,hEq,hUpper,hDeg,hCut,hInc⟩ := hJ
  have hEqK : (Nat.card K.edgeSet : ℝ) = C*(n : ℝ)^r := by rwa [heG,←he] at hEq
  refine ⟨hn,hf,hb,he,by simpa only [he] using ordinary_le_two H n,C,hC,hEqK,hUpper,
    Erdos713BipExtremal.degree_lower_of_record H K hf hb he hEqK hUpper,?_,hInc⟩
  intro S hS
  simpa only [Fintype.card_fin] using Erdos713BipExtremal.record_cut_bound H K hf hb hr hC.le
    (by simpa only [Fintype.card_fin] using hEqK)
    (by simpa only [Fintype.card_fin] using hUpper) S (by simpa only [Fintype.card_fin] using hS)

lemma optimal_joint {W : Type*} [Fintype W] (H : SimpleGraph W) (hHB : H.IsBipartite)
    {α c r s : ℝ} (hr : 1 < r) (hra : r < α) (has : α < s) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (N D : ℕ) :
    ∃ n, N ≤ n ∧ ∃ G : SimpleGraph (Fin n), Joint H r s n G ∧ Optimal H G ∧
      (∀ v, max D (Fintype.card W) ≤ Nat.card (G.neighborSet v)) ∧
      ∃ B : Finset (Fin n), (∀ v ∈ B, SingleFold H G v) ∧ n ≤ B.card+(Fintype.card W)^2 := by
  classical
  have hlim : Tendsto (fun n : ℕ => (number n H : ℝ)/(n : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using lower_ratio_top H (hr.trans hra) hc h
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hlim.eventually_ge_atTop (max D (Fintype.card W) : ℕ))
  obtain ⟨n,hn,hnp,C,hC,G₀,hfree,hB,he,hhalf,hEq,hUpper,hDeg,hCut,hinc,hFold⟩ :=
    joint_with_increment H hr hra has hc h (max N L)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
  have hpos : 0 < number n H := by
    have hp : (0 : ℝ) < Nat.card G₀.edgeSet := by rw [hEq]; positivity
    rw [he] at hp
    exact_mod_cast hp
  obtain ⟨G,hOpt,hE⟩ := exists_optimal hpos
  have hJ₀ : Joint H r s n G₀ := ⟨hnp,hfree,hB,he,hhalf,C,hC,hEq,hUpper,hDeg,hCut,hinc⟩
  have hJ := transport_joint hJ₀ hr hOpt.free hOpt.bipartite hE
  have hMin (v : Fin n) : max D (Fintype.card W) ≤ Nat.card (G.neighborSet v) := by
    have hh := joint_min_average hJ hr v
    rw [hE] at hh
    exact_mod_cast (hL n ((le_max_right N L).trans hn)).trans hh
  let T : Finset (Fin n) := univ.filter (fun v => H.Free (clone G v))
  have hT : T.card ≤ (Fintype.card W)^2 :=
    hOpt.cloneOptimal.safe_card_of_min_degree hHB hOpt.free (fun v => (le_max_right _ _).trans (hMin v))
  refine ⟨n,(le_max_left N L).trans hn,G,hJ,hOpt,hMin,Tᶜ,?_,?_⟩
  · intro v hv
    have hv' : ¬ H.Free (clone G v) := by simpa [T] using hv
    by_contra hfold
    exact hv' (fun hc => hfold (fold_of_obstructed H G v hOpt.free hc))
  · simp only [card_compl,card_univ,Fintype.card_fin]
    have ht := card_le_univ T
    simp only [Fintype.card_fin] at ht
    omega

/-- One fixed-pair witness with a positive proportion of root vertices,
and with the degree mass forced by the SAME past record. -/
def VertexAt {W : Type*} [Fintype W] (H : SimpleGraph W) (p : W × W)
    (r s : ℝ) (D n : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n), Joint H r s n G ∧ Optimal H G ∧
    (∀ v, D ≤ Nat.card (G.neighborSet v)) ∧
    ∃ F : Finset (Fin n), F.Nonempty ∧ (∀ v ∈ F, AtPair H G p v) ∧
      n ≤ 2*(Fintype.card W)^2*F.card ∧
      (Nat.card G.edgeSet : ℝ) ≤ 2*(Fintype.card W : ℝ)^2 * ∑ v ∈ F, (Nat.card (G.neighborSet v) : ℝ)

lemma vertex_witness {W : Type*} [Fintype W] (H : SimpleGraph W) (hHB : H.IsBipartite)
    {α c r s : ℝ} (hr : 1 < r) (hra : r < α) (has : α < s) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (N D : ℕ) :
    ∃ p : W × W, ∃ n, N ≤ n ∧ VertexAt H p r s D n := by
  obtain ⟨n,hn,G,hJ,hOpt,hMin,B,hFold,hBcard⟩ :=
    optimal_joint H hHB hr hra has hc h (max N (2*(Fintype.card W)^2+1)) D
  have hnp : 0 < n := hJ.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
  have hhalf : (n : ℝ)/2 ≤ ∑ _v ∈ B, (1 : ℝ) := by
    have hcB : n ≤ 2*B.card := by omega
    have hcBR : (n : ℝ) ≤ 2*(B.card : ℝ) := by exact_mod_cast hcB
    simp only [sum_const,nsmul_eq_mul,mul_one]
    linarith
  obtain ⟨p,F,hFB,hFne,hF,hCount⟩ := weighted_pair H G B hFold (fun _ => (1 : ℝ)) (by positivity) hhalf
  have hCountR : (n : ℝ) ≤ 2*(Fintype.card W : ℝ)^2*(F.card : ℝ) := by
    simp only [sum_const,nsmul_eq_mul,mul_one] at hCount
    linarith
  have hCountN : n ≤ 2*(Fintype.card W)^2*F.card := by exact_mod_cast hCountR
  have hmass : (Nat.card G.edgeSet : ℝ) ≤
      2*(Fintype.card W : ℝ)^2 * ∑ v ∈ F, (Nat.card (G.neighborSet v) : ℝ) := by
    have hlocal := sum_le_sum (fun v (_ : v ∈ F) => joint_min_average hJ hr v)
    simp only [sum_const,nsmul_eq_mul] at hlocal
    have hweighted := mul_le_mul_of_nonneg_right hCountR
      (div_nonneg (Nat.cast_nonneg (Nat.card G.edgeSet)) hnR.le)
    have hcancel : (n : ℝ)*((Nat.card G.edgeSet : ℝ)/(n : ℝ)) = (Nat.card G.edgeSet : ℝ) := by
      field_simp
    rw [hcancel] at hweighted
    have hmult := mul_le_mul_of_nonneg_left hlocal (show 0 ≤ 2*(Fintype.card W : ℝ)^2 by positivity)
    nlinarith
  exact ⟨p,n,(le_max_left _ _).trans hn,G,hJ,hOpt,
    fun v => (le_max_left _ _).trans (hMin v),F,hFne,hF,hCountN,hmass⟩

def NearVertex {W : Type*} [Fintype W] (H : SimpleGraph W) (p : W × W)
    (α ε : ℝ) (D n : ℕ) : Prop :=
  ∃ r s : ℝ, 1 < r ∧ r < α ∧ α-ε < r ∧ α < s ∧ s < 2 ∧ s < α+ε ∧ VertexAt H p r s D n

lemma NearVertex.mono {W : Type*} [Fintype W] {H : SimpleGraph W} {p : W × W}
    {α ε δ : ℝ} {D E n : ℕ} (h : NearVertex H p α ε D n) (hεδ : ε ≤ δ) (hED : E ≤ D) :
    NearVertex H p α δ E n := by
  obtain ⟨r,s,hr,hra,hεr,has,hs,hsε,G,hJ,hOpt,hDeg,F,hFne,hF,hCount,hMass⟩ := h
  exact ⟨r,s,hr,hra,by linarith,has,hs,by linarith,G,hJ,hOpt,
    fun v => hED.trans (hDeg v),F,hFne,hF,hCount,hMass⟩

lemma near_vertex_witness {W : Type*} [Fintype W] (H : SimpleGraph W) (hHB : H.IsBipartite)
    {α c ε : ℝ} (hα : 1 < α) (hα2 : α < 2) (hc : 0 < c) (hε : 0 < ε)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (N D : ℕ) :
    ∃ p : W × W, ∃ n, N ≤ n ∧ NearVertex H p α ε D n := by
  obtain ⟨r,hr,hra⟩ := exists_between (show max 1 (α-ε) < α by
    exact max_lt hα (by linarith))
  obtain ⟨s,has,hs⟩ := exists_between (show α < min 2 (α+ε) by
    exact lt_min hα2 (by linarith))
  have hr1 : 1 < r := (le_max_left _ _).trans_lt hr
  have hrε : α-ε < r := (le_max_right _ _).trans_lt hr
  have hs2 : s < 2 := hs.trans_le (min_le_left _ _)
  have hsε : s < α+ε := hs.trans_le (min_le_right _ _)
  obtain ⟨p,n,hn,hV⟩ := vertex_witness H hHB hr1 hra has hc h N D
  exact ⟨p,n,hn,r,s,hr1,hra,hrε,has,hs2,hsε,hV⟩

/-- The pair is fixed independently of exponent tolerance, minimum degree,
and size threshold. Vertex density and degree mass are on the SAME host. -/
theorem uniform_pair_vertices {W : Type*} [Fintype W] (H : SimpleGraph W) (hHB : H.IsBipartite)
    {α c : ℝ} (hα : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ p : W × W, ∀ ε : ℝ, 0 < ε → ∀ N D : ℕ, ∃ n, N ≤ n ∧ NearVertex H p α ε D n := by
  let P (p : W × W) (k : ℕ) : Prop := ∃ n, k ≤ n ∧ NearVertex H p α (1/(k+1)) k n
  have hP : ∀ N, ∃ p k, N ≤ k ∧ P p k := by
    intro N
    obtain ⟨p,n,hn,hV⟩ := near_vertex_witness H hHB hα hα2 hc
      (show (0 : ℝ) < 1/(N+1) by positivity) h N N
    exact ⟨p,N,le_rfl,n,hn,hV⟩
  obtain ⟨p,hp⟩ := finite_cofinal hP
  refine ⟨p,?_⟩
  intro ε hε N D
  obtain ⟨K,hK⟩ := exists_nat_one_div_lt hε
  obtain ⟨k,hk,n,hkn,hV⟩ := hp (max N (max K D))
  have hNk : N ≤ k := (le_max_left _ _).trans hk
  have hKk : K ≤ k := (le_max_left K D).trans ((le_max_right _ _).trans hk)
  have hDk : D ≤ k := (le_max_right K D).trans ((le_max_right _ _).trans hk)
  have hεk : (1 : ℝ)/(k+1) < ε := by
    apply (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < K+1) ?_).trans_lt hK
    exact_mod_cast Nat.add_le_add_right hKk 1
  exact ⟨n,hNk.trans hkn,hV.mono hεk.le hDk⟩

/-- A single smaller bipartite quotient occurs at at least n/(2*|H|^2)
distinct roots, on the same secondary-optimal joint hosts. Copies can overlap.
Neither a power rate nor an exact asymptotic for the quotient is asserted. -/
theorem uniform_identification_vertices {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hHB : H.IsBipartite) {α c : ℝ} (hα : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ a b : W, ∃ hab : a ≠ b, ∃ hnab : ¬ H.Adj a b,
      (identified H a b hnab).IsBipartite ∧
      Nat.card {w : W // w ≠ a}+1 = Nat.card W ∧
      ∀ ε : ℝ, 0 < ε → ∀ N D : ℕ, ∃ n, N ≤ n ∧ ∃ r s : ℝ,
        1 < r ∧ r < α ∧ α-ε < r ∧ α < s ∧ s < 2 ∧ s < α+ε ∧
        ∃ G : SimpleGraph (Fin n), Joint H r s n G ∧ Optimal H G ∧
          (∀ v, D ≤ Nat.card (G.neighborSet v)) ∧
          ∃ F : Finset (Fin n), F.Nonempty ∧
            (∀ v ∈ F, ∃ f : (identified H a b hnab).Copy G, f ⟨b,hab.symm⟩ = v) ∧
            n ≤ 2*(Fintype.card W)^2*F.card ∧
            (Nat.card G.edgeSet : ℝ) ≤
              2*(Fintype.card W : ℝ)^2 * ∑ v ∈ F, (Nat.card (G.neighborSet v) : ℝ) := by
  obtain ⟨p,hp⟩ := uniform_pair_vertices H hHB hα hα2 hc h
  obtain ⟨n,hn,r,s,hr,hra,hεr,has,hs,hsε,G,hJ,hOpt,hDeg,F,hFne,hF,hCount,hMass⟩ := hp 1 (by norm_num) 0 0
  obtain ⟨v,hv⟩ := hFne
  obtain ⟨hab,hnab,f,hf⟩ := hF v hv
  refine ⟨p.1,p.2,hab,hnab,hJ.2.2.1.of_hom f.toHom,card_identified_vertices p.1,?_⟩
  intro ε hε N D
  obtain ⟨n,hn,r,s,hr,hra,hεr,has,hs,hsε,G,hJ,hOpt,hDeg,F,hFne,hF,hCount,hMass⟩ := hp ε hε N D
  refine ⟨n,hn,r,s,hr,hra,hεr,has,hs,hsε,G,hJ,hOpt,hDeg,F,hFne,?_,hCount,hMass⟩
  intro v hv
  obtain ⟨hab',hnab',f,hf⟩ := hF v hv
  exact ⟨f,hf⟩

#print axioms joint_min_average
#print axioms optimal_joint
#print axioms vertex_witness
#print axioms uniform_pair_vertices
#print axioms uniform_identification_vertices
end Erdos713SymmRoots
