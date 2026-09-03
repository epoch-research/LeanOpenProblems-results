import FormalConjecturesUtil
import Submission.CompactEdgeAtomsAudit
import Submission.PowerSummation

/-! Summed cloning obstructions. These estimates do not differentiate the
extremal-number asymptotic or transfer an exponent to a quotient. -/
open SimpleGraph Filter Asymptotics Finset
open scoped Topology
namespace Erdos713CloneAverage
open Erdos713Cloning Erdos713PartialCloning Erdos713Rate

noncomputable def mass {W V : Type*} [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) : ℝ := by
  classical
  exact ∑ v : V, if SingleFold H G v then (Nat.card (G.neighborSet v) : ℝ) else 0

lemma mass_nonneg {W V : Type*} [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) :
    0 ≤ mass H G := by
  classical
  unfold mass
  exact sum_nonneg (fun v _ => by split_ifs <;> positivity)

lemma mass_le {W V : Type*} [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) :
    mass H G ≤ 2*(Nat.card G.edgeSet : ℝ) := by
  classical
  have hh := G.sum_degrees_eq_twice_card_edges
  simp only [← card_neighborSet_eq_degree,edgeFinset_card,Fintype.card_eq_nat_card] at hh
  have hh' : (∑ v : V, (Nat.card (G.neighborSet v) : ℝ)) = 2*(Nat.card G.edgeSet : ℝ) := by
    exact_mod_cast hh
  rw [← hh']
  unfold mass
  apply sum_le_sum
  intro v hv
  split_ifs <;> first | exact le_rfl | positivity

lemma empty_partial_free {W V : Type*} [Nonempty V] (H : SimpleGraph W)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) (G : SimpleGraph V) (hFree : H.Free G) :
    H.Free (partialClone G ∅) := by
  classical
  intro hCopy
  obtain ⟨a,b,hab,hnab,f,ha,hb,hfiber,hSupport⟩ :=
    supported_of_copy H G (Classical.arbitrary V) ∅ (by simp) hFree hCopy
  obtain ⟨w,hw⟩ := hNoIso a
  exact notMem_empty _ (hSupport w hw)

lemma extremal_step {W : Type*} (H : SimpleGraph W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    {n : ℕ} (G : SimpleGraph (Fin n)) (hFree : H.Free G)
    (he : Nat.card G.edgeSet = extremalNumber n H) :
    extremalNumber n H ≤ extremalNumber (n+1) H := by
  classical
  cases n with
  | zero =>
    have hG : G = ⊥ := Subsingleton.elim _ _
    have hz : extremalNumber 0 H = 0 := by simpa [hG] using he.symm
    rw [hz]
    exact Nat.zero_le _
  | succ n =>
    have hb := card_edgeFinset_le_extremalNumber (empty_partial_free H hNoIso G hFree)
    have hh : Nat.card (partialClone G ∅).edgeSet ≤ extremalNumber (n+1+1) H := by
      simpa only [edgeFinset_card,Nat.card_eq_fintype_card,Fintype.card_option,Fintype.card_fin] using hb
    simpa only [card_edges,card_empty,add_zero,he] using hh

/-- Pointwise deficit inequality, valid for every exactly extremal host.
No upper estimate on an individual increment is assumed. -/
lemma mass_deficit {W : Type*} (H : SimpleGraph W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    {n : ℕ} (G : SimpleGraph (Fin n)) (hFree : H.Free G)
    (he : Nat.card G.edgeSet = extremalNumber n H) :
    2*(extremalNumber n H : ℝ) - (n : ℝ)*
      ((extremalNumber (n+1) H : ℝ)-(extremalNumber n H : ℝ)) ≤ mass H G := by
  classical
  let D : ℝ := (extremalNumber (n+1) H : ℝ)-(extremalNumber n H : ℝ)
  have hD : 0 ≤ D := sub_nonneg.mpr (by exact_mod_cast extremal_step H hNoIso G hFree he)
  have hlocal (v : Fin n) : (Nat.card (G.neighborSet v) : ℝ) ≤
      (if SingleFold H G v then (Nat.card (G.neighborSet v) : ℝ) else 0)+D := by
    by_cases hv : SingleFold H G v
    · simp only [if_pos hv]
      linarith
    · have hc : H.Free (clone G v) := fun hh => hv (fold_of_obstructed H G v hFree hh)
      have hh := safe_clone_bound H G v hc
      simp only [Fintype.card_fin] at hh
      have hh' : (Nat.card G.edgeSet : ℝ)+(Nat.card (G.neighborSet v) : ℝ) ≤
          (extremalNumber (n+1) H : ℝ) := by exact_mod_cast hh
      rw [he] at hh'
      simp only [if_neg hv,zero_add]
      change (Nat.card (G.neighborSet v) : ℝ) ≤
        (extremalNumber (n+1) H : ℝ)-(extremalNumber n H : ℝ)
      linarith
  have hs := sum_le_sum (fun v (_ : v ∈ (univ : Finset (Fin n))) => hlocal v)
  rw [sum_add_distrib] at hs
  have hd := G.sum_degrees_eq_twice_card_edges
  simp only [← card_neighborSet_eq_degree,edgeFinset_card,Fintype.card_eq_nat_card] at hd
  have hd' : (∑ v : Fin n, (Nat.card (G.neighborSet v) : ℝ)) =
      2*(extremalNumber n H : ℝ) := by rw [← he]; exact_mod_cast hd
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,hd'] at hs
  change 2*(extremalNumber n H : ℝ) ≤ mass H G+(n : ℝ)*D at hs
  dsimp only [D] at hs
  linarith

def deficit (f : ℕ → ℝ) (n : ℕ) : ℝ := 2*f n-(n : ℝ)*(f (n+1)-f n)

lemma sum_deficit (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, deficit f n =
      3*(∑ n ∈ range N, f n)-((N : ℝ)-1)*f N-f 0 := by
  induction N with
  | zero => simp [deficit]
  | succ N ih =>
    rw [sum_range_succ,ih,sum_range_succ]
    simp only [deficit,Nat.cast_add,Nat.cast_one]
    ring

lemma deficit_limit {f : ℕ → ℝ} {α c : ℝ} (hα : 0 ≤ α) (hc : 0 < c)
    (h : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, deficit f n)/(N : ℝ)^(α+1))
      atTop (𝓝 (c*(2-α)/(α+1))) := by
  have hp : 0 < α+1 := by linarith
  have hS := Erdos713FutureRecords.ratio_limit (Erdos713PowerSum.sum_asymptotic hα hc h)
  have hF := Erdos713FutureRecords.ratio_limit h
  have hI : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun N : ℕ => 1-(N : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hI
  have hZero : Tendsto (fun N : ℕ => f 0/(N : ℝ)^(α+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop)
  have ht := ((hS.const_mul 3).sub (hR.mul hF)).sub hZero
  have he : 3*(c/(α+1))-1*c-0 = c*(2-α)/(α+1) := by field_simp; ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sum_deficit,Real.rpow_add hNp,Real.rpow_one]
  field_simp

lemma cumulative_lower {W : Type*} (H : SimpleGraph W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (G : (n : ℕ) → SimpleGraph (Fin n)) (hFree : ∀ n, H.Free (G n))
    (he : ∀ n, Nat.card (G n).edgeSet = extremalNumber n H)
    {α c : ℝ} (hα : 0 ≤ α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (κ : ℝ) (hκ : κ < c*(2-α)/(α+1)) :
    ∀ᶠ N : ℕ in atTop, κ*(N : ℝ)^(α+1) ≤ ∑ n ∈ range N, mass H (G n) := by
  have ht := deficit_limit hα hc h
  filter_upwards [ht.eventually_const_lt hκ,eventually_gt_atTop (0 : ℕ)] with N hN hNp
  have hpow : (0 : ℝ) < (N : ℝ)^(α+1) := Real.rpow_pos_of_pos (by exact_mod_cast hNp) _
  have hs : ∑ n ∈ range N, deficit (fun n => (extremalNumber n H : ℝ)) n ≤
      ∑ n ∈ range N, mass H (G n) :=
    sum_le_sum (fun n _ => mass_deficit H hNoIso (G n) (hFree n) (he n))
  exact (le_of_lt ((lt_div_iff₀ hpow).mp hN)).trans hs

lemma excess_deficit_limit {f : ℕ → ℝ} {α c : ℝ} (hα : 0 ≤ α) (hc : 0 < c)
    (h : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) (η : ℝ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (deficit f n-η*f n))/(N : ℝ)^(α+1))
      atTop (𝓝 (c*(2-α-η)/(α+1))) := by
  have hS := Erdos713FutureRecords.ratio_limit (Erdos713PowerSum.sum_asymptotic hα hc h)
  have ht := (deficit_limit hα hc h).sub (hS.const_mul η)
  have he : c*(2-α)/(α+1)-η*(c/(α+1)) = c*(2-α-η)/(α+1) := by ring
  rw [he] at ht
  convert ht using 1
  funext N
  rw [sum_sub_distrib,← mul_sum,sub_div,mul_div_assoc]

lemma cumulative_excess_lower {W : Type*} (H : SimpleGraph W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (G : (n : ℕ) → SimpleGraph (Fin n)) (hFree : ∀ n, H.Free (G n))
    (he : ∀ n, Nat.card (G n).edgeSet = extremalNumber n H)
    {α c : ℝ} (hα : 0 ≤ α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (η κ : ℝ) (hκ : κ < c*(2-α-η)/(α+1)) :
    ∀ᶠ N : ℕ in atTop, κ*(N : ℝ)^(α+1) ≤
      ∑ n ∈ range N, (mass H (G n)-η*(extremalNumber n H : ℝ)) := by
  have ht := excess_deficit_limit hα hc h η
  filter_upwards [ht.eventually_const_lt hκ,eventually_gt_atTop (0 : ℕ)] with N hN hNp
  have hpow : (0 : ℝ) < (N : ℝ)^(α+1) := Real.rpow_pos_of_pos (by exact_mod_cast hNp) _
  have hs : ∑ n ∈ range N, (deficit (fun n => (extremalNumber n H : ℝ)) n-
        η*(extremalNumber n H : ℝ)) ≤
      ∑ n ∈ range N, (mass H (G n)-η*(extremalNumber n H : ℝ)) :=
    sum_le_sum (fun n _ => sub_le_sub_right (mass_deficit H hNoIso (G n) (hFree n) (he n)) _)
  exact (le_of_lt ((lt_div_iff₀ hpow).mp hN)).trans hs

/-- Every choice of exactly extremal hosts has a positive lower density of
sizes carrying a fixed positive cloning-obstruction mass fraction. This
asserts no minimum degree or past-record property at those sizes. -/
lemma positive_density {W : Type*} (H : SimpleGraph W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (G : (n : ℕ) → SimpleGraph (Fin n)) (hFree : ∀ n, H.Free (G n))
    (he : ∀ n, Nat.card (G n).edgeSet = extremalNumber n H)
    {α c η : ℝ} (hα : 0 ≤ α) (hc : 0 < c) (hη : 0 ≤ η) (hηα : η < 2-α)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      δ*(N : ℝ) ≤ ((range N).filter
        (fun n => η*(extremalNumber n H : ℝ) < mass H (G n))).card := by
  classical
  let κ : ℝ := c*(2-α-η)/(α+1)/2
  have hgap : 0 < 2-α-η := sub_pos.mpr hηα
  have hαp : 0 < α+1 := by linarith
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκlt : κ < c*(2-α-η)/(α+1) := by dsimp [κ] at *; linarith
  obtain ⟨C,hC,hBound⟩ := Erdos713EdgeAttachments.global_extremal_bound_of_upper H hα
    ((isBigO_const_mul_right_iff hc.ne').mp h.isBigO)
  have hCpos : 0 < 2*(C+1) := by linarith
  refine ⟨κ/(2*(C+1)),div_pos hκ hCpos,?_⟩
  filter_upwards [cumulative_excess_lower H hNoIso G hFree he hα hc h η κ hκlt,
    eventually_gt_atTop (0 : ℕ)] with N hN hNp
  let A := (range N).filter (fun n => η*(extremalNumber n H : ℝ) < mass H (G n))
  have hnBound (n : ℕ) (hn : n ∈ range N) :
      mass H (G n) ≤ 2*(C+1)*(N : ℝ)^α := by
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_range.mp hn).le
    have hpow := Real.rpow_le_rpow (Nat.cast_nonneg n) hnN hα
    have hfn := (hBound n).trans (mul_le_mul_of_nonneg_left hpow hC)
    have hm := mass_le H (G n)
    rw [he n] at hm
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg N) α]
  have hs : (∑ n ∈ range N, (mass H (G n)-η*(extremalNumber n H : ℝ))) ≤
      (A.card : ℝ)*(2*(C+1)*(N : ℝ)^α) := by
    calc
      _ ≤ ∑ n ∈ range N, if η*(extremalNumber n H : ℝ) < mass H (G n)
          then 2*(C+1)*(N : ℝ)^α else 0 := by
        apply sum_le_sum
        intro n hn
        split_ifs with hnGood
        · have hnB := hnBound n hn
          have hnonneg : 0 ≤ η*(extremalNumber n H : ℝ) := by positivity
          linarith
        · linarith
      _ = _ := by rw [← sum_filter]; simp only [A,sum_const,nsmul_eq_mul]
  have hPow : (0 : ℝ) < (N : ℝ)^α := Real.rpow_pos_of_pos (by exact_mod_cast hNp) _
  have hMul : κ*(N : ℝ) ≤ (A.card : ℝ)*(2*(C+1)) := by
    apply (mul_le_mul_iff_left₀ hPow).mp
    have hp : (N : ℝ)^(α+1) = (N : ℝ)^α*(N : ℝ) := by
      rw [Real.rpow_add (by exact_mod_cast hNp),Real.rpow_one]
    rw [hp] at hN
    nlinarith
  change κ/(2*(C+1))*(N : ℝ) ≤ (A.card : ℝ)
  rw [div_mul_eq_mul_div,div_le_iff₀ hCpos]
  exact hMul

lemma exists_extremal_family {W : Type*} (H : SimpleGraph W) (hEdge : ∃ a b, H.Adj a b) :
    ∃ G : (n : ℕ) → SimpleGraph (Fin n),
      (∀ n, H.Free (G n)) ∧ (∀ n, Nat.card (G n).edgeSet = extremalNumber n H) := by
  classical
  have hEach (n : ℕ) : ∃ G : SimpleGraph (Fin n), H.Free G ∧
      Nat.card G.edgeSet = extremalNumber n H := by
    let S : Finset (SimpleGraph (Fin n)) := {G | H.Free G}
    have hBot : H.Free (⊥ : SimpleGraph (Fin n)) := by
      rintro ⟨f⟩
      obtain ⟨a,b,hab⟩ := hEdge
      exact f.toHom.map_adj hab
    have hS : S.Nonempty := ⟨⊥,by simpa [S] using hBot⟩
    obtain ⟨G,hG,he⟩ := exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
    refine ⟨G,by simpa [S] using hG,?_⟩
    change Nat.card G.edgeSet = S.sup (fun G => G.edgeFinset.card)
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using he.symm
  choose G hFree he using hEach
  exact ⟨G,hFree,he⟩

lemma exists_positive_density {W : Type*} (H : SimpleGraph W) (hEdge : ∃ a b, H.Adj a b)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) {α c η : ℝ} (hα : 0 ≤ α) (hc : 0 < c)
    (hη : 0 ≤ η) (hηα : η < 2-α)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ G : (n : ℕ) → SimpleGraph (Fin n),
      (∀ n, H.Free (G n)) ∧ (∀ n, Nat.card (G n).edgeSet = extremalNumber n H) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
        δ*(N : ℝ) ≤ ((range N).filter
          (fun n => η*(extremalNumber n H : ℝ) < mass H (G n))).card := by
  obtain ⟨G,hFree,he⟩ := exists_extremal_family H hEdge
  exact ⟨G,hFree,he,positive_density H hNoIso G hFree he hα hc hη hηα h⟩

#print axioms mass_deficit
#print axioms deficit_limit
#print axioms cumulative_lower
#print axioms positive_density
#print axioms exists_positive_density
end Erdos713CloneAverage
