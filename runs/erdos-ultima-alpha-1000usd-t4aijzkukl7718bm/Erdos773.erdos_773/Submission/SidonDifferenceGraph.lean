import Submission.SidonPartitionFunction
import Submission.SumsetIncidence

/-! The difference graph of a Sidon seed and its induced-density bound. -/
namespace Erdos773.SidonDifferenceGraph
open Finset SidonPartitionFunction SumsetIncidence
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] Classical.propDecidable

def Adj (T : Finset ℕ) (x y : ℕ) : Prop :=
  x ≠ y ∧ ∃ a ∈ T, ∃ b ∈ T, x+a=y+b

def translate (T : Finset ℕ) (x : ℕ) : Finset ℕ := T.image (fun a => x+a)

lemma adj_symm (T : Finset ℕ) (x y : ℕ) (h : Adj T x y) : Adj T y x := by
  obtain ⟨hxy,a,ha,b,hb,he⟩ := h
  exact ⟨hxy.symm,b,hb,a,ha,he.symm⟩
lemma adj_irrefl (T : Finset ℕ) (x : ℕ) : ¬Adj T x x := fun h => h.1 rfl
lemma translate_card (T : Finset ℕ) (x : ℕ) : (translate T x).card=T.card := by
  exact card_image_of_injective T (fun a b he => Nat.add_left_cancel he)
lemma translate_subset {T : Finset ℕ} {m x : ℕ} (hT : T ⊆ Icc 1 m) (hx : x ∈ Icc 1 m) :
    translate T x ⊆ Icc 1 (2*m) := by
  intro z hz
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
  have hh := mem_Icc.mp (hT ha)
  have hx := mem_Icc.mp hx
  exact mem_Icc.mpr ⟨by omega,by omega⟩

lemma common_card {T : Finset ℕ} (hT : IsSidon (T:Set ℕ)) (Z : Finset ℕ) {x y : ℕ} (hxy : x ≠ y) :
    (Z.filter (fun z => z ∈ translate T x ∧ z ∈ translate T y)).card ≤ 1 := by
  apply card_le_one.mpr
  intro z hz w hw
  obtain ⟨_,hx,hy⟩ := mem_filter.mp hz
  obtain ⟨_,hx',hy'⟩ := mem_filter.mp hw
  obtain ⟨a,ha,haz⟩ := mem_image.mp hx
  obtain ⟨b,hb,hbz⟩ := mem_image.mp hy
  obtain ⟨c,hc,hcw⟩ := mem_image.mp hx'
  obtain ⟨d,hd,hdw⟩ := mem_image.mp hy'
  have he : a+d=b+c := by omega
  rcases hT a ha b hb d hd c hc he with he | he
  · exact (hxy (by omega)).elim
  · omega

lemma common_zero {T : Finset ℕ} (Z : Finset ℕ) {x y : ℕ} (hxy : x ≠ y) (hnot : ¬Adj T x y) :
    (Z.filter (fun z => z ∈ translate T x ∧ z ∈ translate T y)).card=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨_,hx,hy⟩ := mem_filter.mp hz
  obtain ⟨a,ha,haz⟩ := mem_image.mp hx
  obtain ⟨b,hb,hbz⟩ := mem_image.mp hy
  exact hnot ⟨hxy,a,ha,b,hb,by omega⟩

lemma translate_filter_card {T : Finset ℕ} {m x : ℕ} (hT : T ⊆ Icc 1 m) (hx : x ∈ Icc 1 m) :
    ((Icc 1 (2*m)).filter (fun z => z ∈ translate T x)).card=T.card := by
  have he : (Icc 1 (2*m)).filter (fun z => z ∈ translate T x)=translate T x := by
    ext z
    simp only [mem_filter]
    exact and_iff_right_of_imp (fun hz => translate_subset hT hx hz)
  rw [he,translate_card]

/-- Cauchy-Schwarz forces a high-degree vertex in every sufficiently large
    induced carrier. This inequality retains the diagonal term explicitly. -/
theorem density_bound {T W : Finset ℕ} {m : ℕ} (hT : IsSidon (T:Set ℕ))
    (hTm : T ⊆ Icc 1 m) (hWm : W ⊆ Icc 1 m) (d : ℝ)
    (hdeg : ∀ x ∈ W, ((neighbors (Adj T) W x).card:ℝ) ≤ d) :
    ((W.card:ℝ)*T.card)^2 ≤ (2*(m:ℝ))*(W.card:ℝ)*(T.card+d) := by
  let Z := Icc 1 (2*m)
  let R : ℕ → ℕ → Prop := fun z x => z ∈ translate T x
  have hinc : incidenceCount Z W R=W.card*T.card := by
    rw [incidenceCount_comm]
    unfold incidenceCount
    have hh (x : ℕ) (hx : x ∈ W) : (Z.filter (fun z => R z x)).card=T.card :=
      translate_filter_card hTm (hWm hx)
    simp_rw [show (∑ x ∈ W, (Z.filter (fun z => R z x)).card)=∑ _x ∈ W, T.card from
      sum_congr rfl hh]
    simp
  have hcs := sum_mul_sq_le_sq_mul_sq (R := ℝ) Z (fun _ => (1:ℝ))
    (fun z => ((W.filter (R z)).card:ℝ))
  have hcs' : ((W.card:ℝ)*T.card)^2 ≤ (Z.card:ℝ)*(∑ z ∈ Z, ((W.filter (R z)).card:ℝ)^2) := by
    have hiR : (incidenceCount Z W R:ℝ)=(W.card:ℝ)*T.card := by exact_mod_cast hinc
    simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,← Nat.cast_sum] at hcs
    change (incidenceCount Z W R:ℝ)^2 ≤ _ at hcs
    rwa [hiR] at hcs
  have hrow (x : ℕ) (hx : x ∈ W) :
      (∑ y ∈ W, ((Z.filter (fun z => R z x ∧ R z y)).card:ℝ)) ≤ T.card+d := by
    have hterm (y : ℕ) (hy : y ∈ W) :
        ((Z.filter (fun z => R z x ∧ R z y)).card:ℝ) ≤
          (if y=x then (T.card:ℝ) else 0)+(if Adj T x y then (1:ℝ) else 0) := by
      by_cases hxy : x=y
      · subst y
        have hh := translate_filter_card hTm (hWm hx)
        simpa only [R,Z,and_self,if_true,adj_irrefl,if_false,add_zero] using le_of_eq (congrArg (fun n : ℕ => (n:ℝ)) hh)
      · by_cases hadj : Adj T x y
        · simpa only [if_neg (Ne.symm hxy),if_pos hadj,zero_add] using
            (show ((Z.filter (fun z => R z x ∧ R z y)).card:ℝ) ≤ 1 by exact_mod_cast common_card hT Z hxy)
        · rw [common_zero Z hxy hadj]
          simp [Ne.symm hxy,hadj]
    calc
      _ ≤ ∑ y ∈ W, ((if y=x then (T.card:ℝ) else 0)+(if Adj T x y then (1:ℝ) else 0)) := sum_le_sum hterm
      _ = T.card+(neighbors (Adj T) W x).card := by
        rw [sum_add_distrib,sum_ite_eq']
        simp only [hx,if_true,← sum_filter,sum_const,nsmul_eq_mul,mul_one,neighbors]
      _ ≤ _ := add_le_add le_rfl (hdeg x hx)
  have hrows : (∑ z ∈ Z, ((W.filter (R z)).card:ℝ)^2) ≤ (W.card:ℝ)*(T.card+d) := by
    rw [two_path_identity]
    exact (sum_le_sum hrow).trans_eq (by simp only [sum_const,nsmul_eq_mul])
  have hh := hcs'.trans (mul_le_mul_of_nonneg_left hrows (Nat.cast_nonneg _))
  simpa only [Z,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using hh

lemma remainder_independent {T S : Finset ℕ} (hS : IsSidon (S:Set ℕ)) (hTS : T ⊆ S) :
    Independent (Adj T) (S\T) := by
  intro x hx y hy hadj
  obtain ⟨hxy,a,ha,b,hb,he⟩ := hadj
  obtain ⟨hxS,hxT⟩ := mem_sdiff.mp hx
  obtain ⟨hyS,hyT⟩ := mem_sdiff.mp hy
  rcases hS x hxS y hyS a (hTS ha) b (hTS hb) he with hh | hh
  · exact hxy hh.1
  · exact hxT (hh.1 ▸ hb)

#print axioms common_card
#print axioms density_bound
#print axioms remainder_independent
end
end Erdos773.SidonDifferenceGraph
