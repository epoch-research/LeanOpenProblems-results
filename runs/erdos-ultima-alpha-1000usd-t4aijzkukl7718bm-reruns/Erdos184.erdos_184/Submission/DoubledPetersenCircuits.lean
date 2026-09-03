import Submission.DoubledPetersenStates
import Submission.BinaryVectorEncode

/-!
Completeness of the 72 circuit types as minimal nonzero even multiplicity
vectors on Petersen. The remaining SimpleGraph subdivision correspondence
is not supplied by this file, and Erdos 184 is not settled.
-/
namespace Erdos184
namespace DoubledPetersenCertificate

abbrev Multiplicity := Fin 15 → ℕ

def EvenVector (m : Multiplicity) : Prop :=
  ∀ v : Fin 10,
    (m (incident v 0) + m (incident v 1) + m (incident v 2)) % 2 = 0

def NonzeroVector (m : Multiplicity) : Prop := ∃ e, m e ≠ 0

def MinimalEven (m : Multiplicity) : Prop :=
  NonzeroVector m ∧ EvenVector m ∧
    ∀ q : Multiplicity, (∀ e, q e ≤ m e) → NonzeroVector q → EvenVector q → q = m

def asType (i : Fin 57) : Fin 72 := ⟨i.val,by omega⟩
def asDigon (e : Fin 15) : Fin 72 := ⟨57 + e.val,by omega⟩
def digon (e : Fin 15) : Multiplicity := fun f => if f=e then 2 else 0

def halfType : Fin 6 → Fin 57 := ![21,7,41,18,32,0]

lemma digon_digit (e : Fin 15) : digon e = digit (asDigon e) := by
  funext f
  revert e f; decide

lemma digon_even (e : Fin 15) : EvenVector (digon e) := by
  unfold EvenVector
  revert e; decide

lemma half_even (j : Fin 6) : EvenVector (digit (asType (halfType j))) := by
  unfold EvenVector
  revert j; decide

lemma half_nonzero (j : Fin 6) : NonzeroVector (digit (asType (halfType j))) := by
  unfold NonzeroVector
  revert j; decide

lemma half_le (j : Fin 6) (e : Fin 15) :
    digit (asType (halfType j)) e ≤ bit (twoFactorMask j) e := by
  revert j e; decide

lemma half_ne (j : Fin 6) : digit (asType (halfType j)) ≠ bit (twoFactorMask j) := by
  revert j; decide

lemma binary_encode (m : Multiplicity) (hm : ∀ e, m e < 2) :
    ∃ k : ℕ, k < 32768 ∧ ∀ e, bit k e = m e := by
  refine ⟨BinaryVectorEncode.encode 15 m,?_,?_⟩
  · exact BinaryVectorEncode.encode_lt 15 m hm
  · exact BinaryVectorEncode.digit_encode 15 m hm

lemma minimalEven_is_type (m : Multiplicity) (hm : MinimalEven m) :
    ∃ i : Fin 72, m = digit i := by
  by_cases htwo : ∃ e, 2 ≤ m e
  · obtain ⟨e,he⟩ := htwo
    have hq : digon e = m := hm.2.2 (digon e) (by
      intro f
      by_cases hf : f=e
      · simpa [digon,hf] using he
      · simp [digon,hf])
      ⟨e,by simp [digon]⟩ (digon_even e)
    exact ⟨asDigon e,hq.symm.trans (digon_digit e)⟩
  · have hb : ∀ e, m e < 2 := by
      intro e
      by_contra h
      exact htwo ⟨e,by omega⟩
    obtain ⟨k,hk,hbit⟩ := binary_encode m hb
    have he : EvenMask k := by
      intro v
      simp only [maskDegree,hbit]
      exact hm.2.1 v
    rcases evenMask_classification k hk he with hzero | hcy | hfactor
    · obtain ⟨e,he⟩ := hm.1
      have hh := hbit e
      simp [hzero,bit] at hh
      exact (he hh.symm).elim
    · obtain ⟨i,hi⟩ := hcy
      refine ⟨asType i,?_⟩
      funext e
      exact (hbit e).symm.trans (hi ▸ cycleMask_digits i e)
    · obtain ⟨j,hj⟩ := hfactor
      have hq := hm.2.2 (digit (asType (halfType j))) (by
        intro e
        rw [← hbit e,hj]
        exact half_le j e) (half_nonzero j) (half_even j)
      exfalso
      apply half_ne j
      exact hq.trans (funext fun e => (hbit e).symm.trans (congrArg (fun k => bit k e) hj))


lemma type_even (i : Fin 72) : EvenVector (digit i) := by
  unfold EvenVector
  revert i; decide

lemma type_nonzero (i : Fin 72) : NonzeroVector (digit i) := by
  unfold NonzeroVector
  revert i; decide

lemma cycle_digit_lt_two (i : Fin 57) (e : Fin 15) : digit (asType i) e < 2 := by
  revert i e; decide

set_option maxRecDepth 20000 in
lemma cycle_antichain : ∀ i j : Fin 57,
    (∀ e : Fin 15, digit (asType i) e ≤ digit (asType j) e) → i = j := by
  decide +kernel

set_option maxRecDepth 20000 in
lemma factor_not_le_cycle : ∀ j : Fin 6, ∀ i : Fin 57,
    ¬ (∀ e : Fin 15, bit (twoFactorMask j) e ≤ digit (asType i) e) := by
  decide +kernel

lemma one_edge_not_even (e : Fin 15) :
    ¬ EvenVector (fun f => if f=e then 1 else 0) := by
  unfold EvenVector
  revert e; decide

lemma cycle_type_minimal (i : Fin 57) : MinimalEven (digit (asType i)) := by
  refine ⟨type_nonzero _,type_even _,?_⟩
  intro q hq hqne hqe
  have hb : ∀ e, q e < 2 := fun e => (hq e).trans_lt (cycle_digit_lt_two i e)
  obtain ⟨k,hk,hbit⟩ := binary_encode q hb
  have he : EvenMask k := by
    intro v
    simp only [maskDegree,hbit]
    exact hqe v
  rcases evenMask_classification k hk he with hzero | hcycle | hfactor
  · obtain ⟨e,he⟩ := hqne
    have hh := hbit e
    simp [hzero,bit] at hh
    exact (he hh.symm).elim
  · obtain ⟨j,hj⟩ := hcycle
    have heq : q = digit (asType j) := by
      funext e
      exact (hbit e).symm.trans (hj ▸ cycleMask_digits j e)
    have hji : j = i := cycle_antichain j i (by simpa only [← heq] using hq)
    exact heq.trans (congrArg (fun j => digit (asType j)) hji)
  · obtain ⟨j,hj⟩ := hfactor
    exfalso
    apply factor_not_le_cycle j i
    intro e
    rw [← hj,hbit]
    exact hq e

lemma digon_minimal (e : Fin 15) : MinimalEven (digon e) := by
  refine ⟨⟨e,by simp [digon]⟩,digon_even e,?_⟩
  intro q hq hqne hqe
  have hz : ∀ f, f ≠ e → q f = 0 := by
    intro f hf
    have hh := hq f
    simp only [digon,if_neg hf] at hh
    omega
  have hpos : 0 < q e := by
    obtain ⟨f,hf⟩ := hqne
    by_cases hfe : f=e
    · subst f
      omega
    · exact (hf (hz f hfe)).elim
  have hle : q e ≤ 2 := by simpa [digon] using hq e
  have hnotone : q e ≠ 1 := by
    intro h1
    have heq : q = (fun f => if f=e then 1 else 0) := by
      funext f
      by_cases hf : f=e
      · simp [hf,h1]
      · simp [hf,hz f hf]
    exact one_edge_not_even e (heq ▸ hqe)
  have htwo : q e = 2 := by omega
  funext f
  by_cases hf : f=e
  · simp [digon,hf,htwo]
  · simp [digon,hf,hz f hf]

lemma type_minimal (i : Fin 72) : MinimalEven (digit i) := by
  by_cases hi : i.val < 57
  · exact cycle_type_minimal ⟨i.val,hi⟩
  · let e : Fin 15 := ⟨i.val-57,by omega⟩
    have he : asDigon e = i := by apply Fin.ext; simp only [asDigon,e]; omega
    rw [← he,← digon_digit]
    exact digon_minimal e

lemma minimalEven_iff_type (m : Multiplicity) :
    MinimalEven m ↔ ∃ i : Fin 72, m = digit i := by
  constructor
  · exact minimalEven_is_type m
  · rintro ⟨i,rfl⟩
    exact type_minimal i

/-- Circuit partitions expressed without choosing labels for the 72 types. -/
def IsCircuitPartition (D : List Multiplicity) : Prop :=
  (∀ m ∈ D, MinimalEven m) ∧ ∀ e : Fin 15, (D.map (fun m => m e)).sum = 2

lemma circuitPartition_length_lower (D : List Multiplicity) (hD : IsCircuitPartition D) :
    5 ≤ D.length := by
  have hex : ∀ F : List Multiplicity, (∀ m ∈ F, MinimalEven m) →
      ∃ E : List (Fin 72), E.map digit = F := by
    intro F
    induction F with
    | nil => intro _; exact ⟨[],rfl⟩
    | cons m F ih =>
      intro hf
      obtain ⟨i,hi⟩ := minimalEven_is_type m (hf m (List.mem_cons_self))
      obtain ⟨E,hE⟩ := ih (fun m hm => hf m (List.mem_cons_of_mem _ hm))
      exact ⟨i :: E,by simp only [List.map_cons,hE,← hi]⟩
  obtain ⟨E,hE⟩ := hex D hD.1
  have he : IsPartition E := by
    intro e
    have hh := hD.2 e
    rw [← hE,List.map_map] at hh
    exact hh
  have hb := partition_length_lower E he
  have hlen := congrArg List.length hE
  simp only [List.length_map] at hlen
  omega

lemma extension_circuitPartition (i : Fin 72) :
    IsCircuitPartition ((extension i).map digit) := by
  constructor
  · intro m hm
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
    exact type_minimal j
  · intro e
    simpa only [List.map_map] using extension_partition i e

lemma every_circuit_has_optimal_extension (m : Multiplicity) (hm : MinimalEven m) :
    ∃ D : List Multiplicity, m ∈ D ∧ IsCircuitPartition D ∧ D.length = 5 ∧
      ∀ E : List Multiplicity, IsCircuitPartition E → D.length ≤ E.length := by
  obtain ⟨i,rfl⟩ := minimalEven_is_type m hm
  refine ⟨(extension i).map digit,List.mem_map.mpr ⟨i,mem_extension i,rfl⟩,
    extension_circuitPartition i,?_,?_⟩
  · rw [List.length_map,extension_length]
  · intro E hE
    rw [List.length_map,extension_length]
    exact circuitPartition_length_lower E hE

lemma digons_circuitPartition : IsCircuitPartition (digonPartition.map digit) := by
  constructor
  · intro m hm
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
    exact type_minimal i
  · intro e
    simpa only [List.map_map] using digon_partition e

lemma circuit_partition_sizes_vary :
    ∃ D E : List Multiplicity, IsCircuitPartition D ∧ IsCircuitPartition E ∧
      D.length < E.length := by
  refine ⟨(extension 0).map digit,digonPartition.map digit,
    extension_circuitPartition 0,digons_circuitPartition,?_⟩
  rw [List.length_map,List.length_map,extension_length,digon_partition_length]
  decide

end DoubledPetersenCertificate
end Erdos184
