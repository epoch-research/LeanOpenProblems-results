import Submission.EnvelopeFactorBounds

/-! Factorization gives a degree-dependent comparison and a quadratic bound
in the fractional envelope. Neither estimate is a uniform rounding result. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.EnvelopeFactorBounds
open FractionalEnvelope CycleNumberSubmodularity CountCritical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

omit [Fintype V] in
lemma mem_edgeSet_finset_sup {I : Type*} (s : Finset I) (F : I → SimpleGraph V)
    (e : Sym2 V) : e ∈ (s.sup F).edgeSet ↔ ∃ i ∈ s, e ∈ (F i).edgeSet := by
  induction e using Sym2.ind with
  | h x y => simp only [mem_edgeSet, Finset.sup_eq_iSup, iSup_adj, exists_prop]

lemma even_and_number_finset_sup {I : Type*} (s : Finset I) (F : I → SimpleGraph V)
    (he : ∀ i ∈ s, ∀ v, Even ((F i).degree v))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (F i).edgeSet (F j).edgeSet) :
    (∀ v, Even ((s.sup F).degree v)) ∧ cycleNumber (s.sup F) ≤ ∑ i ∈ s, cycleNumber (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · intro v
      simp only [Finset.sup_empty, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      simp
    · simp [number_bot]
  | @insert i s his ih =>
    have heS : ∀ j ∈ s, ∀ v, Even ((F j).degree v) := fun j hj => he j (Finset.mem_insert_of_mem hj)
    have hdS : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (F j).edgeSet (F k).edgeSet :=
      fun j hj k hk hne => hd j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne
    obtain ⟨heU,hnU⟩ := ih heS hdS
    have hdis : Disjoint (F i).edgeSet (s.sup F).edgeSet := by
      apply Set.disjoint_left.mpr
      intro e hei hes
      obtain ⟨j,hjs,hej⟩ := (mem_edgeSet_finset_sup s F e).mp hes
      exact Set.disjoint_left.mp (hd i (by simp) j (by simp [hjs]) (by intro h; exact his (h ▸ hjs))) hei hej
    have hei := he i (Finset.mem_insert_self i s)
    rw [Finset.sup_insert, Finset.sum_insert his]
    constructor
    · intro v
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using FractionalSeparated.even_sup hdis hei heU v
    · exact (CycleFactors.number_le_add (by rw [edgeSet_sup]) hdis hei heU).trans (Nat.add_le_add_left hnU _)

omit [Fintype V] in
lemma factor_data {I : Type*} [Fintype I] {G : SimpleGraph V} (F : I → SimpleGraph V)
    (hcov : ∀ x y, (∑ i, if (F i).Adj x y then (1 : ℕ) else 0) = if G.Adj x y then 1 else 0) :
    (∀ i, F i ≤ G) ∧
    (∀ i j, i ≠ j → Disjoint (F i).edgeSet (F j).edgeSet) ∧
    (Finset.univ.sup F = G) := by
  have hle (i : I) : F i ≤ G := by
    intro x y hxy
    have hh := Finset.single_le_sum (f := fun j => if (F j).Adj x y then (1 : ℕ) else 0)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp only at hh
    rw [if_pos hxy, hcov] at hh
    by_contra hn
    simp [hn] at hh
  refine ⟨hle,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with
    | h x y =>
      change (F i).Adj x y at hei
      change (F j).Adj x y at hej
      have hxy : G.Adj x y := hle i hei
      have hh := Finset.sum_le_sum_of_subset_of_nonneg
        (show ({i,j} : Finset I) ⊆ Finset.univ from Finset.subset_univ _)
        (f := fun a => if (F a).Adj x y then (1 : ℕ) else 0) (by intro _ _ _; omega)
      dsimp only at hh
      rw [Finset.sum_pair hij, if_pos hei, if_pos hej, hcov, if_pos hxy] at hh
      omega
  · ext x y
    simp only [Finset.sup_eq_iSup, iSup_adj, Finset.mem_univ, exists_prop, true_and]
    constructor
    · rintro ⟨i,hi⟩
      exact hle i hi
    · intro hxy
      by_contra hn
      push_neg at hn
      have hh := hcov x y
      simp [hn,hxy] at hh

lemma number_le_mul_fractional_of_degree_bound (G : SimpleGraph V) (r : ℕ)
    (he : ∀ v, Even (G.degree v)) (hd : ∀ v, G.degree v ≤ 2*r) :
    (cycleNumber G : ℝ) ≤ r * envelope G := by
  obtain ⟨F,hF,hcov⟩ := EvenCycleFactorization.exists_factorization G r he hd
  obtain ⟨hle,hdis,hu⟩ := factor_data F hcov
  have hn := (even_and_number_finset_sup Finset.univ F
    (fun i _ => CycleFactors.cycles_even (hF i)) (fun i _ j _ h => hdis i j h)).2
  rw [hu] at hn
  have hb (i : Fin r) : (cycleNumber (F i) : ℝ) ≤ envelope G := by
    rw [← CycleFactors.optimum_eq_number (hF i)]
    exact optimum_le_envelope (hle i) (CycleFactors.cycles_even (hF i))
  calc
    (cycleNumber G : ℝ) ≤ ∑ i, (cycleNumber (F i) : ℝ) := by exact_mod_cast hn
    _ ≤ ∑ _ : Fin r, envelope G := Finset.sum_le_sum (fun i _ => hb i)
    _ = r * envelope G := by simp

lemma integral_le_mul_fractional_of_degree_bound (G : SimpleGraph V) (r : ℕ)
    (hd : ∀ v, G.degree v ≤ 2*r) :
    (CycleEnvelope.envelope G : ℝ) ≤ r * envelope G := by
  obtain ⟨H,hHG,he,hval⟩ := CycleEnvelope.attained G
  have hdH : ∀ v, H.degree v ≤ 2*r := by
    intro v
    have hh := degree_le_of_le (v := v) hHG
    have hh' := hd v
    simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hh' ⊢
    omega
  have hn := number_le_mul_fractional_of_degree_bound H r he hdH
  rw [hval] at hn
  exact hn.trans (mul_le_mul_of_nonneg_left (envelope_mono hHG) (Nat.cast_nonneg r))

/-- A strict threshold yields an integer square, rather than a real quadratic
with a rounding ambiguity. This is not a linear comparison. -/
lemma integral_le_square_of_fractional_lt (G : SimpleGraph V) (r : ℕ)
    (hb : envelope G < (r : ℝ) + 1) : CycleEnvelope.envelope G ≤ r*r := by
  apply CycleEnvelope.envelope_le
  intro H hHG he
  have hd : ∀ v, H.degree v ≤ 2*r := degree_bound_of_envelope_lt hHG he hb
  obtain ⟨F,hF,hcov⟩ := EvenCycleFactorization.exists_factorization H r he hd
  obtain ⟨hle,hdis,hu⟩ := factor_data F hcov
  have hn := (even_and_number_finset_sup Finset.univ F
    (fun i _ => CycleFactors.cycles_even (hF i)) (fun i _ j _ h => hdis i j h)).2
  rw [hu] at hn
  have bound (i : Fin r) : cycleNumber (F i) ≤ r := by
    have hh := optimum_le_envelope ((hle i).trans hHG) (CycleFactors.cycles_even (hF i))
    rw [CycleFactors.optimum_eq_number (hF i)] at hh
    have hl : (cycleNumber (F i) : ℝ) < (r : ℝ) + 1 := hh.trans_lt hb
    have hlt : cycleNumber (F i) < r+1 := by exact_mod_cast hl
    omega
  calc
    cycleNumber H ≤ ∑ i, cycleNumber (F i) := hn
    _ ≤ ∑ _ : Fin r, r := Finset.sum_le_sum (fun i _ => bound i)
    _ = r*r := by simp

end Erdos184.EnvelopeFactorBounds
