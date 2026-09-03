import Submission.CapsetPolynomial

/-! Small-doubling consequences of the quantitative cap-set bound. -/
namespace Erdos3CapsetDoubling

open Finset
open scoped Pointwise
open Erdos3CapsetPolynomial
set_option maxHeartbeats 1000000

/-- A random-linear-map union bound, expressed by exact finite cardinalities. -/
lemma exists_linear_separating {n m : ℕ} (S : Finset (Vec n))
    (hzero : 0 ∉ S) (hsmall : S.card < 3^m) :
    ∃ f : Vec n →ₗ[F] Vec m, ∀ x ∈ S, f x ≠ 0 := by
  classical
  let M := Vec n →ₗ[F] Vec m
  letI : Finite M := Finite.of_injective (fun f : M ↦ (f : Vec n → Vec m)) DFunLike.coe_injective
  letI : Fintype M := Fintype.ofFinite M
  let bad (v : Vec n) : Finset M := univ.filter (fun f ↦ f v = 0)
  have hH : Fintype.card (Vec m) = 3^m := by simp [Vec, F, ZMod.card]
  have hbcard {v : Vec n} (hv : v ≠ 0) :
      (bad v).card * (3^m) = Fintype.card M := by
    let ev : M →ₗ[F] Vec m := LinearMap.applyₗ v
    have hev : Function.Surjective ev := by
      obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hv
      intro y
      refine ⟨φ.smulRight y, ?_⟩
      change φ v • y = y
      rw [hφ, one_smul]
    have hh := ev.toAddMonoidHom.ker.card_mul_index
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hev, AddSubgroup.card_top] at hh
    change Nat.card {f : M // f v = 0} * Nat.card (Vec m) = Nat.card M at hh
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, hH, bad] using hh
  have hbound : (S.biUnion bad).card * 3^m ≤ S.card * Fintype.card M := by
    calc
      _ ≤ (∑ v ∈ S, (bad v).card) * 3^m :=
        Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ v ∈ S, (bad v).card * 3^m := sum_mul ..
      _ = ∑ _v ∈ S, Fintype.card M := by
        apply sum_congr rfl
        intro v hv
        exact hbcard (fun hh ↦ hzero (hh ▸ hv))
      _ = S.card * Fintype.card M := by simp
  have hMpos : 0 < Fintype.card M := Fintype.card_pos
  have hlt : (S.biUnion bad).card < Fintype.card M := by
    have hh := lt_of_le_of_lt hbound (Nat.mul_lt_mul_of_pos_right hsmall hMpos)
    nlinarith [show (0 : ℕ) < 3^m by positivity]
  obtain ⟨f, _, hf⟩ := exists_mem_notMem_of_card_lt_card (by simpa using hlt)
  refine ⟨f, ?_⟩
  intro v hv hfv
  apply hf
  exact mem_biUnion.mpr ⟨v, hv, mem_filter.mpr ⟨mem_univ _, hfv⟩⟩

/-- Project a cap set into a space whose size is controlled by its triple sumset,
then apply the polynomial-method bound there. -/
theorem capset_card_le_tripling {n : ℕ} (S : Finset (Vec n))
    (hS : ThreeAPFree (S : Set (Vec n))) :
    S.card^15 ≤ 27^5 * (3 * (S+S+S).card)^14 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  let T := (S+S+S).erase 0
  have hz : (0 : Vec n) ∈ S+S+S := by
    obtain ⟨a, ha⟩ := hne
    simpa only [triple_self] using add_mem_add (add_mem_add ha ha) ha
  have hT : T.card + 1 = (S+S+S).card := card_erase_add_one hz
  let m := Nat.log 3 (T.card+1) + 1
  have hmgt : T.card < 3^m :=
    (Nat.lt_succ_self _).trans (Nat.lt_pow_succ_log_self (by decide) _)
  have hmle : 3^m ≤ 3 * (S+S+S).card := by
    dsimp [m]
    rw [pow_succ, ← hT]
    have hh := Nat.pow_log_le_self 3 (by omega : T.card+1 ≠ 0)
    nlinarith
  obtain ⟨f, hf⟩ := exists_linear_separating T (by simp [T]) hmgt
  have he (a b c : S) : f (a : Vec n) + f b + f c = 0 ↔ a=b ∧ b=c := by
    constructor
    · intro hh
      apply (capset_zero_iff hS a b c).mp
      by_contra hn
      have ht : (a : Vec n)+b+c ∈ T := mem_erase.mpr
        ⟨hn, add_mem_add (add_mem_add a.property b.property) c.property⟩
      exact hf _ ht (by simpa only [map_add] using hh)
    · rintro ⟨rfl, rfl⟩
      exact triple_self _
  have hb := capset_card_power_bound (fun a : S ↦ f (a : Vec n)) he
  simp only [Fintype.card_coe] at hb
  exact hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmle 14))

lemma tripling_times_card_sq_le {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Finset G) :
    (S+S+S).card * S.card^2 ≤ (S+S).card^3 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hpr := pluennecke_ruzsa_inequality_nsmul_add hne S 3
  have hthree : 3 • S = S+S+S := by
    change (2+1) • S = S+S+S
    rw [add_nsmul, two_nsmul, one_nsmul]
  rw [hthree] at hpr
  have hreal : ((S+S+S).card : ℝ) ≤
      (((S+S).card : ℝ) / S.card)^3 * S.card := by
    have hh := (NNRat.cast_le (K := ℝ)).mpr hpr
    push_cast at hh
    exact hh
  have hmpos : (0 : ℝ) < S.card := by exact_mod_cast hne.card_pos
  have hh : ((S+S+S).card : ℝ) * (S.card : ℝ)^2 ≤ ((S+S).card : ℝ)^3 := by
    calc
      _ ≤ ((((S+S).card : ℝ) / S.card)^3 * S.card) * (S.card : ℝ)^2 :=
        mul_le_mul_of_nonneg_right hreal (sq_nonneg _)
      _ = _ := by field_simp
  exact_mod_cast hh

/-- Dimension-free polynomial growth of the sumset of a cap set. -/
theorem capset_card_le_doubling {n : ℕ} (S : Finset (Vec n))
    (hS : ThreeAPFree (S : Set (Vec n))) :
    S.card^43 ≤ 3^29 * (S+S).card^42 := by
  have ht := tripling_times_card_sq_le S
  have hc : S.card^15 ≤ 3^29 * (S+S+S).card^14 := by
    calc
      _ ≤ 27^5 * (3*(S+S+S).card)^14 := capset_card_le_tripling S hS
      _ = _ := by ring
  calc
    S.card^43 = S.card^15 * (S.card^2)^14 := by ring
    _ ≤ (3^29 * (S+S+S).card^14) * (S.card^2)^14 := Nat.mul_le_mul_right _ hc
    _ = 3^29 * ((S+S+S).card * S.card^2)^14 := by ring
    _ ≤ 3^29 * ((S+S).card^3)^14 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht 14)
    _ = _ := by ring

#print axioms exists_linear_separating
#print axioms capset_card_le_tripling
#print axioms capset_card_le_doubling
end Erdos3CapsetDoubling
