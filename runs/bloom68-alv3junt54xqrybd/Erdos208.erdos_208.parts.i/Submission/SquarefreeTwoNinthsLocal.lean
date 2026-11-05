import Submission.SquarefreeTwoNinthsDeterminant

/-!
# Four-point cells in a dyadic band

Rational cell widths are encoded by the existing right-closed natural bins.
No prime assumption, minimum-gap assumption, or offset distinctness is used.
-/
namespace SquarefreeTwoNinths

open SquarefreeFourthSign SquarefreeRoth

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Integrality prohibits four actual witnesses in this rational window. -/
lemma no_four_in_window {N H P K : ℕ}
    (hH : 0 < H) (hP : H ≤ P)
    (hmain : 4^6*N*P ≤ K^6) (hnoise : 4^3*H*P ≤ K^3)
    {a b c d : ℕ × ℕ} (ha : Witness N H a) (hb : Witness N H b)
    (hc : Witness N H c) (hd : Witness N H d)
    (hPa : P < a.1) (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1)
    (hspan : (d.1 : ℚ)-a.1 ≤ (P : ℚ)/K) : False := by
  have hP0 : 0 < P := hH.trans_le hP
  have hK0 : 0 < K := by
    by_contra h
    have hk : K = 0 := by omega
    rw [hk] at hnoise
    norm_num at hnoise
    have := Nat.mul_pos hH hP0
    omega
  have hPq : (0 : ℚ) < P := by exact_mod_cast hP0
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hm : (4096 : ℚ)*(N : ℚ)*P ≤ (K : ℚ)^6 := by exact_mod_cast hmain
  have he : (64 : ℚ)*(H : ℚ)*P ≤ (K : ℚ)^3 := by exact_mod_cast hnoise
  have hrN : (N : ℚ)*P/(K : ℚ)^6 ≤ 1/4096 := by
    apply (div_le_iff₀ (pow_pos hKq 6)).mpr
    linarith
  have hrH : (H : ℚ)*P/(K : ℚ)^3 ≤ 1/64 := by
    apply (div_le_iff₀ (pow_pos hKq 3)).mpr
    linarith
  have hbnd := determinant_four_bound N H P ((P : ℚ)/K)
    a.1 b.1 c.1 d.1 a.2 b.2 c.2 d.2
    (by positivity) (by positivity) hPq (by exact_mod_cast hPa.le)
    (by exact_mod_cast hab) (by exact_mod_cast hbc) (by exact_mod_cast hcd) hspan
    (by exact_mod_cast ha.2.2.1.le) (by exact_mod_cast ha.2.2.2)
    (by exact_mod_cast hb.2.2.1.le) (by exact_mod_cast hb.2.2.2)
    (by exact_mod_cast hc.2.2.1.le) (by exact_mod_cast hc.2.2.2)
    (by exact_mod_cast hd.2.2.1.le) (by exact_mod_cast hd.2.2.2)
  have hid : 4*(N : ℚ)*((P : ℚ)/K)^6/(P : ℚ)^5 +
      4*(H : ℚ)*((P : ℚ)/K)^3/(P : ℚ)^2 =
      4*((N : ℚ)*P/(K : ℚ)^6) + 4*((H : ℚ)*P/(K : ℚ)^3) := by
    field_simp
  rw [hid] at hbnd
  have hlo := determinant_four_abs_ge_one hH ha hb hc hd hab hbc hcd
  linarith

/-- No ordered quadruple and injective bases imply cardinality at most three. -/
lemma card_le_three_of_no_ordered_quadruple (S : Finset (ℕ × ℕ))
    (hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)))
    (hfour : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a.1 < b.1 → b.1 < c.1 → c.1 < d.1 → False) : S.card ≤ 3 := by
  classical
  by_contra h
  have hs : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image S Prod.fst hs
  have htwo : (S.erase a).card ≤ 2 := by
    apply card_le_two_of_no_ordered_triple
    · exact hinj.mono (Finset.erase_subset _ _)
    · intro b hb c hc d hd hbc hcd
      have hbS := (Finset.mem_erase.mp hb).2
      have hcS := (Finset.mem_erase.mp hc).2
      have hdS := (Finset.mem_erase.mp hd).2
      have hab : a.1 < b.1 := by
        have hne : a.1 ≠ b.1 := by
          intro heq
          exact (Finset.mem_erase.mp hb).1 (hinj ha hbS heq).symm
        exact lt_of_le_of_ne (hmin b hbS) hne
      exact hfour a ha b hbS c hcS d hdS hab hbc hcd
  have he := Finset.card_erase_add_one ha
  omega

/-- At most three witnesses per bin, so at most `3K` in a band. -/
theorem band_card_le_four (N H P K : ℕ) (S : Finset (ℕ × ℕ))
    (hH : 0 < H) (hP : H ≤ P)
    (hmain : 4^6*N*P ≤ K^6) (hnoise : 4^3*H*P ≤ K^3)
    (hS : ∀ w ∈ S, Witness N H w ∧ P < w.1 ∧ w.1 ≤ 2*P) :
    S.card ≤ 3*K := by
  have hP0 : 0 < P := hH.trans_le hP
  have hK0 : 0 < K := by
    by_contra h
    have hk : K = 0 := by omega
    rw [hk] at hnoise
    norm_num at hnoise
    have := Nat.mul_pos hH hP0
    omega
  have hinj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact witness_base_injective hH (hS a ha).1 (hS b hb).1 hab
  have hfiber : ∀ j ∈ Finset.range K, (S.filter (fun w => bin P K w.1 = j)).card ≤ 3 := by
    intro j _hj
    apply card_le_three_of_no_ordered_quadruple
    · exact hinj.mono (Finset.filter_subset _ _)
    · intro a ha b hb c hc d hd hab hbc hcd
      obtain ⟨haS,haj⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbS,_hbj⟩ := Finset.mem_filter.mp hb
      obtain ⟨hcS,_hcj⟩ := Finset.mem_filter.mp hc
      obtain ⟨hdS,hdj⟩ := Finset.mem_filter.mp hd
      have has := hS a haS
      have hbs := hS b hbS
      have hcs := hS c hcS
      have hds := hS d hdS
      apply no_four_in_window hH hP hmain hnoise has.1 hbs.1 hcs.1 hds.1
        has.2.1 hab hbc hcd
      exact bin_span hP0 hK0 has.2.1 has.2.2 hds.2.1 hds.2.2 (haj.trans hdj.symm)
  have hc := Finset.card_le_mul_card_image_of_maps_to
    (f := fun w : ℕ × ℕ => bin P K w.1) (s := S) (t := Finset.range K)
    (fun w hw => Finset.mem_range.mpr (bin_bounds hP0 hK0 (hS w hw).2.1 (hS w hw).2.2).1)
    3 hfiber
  simpa only [Finset.card_range] using hc

end SquarefreeTwoNinths
