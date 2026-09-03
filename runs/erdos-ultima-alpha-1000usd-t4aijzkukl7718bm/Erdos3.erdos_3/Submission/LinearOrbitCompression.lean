import FormalConjecturesUtil

/-! An elementary lattice compression lemma for many near-integer points of a
linear orbit. A short difference gives a bounded integer determinant; a large
determinant fiber then improves the approximation by a second length factor. -/
namespace Erdos3LinearOrbitCompression
open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

lemma short_pair (H : Finset ℕ) {N Q : ℕ} (hQ : 0 < Q)
    (hH : H ⊆ range N) (hcard : N/Q+1 < H.card) :
    ∃ x ∈ H, ∃ y ∈ H, x < y ∧ y-x < Q := by
  have hmap : Set.MapsTo (fun x : ℕ ↦ x/Q) (H : Set ℕ) (range (N/Q+1) : Set ℕ) := by
    intro x hx
    have hxN := mem_range.mp (hH hx)
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hxN.le))
  obtain ⟨x,hx,y,hy,hxy,hdiv⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (by simpa only [card_range] using hcard) hmap
  have hsmall {a b : ℕ} (hab : a < b) (he : a/Q = b/Q) : b-a < Q := by
    have ha := Nat.mod_add_div a Q
    have hb := Nat.mod_add_div b Q
    have ham := Nat.mod_lt a hQ
    have hbm := Nat.mod_lt b hQ
    rw [he] at ha
    omega
  rcases lt_or_gt_of_ne hxy with hlt|hgt
  · exact ⟨x,hx,y,hy,hlt,hsmall hlt hdiv⟩
  · exact ⟨y,hy,x,hx,hgt,hsmall hgt hdiv.symm⟩

lemma wide_pair (H : Finset ℕ) {m : ℕ} (hcard : m < H.card) :
    ∃ x ∈ H, ∃ y ∈ H, x ≤ y ∧ m ≤ y-x := by
  have hne : H.Nonempty := card_pos.mp (by omega)
  let x := H.min' hne
  let y := H.max' hne
  have hx : x ∈ H := min'_mem H hne
  have hy : y ∈ H := max'_mem H hne
  have hxy : x ≤ y := min'_le H y hy
  have hsub : H ⊆ Icc x y := by
    intro a ha
    exact mem_Icc.mpr ⟨min'_le H a ha,le_max' H a ha⟩
  have hh := card_le_card hsub
  rw [Nat.card_Icc] at hh
  exact ⟨x,hx,y,hy,hxy,by omega⟩

/-- Many points within E/N of integers force a bounded denominator and an
error O(Q*E/(N*m)), where m is any admissible determinant-fiber size.
For positive-density H and fixed Q,E, one may take m proportional to N. -/
theorem compress_linear_orbit (α : ℝ) (H : Finset ℕ) (z : ℕ → ℤ)
    {N Q m E : ℕ} (hN : 0 < N) (hQ : 0 < Q) (hQN : Q ≤ N) (hm : 0 < m)
    (hH : H ⊆ range N) (hshort : N/Q+1 < H.card)
    (hwide : (6*E+1)*m < H.card)
    (happrox : ∀ h ∈ H, |α*(h : ℝ)-(z h : ℝ)| ≤ (E : ℝ)/(N : ℝ)) :
    ∃ q : ℕ, ∃ b : ℤ, 0 < q ∧ q < Q ∧
      |α*(q : ℝ)-(b : ℝ)| ≤ 2*(Q : ℝ)*(E : ℝ)/((N : ℝ)*(m : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨x₀,hx₀,y₀,hy₀,hxy₀,hqQ⟩ := short_pair H hQ hH hshort
  let q := y₀-x₀
  let b : ℤ := z y₀-z x₀
  let e : ℝ := α*(q : ℝ)-(b : ℝ)
  let err : ℕ → ℝ := fun h ↦ α*(h : ℝ)-(z h : ℝ)
  have hq : 0 < q := by dsimp only [q]; omega
  have hqQ' : q < Q := hqQ
  have hqN : q ≤ N := (Nat.le_of_lt hqQ').trans hQN
  have he : e = err y₀-err x₀ := by
    dsimp only [e,err,q,b]
    rw [Nat.cast_sub hxy₀.le,Int.cast_sub]
    ring
  have he_small : |e| ≤ 2*(E : ℝ)/(N : ℝ) := by
    rw [he]
    exact (abs_sub _ _).trans (by
      have ha := happrox y₀ hy₀
      have hb := happrox x₀ hx₀
      change |err y₀| ≤ _ at ha
      change |err x₀| ≤ _ at hb
      exact (add_le_add ha hb).trans_eq (by ring))
  let D : ℕ → ℤ := fun h ↦ (q : ℤ)*z h-b*(h : ℤ)
  have hdet (h : ℕ) : (D h : ℝ) = (h : ℝ)*e-(q : ℝ)*err h := by
    dsimp only [D,e,err]
    push_cast
    ring
  have hdet_bound (h : ℕ) (hh : h ∈ H) : |(D h : ℝ)| ≤ 3*(E : ℝ) := by
    have hhN : h ≤ N := (mem_range.mp (hH hh)).le
    have hhr : (h : ℝ) ≤ N := by exact_mod_cast hhN
    have hqr : (q : ℝ) ≤ N := by exact_mod_cast hqN
    have herr : |err h| ≤ (E : ℝ)/(N : ℝ) := happrox h hh
    have hem : (N : ℝ)*|e| ≤ 2*(E : ℝ) := by
      have ht := (le_div_iff₀ hNr).mp he_small
      nlinarith only [ht]
    have herm : (N : ℝ)*|err h| ≤ (E : ℝ) := by
      have ht := (le_div_iff₀ hNr).mp herr
      nlinarith only [ht]
    rw [hdet]
    calc
      _ ≤ |(h : ℝ)*e|+|(q : ℝ)*err h| := abs_sub _ _
      _ = (h : ℝ)*|e|+(q : ℝ)*|err h| := by
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg h : (0 : ℝ) ≤ h),abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
      _ ≤ (N : ℝ)*|e|+(N : ℝ)*|err h| :=
        add_le_add (mul_le_mul_of_nonneg_right hhr (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hqr (abs_nonneg _))
      _ ≤ _ := by linarith only [hem,herm]
  let T : Finset ℤ := Icc (-(3*(E : ℤ))) (3*(E : ℤ))
  have hDT : ∀ h ∈ H, D h ∈ T := by
    intro h hh
    have hi : |D h| ≤ 3*(E : ℤ) := by exact_mod_cast hdet_bound h hh
    exact mem_Icc.mpr (abs_le.mp hi)
  have hTcard : T.card = 6*E+1 := by
    dsimp only [T]
    rw [Int.card_Icc]
    omega
  obtain ⟨t,ht,hfiber⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hDT
    (by simpa only [hTcard] using hwide)
  let F := H.filter (fun h ↦ D h = t)
  obtain ⟨x,hx,y,hy,hxy,hspan⟩ := wide_pair F hfiber
  have hxH := (mem_filter.mp hx).1
  have hyH := (mem_filter.mp hy).1
  have hDx := (mem_filter.mp hx).2
  have hDy := (mem_filter.mp hy).2
  have hDeq : D y = D x := hDy.trans hDx.symm
  have hDreal : (D y : ℝ) = (D x : ℝ) := by exact_mod_cast hDeq
  rw [hdet,hdet] at hDreal
  have hid : ((y-x : ℕ) : ℝ)*e = (q : ℝ)*(err y-err x) := by
    rw [Nat.cast_sub hxy]
    nlinarith only [hDreal]
  have hspanr : (m : ℝ) ≤ ((y-x : ℕ) : ℝ) := by exact_mod_cast hspan
  have hmul : (m : ℝ)*|e| ≤ (Q : ℝ)*(2*(E : ℝ)/(N : ℝ)) := by
    calc
      _ ≤ ((y-x : ℕ) : ℝ)*|e| := mul_le_mul_of_nonneg_right hspanr (abs_nonneg _)
      _ = |((y-x : ℕ) : ℝ)*e| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg (y-x) : (0 : ℝ) ≤ ((y-x : ℕ) : ℝ))]
      _ = (q : ℝ)*|err y-err x| := by rw [hid,abs_mul,abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
      _ ≤ (q : ℝ)*(|err y|+|err x|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (Nat.cast_nonneg q)
      _ ≤ (q : ℝ)*(2*(E : ℝ)/(N : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
        have ha := happrox y hyH
        have hb := happrox x hxH
        change |err y| ≤ _ at ha
        change |err x| ≤ _ at hb
        exact (add_le_add ha hb).trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hqQ'.le)
        (div_nonneg (by positivity) hNr.le)
  refine ⟨q,b,hq,hqQ',?_⟩
  change |e| ≤ _
  calc
    _ ≤ ((Q : ℝ)*(2*(E : ℝ)/(N : ℝ)))/(m : ℝ) :=
      (le_div_iff₀ hmr).mpr (by nlinarith only [hmul])
    _ = _ := by field_simp

#print axioms compress_linear_orbit
end Erdos3LinearOrbitCompression
