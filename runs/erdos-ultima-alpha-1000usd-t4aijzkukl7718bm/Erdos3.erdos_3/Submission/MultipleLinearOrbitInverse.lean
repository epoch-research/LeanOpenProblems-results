import Submission.DenseLinearOrbitInverse

/-! A bounded-multiple version of dense linear orbit compression. A single
multiple is selected on a large fiber before applying the lattice estimate. -/
namespace Erdos3MultipleLinearOrbitInverse
open Finset Erdos3DenseLinearOrbitInverse
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

/-- If every t<N/D has a near-integer multiple d*t with 0<d<H, then the
slope has a bounded denominator with an inverse-square approximation error. -/
theorem multiple_linear_orbit_inverse (α : ℝ) {N D H E : ℕ}
    (hD : 0 < D) (hH : 0 < H)
    (hN : 8*(2*D*H)*(6*E+1) ≤ N)
    (hgood : ∀ t < N/D, ∃ d : ℕ, ∃ b : ℤ, 0 < d ∧ d < H ∧
      |α*((d*t : ℕ) : ℝ)-(b : ℝ)| ≤ (E : ℝ)/(N : ℝ)) :
    ∃ q : ℕ, ∃ b : ℤ, 0 < q ∧ q < 8*D*H^2 ∧
      |α*(q : ℝ)-(b : ℝ)| ≤
        256*(D : ℝ)^2*(H : ℝ)^2*(E : ℝ)*(6*(E : ℝ)+1)/(N : ℝ)^2 := by
  let T := N/D
  let R := 2*D*H
  have hR : 0 < R := Nat.mul_pos (Nat.mul_pos (by decide) hD) hH
  have hN0 : 0 < N := by
    have hp : 0 < 8*R*(6*E+1) := by positivity
    exact hp.trans_le hN
  have hDN : 2*D ≤ N := by
    have h1 := Nat.mul_le_mul_left (2*D) hH
    have h2 := Nat.mul_le_mul_left (8*(2*D*H)) (show 1 ≤ 6*E+1 by omega)
    nlinarith only [h1,h2,hN]
  have hT : 0 < T := Nat.div_pos (by omega) hD
  have hNT : N ≤ 2*D*T := by
    have hh := Nat.lt_mul_div_succ N hD
    change N < D*(T+1) at hh
    have ht : T+1 ≤ 2*T := by omega
    have hm := Nat.mul_le_mul_left D ht
    nlinarith only [hh,hm]
  have hex (t : ℕ) : ∃ d : ℕ, ∃ b : ℤ, t < T → 0 < d ∧ d < H ∧
      |α*((d*t : ℕ) : ℝ)-(b : ℝ)| ≤ (E : ℝ)/(N : ℝ) := by
    by_cases ht : t < T
    · obtain ⟨d,b,hd,hdH,he⟩ := hgood t ht
      exact ⟨d,b,fun _ ↦ ⟨hd,hdH,he⟩⟩
    · exact ⟨0,0,fun hh ↦ (ht hh).elim⟩
  choose d b hd using hex
  have hmap : ∀ t ∈ range T, d t ∈ range H := by
    intro t ht
    exact mem_range.mpr (hd t (mem_range.mp ht)).2.1
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hmean : (range H).card • ((T : ℝ)/(H : ℝ)) ≤ ((range T).card : ℝ) := by
    rw [card_range,card_range,nsmul_eq_mul,mul_div_cancel₀ _ hHr.ne']
  obtain ⟨a,ha,hfiber⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmap
    (nonempty_range_iff.mpr (by omega)) hmean
  let F := (range T).filter (fun t ↦ d t = a)
  have hcard : T ≤ H*F.card := by
    have hh := (div_le_iff₀ hHr).mp hfiber
    exact_mod_cast (by nlinarith only [hh] : (T : ℝ) ≤ (H : ℝ)*(F.card : ℝ))
  have hdensity : N ≤ R*F.card := by
    have hh := Nat.mul_le_mul_left (2*D) hcard
    dsimp only [R]
    nlinarith only [hNT,hh]
  have hFne : F.Nonempty := by
    apply card_pos.mp
    by_contra hn
    have he : F.card = 0 := by omega
    rw [he,Nat.mul_zero] at hdensity
    omega
  obtain ⟨t₀,ht₀⟩ := hFne
  have ht₀' := mem_filter.mp ht₀
  have ha0 : 0 < a := by rw [← ht₀'.2]; exact (hd t₀ (mem_range.mp ht₀'.1)).1
  have haH : a < H := mem_range.mp ha
  have hFN : F ⊆ range N := by
    intro t ht
    have htT := mem_range.mp (mem_filter.mp ht).1
    exact mem_range.mpr (htT.trans_le (Nat.div_le_self N D))
  have happrox : ∀ t ∈ F, |(α*(a : ℝ))*(t : ℝ)-(b t : ℝ)| ≤ (E : ℝ)/(N : ℝ) := by
    intro t ht
    obtain ⟨ht,he⟩ := mem_filter.mp ht
    have hh := (hd t (mem_range.mp ht)).2.2
    rw [he,Nat.cast_mul] at hh
    simpa only [mul_assoc] using hh
  obtain ⟨q,c,hq,hqR,herr⟩ := dense_linear_orbit_inverse (α*(a : ℝ)) F b
    hR hN hFN hdensity happrox
  refine ⟨q*a,c,Nat.mul_pos hq ha0,?_,?_⟩
  · have hh := Nat.mul_lt_mul_of_pos_right hqR ha0
    have hh' := Nat.mul_le_mul_left (4*R) haH.le
    dsimp only [R] at hh hh'
    nlinarith only [hh,hh']
  · calc
      _ = |(α*(a : ℝ))*(q : ℝ)-(c : ℝ)| := by push_cast; ring_nf
      _ ≤ _ := herr
      _ = _ := by dsimp only [R]; push_cast; ring

#print axioms multiple_linear_orbit_inverse
end Erdos3MultipleLinearOrbitInverse
