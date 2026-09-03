import Submission.Coordinates
import Submission.SieveCertificate

/-! Applying the periodic sieve certificate to Gaussian prime walks. -/

namespace Erdos952Investigation

set_option maxHeartbeats 0

def residue (u : ℤ) : Fin 195 := ⟨(u % 195).toNat, by omega⟩

lemma residue_val (u : ℤ) : ((residue u).val : ℤ) = u % 195 := by
  simp [residue]
  omega

lemma residue_add_one (u : ℤ) : residue (u + 1) = residue u + 1 := by
  apply Fin.ext
  simp only [Fin.val_add]
  have h1 := residue_val (u + 1)
  have h0 := residue_val u
  change (residue (u + 1)).val = ((residue u).val + 1) % 195
  omega

lemma sieveNorm_mod_residue (u v p : ℤ) (hp : p ∣ 195) :
    sieveNorm (residue u).val (residue v).val % p = sieveNorm u v % p := by
  have hu : ((residue u).val : ℤ) ≡ u [ZMOD p] := by
    change ((residue u).val : ℤ) % p = u % p
    rw [residue_val, Int.emod_emod_of_dvd u hp]
  have hv : ((residue v).val : ℤ) ≡ v [ZMOD p] := by
    change ((residue v).val : ℤ) % p = v % p
    rw [residue_val, Int.emod_emod_of_dvd v hp]
  exact (((Int.ModEq.refl 1).add hu).add hv).pow 2 |>.add ((hu.sub hv).pow 2)

lemma norm_eq_sieveNorm {z : GaussianInt} (hz : (z.re + z.im) % 2 = 1) :
    z.norm = sieveNorm (coordU z) (coordV z) := by
  rw [gaussian_norm_sq, coordinates_re hz, coordinates_im hz]
  rfl

lemma large_prime_sieve_allowed {z : GaussianInt} (hz : Prime z)
    (hlarge : 169 < z.norm) : sieveAllowed (residue (coordU z)) (residue (coordV z)) := by
  have hodd := prime_large_odd_coordinate_sum hz (by omega)
  have hnorm := norm_eq_sieveNorm hodd
  have h3 := prime_large_norm_residue hz (by decide : Nat.Prime 3) (by norm_num; omega)
  have h5 := prime_large_norm_residue hz (by decide : Nat.Prime 5) (by norm_num; omega)
  have h13 := prime_large_norm_residue hz (by decide : Nat.Prime 13) (by norm_num; omega)
  unfold sieveAllowed
  rw [sieveNorm_mod_residue _ _ _ (by norm_num : (3 : ℤ) ∣ 195),
    sieveNorm_mod_residue _ _ _ (by norm_num : (5 : ℤ) ∣ 195),
    sieveNorm_mod_residue _ _ _ (by norm_num : (13 : ℤ) ∣ 195), ← hnorm]
  exact ⟨h3, h5, h13⟩

def anchor (u v : ℤ) : ℤ × ℤ :=
  (u - sieveLift (residue u) (residue v), v - sieveLift (residue v) (residue u))

lemma anchor_horizontal (u v : ℤ)
    (h0 : sieveAllowed (residue u) (residue v))
    (h1 : sieveAllowed (residue (u + 1)) (residue v)) :
    anchor (u + 1) v = anchor u v := by
  rw [residue_add_one] at h1
  obtain ⟨ha, hb⟩ := sieve_certificate (residue u) (residue v) h0 h1
  simp only [anchor, residue_add_one, ha, hb]
  congr 1
  omega

lemma sieveAllowed_comm (u v : Fin 195) : sieveAllowed u v ↔ sieveAllowed v u := by
  have h : sieveNorm u.val v.val = sieveNorm v.val u.val := by unfold sieveNorm; ring
  simp only [sieveAllowed, h]

lemma anchor_vertical (u v : ℤ)
    (h0 : sieveAllowed (residue u) (residue v))
    (h1 : sieveAllowed (residue u) (residue (v + 1))) :
    anchor u (v + 1) = anchor u v := by
  have h := anchor_horizontal v u ((sieveAllowed_comm _ _).mp h0)
    ((sieveAllowed_comm _ _).mp h1)
  exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

lemma anchor_adjacent (u v u' v' : ℤ)
    (h0 : sieveAllowed (residue u) (residue v))
    (h1 : sieveAllowed (residue u') (residue v'))
    (hs : (u' = u + 1 ∧ v' = v) ∨ (u = u' + 1 ∧ v' = v) ∨
      (u' = u ∧ v' = v + 1) ∨ (u' = u ∧ v = v' + 1)) :
    anchor u' v' = anchor u v := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact anchor_horizontal _ _ h0 h1
  · exact (anchor_horizontal _ _ h1 h0).symm
  · exact anchor_vertical _ _ h0 h1
  · exact (anchor_vertical _ _ h1 h0).symm

lemma prime_norm_two_anchor {z w : GaussianInt}
    (hz : Prime z) (hw : Prime w) (hzlarge : 169 < z.norm) (hwlarge : 169 < w.norm)
    (hstep : (w - z).norm = 2) :
    anchor (coordU w) (coordV w) = anchor (coordU z) (coordV z) := by
  apply anchor_adjacent _ _ _ _ (large_prime_sieve_allowed hz hzlarge)
    (large_prime_sieve_allowed hw hwlarge)
  exact norm_two_coordinates (prime_large_odd_coordinate_sum hz (by omega))
    (prime_large_odd_coordinate_sum hw (by omega)) hstep

lemma eq_of_anchor_and_residue {z w : GaussianInt}
    (hz : (z.re + z.im) % 2 = 1) (hw : (w.re + w.im) % 2 = 1)
    (ha : anchor (coordU z) (coordV z) = anchor (coordU w) (coordV w))
    (hr : (residue (coordU z), residue (coordV z)) =
      (residue (coordU w), residue (coordV w))) : z = w := by
  have hu : residue (coordU z) = residue (coordU w) := congrArg Prod.fst hr
  have hv : residue (coordV z) = residue (coordV w) := congrArg Prod.snd hr
  have hau := congrArg Prod.fst ha
  have hav := congrArg Prod.snd ha
  simp only [anchor, hu, hv] at hau hav
  have hU : coordU z = coordU w := by omega
  have hV : coordV z = coordV w := by omega
  apply Zsqrtd.ext
  · rw [coordinates_re hz, coordinates_re hw, hU, hV]
  · rw [coordinates_im hz, coordinates_im hw, hU, hV]

lemma step_bound_gt_four (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) : 4 < C := by
  by_contra hC
  have hC : C ≤ 4 := le_of_not_gt hC
  obtain ⟨N, hN⟩ := injective_escapes_norm x hx 169
  let y : ℕ → GaussianInt := fun n => x (N + n)
  have hy : Function.Injective y := by
    intro i j hij
    have := hx hij
    omega
  have hyp (n : ℕ) : Prime (y n) := (h (N + n)).1
  have hyn (n : ℕ) : 169 < (y n).norm := hN (N + n) (by omega)
  have hyo (n : ℕ) : ((y n).re + (y n).im) % 2 = 1 :=
    prime_large_odd_coordinate_sum (hyp n) (by have := hyn n; omega)
  have hstep (n : ℕ) : (y (n + 1) - y n).norm = 2 := by
    have heven := large_prime_difference_even_norm (hyp n) (hyp (n + 1))
      (by have := hyn n; omega) (by have := hyn (n + 1); omega)
    have hne : y (n + 1) - y n ≠ 0 := by
      intro heq
      have := hy (sub_eq_zero.mp heq)
      omega
    have hpos := GaussianInt.norm_pos.mpr hne
    have hlt : (y (n + 1) - y n).norm < C := by
      simpa only [y, Nat.add_assoc] using (h (N + n)).2
    omega
  have ha (n : ℕ) : anchor (coordU (y n)) (coordV (y n)) =
      anchor (coordU (y 0)) (coordV (y 0)) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      exact (prime_norm_two_anchor (hyp n) (hyp (n + 1)) (hyn n) (hyn (n + 1))
        (hstep n)).trans ih
  let f : ℕ → Fin 195 × Fin 195 := fun n => (residue (coordU (y n)), residue (coordV (y n)))
  apply not_injective_infinite_finite f
  intro i j hij
  exact hy (eq_of_anchor_and_residue (hyo i) (hyo j) ((ha i).trans (ha j).symm) hij)

#print axioms step_bound_gt_four

#print axioms prime_norm_two_anchor
#print axioms eq_of_anchor_and_residue

#print axioms large_prime_sieve_allowed
#print axioms anchor_horizontal
#print axioms anchor_vertical

end Erdos952Investigation
