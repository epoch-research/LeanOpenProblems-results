import Submission.Perturb
import Submission.Negative
open Nat Finset BigOperators Int Polynomial

lemma neg_one_pow_prime_mul {p N : ℕ} (hp : p.Prime) (hp5 : 5≤p) :
    (-1:ℤ)^(p*N)=(-1:ℤ)^N := by
  rw [pow_mul]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpw : (-1:ℤ)^p=-1 := by
    obtain ⟨t,rfl⟩ := hodd
    simp [pow_succ, pow_mul]
  rw [hpw]

lemma a_gen_scale_all (m : ℤ) {p N lev : ℕ}
    (hp : p.Prime) (hp5 : 5≤p) (hN : 0<N) (hdiv : p^lev∣N) :
    a_gen m (p*N) ≡ a_gen m N [ZMOD ((p:ℤ)^(3*(lev+1)))] := by
  cases m with
  | ofNat M =>
      exact a_gen_nat_scale hp hp5 hN hdiv
  | negSucc t =>
      cases t with
      | zero =>
          simpa using a_gen_neg_one_scale hp hp5 hN hdiv
      | succ t =>
          cases t with
          | zero =>
              simpa using a_gen_neg_two_scale (lev:=lev) hp hp5 hN
          | succ u =>
              let S := u+2
              have hS : 2≤S := by dsimp [S]; omega
              have hpN : 0<p*N := mul_pos hp.pos hN
              have hhigh := a_gen_negative_involution S (p*N) hS hpN
              have hlow := a_gen_negative_involution S N hS hN
              have hpos := a_gen_nat_scale (M:=S-2) hp hp5 hN hdiv
              have hbound := boundary_scale hS hp hp5 hN hdiv
              have hsum := hpos.add hbound
              have hsign := neg_one_pow_prime_mul hp hp5 (N:=N)
              change a_gen (-((S+1:ℕ):ℤ)) (p*N) ≡
                a_gen (-((S+1:ℕ):ℤ)) N [ZMOD ((p:ℤ)^(3*(lev+1)))]
              rw [hhigh, hlow, hsign]
              have hmul := Int.ModEq.mul_left ((-1:ℤ)^N) hsum
              simpa [S] using hmul
