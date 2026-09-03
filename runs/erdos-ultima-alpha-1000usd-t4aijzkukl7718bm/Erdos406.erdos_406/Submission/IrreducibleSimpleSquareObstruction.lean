import Submission.NewmanReverseValuation
/-! An explicit irreducible binary polynomial with a square value at three.
Its square root has odd prime factors, so this is not an Erdős406 counterexample. -/
namespace Erdos406IrreducibleSquare
open Polynomial Erdos406Cyclotomic Erdos406FactorCount Erdos406FactorBridge
  Erdos406SimpleModTwoRoot Erdos406ReverseValuation
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private lemma modular_pow_step {p a e r b s : ℕ}
    (h : (a : ZMod p) ^ e = r)
    (hc : (r : ZMod p) ^ 2 * (a : ZMod p) ^ b = s) :
    (a : ZMod p) ^ (e * 2 + b) = s := by
  rw [pow_add, pow_mul, h]
  exact hc
private lemma prime_2 : Nat.Prime 2 := by norm_num
private lemma prime_43 : Nat.Prime 43 := by norm_num
private lemma prime_409 : Nat.Prime 409 := by norm_num
private lemma prime_3 : Nat.Prime 3 := by norm_num
private lemma prime_5 : Nat.Prime 5 := by norm_num
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_97 : Nat.Prime 97 := by norm_num
lemma prime_531173 : Nat.Prime 531173 := by
  have h0 : (2 : ZMod 531173) ^ 0 = 1 := by simp
  have h1 : (2 : ZMod 531173) ^ 1 = 2 :=
    modular_pow_step (p := 531173) (a := 2) (e := 0) (r := 1) (b := 1) (s := 2) h0 (by decide +kernel)
  have h2 : (2 : ZMod 531173) ^ 2 = 4 :=
    modular_pow_step (p := 531173) (a := 2) (e := 1) (r := 2) (b := 0) (s := 4) h1 (by decide +kernel)
  have h3 : (2 : ZMod 531173) ^ 3 = 8 :=
    modular_pow_step (p := 531173) (a := 2) (e := 1) (r := 2) (b := 1) (s := 8) h1 (by decide +kernel)
  have h4 : (2 : ZMod 531173) ^ 4 = 16 :=
    modular_pow_step (p := 531173) (a := 2) (e := 2) (r := 4) (b := 0) (s := 16) h2 (by decide +kernel)
  have h5 : (2 : ZMod 531173) ^ 5 = 32 :=
    modular_pow_step (p := 531173) (a := 2) (e := 2) (r := 4) (b := 1) (s := 32) h2 (by decide +kernel)
  have h7 : (2 : ZMod 531173) ^ 7 = 128 :=
    modular_pow_step (p := 531173) (a := 2) (e := 3) (r := 8) (b := 1) (s := 128) h3 (by decide +kernel)
  have h8 : (2 : ZMod 531173) ^ 8 = 256 :=
    modular_pow_step (p := 531173) (a := 2) (e := 4) (r := 16) (b := 0) (s := 256) h4 (by decide +kernel)
  have h10 : (2 : ZMod 531173) ^ 10 = 1024 :=
    modular_pow_step (p := 531173) (a := 2) (e := 5) (r := 32) (b := 0) (s := 1024) h5 (by decide +kernel)
  have h14 : (2 : ZMod 531173) ^ 14 = 16384 :=
    modular_pow_step (p := 531173) (a := 2) (e := 7) (r := 128) (b := 0) (s := 16384) h7 (by decide +kernel)
  have h16 : (2 : ZMod 531173) ^ 16 = 65536 :=
    modular_pow_step (p := 531173) (a := 2) (e := 8) (r := 256) (b := 0) (s := 65536) h8 (by decide +kernel)
  have h21 : (2 : ZMod 531173) ^ 21 = 503633 :=
    modular_pow_step (p := 531173) (a := 2) (e := 10) (r := 1024) (b := 1) (s := 503633) h10 (by decide +kernel)
  have h28 : (2 : ZMod 531173) ^ 28 = 193091 :=
    modular_pow_step (p := 531173) (a := 2) (e := 14) (r := 16384) (b := 0) (s := 193091) h14 (by decide +kernel)
  have h32 : (2 : ZMod 531173) ^ 32 = 433591 :=
    modular_pow_step (p := 531173) (a := 2) (e := 16) (r := 65536) (b := 0) (s := 433591) h16 (by decide +kernel)
  have h42 : (2 : ZMod 531173) ^ 42 = 467729 :=
    modular_pow_step (p := 531173) (a := 2) (e := 21) (r := 503633) (b := 0) (s := 467729) h21 (by decide +kernel)
  have h56 : (2 : ZMod 531173) ^ 56 = 39065 :=
    modular_pow_step (p := 531173) (a := 2) (e := 28) (r := 193091) (b := 0) (s := 39065) h28 (by decide +kernel)
  have h64 : (2 : ZMod 531173) ^ 64 = 439526 :=
    modular_pow_step (p := 531173) (a := 2) (e := 32) (r := 433591) (b := 0) (s := 439526) h32 (by decide +kernel)
  have h85 : (2 : ZMod 531173) ^ 85 = 355457 :=
    modular_pow_step (p := 531173) (a := 2) (e := 42) (r := 467729) (b := 1) (s := 355457) h42 (by decide +kernel)
  have h112 : (2 : ZMod 531173) ^ 112 = 14196 :=
    modular_pow_step (p := 531173) (a := 2) (e := 56) (r := 39065) (b := 0) (s := 14196) h56 (by decide +kernel)
  have h129 : (2 : ZMod 531173) ^ 129 = 530266 :=
    modular_pow_step (p := 531173) (a := 2) (e := 64) (r := 439526) (b := 1) (s := 530266) h64 (by decide +kernel)
  have h171 : (2 : ZMod 531173) ^ 171 = 177024 :=
    modular_pow_step (p := 531173) (a := 2) (e := 85) (r := 355457) (b := 1) (s := 177024) h85 (by decide +kernel)
  have h224 : (2 : ZMod 531173) ^ 224 = 211849 :=
    modular_pow_step (p := 531173) (a := 2) (e := 112) (r := 14196) (b := 0) (s := 211849) h112 (by decide +kernel)
  have h259 : (2 : ZMod 531173) ^ 259 = 51779 :=
    modular_pow_step (p := 531173) (a := 2) (e := 129) (r := 530266) (b := 1) (s := 51779) h129 (by decide +kernel)
  have h342 : (2 : ZMod 531173) ^ 342 = 414268 :=
    modular_pow_step (p := 531173) (a := 2) (e := 171) (r := 177024) (b := 0) (s := 414268) h171 (by decide +kernel)
  have h448 : (2 : ZMod 531173) ^ 448 = 129685 :=
    modular_pow_step (p := 531173) (a := 2) (e := 224) (r := 211849) (b := 0) (s := 129685) h224 (by decide +kernel)
  have h518 : (2 : ZMod 531173) ^ 518 = 234710 :=
    modular_pow_step (p := 531173) (a := 2) (e := 259) (r := 51779) (b := 0) (s := 234710) h259 (by decide +kernel)
  have h684 : (2 : ZMod 531173) ^ 684 = 228908 :=
    modular_pow_step (p := 531173) (a := 2) (e := 342) (r := 414268) (b := 0) (s := 228908) h342 (by decide +kernel)
  have h897 : (2 : ZMod 531173) ^ 897 = 399398 :=
    modular_pow_step (p := 531173) (a := 2) (e := 448) (r := 129685) (b := 1) (s := 399398) h448 (by decide +kernel)
  have h1037 : (2 : ZMod 531173) ^ 1037 = 71021 :=
    modular_pow_step (p := 531173) (a := 2) (e := 518) (r := 234710) (b := 1) (s := 71021) h518 (by decide +kernel)
  have h1369 : (2 : ZMod 531173) ^ 1369 = 499066 :=
    modular_pow_step (p := 531173) (a := 2) (e := 684) (r := 228908) (b := 1) (s := 499066) h684 (by decide +kernel)
  have h1794 : (2 : ZMod 531173) ^ 1794 = 74082 :=
    modular_pow_step (p := 531173) (a := 2) (e := 897) (r := 399398) (b := 0) (s := 74082) h897 (by decide +kernel)
  have h2074 : (2 : ZMod 531173) ^ 2074 = 494806 :=
    modular_pow_step (p := 531173) (a := 2) (e := 1037) (r := 71021) (b := 0) (s := 494806) h1037 (by decide +kernel)
  have h2738 : (2 : ZMod 531173) ^ 2738 = 383829 :=
    modular_pow_step (p := 531173) (a := 2) (e := 1369) (r := 499066) (b := 0) (s := 383829) h1369 (by decide +kernel)
  have h3589 : (2 : ZMod 531173) ^ 3589 = 126576 :=
    modular_pow_step (p := 531173) (a := 2) (e := 1794) (r := 74082) (b := 1) (s := 126576) h1794 (by decide +kernel)
  have h4149 : (2 : ZMod 531173) ^ 4149 = 407011 :=
    modular_pow_step (p := 531173) (a := 2) (e := 2074) (r := 494806) (b := 1) (s := 407011) h2074 (by decide +kernel)
  have h5476 : (2 : ZMod 531173) ^ 5476 = 151480 :=
    modular_pow_step (p := 531173) (a := 2) (e := 2738) (r := 383829) (b := 0) (s := 151480) h2738 (by decide +kernel)
  have h7178 : (2 : ZMod 531173) ^ 7178 = 243750 :=
    modular_pow_step (p := 531173) (a := 2) (e := 3589) (r := 126576) (b := 0) (s := 243750) h3589 (by decide +kernel)
  have h8299 : (2 : ZMod 531173) ^ 8299 = 467703 :=
    modular_pow_step (p := 531173) (a := 2) (e := 4149) (r := 407011) (b := 1) (s := 467703) h4149 (by decide +kernel)
  have h14356 : (2 : ZMod 531173) ^ 14356 = 237758 :=
    modular_pow_step (p := 531173) (a := 2) (e := 7178) (r := 243750) (b := 0) (s := 237758) h7178 (by decide +kernel)
  have h16599 : (2 : ZMod 531173) ^ 16599 = 49736 :=
    modular_pow_step (p := 531173) (a := 2) (e := 8299) (r := 467703) (b := 1) (s := 49736) h8299 (by decide +kernel)
  have h33198 : (2 : ZMod 531173) ^ 33198 = 528208 :=
    modular_pow_step (p := 531173) (a := 2) (e := 16599) (r := 49736) (b := 0) (s := 528208) h16599 (by decide +kernel)
  have h66396 : (2 : ZMod 531173) ^ 66396 = 292457 :=
    modular_pow_step (p := 531173) (a := 2) (e := 33198) (r := 528208) (b := 0) (s := 292457) h33198 (by decide +kernel)
  have h132793 : (2 : ZMod 531173) ^ 132793 = 53740 :=
    modular_pow_step (p := 531173) (a := 2) (e := 66396) (r := 292457) (b := 1) (s := 53740) h66396 (by decide +kernel)
  have h265586 : (2 : ZMod 531173) ^ 265586 = 531172 :=
    modular_pow_step (p := 531173) (a := 2) (e := 132793) (r := 53740) (b := 0) (s := 531172) h132793 (by decide +kernel)
  have h531172 : (2 : ZMod 531173) ^ 531172 = 1 :=
    modular_pow_step (p := 531173) (a := 2) (e := 265586) (r := 531172) (b := 0) (s := 1) h265586 (by decide +kernel)
  apply lucas_primality 531173 2 (by simpa using h531172)
  intro q hq hqd
  rw [show 531173 - 1 = (2 * 2 * 37 * 37 * 97 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_37, Nat.dvd_prime prime_97, hq.ne_one, false_or] at hqd
  rcases hqd with ((((rfl | rfl) | rfl) | rfl) | rfl)
  · change (2 : ZMod 531173) ^ 265586 ≠ 1
    rw [h265586]
    decide +kernel
  · change (2 : ZMod 531173) ^ 265586 ≠ 1
    rw [h265586]
    decide +kernel
  · change (2 : ZMod 531173) ^ 14356 ≠ 1
    rw [h14356]
    decide +kernel
  · change (2 : ZMod 531173) ^ 14356 ≠ 1
    rw [h14356]
    decide +kernel
  · change (2 : ZMod 531173) ^ 5476 ≠ 1
    rw [h5476]
    decide +kernel

lemma prime_15935191 : Nat.Prime 15935191 := by
  have h0 : (3 : ZMod 15935191) ^ 0 = 1 := by simp
  have h1 : (3 : ZMod 15935191) ^ 1 = 3 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 0) (r := 1) (b := 1) (s := 3) h0 (by decide +kernel)
  have h2 : (3 : ZMod 15935191) ^ 2 = 9 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 1) (r := 3) (b := 0) (s := 9) h1 (by decide +kernel)
  have h3 : (3 : ZMod 15935191) ^ 3 = 27 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 1) (r := 3) (b := 1) (s := 27) h1 (by decide +kernel)
  have h5 : (3 : ZMod 15935191) ^ 5 = 243 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 2) (r := 9) (b := 1) (s := 243) h2 (by decide +kernel)
  have h6 : (3 : ZMod 15935191) ^ 6 = 729 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 3) (r := 27) (b := 0) (s := 729) h3 (by decide +kernel)
  have h7 : (3 : ZMod 15935191) ^ 7 = 2187 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 3) (r := 27) (b := 1) (s := 2187) h3 (by decide +kernel)
  have h10 : (3 : ZMod 15935191) ^ 10 = 59049 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 5) (r := 243) (b := 0) (s := 59049) h5 (by decide +kernel)
  have h12 : (3 : ZMod 15935191) ^ 12 = 531441 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 6) (r := 729) (b := 0) (s := 531441) h6 (by decide +kernel)
  have h15 : (3 : ZMod 15935191) ^ 15 = 14348907 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 7) (r := 2187) (b := 1) (s := 14348907) h7 (by decide +kernel)
  have h20 : (3 : ZMod 15935191) ^ 20 = 12912763 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 10) (r := 59049) (b := 0) (s := 12912763) h10 (by decide +kernel)
  have h24 : (3 : ZMod 15935191) ^ 24 = 10146388 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 12) (r := 531441) (b := 0) (s := 10146388) h12 (by decide +kernel)
  have h30 : (3 : ZMod 15935191) ^ 30 = 2788228 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 15) (r := 14348907) (b := 0) (s := 2788228) h15 (by decide +kernel)
  have h40 : (3 : ZMod 15935191) ^ 40 = 15616951 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 20) (r := 12912763) (b := 0) (s := 15616951) h20 (by decide +kernel)
  have h48 : (3 : ZMod 15935191) ^ 48 = 15472572 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 24) (r := 10146388) (b := 0) (s := 15472572) h24 (by decide +kernel)
  have h60 : (3 : ZMod 15935191) ^ 60 = 9357960 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 30) (r := 2788228) (b := 0) (s := 9357960) h30 (by decide +kernel)
  have h81 : (3 : ZMod 15935191) ^ 81 = 9741194 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 40) (r := 15616951) (b := 1) (s := 9741194) h40 (by decide +kernel)
  have h97 : (3 : ZMod 15935191) ^ 97 = 4236902 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 48) (r := 15472572) (b := 1) (s := 4236902) h48 (by decide +kernel)
  have h121 : (3 : ZMod 15935191) ^ 121 = 10413771 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 60) (r := 9357960) (b := 1) (s := 10413771) h60 (by decide +kernel)
  have h162 : (3 : ZMod 15935191) ^ 162 = 1114027 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 81) (r := 9741194) (b := 0) (s := 1114027) h81 (by decide +kernel)
  have h194 : (3 : ZMod 15935191) ^ 194 = 11257093 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 97) (r := 4236902) (b := 0) (s := 11257093) h97 (by decide +kernel)
  have h243 : (3 : ZMod 15935191) ^ 243 = 8381283 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 121) (r := 10413771) (b := 1) (s := 8381283) h121 (by decide +kernel)
  have h324 : (3 : ZMod 15935191) ^ 324 = 7546458 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 162) (r := 1114027) (b := 0) (s := 7546458) h162 (by decide +kernel)
  have h389 : (3 : ZMod 15935191) ^ 389 = 3078071 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 194) (r := 11257093) (b := 1) (s := 3078071) h194 (by decide +kernel)
  have h486 : (3 : ZMod 15935191) ^ 486 = 13315305 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 243) (r := 8381283) (b := 0) (s := 13315305) h243 (by decide +kernel)
  have h648 : (3 : ZMod 15935191) ^ 648 = 2101874 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 324) (r := 7546458) (b := 0) (s := 2101874) h324 (by decide +kernel)
  have h778 : (3 : ZMod 15935191) ^ 778 = 14244126 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 389) (r := 3078071) (b := 0) (s := 14244126) h389 (by decide +kernel)
  have h972 : (3 : ZMod 15935191) ^ 972 = 5963184 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 486) (r := 13315305) (b := 0) (s := 5963184) h486 (by decide +kernel)
  have h1296 : (3 : ZMod 15935191) ^ 1296 = 1959036 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 648) (r := 2101874) (b := 0) (s := 1959036) h648 (by decide +kernel)
  have h1556 : (3 : ZMod 15935191) ^ 1556 = 3327747 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 778) (r := 14244126) (b := 0) (s := 3327747) h778 (by decide +kernel)
  have h1945 : (3 : ZMod 15935191) ^ 1945 = 12307574 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 972) (r := 5963184) (b := 1) (s := 12307574) h972 (by decide +kernel)
  have h2593 : (3 : ZMod 15935191) ^ 2593 = 3816950 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 1296) (r := 1959036) (b := 1) (s := 3816950) h1296 (by decide +kernel)
  have h3112 : (3 : ZMod 15935191) ^ 3112 = 10008806 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 1556) (r := 3327747) (b := 0) (s := 10008806) h1556 (by decide +kernel)
  have h3890 : (3 : ZMod 15935191) ^ 3890 = 5667069 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 1945) (r := 12307574) (b := 0) (s := 5667069) h1945 (by decide +kernel)
  have h5187 : (3 : ZMod 15935191) ^ 5187 = 9134453 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 2593) (r := 3816950) (b := 1) (s := 9134453) h2593 (by decide +kernel)
  have h6224 : (3 : ZMod 15935191) ^ 6224 = 1768720 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 3112) (r := 10008806) (b := 0) (s := 1768720) h3112 (by decide +kernel)
  have h7780 : (3 : ZMod 15935191) ^ 7780 = 14590889 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 3890) (r := 5667069) (b := 0) (s := 14590889) h3890 (by decide +kernel)
  have h10374 : (3 : ZMod 15935191) ^ 10374 = 9884491 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 5187) (r := 9134453) (b := 0) (s := 9884491) h5187 (by decide +kernel)
  have h12449 : (3 : ZMod 15935191) ^ 12449 = 899795 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 6224) (r := 1768720) (b := 1) (s := 899795) h6224 (by decide +kernel)
  have h15561 : (3 : ZMod 15935191) ^ 15561 = 4789974 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 7780) (r := 14590889) (b := 1) (s := 4789974) h7780 (by decide +kernel)
  have h20748 : (3 : ZMod 15935191) ^ 20748 = 12584219 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 10374) (r := 9884491) (b := 0) (s := 12584219) h10374 (by decide +kernel)
  have h24898 : (3 : ZMod 15935191) ^ 24898 = 11792888 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 12449) (r := 899795) (b := 0) (s := 11792888) h12449 (by decide +kernel)
  have h31123 : (3 : ZMod 15935191) ^ 31123 = 5163640 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 15561) (r := 4789974) (b := 1) (s := 5163640) h15561 (by decide +kernel)
  have h41497 : (3 : ZMod 15935191) ^ 41497 = 14389970 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 20748) (r := 12584219) (b := 1) (s := 14389970) h20748 (by decide +kernel)
  have h49797 : (3 : ZMod 15935191) ^ 49797 = 1277251 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 24898) (r := 11792888) (b := 1) (s := 1277251) h24898 (by decide +kernel)
  have h62246 : (3 : ZMod 15935191) ^ 62246 = 2153434 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 31123) (r := 5163640) (b := 0) (s := 2153434) h31123 (by decide +kernel)
  have h82995 : (3 : ZMod 15935191) ^ 82995 = 498967 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 41497) (r := 14389970) (b := 1) (s := 498967) h41497 (by decide +kernel)
  have h99594 : (3 : ZMod 15935191) ^ 99594 = 4938376 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 49797) (r := 1277251) (b := 0) (s := 4938376) h49797 (by decide +kernel)
  have h124493 : (3 : ZMod 15935191) ^ 124493 = 13854293 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 62246) (r := 2153434) (b := 1) (s := 13854293) h62246 (by decide +kernel)
  have h165991 : (3 : ZMod 15935191) ^ 165991 = 5863906 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 82995) (r := 498967) (b := 1) (s := 5863906) h82995 (by decide +kernel)
  have h199189 : (3 : ZMod 15935191) ^ 199189 = 3780704 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 99594) (r := 4938376) (b := 1) (s := 3780704) h99594 (by decide +kernel)
  have h248987 : (3 : ZMod 15935191) ^ 248987 = 9885630 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 124493) (r := 13854293) (b := 1) (s := 9885630) h124493 (by decide +kernel)
  have h331983 : (3 : ZMod 15935191) ^ 331983 = 8625446 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 165991) (r := 5863906) (b := 1) (s := 8625446) h165991 (by decide +kernel)
  have h398379 : (3 : ZMod 15935191) ^ 398379 = 15411196 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 199189) (r := 3780704) (b := 1) (s := 15411196) h199189 (by decide +kernel)
  have h497974 : (3 : ZMod 15935191) ^ 497974 = 14327155 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 248987) (r := 9885630) (b := 0) (s := 14327155) h248987 (by decide +kernel)
  have h663966 : (3 : ZMod 15935191) ^ 663966 = 3346970 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 331983) (r := 8625446) (b := 0) (s := 3346970) h331983 (by decide +kernel)
  have h796759 : (3 : ZMod 15935191) ^ 796759 = 6322094 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 398379) (r := 15411196) (b := 1) (s := 6322094) h398379 (by decide +kernel)
  have h995949 : (3 : ZMod 15935191) ^ 995949 = 8677133 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 497974) (r := 14327155) (b := 1) (s := 8677133) h497974 (by decide +kernel)
  have h1327932 : (3 : ZMod 15935191) ^ 1327932 = 7935765 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 663966) (r := 3346970) (b := 0) (s := 7935765) h663966 (by decide +kernel)
  have h1593519 : (3 : ZMod 15935191) ^ 1593519 = 10157886 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 796759) (r := 6322094) (b := 1) (s := 10157886) h796759 (by decide +kernel)
  have h1991898 : (3 : ZMod 15935191) ^ 1991898 = 6958441 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 995949) (r := 8677133) (b := 0) (s := 6958441) h995949 (by decide +kernel)
  have h2655865 : (3 : ZMod 15935191) ^ 2655865 = 7872103 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 1327932) (r := 7935765) (b := 1) (s := 7872103) h1327932 (by decide +kernel)
  have h3187038 : (3 : ZMod 15935191) ^ 3187038 = 7531683 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 1593519) (r := 10157886) (b := 0) (s := 7531683) h1593519 (by decide +kernel)
  have h3983797 : (3 : ZMod 15935191) ^ 3983797 = 15871529 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 1991898) (r := 6958441) (b := 1) (s := 15871529) h1991898 (by decide +kernel)
  have h5311730 : (3 : ZMod 15935191) ^ 5311730 = 7872102 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 2655865) (r := 7872103) (b := 0) (s := 7872102) h2655865 (by decide +kernel)
  have h7967595 : (3 : ZMod 15935191) ^ 7967595 = 15935190 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 3983797) (r := 15871529) (b := 1) (s := 15935190) h3983797 (by decide +kernel)
  have h15935190 : (3 : ZMod 15935191) ^ 15935190 = 1 :=
    modular_pow_step (p := 15935191) (a := 3) (e := 7967595) (r := 15935190) (b := 0) (s := 1) h7967595 (by decide +kernel)
  apply lucas_primality 15935191 3 (by simpa using h15935190)
  intro q hq hqd
  rw [show 15935191 - 1 = (2 * 3 * 5 * 531173 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_3, Nat.dvd_prime prime_5, Nat.dvd_prime prime_531173, hq.ne_one, false_or] at hqd
  rcases hqd with (((rfl | rfl) | rfl) | rfl)
  · change (3 : ZMod 15935191) ^ 7967595 ≠ 1
    rw [h7967595]
    decide +kernel
  · change (3 : ZMod 15935191) ^ 5311730 ≠ 1
    rw [h5311730]
    decide +kernel
  · change (3 : ZMod 15935191) ^ 3187038 ≠ 1
    rw [h3187038]
    decide +kernel
  · change (3 : ZMod 15935191) ^ 30 ≠ 1
    rw [h30]
    decide +kernel

lemma prime_1121008816469 : Nat.Prime 1121008816469 := by
  have h0 : (2 : ZMod 1121008816469) ^ 0 = 1 := by simp
  have h1 : (2 : ZMod 1121008816469) ^ 1 = 2 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 0) (r := 1) (b := 1) (s := 2) h0 (by decide +kernel)
  have h2 : (2 : ZMod 1121008816469) ^ 2 = 4 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1) (r := 2) (b := 0) (s := 4) h1 (by decide +kernel)
  have h3 : (2 : ZMod 1121008816469) ^ 3 = 8 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1) (r := 2) (b := 1) (s := 8) h1 (by decide +kernel)
  have h4 : (2 : ZMod 1121008816469) ^ 4 = 16 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 2) (r := 4) (b := 0) (s := 16) h2 (by decide +kernel)
  have h5 : (2 : ZMod 1121008816469) ^ 5 = 32 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 2) (r := 4) (b := 1) (s := 32) h2 (by decide +kernel)
  have h6 : (2 : ZMod 1121008816469) ^ 6 = 64 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 3) (r := 8) (b := 0) (s := 64) h3 (by decide +kernel)
  have h8 : (2 : ZMod 1121008816469) ^ 8 = 256 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 4) (r := 16) (b := 0) (s := 256) h4 (by decide +kernel)
  have h10 : (2 : ZMod 1121008816469) ^ 10 = 1024 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 5) (r := 32) (b := 0) (s := 1024) h5 (by decide +kernel)
  have h12 : (2 : ZMod 1121008816469) ^ 12 = 4096 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 6) (r := 64) (b := 0) (s := 4096) h6 (by decide +kernel)
  have h16 : (2 : ZMod 1121008816469) ^ 16 = 65536 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 8) (r := 256) (b := 0) (s := 65536) h8 (by decide +kernel)
  have h17 : (2 : ZMod 1121008816469) ^ 17 = 131072 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 8) (r := 256) (b := 1) (s := 131072) h8 (by decide +kernel)
  have h20 : (2 : ZMod 1121008816469) ^ 20 = 1048576 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 10) (r := 1024) (b := 0) (s := 1048576) h10 (by decide +kernel)
  have h24 : (2 : ZMod 1121008816469) ^ 24 = 16777216 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 12) (r := 4096) (b := 0) (s := 16777216) h12 (by decide +kernel)
  have h32 : (2 : ZMod 1121008816469) ^ 32 = 4294967296 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 16) (r := 65536) (b := 0) (s := 4294967296) h16 (by decide +kernel)
  have h34 : (2 : ZMod 1121008816469) ^ 34 = 17179869184 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 17) (r := 131072) (b := 0) (s := 17179869184) h17 (by decide +kernel)
  have h40 : (2 : ZMod 1121008816469) ^ 40 = 1099511627776 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 20) (r := 1048576) (b := 0) (s := 1099511627776) h20 (by decide +kernel)
  have h48 : (2 : ZMod 1121008816469) ^ 48 = 101763776937 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 24) (r := 16777216) (b := 0) (s := 101763776937) h24 (by decide +kernel)
  have h65 : (2 : ZMod 1121008816469) ^ 65 = 618872338302 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 32) (r := 4294967296) (b := 1) (s := 618872338302) h32 (by decide +kernel)
  have h68 : (2 : ZMod 1121008816469) ^ 68 = 466943440540 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 34) (r := 17179869184) (b := 0) (s := 466943440540) h34 (by decide +kernel)
  have h81 : (2 : ZMod 1121008816469) ^ 81 = 318583111452 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 40) (r := 1099511627776) (b := 1) (s := 318583111452) h40 (by decide +kernel)
  have h97 : (2 : ZMod 1121008816469) ^ 97 = 994594199616 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 48) (r := 101763776937) (b := 1) (s := 994594199616) h48 (by decide +kernel)
  have h130 : (2 : ZMod 1121008816469) ^ 130 = 160688399447 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 65) (r := 618872338302) (b := 0) (s := 160688399447) h65 (by decide +kernel)
  have h137 : (2 : ZMod 1121008816469) ^ 137 = 389956432774 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 68) (r := 466943440540) (b := 1) (s := 389956432774) h68 (by decide +kernel)
  have h163 : (2 : ZMod 1121008816469) ^ 163 = 528775246673 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 81) (r := 318583111452) (b := 1) (s := 528775246673) h81 (by decide +kernel)
  have h194 : (2 : ZMod 1121008816469) ^ 194 = 653040021835 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 97) (r := 994594199616) (b := 0) (s := 653040021835) h97 (by decide +kernel)
  have h261 : (2 : ZMod 1121008816469) ^ 261 = 143945708543 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 130) (r := 160688399447) (b := 1) (s := 143945708543) h130 (by decide +kernel)
  have h274 : (2 : ZMod 1121008816469) ^ 274 = 1022978275337 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 137) (r := 389956432774) (b := 0) (s := 1022978275337) h137 (by decide +kernel)
  have h326 : (2 : ZMod 1121008816469) ^ 326 = 94125456337 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 163) (r := 528775246673) (b := 0) (s := 94125456337) h163 (by decide +kernel)
  have h388 : (2 : ZMod 1121008816469) ^ 388 = 918707893937 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 194) (r := 653040021835) (b := 0) (s := 918707893937) h194 (by decide +kernel)
  have h522 : (2 : ZMod 1121008816469) ^ 522 = 264275378749 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 261) (r := 143945708543) (b := 0) (s := 264275378749) h261 (by decide +kernel)
  have h549 : (2 : ZMod 1121008816469) ^ 549 = 79409005888 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 274) (r := 1022978275337) (b := 1) (s := 79409005888) h274 (by decide +kernel)
  have h653 : (2 : ZMod 1121008816469) ^ 653 = 615030128722 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 326) (r := 94125456337) (b := 1) (s := 615030128722) h326 (by decide +kernel)
  have h776 : (2 : ZMod 1121008816469) ^ 776 = 230807015167 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 388) (r := 918707893937) (b := 0) (s := 230807015167) h388 (by decide +kernel)
  have h1044 : (2 : ZMod 1121008816469) ^ 1044 = 831537608621 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 522) (r := 264275378749) (b := 0) (s := 831537608621) h522 (by decide +kernel)
  have h1099 : (2 : ZMod 1121008816469) ^ 1099 = 781890845892 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 549) (r := 79409005888) (b := 1) (s := 781890845892) h549 (by decide +kernel)
  have h1306 : (2 : ZMod 1121008816469) ^ 1306 = 845211310207 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 653) (r := 615030128722) (b := 0) (s := 845211310207) h653 (by decide +kernel)
  have h1553 : (2 : ZMod 1121008816469) ^ 1553 = 592451103369 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 776) (r := 230807015167) (b := 1) (s := 592451103369) h776 (by decide +kernel)
  have h2088 : (2 : ZMod 1121008816469) ^ 2088 = 545806976464 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1044) (r := 831537608621) (b := 0) (s := 545806976464) h1044 (by decide +kernel)
  have h2198 : (2 : ZMod 1121008816469) ^ 2198 = 341627157752 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1099) (r := 781890845892) (b := 0) (s := 341627157752) h1099 (by decide +kernel)
  have h2613 : (2 : ZMod 1121008816469) ^ 2613 = 542553629570 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1306) (r := 845211310207) (b := 1) (s := 542553629570) h1306 (by decide +kernel)
  have h3107 : (2 : ZMod 1121008816469) ^ 3107 = 24396620276 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1553) (r := 592451103369) (b := 1) (s := 24396620276) h1553 (by decide +kernel)
  have h4176 : (2 : ZMod 1121008816469) ^ 4176 = 303337939735 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 2088) (r := 545806976464) (b := 0) (s := 303337939735) h2088 (by decide +kernel)
  have h4396 : (2 : ZMod 1121008816469) ^ 4396 = 387016919653 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 2198) (r := 341627157752) (b := 0) (s := 387016919653) h2198 (by decide +kernel)
  have h5227 : (2 : ZMod 1121008816469) ^ 5227 = 288730420648 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 2613) (r := 542553629570) (b := 1) (s := 288730420648) h2613 (by decide +kernel)
  have h6215 : (2 : ZMod 1121008816469) ^ 6215 = 1044818444163 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 3107) (r := 24396620276) (b := 1) (s := 1044818444163) h3107 (by decide +kernel)
  have h8352 : (2 : ZMod 1121008816469) ^ 8352 = 637890854753 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 4176) (r := 303337939735) (b := 0) (s := 637890854753) h4176 (by decide +kernel)
  have h8793 : (2 : ZMod 1121008816469) ^ 8793 = 425209930951 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 4396) (r := 387016919653) (b := 1) (s := 425209930951) h4396 (by decide +kernel)
  have h10455 : (2 : ZMod 1121008816469) ^ 10455 = 875128238246 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 5227) (r := 288730420648) (b := 1) (s := 875128238246) h5227 (by decide +kernel)
  have h12431 : (2 : ZMod 1121008816469) ^ 12431 = 760201246281 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 6215) (r := 1044818444163) (b := 1) (s := 760201246281) h6215 (by decide +kernel)
  have h16704 : (2 : ZMod 1121008816469) ^ 16704 = 736472219199 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 8352) (r := 637890854753) (b := 0) (s := 736472219199) h8352 (by decide +kernel)
  have h17587 : (2 : ZMod 1121008816469) ^ 17587 = 1094331020193 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 8793) (r := 425209930951) (b := 1) (s := 1094331020193) h8793 (by decide +kernel)
  have h20911 : (2 : ZMod 1121008816469) ^ 20911 = 276881770245 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 10455) (r := 875128238246) (b := 1) (s := 276881770245) h10455 (by decide +kernel)
  have h24862 : (2 : ZMod 1121008816469) ^ 24862 = 967736988091 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 12431) (r := 760201246281) (b := 0) (s := 967736988091) h12431 (by decide +kernel)
  have h33408 : (2 : ZMod 1121008816469) ^ 33408 = 314613454572 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 16704) (r := 736472219199) (b := 0) (s := 314613454572) h16704 (by decide +kernel)
  have h35174 : (2 : ZMod 1121008816469) ^ 35174 = 120856908739 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 17587) (r := 1094331020193) (b := 0) (s := 120856908739) h17587 (by decide +kernel)
  have h41822 : (2 : ZMod 1121008816469) ^ 41822 = 22067068671 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 20911) (r := 276881770245) (b := 0) (s := 22067068671) h20911 (by decide +kernel)
  have h49724 : (2 : ZMod 1121008816469) ^ 49724 = 1008894907138 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 24862) (r := 967736988091) (b := 0) (s := 1008894907138) h24862 (by decide +kernel)
  have h66817 : (2 : ZMod 1121008816469) ^ 66817 = 40696933457 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 33408) (r := 314613454572) (b := 1) (s := 40696933457) h33408 (by decide +kernel)
  have h70348 : (2 : ZMod 1121008816469) ^ 70348 = 247146266012 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 35174) (r := 120856908739) (b := 0) (s := 247146266012) h35174 (by decide +kernel)
  have h83644 : (2 : ZMod 1121008816469) ^ 83644 = 1095737467536 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 41822) (r := 22067068671) (b := 0) (s := 1095737467536) h41822 (by decide +kernel)
  have h99449 : (2 : ZMod 1121008816469) ^ 99449 = 918863621477 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 49724) (r := 1008894907138) (b := 1) (s := 918863621477) h49724 (by decide +kernel)
  have h133634 : (2 : ZMod 1121008816469) ^ 133634 = 226828597467 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 66817) (r := 40696933457) (b := 0) (s := 226828597467) h66817 (by decide +kernel)
  have h167288 : (2 : ZMod 1121008816469) ^ 167288 = 32536353589 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 83644) (r := 1095737467536) (b := 0) (s := 32536353589) h83644 (by decide +kernel)
  have h198898 : (2 : ZMod 1121008816469) ^ 198898 = 726772104006 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 99449) (r := 918863621477) (b := 0) (s := 726772104006) h99449 (by decide +kernel)
  have h267269 : (2 : ZMod 1121008816469) ^ 267269 = 298876795314 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 133634) (r := 226828597467) (b := 1) (s := 298876795314) h133634 (by decide +kernel)
  have h334576 : (2 : ZMod 1121008816469) ^ 334576 = 609503002109 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 167288) (r := 32536353589) (b := 0) (s := 609503002109) h167288 (by decide +kernel)
  have h397796 : (2 : ZMod 1121008816469) ^ 397796 = 190899732336 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 198898) (r := 726772104006) (b := 0) (s := 190899732336) h198898 (by decide +kernel)
  have h534538 : (2 : ZMod 1121008816469) ^ 534538 = 1021858810855 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 267269) (r := 298876795314) (b := 0) (s := 1021858810855) h267269 (by decide +kernel)
  have h669153 : (2 : ZMod 1121008816469) ^ 669153 = 378011195578 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 334576) (r := 609503002109) (b := 1) (s := 378011195578) h334576 (by decide +kernel)
  have h795592 : (2 : ZMod 1121008816469) ^ 795592 = 780504343851 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 397796) (r := 190899732336) (b := 0) (s := 780504343851) h397796 (by decide +kernel)
  have h1069077 : (2 : ZMod 1121008816469) ^ 1069077 = 233870844142 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 534538) (r := 1021858810855) (b := 1) (s := 233870844142) h534538 (by decide +kernel)
  have h1338307 : (2 : ZMod 1121008816469) ^ 1338307 = 934470833738 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 669153) (r := 378011195578) (b := 1) (s := 934470833738) h669153 (by decide +kernel)
  have h1591184 : (2 : ZMod 1121008816469) ^ 1591184 = 110920587427 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 795592) (r := 780504343851) (b := 0) (s := 110920587427) h795592 (by decide +kernel)
  have h2138154 : (2 : ZMod 1121008816469) ^ 2138154 = 350306239140 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1069077) (r := 233870844142) (b := 0) (s := 350306239140) h1069077 (by decide +kernel)
  have h2676614 : (2 : ZMod 1121008816469) ^ 2676614 = 13682025079 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1338307) (r := 934470833738) (b := 0) (s := 13682025079) h1338307 (by decide +kernel)
  have h3182369 : (2 : ZMod 1121008816469) ^ 3182369 = 419165855359 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1591184) (r := 110920587427) (b := 1) (s := 419165855359) h1591184 (by decide +kernel)
  have h4276309 : (2 : ZMod 1121008816469) ^ 4276309 = 477122232393 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 2138154) (r := 350306239140) (b := 1) (s := 477122232393) h2138154 (by decide +kernel)
  have h5353228 : (2 : ZMod 1121008816469) ^ 5353228 = 947924209369 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 2676614) (r := 13682025079) (b := 0) (s := 947924209369) h2676614 (by decide +kernel)
  have h6364739 : (2 : ZMod 1121008816469) ^ 6364739 = 325292182172 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 3182369) (r := 419165855359) (b := 1) (s := 325292182172) h3182369 (by decide +kernel)
  have h8552618 : (2 : ZMod 1121008816469) ^ 8552618 = 618544682026 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 4276309) (r := 477122232393) (b := 0) (s := 618544682026) h4276309 (by decide +kernel)
  have h10706456 : (2 : ZMod 1121008816469) ^ 10706456 = 156707510954 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 5353228) (r := 947924209369) (b := 0) (s := 156707510954) h5353228 (by decide +kernel)
  have h12729478 : (2 : ZMod 1121008816469) ^ 12729478 = 360182930117 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 6364739) (r := 325292182172) (b := 0) (s := 360182930117) h6364739 (by decide +kernel)
  have h17105237 : (2 : ZMod 1121008816469) ^ 17105237 = 814496801402 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 8552618) (r := 618544682026) (b := 1) (s := 814496801402) h8552618 (by decide +kernel)
  have h21412912 : (2 : ZMod 1121008816469) ^ 21412912 = 212727137930 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 10706456) (r := 156707510954) (b := 0) (s := 212727137930) h10706456 (by decide +kernel)
  have h25458957 : (2 : ZMod 1121008816469) ^ 25458957 = 83415105595 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 12729478) (r := 360182930117) (b := 1) (s := 83415105595) h12729478 (by decide +kernel)
  have h34210474 : (2 : ZMod 1121008816469) ^ 34210474 = 807642777607 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 17105237) (r := 814496801402) (b := 0) (s := 807642777607) h17105237 (by decide +kernel)
  have h42825825 : (2 : ZMod 1121008816469) ^ 42825825 = 494200848299 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 21412912) (r := 212727137930) (b := 1) (s := 494200848299) h21412912 (by decide +kernel)
  have h50917914 : (2 : ZMod 1121008816469) ^ 50917914 = 815023595374 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 25458957) (r := 83415105595) (b := 0) (s := 815023595374) h25458957 (by decide +kernel)
  have h68420948 : (2 : ZMod 1121008816469) ^ 68420948 = 1095459830835 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 34210474) (r := 807642777607) (b := 0) (s := 1095459830835) h34210474 (by decide +kernel)
  have h85651651 : (2 : ZMod 1121008816469) ^ 85651651 = 720314750018 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 42825825) (r := 494200848299) (b := 1) (s := 720314750018) h42825825 (by decide +kernel)
  have h101835829 : (2 : ZMod 1121008816469) ^ 101835829 = 1101401055203 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 50917914) (r := 815023595374) (b := 1) (s := 1101401055203) h50917914 (by decide +kernel)
  have h136841896 : (2 : ZMod 1121008816469) ^ 136841896 = 265850447397 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 68420948) (r := 1095459830835) (b := 0) (s := 265850447397) h68420948 (by decide +kernel)
  have h171303303 : (2 : ZMod 1121008816469) ^ 171303303 = 338730055187 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 85651651) (r := 720314750018) (b := 1) (s := 338730055187) h85651651 (by decide +kernel)
  have h203671659 : (2 : ZMod 1121008816469) ^ 203671659 = 164437348465 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 101835829) (r := 1101401055203) (b := 1) (s := 164437348465) h101835829 (by decide +kernel)
  have h273683793 : (2 : ZMod 1121008816469) ^ 273683793 = 611414614663 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 136841896) (r := 265850447397) (b := 1) (s := 611414614663) h136841896 (by decide +kernel)
  have h342606606 : (2 : ZMod 1121008816469) ^ 342606606 = 1085934710214 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 171303303) (r := 338730055187) (b := 0) (s := 1085934710214) h171303303 (by decide +kernel)
  have h407343319 : (2 : ZMod 1121008816469) ^ 407343319 = 433285499705 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 203671659) (r := 164437348465) (b := 1) (s := 433285499705) h203671659 (by decide +kernel)
  have h547367586 : (2 : ZMod 1121008816469) ^ 547367586 = 461406401976 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 273683793) (r := 611414614663) (b := 0) (s := 461406401976) h273683793 (by decide +kernel)
  have h685213213 : (2 : ZMod 1121008816469) ^ 685213213 = 9648493382 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 342606606) (r := 1085934710214) (b := 1) (s := 9648493382) h342606606 (by decide +kernel)
  have h814686639 : (2 : ZMod 1121008816469) ^ 814686639 = 807545972849 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 407343319) (r := 433285499705) (b := 1) (s := 807545972849) h407343319 (by decide +kernel)
  have h1094735172 : (2 : ZMod 1121008816469) ^ 1094735172 = 41185382055 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 547367586) (r := 461406401976) (b := 0) (s := 41185382055) h547367586 (by decide +kernel)
  have h1370426426 : (2 : ZMod 1121008816469) ^ 1370426426 = 696754360092 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 685213213) (r := 9648493382) (b := 0) (s := 696754360092) h685213213 (by decide +kernel)
  have h1629373279 : (2 : ZMod 1121008816469) ^ 1629373279 = 931108953966 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 814686639) (r := 807545972849) (b := 1) (s := 931108953966) h814686639 (by decide +kernel)
  have h2189470344 : (2 : ZMod 1121008816469) ^ 2189470344 = 331074408748 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1094735172) (r := 41185382055) (b := 0) (s := 331074408748) h1094735172 (by decide +kernel)
  have h2740852852 : (2 : ZMod 1121008816469) ^ 2740852852 = 894531478151 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1370426426) (r := 696754360092) (b := 0) (s := 894531478151) h1370426426 (by decide +kernel)
  have h3258746559 : (2 : ZMod 1121008816469) ^ 3258746559 = 640407455090 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 1629373279) (r := 931108953966) (b := 1) (s := 640407455090) h1629373279 (by decide +kernel)
  have h4378940689 : (2 : ZMod 1121008816469) ^ 4378940689 = 259081998569 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 2189470344) (r := 331074408748) (b := 1) (s := 259081998569) h2189470344 (by decide +kernel)
  have h6517493119 : (2 : ZMod 1121008816469) ^ 6517493119 = 944184259352 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 3258746559) (r := 640407455090) (b := 1) (s := 944184259352) h3258746559 (by decide +kernel)
  have h8757881378 : (2 : ZMod 1121008816469) ^ 8757881378 = 210580132550 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 4378940689) (r := 259081998569) (b := 0) (s := 210580132550) h4378940689 (by decide +kernel)
  have h13034986238 : (2 : ZMod 1121008816469) ^ 13034986238 = 287786396658 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 6517493119) (r := 944184259352) (b := 0) (s := 287786396658) h6517493119 (by decide +kernel)
  have h17515762757 : (2 : ZMod 1121008816469) ^ 17515762757 = 1094798275161 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 8757881378) (r := 210580132550) (b := 1) (s := 1094798275161) h8757881378 (by decide +kernel)
  have h26069972476 : (2 : ZMod 1121008816469) ^ 26069972476 = 911913399837 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 13034986238) (r := 287786396658) (b := 0) (s := 911913399837) h13034986238 (by decide +kernel)
  have h35031525514 : (2 : ZMod 1121008816469) ^ 35031525514 = 564168082735 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 17515762757) (r := 1094798275161) (b := 0) (s := 564168082735) h17515762757 (by decide +kernel)
  have h70063051029 : (2 : ZMod 1121008816469) ^ 70063051029 = 1042994636904 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 35031525514) (r := 564168082735) (b := 1) (s := 1042994636904) h35031525514 (by decide +kernel)
  have h140126102058 : (2 : ZMod 1121008816469) ^ 140126102058 = 717612014529 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 70063051029) (r := 1042994636904) (b := 0) (s := 717612014529) h70063051029 (by decide +kernel)
  have h280252204117 : (2 : ZMod 1121008816469) ^ 280252204117 = 314215212588 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 140126102058) (r := 717612014529) (b := 1) (s := 314215212588) h140126102058 (by decide +kernel)
  have h560504408234 : (2 : ZMod 1121008816469) ^ 560504408234 = 1121008816468 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 280252204117) (r := 314215212588) (b := 0) (s := 1121008816468) h280252204117 (by decide +kernel)
  have h1121008816468 : (2 : ZMod 1121008816469) ^ 1121008816468 = 1 :=
    modular_pow_step (p := 1121008816469) (a := 2) (e := 560504408234) (r := 1121008816468) (b := 0) (s := 1) h560504408234 (by decide +kernel)
  apply lucas_primality 1121008816469 2 (by simpa using h1121008816468)
  intro q hq hqd
  rw [show 1121008816469 - 1 = (2 * 2 * 43 * 409 * 15935191 : ℕ) by norm_num] at hqd
  simp only [hq.dvd_mul, Nat.dvd_prime prime_2, Nat.dvd_prime prime_43, Nat.dvd_prime prime_409, Nat.dvd_prime prime_15935191, hq.ne_one, false_or] at hqd
  rcases hqd with ((((rfl | rfl) | rfl) | rfl) | rfl)
  · change (2 : ZMod 1121008816469) ^ 560504408234 ≠ 1
    rw [h560504408234]
    decide +kernel
  · change (2 : ZMod 1121008816469) ^ 560504408234 ≠ 1
    rw [h560504408234]
    decide +kernel
  · change (2 : ZMod 1121008816469) ^ 26069972476 ≠ 1
    rw [h26069972476]
    decide +kernel
  · change (2 : ZMod 1121008816469) ^ 2740852852 ≠ 1
    rw [h2740852852]
    decide +kernel
  · change (2 : ZMod 1121008816469) ^ 70348 ≠ 1
    rw [h70348]
    decide +kernel


lemma monic_norm_eval_four_gt_one (Q : ℂ[X]) (hQ : Q.Monic)
    (hdeg : 0 < Q.natDegree) (hroot : ∀ z ∈ Q.roots, ‖z‖ < 2) :
    1 < ‖Q.eval 4‖ := by
  have hsplit := IsAlgClosed.splits Q
  rw [hsplit.eval_eq_prod_roots_of_monic hQ]
  apply one_lt_norm_multiset_prod
  · have hcard : 0 < (Q.roots.map (fun z => (4 : ℂ) - z)).card := by
      rw [Multiset.card_map, ← hsplit.natDegree_eq_card_roots]
      exact hdeg
    intro hh
    simp [hh] at hcard
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hz
    have hh := norm_sub_norm_le (4 : ℂ) a
    have hr := hroot a ha
    norm_num at hh
    linarith

/-- A simple prime-evaluation criterion with enough room outside the root disk. -/
lemma irreducible_of_eval_four_prime (P : ℤ[X]) (p : ℕ)
    (hP : P.Monic) (hp : Nat.Prime p) (heval : P.eval 4 = p)
    (hroots : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z‖ < 2) :
    Irreducible P := by
  have hP1 : P ≠ 1 := by
    intro h
    have hh := heval
    rw [h] at hh
    norm_num only [eval_one] at hh
    exact hp.ne_one (by exact_mod_cast hh.symm)
  have hfactor (Q : ℤ[X]) (hQ : Q.Monic) (hd : Q ∣ P) (hne : Q ≠ 1) :
      1 < (Q.eval 4).natAbs := by
    have hQr : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖z‖ < 2 := by
      intro z hz
      apply hroots z
      apply (mem_roots (hP.map _).ne_zero).mpr
      have hh := (mem_roots (hQ.map _).ne_zero).mp hz
      have hv := eval_dvd (x := z) (map_dvd (Int.castRingHom ℂ) hd)
      change (Q.map (Int.castRingHom ℂ)).eval z = 0 at hh
      rwa [hh, zero_dvd_iff] at hv
    have hdeg : 0 < Q.natDegree := hQ.natDegree_pos_of_not_isUnit (by simpa [hQ.isUnit_iff])
    have hh := monic_norm_eval_four_gt_one (Q.map (Int.castRingHom ℂ)) (hQ.map _)
      (by rwa [hQ.natDegree_map]) hQr
    have he : (Q.map (Int.castRingHom ℂ)).eval 4 = ((Q.eval 4 : ℤ) : ℂ) := by
      rw [eval_map]
      exact eval₂_at_apply (Int.castRingHom ℂ) 4
    rw [he, Complex.norm_intCast] at hh
    have hZ : (1 : ℤ) < |Q.eval 4| := by exact_mod_cast hh
    rw [← Int.natCast_natAbs] at hZ
    exact_mod_cast hZ
  apply (irreducible_of_monic hP hP1).mpr
  intro Q R hQ hR he
  by_cases hQ1 : Q = 1
  · exact Or.inl hQ1
  by_cases hR1 : R = 1
  · exact Or.inr hR1
  have hq := hfactor Q hQ (by rw [← he]; exact dvd_mul_right _ _) hQ1
  have hr := hfactor R hR (by rw [← he]; exact dvd_mul_left _ _) hR1
  have hv := congrArg (fun F : ℤ[X] => (F.eval 4).natAbs) he
  dsimp only at hv
  rw [eval_mul, Int.natAbs_mul, heval, Int.natAbs_natCast] at hv
  have hd : (Q.eval 4).natAbs ∣ p := ⟨(R.eval 4).natAbs, hv.symm⟩
  rcases (Nat.dvd_prime hp).mp hd with h1 | hpeq
  · omega
  · have hp0 := hp.pos
    nlinarith

def squareWord : List ℕ := [1,1,1,1,1,0,1,0,1,1,1,1,1,0,0,0,1,1,0,0,1]
noncomputable def squarePoly : ℤ[X] := digitPoly squareWord

lemma squarePoly_monic : squarePoly.Monic :=
  (digitPoly_isMonicOfDegree squareWord (by decide) (by decide)).monic

lemma squarePoly_degree : squarePoly.natDegree = 20 := by
  simpa [squarePoly, squareWord] using
    (digitPoly_isMonicOfDegree squareWord (by decide) (by decide)).natDegree_eq

lemma squarePoly_roots (z : ℂ) (hz : z ∈ (squarePoly.map (Int.castRingHom ℂ)).roots) :
    ‖z‖ < 2 := by
  have hh := (mem_roots (squarePoly_monic.map _).ne_zero).mp hz
  change (squarePoly.map (Int.castRingHom ℂ)).eval z = 0 at hh
  rw [squarePoly, eval_map_digitPoly_complex] at hh
  have he : squareWord = squareWord.dropLast ++ [1] := by decide
  rw [he] at hh
  have hb := Erdos406Newman.upper_root_bound z squareWord.dropLast (by decide) hh
  have hn := norm_nonneg z
  nlinarith

lemma squarePoly_eval_four : squarePoly.eval 4 = (1121008816469 : ℕ) := by
  norm_num [squarePoly, squareWord, digitPoly, Nat.ofDigits]

lemma squarePoly_irreducible : Irreducible squarePoly :=
  irreducible_of_eval_four_prime squarePoly 1121008816469 squarePoly_monic
    prime_1121008816469 squarePoly_eval_four squarePoly_roots

lemma squarePoly_eval_three : squarePoly.eval 3 = (60496 : ℤ)^2 := by
  norm_num [squarePoly, squareWord, digitPoly, Nat.ofDigits]

lemma squarePoly_simple_one : SimpleOne squarePoly := by
  apply (simple_one_iff_eval_one_mod_four squarePoly ?_).mpr
  · norm_num [squarePoly, squareWord, digitPoly, Nat.ofDigits]
  · rw [squarePoly_eval_three]
    norm_num

lemma squarePoly_binary : Erdos406ReciprocalFlip.Binary squarePoly := by
  intro i
  exact Erdos406ReciprocalCandidate.binary_digitPoly squareWord (by decide) i

lemma squarePoly_digit_representation : squarePoly = digitPoly (Nat.digits 3 (60496^2)) := by
  have he : Nat.digits 3 (60496^2) = squareWord := by decide +kernel
  rw [he]
  rfl

lemma squarePoly_not_power_of_two : ¬ (60496^2 : ℕ).isPowerOfTwo := by
  rintro ⟨k, hk⟩
  have hd : 19 ∣ (60496^2 : ℕ) := by decide +kernel
  rw [hk] at hd
  have hh := (by decide : Nat.Prime 19).dvd_of_dvd_pow hd
  norm_num at hh

/-- Irreducibility and a simple root modulo two do not by themselves rule
out square-valued binary polynomials. The square is not a power of two. -/
theorem irreducible_simple_square_example :
    squarePoly.Monic ∧ squarePoly.coeff 0 = 1 ∧ squarePoly.natDegree = 20 ∧
      Erdos406ReciprocalFlip.Binary squarePoly ∧ Irreducible squarePoly ∧
      SimpleOne squarePoly ∧ squarePoly.eval 3 = (60496 : ℤ)^2 ∧
      (60496 : ℕ) = 2^4 * (19 * 199) ∧ ¬ (60496^2 : ℕ).isPowerOfTwo := by
  exact ⟨squarePoly_monic, by norm_num [squarePoly, squareWord, digitPoly, Nat.ofDigits],
    squarePoly_degree, squarePoly_binary, squarePoly_irreducible, squarePoly_simple_one,
    squarePoly_eval_three, by norm_num, squarePoly_not_power_of_two⟩

lemma squarePoly_reverse_residue : squarePoly.reverse.eval 3 % 16 = 8 := by
  have h16 : (16 : ℤ) ∣ squarePoly.eval 3 := by rw [squarePoly_eval_three]; norm_num
  exact (simple_one_iff_reverse_eval_eight squarePoly h16).mp squarePoly_simple_one

lemma squarePoly_nonreciprocal : squarePoly.reverse ≠ squarePoly := by
  intro h
  have hh := squarePoly_reverse_residue
  rw [h, squarePoly_eval_three] at hh
  norm_num at hh

/-- The proposed factor gap is false if exact power-of-two evaluation is
weakened to square evaluation, even while retaining irreducibility, binary
coefficients, normalization, and the simple root condition. -/
theorem square_value_factor_gap_false :
    ¬ (∀ P : ℤ[X], P.Monic → Irreducible P →
      Erdos406ReciprocalFlip.Binary P → P.coeff 0 = 1 → SimpleOne P →
      IsSquare (P.eval 3) → (P.eval 3)^2 ≤ 2 * (8 : ℤ)^P.natDegree) := by
  intro h
  have hh := h squarePoly squarePoly_monic squarePoly_irreducible squarePoly_binary
    irreducible_simple_square_example.2.1 squarePoly_simple_one
    (by rw [squarePoly_eval_three]; exact ⟨60496, by ring⟩)
  rw [squarePoly_eval_three, squarePoly_degree] at hh
  norm_num at hh

#print axioms prime_1121008816469
#print axioms irreducible_of_eval_four_prime
#print axioms irreducible_simple_square_example
#print axioms squarePoly_nonreciprocal
#print axioms square_value_factor_gap_false
end Erdos406IrreducibleSquare
