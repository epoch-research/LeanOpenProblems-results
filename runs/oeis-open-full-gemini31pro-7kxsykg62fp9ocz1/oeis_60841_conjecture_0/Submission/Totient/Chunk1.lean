import Submission.Totient.Base
open Nat Finset Rat

set_option maxHeartbeats 200000000
set_option maxRecDepth 20000000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem tot_460 : totient 460 = 176 := by
  have heq : (2^2 * (5 * (23)) : ℕ) = 460 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_23]
  try omega

theorem v3_phi_460 : v3_fast (totient 460) 100 = v3_phi_list.getD 460 0 := by
  rw [tot_460]
  rfl

theorem tot_461 : totient 461 = 460 := by
  have h : totient 461 = 461 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_461 : v3_fast (totient 461) 100 = v3_phi_list.getD 461 0 := by
  rw [tot_461]
  rfl

theorem tot_462 : totient 462 = 120 := by
  have heq : (2 * (3 * (7 * (11))) : ℕ) = 462 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_11]
  try omega

theorem v3_phi_462 : v3_fast (totient 462) 100 = v3_phi_list.getD 462 0 := by
  rw [tot_462]
  rfl

theorem tot_463 : totient 463 = 462 := by
  have h : totient 463 = 463 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_463 : v3_fast (totient 463) 100 = v3_phi_list.getD 463 0 := by
  rw [tot_463]
  rfl

theorem tot_464 : totient 464 = 224 := by
  have heq : (2^4 * (29) : ℕ) = 464 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29]
  try omega

theorem v3_phi_464 : v3_fast (totient 464) 100 = v3_phi_list.getD 464 0 := by
  rw [tot_464]
  rfl

theorem tot_465 : totient 465 = 240 := by
  have heq : (3 * (5 * (31)) : ℕ) = 465 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_31]
  try omega

theorem v3_phi_465 : v3_fast (totient 465) 100 = v3_phi_list.getD 465 0 := by
  rw [tot_465]
  rfl

theorem tot_466 : totient 466 = 232 := by
  have heq : (2 * (233) : ℕ) = 466 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_233]
  try omega

theorem v3_phi_466 : v3_fast (totient 466) 100 = v3_phi_list.getD 466 0 := by
  rw [tot_466]
  rfl

theorem tot_467 : totient 467 = 466 := by
  have h : totient 467 = 467 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_467 : v3_fast (totient 467) 100 = v3_phi_list.getD 467 0 := by
  rw [tot_467]
  rfl

theorem tot_468 : totient 468 = 144 := by
  have heq : (2^2 * (3^2 * (13)) : ℕ) = 468 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13]
  try omega

theorem v3_phi_468 : v3_fast (totient 468) 100 = v3_phi_list.getD 468 0 := by
  rw [tot_468]
  rfl

theorem tot_469 : totient 469 = 396 := by
  have heq : (7 * (67) : ℕ) = 469 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_67]
  try omega

theorem v3_phi_469 : v3_fast (totient 469) 100 = v3_phi_list.getD 469 0 := by
  rw [tot_469]
  rfl

theorem tot_470 : totient 470 = 184 := by
  have heq : (2 * (5 * (47)) : ℕ) = 470 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_47]
  try omega

theorem v3_phi_470 : v3_fast (totient 470) 100 = v3_phi_list.getD 470 0 := by
  rw [tot_470]
  rfl

theorem tot_471 : totient 471 = 312 := by
  have heq : (3 * (157) : ℕ) = 471 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_157]
  try omega

theorem v3_phi_471 : v3_fast (totient 471) 100 = v3_phi_list.getD 471 0 := by
  rw [tot_471]
  rfl

theorem tot_472 : totient 472 = 232 := by
  have heq : (2^3 * (59) : ℕ) = 472 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_59]
  try omega

theorem v3_phi_472 : v3_fast (totient 472) 100 = v3_phi_list.getD 472 0 := by
  rw [tot_472]
  rfl

theorem tot_473 : totient 473 = 420 := by
  have heq : (11 * (43) : ℕ) = 473 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_43]
  try omega

theorem v3_phi_473 : v3_fast (totient 473) 100 = v3_phi_list.getD 473 0 := by
  rw [tot_473]
  rfl

theorem tot_474 : totient 474 = 156 := by
  have heq : (2 * (3 * (79)) : ℕ) = 474 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_79]
  try omega

theorem v3_phi_474 : v3_fast (totient 474) 100 = v3_phi_list.getD 474 0 := by
  rw [tot_474]
  rfl

theorem tot_475 : totient 475 = 360 := by
  have heq : (5^2 * (19) : ℕ) = 475 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_19]
  try omega

theorem v3_phi_475 : v3_fast (totient 475) 100 = v3_phi_list.getD 475 0 := by
  rw [tot_475]
  rfl

theorem tot_476 : totient 476 = 192 := by
  have heq : (2^2 * (7 * (17)) : ℕ) = 476 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_17]
  try omega

theorem v3_phi_476 : v3_fast (totient 476) 100 = v3_phi_list.getD 476 0 := by
  rw [tot_476]
  rfl

theorem tot_477 : totient 477 = 312 := by
  have heq : (3^2 * (53) : ℕ) = 477 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_53]
  try omega

theorem v3_phi_477 : v3_fast (totient 477) 100 = v3_phi_list.getD 477 0 := by
  rw [tot_477]
  rfl

theorem tot_478 : totient 478 = 238 := by
  have heq : (2 * (239) : ℕ) = 478 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_239]
  try omega

theorem v3_phi_478 : v3_fast (totient 478) 100 = v3_phi_list.getD 478 0 := by
  rw [tot_478]
  rfl

theorem tot_479 : totient 479 = 478 := by
  have h : totient 479 = 479 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_479 : v3_fast (totient 479) 100 = v3_phi_list.getD 479 0 := by
  rw [tot_479]
  rfl

theorem tot_480 : totient 480 = 128 := by
  have heq : (2^5 * (3 * (5)) : ℕ) = 480 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_480 : v3_fast (totient 480) 100 = v3_phi_list.getD 480 0 := by
  rw [tot_480]
  rfl

theorem tot_481 : totient 481 = 432 := by
  have heq : (13 * (37) : ℕ) = 481 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_37]
  try omega

theorem v3_phi_481 : v3_fast (totient 481) 100 = v3_phi_list.getD 481 0 := by
  rw [tot_481]
  rfl

theorem tot_482 : totient 482 = 240 := by
  have heq : (2 * (241) : ℕ) = 482 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_241]
  try omega

theorem v3_phi_482 : v3_fast (totient 482) 100 = v3_phi_list.getD 482 0 := by
  rw [tot_482]
  rfl

theorem tot_483 : totient 483 = 264 := by
  have heq : (3 * (7 * (23)) : ℕ) = 483 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_23]
  try omega

theorem v3_phi_483 : v3_fast (totient 483) 100 = v3_phi_list.getD 483 0 := by
  rw [tot_483]
  rfl

theorem tot_484 : totient 484 = 220 := by
  have heq : (2^2 * (11^2) : ℕ) = 484 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_11]
  try omega

theorem v3_phi_484 : v3_fast (totient 484) 100 = v3_phi_list.getD 484 0 := by
  rw [tot_484]
  rfl

theorem tot_485 : totient 485 = 384 := by
  have heq : (5 * (97) : ℕ) = 485 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_97]
  try omega

theorem v3_phi_485 : v3_fast (totient 485) 100 = v3_phi_list.getD 485 0 := by
  rw [tot_485]
  rfl

theorem tot_486 : totient 486 = 162 := by
  have heq : (2 * (3^5) : ℕ) = 486 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^5) = 3^4 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_486 : v3_fast (totient 486) 100 = v3_phi_list.getD 486 0 := by
  rw [tot_486]
  rfl

theorem tot_487 : totient 487 = 486 := by
  have h : totient 487 = 487 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_487 : v3_fast (totient 487) 100 = v3_phi_list.getD 487 0 := by
  rw [tot_487]
  rfl

theorem tot_488 : totient 488 = 240 := by
  have heq : (2^3 * (61) : ℕ) = 488 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_61]
  try omega

theorem v3_phi_488 : v3_fast (totient 488) 100 = v3_phi_list.getD 488 0 := by
  rw [tot_488]
  rfl

theorem tot_489 : totient 489 = 324 := by
  have heq : (3 * (163) : ℕ) = 489 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_163]
  try omega

theorem v3_phi_489 : v3_fast (totient 489) 100 = v3_phi_list.getD 489 0 := by
  rw [tot_489]
  rfl

theorem tot_490 : totient 490 = 168 := by
  have heq : (2 * (5 * (7^2)) : ℕ) = 490 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5, hp_7]
  try omega

theorem v3_phi_490 : v3_fast (totient 490) 100 = v3_phi_list.getD 490 0 := by
  rw [tot_490]
  rfl

theorem tot_491 : totient 491 = 490 := by
  have h : totient 491 = 491 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_491 : v3_fast (totient 491) 100 = v3_phi_list.getD 491 0 := by
  rw [tot_491]
  rfl

theorem tot_492 : totient 492 = 160 := by
  have heq : (2^2 * (3 * (41)) : ℕ) = 492 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_41]
  try omega

theorem v3_phi_492 : v3_fast (totient 492) 100 = v3_phi_list.getD 492 0 := by
  rw [tot_492]
  rfl

theorem tot_493 : totient 493 = 448 := by
  have heq : (17 * (29) : ℕ) = 493 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_29]
  try omega

theorem v3_phi_493 : v3_fast (totient 493) 100 = v3_phi_list.getD 493 0 := by
  rw [tot_493]
  rfl

theorem tot_494 : totient 494 = 216 := by
  have heq : (2 * (13 * (19)) : ℕ) = 494 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_19]
  try omega

theorem v3_phi_494 : v3_fast (totient 494) 100 = v3_phi_list.getD 494 0 := by
  rw [tot_494]
  rfl

theorem tot_495 : totient 495 = 240 := by
  have heq : (3^2 * (5 * (11)) : ℕ) = 495 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_11]
  try omega

theorem v3_phi_495 : v3_fast (totient 495) 100 = v3_phi_list.getD 495 0 := by
  rw [tot_495]
  rfl

theorem tot_496 : totient 496 = 240 := by
  have heq : (2^4 * (31) : ℕ) = 496 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_31]
  try omega

theorem v3_phi_496 : v3_fast (totient 496) 100 = v3_phi_list.getD 496 0 := by
  rw [tot_496]
  rfl

theorem tot_497 : totient 497 = 420 := by
  have heq : (7 * (71) : ℕ) = 497 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_71]
  try omega

theorem v3_phi_497 : v3_fast (totient 497) 100 = v3_phi_list.getD 497 0 := by
  rw [tot_497]
  rfl

theorem tot_498 : totient 498 = 164 := by
  have heq : (2 * (3 * (83)) : ℕ) = 498 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_83]
  try omega

theorem v3_phi_498 : v3_fast (totient 498) 100 = v3_phi_list.getD 498 0 := by
  rw [tot_498]
  rfl

theorem tot_499 : totient 499 = 498 := by
  have h : totient 499 = 499 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_499 : v3_fast (totient 499) 100 = v3_phi_list.getD 499 0 := by
  rw [tot_499]
  rfl

theorem tot_500 : totient 500 = 200 := by
  have heq : (2^2 * (5^3) : ℕ) = 500 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_500 : v3_fast (totient 500) 100 = v3_phi_list.getD 500 0 := by
  rw [tot_500]
  rfl

theorem tot_501 : totient 501 = 332 := by
  have heq : (3 * (167) : ℕ) = 501 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_167]
  try omega

theorem v3_phi_501 : v3_fast (totient 501) 100 = v3_phi_list.getD 501 0 := by
  rw [tot_501]
  rfl

theorem tot_502 : totient 502 = 250 := by
  have heq : (2 * (251) : ℕ) = 502 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_251]
  try omega

theorem v3_phi_502 : v3_fast (totient 502) 100 = v3_phi_list.getD 502 0 := by
  rw [tot_502]
  rfl

theorem tot_503 : totient 503 = 502 := by
  have h : totient 503 = 503 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_503 : v3_fast (totient 503) 100 = v3_phi_list.getD 503 0 := by
  rw [tot_503]
  rfl

theorem tot_504 : totient 504 = 144 := by
  have heq : (2^3 * (3^2 * (7)) : ℕ) = 504 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_504 : v3_fast (totient 504) 100 = v3_phi_list.getD 504 0 := by
  rw [tot_504]
  rfl

theorem tot_505 : totient 505 = 400 := by
  have heq : (5 * (101) : ℕ) = 505 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_101]
  try omega

theorem v3_phi_505 : v3_fast (totient 505) 100 = v3_phi_list.getD 505 0 := by
  rw [tot_505]
  rfl

theorem tot_506 : totient 506 = 220 := by
  have heq : (2 * (11 * (23)) : ℕ) = 506 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_23]
  try omega

theorem v3_phi_506 : v3_fast (totient 506) 100 = v3_phi_list.getD 506 0 := by
  rw [tot_506]
  rfl

theorem tot_507 : totient 507 = 312 := by
  have heq : (3 * (13^2) : ℕ) = 507 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_13]
  try omega

theorem v3_phi_507 : v3_fast (totient 507) 100 = v3_phi_list.getD 507 0 := by
  rw [tot_507]
  rfl

theorem tot_508 : totient 508 = 252 := by
  have heq : (2^2 * (127) : ℕ) = 508 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_127]
  try omega

theorem v3_phi_508 : v3_fast (totient 508) 100 = v3_phi_list.getD 508 0 := by
  rw [tot_508]
  rfl

theorem tot_509 : totient 509 = 508 := by
  have h : totient 509 = 509 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_509 : v3_fast (totient 509) 100 = v3_phi_list.getD 509 0 := by
  rw [tot_509]
  rfl

theorem tot_510 : totient 510 = 128 := by
  have heq : (2 * (3 * (5 * (17))) : ℕ) = 510 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_17]
  try omega

theorem v3_phi_510 : v3_fast (totient 510) 100 = v3_phi_list.getD 510 0 := by
  rw [tot_510]
  rfl

theorem tot_511 : totient 511 = 432 := by
  have heq : (7 * (73) : ℕ) = 511 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_73]
  try omega

theorem v3_phi_511 : v3_fast (totient 511) 100 = v3_phi_list.getD 511 0 := by
  rw [tot_511]
  rfl

theorem tot_512 : totient 512 = 256 := by
  have h : totient (2^9) = 2^8 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^9 : ℕ) = 512 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_512 : v3_fast (totient 512) 100 = v3_phi_list.getD 512 0 := by
  rw [tot_512]
  rfl

theorem tot_513 : totient 513 = 324 := by
  have heq : (3^3 * (19) : ℕ) = 513 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19]
  try omega

theorem v3_phi_513 : v3_fast (totient 513) 100 = v3_phi_list.getD 513 0 := by
  rw [tot_513]
  rfl

theorem tot_514 : totient 514 = 256 := by
  have heq : (2 * (257) : ℕ) = 514 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_257]
  try omega

theorem v3_phi_514 : v3_fast (totient 514) 100 = v3_phi_list.getD 514 0 := by
  rw [tot_514]
  rfl

theorem tot_515 : totient 515 = 408 := by
  have heq : (5 * (103) : ℕ) = 515 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_103]
  try omega

theorem v3_phi_515 : v3_fast (totient 515) 100 = v3_phi_list.getD 515 0 := by
  rw [tot_515]
  rfl

theorem tot_516 : totient 516 = 168 := by
  have heq : (2^2 * (3 * (43)) : ℕ) = 516 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_43]
  try omega

theorem v3_phi_516 : v3_fast (totient 516) 100 = v3_phi_list.getD 516 0 := by
  rw [tot_516]
  rfl

theorem tot_517 : totient 517 = 460 := by
  have heq : (11 * (47) : ℕ) = 517 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_47]
  try omega

theorem v3_phi_517 : v3_fast (totient 517) 100 = v3_phi_list.getD 517 0 := by
  rw [tot_517]
  rfl

theorem tot_518 : totient 518 = 216 := by
  have heq : (2 * (7 * (37)) : ℕ) = 518 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_37]
  try omega

theorem v3_phi_518 : v3_fast (totient 518) 100 = v3_phi_list.getD 518 0 := by
  rw [tot_518]
  rfl

theorem tot_519 : totient 519 = 344 := by
  have heq : (3 * (173) : ℕ) = 519 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_173]
  try omega

theorem v3_phi_519 : v3_fast (totient 519) 100 = v3_phi_list.getD 519 0 := by
  rw [tot_519]
  rfl

theorem tot_520 : totient 520 = 192 := by
  have heq : (2^3 * (5 * (13)) : ℕ) = 520 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13]
  try omega

theorem v3_phi_520 : v3_fast (totient 520) 100 = v3_phi_list.getD 520 0 := by
  rw [tot_520]
  rfl

theorem tot_521 : totient 521 = 520 := by
  have h : totient 521 = 521 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_521 : v3_fast (totient 521) 100 = v3_phi_list.getD 521 0 := by
  rw [tot_521]
  rfl

theorem tot_522 : totient 522 = 168 := by
  have heq : (2 * (3^2 * (29)) : ℕ) = 522 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29]
  try omega

theorem v3_phi_522 : v3_fast (totient 522) 100 = v3_phi_list.getD 522 0 := by
  rw [tot_522]
  rfl

theorem tot_523 : totient 523 = 522 := by
  have h : totient 523 = 523 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_523 : v3_fast (totient 523) 100 = v3_phi_list.getD 523 0 := by
  rw [tot_523]
  rfl

theorem tot_524 : totient 524 = 260 := by
  have heq : (2^2 * (131) : ℕ) = 524 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_131]
  try omega

theorem v3_phi_524 : v3_fast (totient 524) 100 = v3_phi_list.getD 524 0 := by
  rw [tot_524]
  rfl

theorem tot_525 : totient 525 = 240 := by
  have heq : (3 * (5^2 * (7)) : ℕ) = 525 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_525 : v3_fast (totient 525) 100 = v3_phi_list.getD 525 0 := by
  rw [tot_525]
  rfl

theorem tot_526 : totient 526 = 262 := by
  have heq : (2 * (263) : ℕ) = 526 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_263 : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_263]
  try omega

theorem v3_phi_526 : v3_fast (totient 526) 100 = v3_phi_list.getD 526 0 := by
  rw [tot_526]
  rfl

theorem tot_527 : totient 527 = 480 := by
  have heq : (17 * (31) : ℕ) = 527 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_31]
  try omega

theorem v3_phi_527 : v3_fast (totient 527) 100 = v3_phi_list.getD 527 0 := by
  rw [tot_527]
  rfl

theorem tot_528 : totient 528 = 160 := by
  have heq : (2^4 * (3 * (11)) : ℕ) = 528 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_528 : v3_fast (totient 528) 100 = v3_phi_list.getD 528 0 := by
  rw [tot_528]
  rfl

theorem tot_529 : totient 529 = 506 := by
  have h : totient (23^2) = 23^1 * (23 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (23^2 : ℕ) = 529 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_529 : v3_fast (totient 529) 100 = v3_phi_list.getD 529 0 := by
  rw [tot_529]
  rfl

theorem tot_530 : totient 530 = 208 := by
  have heq : (2 * (5 * (53)) : ℕ) = 530 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_53]
  try omega

theorem v3_phi_530 : v3_fast (totient 530) 100 = v3_phi_list.getD 530 0 := by
  rw [tot_530]
  rfl

theorem tot_531 : totient 531 = 348 := by
  have heq : (3^2 * (59) : ℕ) = 531 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_59]
  try omega

theorem v3_phi_531 : v3_fast (totient 531) 100 = v3_phi_list.getD 531 0 := by
  rw [tot_531]
  rfl

theorem tot_532 : totient 532 = 216 := by
  have heq : (2^2 * (7 * (19)) : ℕ) = 532 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_19]
  try omega

theorem v3_phi_532 : v3_fast (totient 532) 100 = v3_phi_list.getD 532 0 := by
  rw [tot_532]
  rfl

theorem tot_533 : totient 533 = 480 := by
  have heq : (13 * (41) : ℕ) = 533 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_41]
  try omega

theorem v3_phi_533 : v3_fast (totient 533) 100 = v3_phi_list.getD 533 0 := by
  rw [tot_533]
  rfl

theorem tot_534 : totient 534 = 176 := by
  have heq : (2 * (3 * (89)) : ℕ) = 534 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_89]
  try omega

theorem v3_phi_534 : v3_fast (totient 534) 100 = v3_phi_list.getD 534 0 := by
  rw [tot_534]
  rfl

theorem tot_535 : totient 535 = 424 := by
  have heq : (5 * (107) : ℕ) = 535 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_107]
  try omega

theorem v3_phi_535 : v3_fast (totient 535) 100 = v3_phi_list.getD 535 0 := by
  rw [tot_535]
  rfl

theorem tot_536 : totient 536 = 264 := by
  have heq : (2^3 * (67) : ℕ) = 536 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_67]
  try omega

theorem v3_phi_536 : v3_fast (totient 536) 100 = v3_phi_list.getD 536 0 := by
  rw [tot_536]
  rfl

theorem tot_537 : totient 537 = 356 := by
  have heq : (3 * (179) : ℕ) = 537 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_179]
  try omega

theorem v3_phi_537 : v3_fast (totient 537) 100 = v3_phi_list.getD 537 0 := by
  rw [tot_537]
  rfl

theorem tot_538 : totient 538 = 268 := by
  have heq : (2 * (269) : ℕ) = 538 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_269 : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_269]
  try omega

theorem v3_phi_538 : v3_fast (totient 538) 100 = v3_phi_list.getD 538 0 := by
  rw [tot_538]
  rfl

theorem tot_539 : totient 539 = 420 := by
  have heq : (7^2 * (11) : ℕ) = 539 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11]
  try omega

theorem v3_phi_539 : v3_fast (totient 539) 100 = v3_phi_list.getD 539 0 := by
  rw [tot_539]
  rfl

theorem tot_540 : totient 540 = 144 := by
  have heq : (2^2 * (3^3 * (5)) : ℕ) = 540 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_540 : v3_fast (totient 540) 100 = v3_phi_list.getD 540 0 := by
  rw [tot_540]
  rfl

theorem tot_541 : totient 541 = 540 := by
  have h : totient 541 = 541 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_541 : v3_fast (totient 541) 100 = v3_phi_list.getD 541 0 := by
  rw [tot_541]
  rfl

theorem tot_542 : totient 542 = 270 := by
  have heq : (2 * (271) : ℕ) = 542 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_271 : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_271]
  try omega

theorem v3_phi_542 : v3_fast (totient 542) 100 = v3_phi_list.getD 542 0 := by
  rw [tot_542]
  rfl

theorem tot_543 : totient 543 = 360 := by
  have heq : (3 * (181) : ℕ) = 543 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_181]
  try omega

theorem v3_phi_543 : v3_fast (totient 543) 100 = v3_phi_list.getD 543 0 := by
  rw [tot_543]
  rfl

theorem tot_544 : totient 544 = 256 := by
  have heq : (2^5 * (17) : ℕ) = 544 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17]
  try omega

theorem v3_phi_544 : v3_fast (totient 544) 100 = v3_phi_list.getD 544 0 := by
  rw [tot_544]
  rfl

theorem tot_545 : totient 545 = 432 := by
  have heq : (5 * (109) : ℕ) = 545 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_109]
  try omega

theorem v3_phi_545 : v3_fast (totient 545) 100 = v3_phi_list.getD 545 0 := by
  rw [tot_545]
  rfl

theorem tot_546 : totient 546 = 144 := by
  have heq : (2 * (3 * (7 * (13))) : ℕ) = 546 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_13]
  try omega

theorem v3_phi_546 : v3_fast (totient 546) 100 = v3_phi_list.getD 546 0 := by
  rw [tot_546]
  rfl

theorem tot_547 : totient 547 = 546 := by
  have h : totient 547 = 547 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_547 : v3_fast (totient 547) 100 = v3_phi_list.getD 547 0 := by
  rw [tot_547]
  rfl

theorem tot_548 : totient 548 = 272 := by
  have heq : (2^2 * (137) : ℕ) = 548 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_137]
  try omega

theorem v3_phi_548 : v3_fast (totient 548) 100 = v3_phi_list.getD 548 0 := by
  rw [tot_548]
  rfl

theorem tot_549 : totient 549 = 360 := by
  have heq : (3^2 * (61) : ℕ) = 549 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_61]
  try omega

theorem v3_phi_549 : v3_fast (totient 549) 100 = v3_phi_list.getD 549 0 := by
  rw [tot_549]
  rfl

theorem tot_550 : totient 550 = 200 := by
  have heq : (2 * (5^2 * (11)) : ℕ) = 550 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11]
  try omega

theorem v3_phi_550 : v3_fast (totient 550) 100 = v3_phi_list.getD 550 0 := by
  rw [tot_550]
  rfl

theorem tot_551 : totient 551 = 504 := by
  have heq : (19 * (29) : ℕ) = 551 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_29]
  try omega

theorem v3_phi_551 : v3_fast (totient 551) 100 = v3_phi_list.getD 551 0 := by
  rw [tot_551]
  rfl

theorem tot_552 : totient 552 = 176 := by
  have heq : (2^3 * (3 * (23)) : ℕ) = 552 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23]
  try omega

theorem v3_phi_552 : v3_fast (totient 552) 100 = v3_phi_list.getD 552 0 := by
  rw [tot_552]
  rfl

theorem tot_553 : totient 553 = 468 := by
  have heq : (7 * (79) : ℕ) = 553 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_79]
  try omega

theorem v3_phi_553 : v3_fast (totient 553) 100 = v3_phi_list.getD 553 0 := by
  rw [tot_553]
  rfl

theorem tot_554 : totient 554 = 276 := by
  have heq : (2 * (277) : ℕ) = 554 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_277 : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_277]
  try omega

theorem v3_phi_554 : v3_fast (totient 554) 100 = v3_phi_list.getD 554 0 := by
  rw [tot_554]
  rfl

theorem tot_555 : totient 555 = 288 := by
  have heq : (3 * (5 * (37)) : ℕ) = 555 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_37]
  try omega

theorem v3_phi_555 : v3_fast (totient 555) 100 = v3_phi_list.getD 555 0 := by
  rw [tot_555]
  rfl

theorem tot_556 : totient 556 = 276 := by
  have heq : (2^2 * (139) : ℕ) = 556 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_139]
  try omega

theorem v3_phi_556 : v3_fast (totient 556) 100 = v3_phi_list.getD 556 0 := by
  rw [tot_556]
  rfl

theorem tot_557 : totient 557 = 556 := by
  have h : totient 557 = 557 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_557 : v3_fast (totient 557) 100 = v3_phi_list.getD 557 0 := by
  rw [tot_557]
  rfl

theorem tot_558 : totient 558 = 180 := by
  have heq : (2 * (3^2 * (31)) : ℕ) = 558 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31]
  try omega

theorem v3_phi_558 : v3_fast (totient 558) 100 = v3_phi_list.getD 558 0 := by
  rw [tot_558]
  rfl

theorem tot_559 : totient 559 = 504 := by
  have heq : (13 * (43) : ℕ) = 559 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_43]
  try omega

theorem v3_phi_559 : v3_fast (totient 559) 100 = v3_phi_list.getD 559 0 := by
  rw [tot_559]
  rfl

theorem tot_560 : totient 560 = 192 := by
  have heq : (2^4 * (5 * (7)) : ℕ) = 560 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7]
  try omega

theorem v3_phi_560 : v3_fast (totient 560) 100 = v3_phi_list.getD 560 0 := by
  rw [tot_560]
  rfl

theorem tot_561 : totient 561 = 320 := by
  have heq : (3 * (11 * (17)) : ℕ) = 561 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_17]
  try omega

theorem v3_phi_561 : v3_fast (totient 561) 100 = v3_phi_list.getD 561 0 := by
  rw [tot_561]
  rfl

theorem tot_562 : totient 562 = 280 := by
  have heq : (2 * (281) : ℕ) = 562 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_281 : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_281]
  try omega

theorem v3_phi_562 : v3_fast (totient 562) 100 = v3_phi_list.getD 562 0 := by
  rw [tot_562]
  rfl

theorem tot_563 : totient 563 = 562 := by
  have h : totient 563 = 563 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_563 : v3_fast (totient 563) 100 = v3_phi_list.getD 563 0 := by
  rw [tot_563]
  rfl

theorem tot_564 : totient 564 = 184 := by
  have heq : (2^2 * (3 * (47)) : ℕ) = 564 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_47]
  try omega

theorem v3_phi_564 : v3_fast (totient 564) 100 = v3_phi_list.getD 564 0 := by
  rw [tot_564]
  rfl

theorem tot_565 : totient 565 = 448 := by
  have heq : (5 * (113) : ℕ) = 565 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_113]
  try omega

theorem v3_phi_565 : v3_fast (totient 565) 100 = v3_phi_list.getD 565 0 := by
  rw [tot_565]
  rfl

theorem tot_566 : totient 566 = 282 := by
  have heq : (2 * (283) : ℕ) = 566 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_283 : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_283]
  try omega

theorem v3_phi_566 : v3_fast (totient 566) 100 = v3_phi_list.getD 566 0 := by
  rw [tot_566]
  rfl

theorem tot_567 : totient 567 = 324 := by
  have heq : (3^4 * (7) : ℕ) = 567 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7]
  try omega

theorem v3_phi_567 : v3_fast (totient 567) 100 = v3_phi_list.getD 567 0 := by
  rw [tot_567]
  rfl

theorem tot_568 : totient 568 = 280 := by
  have heq : (2^3 * (71) : ℕ) = 568 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_71]
  try omega

theorem v3_phi_568 : v3_fast (totient 568) 100 = v3_phi_list.getD 568 0 := by
  rw [tot_568]
  rfl

theorem tot_569 : totient 569 = 568 := by
  have h : totient 569 = 569 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_569 : v3_fast (totient 569) 100 = v3_phi_list.getD 569 0 := by
  rw [tot_569]
  rfl

theorem tot_570 : totient 570 = 144 := by
  have heq : (2 * (3 * (5 * (19))) : ℕ) = 570 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_19]
  try omega

theorem v3_phi_570 : v3_fast (totient 570) 100 = v3_phi_list.getD 570 0 := by
  rw [tot_570]
  rfl

theorem tot_571 : totient 571 = 570 := by
  have h : totient 571 = 571 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_571 : v3_fast (totient 571) 100 = v3_phi_list.getD 571 0 := by
  rw [tot_571]
  rfl

theorem tot_572 : totient 572 = 240 := by
  have heq : (2^2 * (11 * (13)) : ℕ) = 572 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_13]
  try omega

theorem v3_phi_572 : v3_fast (totient 572) 100 = v3_phi_list.getD 572 0 := by
  rw [tot_572]
  rfl

theorem tot_573 : totient 573 = 380 := by
  have heq : (3 * (191) : ℕ) = 573 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_191]
  try omega

theorem v3_phi_573 : v3_fast (totient 573) 100 = v3_phi_list.getD 573 0 := by
  rw [tot_573]
  rfl

theorem tot_574 : totient 574 = 240 := by
  have heq : (2 * (7 * (41)) : ℕ) = 574 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_41]
  try omega

theorem v3_phi_574 : v3_fast (totient 574) 100 = v3_phi_list.getD 574 0 := by
  rw [tot_574]
  rfl

theorem tot_575 : totient 575 = 440 := by
  have heq : (5^2 * (23) : ℕ) = 575 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_23]
  try omega

theorem v3_phi_575 : v3_fast (totient 575) 100 = v3_phi_list.getD 575 0 := by
  rw [tot_575]
  rfl

theorem tot_576 : totient 576 = 192 := by
  have heq : (2^6 * (3^2) : ℕ) = 576 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_576 : v3_fast (totient 576) 100 = v3_phi_list.getD 576 0 := by
  rw [tot_576]
  rfl

theorem tot_577 : totient 577 = 576 := by
  have h : totient 577 = 577 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_577 : v3_fast (totient 577) 100 = v3_phi_list.getD 577 0 := by
  rw [tot_577]
  rfl

theorem tot_578 : totient 578 = 272 := by
  have heq : (2 * (17^2) : ℕ) = 578 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_17]
  try omega

theorem v3_phi_578 : v3_fast (totient 578) 100 = v3_phi_list.getD 578 0 := by
  rw [tot_578]
  rfl

theorem tot_579 : totient 579 = 384 := by
  have heq : (3 * (193) : ℕ) = 579 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_193]
  try omega

theorem v3_phi_579 : v3_fast (totient 579) 100 = v3_phi_list.getD 579 0 := by
  rw [tot_579]
  rfl

theorem tot_580 : totient 580 = 224 := by
  have heq : (2^2 * (5 * (29)) : ℕ) = 580 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_29]
  try omega

theorem v3_phi_580 : v3_fast (totient 580) 100 = v3_phi_list.getD 580 0 := by
  rw [tot_580]
  rfl

theorem tot_581 : totient 581 = 492 := by
  have heq : (7 * (83) : ℕ) = 581 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_83]
  try omega

theorem v3_phi_581 : v3_fast (totient 581) 100 = v3_phi_list.getD 581 0 := by
  rw [tot_581]
  rfl

theorem tot_582 : totient 582 = 192 := by
  have heq : (2 * (3 * (97)) : ℕ) = 582 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_97]
  try omega

theorem v3_phi_582 : v3_fast (totient 582) 100 = v3_phi_list.getD 582 0 := by
  rw [tot_582]
  rfl

theorem tot_583 : totient 583 = 520 := by
  have heq : (11 * (53) : ℕ) = 583 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_53]
  try omega

theorem v3_phi_583 : v3_fast (totient 583) 100 = v3_phi_list.getD 583 0 := by
  rw [tot_583]
  rfl

theorem tot_584 : totient 584 = 288 := by
  have heq : (2^3 * (73) : ℕ) = 584 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_73]
  try omega

theorem v3_phi_584 : v3_fast (totient 584) 100 = v3_phi_list.getD 584 0 := by
  rw [tot_584]
  rfl

theorem tot_585 : totient 585 = 288 := by
  have heq : (3^2 * (5 * (13)) : ℕ) = 585 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_13]
  try omega

theorem v3_phi_585 : v3_fast (totient 585) 100 = v3_phi_list.getD 585 0 := by
  rw [tot_585]
  rfl

theorem tot_586 : totient 586 = 292 := by
  have heq : (2 * (293) : ℕ) = 586 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_293 : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_293]
  try omega

theorem v3_phi_586 : v3_fast (totient 586) 100 = v3_phi_list.getD 586 0 := by
  rw [tot_586]
  rfl

theorem tot_587 : totient 587 = 586 := by
  have h : totient 587 = 587 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_587 : v3_fast (totient 587) 100 = v3_phi_list.getD 587 0 := by
  rw [tot_587]
  rfl

theorem tot_588 : totient 588 = 168 := by
  have heq : (2^2 * (3 * (7^2)) : ℕ) = 588 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_588 : v3_fast (totient 588) 100 = v3_phi_list.getD 588 0 := by
  rw [tot_588]
  rfl

theorem tot_589 : totient 589 = 540 := by
  have heq : (19 * (31) : ℕ) = 589 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_31]
  try omega

theorem v3_phi_589 : v3_fast (totient 589) 100 = v3_phi_list.getD 589 0 := by
  rw [tot_589]
  rfl

theorem tot_590 : totient 590 = 232 := by
  have heq : (2 * (5 * (59)) : ℕ) = 590 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_59]
  try omega

theorem v3_phi_590 : v3_fast (totient 590) 100 = v3_phi_list.getD 590 0 := by
  rw [tot_590]
  rfl

theorem tot_591 : totient 591 = 392 := by
  have heq : (3 * (197) : ℕ) = 591 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_197]
  try omega

theorem v3_phi_591 : v3_fast (totient 591) 100 = v3_phi_list.getD 591 0 := by
  rw [tot_591]
  rfl

theorem tot_592 : totient 592 = 288 := by
  have heq : (2^4 * (37) : ℕ) = 592 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_37]
  try omega

theorem v3_phi_592 : v3_fast (totient 592) 100 = v3_phi_list.getD 592 0 := by
  rw [tot_592]
  rfl

theorem tot_593 : totient 593 = 592 := by
  have h : totient 593 = 593 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_593 : v3_fast (totient 593) 100 = v3_phi_list.getD 593 0 := by
  rw [tot_593]
  rfl

theorem tot_594 : totient 594 = 180 := by
  have heq : (2 * (3^3 * (11)) : ℕ) = 594 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_594 : v3_fast (totient 594) 100 = v3_phi_list.getD 594 0 := by
  rw [tot_594]
  rfl

theorem tot_595 : totient 595 = 384 := by
  have heq : (5 * (7 * (17)) : ℕ) = 595 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_17]
  try omega

theorem v3_phi_595 : v3_fast (totient 595) 100 = v3_phi_list.getD 595 0 := by
  rw [tot_595]
  rfl

theorem tot_596 : totient 596 = 296 := by
  have heq : (2^2 * (149) : ℕ) = 596 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_149]
  try omega

theorem v3_phi_596 : v3_fast (totient 596) 100 = v3_phi_list.getD 596 0 := by
  rw [tot_596]
  rfl

theorem tot_597 : totient 597 = 396 := by
  have heq : (3 * (199) : ℕ) = 597 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_199]
  try omega

theorem v3_phi_597 : v3_fast (totient 597) 100 = v3_phi_list.getD 597 0 := by
  rw [tot_597]
  rfl

theorem tot_598 : totient 598 = 264 := by
  have heq : (2 * (13 * (23)) : ℕ) = 598 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_23]
  try omega

theorem v3_phi_598 : v3_fast (totient 598) 100 = v3_phi_list.getD 598 0 := by
  rw [tot_598]
  rfl

theorem tot_599 : totient 599 = 598 := by
  have h : totient 599 = 599 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_599 : v3_fast (totient 599) 100 = v3_phi_list.getD 599 0 := by
  rw [tot_599]
  rfl

theorem tot_600 : totient 600 = 160 := by
  have heq : (2^3 * (3 * (5^2)) : ℕ) = 600 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_600 : v3_fast (totient 600) 100 = v3_phi_list.getD 600 0 := by
  rw [tot_600]
  rfl

theorem tot_601 : totient 601 = 600 := by
  have h : totient 601 = 601 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_601 : v3_fast (totient 601) 100 = v3_phi_list.getD 601 0 := by
  rw [tot_601]
  rfl

theorem tot_602 : totient 602 = 252 := by
  have heq : (2 * (7 * (43)) : ℕ) = 602 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_43]
  try omega

theorem v3_phi_602 : v3_fast (totient 602) 100 = v3_phi_list.getD 602 0 := by
  rw [tot_602]
  rfl

theorem tot_603 : totient 603 = 396 := by
  have heq : (3^2 * (67) : ℕ) = 603 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_67]
  try omega

theorem v3_phi_603 : v3_fast (totient 603) 100 = v3_phi_list.getD 603 0 := by
  rw [tot_603]
  rfl

theorem tot_604 : totient 604 = 300 := by
  have heq : (2^2 * (151) : ℕ) = 604 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_151]
  try omega

theorem v3_phi_604 : v3_fast (totient 604) 100 = v3_phi_list.getD 604 0 := by
  rw [tot_604]
  rfl

theorem tot_605 : totient 605 = 440 := by
  have heq : (5 * (11^2) : ℕ) = 605 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_11]
  try omega

theorem v3_phi_605 : v3_fast (totient 605) 100 = v3_phi_list.getD 605 0 := by
  rw [tot_605]
  rfl

theorem tot_606 : totient 606 = 200 := by
  have heq : (2 * (3 * (101)) : ℕ) = 606 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_101]
  try omega

theorem v3_phi_606 : v3_fast (totient 606) 100 = v3_phi_list.getD 606 0 := by
  rw [tot_606]
  rfl

theorem tot_607 : totient 607 = 606 := by
  have h : totient 607 = 607 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_607 : v3_fast (totient 607) 100 = v3_phi_list.getD 607 0 := by
  rw [tot_607]
  rfl

theorem tot_608 : totient 608 = 288 := by
  have heq : (2^5 * (19) : ℕ) = 608 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19]
  try omega

theorem v3_phi_608 : v3_fast (totient 608) 100 = v3_phi_list.getD 608 0 := by
  rw [tot_608]
  rfl

theorem tot_609 : totient 609 = 336 := by
  have heq : (3 * (7 * (29)) : ℕ) = 609 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_29]
  try omega

theorem v3_phi_609 : v3_fast (totient 609) 100 = v3_phi_list.getD 609 0 := by
  rw [tot_609]
  rfl

theorem tot_610 : totient 610 = 240 := by
  have heq : (2 * (5 * (61)) : ℕ) = 610 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_61]
  try omega

theorem v3_phi_610 : v3_fast (totient 610) 100 = v3_phi_list.getD 610 0 := by
  rw [tot_610]
  rfl

theorem tot_611 : totient 611 = 552 := by
  have heq : (13 * (47) : ℕ) = 611 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_47]
  try omega

theorem v3_phi_611 : v3_fast (totient 611) 100 = v3_phi_list.getD 611 0 := by
  rw [tot_611]
  rfl

theorem tot_612 : totient 612 = 192 := by
  have heq : (2^2 * (3^2 * (17)) : ℕ) = 612 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17]
  try omega

theorem v3_phi_612 : v3_fast (totient 612) 100 = v3_phi_list.getD 612 0 := by
  rw [tot_612]
  rfl

theorem tot_613 : totient 613 = 612 := by
  have h : totient 613 = 613 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_613 : v3_fast (totient 613) 100 = v3_phi_list.getD 613 0 := by
  rw [tot_613]
  rfl

theorem tot_614 : totient 614 = 306 := by
  have heq : (2 * (307) : ℕ) = 614 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_307 : totient 307 = 307 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_307]
  try omega

theorem v3_phi_614 : v3_fast (totient 614) 100 = v3_phi_list.getD 614 0 := by
  rw [tot_614]
  rfl

theorem tot_615 : totient 615 = 320 := by
  have heq : (3 * (5 * (41)) : ℕ) = 615 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_41]
  try omega

theorem v3_phi_615 : v3_fast (totient 615) 100 = v3_phi_list.getD 615 0 := by
  rw [tot_615]
  rfl

theorem tot_616 : totient 616 = 240 := by
  have heq : (2^3 * (7 * (11)) : ℕ) = 616 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_11]
  try omega

theorem v3_phi_616 : v3_fast (totient 616) 100 = v3_phi_list.getD 616 0 := by
  rw [tot_616]
  rfl

theorem tot_617 : totient 617 = 616 := by
  have h : totient 617 = 617 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_617 : v3_fast (totient 617) 100 = v3_phi_list.getD 617 0 := by
  rw [tot_617]
  rfl

theorem tot_618 : totient 618 = 204 := by
  have heq : (2 * (3 * (103)) : ℕ) = 618 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_103]
  try omega

theorem v3_phi_618 : v3_fast (totient 618) 100 = v3_phi_list.getD 618 0 := by
  rw [tot_618]
  rfl

theorem tot_619 : totient 619 = 618 := by
  have h : totient 619 = 619 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_619 : v3_fast (totient 619) 100 = v3_phi_list.getD 619 0 := by
  rw [tot_619]
  rfl

theorem tot_620 : totient 620 = 240 := by
  have heq : (2^2 * (5 * (31)) : ℕ) = 620 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_31]
  try omega

theorem v3_phi_620 : v3_fast (totient 620) 100 = v3_phi_list.getD 620 0 := by
  rw [tot_620]
  rfl

theorem tot_621 : totient 621 = 396 := by
  have heq : (3^3 * (23) : ℕ) = 621 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_23]
  try omega

theorem v3_phi_621 : v3_fast (totient 621) 100 = v3_phi_list.getD 621 0 := by
  rw [tot_621]
  rfl

theorem tot_622 : totient 622 = 310 := by
  have heq : (2 * (311) : ℕ) = 622 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_311 : totient 311 = 311 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_311]
  try omega

theorem v3_phi_622 : v3_fast (totient 622) 100 = v3_phi_list.getD 622 0 := by
  rw [tot_622]
  rfl

theorem tot_623 : totient 623 = 528 := by
  have heq : (7 * (89) : ℕ) = 623 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_89]
  try omega

theorem v3_phi_623 : v3_fast (totient 623) 100 = v3_phi_list.getD 623 0 := by
  rw [tot_623]
  rfl

theorem tot_624 : totient 624 = 192 := by
  have heq : (2^4 * (3 * (13)) : ℕ) = 624 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13]
  try omega

theorem v3_phi_624 : v3_fast (totient 624) 100 = v3_phi_list.getD 624 0 := by
  rw [tot_624]
  rfl

theorem tot_625 : totient 625 = 500 := by
  have h : totient (5^4) = 5^3 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (5^4 : ℕ) = 625 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_625 : v3_fast (totient 625) 100 = v3_phi_list.getD 625 0 := by
  rw [tot_625]
  rfl

theorem tot_626 : totient 626 = 312 := by
  have heq : (2 * (313) : ℕ) = 626 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_313 : totient 313 = 313 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_313]
  try omega

theorem v3_phi_626 : v3_fast (totient 626) 100 = v3_phi_list.getD 626 0 := by
  rw [tot_626]
  rfl

theorem tot_627 : totient 627 = 360 := by
  have heq : (3 * (11 * (19)) : ℕ) = 627 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_19]
  try omega

theorem v3_phi_627 : v3_fast (totient 627) 100 = v3_phi_list.getD 627 0 := by
  rw [tot_627]
  rfl

theorem tot_628 : totient 628 = 312 := by
  have heq : (2^2 * (157) : ℕ) = 628 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_157]
  try omega

theorem v3_phi_628 : v3_fast (totient 628) 100 = v3_phi_list.getD 628 0 := by
  rw [tot_628]
  rfl

theorem tot_629 : totient 629 = 576 := by
  have heq : (17 * (37) : ℕ) = 629 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_37]
  try omega

theorem v3_phi_629 : v3_fast (totient 629) 100 = v3_phi_list.getD 629 0 := by
  rw [tot_629]
  rfl

theorem tot_630 : totient 630 = 144 := by
  have heq : (2 * (3^2 * (5 * (7))) : ℕ) = 630 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_630 : v3_fast (totient 630) 100 = v3_phi_list.getD 630 0 := by
  rw [tot_630]
  rfl

theorem tot_631 : totient 631 = 630 := by
  have h : totient 631 = 631 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_631 : v3_fast (totient 631) 100 = v3_phi_list.getD 631 0 := by
  rw [tot_631]
  rfl

theorem tot_632 : totient 632 = 312 := by
  have heq : (2^3 * (79) : ℕ) = 632 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_79]
  try omega

theorem v3_phi_632 : v3_fast (totient 632) 100 = v3_phi_list.getD 632 0 := by
  rw [tot_632]
  rfl

theorem tot_633 : totient 633 = 420 := by
  have heq : (3 * (211) : ℕ) = 633 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_211]
  try omega

theorem v3_phi_633 : v3_fast (totient 633) 100 = v3_phi_list.getD 633 0 := by
  rw [tot_633]
  rfl

theorem tot_634 : totient 634 = 316 := by
  have heq : (2 * (317) : ℕ) = 634 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_317 : totient 317 = 317 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_317]
  try omega

theorem v3_phi_634 : v3_fast (totient 634) 100 = v3_phi_list.getD 634 0 := by
  rw [tot_634]
  rfl

theorem tot_635 : totient 635 = 504 := by
  have heq : (5 * (127) : ℕ) = 635 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_127]
  try omega

theorem v3_phi_635 : v3_fast (totient 635) 100 = v3_phi_list.getD 635 0 := by
  rw [tot_635]
  rfl

theorem tot_636 : totient 636 = 208 := by
  have heq : (2^2 * (3 * (53)) : ℕ) = 636 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_53]
  try omega

theorem v3_phi_636 : v3_fast (totient 636) 100 = v3_phi_list.getD 636 0 := by
  rw [tot_636]
  rfl

theorem tot_637 : totient 637 = 504 := by
  have heq : (7^2 * (13) : ℕ) = 637 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_13]
  try omega

theorem v3_phi_637 : v3_fast (totient 637) 100 = v3_phi_list.getD 637 0 := by
  rw [tot_637]
  rfl

theorem tot_638 : totient 638 = 280 := by
  have heq : (2 * (11 * (29)) : ℕ) = 638 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_29]
  try omega

theorem v3_phi_638 : v3_fast (totient 638) 100 = v3_phi_list.getD 638 0 := by
  rw [tot_638]
  rfl

theorem tot_639 : totient 639 = 420 := by
  have heq : (3^2 * (71) : ℕ) = 639 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_71]
  try omega

theorem v3_phi_639 : v3_fast (totient 639) 100 = v3_phi_list.getD 639 0 := by
  rw [tot_639]
  rfl

theorem tot_640 : totient 640 = 256 := by
  have heq : (2^7 * (5) : ℕ) = 640 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_640 : v3_fast (totient 640) 100 = v3_phi_list.getD 640 0 := by
  rw [tot_640]
  rfl

theorem tot_641 : totient 641 = 640 := by
  have h : totient 641 = 641 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_641 : v3_fast (totient 641) 100 = v3_phi_list.getD 641 0 := by
  rw [tot_641]
  rfl

theorem tot_642 : totient 642 = 212 := by
  have heq : (2 * (3 * (107)) : ℕ) = 642 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_107]
  try omega

theorem v3_phi_642 : v3_fast (totient 642) 100 = v3_phi_list.getD 642 0 := by
  rw [tot_642]
  rfl

theorem tot_643 : totient 643 = 642 := by
  have h : totient 643 = 643 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_643 : v3_fast (totient 643) 100 = v3_phi_list.getD 643 0 := by
  rw [tot_643]
  rfl

theorem tot_644 : totient 644 = 264 := by
  have heq : (2^2 * (7 * (23)) : ℕ) = 644 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_23]
  try omega

theorem v3_phi_644 : v3_fast (totient 644) 100 = v3_phi_list.getD 644 0 := by
  rw [tot_644]
  rfl

theorem tot_645 : totient 645 = 336 := by
  have heq : (3 * (5 * (43)) : ℕ) = 645 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_43]
  try omega

theorem v3_phi_645 : v3_fast (totient 645) 100 = v3_phi_list.getD 645 0 := by
  rw [tot_645]
  rfl

theorem tot_646 : totient 646 = 288 := by
  have heq : (2 * (17 * (19)) : ℕ) = 646 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_19]
  try omega

theorem v3_phi_646 : v3_fast (totient 646) 100 = v3_phi_list.getD 646 0 := by
  rw [tot_646]
  rfl

theorem tot_647 : totient 647 = 646 := by
  have h : totient 647 = 647 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_647 : v3_fast (totient 647) 100 = v3_phi_list.getD 647 0 := by
  rw [tot_647]
  rfl

theorem tot_648 : totient 648 = 216 := by
  have heq : (2^3 * (3^4) : ℕ) = 648 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_648 : v3_fast (totient 648) 100 = v3_phi_list.getD 648 0 := by
  rw [tot_648]
  rfl

theorem tot_649 : totient 649 = 580 := by
  have heq : (11 * (59) : ℕ) = 649 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_59]
  try omega

theorem v3_phi_649 : v3_fast (totient 649) 100 = v3_phi_list.getD 649 0 := by
  rw [tot_649]
  rfl

theorem tot_650 : totient 650 = 240 := by
  have heq : (2 * (5^2 * (13)) : ℕ) = 650 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13]
  try omega

theorem v3_phi_650 : v3_fast (totient 650) 100 = v3_phi_list.getD 650 0 := by
  rw [tot_650]
  rfl

theorem tot_651 : totient 651 = 360 := by
  have heq : (3 * (7 * (31)) : ℕ) = 651 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_31]
  try omega

theorem v3_phi_651 : v3_fast (totient 651) 100 = v3_phi_list.getD 651 0 := by
  rw [tot_651]
  rfl

theorem tot_652 : totient 652 = 324 := by
  have heq : (2^2 * (163) : ℕ) = 652 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_163]
  try omega

theorem v3_phi_652 : v3_fast (totient 652) 100 = v3_phi_list.getD 652 0 := by
  rw [tot_652]
  rfl

theorem tot_653 : totient 653 = 652 := by
  have h : totient 653 = 653 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_653 : v3_fast (totient 653) 100 = v3_phi_list.getD 653 0 := by
  rw [tot_653]
  rfl

theorem tot_654 : totient 654 = 216 := by
  have heq : (2 * (3 * (109)) : ℕ) = 654 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_109]
  try omega

theorem v3_phi_654 : v3_fast (totient 654) 100 = v3_phi_list.getD 654 0 := by
  rw [tot_654]
  rfl

theorem tot_655 : totient 655 = 520 := by
  have heq : (5 * (131) : ℕ) = 655 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_131]
  try omega

theorem v3_phi_655 : v3_fast (totient 655) 100 = v3_phi_list.getD 655 0 := by
  rw [tot_655]
  rfl

theorem tot_656 : totient 656 = 320 := by
  have heq : (2^4 * (41) : ℕ) = 656 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_41]
  try omega

theorem v3_phi_656 : v3_fast (totient 656) 100 = v3_phi_list.getD 656 0 := by
  rw [tot_656]
  rfl

theorem tot_657 : totient 657 = 432 := by
  have heq : (3^2 * (73) : ℕ) = 657 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_73]
  try omega

theorem v3_phi_657 : v3_fast (totient 657) 100 = v3_phi_list.getD 657 0 := by
  rw [tot_657]
  rfl

theorem tot_658 : totient 658 = 276 := by
  have heq : (2 * (7 * (47)) : ℕ) = 658 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_47]
  try omega

theorem v3_phi_658 : v3_fast (totient 658) 100 = v3_phi_list.getD 658 0 := by
  rw [tot_658]
  rfl

theorem tot_659 : totient 659 = 658 := by
  have h : totient 659 = 659 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_659 : v3_fast (totient 659) 100 = v3_phi_list.getD 659 0 := by
  rw [tot_659]
  rfl

theorem tot_660 : totient 660 = 160 := by
  have heq : (2^2 * (3 * (5 * (11))) : ℕ) = 660 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_11]
  try omega

theorem v3_phi_660 : v3_fast (totient 660) 100 = v3_phi_list.getD 660 0 := by
  rw [tot_660]
  rfl

theorem tot_661 : totient 661 = 660 := by
  have h : totient 661 = 661 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_661 : v3_fast (totient 661) 100 = v3_phi_list.getD 661 0 := by
  rw [tot_661]
  rfl

theorem tot_662 : totient 662 = 330 := by
  have heq : (2 * (331) : ℕ) = 662 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_331 : totient 331 = 331 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_331]
  try omega

theorem v3_phi_662 : v3_fast (totient 662) 100 = v3_phi_list.getD 662 0 := by
  rw [tot_662]
  rfl

theorem tot_663 : totient 663 = 384 := by
  have heq : (3 * (13 * (17)) : ℕ) = 663 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_17]
  try omega

theorem v3_phi_663 : v3_fast (totient 663) 100 = v3_phi_list.getD 663 0 := by
  rw [tot_663]
  rfl

theorem tot_664 : totient 664 = 328 := by
  have heq : (2^3 * (83) : ℕ) = 664 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_83]
  try omega

theorem v3_phi_664 : v3_fast (totient 664) 100 = v3_phi_list.getD 664 0 := by
  rw [tot_664]
  rfl

theorem tot_665 : totient 665 = 432 := by
  have heq : (5 * (7 * (19)) : ℕ) = 665 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_19]
  try omega

theorem v3_phi_665 : v3_fast (totient 665) 100 = v3_phi_list.getD 665 0 := by
  rw [tot_665]
  rfl

theorem tot_666 : totient 666 = 216 := by
  have heq : (2 * (3^2 * (37)) : ℕ) = 666 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37]
  try omega

theorem v3_phi_666 : v3_fast (totient 666) 100 = v3_phi_list.getD 666 0 := by
  rw [tot_666]
  rfl

theorem tot_667 : totient 667 = 616 := by
  have heq : (23 * (29) : ℕ) = 667 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_29]
  try omega

theorem v3_phi_667 : v3_fast (totient 667) 100 = v3_phi_list.getD 667 0 := by
  rw [tot_667]
  rfl

theorem tot_668 : totient 668 = 332 := by
  have heq : (2^2 * (167) : ℕ) = 668 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_167]
  try omega

theorem v3_phi_668 : v3_fast (totient 668) 100 = v3_phi_list.getD 668 0 := by
  rw [tot_668]
  rfl

theorem tot_669 : totient 669 = 444 := by
  have heq : (3 * (223) : ℕ) = 669 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_223]
  try omega

theorem v3_phi_669 : v3_fast (totient 669) 100 = v3_phi_list.getD 669 0 := by
  rw [tot_669]
  rfl

theorem tot_670 : totient 670 = 264 := by
  have heq : (2 * (5 * (67)) : ℕ) = 670 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_67]
  try omega

theorem v3_phi_670 : v3_fast (totient 670) 100 = v3_phi_list.getD 670 0 := by
  rw [tot_670]
  rfl

theorem tot_671 : totient 671 = 600 := by
  have heq : (11 * (61) : ℕ) = 671 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_61]
  try omega

theorem v3_phi_671 : v3_fast (totient 671) 100 = v3_phi_list.getD 671 0 := by
  rw [tot_671]
  rfl

theorem tot_672 : totient 672 = 192 := by
  have heq : (2^5 * (3 * (7)) : ℕ) = 672 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_672 : v3_fast (totient 672) 100 = v3_phi_list.getD 672 0 := by
  rw [tot_672]
  rfl

theorem tot_673 : totient 673 = 672 := by
  have h : totient 673 = 673 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_673 : v3_fast (totient 673) 100 = v3_phi_list.getD 673 0 := by
  rw [tot_673]
  rfl

theorem tot_674 : totient 674 = 336 := by
  have heq : (2 * (337) : ℕ) = 674 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_337 : totient 337 = 337 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_337]
  try omega

theorem v3_phi_674 : v3_fast (totient 674) 100 = v3_phi_list.getD 674 0 := by
  rw [tot_674]
  rfl

theorem tot_675 : totient 675 = 360 := by
  have heq : (3^3 * (5^2) : ℕ) = 675 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5]
  try omega

theorem v3_phi_675 : v3_fast (totient 675) 100 = v3_phi_list.getD 675 0 := by
  rw [tot_675]
  rfl

theorem tot_676 : totient 676 = 312 := by
  have heq : (2^2 * (13^2) : ℕ) = 676 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_13]
  try omega

theorem v3_phi_676 : v3_fast (totient 676) 100 = v3_phi_list.getD 676 0 := by
  rw [tot_676]
  rfl

theorem tot_677 : totient 677 = 676 := by
  have h : totient 677 = 677 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_677 : v3_fast (totient 677) 100 = v3_phi_list.getD 677 0 := by
  rw [tot_677]
  rfl

theorem tot_678 : totient 678 = 224 := by
  have heq : (2 * (3 * (113)) : ℕ) = 678 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_113]
  try omega

theorem v3_phi_678 : v3_fast (totient 678) 100 = v3_phi_list.getD 678 0 := by
  rw [tot_678]
  rfl

theorem tot_679 : totient 679 = 576 := by
  have heq : (7 * (97) : ℕ) = 679 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_97]
  try omega

theorem v3_phi_679 : v3_fast (totient 679) 100 = v3_phi_list.getD 679 0 := by
  rw [tot_679]
  rfl

theorem tot_680 : totient 680 = 256 := by
  have heq : (2^3 * (5 * (17)) : ℕ) = 680 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17]
  try omega

theorem v3_phi_680 : v3_fast (totient 680) 100 = v3_phi_list.getD 680 0 := by
  rw [tot_680]
  rfl

theorem tot_681 : totient 681 = 452 := by
  have heq : (3 * (227) : ℕ) = 681 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_227]
  try omega

theorem v3_phi_681 : v3_fast (totient 681) 100 = v3_phi_list.getD 681 0 := by
  rw [tot_681]
  rfl

theorem tot_682 : totient 682 = 300 := by
  have heq : (2 * (11 * (31)) : ℕ) = 682 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_31]
  try omega

theorem v3_phi_682 : v3_fast (totient 682) 100 = v3_phi_list.getD 682 0 := by
  rw [tot_682]
  rfl

theorem tot_683 : totient 683 = 682 := by
  have h : totient 683 = 683 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_683 : v3_fast (totient 683) 100 = v3_phi_list.getD 683 0 := by
  rw [tot_683]
  rfl

theorem tot_684 : totient 684 = 216 := by
  have heq : (2^2 * (3^2 * (19)) : ℕ) = 684 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19]
  try omega

theorem v3_phi_684 : v3_fast (totient 684) 100 = v3_phi_list.getD 684 0 := by
  rw [tot_684]
  rfl

theorem tot_685 : totient 685 = 544 := by
  have heq : (5 * (137) : ℕ) = 685 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_137]
  try omega

theorem v3_phi_685 : v3_fast (totient 685) 100 = v3_phi_list.getD 685 0 := by
  rw [tot_685]
  rfl

theorem tot_686 : totient 686 = 294 := by
  have heq : (2 * (7^3) : ℕ) = 686 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^3) = 7^2 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_686 : v3_fast (totient 686) 100 = v3_phi_list.getD 686 0 := by
  rw [tot_686]
  rfl

theorem tot_687 : totient 687 = 456 := by
  have heq : (3 * (229) : ℕ) = 687 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_229]
  try omega

theorem v3_phi_687 : v3_fast (totient 687) 100 = v3_phi_list.getD 687 0 := by
  rw [tot_687]
  rfl

theorem tot_688 : totient 688 = 336 := by
  have heq : (2^4 * (43) : ℕ) = 688 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_43]
  try omega

theorem v3_phi_688 : v3_fast (totient 688) 100 = v3_phi_list.getD 688 0 := by
  rw [tot_688]
  rfl

theorem tot_689 : totient 689 = 624 := by
  have heq : (13 * (53) : ℕ) = 689 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_53]
  try omega

theorem v3_phi_689 : v3_fast (totient 689) 100 = v3_phi_list.getD 689 0 := by
  rw [tot_689]
  rfl

theorem tot_690 : totient 690 = 176 := by
  have heq : (2 * (3 * (5 * (23))) : ℕ) = 690 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_23]
  try omega

theorem v3_phi_690 : v3_fast (totient 690) 100 = v3_phi_list.getD 690 0 := by
  rw [tot_690]
  rfl

theorem tot_691 : totient 691 = 690 := by
  have h : totient 691 = 691 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_691 : v3_fast (totient 691) 100 = v3_phi_list.getD 691 0 := by
  rw [tot_691]
  rfl

theorem tot_692 : totient 692 = 344 := by
  have heq : (2^2 * (173) : ℕ) = 692 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_173]
  try omega

theorem v3_phi_692 : v3_fast (totient 692) 100 = v3_phi_list.getD 692 0 := by
  rw [tot_692]
  rfl

theorem tot_693 : totient 693 = 360 := by
  have heq : (3^2 * (7 * (11)) : ℕ) = 693 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_11]
  try omega

theorem v3_phi_693 : v3_fast (totient 693) 100 = v3_phi_list.getD 693 0 := by
  rw [tot_693]
  rfl

theorem tot_694 : totient 694 = 346 := by
  have heq : (2 * (347) : ℕ) = 694 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_347 : totient 347 = 347 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_347]
  try omega

theorem v3_phi_694 : v3_fast (totient 694) 100 = v3_phi_list.getD 694 0 := by
  rw [tot_694]
  rfl

theorem tot_695 : totient 695 = 552 := by
  have heq : (5 * (139) : ℕ) = 695 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_139]
  try omega

theorem v3_phi_695 : v3_fast (totient 695) 100 = v3_phi_list.getD 695 0 := by
  rw [tot_695]
  rfl

theorem tot_696 : totient 696 = 224 := by
  have heq : (2^3 * (3 * (29)) : ℕ) = 696 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29]
  try omega

theorem v3_phi_696 : v3_fast (totient 696) 100 = v3_phi_list.getD 696 0 := by
  rw [tot_696]
  rfl

theorem tot_697 : totient 697 = 640 := by
  have heq : (17 * (41) : ℕ) = 697 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_41]
  try omega

theorem v3_phi_697 : v3_fast (totient 697) 100 = v3_phi_list.getD 697 0 := by
  rw [tot_697]
  rfl

theorem tot_698 : totient 698 = 348 := by
  have heq : (2 * (349) : ℕ) = 698 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_349 : totient 349 = 349 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_349]
  try omega

theorem v3_phi_698 : v3_fast (totient 698) 100 = v3_phi_list.getD 698 0 := by
  rw [tot_698]
  rfl

theorem tot_699 : totient 699 = 464 := by
  have heq : (3 * (233) : ℕ) = 699 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_233]
  try omega

theorem v3_phi_699 : v3_fast (totient 699) 100 = v3_phi_list.getD 699 0 := by
  rw [tot_699]
  rfl

theorem tot_700 : totient 700 = 240 := by
  have heq : (2^2 * (5^2 * (7)) : ℕ) = 700 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7]
  try omega

theorem v3_phi_700 : v3_fast (totient 700) 100 = v3_phi_list.getD 700 0 := by
  rw [tot_700]
  rfl

theorem tot_701 : totient 701 = 700 := by
  have h : totient 701 = 701 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_701 : v3_fast (totient 701) 100 = v3_phi_list.getD 701 0 := by
  rw [tot_701]
  rfl

theorem tot_702 : totient 702 = 216 := by
  have heq : (2 * (3^3 * (13)) : ℕ) = 702 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13]
  try omega

theorem v3_phi_702 : v3_fast (totient 702) 100 = v3_phi_list.getD 702 0 := by
  rw [tot_702]
  rfl

theorem tot_703 : totient 703 = 648 := by
  have heq : (19 * (37) : ℕ) = 703 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_37]
  try omega

theorem v3_phi_703 : v3_fast (totient 703) 100 = v3_phi_list.getD 703 0 := by
  rw [tot_703]
  rfl

theorem tot_704 : totient 704 = 320 := by
  have heq : (2^6 * (11) : ℕ) = 704 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11]
  try omega

theorem v3_phi_704 : v3_fast (totient 704) 100 = v3_phi_list.getD 704 0 := by
  rw [tot_704]
  rfl

theorem tot_705 : totient 705 = 368 := by
  have heq : (3 * (5 * (47)) : ℕ) = 705 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_47]
  try omega

theorem v3_phi_705 : v3_fast (totient 705) 100 = v3_phi_list.getD 705 0 := by
  rw [tot_705]
  rfl

theorem tot_706 : totient 706 = 352 := by
  have heq : (2 * (353) : ℕ) = 706 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_353 : totient 353 = 353 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_353]
  try omega

theorem v3_phi_706 : v3_fast (totient 706) 100 = v3_phi_list.getD 706 0 := by
  rw [tot_706]
  rfl

theorem tot_707 : totient 707 = 600 := by
  have heq : (7 * (101) : ℕ) = 707 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_101]
  try omega

theorem v3_phi_707 : v3_fast (totient 707) 100 = v3_phi_list.getD 707 0 := by
  rw [tot_707]
  rfl

theorem tot_708 : totient 708 = 232 := by
  have heq : (2^2 * (3 * (59)) : ℕ) = 708 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_59]
  try omega

theorem v3_phi_708 : v3_fast (totient 708) 100 = v3_phi_list.getD 708 0 := by
  rw [tot_708]
  rfl

theorem tot_709 : totient 709 = 708 := by
  have h : totient 709 = 709 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_709 : v3_fast (totient 709) 100 = v3_phi_list.getD 709 0 := by
  rw [tot_709]
  rfl

theorem tot_710 : totient 710 = 280 := by
  have heq : (2 * (5 * (71)) : ℕ) = 710 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_71]
  try omega

theorem v3_phi_710 : v3_fast (totient 710) 100 = v3_phi_list.getD 710 0 := by
  rw [tot_710]
  rfl

theorem tot_711 : totient 711 = 468 := by
  have heq : (3^2 * (79) : ℕ) = 711 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_79]
  try omega

theorem v3_phi_711 : v3_fast (totient 711) 100 = v3_phi_list.getD 711 0 := by
  rw [tot_711]
  rfl

theorem tot_712 : totient 712 = 352 := by
  have heq : (2^3 * (89) : ℕ) = 712 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_89]
  try omega

theorem v3_phi_712 : v3_fast (totient 712) 100 = v3_phi_list.getD 712 0 := by
  rw [tot_712]
  rfl

theorem tot_713 : totient 713 = 660 := by
  have heq : (23 * (31) : ℕ) = 713 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_31]
  try omega

theorem v3_phi_713 : v3_fast (totient 713) 100 = v3_phi_list.getD 713 0 := by
  rw [tot_713]
  rfl

theorem tot_714 : totient 714 = 192 := by
  have heq : (2 * (3 * (7 * (17))) : ℕ) = 714 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_17]
  try omega

theorem v3_phi_714 : v3_fast (totient 714) 100 = v3_phi_list.getD 714 0 := by
  rw [tot_714]
  rfl

theorem tot_715 : totient 715 = 480 := by
  have heq : (5 * (11 * (13)) : ℕ) = 715 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_13]
  try omega

theorem v3_phi_715 : v3_fast (totient 715) 100 = v3_phi_list.getD 715 0 := by
  rw [tot_715]
  rfl

theorem tot_716 : totient 716 = 356 := by
  have heq : (2^2 * (179) : ℕ) = 716 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_179]
  try omega

theorem v3_phi_716 : v3_fast (totient 716) 100 = v3_phi_list.getD 716 0 := by
  rw [tot_716]
  rfl

theorem tot_717 : totient 717 = 476 := by
  have heq : (3 * (239) : ℕ) = 717 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_239]
  try omega

theorem v3_phi_717 : v3_fast (totient 717) 100 = v3_phi_list.getD 717 0 := by
  rw [tot_717]
  rfl

theorem tot_718 : totient 718 = 358 := by
  have heq : (2 * (359) : ℕ) = 718 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_359 : totient 359 = 359 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_359]
  try omega

theorem v3_phi_718 : v3_fast (totient 718) 100 = v3_phi_list.getD 718 0 := by
  rw [tot_718]
  rfl

theorem tot_719 : totient 719 = 718 := by
  have h : totient 719 = 719 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_719 : v3_fast (totient 719) 100 = v3_phi_list.getD 719 0 := by
  rw [tot_719]
  rfl

theorem tot_720 : totient 720 = 192 := by
  have heq : (2^4 * (3^2 * (5)) : ℕ) = 720 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_720 : v3_fast (totient 720) 100 = v3_phi_list.getD 720 0 := by
  rw [tot_720]
  rfl

theorem tot_721 : totient 721 = 612 := by
  have heq : (7 * (103) : ℕ) = 721 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_103]
  try omega

theorem v3_phi_721 : v3_fast (totient 721) 100 = v3_phi_list.getD 721 0 := by
  rw [tot_721]
  rfl

theorem tot_722 : totient 722 = 342 := by
  have heq : (2 * (19^2) : ℕ) = 722 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient (19^2) = 19^1 * (19 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_19]
  try omega

theorem v3_phi_722 : v3_fast (totient 722) 100 = v3_phi_list.getD 722 0 := by
  rw [tot_722]
  rfl

theorem tot_723 : totient 723 = 480 := by
  have heq : (3 * (241) : ℕ) = 723 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_241]
  try omega

theorem v3_phi_723 : v3_fast (totient 723) 100 = v3_phi_list.getD 723 0 := by
  rw [tot_723]
  rfl

theorem tot_724 : totient 724 = 360 := by
  have heq : (2^2 * (181) : ℕ) = 724 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_181]
  try omega

theorem v3_phi_724 : v3_fast (totient 724) 100 = v3_phi_list.getD 724 0 := by
  rw [tot_724]
  rfl

theorem tot_725 : totient 725 = 560 := by
  have heq : (5^2 * (29) : ℕ) = 725 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_29]
  try omega

theorem v3_phi_725 : v3_fast (totient 725) 100 = v3_phi_list.getD 725 0 := by
  rw [tot_725]
  rfl

theorem tot_726 : totient 726 = 220 := by
  have heq : (2 * (3 * (11^2)) : ℕ) = 726 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_726 : v3_fast (totient 726) 100 = v3_phi_list.getD 726 0 := by
  rw [tot_726]
  rfl

theorem tot_727 : totient 727 = 726 := by
  have h : totient 727 = 727 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_727 : v3_fast (totient 727) 100 = v3_phi_list.getD 727 0 := by
  rw [tot_727]
  rfl

theorem tot_728 : totient 728 = 288 := by
  have heq : (2^3 * (7 * (13)) : ℕ) = 728 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_13]
  try omega

theorem v3_phi_728 : v3_fast (totient 728) 100 = v3_phi_list.getD 728 0 := by
  rw [tot_728]
  rfl

theorem tot_729 : totient 729 = 486 := by
  have h : totient (3^6) = 3^5 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (3^6 : ℕ) = 729 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_729 : v3_fast (totient 729) 100 = v3_phi_list.getD 729 0 := by
  rw [tot_729]
  rfl

theorem tot_730 : totient 730 = 288 := by
  have heq : (2 * (5 * (73)) : ℕ) = 730 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_73]
  try omega

theorem v3_phi_730 : v3_fast (totient 730) 100 = v3_phi_list.getD 730 0 := by
  rw [tot_730]
  rfl

theorem tot_731 : totient 731 = 672 := by
  have heq : (17 * (43) : ℕ) = 731 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_43]
  try omega

theorem v3_phi_731 : v3_fast (totient 731) 100 = v3_phi_list.getD 731 0 := by
  rw [tot_731]
  rfl

theorem tot_732 : totient 732 = 240 := by
  have heq : (2^2 * (3 * (61)) : ℕ) = 732 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_61]
  try omega

theorem v3_phi_732 : v3_fast (totient 732) 100 = v3_phi_list.getD 732 0 := by
  rw [tot_732]
  rfl

theorem tot_733 : totient 733 = 732 := by
  have h : totient 733 = 733 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_733 : v3_fast (totient 733) 100 = v3_phi_list.getD 733 0 := by
  rw [tot_733]
  rfl

theorem tot_734 : totient 734 = 366 := by
  have heq : (2 * (367) : ℕ) = 734 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_367 : totient 367 = 367 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_367]
  try omega

theorem v3_phi_734 : v3_fast (totient 734) 100 = v3_phi_list.getD 734 0 := by
  rw [tot_734]
  rfl

theorem tot_735 : totient 735 = 336 := by
  have heq : (3 * (5 * (7^2)) : ℕ) = 735 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_735 : v3_fast (totient 735) 100 = v3_phi_list.getD 735 0 := by
  rw [tot_735]
  rfl

theorem tot_736 : totient 736 = 352 := by
  have heq : (2^5 * (23) : ℕ) = 736 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23]
  try omega

theorem v3_phi_736 : v3_fast (totient 736) 100 = v3_phi_list.getD 736 0 := by
  rw [tot_736]
  rfl

theorem tot_737 : totient 737 = 660 := by
  have heq : (11 * (67) : ℕ) = 737 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_67]
  try omega

theorem v3_phi_737 : v3_fast (totient 737) 100 = v3_phi_list.getD 737 0 := by
  rw [tot_737]
  rfl

theorem tot_738 : totient 738 = 240 := by
  have heq : (2 * (3^2 * (41)) : ℕ) = 738 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_41]
  try omega

theorem v3_phi_738 : v3_fast (totient 738) 100 = v3_phi_list.getD 738 0 := by
  rw [tot_738]
  rfl

theorem tot_739 : totient 739 = 738 := by
  have h : totient 739 = 739 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_739 : v3_fast (totient 739) 100 = v3_phi_list.getD 739 0 := by
  rw [tot_739]
  rfl

theorem tot_740 : totient 740 = 288 := by
  have heq : (2^2 * (5 * (37)) : ℕ) = 740 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_37]
  try omega

theorem v3_phi_740 : v3_fast (totient 740) 100 = v3_phi_list.getD 740 0 := by
  rw [tot_740]
  rfl

theorem tot_741 : totient 741 = 432 := by
  have heq : (3 * (13 * (19)) : ℕ) = 741 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_19]
  try omega

theorem v3_phi_741 : v3_fast (totient 741) 100 = v3_phi_list.getD 741 0 := by
  rw [tot_741]
  rfl

theorem tot_742 : totient 742 = 312 := by
  have heq : (2 * (7 * (53)) : ℕ) = 742 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_53]
  try omega

theorem v3_phi_742 : v3_fast (totient 742) 100 = v3_phi_list.getD 742 0 := by
  rw [tot_742]
  rfl

theorem tot_743 : totient 743 = 742 := by
  have h : totient 743 = 743 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_743 : v3_fast (totient 743) 100 = v3_phi_list.getD 743 0 := by
  rw [tot_743]
  rfl

theorem tot_744 : totient 744 = 240 := by
  have heq : (2^3 * (3 * (31)) : ℕ) = 744 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31]
  try omega

theorem v3_phi_744 : v3_fast (totient 744) 100 = v3_phi_list.getD 744 0 := by
  rw [tot_744]
  rfl

theorem tot_745 : totient 745 = 592 := by
  have heq : (5 * (149) : ℕ) = 745 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_149]
  try omega

theorem v3_phi_745 : v3_fast (totient 745) 100 = v3_phi_list.getD 745 0 := by
  rw [tot_745]
  rfl

theorem tot_746 : totient 746 = 372 := by
  have heq : (2 * (373) : ℕ) = 746 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_373 : totient 373 = 373 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_373]
  try omega

theorem v3_phi_746 : v3_fast (totient 746) 100 = v3_phi_list.getD 746 0 := by
  rw [tot_746]
  rfl

theorem tot_747 : totient 747 = 492 := by
  have heq : (3^2 * (83) : ℕ) = 747 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_83]
  try omega

theorem v3_phi_747 : v3_fast (totient 747) 100 = v3_phi_list.getD 747 0 := by
  rw [tot_747]
  rfl

theorem tot_748 : totient 748 = 320 := by
  have heq : (2^2 * (11 * (17)) : ℕ) = 748 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_17]
  try omega

theorem v3_phi_748 : v3_fast (totient 748) 100 = v3_phi_list.getD 748 0 := by
  rw [tot_748]
  rfl

theorem tot_749 : totient 749 = 636 := by
  have heq : (7 * (107) : ℕ) = 749 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_107]
  try omega

theorem v3_phi_749 : v3_fast (totient 749) 100 = v3_phi_list.getD 749 0 := by
  rw [tot_749]
  rfl

theorem tot_750 : totient 750 = 200 := by
  have heq : (2 * (3 * (5^3)) : ℕ) = 750 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_750 : v3_fast (totient 750) 100 = v3_phi_list.getD 750 0 := by
  rw [tot_750]
  rfl

theorem tot_751 : totient 751 = 750 := by
  have h : totient 751 = 751 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_751 : v3_fast (totient 751) 100 = v3_phi_list.getD 751 0 := by
  rw [tot_751]
  rfl

theorem tot_752 : totient 752 = 368 := by
  have heq : (2^4 * (47) : ℕ) = 752 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_47]
  try omega

theorem v3_phi_752 : v3_fast (totient 752) 100 = v3_phi_list.getD 752 0 := by
  rw [tot_752]
  rfl

theorem tot_753 : totient 753 = 500 := by
  have heq : (3 * (251) : ℕ) = 753 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_251]
  try omega

theorem v3_phi_753 : v3_fast (totient 753) 100 = v3_phi_list.getD 753 0 := by
  rw [tot_753]
  rfl

theorem tot_754 : totient 754 = 336 := by
  have heq : (2 * (13 * (29)) : ℕ) = 754 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_29]
  try omega

theorem v3_phi_754 : v3_fast (totient 754) 100 = v3_phi_list.getD 754 0 := by
  rw [tot_754]
  rfl

theorem tot_755 : totient 755 = 600 := by
  have heq : (5 * (151) : ℕ) = 755 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_151]
  try omega

theorem v3_phi_755 : v3_fast (totient 755) 100 = v3_phi_list.getD 755 0 := by
  rw [tot_755]
  rfl

theorem tot_756 : totient 756 = 216 := by
  have heq : (2^2 * (3^3 * (7)) : ℕ) = 756 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_756 : v3_fast (totient 756) 100 = v3_phi_list.getD 756 0 := by
  rw [tot_756]
  rfl

theorem tot_757 : totient 757 = 756 := by
  have h : totient 757 = 757 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_757 : v3_fast (totient 757) 100 = v3_phi_list.getD 757 0 := by
  rw [tot_757]
  rfl

theorem tot_758 : totient 758 = 378 := by
  have heq : (2 * (379) : ℕ) = 758 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_379 : totient 379 = 379 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_379]
  try omega

theorem v3_phi_758 : v3_fast (totient 758) 100 = v3_phi_list.getD 758 0 := by
  rw [tot_758]
  rfl

theorem tot_759 : totient 759 = 440 := by
  have heq : (3 * (11 * (23)) : ℕ) = 759 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_23]
  try omega

theorem v3_phi_759 : v3_fast (totient 759) 100 = v3_phi_list.getD 759 0 := by
  rw [tot_759]
  rfl

theorem tot_760 : totient 760 = 288 := by
  have heq : (2^3 * (5 * (19)) : ℕ) = 760 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_19]
  try omega

theorem v3_phi_760 : v3_fast (totient 760) 100 = v3_phi_list.getD 760 0 := by
  rw [tot_760]
  rfl

theorem tot_761 : totient 761 = 760 := by
  have h : totient 761 = 761 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_761 : v3_fast (totient 761) 100 = v3_phi_list.getD 761 0 := by
  rw [tot_761]
  rfl

theorem tot_762 : totient 762 = 252 := by
  have heq : (2 * (3 * (127)) : ℕ) = 762 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_127]
  try omega

theorem v3_phi_762 : v3_fast (totient 762) 100 = v3_phi_list.getD 762 0 := by
  rw [tot_762]
  rfl

theorem tot_763 : totient 763 = 648 := by
  have heq : (7 * (109) : ℕ) = 763 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_109]
  try omega

theorem v3_phi_763 : v3_fast (totient 763) 100 = v3_phi_list.getD 763 0 := by
  rw [tot_763]
  rfl

theorem tot_764 : totient 764 = 380 := by
  have heq : (2^2 * (191) : ℕ) = 764 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_191]
  try omega

theorem v3_phi_764 : v3_fast (totient 764) 100 = v3_phi_list.getD 764 0 := by
  rw [tot_764]
  rfl

theorem tot_765 : totient 765 = 384 := by
  have heq : (3^2 * (5 * (17)) : ℕ) = 765 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_17]
  try omega

theorem v3_phi_765 : v3_fast (totient 765) 100 = v3_phi_list.getD 765 0 := by
  rw [tot_765]
  rfl

theorem tot_766 : totient 766 = 382 := by
  have heq : (2 * (383) : ℕ) = 766 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_383 : totient 383 = 383 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_383]
  try omega

theorem v3_phi_766 : v3_fast (totient 766) 100 = v3_phi_list.getD 766 0 := by
  rw [tot_766]
  rfl

theorem tot_767 : totient 767 = 696 := by
  have heq : (13 * (59) : ℕ) = 767 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_59]
  try omega

theorem v3_phi_767 : v3_fast (totient 767) 100 = v3_phi_list.getD 767 0 := by
  rw [tot_767]
  rfl

theorem tot_768 : totient 768 = 256 := by
  have heq : (2^8 * (3) : ℕ) = 768 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^8) = 2^7 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_768 : v3_fast (totient 768) 100 = v3_phi_list.getD 768 0 := by
  rw [tot_768]
  rfl

theorem tot_769 : totient 769 = 768 := by
  have h : totient 769 = 769 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_769 : v3_fast (totient 769) 100 = v3_phi_list.getD 769 0 := by
  rw [tot_769]
  rfl

theorem tot_770 : totient 770 = 240 := by
  have heq : (2 * (5 * (7 * (11))) : ℕ) = 770 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_11]
  try omega

theorem v3_phi_770 : v3_fast (totient 770) 100 = v3_phi_list.getD 770 0 := by
  rw [tot_770]
  rfl

theorem tot_771 : totient 771 = 512 := by
  have heq : (3 * (257) : ℕ) = 771 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_257]
  try omega

theorem v3_phi_771 : v3_fast (totient 771) 100 = v3_phi_list.getD 771 0 := by
  rw [tot_771]
  rfl

theorem tot_772 : totient 772 = 384 := by
  have heq : (2^2 * (193) : ℕ) = 772 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_193]
  try omega

theorem v3_phi_772 : v3_fast (totient 772) 100 = v3_phi_list.getD 772 0 := by
  rw [tot_772]
  rfl

theorem tot_773 : totient 773 = 772 := by
  have h : totient 773 = 773 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_773 : v3_fast (totient 773) 100 = v3_phi_list.getD 773 0 := by
  rw [tot_773]
  rfl

theorem tot_774 : totient 774 = 252 := by
  have heq : (2 * (3^2 * (43)) : ℕ) = 774 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_43]
  try omega

theorem v3_phi_774 : v3_fast (totient 774) 100 = v3_phi_list.getD 774 0 := by
  rw [tot_774]
  rfl

theorem tot_775 : totient 775 = 600 := by
  have heq : (5^2 * (31) : ℕ) = 775 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_31]
  try omega

theorem v3_phi_775 : v3_fast (totient 775) 100 = v3_phi_list.getD 775 0 := by
  rw [tot_775]
  rfl

theorem tot_776 : totient 776 = 384 := by
  have heq : (2^3 * (97) : ℕ) = 776 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_97]
  try omega

theorem v3_phi_776 : v3_fast (totient 776) 100 = v3_phi_list.getD 776 0 := by
  rw [tot_776]
  rfl

theorem tot_777 : totient 777 = 432 := by
  have heq : (3 * (7 * (37)) : ℕ) = 777 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_37]
  try omega

theorem v3_phi_777 : v3_fast (totient 777) 100 = v3_phi_list.getD 777 0 := by
  rw [tot_777]
  rfl

theorem tot_778 : totient 778 = 388 := by
  have heq : (2 * (389) : ℕ) = 778 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_389 : totient 389 = 389 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_389]
  try omega

theorem v3_phi_778 : v3_fast (totient 778) 100 = v3_phi_list.getD 778 0 := by
  rw [tot_778]
  rfl

theorem tot_779 : totient 779 = 720 := by
  have heq : (19 * (41) : ℕ) = 779 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_41]
  try omega

theorem v3_phi_779 : v3_fast (totient 779) 100 = v3_phi_list.getD 779 0 := by
  rw [tot_779]
  rfl

theorem tot_780 : totient 780 = 192 := by
  have heq : (2^2 * (3 * (5 * (13))) : ℕ) = 780 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_13]
  try omega

theorem v3_phi_780 : v3_fast (totient 780) 100 = v3_phi_list.getD 780 0 := by
  rw [tot_780]
  rfl

theorem tot_781 : totient 781 = 700 := by
  have heq : (11 * (71) : ℕ) = 781 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_71]
  try omega

theorem v3_phi_781 : v3_fast (totient 781) 100 = v3_phi_list.getD 781 0 := by
  rw [tot_781]
  rfl

theorem tot_782 : totient 782 = 352 := by
  have heq : (2 * (17 * (23)) : ℕ) = 782 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_23]
  try omega

theorem v3_phi_782 : v3_fast (totient 782) 100 = v3_phi_list.getD 782 0 := by
  rw [tot_782]
  rfl

theorem tot_783 : totient 783 = 504 := by
  have heq : (3^3 * (29) : ℕ) = 783 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_29]
  try omega

theorem v3_phi_783 : v3_fast (totient 783) 100 = v3_phi_list.getD 783 0 := by
  rw [tot_783]
  rfl

theorem tot_784 : totient 784 = 336 := by
  have heq : (2^4 * (7^2) : ℕ) = 784 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_784 : v3_fast (totient 784) 100 = v3_phi_list.getD 784 0 := by
  rw [tot_784]
  rfl

theorem tot_785 : totient 785 = 624 := by
  have heq : (5 * (157) : ℕ) = 785 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_157]
  try omega

theorem v3_phi_785 : v3_fast (totient 785) 100 = v3_phi_list.getD 785 0 := by
  rw [tot_785]
  rfl

theorem tot_786 : totient 786 = 260 := by
  have heq : (2 * (3 * (131)) : ℕ) = 786 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_131]
  try omega

theorem v3_phi_786 : v3_fast (totient 786) 100 = v3_phi_list.getD 786 0 := by
  rw [tot_786]
  rfl

theorem tot_787 : totient 787 = 786 := by
  have h : totient 787 = 787 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_787 : v3_fast (totient 787) 100 = v3_phi_list.getD 787 0 := by
  rw [tot_787]
  rfl

theorem tot_788 : totient 788 = 392 := by
  have heq : (2^2 * (197) : ℕ) = 788 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_197]
  try omega

theorem v3_phi_788 : v3_fast (totient 788) 100 = v3_phi_list.getD 788 0 := by
  rw [tot_788]
  rfl

theorem tot_789 : totient 789 = 524 := by
  have heq : (3 * (263) : ℕ) = 789 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_263 : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_263]
  try omega

theorem v3_phi_789 : v3_fast (totient 789) 100 = v3_phi_list.getD 789 0 := by
  rw [tot_789]
  rfl

theorem tot_790 : totient 790 = 312 := by
  have heq : (2 * (5 * (79)) : ℕ) = 790 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_79]
  try omega

theorem v3_phi_790 : v3_fast (totient 790) 100 = v3_phi_list.getD 790 0 := by
  rw [tot_790]
  rfl

theorem tot_791 : totient 791 = 672 := by
  have heq : (7 * (113) : ℕ) = 791 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_113]
  try omega

theorem v3_phi_791 : v3_fast (totient 791) 100 = v3_phi_list.getD 791 0 := by
  rw [tot_791]
  rfl

theorem tot_792 : totient 792 = 240 := by
  have heq : (2^3 * (3^2 * (11)) : ℕ) = 792 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_792 : v3_fast (totient 792) 100 = v3_phi_list.getD 792 0 := by
  rw [tot_792]
  rfl

theorem tot_793 : totient 793 = 720 := by
  have heq : (13 * (61) : ℕ) = 793 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_61]
  try omega

theorem v3_phi_793 : v3_fast (totient 793) 100 = v3_phi_list.getD 793 0 := by
  rw [tot_793]
  rfl

theorem tot_794 : totient 794 = 396 := by
  have heq : (2 * (397) : ℕ) = 794 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_397 : totient 397 = 397 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_397]
  try omega

theorem v3_phi_794 : v3_fast (totient 794) 100 = v3_phi_list.getD 794 0 := by
  rw [tot_794]
  rfl

theorem tot_795 : totient 795 = 416 := by
  have heq : (3 * (5 * (53)) : ℕ) = 795 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_53]
  try omega

theorem v3_phi_795 : v3_fast (totient 795) 100 = v3_phi_list.getD 795 0 := by
  rw [tot_795]
  rfl

theorem tot_796 : totient 796 = 396 := by
  have heq : (2^2 * (199) : ℕ) = 796 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_199]
  try omega

theorem v3_phi_796 : v3_fast (totient 796) 100 = v3_phi_list.getD 796 0 := by
  rw [tot_796]
  rfl

theorem tot_797 : totient 797 = 796 := by
  have h : totient 797 = 797 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_797 : v3_fast (totient 797) 100 = v3_phi_list.getD 797 0 := by
  rw [tot_797]
  rfl

theorem tot_798 : totient 798 = 216 := by
  have heq : (2 * (3 * (7 * (19))) : ℕ) = 798 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_19]
  try omega

theorem v3_phi_798 : v3_fast (totient 798) 100 = v3_phi_list.getD 798 0 := by
  rw [tot_798]
  rfl

theorem tot_799 : totient 799 = 736 := by
  have heq : (17 * (47) : ℕ) = 799 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_47]
  try omega

theorem v3_phi_799 : v3_fast (totient 799) 100 = v3_phi_list.getD 799 0 := by
  rw [tot_799]
  rfl

theorem tot_800 : totient 800 = 320 := by
  have heq : (2^5 * (5^2) : ℕ) = 800 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_800 : v3_fast (totient 800) 100 = v3_phi_list.getD 800 0 := by
  rw [tot_800]
  rfl

theorem tot_801 : totient 801 = 528 := by
  have heq : (3^2 * (89) : ℕ) = 801 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_89]
  try omega

theorem v3_phi_801 : v3_fast (totient 801) 100 = v3_phi_list.getD 801 0 := by
  rw [tot_801]
  rfl

theorem tot_802 : totient 802 = 400 := by
  have heq : (2 * (401) : ℕ) = 802 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_401 : totient 401 = 401 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_401]
  try omega

theorem v3_phi_802 : v3_fast (totient 802) 100 = v3_phi_list.getD 802 0 := by
  rw [tot_802]
  rfl

theorem tot_803 : totient 803 = 720 := by
  have heq : (11 * (73) : ℕ) = 803 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_73]
  try omega

theorem v3_phi_803 : v3_fast (totient 803) 100 = v3_phi_list.getD 803 0 := by
  rw [tot_803]
  rfl

theorem tot_804 : totient 804 = 264 := by
  have heq : (2^2 * (3 * (67)) : ℕ) = 804 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_67]
  try omega

theorem v3_phi_804 : v3_fast (totient 804) 100 = v3_phi_list.getD 804 0 := by
  rw [tot_804]
  rfl

theorem tot_805 : totient 805 = 528 := by
  have heq : (5 * (7 * (23)) : ℕ) = 805 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_23]
  try omega

theorem v3_phi_805 : v3_fast (totient 805) 100 = v3_phi_list.getD 805 0 := by
  rw [tot_805]
  rfl

theorem tot_806 : totient 806 = 360 := by
  have heq : (2 * (13 * (31)) : ℕ) = 806 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_31]
  try omega

theorem v3_phi_806 : v3_fast (totient 806) 100 = v3_phi_list.getD 806 0 := by
  rw [tot_806]
  rfl

theorem tot_807 : totient 807 = 536 := by
  have heq : (3 * (269) : ℕ) = 807 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_269 : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_269]
  try omega

theorem v3_phi_807 : v3_fast (totient 807) 100 = v3_phi_list.getD 807 0 := by
  rw [tot_807]
  rfl

theorem tot_808 : totient 808 = 400 := by
  have heq : (2^3 * (101) : ℕ) = 808 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_101]
  try omega

theorem v3_phi_808 : v3_fast (totient 808) 100 = v3_phi_list.getD 808 0 := by
  rw [tot_808]
  rfl

theorem tot_809 : totient 809 = 808 := by
  have h : totient 809 = 809 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_809 : v3_fast (totient 809) 100 = v3_phi_list.getD 809 0 := by
  rw [tot_809]
  rfl

theorem tot_810 : totient 810 = 216 := by
  have heq : (2 * (3^4 * (5)) : ℕ) = 810 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_810 : v3_fast (totient 810) 100 = v3_phi_list.getD 810 0 := by
  rw [tot_810]
  rfl

theorem tot_811 : totient 811 = 810 := by
  have h : totient 811 = 811 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_811 : v3_fast (totient 811) 100 = v3_phi_list.getD 811 0 := by
  rw [tot_811]
  rfl

theorem tot_812 : totient 812 = 336 := by
  have heq : (2^2 * (7 * (29)) : ℕ) = 812 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_29]
  try omega

theorem v3_phi_812 : v3_fast (totient 812) 100 = v3_phi_list.getD 812 0 := by
  rw [tot_812]
  rfl

theorem tot_813 : totient 813 = 540 := by
  have heq : (3 * (271) : ℕ) = 813 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_271 : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_271]
  try omega

theorem v3_phi_813 : v3_fast (totient 813) 100 = v3_phi_list.getD 813 0 := by
  rw [tot_813]
  rfl

theorem tot_814 : totient 814 = 360 := by
  have heq : (2 * (11 * (37)) : ℕ) = 814 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_37]
  try omega

theorem v3_phi_814 : v3_fast (totient 814) 100 = v3_phi_list.getD 814 0 := by
  rw [tot_814]
  rfl

theorem tot_815 : totient 815 = 648 := by
  have heq : (5 * (163) : ℕ) = 815 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_163]
  try omega

theorem v3_phi_815 : v3_fast (totient 815) 100 = v3_phi_list.getD 815 0 := by
  rw [tot_815]
  rfl

theorem tot_816 : totient 816 = 256 := by
  have heq : (2^4 * (3 * (17)) : ℕ) = 816 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17]
  try omega

theorem v3_phi_816 : v3_fast (totient 816) 100 = v3_phi_list.getD 816 0 := by
  rw [tot_816]
  rfl

theorem tot_817 : totient 817 = 756 := by
  have heq : (19 * (43) : ℕ) = 817 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_43]
  try omega

theorem v3_phi_817 : v3_fast (totient 817) 100 = v3_phi_list.getD 817 0 := by
  rw [tot_817]
  rfl

theorem tot_818 : totient 818 = 408 := by
  have heq : (2 * (409) : ℕ) = 818 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_409 : totient 409 = 409 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_409]
  try omega

theorem v3_phi_818 : v3_fast (totient 818) 100 = v3_phi_list.getD 818 0 := by
  rw [tot_818]
  rfl

theorem tot_819 : totient 819 = 432 := by
  have heq : (3^2 * (7 * (13)) : ℕ) = 819 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_13]
  try omega

theorem v3_phi_819 : v3_fast (totient 819) 100 = v3_phi_list.getD 819 0 := by
  rw [tot_819]
  rfl

theorem tot_820 : totient 820 = 320 := by
  have heq : (2^2 * (5 * (41)) : ℕ) = 820 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_41]
  try omega

theorem v3_phi_820 : v3_fast (totient 820) 100 = v3_phi_list.getD 820 0 := by
  rw [tot_820]
  rfl

theorem tot_821 : totient 821 = 820 := by
  have h : totient 821 = 821 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_821 : v3_fast (totient 821) 100 = v3_phi_list.getD 821 0 := by
  rw [tot_821]
  rfl

theorem tot_822 : totient 822 = 272 := by
  have heq : (2 * (3 * (137)) : ℕ) = 822 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_137]
  try omega

theorem v3_phi_822 : v3_fast (totient 822) 100 = v3_phi_list.getD 822 0 := by
  rw [tot_822]
  rfl

theorem tot_823 : totient 823 = 822 := by
  have h : totient 823 = 823 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_823 : v3_fast (totient 823) 100 = v3_phi_list.getD 823 0 := by
  rw [tot_823]
  rfl

theorem tot_824 : totient 824 = 408 := by
  have heq : (2^3 * (103) : ℕ) = 824 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_103]
  try omega

theorem v3_phi_824 : v3_fast (totient 824) 100 = v3_phi_list.getD 824 0 := by
  rw [tot_824]
  rfl

theorem tot_825 : totient 825 = 400 := by
  have heq : (3 * (5^2 * (11)) : ℕ) = 825 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_11]
  try omega

theorem v3_phi_825 : v3_fast (totient 825) 100 = v3_phi_list.getD 825 0 := by
  rw [tot_825]
  rfl

theorem tot_826 : totient 826 = 348 := by
  have heq : (2 * (7 * (59)) : ℕ) = 826 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_59]
  try omega

theorem v3_phi_826 : v3_fast (totient 826) 100 = v3_phi_list.getD 826 0 := by
  rw [tot_826]
  rfl

theorem tot_827 : totient 827 = 826 := by
  have h : totient 827 = 827 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_827 : v3_fast (totient 827) 100 = v3_phi_list.getD 827 0 := by
  rw [tot_827]
  rfl

theorem tot_828 : totient 828 = 264 := by
  have heq : (2^2 * (3^2 * (23)) : ℕ) = 828 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23]
  try omega

theorem v3_phi_828 : v3_fast (totient 828) 100 = v3_phi_list.getD 828 0 := by
  rw [tot_828]
  rfl

theorem tot_829 : totient 829 = 828 := by
  have h : totient 829 = 829 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_829 : v3_fast (totient 829) 100 = v3_phi_list.getD 829 0 := by
  rw [tot_829]
  rfl

theorem tot_830 : totient 830 = 328 := by
  have heq : (2 * (5 * (83)) : ℕ) = 830 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_83]
  try omega

theorem v3_phi_830 : v3_fast (totient 830) 100 = v3_phi_list.getD 830 0 := by
  rw [tot_830]
  rfl

theorem tot_831 : totient 831 = 552 := by
  have heq : (3 * (277) : ℕ) = 831 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_277 : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_277]
  try omega

theorem v3_phi_831 : v3_fast (totient 831) 100 = v3_phi_list.getD 831 0 := by
  rw [tot_831]
  rfl

theorem tot_832 : totient 832 = 384 := by
  have heq : (2^6 * (13) : ℕ) = 832 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13]
  try omega

theorem v3_phi_832 : v3_fast (totient 832) 100 = v3_phi_list.getD 832 0 := by
  rw [tot_832]
  rfl

theorem tot_833 : totient 833 = 672 := by
  have heq : (7^2 * (17) : ℕ) = 833 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_17]
  try omega

theorem v3_phi_833 : v3_fast (totient 833) 100 = v3_phi_list.getD 833 0 := by
  rw [tot_833]
  rfl

theorem tot_834 : totient 834 = 276 := by
  have heq : (2 * (3 * (139)) : ℕ) = 834 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_139]
  try omega

theorem v3_phi_834 : v3_fast (totient 834) 100 = v3_phi_list.getD 834 0 := by
  rw [tot_834]
  rfl

theorem tot_835 : totient 835 = 664 := by
  have heq : (5 * (167) : ℕ) = 835 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_167]
  try omega

theorem v3_phi_835 : v3_fast (totient 835) 100 = v3_phi_list.getD 835 0 := by
  rw [tot_835]
  rfl

theorem tot_836 : totient 836 = 360 := by
  have heq : (2^2 * (11 * (19)) : ℕ) = 836 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_19]
  try omega

theorem v3_phi_836 : v3_fast (totient 836) 100 = v3_phi_list.getD 836 0 := by
  rw [tot_836]
  rfl

theorem tot_837 : totient 837 = 540 := by
  have heq : (3^3 * (31) : ℕ) = 837 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_31]
  try omega

theorem v3_phi_837 : v3_fast (totient 837) 100 = v3_phi_list.getD 837 0 := by
  rw [tot_837]
  rfl

theorem tot_838 : totient 838 = 418 := by
  have heq : (2 * (419) : ℕ) = 838 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_419 : totient 419 = 419 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_419]
  try omega

theorem v3_phi_838 : v3_fast (totient 838) 100 = v3_phi_list.getD 838 0 := by
  rw [tot_838]
  rfl

theorem tot_839 : totient 839 = 838 := by
  have h : totient 839 = 839 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_839 : v3_fast (totient 839) 100 = v3_phi_list.getD 839 0 := by
  rw [tot_839]
  rfl

theorem tot_840 : totient 840 = 192 := by
  have heq : (2^3 * (3 * (5 * (7))) : ℕ) = 840 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_840 : v3_fast (totient 840) 100 = v3_phi_list.getD 840 0 := by
  rw [tot_840]
  rfl

theorem tot_841 : totient 841 = 812 := by
  have h : totient (29^2) = 29^1 * (29 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (29^2 : ℕ) = 841 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_841 : v3_fast (totient 841) 100 = v3_phi_list.getD 841 0 := by
  rw [tot_841]
  rfl

theorem tot_842 : totient 842 = 420 := by
  have heq : (2 * (421) : ℕ) = 842 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_421 : totient 421 = 421 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_421]
  try omega

theorem v3_phi_842 : v3_fast (totient 842) 100 = v3_phi_list.getD 842 0 := by
  rw [tot_842]
  rfl

theorem tot_843 : totient 843 = 560 := by
  have heq : (3 * (281) : ℕ) = 843 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_281 : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_281]
  try omega

theorem v3_phi_843 : v3_fast (totient 843) 100 = v3_phi_list.getD 843 0 := by
  rw [tot_843]
  rfl

theorem tot_844 : totient 844 = 420 := by
  have heq : (2^2 * (211) : ℕ) = 844 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_211]
  try omega

theorem v3_phi_844 : v3_fast (totient 844) 100 = v3_phi_list.getD 844 0 := by
  rw [tot_844]
  rfl

theorem tot_845 : totient 845 = 624 := by
  have heq : (5 * (13^2) : ℕ) = 845 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_13]
  try omega

theorem v3_phi_845 : v3_fast (totient 845) 100 = v3_phi_list.getD 845 0 := by
  rw [tot_845]
  rfl

theorem tot_846 : totient 846 = 276 := by
  have heq : (2 * (3^2 * (47)) : ℕ) = 846 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_47]
  try omega

theorem v3_phi_846 : v3_fast (totient 846) 100 = v3_phi_list.getD 846 0 := by
  rw [tot_846]
  rfl

theorem tot_847 : totient 847 = 660 := by
  have heq : (7 * (11^2) : ℕ) = 847 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_7, hp_11]
  try omega

theorem v3_phi_847 : v3_fast (totient 847) 100 = v3_phi_list.getD 847 0 := by
  rw [tot_847]
  rfl

theorem tot_848 : totient 848 = 416 := by
  have heq : (2^4 * (53) : ℕ) = 848 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_53]
  try omega

theorem v3_phi_848 : v3_fast (totient 848) 100 = v3_phi_list.getD 848 0 := by
  rw [tot_848]
  rfl

theorem tot_849 : totient 849 = 564 := by
  have heq : (3 * (283) : ℕ) = 849 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_283 : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_283]
  try omega

theorem v3_phi_849 : v3_fast (totient 849) 100 = v3_phi_list.getD 849 0 := by
  rw [tot_849]
  rfl

theorem tot_850 : totient 850 = 320 := by
  have heq : (2 * (5^2 * (17)) : ℕ) = 850 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17]
  try omega

theorem v3_phi_850 : v3_fast (totient 850) 100 = v3_phi_list.getD 850 0 := by
  rw [tot_850]
  rfl

theorem tot_851 : totient 851 = 792 := by
  have heq : (23 * (37) : ℕ) = 851 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_37]
  try omega

theorem v3_phi_851 : v3_fast (totient 851) 100 = v3_phi_list.getD 851 0 := by
  rw [tot_851]
  rfl

theorem tot_852 : totient 852 = 280 := by
  have heq : (2^2 * (3 * (71)) : ℕ) = 852 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_71]
  try omega

theorem v3_phi_852 : v3_fast (totient 852) 100 = v3_phi_list.getD 852 0 := by
  rw [tot_852]
  rfl

theorem tot_853 : totient 853 = 852 := by
  have h : totient 853 = 853 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_853 : v3_fast (totient 853) 100 = v3_phi_list.getD 853 0 := by
  rw [tot_853]
  rfl

theorem tot_854 : totient 854 = 360 := by
  have heq : (2 * (7 * (61)) : ℕ) = 854 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_61]
  try omega

theorem v3_phi_854 : v3_fast (totient 854) 100 = v3_phi_list.getD 854 0 := by
  rw [tot_854]
  rfl

theorem tot_855 : totient 855 = 432 := by
  have heq : (3^2 * (5 * (19)) : ℕ) = 855 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_19]
  try omega

theorem v3_phi_855 : v3_fast (totient 855) 100 = v3_phi_list.getD 855 0 := by
  rw [tot_855]
  rfl

theorem tot_856 : totient 856 = 424 := by
  have heq : (2^3 * (107) : ℕ) = 856 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_107]
  try omega

theorem v3_phi_856 : v3_fast (totient 856) 100 = v3_phi_list.getD 856 0 := by
  rw [tot_856]
  rfl

theorem tot_857 : totient 857 = 856 := by
  have h : totient 857 = 857 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_857 : v3_fast (totient 857) 100 = v3_phi_list.getD 857 0 := by
  rw [tot_857]
  rfl

theorem tot_858 : totient 858 = 240 := by
  have heq : (2 * (3 * (11 * (13))) : ℕ) = 858 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11, hp_13]
  try omega

theorem v3_phi_858 : v3_fast (totient 858) 100 = v3_phi_list.getD 858 0 := by
  rw [tot_858]
  rfl

theorem tot_859 : totient 859 = 858 := by
  have h : totient 859 = 859 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_859 : v3_fast (totient 859) 100 = v3_phi_list.getD 859 0 := by
  rw [tot_859]
  rfl

theorem tot_860 : totient 860 = 336 := by
  have heq : (2^2 * (5 * (43)) : ℕ) = 860 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_43]
  try omega

theorem v3_phi_860 : v3_fast (totient 860) 100 = v3_phi_list.getD 860 0 := by
  rw [tot_860]
  rfl

theorem tot_861 : totient 861 = 480 := by
  have heq : (3 * (7 * (41)) : ℕ) = 861 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_41]
  try omega

theorem v3_phi_861 : v3_fast (totient 861) 100 = v3_phi_list.getD 861 0 := by
  rw [tot_861]
  rfl

theorem tot_862 : totient 862 = 430 := by
  have heq : (2 * (431) : ℕ) = 862 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_431 : totient 431 = 431 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_431]
  try omega

theorem v3_phi_862 : v3_fast (totient 862) 100 = v3_phi_list.getD 862 0 := by
  rw [tot_862]
  rfl

theorem tot_863 : totient 863 = 862 := by
  have h : totient 863 = 863 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_863 : v3_fast (totient 863) 100 = v3_phi_list.getD 863 0 := by
  rw [tot_863]
  rfl

theorem tot_864 : totient 864 = 288 := by
  have heq : (2^5 * (3^3) : ℕ) = 864 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_864 : v3_fast (totient 864) 100 = v3_phi_list.getD 864 0 := by
  rw [tot_864]
  rfl

theorem tot_865 : totient 865 = 688 := by
  have heq : (5 * (173) : ℕ) = 865 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_173]
  try omega

theorem v3_phi_865 : v3_fast (totient 865) 100 = v3_phi_list.getD 865 0 := by
  rw [tot_865]
  rfl

theorem tot_866 : totient 866 = 432 := by
  have heq : (2 * (433) : ℕ) = 866 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_433 : totient 433 = 433 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_433]
  try omega

theorem v3_phi_866 : v3_fast (totient 866) 100 = v3_phi_list.getD 866 0 := by
  rw [tot_866]
  rfl

theorem tot_867 : totient 867 = 544 := by
  have heq : (3 * (17^2) : ℕ) = 867 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_17]
  try omega

theorem v3_phi_867 : v3_fast (totient 867) 100 = v3_phi_list.getD 867 0 := by
  rw [tot_867]
  rfl

theorem tot_868 : totient 868 = 360 := by
  have heq : (2^2 * (7 * (31)) : ℕ) = 868 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_31]
  try omega

theorem v3_phi_868 : v3_fast (totient 868) 100 = v3_phi_list.getD 868 0 := by
  rw [tot_868]
  rfl

theorem tot_869 : totient 869 = 780 := by
  have heq : (11 * (79) : ℕ) = 869 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_79]
  try omega

theorem v3_phi_869 : v3_fast (totient 869) 100 = v3_phi_list.getD 869 0 := by
  rw [tot_869]
  rfl

theorem tot_870 : totient 870 = 224 := by
  have heq : (2 * (3 * (5 * (29))) : ℕ) = 870 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_29]
  try omega

theorem v3_phi_870 : v3_fast (totient 870) 100 = v3_phi_list.getD 870 0 := by
  rw [tot_870]
  rfl

theorem tot_871 : totient 871 = 792 := by
  have heq : (13 * (67) : ℕ) = 871 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_67]
  try omega

theorem v3_phi_871 : v3_fast (totient 871) 100 = v3_phi_list.getD 871 0 := by
  rw [tot_871]
  rfl

theorem tot_872 : totient 872 = 432 := by
  have heq : (2^3 * (109) : ℕ) = 872 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_109]
  try omega

theorem v3_phi_872 : v3_fast (totient 872) 100 = v3_phi_list.getD 872 0 := by
  rw [tot_872]
  rfl

theorem tot_873 : totient 873 = 576 := by
  have heq : (3^2 * (97) : ℕ) = 873 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_97]
  try omega

theorem v3_phi_873 : v3_fast (totient 873) 100 = v3_phi_list.getD 873 0 := by
  rw [tot_873]
  rfl

theorem tot_874 : totient 874 = 396 := by
  have heq : (2 * (19 * (23)) : ℕ) = 874 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_23]
  try omega

theorem v3_phi_874 : v3_fast (totient 874) 100 = v3_phi_list.getD 874 0 := by
  rw [tot_874]
  rfl

theorem tot_875 : totient 875 = 600 := by
  have heq : (5^3 * (7) : ℕ) = 875 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7]
  try omega

theorem v3_phi_875 : v3_fast (totient 875) 100 = v3_phi_list.getD 875 0 := by
  rw [tot_875]
  rfl

theorem tot_876 : totient 876 = 288 := by
  have heq : (2^2 * (3 * (73)) : ℕ) = 876 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_73]
  try omega

theorem v3_phi_876 : v3_fast (totient 876) 100 = v3_phi_list.getD 876 0 := by
  rw [tot_876]
  rfl

theorem tot_877 : totient 877 = 876 := by
  have h : totient 877 = 877 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_877 : v3_fast (totient 877) 100 = v3_phi_list.getD 877 0 := by
  rw [tot_877]
  rfl

theorem tot_878 : totient 878 = 438 := by
  have heq : (2 * (439) : ℕ) = 878 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_439 : totient 439 = 439 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_439]
  try omega

theorem v3_phi_878 : v3_fast (totient 878) 100 = v3_phi_list.getD 878 0 := by
  rw [tot_878]
  rfl

theorem tot_879 : totient 879 = 584 := by
  have heq : (3 * (293) : ℕ) = 879 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_293 : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_293]
  try omega

theorem v3_phi_879 : v3_fast (totient 879) 100 = v3_phi_list.getD 879 0 := by
  rw [tot_879]
  rfl

theorem tot_880 : totient 880 = 320 := by
  have heq : (2^4 * (5 * (11)) : ℕ) = 880 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11]
  try omega

theorem v3_phi_880 : v3_fast (totient 880) 100 = v3_phi_list.getD 880 0 := by
  rw [tot_880]
  rfl

theorem tot_881 : totient 881 = 880 := by
  have h : totient 881 = 881 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_881 : v3_fast (totient 881) 100 = v3_phi_list.getD 881 0 := by
  rw [tot_881]
  rfl

theorem tot_882 : totient 882 = 252 := by
  have heq : (2 * (3^2 * (7^2)) : ℕ) = 882 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_882 : v3_fast (totient 882) 100 = v3_phi_list.getD 882 0 := by
  rw [tot_882]
  rfl

theorem tot_883 : totient 883 = 882 := by
  have h : totient 883 = 883 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_883 : v3_fast (totient 883) 100 = v3_phi_list.getD 883 0 := by
  rw [tot_883]
  rfl

theorem tot_884 : totient 884 = 384 := by
  have heq : (2^2 * (13 * (17)) : ℕ) = 884 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_17]
  try omega

theorem v3_phi_884 : v3_fast (totient 884) 100 = v3_phi_list.getD 884 0 := by
  rw [tot_884]
  rfl

theorem tot_885 : totient 885 = 464 := by
  have heq : (3 * (5 * (59)) : ℕ) = 885 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_59]
  try omega

theorem v3_phi_885 : v3_fast (totient 885) 100 = v3_phi_list.getD 885 0 := by
  rw [tot_885]
  rfl

theorem tot_886 : totient 886 = 442 := by
  have heq : (2 * (443) : ℕ) = 886 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_443 : totient 443 = 443 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_443]
  try omega

theorem v3_phi_886 : v3_fast (totient 886) 100 = v3_phi_list.getD 886 0 := by
  rw [tot_886]
  rfl

theorem tot_887 : totient 887 = 886 := by
  have h : totient 887 = 887 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_887 : v3_fast (totient 887) 100 = v3_phi_list.getD 887 0 := by
  rw [tot_887]
  rfl

theorem tot_888 : totient 888 = 288 := by
  have heq : (2^3 * (3 * (37)) : ℕ) = 888 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37]
  try omega

theorem v3_phi_888 : v3_fast (totient 888) 100 = v3_phi_list.getD 888 0 := by
  rw [tot_888]
  rfl

theorem tot_889 : totient 889 = 756 := by
  have heq : (7 * (127) : ℕ) = 889 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_127]
  try omega

theorem v3_phi_889 : v3_fast (totient 889) 100 = v3_phi_list.getD 889 0 := by
  rw [tot_889]
  rfl

theorem tot_890 : totient 890 = 352 := by
  have heq : (2 * (5 * (89)) : ℕ) = 890 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_89]
  try omega

theorem v3_phi_890 : v3_fast (totient 890) 100 = v3_phi_list.getD 890 0 := by
  rw [tot_890]
  rfl

theorem tot_891 : totient 891 = 540 := by
  have heq : (3^4 * (11) : ℕ) = 891 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11]
  try omega

theorem v3_phi_891 : v3_fast (totient 891) 100 = v3_phi_list.getD 891 0 := by
  rw [tot_891]
  rfl

theorem tot_892 : totient 892 = 444 := by
  have heq : (2^2 * (223) : ℕ) = 892 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_223]
  try omega

theorem v3_phi_892 : v3_fast (totient 892) 100 = v3_phi_list.getD 892 0 := by
  rw [tot_892]
  rfl

theorem tot_893 : totient 893 = 828 := by
  have heq : (19 * (47) : ℕ) = 893 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_47]
  try omega

theorem v3_phi_893 : v3_fast (totient 893) 100 = v3_phi_list.getD 893 0 := by
  rw [tot_893]
  rfl

theorem tot_894 : totient 894 = 296 := by
  have heq : (2 * (3 * (149)) : ℕ) = 894 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_149]
  try omega

theorem v3_phi_894 : v3_fast (totient 894) 100 = v3_phi_list.getD 894 0 := by
  rw [tot_894]
  rfl

theorem tot_895 : totient 895 = 712 := by
  have heq : (5 * (179) : ℕ) = 895 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_179]
  try omega

theorem v3_phi_895 : v3_fast (totient 895) 100 = v3_phi_list.getD 895 0 := by
  rw [tot_895]
  rfl

theorem tot_896 : totient 896 = 384 := by
  have heq : (2^7 * (7) : ℕ) = 896 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_896 : v3_fast (totient 896) 100 = v3_phi_list.getD 896 0 := by
  rw [tot_896]
  rfl

theorem tot_897 : totient 897 = 528 := by
  have heq : (3 * (13 * (23)) : ℕ) = 897 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_23]
  try omega

theorem v3_phi_897 : v3_fast (totient 897) 100 = v3_phi_list.getD 897 0 := by
  rw [tot_897]
  rfl

theorem tot_898 : totient 898 = 448 := by
  have heq : (2 * (449) : ℕ) = 898 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_449 : totient 449 = 449 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_449]
  try omega

theorem v3_phi_898 : v3_fast (totient 898) 100 = v3_phi_list.getD 898 0 := by
  rw [tot_898]
  rfl

theorem tot_899 : totient 899 = 840 := by
  have heq : (29 * (31) : ℕ) = 899 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_31]
  try omega

theorem v3_phi_899 : v3_fast (totient 899) 100 = v3_phi_list.getD 899 0 := by
  rw [tot_899]
  rfl

theorem tot_900 : totient 900 = 240 := by
  have heq : (2^2 * (3^2 * (5^2)) : ℕ) = 900 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_900 : v3_fast (totient 900) 100 = v3_phi_list.getD 900 0 := by
  rw [tot_900]
  rfl

theorem tot_901 : totient 901 = 832 := by
  have heq : (17 * (53) : ℕ) = 901 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_53]
  try omega

theorem v3_phi_901 : v3_fast (totient 901) 100 = v3_phi_list.getD 901 0 := by
  rw [tot_901]
  rfl

theorem tot_902 : totient 902 = 400 := by
  have heq : (2 * (11 * (41)) : ℕ) = 902 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_41]
  try omega

theorem v3_phi_902 : v3_fast (totient 902) 100 = v3_phi_list.getD 902 0 := by
  rw [tot_902]
  rfl

theorem tot_903 : totient 903 = 504 := by
  have heq : (3 * (7 * (43)) : ℕ) = 903 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_43]
  try omega

theorem v3_phi_903 : v3_fast (totient 903) 100 = v3_phi_list.getD 903 0 := by
  rw [tot_903]
  rfl

theorem tot_904 : totient 904 = 448 := by
  have heq : (2^3 * (113) : ℕ) = 904 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_113]
  try omega

theorem v3_phi_904 : v3_fast (totient 904) 100 = v3_phi_list.getD 904 0 := by
  rw [tot_904]
  rfl

theorem tot_905 : totient 905 = 720 := by
  have heq : (5 * (181) : ℕ) = 905 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_181]
  try omega

theorem v3_phi_905 : v3_fast (totient 905) 100 = v3_phi_list.getD 905 0 := by
  rw [tot_905]
  rfl

theorem tot_906 : totient 906 = 300 := by
  have heq : (2 * (3 * (151)) : ℕ) = 906 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_151]
  try omega

theorem v3_phi_906 : v3_fast (totient 906) 100 = v3_phi_list.getD 906 0 := by
  rw [tot_906]
  rfl

theorem tot_907 : totient 907 = 906 := by
  have h : totient 907 = 907 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_907 : v3_fast (totient 907) 100 = v3_phi_list.getD 907 0 := by
  rw [tot_907]
  rfl

theorem tot_908 : totient 908 = 452 := by
  have heq : (2^2 * (227) : ℕ) = 908 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_227]
  try omega

theorem v3_phi_908 : v3_fast (totient 908) 100 = v3_phi_list.getD 908 0 := by
  rw [tot_908]
  rfl

theorem tot_909 : totient 909 = 600 := by
  have heq : (3^2 * (101) : ℕ) = 909 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_101]
  try omega

theorem v3_phi_909 : v3_fast (totient 909) 100 = v3_phi_list.getD 909 0 := by
  rw [tot_909]
  rfl

theorem tot_910 : totient 910 = 288 := by
  have heq : (2 * (5 * (7 * (13))) : ℕ) = 910 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_13]
  try omega

theorem v3_phi_910 : v3_fast (totient 910) 100 = v3_phi_list.getD 910 0 := by
  rw [tot_910]
  rfl

theorem tot_911 : totient 911 = 910 := by
  have h : totient 911 = 911 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_911 : v3_fast (totient 911) 100 = v3_phi_list.getD 911 0 := by
  rw [tot_911]
  rfl

theorem tot_912 : totient 912 = 288 := by
  have heq : (2^4 * (3 * (19)) : ℕ) = 912 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19]
  try omega

theorem v3_phi_912 : v3_fast (totient 912) 100 = v3_phi_list.getD 912 0 := by
  rw [tot_912]
  rfl

theorem tot_913 : totient 913 = 820 := by
  have heq : (11 * (83) : ℕ) = 913 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_83]
  try omega

theorem v3_phi_913 : v3_fast (totient 913) 100 = v3_phi_list.getD 913 0 := by
  rw [tot_913]
  rfl

theorem tot_914 : totient 914 = 456 := by
  have heq : (2 * (457) : ℕ) = 914 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_457 : totient 457 = 457 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_457]
  try omega

theorem v3_phi_914 : v3_fast (totient 914) 100 = v3_phi_list.getD 914 0 := by
  rw [tot_914]
  rfl

theorem tot_915 : totient 915 = 480 := by
  have heq : (3 * (5 * (61)) : ℕ) = 915 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_61]
  try omega

theorem v3_phi_915 : v3_fast (totient 915) 100 = v3_phi_list.getD 915 0 := by
  rw [tot_915]
  rfl

theorem tot_916 : totient 916 = 456 := by
  have heq : (2^2 * (229) : ℕ) = 916 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_229]
  try omega

theorem v3_phi_916 : v3_fast (totient 916) 100 = v3_phi_list.getD 916 0 := by
  rw [tot_916]
  rfl

theorem tot_917 : totient 917 = 780 := by
  have heq : (7 * (131) : ℕ) = 917 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_131]
  try omega

theorem v3_phi_917 : v3_fast (totient 917) 100 = v3_phi_list.getD 917 0 := by
  rw [tot_917]
  rfl

theorem tot_918 : totient 918 = 288 := by
  have heq : (2 * (3^3 * (17)) : ℕ) = 918 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17]
  try omega

theorem v3_phi_918 : v3_fast (totient 918) 100 = v3_phi_list.getD 918 0 := by
  rw [tot_918]
  rfl

theorem tot_919 : totient 919 = 918 := by
  have h : totient 919 = 919 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_919 : v3_fast (totient 919) 100 = v3_phi_list.getD 919 0 := by
  rw [tot_919]
  rfl

theorem v3_phi_eq_list_1 (k : ℕ) (hk1 : 460 ≤ k) (hk2 : k ≤ 919) : v3_fast k.totient 100 = v3_phi_list.getD k 0 := by
  have heq : k = 460 + (k - 460) := by omega
  revert hk1 hk2
  rw [heq]
  match k - 460 with
  | 0 => intro _ _; exact v3_phi_460
  | 1 => intro _ _; exact v3_phi_461
  | 2 => intro _ _; exact v3_phi_462
  | 3 => intro _ _; exact v3_phi_463
  | 4 => intro _ _; exact v3_phi_464
  | 5 => intro _ _; exact v3_phi_465
  | 6 => intro _ _; exact v3_phi_466
  | 7 => intro _ _; exact v3_phi_467
  | 8 => intro _ _; exact v3_phi_468
  | 9 => intro _ _; exact v3_phi_469
  | 10 => intro _ _; exact v3_phi_470
  | 11 => intro _ _; exact v3_phi_471
  | 12 => intro _ _; exact v3_phi_472
  | 13 => intro _ _; exact v3_phi_473
  | 14 => intro _ _; exact v3_phi_474
  | 15 => intro _ _; exact v3_phi_475
  | 16 => intro _ _; exact v3_phi_476
  | 17 => intro _ _; exact v3_phi_477
  | 18 => intro _ _; exact v3_phi_478
  | 19 => intro _ _; exact v3_phi_479
  | 20 => intro _ _; exact v3_phi_480
  | 21 => intro _ _; exact v3_phi_481
  | 22 => intro _ _; exact v3_phi_482
  | 23 => intro _ _; exact v3_phi_483
  | 24 => intro _ _; exact v3_phi_484
  | 25 => intro _ _; exact v3_phi_485
  | 26 => intro _ _; exact v3_phi_486
  | 27 => intro _ _; exact v3_phi_487
  | 28 => intro _ _; exact v3_phi_488
  | 29 => intro _ _; exact v3_phi_489
  | 30 => intro _ _; exact v3_phi_490
  | 31 => intro _ _; exact v3_phi_491
  | 32 => intro _ _; exact v3_phi_492
  | 33 => intro _ _; exact v3_phi_493
  | 34 => intro _ _; exact v3_phi_494
  | 35 => intro _ _; exact v3_phi_495
  | 36 => intro _ _; exact v3_phi_496
  | 37 => intro _ _; exact v3_phi_497
  | 38 => intro _ _; exact v3_phi_498
  | 39 => intro _ _; exact v3_phi_499
  | 40 => intro _ _; exact v3_phi_500
  | 41 => intro _ _; exact v3_phi_501
  | 42 => intro _ _; exact v3_phi_502
  | 43 => intro _ _; exact v3_phi_503
  | 44 => intro _ _; exact v3_phi_504
  | 45 => intro _ _; exact v3_phi_505
  | 46 => intro _ _; exact v3_phi_506
  | 47 => intro _ _; exact v3_phi_507
  | 48 => intro _ _; exact v3_phi_508
  | 49 => intro _ _; exact v3_phi_509
  | 50 => intro _ _; exact v3_phi_510
  | 51 => intro _ _; exact v3_phi_511
  | 52 => intro _ _; exact v3_phi_512
  | 53 => intro _ _; exact v3_phi_513
  | 54 => intro _ _; exact v3_phi_514
  | 55 => intro _ _; exact v3_phi_515
  | 56 => intro _ _; exact v3_phi_516
  | 57 => intro _ _; exact v3_phi_517
  | 58 => intro _ _; exact v3_phi_518
  | 59 => intro _ _; exact v3_phi_519
  | 60 => intro _ _; exact v3_phi_520
  | 61 => intro _ _; exact v3_phi_521
  | 62 => intro _ _; exact v3_phi_522
  | 63 => intro _ _; exact v3_phi_523
  | 64 => intro _ _; exact v3_phi_524
  | 65 => intro _ _; exact v3_phi_525
  | 66 => intro _ _; exact v3_phi_526
  | 67 => intro _ _; exact v3_phi_527
  | 68 => intro _ _; exact v3_phi_528
  | 69 => intro _ _; exact v3_phi_529
  | 70 => intro _ _; exact v3_phi_530
  | 71 => intro _ _; exact v3_phi_531
  | 72 => intro _ _; exact v3_phi_532
  | 73 => intro _ _; exact v3_phi_533
  | 74 => intro _ _; exact v3_phi_534
  | 75 => intro _ _; exact v3_phi_535
  | 76 => intro _ _; exact v3_phi_536
  | 77 => intro _ _; exact v3_phi_537
  | 78 => intro _ _; exact v3_phi_538
  | 79 => intro _ _; exact v3_phi_539
  | 80 => intro _ _; exact v3_phi_540
  | 81 => intro _ _; exact v3_phi_541
  | 82 => intro _ _; exact v3_phi_542
  | 83 => intro _ _; exact v3_phi_543
  | 84 => intro _ _; exact v3_phi_544
  | 85 => intro _ _; exact v3_phi_545
  | 86 => intro _ _; exact v3_phi_546
  | 87 => intro _ _; exact v3_phi_547
  | 88 => intro _ _; exact v3_phi_548
  | 89 => intro _ _; exact v3_phi_549
  | 90 => intro _ _; exact v3_phi_550
  | 91 => intro _ _; exact v3_phi_551
  | 92 => intro _ _; exact v3_phi_552
  | 93 => intro _ _; exact v3_phi_553
  | 94 => intro _ _; exact v3_phi_554
  | 95 => intro _ _; exact v3_phi_555
  | 96 => intro _ _; exact v3_phi_556
  | 97 => intro _ _; exact v3_phi_557
  | 98 => intro _ _; exact v3_phi_558
  | 99 => intro _ _; exact v3_phi_559
  | 100 => intro _ _; exact v3_phi_560
  | 101 => intro _ _; exact v3_phi_561
  | 102 => intro _ _; exact v3_phi_562
  | 103 => intro _ _; exact v3_phi_563
  | 104 => intro _ _; exact v3_phi_564
  | 105 => intro _ _; exact v3_phi_565
  | 106 => intro _ _; exact v3_phi_566
  | 107 => intro _ _; exact v3_phi_567
  | 108 => intro _ _; exact v3_phi_568
  | 109 => intro _ _; exact v3_phi_569
  | 110 => intro _ _; exact v3_phi_570
  | 111 => intro _ _; exact v3_phi_571
  | 112 => intro _ _; exact v3_phi_572
  | 113 => intro _ _; exact v3_phi_573
  | 114 => intro _ _; exact v3_phi_574
  | 115 => intro _ _; exact v3_phi_575
  | 116 => intro _ _; exact v3_phi_576
  | 117 => intro _ _; exact v3_phi_577
  | 118 => intro _ _; exact v3_phi_578
  | 119 => intro _ _; exact v3_phi_579
  | 120 => intro _ _; exact v3_phi_580
  | 121 => intro _ _; exact v3_phi_581
  | 122 => intro _ _; exact v3_phi_582
  | 123 => intro _ _; exact v3_phi_583
  | 124 => intro _ _; exact v3_phi_584
  | 125 => intro _ _; exact v3_phi_585
  | 126 => intro _ _; exact v3_phi_586
  | 127 => intro _ _; exact v3_phi_587
  | 128 => intro _ _; exact v3_phi_588
  | 129 => intro _ _; exact v3_phi_589
  | 130 => intro _ _; exact v3_phi_590
  | 131 => intro _ _; exact v3_phi_591
  | 132 => intro _ _; exact v3_phi_592
  | 133 => intro _ _; exact v3_phi_593
  | 134 => intro _ _; exact v3_phi_594
  | 135 => intro _ _; exact v3_phi_595
  | 136 => intro _ _; exact v3_phi_596
  | 137 => intro _ _; exact v3_phi_597
  | 138 => intro _ _; exact v3_phi_598
  | 139 => intro _ _; exact v3_phi_599
  | 140 => intro _ _; exact v3_phi_600
  | 141 => intro _ _; exact v3_phi_601
  | 142 => intro _ _; exact v3_phi_602
  | 143 => intro _ _; exact v3_phi_603
  | 144 => intro _ _; exact v3_phi_604
  | 145 => intro _ _; exact v3_phi_605
  | 146 => intro _ _; exact v3_phi_606
  | 147 => intro _ _; exact v3_phi_607
  | 148 => intro _ _; exact v3_phi_608
  | 149 => intro _ _; exact v3_phi_609
  | 150 => intro _ _; exact v3_phi_610
  | 151 => intro _ _; exact v3_phi_611
  | 152 => intro _ _; exact v3_phi_612
  | 153 => intro _ _; exact v3_phi_613
  | 154 => intro _ _; exact v3_phi_614
  | 155 => intro _ _; exact v3_phi_615
  | 156 => intro _ _; exact v3_phi_616
  | 157 => intro _ _; exact v3_phi_617
  | 158 => intro _ _; exact v3_phi_618
  | 159 => intro _ _; exact v3_phi_619
  | 160 => intro _ _; exact v3_phi_620
  | 161 => intro _ _; exact v3_phi_621
  | 162 => intro _ _; exact v3_phi_622
  | 163 => intro _ _; exact v3_phi_623
  | 164 => intro _ _; exact v3_phi_624
  | 165 => intro _ _; exact v3_phi_625
  | 166 => intro _ _; exact v3_phi_626
  | 167 => intro _ _; exact v3_phi_627
  | 168 => intro _ _; exact v3_phi_628
  | 169 => intro _ _; exact v3_phi_629
  | 170 => intro _ _; exact v3_phi_630
  | 171 => intro _ _; exact v3_phi_631
  | 172 => intro _ _; exact v3_phi_632
  | 173 => intro _ _; exact v3_phi_633
  | 174 => intro _ _; exact v3_phi_634
  | 175 => intro _ _; exact v3_phi_635
  | 176 => intro _ _; exact v3_phi_636
  | 177 => intro _ _; exact v3_phi_637
  | 178 => intro _ _; exact v3_phi_638
  | 179 => intro _ _; exact v3_phi_639
  | 180 => intro _ _; exact v3_phi_640
  | 181 => intro _ _; exact v3_phi_641
  | 182 => intro _ _; exact v3_phi_642
  | 183 => intro _ _; exact v3_phi_643
  | 184 => intro _ _; exact v3_phi_644
  | 185 => intro _ _; exact v3_phi_645
  | 186 => intro _ _; exact v3_phi_646
  | 187 => intro _ _; exact v3_phi_647
  | 188 => intro _ _; exact v3_phi_648
  | 189 => intro _ _; exact v3_phi_649
  | 190 => intro _ _; exact v3_phi_650
  | 191 => intro _ _; exact v3_phi_651
  | 192 => intro _ _; exact v3_phi_652
  | 193 => intro _ _; exact v3_phi_653
  | 194 => intro _ _; exact v3_phi_654
  | 195 => intro _ _; exact v3_phi_655
  | 196 => intro _ _; exact v3_phi_656
  | 197 => intro _ _; exact v3_phi_657
  | 198 => intro _ _; exact v3_phi_658
  | 199 => intro _ _; exact v3_phi_659
  | 200 => intro _ _; exact v3_phi_660
  | 201 => intro _ _; exact v3_phi_661
  | 202 => intro _ _; exact v3_phi_662
  | 203 => intro _ _; exact v3_phi_663
  | 204 => intro _ _; exact v3_phi_664
  | 205 => intro _ _; exact v3_phi_665
  | 206 => intro _ _; exact v3_phi_666
  | 207 => intro _ _; exact v3_phi_667
  | 208 => intro _ _; exact v3_phi_668
  | 209 => intro _ _; exact v3_phi_669
  | 210 => intro _ _; exact v3_phi_670
  | 211 => intro _ _; exact v3_phi_671
  | 212 => intro _ _; exact v3_phi_672
  | 213 => intro _ _; exact v3_phi_673
  | 214 => intro _ _; exact v3_phi_674
  | 215 => intro _ _; exact v3_phi_675
  | 216 => intro _ _; exact v3_phi_676
  | 217 => intro _ _; exact v3_phi_677
  | 218 => intro _ _; exact v3_phi_678
  | 219 => intro _ _; exact v3_phi_679
  | 220 => intro _ _; exact v3_phi_680
  | 221 => intro _ _; exact v3_phi_681
  | 222 => intro _ _; exact v3_phi_682
  | 223 => intro _ _; exact v3_phi_683
  | 224 => intro _ _; exact v3_phi_684
  | 225 => intro _ _; exact v3_phi_685
  | 226 => intro _ _; exact v3_phi_686
  | 227 => intro _ _; exact v3_phi_687
  | 228 => intro _ _; exact v3_phi_688
  | 229 => intro _ _; exact v3_phi_689
  | 230 => intro _ _; exact v3_phi_690
  | 231 => intro _ _; exact v3_phi_691
  | 232 => intro _ _; exact v3_phi_692
  | 233 => intro _ _; exact v3_phi_693
  | 234 => intro _ _; exact v3_phi_694
  | 235 => intro _ _; exact v3_phi_695
  | 236 => intro _ _; exact v3_phi_696
  | 237 => intro _ _; exact v3_phi_697
  | 238 => intro _ _; exact v3_phi_698
  | 239 => intro _ _; exact v3_phi_699
  | 240 => intro _ _; exact v3_phi_700
  | 241 => intro _ _; exact v3_phi_701
  | 242 => intro _ _; exact v3_phi_702
  | 243 => intro _ _; exact v3_phi_703
  | 244 => intro _ _; exact v3_phi_704
  | 245 => intro _ _; exact v3_phi_705
  | 246 => intro _ _; exact v3_phi_706
  | 247 => intro _ _; exact v3_phi_707
  | 248 => intro _ _; exact v3_phi_708
  | 249 => intro _ _; exact v3_phi_709
  | 250 => intro _ _; exact v3_phi_710
  | 251 => intro _ _; exact v3_phi_711
  | 252 => intro _ _; exact v3_phi_712
  | 253 => intro _ _; exact v3_phi_713
  | 254 => intro _ _; exact v3_phi_714
  | 255 => intro _ _; exact v3_phi_715
  | 256 => intro _ _; exact v3_phi_716
  | 257 => intro _ _; exact v3_phi_717
  | 258 => intro _ _; exact v3_phi_718
  | 259 => intro _ _; exact v3_phi_719
  | 260 => intro _ _; exact v3_phi_720
  | 261 => intro _ _; exact v3_phi_721
  | 262 => intro _ _; exact v3_phi_722
  | 263 => intro _ _; exact v3_phi_723
  | 264 => intro _ _; exact v3_phi_724
  | 265 => intro _ _; exact v3_phi_725
  | 266 => intro _ _; exact v3_phi_726
  | 267 => intro _ _; exact v3_phi_727
  | 268 => intro _ _; exact v3_phi_728
  | 269 => intro _ _; exact v3_phi_729
  | 270 => intro _ _; exact v3_phi_730
  | 271 => intro _ _; exact v3_phi_731
  | 272 => intro _ _; exact v3_phi_732
  | 273 => intro _ _; exact v3_phi_733
  | 274 => intro _ _; exact v3_phi_734
  | 275 => intro _ _; exact v3_phi_735
  | 276 => intro _ _; exact v3_phi_736
  | 277 => intro _ _; exact v3_phi_737
  | 278 => intro _ _; exact v3_phi_738
  | 279 => intro _ _; exact v3_phi_739
  | 280 => intro _ _; exact v3_phi_740
  | 281 => intro _ _; exact v3_phi_741
  | 282 => intro _ _; exact v3_phi_742
  | 283 => intro _ _; exact v3_phi_743
  | 284 => intro _ _; exact v3_phi_744
  | 285 => intro _ _; exact v3_phi_745
  | 286 => intro _ _; exact v3_phi_746
  | 287 => intro _ _; exact v3_phi_747
  | 288 => intro _ _; exact v3_phi_748
  | 289 => intro _ _; exact v3_phi_749
  | 290 => intro _ _; exact v3_phi_750
  | 291 => intro _ _; exact v3_phi_751
  | 292 => intro _ _; exact v3_phi_752
  | 293 => intro _ _; exact v3_phi_753
  | 294 => intro _ _; exact v3_phi_754
  | 295 => intro _ _; exact v3_phi_755
  | 296 => intro _ _; exact v3_phi_756
  | 297 => intro _ _; exact v3_phi_757
  | 298 => intro _ _; exact v3_phi_758
  | 299 => intro _ _; exact v3_phi_759
  | 300 => intro _ _; exact v3_phi_760
  | 301 => intro _ _; exact v3_phi_761
  | 302 => intro _ _; exact v3_phi_762
  | 303 => intro _ _; exact v3_phi_763
  | 304 => intro _ _; exact v3_phi_764
  | 305 => intro _ _; exact v3_phi_765
  | 306 => intro _ _; exact v3_phi_766
  | 307 => intro _ _; exact v3_phi_767
  | 308 => intro _ _; exact v3_phi_768
  | 309 => intro _ _; exact v3_phi_769
  | 310 => intro _ _; exact v3_phi_770
  | 311 => intro _ _; exact v3_phi_771
  | 312 => intro _ _; exact v3_phi_772
  | 313 => intro _ _; exact v3_phi_773
  | 314 => intro _ _; exact v3_phi_774
  | 315 => intro _ _; exact v3_phi_775
  | 316 => intro _ _; exact v3_phi_776
  | 317 => intro _ _; exact v3_phi_777
  | 318 => intro _ _; exact v3_phi_778
  | 319 => intro _ _; exact v3_phi_779
  | 320 => intro _ _; exact v3_phi_780
  | 321 => intro _ _; exact v3_phi_781
  | 322 => intro _ _; exact v3_phi_782
  | 323 => intro _ _; exact v3_phi_783
  | 324 => intro _ _; exact v3_phi_784
  | 325 => intro _ _; exact v3_phi_785
  | 326 => intro _ _; exact v3_phi_786
  | 327 => intro _ _; exact v3_phi_787
  | 328 => intro _ _; exact v3_phi_788
  | 329 => intro _ _; exact v3_phi_789
  | 330 => intro _ _; exact v3_phi_790
  | 331 => intro _ _; exact v3_phi_791
  | 332 => intro _ _; exact v3_phi_792
  | 333 => intro _ _; exact v3_phi_793
  | 334 => intro _ _; exact v3_phi_794
  | 335 => intro _ _; exact v3_phi_795
  | 336 => intro _ _; exact v3_phi_796
  | 337 => intro _ _; exact v3_phi_797
  | 338 => intro _ _; exact v3_phi_798
  | 339 => intro _ _; exact v3_phi_799
  | 340 => intro _ _; exact v3_phi_800
  | 341 => intro _ _; exact v3_phi_801
  | 342 => intro _ _; exact v3_phi_802
  | 343 => intro _ _; exact v3_phi_803
  | 344 => intro _ _; exact v3_phi_804
  | 345 => intro _ _; exact v3_phi_805
  | 346 => intro _ _; exact v3_phi_806
  | 347 => intro _ _; exact v3_phi_807
  | 348 => intro _ _; exact v3_phi_808
  | 349 => intro _ _; exact v3_phi_809
  | 350 => intro _ _; exact v3_phi_810
  | 351 => intro _ _; exact v3_phi_811
  | 352 => intro _ _; exact v3_phi_812
  | 353 => intro _ _; exact v3_phi_813
  | 354 => intro _ _; exact v3_phi_814
  | 355 => intro _ _; exact v3_phi_815
  | 356 => intro _ _; exact v3_phi_816
  | 357 => intro _ _; exact v3_phi_817
  | 358 => intro _ _; exact v3_phi_818
  | 359 => intro _ _; exact v3_phi_819
  | 360 => intro _ _; exact v3_phi_820
  | 361 => intro _ _; exact v3_phi_821
  | 362 => intro _ _; exact v3_phi_822
  | 363 => intro _ _; exact v3_phi_823
  | 364 => intro _ _; exact v3_phi_824
  | 365 => intro _ _; exact v3_phi_825
  | 366 => intro _ _; exact v3_phi_826
  | 367 => intro _ _; exact v3_phi_827
  | 368 => intro _ _; exact v3_phi_828
  | 369 => intro _ _; exact v3_phi_829
  | 370 => intro _ _; exact v3_phi_830
  | 371 => intro _ _; exact v3_phi_831
  | 372 => intro _ _; exact v3_phi_832
  | 373 => intro _ _; exact v3_phi_833
  | 374 => intro _ _; exact v3_phi_834
  | 375 => intro _ _; exact v3_phi_835
  | 376 => intro _ _; exact v3_phi_836
  | 377 => intro _ _; exact v3_phi_837
  | 378 => intro _ _; exact v3_phi_838
  | 379 => intro _ _; exact v3_phi_839
  | 380 => intro _ _; exact v3_phi_840
  | 381 => intro _ _; exact v3_phi_841
  | 382 => intro _ _; exact v3_phi_842
  | 383 => intro _ _; exact v3_phi_843
  | 384 => intro _ _; exact v3_phi_844
  | 385 => intro _ _; exact v3_phi_845
  | 386 => intro _ _; exact v3_phi_846
  | 387 => intro _ _; exact v3_phi_847
  | 388 => intro _ _; exact v3_phi_848
  | 389 => intro _ _; exact v3_phi_849
  | 390 => intro _ _; exact v3_phi_850
  | 391 => intro _ _; exact v3_phi_851
  | 392 => intro _ _; exact v3_phi_852
  | 393 => intro _ _; exact v3_phi_853
  | 394 => intro _ _; exact v3_phi_854
  | 395 => intro _ _; exact v3_phi_855
  | 396 => intro _ _; exact v3_phi_856
  | 397 => intro _ _; exact v3_phi_857
  | 398 => intro _ _; exact v3_phi_858
  | 399 => intro _ _; exact v3_phi_859
  | 400 => intro _ _; exact v3_phi_860
  | 401 => intro _ _; exact v3_phi_861
  | 402 => intro _ _; exact v3_phi_862
  | 403 => intro _ _; exact v3_phi_863
  | 404 => intro _ _; exact v3_phi_864
  | 405 => intro _ _; exact v3_phi_865
  | 406 => intro _ _; exact v3_phi_866
  | 407 => intro _ _; exact v3_phi_867
  | 408 => intro _ _; exact v3_phi_868
  | 409 => intro _ _; exact v3_phi_869
  | 410 => intro _ _; exact v3_phi_870
  | 411 => intro _ _; exact v3_phi_871
  | 412 => intro _ _; exact v3_phi_872
  | 413 => intro _ _; exact v3_phi_873
  | 414 => intro _ _; exact v3_phi_874
  | 415 => intro _ _; exact v3_phi_875
  | 416 => intro _ _; exact v3_phi_876
  | 417 => intro _ _; exact v3_phi_877
  | 418 => intro _ _; exact v3_phi_878
  | 419 => intro _ _; exact v3_phi_879
  | 420 => intro _ _; exact v3_phi_880
  | 421 => intro _ _; exact v3_phi_881
  | 422 => intro _ _; exact v3_phi_882
  | 423 => intro _ _; exact v3_phi_883
  | 424 => intro _ _; exact v3_phi_884
  | 425 => intro _ _; exact v3_phi_885
  | 426 => intro _ _; exact v3_phi_886
  | 427 => intro _ _; exact v3_phi_887
  | 428 => intro _ _; exact v3_phi_888
  | 429 => intro _ _; exact v3_phi_889
  | 430 => intro _ _; exact v3_phi_890
  | 431 => intro _ _; exact v3_phi_891
  | 432 => intro _ _; exact v3_phi_892
  | 433 => intro _ _; exact v3_phi_893
  | 434 => intro _ _; exact v3_phi_894
  | 435 => intro _ _; exact v3_phi_895
  | 436 => intro _ _; exact v3_phi_896
  | 437 => intro _ _; exact v3_phi_897
  | 438 => intro _ _; exact v3_phi_898
  | 439 => intro _ _; exact v3_phi_899
  | 440 => intro _ _; exact v3_phi_900
  | 441 => intro _ _; exact v3_phi_901
  | 442 => intro _ _; exact v3_phi_902
  | 443 => intro _ _; exact v3_phi_903
  | 444 => intro _ _; exact v3_phi_904
  | 445 => intro _ _; exact v3_phi_905
  | 446 => intro _ _; exact v3_phi_906
  | 447 => intro _ _; exact v3_phi_907
  | 448 => intro _ _; exact v3_phi_908
  | 449 => intro _ _; exact v3_phi_909
  | 450 => intro _ _; exact v3_phi_910
  | 451 => intro _ _; exact v3_phi_911
  | 452 => intro _ _; exact v3_phi_912
  | 453 => intro _ _; exact v3_phi_913
  | 454 => intro _ _; exact v3_phi_914
  | 455 => intro _ _; exact v3_phi_915
  | 456 => intro _ _; exact v3_phi_916
  | 457 => intro _ _; exact v3_phi_917
  | 458 => intro _ _; exact v3_phi_918
  | 459 => intro _ _; exact v3_phi_919
  | x + 460 => intro h1 h2; omega

