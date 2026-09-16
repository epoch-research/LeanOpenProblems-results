import Submission.Totient.Base
open Nat Finset Rat

set_option maxHeartbeats 200000000
set_option maxRecDepth 20000000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem tot_1380 : totient 1380 = 352 := by
  have heq : (2^2 * (3 * (5 * (23))) : ℕ) = 1380 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_23]
  try omega

theorem v3_phi_1380 : v3_fast (totient 1380) 100 = v3_phi_list.getD 1380 0 := by
  rw [tot_1380]
  rfl

theorem tot_1381 : totient 1381 = 1380 := by
  have h : totient 1381 = 1381 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1381 : v3_fast (totient 1381) 100 = v3_phi_list.getD 1381 0 := by
  rw [tot_1381]
  rfl

theorem tot_1382 : totient 1382 = 690 := by
  have heq : (2 * (691) : ℕ) = 1382 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_691 : totient 691 = 691 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_691]
  try omega

theorem v3_phi_1382 : v3_fast (totient 1382) 100 = v3_phi_list.getD 1382 0 := by
  rw [tot_1382]
  rfl

theorem tot_1383 : totient 1383 = 920 := by
  have heq : (3 * (461) : ℕ) = 1383 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_461 : totient 461 = 461 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_461]
  try omega

theorem v3_phi_1383 : v3_fast (totient 1383) 100 = v3_phi_list.getD 1383 0 := by
  rw [tot_1383]
  rfl

theorem tot_1384 : totient 1384 = 688 := by
  have heq : (2^3 * (173) : ℕ) = 1384 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_173]
  try omega

theorem v3_phi_1384 : v3_fast (totient 1384) 100 = v3_phi_list.getD 1384 0 := by
  rw [tot_1384]
  rfl

theorem tot_1385 : totient 1385 = 1104 := by
  have heq : (5 * (277) : ℕ) = 1385 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_277 : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_277]
  try omega

theorem v3_phi_1385 : v3_fast (totient 1385) 100 = v3_phi_list.getD 1385 0 := by
  rw [tot_1385]
  rfl

theorem tot_1386 : totient 1386 = 360 := by
  have heq : (2 * (3^2 * (7 * (11))) : ℕ) = 1386 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_11]
  try omega

theorem v3_phi_1386 : v3_fast (totient 1386) 100 = v3_phi_list.getD 1386 0 := by
  rw [tot_1386]
  rfl

theorem tot_1387 : totient 1387 = 1296 := by
  have heq : (19 * (73) : ℕ) = 1387 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_73]
  try omega

theorem v3_phi_1387 : v3_fast (totient 1387) 100 = v3_phi_list.getD 1387 0 := by
  rw [tot_1387]
  rfl

theorem tot_1388 : totient 1388 = 692 := by
  have heq : (2^2 * (347) : ℕ) = 1388 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_347 : totient 347 = 347 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_347]
  try omega

theorem v3_phi_1388 : v3_fast (totient 1388) 100 = v3_phi_list.getD 1388 0 := by
  rw [tot_1388]
  rfl

theorem tot_1389 : totient 1389 = 924 := by
  have heq : (3 * (463) : ℕ) = 1389 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_463 : totient 463 = 463 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_463]
  try omega

theorem v3_phi_1389 : v3_fast (totient 1389) 100 = v3_phi_list.getD 1389 0 := by
  rw [tot_1389]
  rfl

theorem tot_1390 : totient 1390 = 552 := by
  have heq : (2 * (5 * (139)) : ℕ) = 1390 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_139]
  try omega

theorem v3_phi_1390 : v3_fast (totient 1390) 100 = v3_phi_list.getD 1390 0 := by
  rw [tot_1390]
  rfl

theorem tot_1391 : totient 1391 = 1272 := by
  have heq : (13 * (107) : ℕ) = 1391 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_107]
  try omega

theorem v3_phi_1391 : v3_fast (totient 1391) 100 = v3_phi_list.getD 1391 0 := by
  rw [tot_1391]
  rfl

theorem tot_1392 : totient 1392 = 448 := by
  have heq : (2^4 * (3 * (29)) : ℕ) = 1392 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29]
  try omega

theorem v3_phi_1392 : v3_fast (totient 1392) 100 = v3_phi_list.getD 1392 0 := by
  rw [tot_1392]
  rfl

theorem tot_1393 : totient 1393 = 1188 := by
  have heq : (7 * (199) : ℕ) = 1393 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_199]
  try omega

theorem v3_phi_1393 : v3_fast (totient 1393) 100 = v3_phi_list.getD 1393 0 := by
  rw [tot_1393]
  rfl

theorem tot_1394 : totient 1394 = 640 := by
  have heq : (2 * (17 * (41)) : ℕ) = 1394 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_41]
  try omega

theorem v3_phi_1394 : v3_fast (totient 1394) 100 = v3_phi_list.getD 1394 0 := by
  rw [tot_1394]
  rfl

theorem tot_1395 : totient 1395 = 720 := by
  have heq : (3^2 * (5 * (31)) : ℕ) = 1395 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_31]
  try omega

theorem v3_phi_1395 : v3_fast (totient 1395) 100 = v3_phi_list.getD 1395 0 := by
  rw [tot_1395]
  rfl

theorem tot_1396 : totient 1396 = 696 := by
  have heq : (2^2 * (349) : ℕ) = 1396 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_349 : totient 349 = 349 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_349]
  try omega

theorem v3_phi_1396 : v3_fast (totient 1396) 100 = v3_phi_list.getD 1396 0 := by
  rw [tot_1396]
  rfl

theorem tot_1397 : totient 1397 = 1260 := by
  have heq : (11 * (127) : ℕ) = 1397 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_127]
  try omega

theorem v3_phi_1397 : v3_fast (totient 1397) 100 = v3_phi_list.getD 1397 0 := by
  rw [tot_1397]
  rfl

theorem tot_1398 : totient 1398 = 464 := by
  have heq : (2 * (3 * (233)) : ℕ) = 1398 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_233]
  try omega

theorem v3_phi_1398 : v3_fast (totient 1398) 100 = v3_phi_list.getD 1398 0 := by
  rw [tot_1398]
  rfl

theorem tot_1399 : totient 1399 = 1398 := by
  have h : totient 1399 = 1399 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1399 : v3_fast (totient 1399) 100 = v3_phi_list.getD 1399 0 := by
  rw [tot_1399]
  rfl

theorem tot_1400 : totient 1400 = 480 := by
  have heq : (2^3 * (5^2 * (7)) : ℕ) = 1400 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7]
  try omega

theorem v3_phi_1400 : v3_fast (totient 1400) 100 = v3_phi_list.getD 1400 0 := by
  rw [tot_1400]
  rfl

theorem tot_1401 : totient 1401 = 932 := by
  have heq : (3 * (467) : ℕ) = 1401 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_467 : totient 467 = 467 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_467]
  try omega

theorem v3_phi_1401 : v3_fast (totient 1401) 100 = v3_phi_list.getD 1401 0 := by
  rw [tot_1401]
  rfl

theorem tot_1402 : totient 1402 = 700 := by
  have heq : (2 * (701) : ℕ) = 1402 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_701 : totient 701 = 701 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_701]
  try omega

theorem v3_phi_1402 : v3_fast (totient 1402) 100 = v3_phi_list.getD 1402 0 := by
  rw [tot_1402]
  rfl

theorem tot_1403 : totient 1403 = 1320 := by
  have heq : (23 * (61) : ℕ) = 1403 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_61]
  try omega

theorem v3_phi_1403 : v3_fast (totient 1403) 100 = v3_phi_list.getD 1403 0 := by
  rw [tot_1403]
  rfl

theorem tot_1404 : totient 1404 = 432 := by
  have heq : (2^2 * (3^3 * (13)) : ℕ) = 1404 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13]
  try omega

theorem v3_phi_1404 : v3_fast (totient 1404) 100 = v3_phi_list.getD 1404 0 := by
  rw [tot_1404]
  rfl

theorem tot_1405 : totient 1405 = 1120 := by
  have heq : (5 * (281) : ℕ) = 1405 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_281 : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_281]
  try omega

theorem v3_phi_1405 : v3_fast (totient 1405) 100 = v3_phi_list.getD 1405 0 := by
  rw [tot_1405]
  rfl

theorem tot_1406 : totient 1406 = 648 := by
  have heq : (2 * (19 * (37)) : ℕ) = 1406 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_37]
  try omega

theorem v3_phi_1406 : v3_fast (totient 1406) 100 = v3_phi_list.getD 1406 0 := by
  rw [tot_1406]
  rfl

theorem tot_1407 : totient 1407 = 792 := by
  have heq : (3 * (7 * (67)) : ℕ) = 1407 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_67]
  try omega

theorem v3_phi_1407 : v3_fast (totient 1407) 100 = v3_phi_list.getD 1407 0 := by
  rw [tot_1407]
  rfl

theorem tot_1408 : totient 1408 = 640 := by
  have heq : (2^7 * (11) : ℕ) = 1408 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11]
  try omega

theorem v3_phi_1408 : v3_fast (totient 1408) 100 = v3_phi_list.getD 1408 0 := by
  rw [tot_1408]
  rfl

theorem tot_1409 : totient 1409 = 1408 := by
  have h : totient 1409 = 1409 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1409 : v3_fast (totient 1409) 100 = v3_phi_list.getD 1409 0 := by
  rw [tot_1409]
  rfl

theorem tot_1410 : totient 1410 = 368 := by
  have heq : (2 * (3 * (5 * (47))) : ℕ) = 1410 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_47]
  try omega

theorem v3_phi_1410 : v3_fast (totient 1410) 100 = v3_phi_list.getD 1410 0 := by
  rw [tot_1410]
  rfl

theorem tot_1411 : totient 1411 = 1312 := by
  have heq : (17 * (83) : ℕ) = 1411 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_83]
  try omega

theorem v3_phi_1411 : v3_fast (totient 1411) 100 = v3_phi_list.getD 1411 0 := by
  rw [tot_1411]
  rfl

theorem tot_1412 : totient 1412 = 704 := by
  have heq : (2^2 * (353) : ℕ) = 1412 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_353 : totient 353 = 353 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_353]
  try omega

theorem v3_phi_1412 : v3_fast (totient 1412) 100 = v3_phi_list.getD 1412 0 := by
  rw [tot_1412]
  rfl

theorem tot_1413 : totient 1413 = 936 := by
  have heq : (3^2 * (157) : ℕ) = 1413 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_157]
  try omega

theorem v3_phi_1413 : v3_fast (totient 1413) 100 = v3_phi_list.getD 1413 0 := by
  rw [tot_1413]
  rfl

theorem tot_1414 : totient 1414 = 600 := by
  have heq : (2 * (7 * (101)) : ℕ) = 1414 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_101]
  try omega

theorem v3_phi_1414 : v3_fast (totient 1414) 100 = v3_phi_list.getD 1414 0 := by
  rw [tot_1414]
  rfl

theorem tot_1415 : totient 1415 = 1128 := by
  have heq : (5 * (283) : ℕ) = 1415 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_283 : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_283]
  try omega

theorem v3_phi_1415 : v3_fast (totient 1415) 100 = v3_phi_list.getD 1415 0 := by
  rw [tot_1415]
  rfl

theorem tot_1416 : totient 1416 = 464 := by
  have heq : (2^3 * (3 * (59)) : ℕ) = 1416 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_59]
  try omega

theorem v3_phi_1416 : v3_fast (totient 1416) 100 = v3_phi_list.getD 1416 0 := by
  rw [tot_1416]
  rfl

theorem tot_1417 : totient 1417 = 1296 := by
  have heq : (13 * (109) : ℕ) = 1417 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_109]
  try omega

theorem v3_phi_1417 : v3_fast (totient 1417) 100 = v3_phi_list.getD 1417 0 := by
  rw [tot_1417]
  rfl

theorem tot_1418 : totient 1418 = 708 := by
  have heq : (2 * (709) : ℕ) = 1418 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_709 : totient 709 = 709 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_709]
  try omega

theorem v3_phi_1418 : v3_fast (totient 1418) 100 = v3_phi_list.getD 1418 0 := by
  rw [tot_1418]
  rfl

theorem tot_1419 : totient 1419 = 840 := by
  have heq : (3 * (11 * (43)) : ℕ) = 1419 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_43]
  try omega

theorem v3_phi_1419 : v3_fast (totient 1419) 100 = v3_phi_list.getD 1419 0 := by
  rw [tot_1419]
  rfl

theorem tot_1420 : totient 1420 = 560 := by
  have heq : (2^2 * (5 * (71)) : ℕ) = 1420 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_71]
  try omega

theorem v3_phi_1420 : v3_fast (totient 1420) 100 = v3_phi_list.getD 1420 0 := by
  rw [tot_1420]
  rfl

theorem tot_1421 : totient 1421 = 1176 := by
  have heq : (7^2 * (29) : ℕ) = 1421 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_29]
  try omega

theorem v3_phi_1421 : v3_fast (totient 1421) 100 = v3_phi_list.getD 1421 0 := by
  rw [tot_1421]
  rfl

theorem tot_1422 : totient 1422 = 468 := by
  have heq : (2 * (3^2 * (79)) : ℕ) = 1422 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_79]
  try omega

theorem v3_phi_1422 : v3_fast (totient 1422) 100 = v3_phi_list.getD 1422 0 := by
  rw [tot_1422]
  rfl

theorem tot_1423 : totient 1423 = 1422 := by
  have h : totient 1423 = 1423 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1423 : v3_fast (totient 1423) 100 = v3_phi_list.getD 1423 0 := by
  rw [tot_1423]
  rfl

theorem tot_1424 : totient 1424 = 704 := by
  have heq : (2^4 * (89) : ℕ) = 1424 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_89]
  try omega

theorem v3_phi_1424 : v3_fast (totient 1424) 100 = v3_phi_list.getD 1424 0 := by
  rw [tot_1424]
  rfl

theorem tot_1425 : totient 1425 = 720 := by
  have heq : (3 * (5^2 * (19)) : ℕ) = 1425 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_19]
  try omega

theorem v3_phi_1425 : v3_fast (totient 1425) 100 = v3_phi_list.getD 1425 0 := by
  rw [tot_1425]
  rfl

theorem tot_1426 : totient 1426 = 660 := by
  have heq : (2 * (23 * (31)) : ℕ) = 1426 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23, hp_31]
  try omega

theorem v3_phi_1426 : v3_fast (totient 1426) 100 = v3_phi_list.getD 1426 0 := by
  rw [tot_1426]
  rfl

theorem tot_1427 : totient 1427 = 1426 := by
  have h : totient 1427 = 1427 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1427 : v3_fast (totient 1427) 100 = v3_phi_list.getD 1427 0 := by
  rw [tot_1427]
  rfl

theorem tot_1428 : totient 1428 = 384 := by
  have heq : (2^2 * (3 * (7 * (17))) : ℕ) = 1428 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_17]
  try omega

theorem v3_phi_1428 : v3_fast (totient 1428) 100 = v3_phi_list.getD 1428 0 := by
  rw [tot_1428]
  rfl

theorem tot_1429 : totient 1429 = 1428 := by
  have h : totient 1429 = 1429 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1429 : v3_fast (totient 1429) 100 = v3_phi_list.getD 1429 0 := by
  rw [tot_1429]
  rfl

theorem tot_1430 : totient 1430 = 480 := by
  have heq : (2 * (5 * (11 * (13))) : ℕ) = 1430 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11, hp_13]
  try omega

theorem v3_phi_1430 : v3_fast (totient 1430) 100 = v3_phi_list.getD 1430 0 := by
  rw [tot_1430]
  rfl

theorem tot_1431 : totient 1431 = 936 := by
  have heq : (3^3 * (53) : ℕ) = 1431 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_53]
  try omega

theorem v3_phi_1431 : v3_fast (totient 1431) 100 = v3_phi_list.getD 1431 0 := by
  rw [tot_1431]
  rfl

theorem tot_1432 : totient 1432 = 712 := by
  have heq : (2^3 * (179) : ℕ) = 1432 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_179]
  try omega

theorem v3_phi_1432 : v3_fast (totient 1432) 100 = v3_phi_list.getD 1432 0 := by
  rw [tot_1432]
  rfl

theorem tot_1433 : totient 1433 = 1432 := by
  have h : totient 1433 = 1433 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1433 : v3_fast (totient 1433) 100 = v3_phi_list.getD 1433 0 := by
  rw [tot_1433]
  rfl

theorem tot_1434 : totient 1434 = 476 := by
  have heq : (2 * (3 * (239)) : ℕ) = 1434 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_239]
  try omega

theorem v3_phi_1434 : v3_fast (totient 1434) 100 = v3_phi_list.getD 1434 0 := by
  rw [tot_1434]
  rfl

theorem tot_1435 : totient 1435 = 960 := by
  have heq : (5 * (7 * (41)) : ℕ) = 1435 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_41]
  try omega

theorem v3_phi_1435 : v3_fast (totient 1435) 100 = v3_phi_list.getD 1435 0 := by
  rw [tot_1435]
  rfl

theorem tot_1436 : totient 1436 = 716 := by
  have heq : (2^2 * (359) : ℕ) = 1436 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_359 : totient 359 = 359 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_359]
  try omega

theorem v3_phi_1436 : v3_fast (totient 1436) 100 = v3_phi_list.getD 1436 0 := by
  rw [tot_1436]
  rfl

theorem tot_1437 : totient 1437 = 956 := by
  have heq : (3 * (479) : ℕ) = 1437 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_479 : totient 479 = 479 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_479]
  try omega

theorem v3_phi_1437 : v3_fast (totient 1437) 100 = v3_phi_list.getD 1437 0 := by
  rw [tot_1437]
  rfl

theorem tot_1438 : totient 1438 = 718 := by
  have heq : (2 * (719) : ℕ) = 1438 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_719 : totient 719 = 719 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_719]
  try omega

theorem v3_phi_1438 : v3_fast (totient 1438) 100 = v3_phi_list.getD 1438 0 := by
  rw [tot_1438]
  rfl

theorem tot_1439 : totient 1439 = 1438 := by
  have h : totient 1439 = 1439 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1439 : v3_fast (totient 1439) 100 = v3_phi_list.getD 1439 0 := by
  rw [tot_1439]
  rfl

theorem tot_1440 : totient 1440 = 384 := by
  have heq : (2^5 * (3^2 * (5)) : ℕ) = 1440 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_1440 : v3_fast (totient 1440) 100 = v3_phi_list.getD 1440 0 := by
  rw [tot_1440]
  rfl

theorem tot_1441 : totient 1441 = 1300 := by
  have heq : (11 * (131) : ℕ) = 1441 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_131]
  try omega

theorem v3_phi_1441 : v3_fast (totient 1441) 100 = v3_phi_list.getD 1441 0 := by
  rw [tot_1441]
  rfl

theorem tot_1442 : totient 1442 = 612 := by
  have heq : (2 * (7 * (103)) : ℕ) = 1442 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_103]
  try omega

theorem v3_phi_1442 : v3_fast (totient 1442) 100 = v3_phi_list.getD 1442 0 := by
  rw [tot_1442]
  rfl

theorem tot_1443 : totient 1443 = 864 := by
  have heq : (3 * (13 * (37)) : ℕ) = 1443 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_37]
  try omega

theorem v3_phi_1443 : v3_fast (totient 1443) 100 = v3_phi_list.getD 1443 0 := by
  rw [tot_1443]
  rfl

theorem tot_1444 : totient 1444 = 684 := by
  have heq : (2^2 * (19^2) : ℕ) = 1444 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient (19^2) = 19^1 * (19 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_19]
  try omega

theorem v3_phi_1444 : v3_fast (totient 1444) 100 = v3_phi_list.getD 1444 0 := by
  rw [tot_1444]
  rfl

theorem tot_1445 : totient 1445 = 1088 := by
  have heq : (5 * (17^2) : ℕ) = 1445 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_17]
  try omega

theorem v3_phi_1445 : v3_fast (totient 1445) 100 = v3_phi_list.getD 1445 0 := by
  rw [tot_1445]
  rfl

theorem tot_1446 : totient 1446 = 480 := by
  have heq : (2 * (3 * (241)) : ℕ) = 1446 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_241]
  try omega

theorem v3_phi_1446 : v3_fast (totient 1446) 100 = v3_phi_list.getD 1446 0 := by
  rw [tot_1446]
  rfl

theorem tot_1447 : totient 1447 = 1446 := by
  have h : totient 1447 = 1447 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1447 : v3_fast (totient 1447) 100 = v3_phi_list.getD 1447 0 := by
  rw [tot_1447]
  rfl

theorem tot_1448 : totient 1448 = 720 := by
  have heq : (2^3 * (181) : ℕ) = 1448 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_181]
  try omega

theorem v3_phi_1448 : v3_fast (totient 1448) 100 = v3_phi_list.getD 1448 0 := by
  rw [tot_1448]
  rfl

theorem tot_1449 : totient 1449 = 792 := by
  have heq : (3^2 * (7 * (23)) : ℕ) = 1449 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_23]
  try omega

theorem v3_phi_1449 : v3_fast (totient 1449) 100 = v3_phi_list.getD 1449 0 := by
  rw [tot_1449]
  rfl

theorem tot_1450 : totient 1450 = 560 := by
  have heq : (2 * (5^2 * (29)) : ℕ) = 1450 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_29]
  try omega

theorem v3_phi_1450 : v3_fast (totient 1450) 100 = v3_phi_list.getD 1450 0 := by
  rw [tot_1450]
  rfl

theorem tot_1451 : totient 1451 = 1450 := by
  have h : totient 1451 = 1451 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1451 : v3_fast (totient 1451) 100 = v3_phi_list.getD 1451 0 := by
  rw [tot_1451]
  rfl

theorem tot_1452 : totient 1452 = 440 := by
  have heq : (2^2 * (3 * (11^2)) : ℕ) = 1452 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_1452 : v3_fast (totient 1452) 100 = v3_phi_list.getD 1452 0 := by
  rw [tot_1452]
  rfl

theorem tot_1453 : totient 1453 = 1452 := by
  have h : totient 1453 = 1453 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1453 : v3_fast (totient 1453) 100 = v3_phi_list.getD 1453 0 := by
  rw [tot_1453]
  rfl

theorem tot_1454 : totient 1454 = 726 := by
  have heq : (2 * (727) : ℕ) = 1454 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_727 : totient 727 = 727 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_727]
  try omega

theorem v3_phi_1454 : v3_fast (totient 1454) 100 = v3_phi_list.getD 1454 0 := by
  rw [tot_1454]
  rfl

theorem tot_1455 : totient 1455 = 768 := by
  have heq : (3 * (5 * (97)) : ℕ) = 1455 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_97]
  try omega

theorem v3_phi_1455 : v3_fast (totient 1455) 100 = v3_phi_list.getD 1455 0 := by
  rw [tot_1455]
  rfl

theorem tot_1456 : totient 1456 = 576 := by
  have heq : (2^4 * (7 * (13)) : ℕ) = 1456 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_13]
  try omega

theorem v3_phi_1456 : v3_fast (totient 1456) 100 = v3_phi_list.getD 1456 0 := by
  rw [tot_1456]
  rfl

theorem tot_1457 : totient 1457 = 1380 := by
  have heq : (31 * (47) : ℕ) = 1457 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_31, hp_47]
  try omega

theorem v3_phi_1457 : v3_fast (totient 1457) 100 = v3_phi_list.getD 1457 0 := by
  rw [tot_1457]
  rfl

theorem tot_1458 : totient 1458 = 486 := by
  have heq : (2 * (3^6) : ℕ) = 1458 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^6) = 3^5 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_1458 : v3_fast (totient 1458) 100 = v3_phi_list.getD 1458 0 := by
  rw [tot_1458]
  rfl

theorem tot_1459 : totient 1459 = 1458 := by
  have h : totient 1459 = 1459 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1459 : v3_fast (totient 1459) 100 = v3_phi_list.getD 1459 0 := by
  rw [tot_1459]
  rfl

theorem tot_1460 : totient 1460 = 576 := by
  have heq : (2^2 * (5 * (73)) : ℕ) = 1460 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_73]
  try omega

theorem v3_phi_1460 : v3_fast (totient 1460) 100 = v3_phi_list.getD 1460 0 := by
  rw [tot_1460]
  rfl

theorem tot_1461 : totient 1461 = 972 := by
  have heq : (3 * (487) : ℕ) = 1461 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_487 : totient 487 = 487 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_487]
  try omega

theorem v3_phi_1461 : v3_fast (totient 1461) 100 = v3_phi_list.getD 1461 0 := by
  rw [tot_1461]
  rfl

theorem tot_1462 : totient 1462 = 672 := by
  have heq : (2 * (17 * (43)) : ℕ) = 1462 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_43]
  try omega

theorem v3_phi_1462 : v3_fast (totient 1462) 100 = v3_phi_list.getD 1462 0 := by
  rw [tot_1462]
  rfl

theorem tot_1463 : totient 1463 = 1080 := by
  have heq : (7 * (11 * (19)) : ℕ) = 1463 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11, hp_19]
  try omega

theorem v3_phi_1463 : v3_fast (totient 1463) 100 = v3_phi_list.getD 1463 0 := by
  rw [tot_1463]
  rfl

theorem tot_1464 : totient 1464 = 480 := by
  have heq : (2^3 * (3 * (61)) : ℕ) = 1464 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_61]
  try omega

theorem v3_phi_1464 : v3_fast (totient 1464) 100 = v3_phi_list.getD 1464 0 := by
  rw [tot_1464]
  rfl

theorem tot_1465 : totient 1465 = 1168 := by
  have heq : (5 * (293) : ℕ) = 1465 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_293 : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_293]
  try omega

theorem v3_phi_1465 : v3_fast (totient 1465) 100 = v3_phi_list.getD 1465 0 := by
  rw [tot_1465]
  rfl

theorem tot_1466 : totient 1466 = 732 := by
  have heq : (2 * (733) : ℕ) = 1466 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_733 : totient 733 = 733 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_733]
  try omega

theorem v3_phi_1466 : v3_fast (totient 1466) 100 = v3_phi_list.getD 1466 0 := by
  rw [tot_1466]
  rfl

theorem tot_1467 : totient 1467 = 972 := by
  have heq : (3^2 * (163) : ℕ) = 1467 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_163]
  try omega

theorem v3_phi_1467 : v3_fast (totient 1467) 100 = v3_phi_list.getD 1467 0 := by
  rw [tot_1467]
  rfl

theorem tot_1468 : totient 1468 = 732 := by
  have heq : (2^2 * (367) : ℕ) = 1468 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_367 : totient 367 = 367 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_367]
  try omega

theorem v3_phi_1468 : v3_fast (totient 1468) 100 = v3_phi_list.getD 1468 0 := by
  rw [tot_1468]
  rfl

theorem tot_1469 : totient 1469 = 1344 := by
  have heq : (13 * (113) : ℕ) = 1469 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_113]
  try omega

theorem v3_phi_1469 : v3_fast (totient 1469) 100 = v3_phi_list.getD 1469 0 := by
  rw [tot_1469]
  rfl

theorem tot_1470 : totient 1470 = 336 := by
  have heq : (2 * (3 * (5 * (7^2))) : ℕ) = 1470 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_1470 : v3_fast (totient 1470) 100 = v3_phi_list.getD 1470 0 := by
  rw [tot_1470]
  rfl

theorem tot_1471 : totient 1471 = 1470 := by
  have h : totient 1471 = 1471 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1471 : v3_fast (totient 1471) 100 = v3_phi_list.getD 1471 0 := by
  rw [tot_1471]
  rfl

theorem tot_1472 : totient 1472 = 704 := by
  have heq : (2^6 * (23) : ℕ) = 1472 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23]
  try omega

theorem v3_phi_1472 : v3_fast (totient 1472) 100 = v3_phi_list.getD 1472 0 := by
  rw [tot_1472]
  rfl

theorem tot_1473 : totient 1473 = 980 := by
  have heq : (3 * (491) : ℕ) = 1473 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_491 : totient 491 = 491 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_491]
  try omega

theorem v3_phi_1473 : v3_fast (totient 1473) 100 = v3_phi_list.getD 1473 0 := by
  rw [tot_1473]
  rfl

theorem tot_1474 : totient 1474 = 660 := by
  have heq : (2 * (11 * (67)) : ℕ) = 1474 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_67]
  try omega

theorem v3_phi_1474 : v3_fast (totient 1474) 100 = v3_phi_list.getD 1474 0 := by
  rw [tot_1474]
  rfl

theorem tot_1475 : totient 1475 = 1160 := by
  have heq : (5^2 * (59) : ℕ) = 1475 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_59]
  try omega

theorem v3_phi_1475 : v3_fast (totient 1475) 100 = v3_phi_list.getD 1475 0 := by
  rw [tot_1475]
  rfl

theorem tot_1476 : totient 1476 = 480 := by
  have heq : (2^2 * (3^2 * (41)) : ℕ) = 1476 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_41]
  try omega

theorem v3_phi_1476 : v3_fast (totient 1476) 100 = v3_phi_list.getD 1476 0 := by
  rw [tot_1476]
  rfl

theorem tot_1477 : totient 1477 = 1260 := by
  have heq : (7 * (211) : ℕ) = 1477 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_211]
  try omega

theorem v3_phi_1477 : v3_fast (totient 1477) 100 = v3_phi_list.getD 1477 0 := by
  rw [tot_1477]
  rfl

theorem tot_1478 : totient 1478 = 738 := by
  have heq : (2 * (739) : ℕ) = 1478 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_739 : totient 739 = 739 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_739]
  try omega

theorem v3_phi_1478 : v3_fast (totient 1478) 100 = v3_phi_list.getD 1478 0 := by
  rw [tot_1478]
  rfl

theorem tot_1479 : totient 1479 = 896 := by
  have heq : (3 * (17 * (29)) : ℕ) = 1479 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17, hp_29]
  try omega

theorem v3_phi_1479 : v3_fast (totient 1479) 100 = v3_phi_list.getD 1479 0 := by
  rw [tot_1479]
  rfl

theorem tot_1480 : totient 1480 = 576 := by
  have heq : (2^3 * (5 * (37)) : ℕ) = 1480 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_37]
  try omega

theorem v3_phi_1480 : v3_fast (totient 1480) 100 = v3_phi_list.getD 1480 0 := by
  rw [tot_1480]
  rfl

theorem tot_1481 : totient 1481 = 1480 := by
  have h : totient 1481 = 1481 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1481 : v3_fast (totient 1481) 100 = v3_phi_list.getD 1481 0 := by
  rw [tot_1481]
  rfl

theorem tot_1482 : totient 1482 = 432 := by
  have heq : (2 * (3 * (13 * (19))) : ℕ) = 1482 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13, hp_19]
  try omega

theorem v3_phi_1482 : v3_fast (totient 1482) 100 = v3_phi_list.getD 1482 0 := by
  rw [tot_1482]
  rfl

theorem tot_1483 : totient 1483 = 1482 := by
  have h : totient 1483 = 1483 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1483 : v3_fast (totient 1483) 100 = v3_phi_list.getD 1483 0 := by
  rw [tot_1483]
  rfl

theorem tot_1484 : totient 1484 = 624 := by
  have heq : (2^2 * (7 * (53)) : ℕ) = 1484 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_53]
  try omega

theorem v3_phi_1484 : v3_fast (totient 1484) 100 = v3_phi_list.getD 1484 0 := by
  rw [tot_1484]
  rfl

theorem tot_1485 : totient 1485 = 720 := by
  have heq : (3^3 * (5 * (11)) : ℕ) = 1485 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_11]
  try omega

theorem v3_phi_1485 : v3_fast (totient 1485) 100 = v3_phi_list.getD 1485 0 := by
  rw [tot_1485]
  rfl

theorem tot_1486 : totient 1486 = 742 := by
  have heq : (2 * (743) : ℕ) = 1486 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_743 : totient 743 = 743 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_743]
  try omega

theorem v3_phi_1486 : v3_fast (totient 1486) 100 = v3_phi_list.getD 1486 0 := by
  rw [tot_1486]
  rfl

theorem tot_1487 : totient 1487 = 1486 := by
  have h : totient 1487 = 1487 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1487 : v3_fast (totient 1487) 100 = v3_phi_list.getD 1487 0 := by
  rw [tot_1487]
  rfl

theorem tot_1488 : totient 1488 = 480 := by
  have heq : (2^4 * (3 * (31)) : ℕ) = 1488 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31]
  try omega

theorem v3_phi_1488 : v3_fast (totient 1488) 100 = v3_phi_list.getD 1488 0 := by
  rw [tot_1488]
  rfl

theorem tot_1489 : totient 1489 = 1488 := by
  have h : totient 1489 = 1489 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1489 : v3_fast (totient 1489) 100 = v3_phi_list.getD 1489 0 := by
  rw [tot_1489]
  rfl

theorem tot_1490 : totient 1490 = 592 := by
  have heq : (2 * (5 * (149)) : ℕ) = 1490 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_149]
  try omega

theorem v3_phi_1490 : v3_fast (totient 1490) 100 = v3_phi_list.getD 1490 0 := by
  rw [tot_1490]
  rfl

theorem tot_1491 : totient 1491 = 840 := by
  have heq : (3 * (7 * (71)) : ℕ) = 1491 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_71]
  try omega

theorem v3_phi_1491 : v3_fast (totient 1491) 100 = v3_phi_list.getD 1491 0 := by
  rw [tot_1491]
  rfl

theorem tot_1492 : totient 1492 = 744 := by
  have heq : (2^2 * (373) : ℕ) = 1492 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_373 : totient 373 = 373 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_373]
  try omega

theorem v3_phi_1492 : v3_fast (totient 1492) 100 = v3_phi_list.getD 1492 0 := by
  rw [tot_1492]
  rfl

theorem tot_1493 : totient 1493 = 1492 := by
  have h : totient 1493 = 1493 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1493 : v3_fast (totient 1493) 100 = v3_phi_list.getD 1493 0 := by
  rw [tot_1493]
  rfl

theorem tot_1494 : totient 1494 = 492 := by
  have heq : (2 * (3^2 * (83)) : ℕ) = 1494 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_83]
  try omega

theorem v3_phi_1494 : v3_fast (totient 1494) 100 = v3_phi_list.getD 1494 0 := by
  rw [tot_1494]
  rfl

theorem tot_1495 : totient 1495 = 1056 := by
  have heq : (5 * (13 * (23)) : ℕ) = 1495 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13, hp_23]
  try omega

theorem v3_phi_1495 : v3_fast (totient 1495) 100 = v3_phi_list.getD 1495 0 := by
  rw [tot_1495]
  rfl

theorem tot_1496 : totient 1496 = 640 := by
  have heq : (2^3 * (11 * (17)) : ℕ) = 1496 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_17]
  try omega

theorem v3_phi_1496 : v3_fast (totient 1496) 100 = v3_phi_list.getD 1496 0 := by
  rw [tot_1496]
  rfl

theorem tot_1497 : totient 1497 = 996 := by
  have heq : (3 * (499) : ℕ) = 1497 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_499 : totient 499 = 499 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_499]
  try omega

theorem v3_phi_1497 : v3_fast (totient 1497) 100 = v3_phi_list.getD 1497 0 := by
  rw [tot_1497]
  rfl

theorem tot_1498 : totient 1498 = 636 := by
  have heq : (2 * (7 * (107)) : ℕ) = 1498 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_107]
  try omega

theorem v3_phi_1498 : v3_fast (totient 1498) 100 = v3_phi_list.getD 1498 0 := by
  rw [tot_1498]
  rfl

theorem tot_1499 : totient 1499 = 1498 := by
  have h : totient 1499 = 1499 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1499 : v3_fast (totient 1499) 100 = v3_phi_list.getD 1499 0 := by
  rw [tot_1499]
  rfl

theorem tot_1500 : totient 1500 = 400 := by
  have heq : (2^2 * (3 * (5^3)) : ℕ) = 1500 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_1500 : v3_fast (totient 1500) 100 = v3_phi_list.getD 1500 0 := by
  rw [tot_1500]
  rfl

theorem tot_1501 : totient 1501 = 1404 := by
  have heq : (19 * (79) : ℕ) = 1501 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_79]
  try omega

theorem v3_phi_1501 : v3_fast (totient 1501) 100 = v3_phi_list.getD 1501 0 := by
  rw [tot_1501]
  rfl

theorem tot_1502 : totient 1502 = 750 := by
  have heq : (2 * (751) : ℕ) = 1502 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_751 : totient 751 = 751 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_751]
  try omega

theorem v3_phi_1502 : v3_fast (totient 1502) 100 = v3_phi_list.getD 1502 0 := by
  rw [tot_1502]
  rfl

theorem tot_1503 : totient 1503 = 996 := by
  have heq : (3^2 * (167) : ℕ) = 1503 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_167]
  try omega

theorem v3_phi_1503 : v3_fast (totient 1503) 100 = v3_phi_list.getD 1503 0 := by
  rw [tot_1503]
  rfl

theorem tot_1504 : totient 1504 = 736 := by
  have heq : (2^5 * (47) : ℕ) = 1504 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_47]
  try omega

theorem v3_phi_1504 : v3_fast (totient 1504) 100 = v3_phi_list.getD 1504 0 := by
  rw [tot_1504]
  rfl

theorem tot_1505 : totient 1505 = 1008 := by
  have heq : (5 * (7 * (43)) : ℕ) = 1505 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_43]
  try omega

theorem v3_phi_1505 : v3_fast (totient 1505) 100 = v3_phi_list.getD 1505 0 := by
  rw [tot_1505]
  rfl

theorem tot_1506 : totient 1506 = 500 := by
  have heq : (2 * (3 * (251)) : ℕ) = 1506 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_251]
  try omega

theorem v3_phi_1506 : v3_fast (totient 1506) 100 = v3_phi_list.getD 1506 0 := by
  rw [tot_1506]
  rfl

theorem tot_1507 : totient 1507 = 1360 := by
  have heq : (11 * (137) : ℕ) = 1507 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_137]
  try omega

theorem v3_phi_1507 : v3_fast (totient 1507) 100 = v3_phi_list.getD 1507 0 := by
  rw [tot_1507]
  rfl

theorem tot_1508 : totient 1508 = 672 := by
  have heq : (2^2 * (13 * (29)) : ℕ) = 1508 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_29]
  try omega

theorem v3_phi_1508 : v3_fast (totient 1508) 100 = v3_phi_list.getD 1508 0 := by
  rw [tot_1508]
  rfl

theorem tot_1509 : totient 1509 = 1004 := by
  have heq : (3 * (503) : ℕ) = 1509 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_503 : totient 503 = 503 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_503]
  try omega

theorem v3_phi_1509 : v3_fast (totient 1509) 100 = v3_phi_list.getD 1509 0 := by
  rw [tot_1509]
  rfl

theorem tot_1510 : totient 1510 = 600 := by
  have heq : (2 * (5 * (151)) : ℕ) = 1510 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_151]
  try omega

theorem v3_phi_1510 : v3_fast (totient 1510) 100 = v3_phi_list.getD 1510 0 := by
  rw [tot_1510]
  rfl

theorem tot_1511 : totient 1511 = 1510 := by
  have h : totient 1511 = 1511 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1511 : v3_fast (totient 1511) 100 = v3_phi_list.getD 1511 0 := by
  rw [tot_1511]
  rfl

theorem tot_1512 : totient 1512 = 432 := by
  have heq : (2^3 * (3^3 * (7)) : ℕ) = 1512 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_1512 : v3_fast (totient 1512) 100 = v3_phi_list.getD 1512 0 := by
  rw [tot_1512]
  rfl

theorem tot_1513 : totient 1513 = 1408 := by
  have heq : (17 * (89) : ℕ) = 1513 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_89]
  try omega

theorem v3_phi_1513 : v3_fast (totient 1513) 100 = v3_phi_list.getD 1513 0 := by
  rw [tot_1513]
  rfl

theorem tot_1514 : totient 1514 = 756 := by
  have heq : (2 * (757) : ℕ) = 1514 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_757 : totient 757 = 757 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_757]
  try omega

theorem v3_phi_1514 : v3_fast (totient 1514) 100 = v3_phi_list.getD 1514 0 := by
  rw [tot_1514]
  rfl

theorem tot_1515 : totient 1515 = 800 := by
  have heq : (3 * (5 * (101)) : ℕ) = 1515 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_101]
  try omega

theorem v3_phi_1515 : v3_fast (totient 1515) 100 = v3_phi_list.getD 1515 0 := by
  rw [tot_1515]
  rfl

theorem tot_1516 : totient 1516 = 756 := by
  have heq : (2^2 * (379) : ℕ) = 1516 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_379 : totient 379 = 379 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_379]
  try omega

theorem v3_phi_1516 : v3_fast (totient 1516) 100 = v3_phi_list.getD 1516 0 := by
  rw [tot_1516]
  rfl

theorem tot_1517 : totient 1517 = 1440 := by
  have heq : (37 * (41) : ℕ) = 1517 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_37, hp_41]
  try omega

theorem v3_phi_1517 : v3_fast (totient 1517) 100 = v3_phi_list.getD 1517 0 := by
  rw [tot_1517]
  rfl

theorem tot_1518 : totient 1518 = 440 := by
  have heq : (2 * (3 * (11 * (23))) : ℕ) = 1518 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11, hp_23]
  try omega

theorem v3_phi_1518 : v3_fast (totient 1518) 100 = v3_phi_list.getD 1518 0 := by
  rw [tot_1518]
  rfl

theorem tot_1519 : totient 1519 = 1260 := by
  have heq : (7^2 * (31) : ℕ) = 1519 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_31]
  try omega

theorem v3_phi_1519 : v3_fast (totient 1519) 100 = v3_phi_list.getD 1519 0 := by
  rw [tot_1519]
  rfl

theorem tot_1520 : totient 1520 = 576 := by
  have heq : (2^4 * (5 * (19)) : ℕ) = 1520 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_19]
  try omega

theorem v3_phi_1520 : v3_fast (totient 1520) 100 = v3_phi_list.getD 1520 0 := by
  rw [tot_1520]
  rfl

theorem tot_1521 : totient 1521 = 936 := by
  have heq : (3^2 * (13^2) : ℕ) = 1521 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_13]
  try omega

theorem v3_phi_1521 : v3_fast (totient 1521) 100 = v3_phi_list.getD 1521 0 := by
  rw [tot_1521]
  rfl

theorem tot_1522 : totient 1522 = 760 := by
  have heq : (2 * (761) : ℕ) = 1522 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_761 : totient 761 = 761 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_761]
  try omega

theorem v3_phi_1522 : v3_fast (totient 1522) 100 = v3_phi_list.getD 1522 0 := by
  rw [tot_1522]
  rfl

theorem tot_1523 : totient 1523 = 1522 := by
  have h : totient 1523 = 1523 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1523 : v3_fast (totient 1523) 100 = v3_phi_list.getD 1523 0 := by
  rw [tot_1523]
  rfl

theorem tot_1524 : totient 1524 = 504 := by
  have heq : (2^2 * (3 * (127)) : ℕ) = 1524 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_127]
  try omega

theorem v3_phi_1524 : v3_fast (totient 1524) 100 = v3_phi_list.getD 1524 0 := by
  rw [tot_1524]
  rfl

theorem tot_1525 : totient 1525 = 1200 := by
  have heq : (5^2 * (61) : ℕ) = 1525 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_61]
  try omega

theorem v3_phi_1525 : v3_fast (totient 1525) 100 = v3_phi_list.getD 1525 0 := by
  rw [tot_1525]
  rfl

theorem tot_1526 : totient 1526 = 648 := by
  have heq : (2 * (7 * (109)) : ℕ) = 1526 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_109]
  try omega

theorem v3_phi_1526 : v3_fast (totient 1526) 100 = v3_phi_list.getD 1526 0 := by
  rw [tot_1526]
  rfl

theorem tot_1527 : totient 1527 = 1016 := by
  have heq : (3 * (509) : ℕ) = 1527 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_509 : totient 509 = 509 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_509]
  try omega

theorem v3_phi_1527 : v3_fast (totient 1527) 100 = v3_phi_list.getD 1527 0 := by
  rw [tot_1527]
  rfl

theorem tot_1528 : totient 1528 = 760 := by
  have heq : (2^3 * (191) : ℕ) = 1528 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_191]
  try omega

theorem v3_phi_1528 : v3_fast (totient 1528) 100 = v3_phi_list.getD 1528 0 := by
  rw [tot_1528]
  rfl

theorem tot_1529 : totient 1529 = 1380 := by
  have heq : (11 * (139) : ℕ) = 1529 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_139]
  try omega

theorem v3_phi_1529 : v3_fast (totient 1529) 100 = v3_phi_list.getD 1529 0 := by
  rw [tot_1529]
  rfl

theorem tot_1530 : totient 1530 = 384 := by
  have heq : (2 * (3^2 * (5 * (17))) : ℕ) = 1530 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_17]
  try omega

theorem v3_phi_1530 : v3_fast (totient 1530) 100 = v3_phi_list.getD 1530 0 := by
  rw [tot_1530]
  rfl

theorem tot_1531 : totient 1531 = 1530 := by
  have h : totient 1531 = 1531 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1531 : v3_fast (totient 1531) 100 = v3_phi_list.getD 1531 0 := by
  rw [tot_1531]
  rfl

theorem tot_1532 : totient 1532 = 764 := by
  have heq : (2^2 * (383) : ℕ) = 1532 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_383 : totient 383 = 383 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_383]
  try omega

theorem v3_phi_1532 : v3_fast (totient 1532) 100 = v3_phi_list.getD 1532 0 := by
  rw [tot_1532]
  rfl

theorem tot_1533 : totient 1533 = 864 := by
  have heq : (3 * (7 * (73)) : ℕ) = 1533 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_73]
  try omega

theorem v3_phi_1533 : v3_fast (totient 1533) 100 = v3_phi_list.getD 1533 0 := by
  rw [tot_1533]
  rfl

theorem tot_1534 : totient 1534 = 696 := by
  have heq : (2 * (13 * (59)) : ℕ) = 1534 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_59]
  try omega

theorem v3_phi_1534 : v3_fast (totient 1534) 100 = v3_phi_list.getD 1534 0 := by
  rw [tot_1534]
  rfl

theorem tot_1535 : totient 1535 = 1224 := by
  have heq : (5 * (307) : ℕ) = 1535 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_307 : totient 307 = 307 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_307]
  try omega

theorem v3_phi_1535 : v3_fast (totient 1535) 100 = v3_phi_list.getD 1535 0 := by
  rw [tot_1535]
  rfl

theorem tot_1536 : totient 1536 = 512 := by
  have heq : (2^9 * (3) : ℕ) = 1536 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^9) = 2^8 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_1536 : v3_fast (totient 1536) 100 = v3_phi_list.getD 1536 0 := by
  rw [tot_1536]
  rfl

theorem tot_1537 : totient 1537 = 1456 := by
  have heq : (29 * (53) : ℕ) = 1537 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_53]
  try omega

theorem v3_phi_1537 : v3_fast (totient 1537) 100 = v3_phi_list.getD 1537 0 := by
  rw [tot_1537]
  rfl

theorem tot_1538 : totient 1538 = 768 := by
  have heq : (2 * (769) : ℕ) = 1538 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_769 : totient 769 = 769 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_769]
  try omega

theorem v3_phi_1538 : v3_fast (totient 1538) 100 = v3_phi_list.getD 1538 0 := by
  rw [tot_1538]
  rfl

theorem tot_1539 : totient 1539 = 972 := by
  have heq : (3^4 * (19) : ℕ) = 1539 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19]
  try omega

theorem v3_phi_1539 : v3_fast (totient 1539) 100 = v3_phi_list.getD 1539 0 := by
  rw [tot_1539]
  rfl

theorem tot_1540 : totient 1540 = 480 := by
  have heq : (2^2 * (5 * (7 * (11))) : ℕ) = 1540 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_11]
  try omega

theorem v3_phi_1540 : v3_fast (totient 1540) 100 = v3_phi_list.getD 1540 0 := by
  rw [tot_1540]
  rfl

theorem tot_1541 : totient 1541 = 1452 := by
  have heq : (23 * (67) : ℕ) = 1541 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_67]
  try omega

theorem v3_phi_1541 : v3_fast (totient 1541) 100 = v3_phi_list.getD 1541 0 := by
  rw [tot_1541]
  rfl

theorem tot_1542 : totient 1542 = 512 := by
  have heq : (2 * (3 * (257)) : ℕ) = 1542 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_257]
  try omega

theorem v3_phi_1542 : v3_fast (totient 1542) 100 = v3_phi_list.getD 1542 0 := by
  rw [tot_1542]
  rfl

theorem tot_1543 : totient 1543 = 1542 := by
  have h : totient 1543 = 1543 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1543 : v3_fast (totient 1543) 100 = v3_phi_list.getD 1543 0 := by
  rw [tot_1543]
  rfl

theorem tot_1544 : totient 1544 = 768 := by
  have heq : (2^3 * (193) : ℕ) = 1544 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_193]
  try omega

theorem v3_phi_1544 : v3_fast (totient 1544) 100 = v3_phi_list.getD 1544 0 := by
  rw [tot_1544]
  rfl

theorem tot_1545 : totient 1545 = 816 := by
  have heq : (3 * (5 * (103)) : ℕ) = 1545 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_103]
  try omega

theorem v3_phi_1545 : v3_fast (totient 1545) 100 = v3_phi_list.getD 1545 0 := by
  rw [tot_1545]
  rfl

theorem tot_1546 : totient 1546 = 772 := by
  have heq : (2 * (773) : ℕ) = 1546 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_773 : totient 773 = 773 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_773]
  try omega

theorem v3_phi_1546 : v3_fast (totient 1546) 100 = v3_phi_list.getD 1546 0 := by
  rw [tot_1546]
  rfl

theorem tot_1547 : totient 1547 = 1152 := by
  have heq : (7 * (13 * (17)) : ℕ) = 1547 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_13, hp_17]
  try omega

theorem v3_phi_1547 : v3_fast (totient 1547) 100 = v3_phi_list.getD 1547 0 := by
  rw [tot_1547]
  rfl

theorem tot_1548 : totient 1548 = 504 := by
  have heq : (2^2 * (3^2 * (43)) : ℕ) = 1548 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_43]
  try omega

theorem v3_phi_1548 : v3_fast (totient 1548) 100 = v3_phi_list.getD 1548 0 := by
  rw [tot_1548]
  rfl

theorem tot_1549 : totient 1549 = 1548 := by
  have h : totient 1549 = 1549 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1549 : v3_fast (totient 1549) 100 = v3_phi_list.getD 1549 0 := by
  rw [tot_1549]
  rfl

theorem tot_1550 : totient 1550 = 600 := by
  have heq : (2 * (5^2 * (31)) : ℕ) = 1550 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_31]
  try omega

theorem v3_phi_1550 : v3_fast (totient 1550) 100 = v3_phi_list.getD 1550 0 := by
  rw [tot_1550]
  rfl

theorem tot_1551 : totient 1551 = 920 := by
  have heq : (3 * (11 * (47)) : ℕ) = 1551 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_47]
  try omega

theorem v3_phi_1551 : v3_fast (totient 1551) 100 = v3_phi_list.getD 1551 0 := by
  rw [tot_1551]
  rfl

theorem tot_1552 : totient 1552 = 768 := by
  have heq : (2^4 * (97) : ℕ) = 1552 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_97]
  try omega

theorem v3_phi_1552 : v3_fast (totient 1552) 100 = v3_phi_list.getD 1552 0 := by
  rw [tot_1552]
  rfl

theorem tot_1553 : totient 1553 = 1552 := by
  have h : totient 1553 = 1553 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1553 : v3_fast (totient 1553) 100 = v3_phi_list.getD 1553 0 := by
  rw [tot_1553]
  rfl

theorem tot_1554 : totient 1554 = 432 := by
  have heq : (2 * (3 * (7 * (37))) : ℕ) = 1554 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_37]
  try omega

theorem v3_phi_1554 : v3_fast (totient 1554) 100 = v3_phi_list.getD 1554 0 := by
  rw [tot_1554]
  rfl

theorem tot_1555 : totient 1555 = 1240 := by
  have heq : (5 * (311) : ℕ) = 1555 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_311 : totient 311 = 311 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_311]
  try omega

theorem v3_phi_1555 : v3_fast (totient 1555) 100 = v3_phi_list.getD 1555 0 := by
  rw [tot_1555]
  rfl

theorem tot_1556 : totient 1556 = 776 := by
  have heq : (2^2 * (389) : ℕ) = 1556 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_389 : totient 389 = 389 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_389]
  try omega

theorem v3_phi_1556 : v3_fast (totient 1556) 100 = v3_phi_list.getD 1556 0 := by
  rw [tot_1556]
  rfl

theorem tot_1557 : totient 1557 = 1032 := by
  have heq : (3^2 * (173) : ℕ) = 1557 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_173]
  try omega

theorem v3_phi_1557 : v3_fast (totient 1557) 100 = v3_phi_list.getD 1557 0 := by
  rw [tot_1557]
  rfl

theorem tot_1558 : totient 1558 = 720 := by
  have heq : (2 * (19 * (41)) : ℕ) = 1558 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_41]
  try omega

theorem v3_phi_1558 : v3_fast (totient 1558) 100 = v3_phi_list.getD 1558 0 := by
  rw [tot_1558]
  rfl

theorem tot_1559 : totient 1559 = 1558 := by
  have h : totient 1559 = 1559 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1559 : v3_fast (totient 1559) 100 = v3_phi_list.getD 1559 0 := by
  rw [tot_1559]
  rfl

theorem tot_1560 : totient 1560 = 384 := by
  have heq : (2^3 * (3 * (5 * (13))) : ℕ) = 1560 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_13]
  try omega

theorem v3_phi_1560 : v3_fast (totient 1560) 100 = v3_phi_list.getD 1560 0 := by
  rw [tot_1560]
  rfl

theorem tot_1561 : totient 1561 = 1332 := by
  have heq : (7 * (223) : ℕ) = 1561 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_223]
  try omega

theorem v3_phi_1561 : v3_fast (totient 1561) 100 = v3_phi_list.getD 1561 0 := by
  rw [tot_1561]
  rfl

theorem tot_1562 : totient 1562 = 700 := by
  have heq : (2 * (11 * (71)) : ℕ) = 1562 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_71]
  try omega

theorem v3_phi_1562 : v3_fast (totient 1562) 100 = v3_phi_list.getD 1562 0 := by
  rw [tot_1562]
  rfl

theorem tot_1563 : totient 1563 = 1040 := by
  have heq : (3 * (521) : ℕ) = 1563 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_521 : totient 521 = 521 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_521]
  try omega

theorem v3_phi_1563 : v3_fast (totient 1563) 100 = v3_phi_list.getD 1563 0 := by
  rw [tot_1563]
  rfl

theorem tot_1564 : totient 1564 = 704 := by
  have heq : (2^2 * (17 * (23)) : ℕ) = 1564 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_23]
  try omega

theorem v3_phi_1564 : v3_fast (totient 1564) 100 = v3_phi_list.getD 1564 0 := by
  rw [tot_1564]
  rfl

theorem tot_1565 : totient 1565 = 1248 := by
  have heq : (5 * (313) : ℕ) = 1565 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_313 : totient 313 = 313 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_313]
  try omega

theorem v3_phi_1565 : v3_fast (totient 1565) 100 = v3_phi_list.getD 1565 0 := by
  rw [tot_1565]
  rfl

theorem tot_1566 : totient 1566 = 504 := by
  have heq : (2 * (3^3 * (29)) : ℕ) = 1566 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29]
  try omega

theorem v3_phi_1566 : v3_fast (totient 1566) 100 = v3_phi_list.getD 1566 0 := by
  rw [tot_1566]
  rfl

theorem tot_1567 : totient 1567 = 1566 := by
  have h : totient 1567 = 1567 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1567 : v3_fast (totient 1567) 100 = v3_phi_list.getD 1567 0 := by
  rw [tot_1567]
  rfl

theorem tot_1568 : totient 1568 = 672 := by
  have heq : (2^5 * (7^2) : ℕ) = 1568 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_1568 : v3_fast (totient 1568) 100 = v3_phi_list.getD 1568 0 := by
  rw [tot_1568]
  rfl

theorem tot_1569 : totient 1569 = 1044 := by
  have heq : (3 * (523) : ℕ) = 1569 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_523 : totient 523 = 523 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_523]
  try omega

theorem v3_phi_1569 : v3_fast (totient 1569) 100 = v3_phi_list.getD 1569 0 := by
  rw [tot_1569]
  rfl

theorem tot_1570 : totient 1570 = 624 := by
  have heq : (2 * (5 * (157)) : ℕ) = 1570 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_157]
  try omega

theorem v3_phi_1570 : v3_fast (totient 1570) 100 = v3_phi_list.getD 1570 0 := by
  rw [tot_1570]
  rfl

theorem tot_1571 : totient 1571 = 1570 := by
  have h : totient 1571 = 1571 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1571 : v3_fast (totient 1571) 100 = v3_phi_list.getD 1571 0 := by
  rw [tot_1571]
  rfl

theorem tot_1572 : totient 1572 = 520 := by
  have heq : (2^2 * (3 * (131)) : ℕ) = 1572 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_131]
  try omega

theorem v3_phi_1572 : v3_fast (totient 1572) 100 = v3_phi_list.getD 1572 0 := by
  rw [tot_1572]
  rfl

theorem tot_1573 : totient 1573 = 1320 := by
  have heq : (11^2 * (13) : ℕ) = 1573 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_13]
  try omega

theorem v3_phi_1573 : v3_fast (totient 1573) 100 = v3_phi_list.getD 1573 0 := by
  rw [tot_1573]
  rfl

theorem tot_1574 : totient 1574 = 786 := by
  have heq : (2 * (787) : ℕ) = 1574 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_787 : totient 787 = 787 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_787]
  try omega

theorem v3_phi_1574 : v3_fast (totient 1574) 100 = v3_phi_list.getD 1574 0 := by
  rw [tot_1574]
  rfl

theorem tot_1575 : totient 1575 = 720 := by
  have heq : (3^2 * (5^2 * (7)) : ℕ) = 1575 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_1575 : v3_fast (totient 1575) 100 = v3_phi_list.getD 1575 0 := by
  rw [tot_1575]
  rfl

theorem tot_1576 : totient 1576 = 784 := by
  have heq : (2^3 * (197) : ℕ) = 1576 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_197]
  try omega

theorem v3_phi_1576 : v3_fast (totient 1576) 100 = v3_phi_list.getD 1576 0 := by
  rw [tot_1576]
  rfl

theorem tot_1577 : totient 1577 = 1476 := by
  have heq : (19 * (83) : ℕ) = 1577 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_83]
  try omega

theorem v3_phi_1577 : v3_fast (totient 1577) 100 = v3_phi_list.getD 1577 0 := by
  rw [tot_1577]
  rfl

theorem tot_1578 : totient 1578 = 524 := by
  have heq : (2 * (3 * (263)) : ℕ) = 1578 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_263 : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_263]
  try omega

theorem v3_phi_1578 : v3_fast (totient 1578) 100 = v3_phi_list.getD 1578 0 := by
  rw [tot_1578]
  rfl

theorem tot_1579 : totient 1579 = 1578 := by
  have h : totient 1579 = 1579 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1579 : v3_fast (totient 1579) 100 = v3_phi_list.getD 1579 0 := by
  rw [tot_1579]
  rfl

theorem tot_1580 : totient 1580 = 624 := by
  have heq : (2^2 * (5 * (79)) : ℕ) = 1580 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_79]
  try omega

theorem v3_phi_1580 : v3_fast (totient 1580) 100 = v3_phi_list.getD 1580 0 := by
  rw [tot_1580]
  rfl

theorem tot_1581 : totient 1581 = 960 := by
  have heq : (3 * (17 * (31)) : ℕ) = 1581 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17, hp_31]
  try omega

theorem v3_phi_1581 : v3_fast (totient 1581) 100 = v3_phi_list.getD 1581 0 := by
  rw [tot_1581]
  rfl

theorem tot_1582 : totient 1582 = 672 := by
  have heq : (2 * (7 * (113)) : ℕ) = 1582 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_113]
  try omega

theorem v3_phi_1582 : v3_fast (totient 1582) 100 = v3_phi_list.getD 1582 0 := by
  rw [tot_1582]
  rfl

theorem tot_1583 : totient 1583 = 1582 := by
  have h : totient 1583 = 1583 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1583 : v3_fast (totient 1583) 100 = v3_phi_list.getD 1583 0 := by
  rw [tot_1583]
  rfl

theorem tot_1584 : totient 1584 = 480 := by
  have heq : (2^4 * (3^2 * (11)) : ℕ) = 1584 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_1584 : v3_fast (totient 1584) 100 = v3_phi_list.getD 1584 0 := by
  rw [tot_1584]
  rfl

theorem tot_1585 : totient 1585 = 1264 := by
  have heq : (5 * (317) : ℕ) = 1585 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_317 : totient 317 = 317 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_317]
  try omega

theorem v3_phi_1585 : v3_fast (totient 1585) 100 = v3_phi_list.getD 1585 0 := by
  rw [tot_1585]
  rfl

theorem tot_1586 : totient 1586 = 720 := by
  have heq : (2 * (13 * (61)) : ℕ) = 1586 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_61]
  try omega

theorem v3_phi_1586 : v3_fast (totient 1586) 100 = v3_phi_list.getD 1586 0 := by
  rw [tot_1586]
  rfl

theorem tot_1587 : totient 1587 = 1012 := by
  have heq : (3 * (23^2) : ℕ) = 1587 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient (23^2) = 23^1 * (23 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_23]
  try omega

theorem v3_phi_1587 : v3_fast (totient 1587) 100 = v3_phi_list.getD 1587 0 := by
  rw [tot_1587]
  rfl

theorem tot_1588 : totient 1588 = 792 := by
  have heq : (2^2 * (397) : ℕ) = 1588 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_397 : totient 397 = 397 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_397]
  try omega

theorem v3_phi_1588 : v3_fast (totient 1588) 100 = v3_phi_list.getD 1588 0 := by
  rw [tot_1588]
  rfl

theorem tot_1589 : totient 1589 = 1356 := by
  have heq : (7 * (227) : ℕ) = 1589 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_227]
  try omega

theorem v3_phi_1589 : v3_fast (totient 1589) 100 = v3_phi_list.getD 1589 0 := by
  rw [tot_1589]
  rfl

theorem tot_1590 : totient 1590 = 416 := by
  have heq : (2 * (3 * (5 * (53))) : ℕ) = 1590 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_53]
  try omega

theorem v3_phi_1590 : v3_fast (totient 1590) 100 = v3_phi_list.getD 1590 0 := by
  rw [tot_1590]
  rfl

theorem tot_1591 : totient 1591 = 1512 := by
  have heq : (37 * (43) : ℕ) = 1591 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_37, hp_43]
  try omega

theorem v3_phi_1591 : v3_fast (totient 1591) 100 = v3_phi_list.getD 1591 0 := by
  rw [tot_1591]
  rfl

theorem tot_1592 : totient 1592 = 792 := by
  have heq : (2^3 * (199) : ℕ) = 1592 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_199]
  try omega

theorem v3_phi_1592 : v3_fast (totient 1592) 100 = v3_phi_list.getD 1592 0 := by
  rw [tot_1592]
  rfl

theorem tot_1593 : totient 1593 = 1044 := by
  have heq : (3^3 * (59) : ℕ) = 1593 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_59]
  try omega

theorem v3_phi_1593 : v3_fast (totient 1593) 100 = v3_phi_list.getD 1593 0 := by
  rw [tot_1593]
  rfl

theorem tot_1594 : totient 1594 = 796 := by
  have heq : (2 * (797) : ℕ) = 1594 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_797 : totient 797 = 797 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_797]
  try omega

theorem v3_phi_1594 : v3_fast (totient 1594) 100 = v3_phi_list.getD 1594 0 := by
  rw [tot_1594]
  rfl

theorem tot_1595 : totient 1595 = 1120 := by
  have heq : (5 * (11 * (29)) : ℕ) = 1595 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_29]
  try omega

theorem v3_phi_1595 : v3_fast (totient 1595) 100 = v3_phi_list.getD 1595 0 := by
  rw [tot_1595]
  rfl

theorem tot_1596 : totient 1596 = 432 := by
  have heq : (2^2 * (3 * (7 * (19))) : ℕ) = 1596 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_19]
  try omega

theorem v3_phi_1596 : v3_fast (totient 1596) 100 = v3_phi_list.getD 1596 0 := by
  rw [tot_1596]
  rfl

theorem tot_1597 : totient 1597 = 1596 := by
  have h : totient 1597 = 1597 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1597 : v3_fast (totient 1597) 100 = v3_phi_list.getD 1597 0 := by
  rw [tot_1597]
  rfl

theorem tot_1598 : totient 1598 = 736 := by
  have heq : (2 * (17 * (47)) : ℕ) = 1598 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_47]
  try omega

theorem v3_phi_1598 : v3_fast (totient 1598) 100 = v3_phi_list.getD 1598 0 := by
  rw [tot_1598]
  rfl

theorem tot_1599 : totient 1599 = 960 := by
  have heq : (3 * (13 * (41)) : ℕ) = 1599 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_41]
  try omega

theorem v3_phi_1599 : v3_fast (totient 1599) 100 = v3_phi_list.getD 1599 0 := by
  rw [tot_1599]
  rfl

theorem tot_1600 : totient 1600 = 640 := by
  have heq : (2^6 * (5^2) : ℕ) = 1600 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_1600 : v3_fast (totient 1600) 100 = v3_phi_list.getD 1600 0 := by
  rw [tot_1600]
  rfl

theorem tot_1601 : totient 1601 = 1600 := by
  have h : totient 1601 = 1601 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1601 : v3_fast (totient 1601) 100 = v3_phi_list.getD 1601 0 := by
  rw [tot_1601]
  rfl

theorem tot_1602 : totient 1602 = 528 := by
  have heq : (2 * (3^2 * (89)) : ℕ) = 1602 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_89]
  try omega

theorem v3_phi_1602 : v3_fast (totient 1602) 100 = v3_phi_list.getD 1602 0 := by
  rw [tot_1602]
  rfl

theorem tot_1603 : totient 1603 = 1368 := by
  have heq : (7 * (229) : ℕ) = 1603 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_229]
  try omega

theorem v3_phi_1603 : v3_fast (totient 1603) 100 = v3_phi_list.getD 1603 0 := by
  rw [tot_1603]
  rfl

theorem tot_1604 : totient 1604 = 800 := by
  have heq : (2^2 * (401) : ℕ) = 1604 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_401 : totient 401 = 401 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_401]
  try omega

theorem v3_phi_1604 : v3_fast (totient 1604) 100 = v3_phi_list.getD 1604 0 := by
  rw [tot_1604]
  rfl

theorem tot_1605 : totient 1605 = 848 := by
  have heq : (3 * (5 * (107)) : ℕ) = 1605 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_107]
  try omega

theorem v3_phi_1605 : v3_fast (totient 1605) 100 = v3_phi_list.getD 1605 0 := by
  rw [tot_1605]
  rfl

theorem tot_1606 : totient 1606 = 720 := by
  have heq : (2 * (11 * (73)) : ℕ) = 1606 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_73]
  try omega

theorem v3_phi_1606 : v3_fast (totient 1606) 100 = v3_phi_list.getD 1606 0 := by
  rw [tot_1606]
  rfl

theorem tot_1607 : totient 1607 = 1606 := by
  have h : totient 1607 = 1607 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1607 : v3_fast (totient 1607) 100 = v3_phi_list.getD 1607 0 := by
  rw [tot_1607]
  rfl

theorem tot_1608 : totient 1608 = 528 := by
  have heq : (2^3 * (3 * (67)) : ℕ) = 1608 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_67]
  try omega

theorem v3_phi_1608 : v3_fast (totient 1608) 100 = v3_phi_list.getD 1608 0 := by
  rw [tot_1608]
  rfl

theorem tot_1609 : totient 1609 = 1608 := by
  have h : totient 1609 = 1609 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1609 : v3_fast (totient 1609) 100 = v3_phi_list.getD 1609 0 := by
  rw [tot_1609]
  rfl

theorem tot_1610 : totient 1610 = 528 := by
  have heq : (2 * (5 * (7 * (23))) : ℕ) = 1610 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_23]
  try omega

theorem v3_phi_1610 : v3_fast (totient 1610) 100 = v3_phi_list.getD 1610 0 := by
  rw [tot_1610]
  rfl

theorem tot_1611 : totient 1611 = 1068 := by
  have heq : (3^2 * (179) : ℕ) = 1611 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_179]
  try omega

theorem v3_phi_1611 : v3_fast (totient 1611) 100 = v3_phi_list.getD 1611 0 := by
  rw [tot_1611]
  rfl

theorem tot_1612 : totient 1612 = 720 := by
  have heq : (2^2 * (13 * (31)) : ℕ) = 1612 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_31]
  try omega

theorem v3_phi_1612 : v3_fast (totient 1612) 100 = v3_phi_list.getD 1612 0 := by
  rw [tot_1612]
  rfl

theorem tot_1613 : totient 1613 = 1612 := by
  have h : totient 1613 = 1613 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1613 : v3_fast (totient 1613) 100 = v3_phi_list.getD 1613 0 := by
  rw [tot_1613]
  rfl

theorem tot_1614 : totient 1614 = 536 := by
  have heq : (2 * (3 * (269)) : ℕ) = 1614 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_269 : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_269]
  try omega

theorem v3_phi_1614 : v3_fast (totient 1614) 100 = v3_phi_list.getD 1614 0 := by
  rw [tot_1614]
  rfl

theorem tot_1615 : totient 1615 = 1152 := by
  have heq : (5 * (17 * (19)) : ℕ) = 1615 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_17, hp_19]
  try omega

theorem v3_phi_1615 : v3_fast (totient 1615) 100 = v3_phi_list.getD 1615 0 := by
  rw [tot_1615]
  rfl

theorem tot_1616 : totient 1616 = 800 := by
  have heq : (2^4 * (101) : ℕ) = 1616 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_101]
  try omega

theorem v3_phi_1616 : v3_fast (totient 1616) 100 = v3_phi_list.getD 1616 0 := by
  rw [tot_1616]
  rfl

theorem tot_1617 : totient 1617 = 840 := by
  have heq : (3 * (7^2 * (11)) : ℕ) = 1617 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_11]
  try omega

theorem v3_phi_1617 : v3_fast (totient 1617) 100 = v3_phi_list.getD 1617 0 := by
  rw [tot_1617]
  rfl

theorem tot_1618 : totient 1618 = 808 := by
  have heq : (2 * (809) : ℕ) = 1618 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_809 : totient 809 = 809 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_809]
  try omega

theorem v3_phi_1618 : v3_fast (totient 1618) 100 = v3_phi_list.getD 1618 0 := by
  rw [tot_1618]
  rfl

theorem tot_1619 : totient 1619 = 1618 := by
  have h : totient 1619 = 1619 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1619 : v3_fast (totient 1619) 100 = v3_phi_list.getD 1619 0 := by
  rw [tot_1619]
  rfl

theorem tot_1620 : totient 1620 = 432 := by
  have heq : (2^2 * (3^4 * (5)) : ℕ) = 1620 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_1620 : v3_fast (totient 1620) 100 = v3_phi_list.getD 1620 0 := by
  rw [tot_1620]
  rfl

theorem tot_1621 : totient 1621 = 1620 := by
  have h : totient 1621 = 1621 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1621 : v3_fast (totient 1621) 100 = v3_phi_list.getD 1621 0 := by
  rw [tot_1621]
  rfl

theorem tot_1622 : totient 1622 = 810 := by
  have heq : (2 * (811) : ℕ) = 1622 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_811 : totient 811 = 811 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_811]
  try omega

theorem v3_phi_1622 : v3_fast (totient 1622) 100 = v3_phi_list.getD 1622 0 := by
  rw [tot_1622]
  rfl

theorem tot_1623 : totient 1623 = 1080 := by
  have heq : (3 * (541) : ℕ) = 1623 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_541 : totient 541 = 541 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_541]
  try omega

theorem v3_phi_1623 : v3_fast (totient 1623) 100 = v3_phi_list.getD 1623 0 := by
  rw [tot_1623]
  rfl

theorem tot_1624 : totient 1624 = 672 := by
  have heq : (2^3 * (7 * (29)) : ℕ) = 1624 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_29]
  try omega

theorem v3_phi_1624 : v3_fast (totient 1624) 100 = v3_phi_list.getD 1624 0 := by
  rw [tot_1624]
  rfl

theorem tot_1625 : totient 1625 = 1200 := by
  have heq : (5^3 * (13) : ℕ) = 1625 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13]
  try omega

theorem v3_phi_1625 : v3_fast (totient 1625) 100 = v3_phi_list.getD 1625 0 := by
  rw [tot_1625]
  rfl

theorem tot_1626 : totient 1626 = 540 := by
  have heq : (2 * (3 * (271)) : ℕ) = 1626 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_271 : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_271]
  try omega

theorem v3_phi_1626 : v3_fast (totient 1626) 100 = v3_phi_list.getD 1626 0 := by
  rw [tot_1626]
  rfl

theorem tot_1627 : totient 1627 = 1626 := by
  have h : totient 1627 = 1627 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1627 : v3_fast (totient 1627) 100 = v3_phi_list.getD 1627 0 := by
  rw [tot_1627]
  rfl

theorem tot_1628 : totient 1628 = 720 := by
  have heq : (2^2 * (11 * (37)) : ℕ) = 1628 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_37]
  try omega

theorem v3_phi_1628 : v3_fast (totient 1628) 100 = v3_phi_list.getD 1628 0 := by
  rw [tot_1628]
  rfl

theorem tot_1629 : totient 1629 = 1080 := by
  have heq : (3^2 * (181) : ℕ) = 1629 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_181]
  try omega

theorem v3_phi_1629 : v3_fast (totient 1629) 100 = v3_phi_list.getD 1629 0 := by
  rw [tot_1629]
  rfl

theorem tot_1630 : totient 1630 = 648 := by
  have heq : (2 * (5 * (163)) : ℕ) = 1630 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_163]
  try omega

theorem v3_phi_1630 : v3_fast (totient 1630) 100 = v3_phi_list.getD 1630 0 := by
  rw [tot_1630]
  rfl

theorem tot_1631 : totient 1631 = 1392 := by
  have heq : (7 * (233) : ℕ) = 1631 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_233]
  try omega

theorem v3_phi_1631 : v3_fast (totient 1631) 100 = v3_phi_list.getD 1631 0 := by
  rw [tot_1631]
  rfl

theorem tot_1632 : totient 1632 = 512 := by
  have heq : (2^5 * (3 * (17)) : ℕ) = 1632 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17]
  try omega

theorem v3_phi_1632 : v3_fast (totient 1632) 100 = v3_phi_list.getD 1632 0 := by
  rw [tot_1632]
  rfl

theorem tot_1633 : totient 1633 = 1540 := by
  have heq : (23 * (71) : ℕ) = 1633 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_71]
  try omega

theorem v3_phi_1633 : v3_fast (totient 1633) 100 = v3_phi_list.getD 1633 0 := by
  rw [tot_1633]
  rfl

theorem tot_1634 : totient 1634 = 756 := by
  have heq : (2 * (19 * (43)) : ℕ) = 1634 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_43]
  try omega

theorem v3_phi_1634 : v3_fast (totient 1634) 100 = v3_phi_list.getD 1634 0 := by
  rw [tot_1634]
  rfl

theorem tot_1635 : totient 1635 = 864 := by
  have heq : (3 * (5 * (109)) : ℕ) = 1635 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_109]
  try omega

theorem v3_phi_1635 : v3_fast (totient 1635) 100 = v3_phi_list.getD 1635 0 := by
  rw [tot_1635]
  rfl

theorem tot_1636 : totient 1636 = 816 := by
  have heq : (2^2 * (409) : ℕ) = 1636 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_409 : totient 409 = 409 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_409]
  try omega

theorem v3_phi_1636 : v3_fast (totient 1636) 100 = v3_phi_list.getD 1636 0 := by
  rw [tot_1636]
  rfl

theorem tot_1637 : totient 1637 = 1636 := by
  have h : totient 1637 = 1637 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1637 : v3_fast (totient 1637) 100 = v3_phi_list.getD 1637 0 := by
  rw [tot_1637]
  rfl

theorem tot_1638 : totient 1638 = 432 := by
  have heq : (2 * (3^2 * (7 * (13))) : ℕ) = 1638 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_13]
  try omega

theorem v3_phi_1638 : v3_fast (totient 1638) 100 = v3_phi_list.getD 1638 0 := by
  rw [tot_1638]
  rfl

theorem tot_1639 : totient 1639 = 1480 := by
  have heq : (11 * (149) : ℕ) = 1639 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_149]
  try omega

theorem v3_phi_1639 : v3_fast (totient 1639) 100 = v3_phi_list.getD 1639 0 := by
  rw [tot_1639]
  rfl

theorem tot_1640 : totient 1640 = 640 := by
  have heq : (2^3 * (5 * (41)) : ℕ) = 1640 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_41]
  try omega

theorem v3_phi_1640 : v3_fast (totient 1640) 100 = v3_phi_list.getD 1640 0 := by
  rw [tot_1640]
  rfl

theorem tot_1641 : totient 1641 = 1092 := by
  have heq : (3 * (547) : ℕ) = 1641 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_547 : totient 547 = 547 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_547]
  try omega

theorem v3_phi_1641 : v3_fast (totient 1641) 100 = v3_phi_list.getD 1641 0 := by
  rw [tot_1641]
  rfl

theorem tot_1642 : totient 1642 = 820 := by
  have heq : (2 * (821) : ℕ) = 1642 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_821 : totient 821 = 821 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_821]
  try omega

theorem v3_phi_1642 : v3_fast (totient 1642) 100 = v3_phi_list.getD 1642 0 := by
  rw [tot_1642]
  rfl

theorem tot_1643 : totient 1643 = 1560 := by
  have heq : (31 * (53) : ℕ) = 1643 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_31, hp_53]
  try omega

theorem v3_phi_1643 : v3_fast (totient 1643) 100 = v3_phi_list.getD 1643 0 := by
  rw [tot_1643]
  rfl

theorem tot_1644 : totient 1644 = 544 := by
  have heq : (2^2 * (3 * (137)) : ℕ) = 1644 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_137]
  try omega

theorem v3_phi_1644 : v3_fast (totient 1644) 100 = v3_phi_list.getD 1644 0 := by
  rw [tot_1644]
  rfl

theorem tot_1645 : totient 1645 = 1104 := by
  have heq : (5 * (7 * (47)) : ℕ) = 1645 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_47]
  try omega

theorem v3_phi_1645 : v3_fast (totient 1645) 100 = v3_phi_list.getD 1645 0 := by
  rw [tot_1645]
  rfl

theorem tot_1646 : totient 1646 = 822 := by
  have heq : (2 * (823) : ℕ) = 1646 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_823 : totient 823 = 823 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_823]
  try omega

theorem v3_phi_1646 : v3_fast (totient 1646) 100 = v3_phi_list.getD 1646 0 := by
  rw [tot_1646]
  rfl

theorem tot_1647 : totient 1647 = 1080 := by
  have heq : (3^3 * (61) : ℕ) = 1647 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_61]
  try omega

theorem v3_phi_1647 : v3_fast (totient 1647) 100 = v3_phi_list.getD 1647 0 := by
  rw [tot_1647]
  rfl

theorem tot_1648 : totient 1648 = 816 := by
  have heq : (2^4 * (103) : ℕ) = 1648 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_103]
  try omega

theorem v3_phi_1648 : v3_fast (totient 1648) 100 = v3_phi_list.getD 1648 0 := by
  rw [tot_1648]
  rfl

theorem tot_1649 : totient 1649 = 1536 := by
  have heq : (17 * (97) : ℕ) = 1649 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_97]
  try omega

theorem v3_phi_1649 : v3_fast (totient 1649) 100 = v3_phi_list.getD 1649 0 := by
  rw [tot_1649]
  rfl

theorem tot_1650 : totient 1650 = 400 := by
  have heq : (2 * (3 * (5^2 * (11))) : ℕ) = 1650 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_11]
  try omega

theorem v3_phi_1650 : v3_fast (totient 1650) 100 = v3_phi_list.getD 1650 0 := by
  rw [tot_1650]
  rfl

theorem tot_1651 : totient 1651 = 1512 := by
  have heq : (13 * (127) : ℕ) = 1651 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_127]
  try omega

theorem v3_phi_1651 : v3_fast (totient 1651) 100 = v3_phi_list.getD 1651 0 := by
  rw [tot_1651]
  rfl

theorem tot_1652 : totient 1652 = 696 := by
  have heq : (2^2 * (7 * (59)) : ℕ) = 1652 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_59]
  try omega

theorem v3_phi_1652 : v3_fast (totient 1652) 100 = v3_phi_list.getD 1652 0 := by
  rw [tot_1652]
  rfl

theorem tot_1653 : totient 1653 = 1008 := by
  have heq : (3 * (19 * (29)) : ℕ) = 1653 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19, hp_29]
  try omega

theorem v3_phi_1653 : v3_fast (totient 1653) 100 = v3_phi_list.getD 1653 0 := by
  rw [tot_1653]
  rfl

theorem tot_1654 : totient 1654 = 826 := by
  have heq : (2 * (827) : ℕ) = 1654 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_827 : totient 827 = 827 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_827]
  try omega

theorem v3_phi_1654 : v3_fast (totient 1654) 100 = v3_phi_list.getD 1654 0 := by
  rw [tot_1654]
  rfl

theorem tot_1655 : totient 1655 = 1320 := by
  have heq : (5 * (331) : ℕ) = 1655 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_331 : totient 331 = 331 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_331]
  try omega

theorem v3_phi_1655 : v3_fast (totient 1655) 100 = v3_phi_list.getD 1655 0 := by
  rw [tot_1655]
  rfl

theorem tot_1656 : totient 1656 = 528 := by
  have heq : (2^3 * (3^2 * (23)) : ℕ) = 1656 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23]
  try omega

theorem v3_phi_1656 : v3_fast (totient 1656) 100 = v3_phi_list.getD 1656 0 := by
  rw [tot_1656]
  rfl

theorem tot_1657 : totient 1657 = 1656 := by
  have h : totient 1657 = 1657 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1657 : v3_fast (totient 1657) 100 = v3_phi_list.getD 1657 0 := by
  rw [tot_1657]
  rfl

theorem tot_1658 : totient 1658 = 828 := by
  have heq : (2 * (829) : ℕ) = 1658 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_829 : totient 829 = 829 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_829]
  try omega

theorem v3_phi_1658 : v3_fast (totient 1658) 100 = v3_phi_list.getD 1658 0 := by
  rw [tot_1658]
  rfl

theorem tot_1659 : totient 1659 = 936 := by
  have heq : (3 * (7 * (79)) : ℕ) = 1659 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_79]
  try omega

theorem v3_phi_1659 : v3_fast (totient 1659) 100 = v3_phi_list.getD 1659 0 := by
  rw [tot_1659]
  rfl

theorem tot_1660 : totient 1660 = 656 := by
  have heq : (2^2 * (5 * (83)) : ℕ) = 1660 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_83]
  try omega

theorem v3_phi_1660 : v3_fast (totient 1660) 100 = v3_phi_list.getD 1660 0 := by
  rw [tot_1660]
  rfl

theorem tot_1661 : totient 1661 = 1500 := by
  have heq : (11 * (151) : ℕ) = 1661 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_151]
  try omega

theorem v3_phi_1661 : v3_fast (totient 1661) 100 = v3_phi_list.getD 1661 0 := by
  rw [tot_1661]
  rfl

theorem tot_1662 : totient 1662 = 552 := by
  have heq : (2 * (3 * (277)) : ℕ) = 1662 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_277 : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_277]
  try omega

theorem v3_phi_1662 : v3_fast (totient 1662) 100 = v3_phi_list.getD 1662 0 := by
  rw [tot_1662]
  rfl

theorem tot_1663 : totient 1663 = 1662 := by
  have h : totient 1663 = 1663 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1663 : v3_fast (totient 1663) 100 = v3_phi_list.getD 1663 0 := by
  rw [tot_1663]
  rfl

theorem tot_1664 : totient 1664 = 768 := by
  have heq : (2^7 * (13) : ℕ) = 1664 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13]
  try omega

theorem v3_phi_1664 : v3_fast (totient 1664) 100 = v3_phi_list.getD 1664 0 := by
  rw [tot_1664]
  rfl

theorem tot_1665 : totient 1665 = 864 := by
  have heq : (3^2 * (5 * (37)) : ℕ) = 1665 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_37]
  try omega

theorem v3_phi_1665 : v3_fast (totient 1665) 100 = v3_phi_list.getD 1665 0 := by
  rw [tot_1665]
  rfl

theorem tot_1666 : totient 1666 = 672 := by
  have heq : (2 * (7^2 * (17)) : ℕ) = 1666 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_17]
  try omega

theorem v3_phi_1666 : v3_fast (totient 1666) 100 = v3_phi_list.getD 1666 0 := by
  rw [tot_1666]
  rfl

theorem tot_1667 : totient 1667 = 1666 := by
  have h : totient 1667 = 1667 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1667 : v3_fast (totient 1667) 100 = v3_phi_list.getD 1667 0 := by
  rw [tot_1667]
  rfl

theorem tot_1668 : totient 1668 = 552 := by
  have heq : (2^2 * (3 * (139)) : ℕ) = 1668 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_139]
  try omega

theorem v3_phi_1668 : v3_fast (totient 1668) 100 = v3_phi_list.getD 1668 0 := by
  rw [tot_1668]
  rfl

theorem tot_1669 : totient 1669 = 1668 := by
  have h : totient 1669 = 1669 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1669 : v3_fast (totient 1669) 100 = v3_phi_list.getD 1669 0 := by
  rw [tot_1669]
  rfl

theorem tot_1670 : totient 1670 = 664 := by
  have heq : (2 * (5 * (167)) : ℕ) = 1670 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_167]
  try omega

theorem v3_phi_1670 : v3_fast (totient 1670) 100 = v3_phi_list.getD 1670 0 := by
  rw [tot_1670]
  rfl

theorem tot_1671 : totient 1671 = 1112 := by
  have heq : (3 * (557) : ℕ) = 1671 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_557 : totient 557 = 557 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_557]
  try omega

theorem v3_phi_1671 : v3_fast (totient 1671) 100 = v3_phi_list.getD 1671 0 := by
  rw [tot_1671]
  rfl

theorem tot_1672 : totient 1672 = 720 := by
  have heq : (2^3 * (11 * (19)) : ℕ) = 1672 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_19]
  try omega

theorem v3_phi_1672 : v3_fast (totient 1672) 100 = v3_phi_list.getD 1672 0 := by
  rw [tot_1672]
  rfl

theorem tot_1673 : totient 1673 = 1428 := by
  have heq : (7 * (239) : ℕ) = 1673 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_239]
  try omega

theorem v3_phi_1673 : v3_fast (totient 1673) 100 = v3_phi_list.getD 1673 0 := by
  rw [tot_1673]
  rfl

theorem tot_1674 : totient 1674 = 540 := by
  have heq : (2 * (3^3 * (31)) : ℕ) = 1674 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31]
  try omega

theorem v3_phi_1674 : v3_fast (totient 1674) 100 = v3_phi_list.getD 1674 0 := by
  rw [tot_1674]
  rfl

theorem tot_1675 : totient 1675 = 1320 := by
  have heq : (5^2 * (67) : ℕ) = 1675 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_67]
  try omega

theorem v3_phi_1675 : v3_fast (totient 1675) 100 = v3_phi_list.getD 1675 0 := by
  rw [tot_1675]
  rfl

theorem tot_1676 : totient 1676 = 836 := by
  have heq : (2^2 * (419) : ℕ) = 1676 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_419 : totient 419 = 419 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_419]
  try omega

theorem v3_phi_1676 : v3_fast (totient 1676) 100 = v3_phi_list.getD 1676 0 := by
  rw [tot_1676]
  rfl

theorem tot_1677 : totient 1677 = 1008 := by
  have heq : (3 * (13 * (43)) : ℕ) = 1677 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_43]
  try omega

theorem v3_phi_1677 : v3_fast (totient 1677) 100 = v3_phi_list.getD 1677 0 := by
  rw [tot_1677]
  rfl

theorem tot_1678 : totient 1678 = 838 := by
  have heq : (2 * (839) : ℕ) = 1678 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_839 : totient 839 = 839 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_839]
  try omega

theorem v3_phi_1678 : v3_fast (totient 1678) 100 = v3_phi_list.getD 1678 0 := by
  rw [tot_1678]
  rfl

theorem tot_1679 : totient 1679 = 1584 := by
  have heq : (23 * (73) : ℕ) = 1679 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_73]
  try omega

theorem v3_phi_1679 : v3_fast (totient 1679) 100 = v3_phi_list.getD 1679 0 := by
  rw [tot_1679]
  rfl

theorem tot_1680 : totient 1680 = 384 := by
  have heq : (2^4 * (3 * (5 * (7))) : ℕ) = 1680 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_1680 : v3_fast (totient 1680) 100 = v3_phi_list.getD 1680 0 := by
  rw [tot_1680]
  rfl

theorem tot_1681 : totient 1681 = 1640 := by
  have h : totient (41^2) = 41^1 * (41 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (41^2 : ℕ) = 1681 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_1681 : v3_fast (totient 1681) 100 = v3_phi_list.getD 1681 0 := by
  rw [tot_1681]
  rfl

theorem tot_1682 : totient 1682 = 812 := by
  have heq : (2 * (29^2) : ℕ) = 1682 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_29 : totient (29^2) = 29^1 * (29 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_29]
  try omega

theorem v3_phi_1682 : v3_fast (totient 1682) 100 = v3_phi_list.getD 1682 0 := by
  rw [tot_1682]
  rfl

theorem tot_1683 : totient 1683 = 960 := by
  have heq : (3^2 * (11 * (17)) : ℕ) = 1683 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_17]
  try omega

theorem v3_phi_1683 : v3_fast (totient 1683) 100 = v3_phi_list.getD 1683 0 := by
  rw [tot_1683]
  rfl

theorem tot_1684 : totient 1684 = 840 := by
  have heq : (2^2 * (421) : ℕ) = 1684 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_421 : totient 421 = 421 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_421]
  try omega

theorem v3_phi_1684 : v3_fast (totient 1684) 100 = v3_phi_list.getD 1684 0 := by
  rw [tot_1684]
  rfl

theorem tot_1685 : totient 1685 = 1344 := by
  have heq : (5 * (337) : ℕ) = 1685 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_337 : totient 337 = 337 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_337]
  try omega

theorem v3_phi_1685 : v3_fast (totient 1685) 100 = v3_phi_list.getD 1685 0 := by
  rw [tot_1685]
  rfl

theorem tot_1686 : totient 1686 = 560 := by
  have heq : (2 * (3 * (281)) : ℕ) = 1686 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_281 : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_281]
  try omega

theorem v3_phi_1686 : v3_fast (totient 1686) 100 = v3_phi_list.getD 1686 0 := by
  rw [tot_1686]
  rfl

theorem tot_1687 : totient 1687 = 1440 := by
  have heq : (7 * (241) : ℕ) = 1687 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_241]
  try omega

theorem v3_phi_1687 : v3_fast (totient 1687) 100 = v3_phi_list.getD 1687 0 := by
  rw [tot_1687]
  rfl

theorem tot_1688 : totient 1688 = 840 := by
  have heq : (2^3 * (211) : ℕ) = 1688 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_211]
  try omega

theorem v3_phi_1688 : v3_fast (totient 1688) 100 = v3_phi_list.getD 1688 0 := by
  rw [tot_1688]
  rfl

theorem tot_1689 : totient 1689 = 1124 := by
  have heq : (3 * (563) : ℕ) = 1689 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_563 : totient 563 = 563 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_563]
  try omega

theorem v3_phi_1689 : v3_fast (totient 1689) 100 = v3_phi_list.getD 1689 0 := by
  rw [tot_1689]
  rfl

theorem tot_1690 : totient 1690 = 624 := by
  have heq : (2 * (5 * (13^2)) : ℕ) = 1690 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5, hp_13]
  try omega

theorem v3_phi_1690 : v3_fast (totient 1690) 100 = v3_phi_list.getD 1690 0 := by
  rw [tot_1690]
  rfl

theorem tot_1691 : totient 1691 = 1584 := by
  have heq : (19 * (89) : ℕ) = 1691 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_89]
  try omega

theorem v3_phi_1691 : v3_fast (totient 1691) 100 = v3_phi_list.getD 1691 0 := by
  rw [tot_1691]
  rfl

theorem tot_1692 : totient 1692 = 552 := by
  have heq : (2^2 * (3^2 * (47)) : ℕ) = 1692 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_47]
  try omega

theorem v3_phi_1692 : v3_fast (totient 1692) 100 = v3_phi_list.getD 1692 0 := by
  rw [tot_1692]
  rfl

theorem tot_1693 : totient 1693 = 1692 := by
  have h : totient 1693 = 1693 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1693 : v3_fast (totient 1693) 100 = v3_phi_list.getD 1693 0 := by
  rw [tot_1693]
  rfl

theorem tot_1694 : totient 1694 = 660 := by
  have heq : (2 * (7 * (11^2)) : ℕ) = 1694 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7, hp_11]
  try omega

theorem v3_phi_1694 : v3_fast (totient 1694) 100 = v3_phi_list.getD 1694 0 := by
  rw [tot_1694]
  rfl

theorem tot_1695 : totient 1695 = 896 := by
  have heq : (3 * (5 * (113)) : ℕ) = 1695 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_113]
  try omega

theorem v3_phi_1695 : v3_fast (totient 1695) 100 = v3_phi_list.getD 1695 0 := by
  rw [tot_1695]
  rfl

theorem tot_1696 : totient 1696 = 832 := by
  have heq : (2^5 * (53) : ℕ) = 1696 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_53]
  try omega

theorem v3_phi_1696 : v3_fast (totient 1696) 100 = v3_phi_list.getD 1696 0 := by
  rw [tot_1696]
  rfl

theorem tot_1697 : totient 1697 = 1696 := by
  have h : totient 1697 = 1697 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1697 : v3_fast (totient 1697) 100 = v3_phi_list.getD 1697 0 := by
  rw [tot_1697]
  rfl

theorem tot_1698 : totient 1698 = 564 := by
  have heq : (2 * (3 * (283)) : ℕ) = 1698 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_283 : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_283]
  try omega

theorem v3_phi_1698 : v3_fast (totient 1698) 100 = v3_phi_list.getD 1698 0 := by
  rw [tot_1698]
  rfl

theorem tot_1699 : totient 1699 = 1698 := by
  have h : totient 1699 = 1699 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1699 : v3_fast (totient 1699) 100 = v3_phi_list.getD 1699 0 := by
  rw [tot_1699]
  rfl

theorem tot_1700 : totient 1700 = 640 := by
  have heq : (2^2 * (5^2 * (17)) : ℕ) = 1700 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17]
  try omega

theorem v3_phi_1700 : v3_fast (totient 1700) 100 = v3_phi_list.getD 1700 0 := by
  rw [tot_1700]
  rfl

theorem tot_1701 : totient 1701 = 972 := by
  have heq : (3^5 * (7) : ℕ) = 1701 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^5) = 3^4 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7]
  try omega

theorem v3_phi_1701 : v3_fast (totient 1701) 100 = v3_phi_list.getD 1701 0 := by
  rw [tot_1701]
  rfl

theorem tot_1702 : totient 1702 = 792 := by
  have heq : (2 * (23 * (37)) : ℕ) = 1702 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23, hp_37]
  try omega

theorem v3_phi_1702 : v3_fast (totient 1702) 100 = v3_phi_list.getD 1702 0 := by
  rw [tot_1702]
  rfl

theorem tot_1703 : totient 1703 = 1560 := by
  have heq : (13 * (131) : ℕ) = 1703 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_131]
  try omega

theorem v3_phi_1703 : v3_fast (totient 1703) 100 = v3_phi_list.getD 1703 0 := by
  rw [tot_1703]
  rfl

theorem tot_1704 : totient 1704 = 560 := by
  have heq : (2^3 * (3 * (71)) : ℕ) = 1704 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_71]
  try omega

theorem v3_phi_1704 : v3_fast (totient 1704) 100 = v3_phi_list.getD 1704 0 := by
  rw [tot_1704]
  rfl

theorem tot_1705 : totient 1705 = 1200 := by
  have heq : (5 * (11 * (31)) : ℕ) = 1705 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_31]
  try omega

theorem v3_phi_1705 : v3_fast (totient 1705) 100 = v3_phi_list.getD 1705 0 := by
  rw [tot_1705]
  rfl

theorem tot_1706 : totient 1706 = 852 := by
  have heq : (2 * (853) : ℕ) = 1706 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_853 : totient 853 = 853 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_853]
  try omega

theorem v3_phi_1706 : v3_fast (totient 1706) 100 = v3_phi_list.getD 1706 0 := by
  rw [tot_1706]
  rfl

theorem tot_1707 : totient 1707 = 1136 := by
  have heq : (3 * (569) : ℕ) = 1707 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_569 : totient 569 = 569 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_569]
  try omega

theorem v3_phi_1707 : v3_fast (totient 1707) 100 = v3_phi_list.getD 1707 0 := by
  rw [tot_1707]
  rfl

theorem tot_1708 : totient 1708 = 720 := by
  have heq : (2^2 * (7 * (61)) : ℕ) = 1708 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_61]
  try omega

theorem v3_phi_1708 : v3_fast (totient 1708) 100 = v3_phi_list.getD 1708 0 := by
  rw [tot_1708]
  rfl

theorem tot_1709 : totient 1709 = 1708 := by
  have h : totient 1709 = 1709 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1709 : v3_fast (totient 1709) 100 = v3_phi_list.getD 1709 0 := by
  rw [tot_1709]
  rfl

theorem tot_1710 : totient 1710 = 432 := by
  have heq : (2 * (3^2 * (5 * (19))) : ℕ) = 1710 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_19]
  try omega

theorem v3_phi_1710 : v3_fast (totient 1710) 100 = v3_phi_list.getD 1710 0 := by
  rw [tot_1710]
  rfl

theorem tot_1711 : totient 1711 = 1624 := by
  have heq : (29 * (59) : ℕ) = 1711 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_59]
  try omega

theorem v3_phi_1711 : v3_fast (totient 1711) 100 = v3_phi_list.getD 1711 0 := by
  rw [tot_1711]
  rfl

theorem tot_1712 : totient 1712 = 848 := by
  have heq : (2^4 * (107) : ℕ) = 1712 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_107]
  try omega

theorem v3_phi_1712 : v3_fast (totient 1712) 100 = v3_phi_list.getD 1712 0 := by
  rw [tot_1712]
  rfl

theorem tot_1713 : totient 1713 = 1140 := by
  have heq : (3 * (571) : ℕ) = 1713 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_571 : totient 571 = 571 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_571]
  try omega

theorem v3_phi_1713 : v3_fast (totient 1713) 100 = v3_phi_list.getD 1713 0 := by
  rw [tot_1713]
  rfl

theorem tot_1714 : totient 1714 = 856 := by
  have heq : (2 * (857) : ℕ) = 1714 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_857 : totient 857 = 857 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_857]
  try omega

theorem v3_phi_1714 : v3_fast (totient 1714) 100 = v3_phi_list.getD 1714 0 := by
  rw [tot_1714]
  rfl

theorem tot_1715 : totient 1715 = 1176 := by
  have heq : (5 * (7^3) : ℕ) = 1715 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^3) = 7^2 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_7]
  try omega

theorem v3_phi_1715 : v3_fast (totient 1715) 100 = v3_phi_list.getD 1715 0 := by
  rw [tot_1715]
  rfl

theorem tot_1716 : totient 1716 = 480 := by
  have heq : (2^2 * (3 * (11 * (13))) : ℕ) = 1716 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11, hp_13]
  try omega

theorem v3_phi_1716 : v3_fast (totient 1716) 100 = v3_phi_list.getD 1716 0 := by
  rw [tot_1716]
  rfl

theorem tot_1717 : totient 1717 = 1600 := by
  have heq : (17 * (101) : ℕ) = 1717 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_101]
  try omega

theorem v3_phi_1717 : v3_fast (totient 1717) 100 = v3_phi_list.getD 1717 0 := by
  rw [tot_1717]
  rfl

theorem tot_1718 : totient 1718 = 858 := by
  have heq : (2 * (859) : ℕ) = 1718 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_859 : totient 859 = 859 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_859]
  try omega

theorem v3_phi_1718 : v3_fast (totient 1718) 100 = v3_phi_list.getD 1718 0 := by
  rw [tot_1718]
  rfl

theorem tot_1719 : totient 1719 = 1140 := by
  have heq : (3^2 * (191) : ℕ) = 1719 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_191]
  try omega

theorem v3_phi_1719 : v3_fast (totient 1719) 100 = v3_phi_list.getD 1719 0 := by
  rw [tot_1719]
  rfl

theorem tot_1720 : totient 1720 = 672 := by
  have heq : (2^3 * (5 * (43)) : ℕ) = 1720 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_43]
  try omega

theorem v3_phi_1720 : v3_fast (totient 1720) 100 = v3_phi_list.getD 1720 0 := by
  rw [tot_1720]
  rfl

theorem tot_1721 : totient 1721 = 1720 := by
  have h : totient 1721 = 1721 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1721 : v3_fast (totient 1721) 100 = v3_phi_list.getD 1721 0 := by
  rw [tot_1721]
  rfl

theorem tot_1722 : totient 1722 = 480 := by
  have heq : (2 * (3 * (7 * (41))) : ℕ) = 1722 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_41]
  try omega

theorem v3_phi_1722 : v3_fast (totient 1722) 100 = v3_phi_list.getD 1722 0 := by
  rw [tot_1722]
  rfl

theorem tot_1723 : totient 1723 = 1722 := by
  have h : totient 1723 = 1723 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1723 : v3_fast (totient 1723) 100 = v3_phi_list.getD 1723 0 := by
  rw [tot_1723]
  rfl

theorem tot_1724 : totient 1724 = 860 := by
  have heq : (2^2 * (431) : ℕ) = 1724 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_431 : totient 431 = 431 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_431]
  try omega

theorem v3_phi_1724 : v3_fast (totient 1724) 100 = v3_phi_list.getD 1724 0 := by
  rw [tot_1724]
  rfl

theorem tot_1725 : totient 1725 = 880 := by
  have heq : (3 * (5^2 * (23)) : ℕ) = 1725 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_23]
  try omega

theorem v3_phi_1725 : v3_fast (totient 1725) 100 = v3_phi_list.getD 1725 0 := by
  rw [tot_1725]
  rfl

theorem tot_1726 : totient 1726 = 862 := by
  have heq : (2 * (863) : ℕ) = 1726 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_863 : totient 863 = 863 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_863]
  try omega

theorem v3_phi_1726 : v3_fast (totient 1726) 100 = v3_phi_list.getD 1726 0 := by
  rw [tot_1726]
  rfl

theorem tot_1727 : totient 1727 = 1560 := by
  have heq : (11 * (157) : ℕ) = 1727 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_157]
  try omega

theorem v3_phi_1727 : v3_fast (totient 1727) 100 = v3_phi_list.getD 1727 0 := by
  rw [tot_1727]
  rfl

theorem tot_1728 : totient 1728 = 576 := by
  have heq : (2^6 * (3^3) : ℕ) = 1728 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_1728 : v3_fast (totient 1728) 100 = v3_phi_list.getD 1728 0 := by
  rw [tot_1728]
  rfl

theorem tot_1729 : totient 1729 = 1296 := by
  have heq : (7 * (13 * (19)) : ℕ) = 1729 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_13, hp_19]
  try omega

theorem v3_phi_1729 : v3_fast (totient 1729) 100 = v3_phi_list.getD 1729 0 := by
  rw [tot_1729]
  rfl

theorem tot_1730 : totient 1730 = 688 := by
  have heq : (2 * (5 * (173)) : ℕ) = 1730 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_173]
  try omega

theorem v3_phi_1730 : v3_fast (totient 1730) 100 = v3_phi_list.getD 1730 0 := by
  rw [tot_1730]
  rfl

theorem tot_1731 : totient 1731 = 1152 := by
  have heq : (3 * (577) : ℕ) = 1731 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_577 : totient 577 = 577 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_577]
  try omega

theorem v3_phi_1731 : v3_fast (totient 1731) 100 = v3_phi_list.getD 1731 0 := by
  rw [tot_1731]
  rfl

theorem tot_1732 : totient 1732 = 864 := by
  have heq : (2^2 * (433) : ℕ) = 1732 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_433 : totient 433 = 433 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_433]
  try omega

theorem v3_phi_1732 : v3_fast (totient 1732) 100 = v3_phi_list.getD 1732 0 := by
  rw [tot_1732]
  rfl

theorem tot_1733 : totient 1733 = 1732 := by
  have h : totient 1733 = 1733 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1733 : v3_fast (totient 1733) 100 = v3_phi_list.getD 1733 0 := by
  rw [tot_1733]
  rfl

theorem tot_1734 : totient 1734 = 544 := by
  have heq : (2 * (3 * (17^2)) : ℕ) = 1734 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_17]
  try omega

theorem v3_phi_1734 : v3_fast (totient 1734) 100 = v3_phi_list.getD 1734 0 := by
  rw [tot_1734]
  rfl

theorem tot_1735 : totient 1735 = 1384 := by
  have heq : (5 * (347) : ℕ) = 1735 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_347 : totient 347 = 347 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_347]
  try omega

theorem v3_phi_1735 : v3_fast (totient 1735) 100 = v3_phi_list.getD 1735 0 := by
  rw [tot_1735]
  rfl

theorem tot_1736 : totient 1736 = 720 := by
  have heq : (2^3 * (7 * (31)) : ℕ) = 1736 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_31]
  try omega

theorem v3_phi_1736 : v3_fast (totient 1736) 100 = v3_phi_list.getD 1736 0 := by
  rw [tot_1736]
  rfl

theorem tot_1737 : totient 1737 = 1152 := by
  have heq : (3^2 * (193) : ℕ) = 1737 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_193]
  try omega

theorem v3_phi_1737 : v3_fast (totient 1737) 100 = v3_phi_list.getD 1737 0 := by
  rw [tot_1737]
  rfl

theorem tot_1738 : totient 1738 = 780 := by
  have heq : (2 * (11 * (79)) : ℕ) = 1738 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_79]
  try omega

theorem v3_phi_1738 : v3_fast (totient 1738) 100 = v3_phi_list.getD 1738 0 := by
  rw [tot_1738]
  rfl

theorem tot_1739 : totient 1739 = 1656 := by
  have heq : (37 * (47) : ℕ) = 1739 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_37, hp_47]
  try omega

theorem v3_phi_1739 : v3_fast (totient 1739) 100 = v3_phi_list.getD 1739 0 := by
  rw [tot_1739]
  rfl

theorem tot_1740 : totient 1740 = 448 := by
  have heq : (2^2 * (3 * (5 * (29))) : ℕ) = 1740 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_29]
  try omega

theorem v3_phi_1740 : v3_fast (totient 1740) 100 = v3_phi_list.getD 1740 0 := by
  rw [tot_1740]
  rfl

theorem tot_1741 : totient 1741 = 1740 := by
  have h : totient 1741 = 1741 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1741 : v3_fast (totient 1741) 100 = v3_phi_list.getD 1741 0 := by
  rw [tot_1741]
  rfl

theorem tot_1742 : totient 1742 = 792 := by
  have heq : (2 * (13 * (67)) : ℕ) = 1742 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_67]
  try omega

theorem v3_phi_1742 : v3_fast (totient 1742) 100 = v3_phi_list.getD 1742 0 := by
  rw [tot_1742]
  rfl

theorem tot_1743 : totient 1743 = 984 := by
  have heq : (3 * (7 * (83)) : ℕ) = 1743 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_83]
  try omega

theorem v3_phi_1743 : v3_fast (totient 1743) 100 = v3_phi_list.getD 1743 0 := by
  rw [tot_1743]
  rfl

theorem tot_1744 : totient 1744 = 864 := by
  have heq : (2^4 * (109) : ℕ) = 1744 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_109]
  try omega

theorem v3_phi_1744 : v3_fast (totient 1744) 100 = v3_phi_list.getD 1744 0 := by
  rw [tot_1744]
  rfl

theorem tot_1745 : totient 1745 = 1392 := by
  have heq : (5 * (349) : ℕ) = 1745 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_349 : totient 349 = 349 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_349]
  try omega

theorem v3_phi_1745 : v3_fast (totient 1745) 100 = v3_phi_list.getD 1745 0 := by
  rw [tot_1745]
  rfl

theorem tot_1746 : totient 1746 = 576 := by
  have heq : (2 * (3^2 * (97)) : ℕ) = 1746 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_97]
  try omega

theorem v3_phi_1746 : v3_fast (totient 1746) 100 = v3_phi_list.getD 1746 0 := by
  rw [tot_1746]
  rfl

theorem tot_1747 : totient 1747 = 1746 := by
  have h : totient 1747 = 1747 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1747 : v3_fast (totient 1747) 100 = v3_phi_list.getD 1747 0 := by
  rw [tot_1747]
  rfl

theorem tot_1748 : totient 1748 = 792 := by
  have heq : (2^2 * (19 * (23)) : ℕ) = 1748 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_23]
  try omega

theorem v3_phi_1748 : v3_fast (totient 1748) 100 = v3_phi_list.getD 1748 0 := by
  rw [tot_1748]
  rfl

theorem tot_1749 : totient 1749 = 1040 := by
  have heq : (3 * (11 * (53)) : ℕ) = 1749 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_53]
  try omega

theorem v3_phi_1749 : v3_fast (totient 1749) 100 = v3_phi_list.getD 1749 0 := by
  rw [tot_1749]
  rfl

theorem tot_1750 : totient 1750 = 600 := by
  have heq : (2 * (5^3 * (7)) : ℕ) = 1750 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7]
  try omega

theorem v3_phi_1750 : v3_fast (totient 1750) 100 = v3_phi_list.getD 1750 0 := by
  rw [tot_1750]
  rfl

theorem tot_1751 : totient 1751 = 1632 := by
  have heq : (17 * (103) : ℕ) = 1751 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_103]
  try omega

theorem v3_phi_1751 : v3_fast (totient 1751) 100 = v3_phi_list.getD 1751 0 := by
  rw [tot_1751]
  rfl

theorem tot_1752 : totient 1752 = 576 := by
  have heq : (2^3 * (3 * (73)) : ℕ) = 1752 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_73]
  try omega

theorem v3_phi_1752 : v3_fast (totient 1752) 100 = v3_phi_list.getD 1752 0 := by
  rw [tot_1752]
  rfl

theorem tot_1753 : totient 1753 = 1752 := by
  have h : totient 1753 = 1753 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1753 : v3_fast (totient 1753) 100 = v3_phi_list.getD 1753 0 := by
  rw [tot_1753]
  rfl

theorem tot_1754 : totient 1754 = 876 := by
  have heq : (2 * (877) : ℕ) = 1754 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_877 : totient 877 = 877 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_877]
  try omega

theorem v3_phi_1754 : v3_fast (totient 1754) 100 = v3_phi_list.getD 1754 0 := by
  rw [tot_1754]
  rfl

theorem tot_1755 : totient 1755 = 864 := by
  have heq : (3^3 * (5 * (13)) : ℕ) = 1755 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_13]
  try omega

theorem v3_phi_1755 : v3_fast (totient 1755) 100 = v3_phi_list.getD 1755 0 := by
  rw [tot_1755]
  rfl

theorem tot_1756 : totient 1756 = 876 := by
  have heq : (2^2 * (439) : ℕ) = 1756 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_439 : totient 439 = 439 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_439]
  try omega

theorem v3_phi_1756 : v3_fast (totient 1756) 100 = v3_phi_list.getD 1756 0 := by
  rw [tot_1756]
  rfl

theorem tot_1757 : totient 1757 = 1500 := by
  have heq : (7 * (251) : ℕ) = 1757 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_251]
  try omega

theorem v3_phi_1757 : v3_fast (totient 1757) 100 = v3_phi_list.getD 1757 0 := by
  rw [tot_1757]
  rfl

theorem tot_1758 : totient 1758 = 584 := by
  have heq : (2 * (3 * (293)) : ℕ) = 1758 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_293 : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_293]
  try omega

theorem v3_phi_1758 : v3_fast (totient 1758) 100 = v3_phi_list.getD 1758 0 := by
  rw [tot_1758]
  rfl

theorem tot_1759 : totient 1759 = 1758 := by
  have h : totient 1759 = 1759 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1759 : v3_fast (totient 1759) 100 = v3_phi_list.getD 1759 0 := by
  rw [tot_1759]
  rfl

theorem tot_1760 : totient 1760 = 640 := by
  have heq : (2^5 * (5 * (11)) : ℕ) = 1760 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11]
  try omega

theorem v3_phi_1760 : v3_fast (totient 1760) 100 = v3_phi_list.getD 1760 0 := by
  rw [tot_1760]
  rfl

theorem tot_1761 : totient 1761 = 1172 := by
  have heq : (3 * (587) : ℕ) = 1761 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_587 : totient 587 = 587 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_587]
  try omega

theorem v3_phi_1761 : v3_fast (totient 1761) 100 = v3_phi_list.getD 1761 0 := by
  rw [tot_1761]
  rfl

theorem tot_1762 : totient 1762 = 880 := by
  have heq : (2 * (881) : ℕ) = 1762 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_881 : totient 881 = 881 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_881]
  try omega

theorem v3_phi_1762 : v3_fast (totient 1762) 100 = v3_phi_list.getD 1762 0 := by
  rw [tot_1762]
  rfl

theorem tot_1763 : totient 1763 = 1680 := by
  have heq : (41 * (43) : ℕ) = 1763 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_41, hp_43]
  try omega

theorem v3_phi_1763 : v3_fast (totient 1763) 100 = v3_phi_list.getD 1763 0 := by
  rw [tot_1763]
  rfl

theorem tot_1764 : totient 1764 = 504 := by
  have heq : (2^2 * (3^2 * (7^2)) : ℕ) = 1764 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_1764 : v3_fast (totient 1764) 100 = v3_phi_list.getD 1764 0 := by
  rw [tot_1764]
  rfl

theorem tot_1765 : totient 1765 = 1408 := by
  have heq : (5 * (353) : ℕ) = 1765 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_353 : totient 353 = 353 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_353]
  try omega

theorem v3_phi_1765 : v3_fast (totient 1765) 100 = v3_phi_list.getD 1765 0 := by
  rw [tot_1765]
  rfl

theorem tot_1766 : totient 1766 = 882 := by
  have heq : (2 * (883) : ℕ) = 1766 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_883 : totient 883 = 883 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_883]
  try omega

theorem v3_phi_1766 : v3_fast (totient 1766) 100 = v3_phi_list.getD 1766 0 := by
  rw [tot_1766]
  rfl

theorem tot_1767 : totient 1767 = 1080 := by
  have heq : (3 * (19 * (31)) : ℕ) = 1767 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19, hp_31]
  try omega

theorem v3_phi_1767 : v3_fast (totient 1767) 100 = v3_phi_list.getD 1767 0 := by
  rw [tot_1767]
  rfl

theorem tot_1768 : totient 1768 = 768 := by
  have heq : (2^3 * (13 * (17)) : ℕ) = 1768 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_17]
  try omega

theorem v3_phi_1768 : v3_fast (totient 1768) 100 = v3_phi_list.getD 1768 0 := by
  rw [tot_1768]
  rfl

theorem tot_1769 : totient 1769 = 1680 := by
  have heq : (29 * (61) : ℕ) = 1769 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_61]
  try omega

theorem v3_phi_1769 : v3_fast (totient 1769) 100 = v3_phi_list.getD 1769 0 := by
  rw [tot_1769]
  rfl

theorem tot_1770 : totient 1770 = 464 := by
  have heq : (2 * (3 * (5 * (59))) : ℕ) = 1770 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_59]
  try omega

theorem v3_phi_1770 : v3_fast (totient 1770) 100 = v3_phi_list.getD 1770 0 := by
  rw [tot_1770]
  rfl

theorem tot_1771 : totient 1771 = 1320 := by
  have heq : (7 * (11 * (23)) : ℕ) = 1771 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11, hp_23]
  try omega

theorem v3_phi_1771 : v3_fast (totient 1771) 100 = v3_phi_list.getD 1771 0 := by
  rw [tot_1771]
  rfl

theorem tot_1772 : totient 1772 = 884 := by
  have heq : (2^2 * (443) : ℕ) = 1772 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_443 : totient 443 = 443 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_443]
  try omega

theorem v3_phi_1772 : v3_fast (totient 1772) 100 = v3_phi_list.getD 1772 0 := by
  rw [tot_1772]
  rfl

theorem tot_1773 : totient 1773 = 1176 := by
  have heq : (3^2 * (197) : ℕ) = 1773 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_197]
  try omega

theorem v3_phi_1773 : v3_fast (totient 1773) 100 = v3_phi_list.getD 1773 0 := by
  rw [tot_1773]
  rfl

theorem tot_1774 : totient 1774 = 886 := by
  have heq : (2 * (887) : ℕ) = 1774 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_887 : totient 887 = 887 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_887]
  try omega

theorem v3_phi_1774 : v3_fast (totient 1774) 100 = v3_phi_list.getD 1774 0 := by
  rw [tot_1774]
  rfl

theorem tot_1775 : totient 1775 = 1400 := by
  have heq : (5^2 * (71) : ℕ) = 1775 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_71]
  try omega

theorem v3_phi_1775 : v3_fast (totient 1775) 100 = v3_phi_list.getD 1775 0 := by
  rw [tot_1775]
  rfl

theorem tot_1776 : totient 1776 = 576 := by
  have heq : (2^4 * (3 * (37)) : ℕ) = 1776 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37]
  try omega

theorem v3_phi_1776 : v3_fast (totient 1776) 100 = v3_phi_list.getD 1776 0 := by
  rw [tot_1776]
  rfl

theorem tot_1777 : totient 1777 = 1776 := by
  have h : totient 1777 = 1777 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1777 : v3_fast (totient 1777) 100 = v3_phi_list.getD 1777 0 := by
  rw [tot_1777]
  rfl

theorem tot_1778 : totient 1778 = 756 := by
  have heq : (2 * (7 * (127)) : ℕ) = 1778 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_127]
  try omega

theorem v3_phi_1778 : v3_fast (totient 1778) 100 = v3_phi_list.getD 1778 0 := by
  rw [tot_1778]
  rfl

theorem tot_1779 : totient 1779 = 1184 := by
  have heq : (3 * (593) : ℕ) = 1779 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_593 : totient 593 = 593 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_593]
  try omega

theorem v3_phi_1779 : v3_fast (totient 1779) 100 = v3_phi_list.getD 1779 0 := by
  rw [tot_1779]
  rfl

theorem tot_1780 : totient 1780 = 704 := by
  have heq : (2^2 * (5 * (89)) : ℕ) = 1780 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_89]
  try omega

theorem v3_phi_1780 : v3_fast (totient 1780) 100 = v3_phi_list.getD 1780 0 := by
  rw [tot_1780]
  rfl

theorem tot_1781 : totient 1781 = 1632 := by
  have heq : (13 * (137) : ℕ) = 1781 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_137]
  try omega

theorem v3_phi_1781 : v3_fast (totient 1781) 100 = v3_phi_list.getD 1781 0 := by
  rw [tot_1781]
  rfl

theorem tot_1782 : totient 1782 = 540 := by
  have heq : (2 * (3^4 * (11)) : ℕ) = 1782 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_1782 : v3_fast (totient 1782) 100 = v3_phi_list.getD 1782 0 := by
  rw [tot_1782]
  rfl

theorem tot_1783 : totient 1783 = 1782 := by
  have h : totient 1783 = 1783 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1783 : v3_fast (totient 1783) 100 = v3_phi_list.getD 1783 0 := by
  rw [tot_1783]
  rfl

theorem tot_1784 : totient 1784 = 888 := by
  have heq : (2^3 * (223) : ℕ) = 1784 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_223]
  try omega

theorem v3_phi_1784 : v3_fast (totient 1784) 100 = v3_phi_list.getD 1784 0 := by
  rw [tot_1784]
  rfl

theorem tot_1785 : totient 1785 = 768 := by
  have heq : (3 * (5 * (7 * (17))) : ℕ) = 1785 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7, hp_17]
  try omega

theorem v3_phi_1785 : v3_fast (totient 1785) 100 = v3_phi_list.getD 1785 0 := by
  rw [tot_1785]
  rfl

theorem tot_1786 : totient 1786 = 828 := by
  have heq : (2 * (19 * (47)) : ℕ) = 1786 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_47]
  try omega

theorem v3_phi_1786 : v3_fast (totient 1786) 100 = v3_phi_list.getD 1786 0 := by
  rw [tot_1786]
  rfl

theorem tot_1787 : totient 1787 = 1786 := by
  have h : totient 1787 = 1787 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1787 : v3_fast (totient 1787) 100 = v3_phi_list.getD 1787 0 := by
  rw [tot_1787]
  rfl

theorem tot_1788 : totient 1788 = 592 := by
  have heq : (2^2 * (3 * (149)) : ℕ) = 1788 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_149]
  try omega

theorem v3_phi_1788 : v3_fast (totient 1788) 100 = v3_phi_list.getD 1788 0 := by
  rw [tot_1788]
  rfl

theorem tot_1789 : totient 1789 = 1788 := by
  have h : totient 1789 = 1789 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1789 : v3_fast (totient 1789) 100 = v3_phi_list.getD 1789 0 := by
  rw [tot_1789]
  rfl

theorem tot_1790 : totient 1790 = 712 := by
  have heq : (2 * (5 * (179)) : ℕ) = 1790 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_179]
  try omega

theorem v3_phi_1790 : v3_fast (totient 1790) 100 = v3_phi_list.getD 1790 0 := by
  rw [tot_1790]
  rfl

theorem tot_1791 : totient 1791 = 1188 := by
  have heq : (3^2 * (199) : ℕ) = 1791 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_199]
  try omega

theorem v3_phi_1791 : v3_fast (totient 1791) 100 = v3_phi_list.getD 1791 0 := by
  rw [tot_1791]
  rfl

theorem tot_1792 : totient 1792 = 768 := by
  have heq : (2^8 * (7) : ℕ) = 1792 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^8) = 2^7 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_1792 : v3_fast (totient 1792) 100 = v3_phi_list.getD 1792 0 := by
  rw [tot_1792]
  rfl

theorem tot_1793 : totient 1793 = 1620 := by
  have heq : (11 * (163) : ℕ) = 1793 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_163]
  try omega

theorem v3_phi_1793 : v3_fast (totient 1793) 100 = v3_phi_list.getD 1793 0 := by
  rw [tot_1793]
  rfl

theorem tot_1794 : totient 1794 = 528 := by
  have heq : (2 * (3 * (13 * (23))) : ℕ) = 1794 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13, hp_23]
  try omega

theorem v3_phi_1794 : v3_fast (totient 1794) 100 = v3_phi_list.getD 1794 0 := by
  rw [tot_1794]
  rfl

theorem tot_1795 : totient 1795 = 1432 := by
  have heq : (5 * (359) : ℕ) = 1795 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_359 : totient 359 = 359 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_359]
  try omega

theorem v3_phi_1795 : v3_fast (totient 1795) 100 = v3_phi_list.getD 1795 0 := by
  rw [tot_1795]
  rfl

theorem tot_1796 : totient 1796 = 896 := by
  have heq : (2^2 * (449) : ℕ) = 1796 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_449 : totient 449 = 449 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_449]
  try omega

theorem v3_phi_1796 : v3_fast (totient 1796) 100 = v3_phi_list.getD 1796 0 := by
  rw [tot_1796]
  rfl

theorem tot_1797 : totient 1797 = 1196 := by
  have heq : (3 * (599) : ℕ) = 1797 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_599 : totient 599 = 599 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_599]
  try omega

theorem v3_phi_1797 : v3_fast (totient 1797) 100 = v3_phi_list.getD 1797 0 := by
  rw [tot_1797]
  rfl

theorem tot_1798 : totient 1798 = 840 := by
  have heq : (2 * (29 * (31)) : ℕ) = 1798 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29, hp_31]
  try omega

theorem v3_phi_1798 : v3_fast (totient 1798) 100 = v3_phi_list.getD 1798 0 := by
  rw [tot_1798]
  rfl

theorem tot_1799 : totient 1799 = 1536 := by
  have heq : (7 * (257) : ℕ) = 1799 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_257]
  try omega

theorem v3_phi_1799 : v3_fast (totient 1799) 100 = v3_phi_list.getD 1799 0 := by
  rw [tot_1799]
  rfl

theorem tot_1800 : totient 1800 = 480 := by
  have heq : (2^3 * (3^2 * (5^2)) : ℕ) = 1800 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_1800 : v3_fast (totient 1800) 100 = v3_phi_list.getD 1800 0 := by
  rw [tot_1800]
  rfl

theorem tot_1801 : totient 1801 = 1800 := by
  have h : totient 1801 = 1801 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1801 : v3_fast (totient 1801) 100 = v3_phi_list.getD 1801 0 := by
  rw [tot_1801]
  rfl

theorem tot_1802 : totient 1802 = 832 := by
  have heq : (2 * (17 * (53)) : ℕ) = 1802 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_53]
  try omega

theorem v3_phi_1802 : v3_fast (totient 1802) 100 = v3_phi_list.getD 1802 0 := by
  rw [tot_1802]
  rfl

theorem tot_1803 : totient 1803 = 1200 := by
  have heq : (3 * (601) : ℕ) = 1803 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_601 : totient 601 = 601 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_601]
  try omega

theorem v3_phi_1803 : v3_fast (totient 1803) 100 = v3_phi_list.getD 1803 0 := by
  rw [tot_1803]
  rfl

theorem tot_1804 : totient 1804 = 800 := by
  have heq : (2^2 * (11 * (41)) : ℕ) = 1804 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_41]
  try omega

theorem v3_phi_1804 : v3_fast (totient 1804) 100 = v3_phi_list.getD 1804 0 := by
  rw [tot_1804]
  rfl

theorem tot_1805 : totient 1805 = 1368 := by
  have heq : (5 * (19^2) : ℕ) = 1805 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient (19^2) = 19^1 * (19 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_19]
  try omega

theorem v3_phi_1805 : v3_fast (totient 1805) 100 = v3_phi_list.getD 1805 0 := by
  rw [tot_1805]
  rfl

theorem tot_1806 : totient 1806 = 504 := by
  have heq : (2 * (3 * (7 * (43))) : ℕ) = 1806 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_43]
  try omega

theorem v3_phi_1806 : v3_fast (totient 1806) 100 = v3_phi_list.getD 1806 0 := by
  rw [tot_1806]
  rfl

theorem tot_1807 : totient 1807 = 1656 := by
  have heq : (13 * (139) : ℕ) = 1807 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_139]
  try omega

theorem v3_phi_1807 : v3_fast (totient 1807) 100 = v3_phi_list.getD 1807 0 := by
  rw [tot_1807]
  rfl

theorem v3_phi_eq_list_3 (k : ℕ) (hk1 : 1380 ≤ k) (hk2 : k ≤ 1807) : v3_fast k.totient 100 = v3_phi_list.getD k 0 := by
  have heq : k = 1380 + (k - 1380) := by omega
  revert hk1 hk2
  rw [heq]
  match k - 1380 with
  | 0 => intro _ _; exact v3_phi_1380
  | 1 => intro _ _; exact v3_phi_1381
  | 2 => intro _ _; exact v3_phi_1382
  | 3 => intro _ _; exact v3_phi_1383
  | 4 => intro _ _; exact v3_phi_1384
  | 5 => intro _ _; exact v3_phi_1385
  | 6 => intro _ _; exact v3_phi_1386
  | 7 => intro _ _; exact v3_phi_1387
  | 8 => intro _ _; exact v3_phi_1388
  | 9 => intro _ _; exact v3_phi_1389
  | 10 => intro _ _; exact v3_phi_1390
  | 11 => intro _ _; exact v3_phi_1391
  | 12 => intro _ _; exact v3_phi_1392
  | 13 => intro _ _; exact v3_phi_1393
  | 14 => intro _ _; exact v3_phi_1394
  | 15 => intro _ _; exact v3_phi_1395
  | 16 => intro _ _; exact v3_phi_1396
  | 17 => intro _ _; exact v3_phi_1397
  | 18 => intro _ _; exact v3_phi_1398
  | 19 => intro _ _; exact v3_phi_1399
  | 20 => intro _ _; exact v3_phi_1400
  | 21 => intro _ _; exact v3_phi_1401
  | 22 => intro _ _; exact v3_phi_1402
  | 23 => intro _ _; exact v3_phi_1403
  | 24 => intro _ _; exact v3_phi_1404
  | 25 => intro _ _; exact v3_phi_1405
  | 26 => intro _ _; exact v3_phi_1406
  | 27 => intro _ _; exact v3_phi_1407
  | 28 => intro _ _; exact v3_phi_1408
  | 29 => intro _ _; exact v3_phi_1409
  | 30 => intro _ _; exact v3_phi_1410
  | 31 => intro _ _; exact v3_phi_1411
  | 32 => intro _ _; exact v3_phi_1412
  | 33 => intro _ _; exact v3_phi_1413
  | 34 => intro _ _; exact v3_phi_1414
  | 35 => intro _ _; exact v3_phi_1415
  | 36 => intro _ _; exact v3_phi_1416
  | 37 => intro _ _; exact v3_phi_1417
  | 38 => intro _ _; exact v3_phi_1418
  | 39 => intro _ _; exact v3_phi_1419
  | 40 => intro _ _; exact v3_phi_1420
  | 41 => intro _ _; exact v3_phi_1421
  | 42 => intro _ _; exact v3_phi_1422
  | 43 => intro _ _; exact v3_phi_1423
  | 44 => intro _ _; exact v3_phi_1424
  | 45 => intro _ _; exact v3_phi_1425
  | 46 => intro _ _; exact v3_phi_1426
  | 47 => intro _ _; exact v3_phi_1427
  | 48 => intro _ _; exact v3_phi_1428
  | 49 => intro _ _; exact v3_phi_1429
  | 50 => intro _ _; exact v3_phi_1430
  | 51 => intro _ _; exact v3_phi_1431
  | 52 => intro _ _; exact v3_phi_1432
  | 53 => intro _ _; exact v3_phi_1433
  | 54 => intro _ _; exact v3_phi_1434
  | 55 => intro _ _; exact v3_phi_1435
  | 56 => intro _ _; exact v3_phi_1436
  | 57 => intro _ _; exact v3_phi_1437
  | 58 => intro _ _; exact v3_phi_1438
  | 59 => intro _ _; exact v3_phi_1439
  | 60 => intro _ _; exact v3_phi_1440
  | 61 => intro _ _; exact v3_phi_1441
  | 62 => intro _ _; exact v3_phi_1442
  | 63 => intro _ _; exact v3_phi_1443
  | 64 => intro _ _; exact v3_phi_1444
  | 65 => intro _ _; exact v3_phi_1445
  | 66 => intro _ _; exact v3_phi_1446
  | 67 => intro _ _; exact v3_phi_1447
  | 68 => intro _ _; exact v3_phi_1448
  | 69 => intro _ _; exact v3_phi_1449
  | 70 => intro _ _; exact v3_phi_1450
  | 71 => intro _ _; exact v3_phi_1451
  | 72 => intro _ _; exact v3_phi_1452
  | 73 => intro _ _; exact v3_phi_1453
  | 74 => intro _ _; exact v3_phi_1454
  | 75 => intro _ _; exact v3_phi_1455
  | 76 => intro _ _; exact v3_phi_1456
  | 77 => intro _ _; exact v3_phi_1457
  | 78 => intro _ _; exact v3_phi_1458
  | 79 => intro _ _; exact v3_phi_1459
  | 80 => intro _ _; exact v3_phi_1460
  | 81 => intro _ _; exact v3_phi_1461
  | 82 => intro _ _; exact v3_phi_1462
  | 83 => intro _ _; exact v3_phi_1463
  | 84 => intro _ _; exact v3_phi_1464
  | 85 => intro _ _; exact v3_phi_1465
  | 86 => intro _ _; exact v3_phi_1466
  | 87 => intro _ _; exact v3_phi_1467
  | 88 => intro _ _; exact v3_phi_1468
  | 89 => intro _ _; exact v3_phi_1469
  | 90 => intro _ _; exact v3_phi_1470
  | 91 => intro _ _; exact v3_phi_1471
  | 92 => intro _ _; exact v3_phi_1472
  | 93 => intro _ _; exact v3_phi_1473
  | 94 => intro _ _; exact v3_phi_1474
  | 95 => intro _ _; exact v3_phi_1475
  | 96 => intro _ _; exact v3_phi_1476
  | 97 => intro _ _; exact v3_phi_1477
  | 98 => intro _ _; exact v3_phi_1478
  | 99 => intro _ _; exact v3_phi_1479
  | 100 => intro _ _; exact v3_phi_1480
  | 101 => intro _ _; exact v3_phi_1481
  | 102 => intro _ _; exact v3_phi_1482
  | 103 => intro _ _; exact v3_phi_1483
  | 104 => intro _ _; exact v3_phi_1484
  | 105 => intro _ _; exact v3_phi_1485
  | 106 => intro _ _; exact v3_phi_1486
  | 107 => intro _ _; exact v3_phi_1487
  | 108 => intro _ _; exact v3_phi_1488
  | 109 => intro _ _; exact v3_phi_1489
  | 110 => intro _ _; exact v3_phi_1490
  | 111 => intro _ _; exact v3_phi_1491
  | 112 => intro _ _; exact v3_phi_1492
  | 113 => intro _ _; exact v3_phi_1493
  | 114 => intro _ _; exact v3_phi_1494
  | 115 => intro _ _; exact v3_phi_1495
  | 116 => intro _ _; exact v3_phi_1496
  | 117 => intro _ _; exact v3_phi_1497
  | 118 => intro _ _; exact v3_phi_1498
  | 119 => intro _ _; exact v3_phi_1499
  | 120 => intro _ _; exact v3_phi_1500
  | 121 => intro _ _; exact v3_phi_1501
  | 122 => intro _ _; exact v3_phi_1502
  | 123 => intro _ _; exact v3_phi_1503
  | 124 => intro _ _; exact v3_phi_1504
  | 125 => intro _ _; exact v3_phi_1505
  | 126 => intro _ _; exact v3_phi_1506
  | 127 => intro _ _; exact v3_phi_1507
  | 128 => intro _ _; exact v3_phi_1508
  | 129 => intro _ _; exact v3_phi_1509
  | 130 => intro _ _; exact v3_phi_1510
  | 131 => intro _ _; exact v3_phi_1511
  | 132 => intro _ _; exact v3_phi_1512
  | 133 => intro _ _; exact v3_phi_1513
  | 134 => intro _ _; exact v3_phi_1514
  | 135 => intro _ _; exact v3_phi_1515
  | 136 => intro _ _; exact v3_phi_1516
  | 137 => intro _ _; exact v3_phi_1517
  | 138 => intro _ _; exact v3_phi_1518
  | 139 => intro _ _; exact v3_phi_1519
  | 140 => intro _ _; exact v3_phi_1520
  | 141 => intro _ _; exact v3_phi_1521
  | 142 => intro _ _; exact v3_phi_1522
  | 143 => intro _ _; exact v3_phi_1523
  | 144 => intro _ _; exact v3_phi_1524
  | 145 => intro _ _; exact v3_phi_1525
  | 146 => intro _ _; exact v3_phi_1526
  | 147 => intro _ _; exact v3_phi_1527
  | 148 => intro _ _; exact v3_phi_1528
  | 149 => intro _ _; exact v3_phi_1529
  | 150 => intro _ _; exact v3_phi_1530
  | 151 => intro _ _; exact v3_phi_1531
  | 152 => intro _ _; exact v3_phi_1532
  | 153 => intro _ _; exact v3_phi_1533
  | 154 => intro _ _; exact v3_phi_1534
  | 155 => intro _ _; exact v3_phi_1535
  | 156 => intro _ _; exact v3_phi_1536
  | 157 => intro _ _; exact v3_phi_1537
  | 158 => intro _ _; exact v3_phi_1538
  | 159 => intro _ _; exact v3_phi_1539
  | 160 => intro _ _; exact v3_phi_1540
  | 161 => intro _ _; exact v3_phi_1541
  | 162 => intro _ _; exact v3_phi_1542
  | 163 => intro _ _; exact v3_phi_1543
  | 164 => intro _ _; exact v3_phi_1544
  | 165 => intro _ _; exact v3_phi_1545
  | 166 => intro _ _; exact v3_phi_1546
  | 167 => intro _ _; exact v3_phi_1547
  | 168 => intro _ _; exact v3_phi_1548
  | 169 => intro _ _; exact v3_phi_1549
  | 170 => intro _ _; exact v3_phi_1550
  | 171 => intro _ _; exact v3_phi_1551
  | 172 => intro _ _; exact v3_phi_1552
  | 173 => intro _ _; exact v3_phi_1553
  | 174 => intro _ _; exact v3_phi_1554
  | 175 => intro _ _; exact v3_phi_1555
  | 176 => intro _ _; exact v3_phi_1556
  | 177 => intro _ _; exact v3_phi_1557
  | 178 => intro _ _; exact v3_phi_1558
  | 179 => intro _ _; exact v3_phi_1559
  | 180 => intro _ _; exact v3_phi_1560
  | 181 => intro _ _; exact v3_phi_1561
  | 182 => intro _ _; exact v3_phi_1562
  | 183 => intro _ _; exact v3_phi_1563
  | 184 => intro _ _; exact v3_phi_1564
  | 185 => intro _ _; exact v3_phi_1565
  | 186 => intro _ _; exact v3_phi_1566
  | 187 => intro _ _; exact v3_phi_1567
  | 188 => intro _ _; exact v3_phi_1568
  | 189 => intro _ _; exact v3_phi_1569
  | 190 => intro _ _; exact v3_phi_1570
  | 191 => intro _ _; exact v3_phi_1571
  | 192 => intro _ _; exact v3_phi_1572
  | 193 => intro _ _; exact v3_phi_1573
  | 194 => intro _ _; exact v3_phi_1574
  | 195 => intro _ _; exact v3_phi_1575
  | 196 => intro _ _; exact v3_phi_1576
  | 197 => intro _ _; exact v3_phi_1577
  | 198 => intro _ _; exact v3_phi_1578
  | 199 => intro _ _; exact v3_phi_1579
  | 200 => intro _ _; exact v3_phi_1580
  | 201 => intro _ _; exact v3_phi_1581
  | 202 => intro _ _; exact v3_phi_1582
  | 203 => intro _ _; exact v3_phi_1583
  | 204 => intro _ _; exact v3_phi_1584
  | 205 => intro _ _; exact v3_phi_1585
  | 206 => intro _ _; exact v3_phi_1586
  | 207 => intro _ _; exact v3_phi_1587
  | 208 => intro _ _; exact v3_phi_1588
  | 209 => intro _ _; exact v3_phi_1589
  | 210 => intro _ _; exact v3_phi_1590
  | 211 => intro _ _; exact v3_phi_1591
  | 212 => intro _ _; exact v3_phi_1592
  | 213 => intro _ _; exact v3_phi_1593
  | 214 => intro _ _; exact v3_phi_1594
  | 215 => intro _ _; exact v3_phi_1595
  | 216 => intro _ _; exact v3_phi_1596
  | 217 => intro _ _; exact v3_phi_1597
  | 218 => intro _ _; exact v3_phi_1598
  | 219 => intro _ _; exact v3_phi_1599
  | 220 => intro _ _; exact v3_phi_1600
  | 221 => intro _ _; exact v3_phi_1601
  | 222 => intro _ _; exact v3_phi_1602
  | 223 => intro _ _; exact v3_phi_1603
  | 224 => intro _ _; exact v3_phi_1604
  | 225 => intro _ _; exact v3_phi_1605
  | 226 => intro _ _; exact v3_phi_1606
  | 227 => intro _ _; exact v3_phi_1607
  | 228 => intro _ _; exact v3_phi_1608
  | 229 => intro _ _; exact v3_phi_1609
  | 230 => intro _ _; exact v3_phi_1610
  | 231 => intro _ _; exact v3_phi_1611
  | 232 => intro _ _; exact v3_phi_1612
  | 233 => intro _ _; exact v3_phi_1613
  | 234 => intro _ _; exact v3_phi_1614
  | 235 => intro _ _; exact v3_phi_1615
  | 236 => intro _ _; exact v3_phi_1616
  | 237 => intro _ _; exact v3_phi_1617
  | 238 => intro _ _; exact v3_phi_1618
  | 239 => intro _ _; exact v3_phi_1619
  | 240 => intro _ _; exact v3_phi_1620
  | 241 => intro _ _; exact v3_phi_1621
  | 242 => intro _ _; exact v3_phi_1622
  | 243 => intro _ _; exact v3_phi_1623
  | 244 => intro _ _; exact v3_phi_1624
  | 245 => intro _ _; exact v3_phi_1625
  | 246 => intro _ _; exact v3_phi_1626
  | 247 => intro _ _; exact v3_phi_1627
  | 248 => intro _ _; exact v3_phi_1628
  | 249 => intro _ _; exact v3_phi_1629
  | 250 => intro _ _; exact v3_phi_1630
  | 251 => intro _ _; exact v3_phi_1631
  | 252 => intro _ _; exact v3_phi_1632
  | 253 => intro _ _; exact v3_phi_1633
  | 254 => intro _ _; exact v3_phi_1634
  | 255 => intro _ _; exact v3_phi_1635
  | 256 => intro _ _; exact v3_phi_1636
  | 257 => intro _ _; exact v3_phi_1637
  | 258 => intro _ _; exact v3_phi_1638
  | 259 => intro _ _; exact v3_phi_1639
  | 260 => intro _ _; exact v3_phi_1640
  | 261 => intro _ _; exact v3_phi_1641
  | 262 => intro _ _; exact v3_phi_1642
  | 263 => intro _ _; exact v3_phi_1643
  | 264 => intro _ _; exact v3_phi_1644
  | 265 => intro _ _; exact v3_phi_1645
  | 266 => intro _ _; exact v3_phi_1646
  | 267 => intro _ _; exact v3_phi_1647
  | 268 => intro _ _; exact v3_phi_1648
  | 269 => intro _ _; exact v3_phi_1649
  | 270 => intro _ _; exact v3_phi_1650
  | 271 => intro _ _; exact v3_phi_1651
  | 272 => intro _ _; exact v3_phi_1652
  | 273 => intro _ _; exact v3_phi_1653
  | 274 => intro _ _; exact v3_phi_1654
  | 275 => intro _ _; exact v3_phi_1655
  | 276 => intro _ _; exact v3_phi_1656
  | 277 => intro _ _; exact v3_phi_1657
  | 278 => intro _ _; exact v3_phi_1658
  | 279 => intro _ _; exact v3_phi_1659
  | 280 => intro _ _; exact v3_phi_1660
  | 281 => intro _ _; exact v3_phi_1661
  | 282 => intro _ _; exact v3_phi_1662
  | 283 => intro _ _; exact v3_phi_1663
  | 284 => intro _ _; exact v3_phi_1664
  | 285 => intro _ _; exact v3_phi_1665
  | 286 => intro _ _; exact v3_phi_1666
  | 287 => intro _ _; exact v3_phi_1667
  | 288 => intro _ _; exact v3_phi_1668
  | 289 => intro _ _; exact v3_phi_1669
  | 290 => intro _ _; exact v3_phi_1670
  | 291 => intro _ _; exact v3_phi_1671
  | 292 => intro _ _; exact v3_phi_1672
  | 293 => intro _ _; exact v3_phi_1673
  | 294 => intro _ _; exact v3_phi_1674
  | 295 => intro _ _; exact v3_phi_1675
  | 296 => intro _ _; exact v3_phi_1676
  | 297 => intro _ _; exact v3_phi_1677
  | 298 => intro _ _; exact v3_phi_1678
  | 299 => intro _ _; exact v3_phi_1679
  | 300 => intro _ _; exact v3_phi_1680
  | 301 => intro _ _; exact v3_phi_1681
  | 302 => intro _ _; exact v3_phi_1682
  | 303 => intro _ _; exact v3_phi_1683
  | 304 => intro _ _; exact v3_phi_1684
  | 305 => intro _ _; exact v3_phi_1685
  | 306 => intro _ _; exact v3_phi_1686
  | 307 => intro _ _; exact v3_phi_1687
  | 308 => intro _ _; exact v3_phi_1688
  | 309 => intro _ _; exact v3_phi_1689
  | 310 => intro _ _; exact v3_phi_1690
  | 311 => intro _ _; exact v3_phi_1691
  | 312 => intro _ _; exact v3_phi_1692
  | 313 => intro _ _; exact v3_phi_1693
  | 314 => intro _ _; exact v3_phi_1694
  | 315 => intro _ _; exact v3_phi_1695
  | 316 => intro _ _; exact v3_phi_1696
  | 317 => intro _ _; exact v3_phi_1697
  | 318 => intro _ _; exact v3_phi_1698
  | 319 => intro _ _; exact v3_phi_1699
  | 320 => intro _ _; exact v3_phi_1700
  | 321 => intro _ _; exact v3_phi_1701
  | 322 => intro _ _; exact v3_phi_1702
  | 323 => intro _ _; exact v3_phi_1703
  | 324 => intro _ _; exact v3_phi_1704
  | 325 => intro _ _; exact v3_phi_1705
  | 326 => intro _ _; exact v3_phi_1706
  | 327 => intro _ _; exact v3_phi_1707
  | 328 => intro _ _; exact v3_phi_1708
  | 329 => intro _ _; exact v3_phi_1709
  | 330 => intro _ _; exact v3_phi_1710
  | 331 => intro _ _; exact v3_phi_1711
  | 332 => intro _ _; exact v3_phi_1712
  | 333 => intro _ _; exact v3_phi_1713
  | 334 => intro _ _; exact v3_phi_1714
  | 335 => intro _ _; exact v3_phi_1715
  | 336 => intro _ _; exact v3_phi_1716
  | 337 => intro _ _; exact v3_phi_1717
  | 338 => intro _ _; exact v3_phi_1718
  | 339 => intro _ _; exact v3_phi_1719
  | 340 => intro _ _; exact v3_phi_1720
  | 341 => intro _ _; exact v3_phi_1721
  | 342 => intro _ _; exact v3_phi_1722
  | 343 => intro _ _; exact v3_phi_1723
  | 344 => intro _ _; exact v3_phi_1724
  | 345 => intro _ _; exact v3_phi_1725
  | 346 => intro _ _; exact v3_phi_1726
  | 347 => intro _ _; exact v3_phi_1727
  | 348 => intro _ _; exact v3_phi_1728
  | 349 => intro _ _; exact v3_phi_1729
  | 350 => intro _ _; exact v3_phi_1730
  | 351 => intro _ _; exact v3_phi_1731
  | 352 => intro _ _; exact v3_phi_1732
  | 353 => intro _ _; exact v3_phi_1733
  | 354 => intro _ _; exact v3_phi_1734
  | 355 => intro _ _; exact v3_phi_1735
  | 356 => intro _ _; exact v3_phi_1736
  | 357 => intro _ _; exact v3_phi_1737
  | 358 => intro _ _; exact v3_phi_1738
  | 359 => intro _ _; exact v3_phi_1739
  | 360 => intro _ _; exact v3_phi_1740
  | 361 => intro _ _; exact v3_phi_1741
  | 362 => intro _ _; exact v3_phi_1742
  | 363 => intro _ _; exact v3_phi_1743
  | 364 => intro _ _; exact v3_phi_1744
  | 365 => intro _ _; exact v3_phi_1745
  | 366 => intro _ _; exact v3_phi_1746
  | 367 => intro _ _; exact v3_phi_1747
  | 368 => intro _ _; exact v3_phi_1748
  | 369 => intro _ _; exact v3_phi_1749
  | 370 => intro _ _; exact v3_phi_1750
  | 371 => intro _ _; exact v3_phi_1751
  | 372 => intro _ _; exact v3_phi_1752
  | 373 => intro _ _; exact v3_phi_1753
  | 374 => intro _ _; exact v3_phi_1754
  | 375 => intro _ _; exact v3_phi_1755
  | 376 => intro _ _; exact v3_phi_1756
  | 377 => intro _ _; exact v3_phi_1757
  | 378 => intro _ _; exact v3_phi_1758
  | 379 => intro _ _; exact v3_phi_1759
  | 380 => intro _ _; exact v3_phi_1760
  | 381 => intro _ _; exact v3_phi_1761
  | 382 => intro _ _; exact v3_phi_1762
  | 383 => intro _ _; exact v3_phi_1763
  | 384 => intro _ _; exact v3_phi_1764
  | 385 => intro _ _; exact v3_phi_1765
  | 386 => intro _ _; exact v3_phi_1766
  | 387 => intro _ _; exact v3_phi_1767
  | 388 => intro _ _; exact v3_phi_1768
  | 389 => intro _ _; exact v3_phi_1769
  | 390 => intro _ _; exact v3_phi_1770
  | 391 => intro _ _; exact v3_phi_1771
  | 392 => intro _ _; exact v3_phi_1772
  | 393 => intro _ _; exact v3_phi_1773
  | 394 => intro _ _; exact v3_phi_1774
  | 395 => intro _ _; exact v3_phi_1775
  | 396 => intro _ _; exact v3_phi_1776
  | 397 => intro _ _; exact v3_phi_1777
  | 398 => intro _ _; exact v3_phi_1778
  | 399 => intro _ _; exact v3_phi_1779
  | 400 => intro _ _; exact v3_phi_1780
  | 401 => intro _ _; exact v3_phi_1781
  | 402 => intro _ _; exact v3_phi_1782
  | 403 => intro _ _; exact v3_phi_1783
  | 404 => intro _ _; exact v3_phi_1784
  | 405 => intro _ _; exact v3_phi_1785
  | 406 => intro _ _; exact v3_phi_1786
  | 407 => intro _ _; exact v3_phi_1787
  | 408 => intro _ _; exact v3_phi_1788
  | 409 => intro _ _; exact v3_phi_1789
  | 410 => intro _ _; exact v3_phi_1790
  | 411 => intro _ _; exact v3_phi_1791
  | 412 => intro _ _; exact v3_phi_1792
  | 413 => intro _ _; exact v3_phi_1793
  | 414 => intro _ _; exact v3_phi_1794
  | 415 => intro _ _; exact v3_phi_1795
  | 416 => intro _ _; exact v3_phi_1796
  | 417 => intro _ _; exact v3_phi_1797
  | 418 => intro _ _; exact v3_phi_1798
  | 419 => intro _ _; exact v3_phi_1799
  | 420 => intro _ _; exact v3_phi_1800
  | 421 => intro _ _; exact v3_phi_1801
  | 422 => intro _ _; exact v3_phi_1802
  | 423 => intro _ _; exact v3_phi_1803
  | 424 => intro _ _; exact v3_phi_1804
  | 425 => intro _ _; exact v3_phi_1805
  | 426 => intro _ _; exact v3_phi_1806
  | 427 => intro _ _; exact v3_phi_1807
  | x + 428 => intro h1 h2; omega

