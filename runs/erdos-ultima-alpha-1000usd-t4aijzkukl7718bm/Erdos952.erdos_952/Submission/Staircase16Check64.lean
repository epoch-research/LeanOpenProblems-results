import Submission.Staircase16Data
namespace Erdos952Investigation.Staircase16
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
lemma row_checked_6400 : RowCheck 6400 := by
  decide +kernel

lemma row_checked_6401 : RowCheck 6401 := by
  decide +kernel

lemma row_checked_6402 : RowCheck 6402 := by
  decide +kernel

lemma row_checked_6403 : RowCheck 6403 := by
  decide +kernel

lemma row_checked_6404 : RowCheck 6404 := by
  decide +kernel

lemma row_checked_6405 : RowCheck 6405 := by
  decide +kernel

lemma row_checked_6406 : RowCheck 6406 := by
  decide +kernel

lemma row_checked_6407 : RowCheck 6407 := by
  decide +kernel

lemma row_checked_6408 : RowCheck 6408 := by
  decide +kernel

lemma row_checked_6409 : RowCheck 6409 := by
  decide +kernel

lemma row_checked_6410 : RowCheck 6410 := by
  decide +kernel

lemma row_checked_6411 : RowCheck 6411 := by
  decide +kernel

lemma row_checked_6412 : RowCheck 6412 := by
  decide +kernel

lemma row_checked_6413 : RowCheck 6413 := by
  decide +kernel

lemma row_checked_6414 : RowCheck 6414 := by
  decide +kernel

lemma row_checked_6415 : RowCheck 6415 := by
  decide +kernel

lemma row_checked_6416 : RowCheck 6416 := by
  decide +kernel

lemma row_checked_6417 : RowCheck 6417 := by
  decide +kernel

lemma row_checked_6418 : RowCheck 6418 := by
  decide +kernel

lemma row_checked_6419 : RowCheck 6419 := by
  decide +kernel

lemma row_checked_6420 : RowCheck 6420 := by
  decide +kernel

lemma row_checked_6421 : RowCheck 6421 := by
  decide +kernel

lemma row_checked_6422 : RowCheck 6422 := by
  decide +kernel

lemma row_checked_6423 : RowCheck 6423 := by
  decide +kernel

lemma row_checked_6424 : RowCheck 6424 := by
  decide +kernel

lemma row_checked_6425 : RowCheck 6425 := by
  decide +kernel

lemma row_checked_6426 : RowCheck 6426 := by
  decide +kernel

lemma row_checked_6427 : RowCheck 6427 := by
  decide +kernel

lemma row_checked_6428 : RowCheck 6428 := by
  decide +kernel

lemma row_checked_6429 : RowCheck 6429 := by
  decide +kernel

lemma row_checked_6430 : RowCheck 6430 := by
  decide +kernel

lemma row_checked_6431 : RowCheck 6431 := by
  decide +kernel

lemma row_checked_6432 : RowCheck 6432 := by
  decide +kernel

lemma row_checked_6433 : RowCheck 6433 := by
  decide +kernel

lemma row_checked_6434 : RowCheck 6434 := by
  decide +kernel

lemma row_checked_6435 : RowCheck 6435 := by
  decide +kernel

lemma row_checked_6436 : RowCheck 6436 := by
  decide +kernel

lemma row_checked_6437 : RowCheck 6437 := by
  decide +kernel

lemma row_checked_6438 : RowCheck 6438 := by
  decide +kernel

lemma block_checked_64 : ∀ r : Fin 39, RowCheck ⟨6400+r.val, by have := r.isLt; simp [radius]; omega⟩ := by
  intro r
  fin_cases r
  · exact row_checked_6400
  · exact row_checked_6401
  · exact row_checked_6402
  · exact row_checked_6403
  · exact row_checked_6404
  · exact row_checked_6405
  · exact row_checked_6406
  · exact row_checked_6407
  · exact row_checked_6408
  · exact row_checked_6409
  · exact row_checked_6410
  · exact row_checked_6411
  · exact row_checked_6412
  · exact row_checked_6413
  · exact row_checked_6414
  · exact row_checked_6415
  · exact row_checked_6416
  · exact row_checked_6417
  · exact row_checked_6418
  · exact row_checked_6419
  · exact row_checked_6420
  · exact row_checked_6421
  · exact row_checked_6422
  · exact row_checked_6423
  · exact row_checked_6424
  · exact row_checked_6425
  · exact row_checked_6426
  · exact row_checked_6427
  · exact row_checked_6428
  · exact row_checked_6429
  · exact row_checked_6430
  · exact row_checked_6431
  · exact row_checked_6432
  · exact row_checked_6433
  · exact row_checked_6434
  · exact row_checked_6435
  · exact row_checked_6436
  · exact row_checked_6437
  · exact row_checked_6438
end Erdos952Investigation.Staircase16
