import Submission.PrimeProof
import Submission.Diffs.Diff0
import Submission.Diffs.Diff1
import Submission.Diffs.Diff2
import Submission.Diffs.Diff3
import Submission.Diffs.Diff4
import Submission.Diffs.Diff5
import Submission.Diffs.Diff6
import Submission.Diffs.Diff7
import Submission.Diffs.Diff8
import Submission.Diffs.Diff9
import Submission.Diffs.Diff10
import Submission.Diffs.Diff11
import Submission.Diffs.Diff12
import Submission.Diffs.Diff13
import Submission.Diffs.Diff14
import Submission.Diffs.Diff15
import Submission.Diffs.Diff16
import Submission.Diffs.Diff17
import Submission.Diffs.Diff18
import Submission.Diffs.Diff19
import Submission.Diffs.Diff20
import Submission.Diffs.Diff21
import Submission.Diffs.Diff22
import Submission.Diffs.Diff23
import Submission.Diffs.Diff24
import Submission.Diffs.Diff25
import Submission.Diffs.Diff26
import Submission.Diffs.Diff27
import Submission.Diffs.Diff28
import Submission.Diffs.Diff29
import Submission.Diffs.Diff30
import Submission.Diffs.Diff31
import Submission.PiVals2

lemma pi_47895 : my_pi 47895 = 4935 :=
  pi_step 47895 47742 153 4922 13 rfl pi_47742 diff_302

lemma pi_48180 : my_pi 48180 = 4960 :=
  pi_step 48180 47895 285 4935 25 rfl pi_47895 diff_303

lemma pi_48205 : my_pi 48205 = 4963 :=
  pi_step 48205 48180 25 4960 3 rfl pi_48180 diff_304

lemma pi_48620 : my_pi 48620 = 5001 :=
  pi_step 48620 48205 415 4963 38 rfl pi_48205 diff_305

lemma pi_49062 : my_pi 49062 = 5043 :=
  pi_step 49062 48620 442 5001 42 rfl pi_48620 diff_306

lemma pi_49141 : my_pi 49141 = 5051 :=
  pi_step 49141 49062 79 5043 8 rfl pi_49062 diff_307

lemma pi_49455 : my_pi 49455 = 5081 :=
  pi_step 49455 49141 314 5051 30 rfl pi_49141 diff_308

lemma pi_49506 : my_pi 49506 = 5086 :=
  pi_step 49506 49455 51 5081 5 rfl pi_49455 diff_309

lemma pi_49952 : my_pi 49952 = 5129 :=
  pi_step 49952 49506 446 5086 43 rfl pi_49506 diff_310

lemma pi_50400 : my_pi 50400 = 5172 :=
  pi_step 50400 49952 448 5129 43 rfl pi_49952 diff_311

lemma pi_50403 : my_pi 50403 = 5172 :=
  pi_step 50403 50400 3 5172 0 rfl pi_50400 diff_312

lemma pi_50721 : my_pi 50721 = 5197 :=
  pi_step 50721 50403 318 5172 25 rfl pi_50403 diff_313

lemma pi_50850 : my_pi 50850 = 5208 :=
  pi_step 50850 50721 129 5197 11 rfl pi_50721 diff_314

lemma pi_51302 : my_pi 51302 = 5248 :=
  pi_step 51302 50850 452 5208 40 rfl pi_50850 diff_315

lemma pi_51360 : my_pi 51360 = 5254 :=
  pi_step 51360 51302 58 5248 6 rfl pi_51302 diff_316

lemma pi_51681 : my_pi 51681 = 5289 :=
  pi_step 51681 51360 321 5254 35 rfl pi_51360 diff_317

lemma pi_51756 : my_pi 51756 = 5295 :=
  pi_step 51756 51681 75 5289 6 rfl pi_51681 diff_318

lemma pi_52212 : my_pi 52212 = 5338 :=
  pi_step 52212 51756 456 5295 43 rfl pi_51756 diff_319

lemma pi_52650 : my_pi 52650 = 5375 :=
  pi_step 52650 52212 438 5338 37 rfl pi_52212 diff_320

lemma pi_52670 : my_pi 52670 = 5376 :=
  pi_step 52670 52650 20 5375 1 rfl pi_52650 diff_321

lemma pi_52975 : my_pi 52975 = 5406 :=
  pi_step 52975 52670 305 5376 30 rfl pi_52670 diff_322

lemma pi_53130 : my_pi 53130 = 5421 :=
  pi_step 53130 52975 155 5406 15 rfl pi_52975 diff_323

lemma pi_53592 : my_pi 53592 = 5459 :=
  pi_step 53592 53130 462 5421 38 rfl pi_53130 diff_324

lemma pi_53956 : my_pi 53956 = 5497 :=
  pi_step 53956 53592 364 5459 38 rfl pi_53592 diff_325

lemma pi_54056 : my_pi 54056 = 5505 :=
  pi_step 54056 53956 100 5497 8 rfl pi_53956 diff_326

lemma pi_54285 : my_pi 54285 = 5521 :=
  pi_step 54285 54056 229 5505 16 rfl pi_54056 diff_327

lemma pi_54522 : my_pi 54522 = 5548 :=
  pi_step 54522 54285 237 5521 27 rfl pi_54285 diff_328

lemma pi_54990 : my_pi 54990 = 5590 :=
  pi_step 54990 54522 468 5548 42 rfl pi_54522 diff_329

lemma pi_55278 : my_pi 55278 = 5615 :=
  pi_step 55278 54990 288 5590 25 rfl pi_54990 diff_330

lemma pi_55460 : my_pi 55460 = 5630 :=
  pi_step 55460 55278 182 5615 15 rfl pi_55278 diff_331

lemma pi_55611 : my_pi 55611 = 5641 :=
  pi_step 55611 55460 151 5630 11 rfl pi_55460 diff_332

lemma pi_55932 : my_pi 55932 = 5678 :=
  pi_step 55932 55611 321 5641 37 rfl pi_55611 diff_333

lemma pi_56280 : my_pi 56280 = 5709 :=
  pi_step 56280 55932 348 5678 31 rfl pi_55932 diff_334

lemma pi_56406 : my_pi 56406 = 5718 :=
  pi_step 56406 56280 126 5709 9 rfl pi_56280 diff_335

lemma pi_56616 : my_pi 56616 = 5741 :=
  pi_step 56616 56406 210 5718 23 rfl pi_56406 diff_336

lemma pi_56882 : my_pi 56882 = 5766 :=
  pi_step 56882 56616 266 5741 25 rfl pi_56616 diff_337

lemma pi_57360 : my_pi 57360 = 5816 :=
  pi_step 57360 56882 478 5766 50 rfl pi_56882 diff_338

lemma pi_57630 : my_pi 57630 = 5836 :=
  pi_step 57630 57360 270 5816 20 rfl pi_57360 diff_339

lemma pi_57840 : my_pi 57840 = 5860 :=
  pi_step 57840 57630 210 5836 24 rfl pi_57630 diff_340

lemma pi_57970 : my_pi 57970 = 5870 :=
  pi_step 57970 57840 130 5860 10 rfl pi_57840 diff_341

lemma pi_58322 : my_pi 58322 = 5905 :=
  pi_step 58322 57970 352 5870 35 rfl pi_57970 diff_342

lemma pi_58806 : my_pi 58806 = 5948 :=
  pi_step 58806 58322 484 5905 43 rfl pi_58322 diff_343

lemma pi_58996 : my_pi 58996 = 5962 :=
  pi_step 58996 58806 190 5948 14 rfl pi_58806 diff_344

lemma pi_59292 : my_pi 59292 = 5995 :=
  pi_step 59292 58996 296 5962 33 rfl pi_58996 diff_345

lemma pi_59340 : my_pi 59340 = 5996 :=
  pi_step 59340 59292 48 5995 1 rfl pi_59292 diff_346

lemma pi_59780 : my_pi 59780 = 6043 :=
  pi_step 59780 59340 440 5996 47 rfl pi_59340 diff_347

lemma pi_60031 : my_pi 60031 = 6060 :=
  pi_step 60031 59780 251 6043 17 rfl pi_59780 diff_348

lemma pi_60270 : my_pi 60270 = 6082 :=
  pi_step 60270 60031 239 6060 22 rfl pi_60031 diff_349

lemma pi_60378 : my_pi 60378 = 6091 :=
  pi_step 60378 60270 108 6082 9 rfl pi_60270 diff_350

lemma pi_60762 : my_pi 60762 = 6125 :=
  pi_step 60762 60378 384 6091 34 rfl pi_60378 diff_351

lemma pi_61256 : my_pi 61256 = 6164 :=
  pi_step 61256 60762 494 6125 39 rfl pi_60762 diff_352

lemma pi_61425 : my_pi 61425 = 6179 :=
  pi_step 61425 61256 169 6164 15 rfl pi_61256 diff_353

lemma pi_61752 : my_pi 61752 = 6213 :=
  pi_step 61752 61425 327 6179 34 rfl pi_61425 diff_354

lemma pi_61776 : my_pi 61776 = 6214 :=
  pi_step 61776 61752 24 6213 1 rfl pi_61752 diff_355

lemma pi_62250 : my_pi 62250 = 6256 :=
  pi_step 62250 61776 474 6214 42 rfl pi_61776 diff_356

lemma pi_62481 : my_pi 62481 = 6273 :=
  pi_step 62481 62250 231 6256 17 rfl pi_62250 diff_357

lemma pi_62750 : my_pi 62750 = 6297 :=
  pi_step 62750 62481 269 6273 24 rfl pi_62481 diff_358

lemma pi_62835 : my_pi 62835 = 6304 :=
  pi_step 62835 62750 85 6297 7 rfl pi_62750 diff_359

lemma pi_63252 : my_pi 63252 = 6338 :=
  pi_step 63252 62835 417 6304 34 rfl pi_62835 diff_360

lemma pi_63546 : my_pi 63546 = 6369 :=
  pi_step 63546 63252 294 6338 31 rfl pi_63252 diff_361

lemma pi_63756 : my_pi 63756 = 6393 :=
  pi_step 63756 63546 210 6369 24 rfl pi_63546 diff_362

lemma pi_63903 : my_pi 63903 = 6407 :=
  pi_step 63903 63756 147 6393 14 rfl pi_63756 diff_363

lemma pi_64262 : my_pi 64262 = 6434 :=
  pi_step 64262 63903 359 6407 27 rfl pi_63903 diff_364

lemma pi_64770 : my_pi 64770 = 6474 :=
  pi_step 64770 64262 508 6434 40 rfl pi_64262 diff_365

lemma pi_64980 : my_pi 64980 = 6492 :=
  pi_step 64980 64770 210 6474 18 rfl pi_64770 diff_366

lemma pi_65280 : my_pi 65280 = 6521 :=
  pi_step 65280 64980 300 6492 29 rfl pi_64980 diff_367

lemma pi_65341 : my_pi 65341 = 6526 :=
  pi_step 65341 65280 61 6521 5 rfl pi_65280 diff_368

lemma pi_65792 : my_pi 65792 = 6572 :=
  pi_step 65792 65341 451 6526 46 rfl pi_65341 diff_369

lemma pi_66066 : my_pi 66066 = 6595 :=
  pi_step 66066 65792 274 6572 23 rfl pi_65792 diff_370

lemma pi_66306 : my_pi 66306 = 6613 :=
  pi_step 66306 66066 240 6595 18 rfl pi_66066 diff_371

lemma pi_66430 : my_pi 66430 = 6623 :=
  pi_step 66430 66306 124 6613 10 rfl pi_66306 diff_372

lemma pi_66822 : my_pi 66822 = 6659 :=
  pi_step 66822 66430 392 6623 36 rfl pi_66430 diff_373

lemma pi_67340 : my_pi 67340 = 6707 :=
  pi_step 67340 66822 518 6659 48 rfl pi_66822 diff_374

lemma pi_67528 : my_pi 67528 = 6727 :=
  pi_step 67528 67340 188 6707 20 rfl pi_67340 diff_375

lemma pi_67860 : my_pi 67860 = 6759 :=
  pi_step 67860 67528 332 6727 32 rfl pi_67528 diff_376

lemma pi_67896 : my_pi 67896 = 6762 :=
  pi_step 67896 67860 36 6759 3 rfl pi_67860 diff_377

lemma pi_68382 : my_pi 68382 = 6800 :=
  pi_step 68382 67896 486 6762 38 rfl pi_67896 diff_378

lemma pi_68635 : my_pi 68635 = 6822 :=
  pi_step 68635 68382 253 6800 22 rfl pi_68382 diff_379

lemma pi_68906 : my_pi 68906 = 6848 :=
  pi_step 68906 68635 271 6822 26 rfl pi_68635 diff_380

lemma pi_69006 : my_pi 69006 = 6855 :=
  pi_step 69006 68906 100 6848 7 rfl pi_68906 diff_381

lemma pi_69432 : my_pi 69432 = 6892 :=
  pi_step 69432 69006 426 6855 37 rfl pi_69006 diff_382

lemma pi_69960 : my_pi 69960 = 6933 :=
  pi_step 69960 69432 528 6892 41 rfl pi_69432 diff_383

lemma pi_70125 : my_pi 70125 = 6949 :=
  pi_step 70125 69960 165 6933 16 rfl pi_69960 diff_384

lemma pi_70490 : my_pi 70490 = 6985 :=
  pi_step 70490 70125 365 6949 36 rfl pi_70125 diff_385

lemma pi_70500 : my_pi 70500 = 6985 :=
  pi_step 70500 70490 10 6985 0 rfl pi_70490 diff_386

lemma pi_71022 : my_pi 71022 = 7034 :=
  pi_step 71022 70500 522 6985 49 rfl pi_70500 diff_387

lemma pi_71253 : my_pi 71253 = 7053 :=
  pi_step 71253 71022 231 7034 19 rfl pi_71022 diff_388

lemma pi_71556 : my_pi 71556 = 7087 :=
  pi_step 71556 71253 303 7053 34 rfl pi_71253 diff_389

lemma pi_71631 : my_pi 71631 = 7091 :=
  pi_step 71631 71556 75 7087 4 rfl pi_71556 diff_390

lemma pi_72092 : my_pi 72092 = 7137 :=
  pi_step 72092 71631 461 7091 46 rfl pi_71631 diff_391

lemma pi_72390 : my_pi 72390 = 7164 :=
  pi_step 72390 72092 298 7137 27 rfl pi_72092 diff_392

lemma pi_72630 : my_pi 72630 = 7181 :=
  pi_step 72630 72390 240 7164 17 rfl pi_72390 diff_393

lemma pi_72771 : my_pi 72771 = 7197 :=
  pi_step 72771 72630 141 7181 16 rfl pi_72630 diff_394

lemma pi_73170 : my_pi 73170 = 7232 :=
  pi_step 73170 72771 399 7197 35 rfl pi_72771 diff_395

lemma pi_73536 : my_pi 73536 = 7260 :=
  pi_step 73536 73170 366 7232 28 rfl pi_73170 diff_396

lemma pi_73712 : my_pi 73712 = 7279 :=
  pi_step 73712 73536 176 7260 19 rfl pi_73536 diff_397

lemma pi_73920 : my_pi 73920 = 7295 :=
  pi_step 73920 73712 208 7279 16 rfl pi_73712 diff_398

lemma pi_74256 : my_pi 74256 = 7325 :=
  pi_step 74256 73920 336 7295 30 rfl pi_73920 diff_399

lemma pi_74691 : my_pi 74691 = 7363 :=
  pi_step 74691 74256 435 7325 38 rfl pi_74256 diff_400

lemma pi_74802 : my_pi 74802 = 7376 :=
  pi_step 74802 74691 111 7363 13 rfl pi_74691 diff_401

lemma pi_75078 : my_pi 75078 = 7399 :=
  pi_step 75078 74802 276 7376 23 rfl pi_74802 diff_402

