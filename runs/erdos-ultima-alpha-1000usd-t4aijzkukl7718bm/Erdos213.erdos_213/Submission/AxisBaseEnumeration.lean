import Submission.AxisBaseBlock0
import Submission.AxisBaseBlock1
import Submission.AxisBaseBlock2
import Submission.AxisBaseBlock3
import Submission.AxisBaseBlock4
import Submission.AxisBaseBlock5
import Submission.AxisBaseBlock6
import Submission.AxisBaseBlock7
import Submission.AxisBaseBlock8
import Submission.AxisBaseBlock9
import Submission.AxisBaseBlock10
import Submission.AxisBaseBlock11
import Submission.AxisBaseBlock12
import Submission.AxisBaseBlock13
import Submission.AxisBaseBlock14
import Submission.AxisBaseBlock15
import Submission.AxisBaseBlock16
import Submission.AxisBaseBlock17
import Submission.AxisBaseBlock18
import Submission.AxisBaseBlock19
import Submission.AxisBaseBlock20
import Submission.AxisBaseBlock21
import Submission.AxisBaseBlock22
import Submission.AxisBaseBlock23
import Submission.AxisBaseBlock24
import Submission.AxisBaseBlock25
import Submission.AxisBaseBlock26
import Submission.AxisBaseBlock27
import Submission.AxisBaseBlock28
import Submission.AxisBaseBlock29
import Submission.AxisBaseBlock30
import Submission.AxisBaseBlock31

/-! Exhaustive kernel-only classification of all 2^21 normalized base signings.
The blocks share cached high-bit coefficients. No compiler-evaluation axiom is used.
This is only an auxiliary non-general-position rank diagnostic. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem group0 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((0*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7
  · exact block8
  · exact block9
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15

private theorem group1 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((1*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
  · exact block31

private theorem group2 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((2*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block32
  · exact block33
  · exact block34
  · exact block35
  · exact block36
  · exact block37
  · exact block38
  · exact block39
  · exact block40
  · exact block41
  · exact block42
  · exact block43
  · exact block44
  · exact block45
  · exact block46
  · exact block47

private theorem group3 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((3*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block48
  · exact block49
  · exact block50
  · exact block51
  · exact block52
  · exact block53
  · exact block54
  · exact block55
  · exact block56
  · exact block57
  · exact block58
  · exact block59
  · exact block60
  · exact block61
  · exact block62
  · exact block63

private theorem group4 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((4*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block64
  · exact block65
  · exact block66
  · exact block67
  · exact block68
  · exact block69
  · exact block70
  · exact block71
  · exact block72
  · exact block73
  · exact block74
  · exact block75
  · exact block76
  · exact block77
  · exact block78
  · exact block79

private theorem group5 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((5*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block80
  · exact block81
  · exact block82
  · exact block83
  · exact block84
  · exact block85
  · exact block86
  · exact block87
  · exact block88
  · exact block89
  · exact block90
  · exact block91
  · exact block92
  · exact block93
  · exact block94
  · exact block95

private theorem group6 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((6*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block96
  · exact block97
  · exact block98
  · exact block99
  · exact block100
  · exact block101
  · exact block102
  · exact block103
  · exact block104
  · exact block105
  · exact block106
  · exact block107
  · exact block108
  · exact block109
  · exact block110
  · exact block111

private theorem group7 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((7*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block112
  · exact block113
  · exact block114
  · exact block115
  · exact block116
  · exact block117
  · exact block118
  · exact block119
  · exact block120
  · exact block121
  · exact block122
  · exact block123
  · exact block124
  · exact block125
  · exact block126
  · exact block127

private theorem group8 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((8*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block128
  · exact block129
  · exact block130
  · exact block131
  · exact block132
  · exact block133
  · exact block134
  · exact block135
  · exact block136
  · exact block137
  · exact block138
  · exact block139
  · exact block140
  · exact block141
  · exact block142
  · exact block143

private theorem group9 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((9*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block144
  · exact block145
  · exact block146
  · exact block147
  · exact block148
  · exact block149
  · exact block150
  · exact block151
  · exact block152
  · exact block153
  · exact block154
  · exact block155
  · exact block156
  · exact block157
  · exact block158
  · exact block159

private theorem group10 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((10*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block160
  · exact block161
  · exact block162
  · exact block163
  · exact block164
  · exact block165
  · exact block166
  · exact block167
  · exact block168
  · exact block169
  · exact block170
  · exact block171
  · exact block172
  · exact block173
  · exact block174
  · exact block175

private theorem group11 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((11*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block176
  · exact block177
  · exact block178
  · exact block179
  · exact block180
  · exact block181
  · exact block182
  · exact block183
  · exact block184
  · exact block185
  · exact block186
  · exact block187
  · exact block188
  · exact block189
  · exact block190
  · exact block191

private theorem group12 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((12*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block192
  · exact block193
  · exact block194
  · exact block195
  · exact block196
  · exact block197
  · exact block198
  · exact block199
  · exact block200
  · exact block201
  · exact block202
  · exact block203
  · exact block204
  · exact block205
  · exact block206
  · exact block207

private theorem group13 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((13*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block208
  · exact block209
  · exact block210
  · exact block211
  · exact block212
  · exact block213
  · exact block214
  · exact block215
  · exact block216
  · exact block217
  · exact block218
  · exact block219
  · exact block220
  · exact block221
  · exact block222
  · exact block223

private theorem group14 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((14*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block224
  · exact block225
  · exact block226
  · exact block227
  · exact block228
  · exact block229
  · exact block230
  · exact block231
  · exact block232
  · exact block233
  · exact block234
  · exact block235
  · exact block236
  · exact block237
  · exact block238
  · exact block239

private theorem group15 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((15*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block240
  · exact block241
  · exact block242
  · exact block243
  · exact block244
  · exact block245
  · exact block246
  · exact block247
  · exact block248
  · exact block249
  · exact block250
  · exact block251
  · exact block252
  · exact block253
  · exact block254
  · exact block255

private theorem group16 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((16*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block256
  · exact block257
  · exact block258
  · exact block259
  · exact block260
  · exact block261
  · exact block262
  · exact block263
  · exact block264
  · exact block265
  · exact block266
  · exact block267
  · exact block268
  · exact block269
  · exact block270
  · exact block271

private theorem group17 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((17*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block272
  · exact block273
  · exact block274
  · exact block275
  · exact block276
  · exact block277
  · exact block278
  · exact block279
  · exact block280
  · exact block281
  · exact block282
  · exact block283
  · exact block284
  · exact block285
  · exact block286
  · exact block287

private theorem group18 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((18*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block288
  · exact block289
  · exact block290
  · exact block291
  · exact block292
  · exact block293
  · exact block294
  · exact block295
  · exact block296
  · exact block297
  · exact block298
  · exact block299
  · exact block300
  · exact block301
  · exact block302
  · exact block303

private theorem group19 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((19*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block304
  · exact block305
  · exact block306
  · exact block307
  · exact block308
  · exact block309
  · exact block310
  · exact block311
  · exact block312
  · exact block313
  · exact block314
  · exact block315
  · exact block316
  · exact block317
  · exact block318
  · exact block319

private theorem group20 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((20*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block320
  · exact block321
  · exact block322
  · exact block323
  · exact block324
  · exact block325
  · exact block326
  · exact block327
  · exact block328
  · exact block329
  · exact block330
  · exact block331
  · exact block332
  · exact block333
  · exact block334
  · exact block335

private theorem group21 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((21*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block336
  · exact block337
  · exact block338
  · exact block339
  · exact block340
  · exact block341
  · exact block342
  · exact block343
  · exact block344
  · exact block345
  · exact block346
  · exact block347
  · exact block348
  · exact block349
  · exact block350
  · exact block351

private theorem group22 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((22*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block352
  · exact block353
  · exact block354
  · exact block355
  · exact block356
  · exact block357
  · exact block358
  · exact block359
  · exact block360
  · exact block361
  · exact block362
  · exact block363
  · exact block364
  · exact block365
  · exact block366
  · exact block367

private theorem group23 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((23*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block368
  · exact block369
  · exact block370
  · exact block371
  · exact block372
  · exact block373
  · exact block374
  · exact block375
  · exact block376
  · exact block377
  · exact block378
  · exact block379
  · exact block380
  · exact block381
  · exact block382
  · exact block383

private theorem group24 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((24*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block384
  · exact block385
  · exact block386
  · exact block387
  · exact block388
  · exact block389
  · exact block390
  · exact block391
  · exact block392
  · exact block393
  · exact block394
  · exact block395
  · exact block396
  · exact block397
  · exact block398
  · exact block399

private theorem group25 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((25*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block400
  · exact block401
  · exact block402
  · exact block403
  · exact block404
  · exact block405
  · exact block406
  · exact block407
  · exact block408
  · exact block409
  · exact block410
  · exact block411
  · exact block412
  · exact block413
  · exact block414
  · exact block415

private theorem group26 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((26*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block416
  · exact block417
  · exact block418
  · exact block419
  · exact block420
  · exact block421
  · exact block422
  · exact block423
  · exact block424
  · exact block425
  · exact block426
  · exact block427
  · exact block428
  · exact block429
  · exact block430
  · exact block431

private theorem group27 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((27*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block432
  · exact block433
  · exact block434
  · exact block435
  · exact block436
  · exact block437
  · exact block438
  · exact block439
  · exact block440
  · exact block441
  · exact block442
  · exact block443
  · exact block444
  · exact block445
  · exact block446
  · exact block447

private theorem group28 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((28*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block448
  · exact block449
  · exact block450
  · exact block451
  · exact block452
  · exact block453
  · exact block454
  · exact block455
  · exact block456
  · exact block457
  · exact block458
  · exact block459
  · exact block460
  · exact block461
  · exact block462
  · exact block463

private theorem group29 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((29*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block464
  · exact block465
  · exact block466
  · exact block467
  · exact block468
  · exact block469
  · exact block470
  · exact block471
  · exact block472
  · exact block473
  · exact block474
  · exact block475
  · exact block476
  · exact block477
  · exact block478
  · exact block479

private theorem group30 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((30*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block480
  · exact block481
  · exact block482
  · exact block483
  · exact block484
  · exact block485
  · exact block486
  · exact block487
  · exact block488
  · exact block489
  · exact block490
  · exact block491
  · exact block492
  · exact block493
  · exact block494
  · exact block495

private theorem group31 (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((31*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases r
  · exact block496
  · exact block497
  · exact block498
  · exact block499
  · exact block500
  · exact block501
  · exact block502
  · exact block503
  · exact block504
  · exact block505
  · exact block506
  · exact block507
  · exact block508
  · exact block509
  · exact block510
  · exact block511

private theorem all_groups (g : Fin 32) (r : Fin 16) : ∀ hi lo : Fin 64,
    checked ((g.val*16+r.val)*64+hi.val) lo.val=true := by
  fin_cases g
  · exact group0 r
  · exact group1 r
  · exact group2 r
  · exact group3 r
  · exact group4 r
  · exact group5 r
  · exact group6 r
  · exact group7 r
  · exact group8 r
  · exact group9 r
  · exact group10 r
  · exact group11 r
  · exact group12 r
  · exact group13 r
  · exact group14 r
  · exact group15 r
  · exact group16 r
  · exact group17 r
  · exact group18 r
  · exact group19 r
  · exact group20 r
  · exact group21 r
  · exact group22 r
  · exact group23 r
  · exact group24 r
  · exact group25 r
  · exact group26 r
  · exact group27 r
  · exact group28 r
  · exact group29 r
  · exact group30 r
  · exact group31 r

private theorem all_blocks (b : Fin 512) : ∀ hi lo : Fin 64,
    checked (b.val*64+hi.val) lo.val=true := by
  intro hi lo
  have hg : b.val/16<32 := by omega
  have hr : b.val%16<16 := Nat.mod_lt _ (by decide)
  have h := all_groups ⟨b.val/16,hg⟩ ⟨b.val%16,hr⟩ hi lo
  simp only at h
  have he : b.val/16*16+b.val%16=b.val := by omega
  simpa only [he] using h

/-- This covers all old signs; the list is not assumed complete as an input. -/
theorem all_checked (hi lo : ℕ) (hh : hi<32768) (hl : lo<64) :
    checked hi lo=true := by
  have hb : hi/64<512 := by omega
  have hr : hi%64<64 := Nat.mod_lt _ (by decide)
  have h := all_blocks ⟨hi/64,hb⟩ ⟨hi%64,hr⟩ ⟨lo,hl⟩
  simp only at h
  have he : hi/64*64+hi%64=hi := by omega
  simpa only [he] using h

#print axioms all_checked
end Erdos213.AxisBaseCompleteness
