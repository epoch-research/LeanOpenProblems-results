import Submission.FiniteIntervals
import Submission.SixRepresentativeCertificates1_000
import Submission.SixRepresentativeCertificates1_001
import Submission.SixRepresentativeCertificates1_002
import Submission.SixRepresentativeCertificates1_003
import Submission.SixRepresentativeCertificates1_004
import Submission.SixRepresentativeCertificates1_005
import Submission.SixRepresentativeCertificates1_006
import Submission.SixRepresentativeCertificates1_007

namespace Erdos184Work.SixRepresentativeCertificates1
open PureSixRowModel1 LabelKernel Erdos184Serial
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
def CertificateIndex (j : ℕ) : Prop := ∀ hj : j < 387, Certificate ⟨j,hj⟩
lemma certificate_interval00 : FiniteIntervals.Covers CertificateIndex 0 16 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 0 16
  intro i
  fin_cases i
  · intro hj
    exact certificate0
  · intro hj
    exact certificate1
  · intro hj
    exact certificate2
  · intro hj
    exact certificate3
  · intro hj
    exact certificate4
  · intro hj
    exact certificate5
  · intro hj
    exact certificate6
  · intro hj
    exact certificate7
  · intro hj
    exact certificate8
  · intro hj
    exact certificate9
  · intro hj
    exact certificate10
  · intro hj
    exact certificate11
  · intro hj
    exact certificate12
  · intro hj
    exact certificate13
  · intro hj
    exact certificate14
  · intro hj
    exact certificate15
lemma certificate_interval01 : FiniteIntervals.Covers CertificateIndex 16 32 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 16 16
  intro i
  fin_cases i
  · intro hj
    exact certificate16
  · intro hj
    exact certificate17
  · intro hj
    exact certificate18
  · intro hj
    exact certificate19
  · intro hj
    exact certificate20
  · intro hj
    exact certificate21
  · intro hj
    exact certificate22
  · intro hj
    exact certificate23
  · intro hj
    exact certificate24
  · intro hj
    exact certificate25
  · intro hj
    exact certificate26
  · intro hj
    exact certificate27
  · intro hj
    exact certificate28
  · intro hj
    exact certificate29
  · intro hj
    exact certificate30
  · intro hj
    exact certificate31
lemma certificate_interval02 : FiniteIntervals.Covers CertificateIndex 32 48 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 32 16
  intro i
  fin_cases i
  · intro hj
    exact certificate32
  · intro hj
    exact certificate33
  · intro hj
    exact certificate34
  · intro hj
    exact certificate35
  · intro hj
    exact certificate36
  · intro hj
    exact certificate37
  · intro hj
    exact certificate38
  · intro hj
    exact certificate39
  · intro hj
    exact certificate40
  · intro hj
    exact certificate41
  · intro hj
    exact certificate42
  · intro hj
    exact certificate43
  · intro hj
    exact certificate44
  · intro hj
    exact certificate45
  · intro hj
    exact certificate46
  · intro hj
    exact certificate47
lemma certificate_interval03 : FiniteIntervals.Covers CertificateIndex 48 64 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 48 16
  intro i
  fin_cases i
  · intro hj
    exact certificate48
  · intro hj
    exact certificate49
  · intro hj
    exact certificate50
  · intro hj
    exact certificate51
  · intro hj
    exact certificate52
  · intro hj
    exact certificate53
  · intro hj
    exact certificate54
  · intro hj
    exact certificate55
  · intro hj
    exact certificate56
  · intro hj
    exact certificate57
  · intro hj
    exact certificate58
  · intro hj
    exact certificate59
  · intro hj
    exact certificate60
  · intro hj
    exact certificate61
  · intro hj
    exact certificate62
  · intro hj
    exact certificate63
lemma certificate_interval04 : FiniteIntervals.Covers CertificateIndex 64 80 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 64 16
  intro i
  fin_cases i
  · intro hj
    exact certificate64
  · intro hj
    exact certificate65
  · intro hj
    exact certificate66
  · intro hj
    exact certificate67
  · intro hj
    exact certificate68
  · intro hj
    exact certificate69
  · intro hj
    exact certificate70
  · intro hj
    exact certificate71
  · intro hj
    exact certificate72
  · intro hj
    exact certificate73
  · intro hj
    exact certificate74
  · intro hj
    exact certificate75
  · intro hj
    exact certificate76
  · intro hj
    exact certificate77
  · intro hj
    exact certificate78
  · intro hj
    exact certificate79
lemma certificate_interval05 : FiniteIntervals.Covers CertificateIndex 80 96 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 80 16
  intro i
  fin_cases i
  · intro hj
    exact certificate80
  · intro hj
    exact certificate81
  · intro hj
    exact certificate82
  · intro hj
    exact certificate83
  · intro hj
    exact certificate84
  · intro hj
    exact certificate85
  · intro hj
    exact certificate86
  · intro hj
    exact certificate87
  · intro hj
    exact certificate88
  · intro hj
    exact certificate89
  · intro hj
    exact certificate90
  · intro hj
    exact certificate91
  · intro hj
    exact certificate92
  · intro hj
    exact certificate93
  · intro hj
    exact certificate94
  · intro hj
    exact certificate95
lemma certificate_interval06 : FiniteIntervals.Covers CertificateIndex 96 112 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 96 16
  intro i
  fin_cases i
  · intro hj
    exact certificate96
  · intro hj
    exact certificate97
  · intro hj
    exact certificate98
  · intro hj
    exact certificate99
  · intro hj
    exact certificate100
  · intro hj
    exact certificate101
  · intro hj
    exact certificate102
  · intro hj
    exact certificate103
  · intro hj
    exact certificate104
  · intro hj
    exact certificate105
  · intro hj
    exact certificate106
  · intro hj
    exact certificate107
  · intro hj
    exact certificate108
  · intro hj
    exact certificate109
  · intro hj
    exact certificate110
  · intro hj
    exact certificate111
lemma certificate_interval07 : FiniteIntervals.Covers CertificateIndex 112 128 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 112 16
  intro i
  fin_cases i
  · intro hj
    exact certificate112
  · intro hj
    exact certificate113
  · intro hj
    exact certificate114
  · intro hj
    exact certificate115
  · intro hj
    exact certificate116
  · intro hj
    exact certificate117
  · intro hj
    exact certificate118
  · intro hj
    exact certificate119
  · intro hj
    exact certificate120
  · intro hj
    exact certificate121
  · intro hj
    exact certificate122
  · intro hj
    exact certificate123
  · intro hj
    exact certificate124
  · intro hj
    exact certificate125
  · intro hj
    exact certificate126
  · intro hj
    exact certificate127
lemma certificate_interval08 : FiniteIntervals.Covers CertificateIndex 128 144 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 128 16
  intro i
  fin_cases i
  · intro hj
    exact certificate128
  · intro hj
    exact certificate129
  · intro hj
    exact certificate130
  · intro hj
    exact certificate131
  · intro hj
    exact certificate132
  · intro hj
    exact certificate133
  · intro hj
    exact certificate134
  · intro hj
    exact certificate135
  · intro hj
    exact certificate136
  · intro hj
    exact certificate137
  · intro hj
    exact certificate138
  · intro hj
    exact certificate139
  · intro hj
    exact certificate140
  · intro hj
    exact certificate141
  · intro hj
    exact certificate142
  · intro hj
    exact certificate143
lemma certificate_interval09 : FiniteIntervals.Covers CertificateIndex 144 160 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 144 16
  intro i
  fin_cases i
  · intro hj
    exact certificate144
  · intro hj
    exact certificate145
  · intro hj
    exact certificate146
  · intro hj
    exact certificate147
  · intro hj
    exact certificate148
  · intro hj
    exact certificate149
  · intro hj
    exact certificate150
  · intro hj
    exact certificate151
  · intro hj
    exact certificate152
  · intro hj
    exact certificate153
  · intro hj
    exact certificate154
  · intro hj
    exact certificate155
  · intro hj
    exact certificate156
  · intro hj
    exact certificate157
  · intro hj
    exact certificate158
  · intro hj
    exact certificate159
lemma certificate_interval10 : FiniteIntervals.Covers CertificateIndex 160 176 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 160 16
  intro i
  fin_cases i
  · intro hj
    exact certificate160
  · intro hj
    exact certificate161
  · intro hj
    exact certificate162
  · intro hj
    exact certificate163
  · intro hj
    exact certificate164
  · intro hj
    exact certificate165
  · intro hj
    exact certificate166
  · intro hj
    exact certificate167
  · intro hj
    exact certificate168
  · intro hj
    exact certificate169
  · intro hj
    exact certificate170
  · intro hj
    exact certificate171
  · intro hj
    exact certificate172
  · intro hj
    exact certificate173
  · intro hj
    exact certificate174
  · intro hj
    exact certificate175
lemma certificate_interval11 : FiniteIntervals.Covers CertificateIndex 176 192 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 176 16
  intro i
  fin_cases i
  · intro hj
    exact certificate176
  · intro hj
    exact certificate177
  · intro hj
    exact certificate178
  · intro hj
    exact certificate179
  · intro hj
    exact certificate180
  · intro hj
    exact certificate181
  · intro hj
    exact certificate182
  · intro hj
    exact certificate183
  · intro hj
    exact certificate184
  · intro hj
    exact certificate185
  · intro hj
    exact certificate186
  · intro hj
    exact certificate187
  · intro hj
    exact certificate188
  · intro hj
    exact certificate189
  · intro hj
    exact certificate190
  · intro hj
    exact certificate191
lemma certificate_interval12 : FiniteIntervals.Covers CertificateIndex 192 208 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 192 16
  intro i
  fin_cases i
  · intro hj
    exact certificate192
  · intro hj
    exact certificate193
  · intro hj
    exact certificate194
  · intro hj
    exact certificate195
  · intro hj
    exact certificate196
  · intro hj
    exact certificate197
  · intro hj
    exact certificate198
  · intro hj
    exact certificate199
  · intro hj
    exact certificate200
  · intro hj
    exact certificate201
  · intro hj
    exact certificate202
  · intro hj
    exact certificate203
  · intro hj
    exact certificate204
  · intro hj
    exact certificate205
  · intro hj
    exact certificate206
  · intro hj
    exact certificate207
lemma certificate_interval13 : FiniteIntervals.Covers CertificateIndex 208 224 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 208 16
  intro i
  fin_cases i
  · intro hj
    exact certificate208
  · intro hj
    exact certificate209
  · intro hj
    exact certificate210
  · intro hj
    exact certificate211
  · intro hj
    exact certificate212
  · intro hj
    exact certificate213
  · intro hj
    exact certificate214
  · intro hj
    exact certificate215
  · intro hj
    exact certificate216
  · intro hj
    exact certificate217
  · intro hj
    exact certificate218
  · intro hj
    exact certificate219
  · intro hj
    exact certificate220
  · intro hj
    exact certificate221
  · intro hj
    exact certificate222
  · intro hj
    exact certificate223
lemma certificate_interval14 : FiniteIntervals.Covers CertificateIndex 224 240 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 224 16
  intro i
  fin_cases i
  · intro hj
    exact certificate224
  · intro hj
    exact certificate225
  · intro hj
    exact certificate226
  · intro hj
    exact certificate227
  · intro hj
    exact certificate228
  · intro hj
    exact certificate229
  · intro hj
    exact certificate230
  · intro hj
    exact certificate231
  · intro hj
    exact certificate232
  · intro hj
    exact certificate233
  · intro hj
    exact certificate234
  · intro hj
    exact certificate235
  · intro hj
    exact certificate236
  · intro hj
    exact certificate237
  · intro hj
    exact certificate238
  · intro hj
    exact certificate239
lemma certificate_interval15 : FiniteIntervals.Covers CertificateIndex 240 256 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 240 16
  intro i
  fin_cases i
  · intro hj
    exact certificate240
  · intro hj
    exact certificate241
  · intro hj
    exact certificate242
  · intro hj
    exact certificate243
  · intro hj
    exact certificate244
  · intro hj
    exact certificate245
  · intro hj
    exact certificate246
  · intro hj
    exact certificate247
  · intro hj
    exact certificate248
  · intro hj
    exact certificate249
  · intro hj
    exact certificate250
  · intro hj
    exact certificate251
  · intro hj
    exact certificate252
  · intro hj
    exact certificate253
  · intro hj
    exact certificate254
  · intro hj
    exact certificate255
lemma certificate_interval16 : FiniteIntervals.Covers CertificateIndex 256 272 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 256 16
  intro i
  fin_cases i
  · intro hj
    exact certificate256
  · intro hj
    exact certificate257
  · intro hj
    exact certificate258
  · intro hj
    exact certificate259
  · intro hj
    exact certificate260
  · intro hj
    exact certificate261
  · intro hj
    exact certificate262
  · intro hj
    exact certificate263
  · intro hj
    exact certificate264
  · intro hj
    exact certificate265
  · intro hj
    exact certificate266
  · intro hj
    exact certificate267
  · intro hj
    exact certificate268
  · intro hj
    exact certificate269
  · intro hj
    exact certificate270
  · intro hj
    exact certificate271
lemma certificate_interval17 : FiniteIntervals.Covers CertificateIndex 272 288 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 272 16
  intro i
  fin_cases i
  · intro hj
    exact certificate272
  · intro hj
    exact certificate273
  · intro hj
    exact certificate274
  · intro hj
    exact certificate275
  · intro hj
    exact certificate276
  · intro hj
    exact certificate277
  · intro hj
    exact certificate278
  · intro hj
    exact certificate279
  · intro hj
    exact certificate280
  · intro hj
    exact certificate281
  · intro hj
    exact certificate282
  · intro hj
    exact certificate283
  · intro hj
    exact certificate284
  · intro hj
    exact certificate285
  · intro hj
    exact certificate286
  · intro hj
    exact certificate287
lemma certificate_interval18 : FiniteIntervals.Covers CertificateIndex 288 304 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 288 16
  intro i
  fin_cases i
  · intro hj
    exact certificate288
  · intro hj
    exact certificate289
  · intro hj
    exact certificate290
  · intro hj
    exact certificate291
  · intro hj
    exact certificate292
  · intro hj
    exact certificate293
  · intro hj
    exact certificate294
  · intro hj
    exact certificate295
  · intro hj
    exact certificate296
  · intro hj
    exact certificate297
  · intro hj
    exact certificate298
  · intro hj
    exact certificate299
  · intro hj
    exact certificate300
  · intro hj
    exact certificate301
  · intro hj
    exact certificate302
  · intro hj
    exact certificate303
lemma certificate_interval19 : FiniteIntervals.Covers CertificateIndex 304 320 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 304 16
  intro i
  fin_cases i
  · intro hj
    exact certificate304
  · intro hj
    exact certificate305
  · intro hj
    exact certificate306
  · intro hj
    exact certificate307
  · intro hj
    exact certificate308
  · intro hj
    exact certificate309
  · intro hj
    exact certificate310
  · intro hj
    exact certificate311
  · intro hj
    exact certificate312
  · intro hj
    exact certificate313
  · intro hj
    exact certificate314
  · intro hj
    exact certificate315
  · intro hj
    exact certificate316
  · intro hj
    exact certificate317
  · intro hj
    exact certificate318
  · intro hj
    exact certificate319
lemma certificate_interval20 : FiniteIntervals.Covers CertificateIndex 320 336 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 320 16
  intro i
  fin_cases i
  · intro hj
    exact certificate320
  · intro hj
    exact certificate321
  · intro hj
    exact certificate322
  · intro hj
    exact certificate323
  · intro hj
    exact certificate324
  · intro hj
    exact certificate325
  · intro hj
    exact certificate326
  · intro hj
    exact certificate327
  · intro hj
    exact certificate328
  · intro hj
    exact certificate329
  · intro hj
    exact certificate330
  · intro hj
    exact certificate331
  · intro hj
    exact certificate332
  · intro hj
    exact certificate333
  · intro hj
    exact certificate334
  · intro hj
    exact certificate335
lemma certificate_interval21 : FiniteIntervals.Covers CertificateIndex 336 352 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 336 16
  intro i
  fin_cases i
  · intro hj
    exact certificate336
  · intro hj
    exact certificate337
  · intro hj
    exact certificate338
  · intro hj
    exact certificate339
  · intro hj
    exact certificate340
  · intro hj
    exact certificate341
  · intro hj
    exact certificate342
  · intro hj
    exact certificate343
  · intro hj
    exact certificate344
  · intro hj
    exact certificate345
  · intro hj
    exact certificate346
  · intro hj
    exact certificate347
  · intro hj
    exact certificate348
  · intro hj
    exact certificate349
  · intro hj
    exact certificate350
  · intro hj
    exact certificate351
lemma certificate_interval22 : FiniteIntervals.Covers CertificateIndex 352 368 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 352 16
  intro i
  fin_cases i
  · intro hj
    exact certificate352
  · intro hj
    exact certificate353
  · intro hj
    exact certificate354
  · intro hj
    exact certificate355
  · intro hj
    exact certificate356
  · intro hj
    exact certificate357
  · intro hj
    exact certificate358
  · intro hj
    exact certificate359
  · intro hj
    exact certificate360
  · intro hj
    exact certificate361
  · intro hj
    exact certificate362
  · intro hj
    exact certificate363
  · intro hj
    exact certificate364
  · intro hj
    exact certificate365
  · intro hj
    exact certificate366
  · intro hj
    exact certificate367
lemma certificate_interval23 : FiniteIntervals.Covers CertificateIndex 368 384 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 368 16
  intro i
  fin_cases i
  · intro hj
    exact certificate368
  · intro hj
    exact certificate369
  · intro hj
    exact certificate370
  · intro hj
    exact certificate371
  · intro hj
    exact certificate372
  · intro hj
    exact certificate373
  · intro hj
    exact certificate374
  · intro hj
    exact certificate375
  · intro hj
    exact certificate376
  · intro hj
    exact certificate377
  · intro hj
    exact certificate378
  · intro hj
    exact certificate379
  · intro hj
    exact certificate380
  · intro hj
    exact certificate381
  · intro hj
    exact certificate382
  · intro hj
    exact certificate383
lemma certificate_interval24 : FiniteIntervals.Covers CertificateIndex 384 387 := by
  apply FiniteIntervals.of_fin (P := CertificateIndex) 384 3
  intro i
  fin_cases i
  · intro hj
    exact certificate384
  · intro hj
    exact certificate385
  · intro hj
    exact certificate386
lemma certificates (r : Representatives) : Certificate r := by
  have hc : FiniteIntervals.Covers CertificateIndex 0 387 := (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge certificate_interval00 (FiniteIntervals.merge certificate_interval01 certificate_interval02)) (FiniteIntervals.merge certificate_interval03 (FiniteIntervals.merge certificate_interval04 certificate_interval05))) (FiniteIntervals.merge (FiniteIntervals.merge certificate_interval06 (FiniteIntervals.merge certificate_interval07 certificate_interval08)) (FiniteIntervals.merge certificate_interval09 (FiniteIntervals.merge certificate_interval10 certificate_interval11)))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge certificate_interval12 (FiniteIntervals.merge certificate_interval13 certificate_interval14)) (FiniteIntervals.merge certificate_interval15 (FiniteIntervals.merge certificate_interval16 certificate_interval17))) (FiniteIntervals.merge (FiniteIntervals.merge certificate_interval18 (FiniteIntervals.merge certificate_interval19 certificate_interval20)) (FiniteIntervals.merge (FiniteIntervals.merge certificate_interval21 certificate_interval22) (FiniteIntervals.merge certificate_interval23 certificate_interval24)))))
  exact hc r.val (Nat.zero_le _) r.isLt r.isLt
lemma exists_two_of_upper (r : Representatives)
    (hu : ∀ P, Partition (code (src (unkey (representativeKey r)))
      (dst (unkey (representativeKey r)))) Finset.univ P → P.card ≤ 6) :
    r ∈ good ∧ ∃ P, Partition (code (src (unkey (representativeKey r)))
      (dst (unkey (representativeKey r)))) Finset.univ P ∧ P.card = 2 := by
  obtain ⟨D,hd,hs⟩ := certificates r
  obtain ⟨P,hP,hcP⟩ := PartitionData.exists_partition hd
  have hh := hu P hP
  have hz : D.size ≤ 6 := by omega
  obtain ⟨he,hg⟩ := hs hz
  exact ⟨hg,P,hP,hcP.trans he⟩
#print axioms exists_two_of_upper
end Erdos184Work.SixRepresentativeCertificates1
