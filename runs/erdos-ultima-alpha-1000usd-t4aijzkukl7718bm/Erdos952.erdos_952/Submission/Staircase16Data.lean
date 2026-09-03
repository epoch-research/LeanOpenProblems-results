import Submission.ComponentEight
import Submission.OctantReduction

/-! A compact staircase boundary for a bound-sixteen fixed-seed moat.
The following data are untrusted; the separate row checks verify closure. -/
namespace Erdos952Investigation.Staircase16
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def radius : ℕ := 6438

def rowDataBlock0 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 50
(.branch 25
(.branch 12
(.branch 6
(.branch 3
(.branch 1
(.leaf (3341, 3339, 0))
(.branch 2
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 4
(.leaf (3341, 3339, 0))
(.branch 5
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 9
(.branch 7
(.leaf (3341, 3339, 0))
(.branch 8
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 10
(.leaf (3341, 3339, 0))
(.branch 11
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 18
(.branch 15
(.branch 13
(.leaf (3341, 3339, 0))
(.branch 14
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 16
(.leaf (3341, 3339, 0))
(.branch 17
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 21
(.branch 19
(.leaf (3341, 3339, 0))
(.branch 20
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 23
(.branch 22
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 24
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 37
(.branch 31
(.branch 28
(.branch 26
(.leaf (3341, 3339, 0))
(.branch 27
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 29
(.leaf (3341, 3339, 0))
(.branch 30
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 34
(.branch 32
(.leaf (3341, 3339, 0))
(.branch 33
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 35
(.leaf (3341, 3339, 0))
(.branch 36
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 43
(.branch 40
(.branch 38
(.leaf (3341, 3339, 0))
(.branch 39
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 41
(.leaf (3341, 3339, 0))
(.branch 42
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 46
(.branch 44
(.leaf (3341, 3339, 0))
(.branch 45
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 48
(.branch 47
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 49
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 75
(.branch 62
(.branch 56
(.branch 53
(.branch 51
(.leaf (3341, 3339, 0))
(.branch 52
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 54
(.leaf (3341, 3339, 0))
(.branch 55
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 59
(.branch 57
(.leaf (3341, 3339, 0))
(.branch 58
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 60
(.leaf (3341, 3339, 0))
(.branch 61
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 68
(.branch 65
(.branch 63
(.leaf (3341, 3339, 0))
(.branch 64
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 66
(.leaf (3341, 3339, 0))
(.branch 67
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 71
(.branch 69
(.leaf (3341, 3339, 0))
(.branch 70
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 73
(.branch 72
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 74
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 87
(.branch 81
(.branch 78
(.branch 76
(.leaf (3341, 3339, 0))
(.branch 77
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 79
(.leaf (3341, 3339, 0))
(.branch 80
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 84
(.branch 82
(.leaf (3341, 3339, 0))
(.branch 83
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 85
(.leaf (3341, 3339, 0))
(.branch 86
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 93
(.branch 90
(.branch 88
(.leaf (3341, 3339, 0))
(.branch 89
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 91
(.leaf (3341, 3339, 0))
(.branch 92
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 96
(.branch 94
(.leaf (3341, 3339, 0))
(.branch 95
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 98
(.branch 97
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 99
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock1 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 150
(.branch 125
(.branch 112
(.branch 106
(.branch 103
(.branch 101
(.leaf (3341, 3339, 0))
(.branch 102
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 104
(.leaf (3341, 3339, 0))
(.branch 105
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 109
(.branch 107
(.leaf (3341, 3339, 0))
(.branch 108
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 110
(.leaf (3341, 3339, 0))
(.branch 111
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 118
(.branch 115
(.branch 113
(.leaf (3341, 3339, 0))
(.branch 114
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 116
(.leaf (3341, 3339, 0))
(.branch 117
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 121
(.branch 119
(.leaf (3341, 3339, 0))
(.branch 120
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 123
(.branch 122
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 124
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 137
(.branch 131
(.branch 128
(.branch 126
(.leaf (3341, 3339, 0))
(.branch 127
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 129
(.leaf (3341, 3339, 0))
(.branch 130
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 134
(.branch 132
(.leaf (3341, 3339, 0))
(.branch 133
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 135
(.leaf (3341, 3339, 0))
(.branch 136
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 143
(.branch 140
(.branch 138
(.leaf (3341, 3339, 0))
(.branch 139
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 141
(.leaf (3341, 3339, 0))
(.branch 142
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 146
(.branch 144
(.leaf (3341, 3339, 0))
(.branch 145
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 148
(.branch 147
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 149
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 175
(.branch 162
(.branch 156
(.branch 153
(.branch 151
(.leaf (3341, 3339, 0))
(.branch 152
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 154
(.leaf (3341, 3339, 0))
(.branch 155
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 159
(.branch 157
(.leaf (3341, 3339, 0))
(.branch 158
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 160
(.leaf (3341, 3339, 0))
(.branch 161
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 168
(.branch 165
(.branch 163
(.leaf (3341, 3339, 0))
(.branch 164
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 166
(.leaf (3341, 3339, 0))
(.branch 167
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 171
(.branch 169
(.leaf (3341, 3339, 0))
(.branch 170
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 173
(.branch 172
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 174
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 187
(.branch 181
(.branch 178
(.branch 176
(.leaf (3341, 3339, 0))
(.branch 177
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 179
(.leaf (3341, 3339, 0))
(.branch 180
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 184
(.branch 182
(.leaf (3341, 3339, 0))
(.branch 183
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 185
(.leaf (3341, 3339, 0))
(.branch 186
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 193
(.branch 190
(.branch 188
(.leaf (3341, 3339, 0))
(.branch 189
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 191
(.leaf (3341, 3339, 0))
(.branch 192
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 196
(.branch 194
(.leaf (3341, 3339, 0))
(.branch 195
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 198
(.branch 197
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 199
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock2 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 250
(.branch 225
(.branch 212
(.branch 206
(.branch 203
(.branch 201
(.leaf (3341, 3339, 0))
(.branch 202
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 204
(.leaf (3341, 3339, 0))
(.branch 205
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 209
(.branch 207
(.leaf (3341, 3339, 0))
(.branch 208
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 210
(.leaf (3341, 3339, 0))
(.branch 211
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 218
(.branch 215
(.branch 213
(.leaf (3341, 3339, 0))
(.branch 214
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 216
(.leaf (3341, 3339, 0))
(.branch 217
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 221
(.branch 219
(.leaf (3341, 3339, 0))
(.branch 220
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 223
(.branch 222
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 224
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 237
(.branch 231
(.branch 228
(.branch 226
(.leaf (3341, 3339, 0))
(.branch 227
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 229
(.leaf (3341, 3339, 0))
(.branch 230
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 234
(.branch 232
(.leaf (3341, 3339, 0))
(.branch 233
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 235
(.leaf (3341, 3339, 0))
(.branch 236
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 243
(.branch 240
(.branch 238
(.leaf (3341, 3339, 0))
(.branch 239
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 241
(.leaf (3341, 3339, 0))
(.branch 242
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 246
(.branch 244
(.leaf (3341, 3339, 0))
(.branch 245
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 248
(.branch 247
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 249
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 275
(.branch 262
(.branch 256
(.branch 253
(.branch 251
(.leaf (3341, 3339, 0))
(.branch 252
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 254
(.leaf (3341, 3339, 0))
(.branch 255
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 259
(.branch 257
(.leaf (3341, 3339, 0))
(.branch 258
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 260
(.leaf (3341, 3339, 0))
(.branch 261
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 268
(.branch 265
(.branch 263
(.leaf (3341, 3339, 0))
(.branch 264
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 266
(.leaf (3341, 3339, 0))
(.branch 267
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 271
(.branch 269
(.leaf (3341, 3339, 0))
(.branch 270
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 273
(.branch 272
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 274
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 287
(.branch 281
(.branch 278
(.branch 276
(.leaf (3341, 3339, 0))
(.branch 277
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 279
(.leaf (3341, 3339, 0))
(.branch 280
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 284
(.branch 282
(.leaf (3341, 3339, 0))
(.branch 283
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 285
(.leaf (3341, 3339, 0))
(.branch 286
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 293
(.branch 290
(.branch 288
(.leaf (3341, 3339, 0))
(.branch 289
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 291
(.leaf (3341, 3339, 0))
(.branch 292
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 296
(.branch 294
(.leaf (3341, 3339, 0))
(.branch 295
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 298
(.branch 297
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 299
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock3 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 350
(.branch 325
(.branch 312
(.branch 306
(.branch 303
(.branch 301
(.leaf (3341, 3339, 0))
(.branch 302
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 304
(.leaf (3341, 3339, 0))
(.branch 305
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 309
(.branch 307
(.leaf (3341, 3339, 0))
(.branch 308
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 310
(.leaf (3341, 3339, 0))
(.branch 311
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 318
(.branch 315
(.branch 313
(.leaf (3341, 3339, 0))
(.branch 314
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 316
(.leaf (3341, 3339, 0))
(.branch 317
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 321
(.branch 319
(.leaf (3341, 3339, 0))
(.branch 320
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 323
(.branch 322
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 324
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 337
(.branch 331
(.branch 328
(.branch 326
(.leaf (3341, 3339, 0))
(.branch 327
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 329
(.leaf (3341, 3339, 0))
(.branch 330
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 334
(.branch 332
(.leaf (3341, 3339, 0))
(.branch 333
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 335
(.leaf (3341, 3339, 0))
(.branch 336
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 343
(.branch 340
(.branch 338
(.leaf (3341, 3339, 0))
(.branch 339
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 341
(.leaf (3341, 3339, 0))
(.branch 342
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 346
(.branch 344
(.leaf (3341, 3339, 0))
(.branch 345
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 348
(.branch 347
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 349
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 375
(.branch 362
(.branch 356
(.branch 353
(.branch 351
(.leaf (3341, 3339, 0))
(.branch 352
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 354
(.leaf (3341, 3339, 0))
(.branch 355
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 359
(.branch 357
(.leaf (3341, 3339, 0))
(.branch 358
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 360
(.leaf (3341, 3339, 0))
(.branch 361
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 368
(.branch 365
(.branch 363
(.leaf (3341, 3339, 0))
(.branch 364
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 366
(.leaf (3341, 3339, 0))
(.branch 367
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 371
(.branch 369
(.leaf (3341, 3339, 0))
(.branch 370
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 373
(.branch 372
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 374
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 387
(.branch 381
(.branch 378
(.branch 376
(.leaf (3341, 3339, 0))
(.branch 377
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 379
(.leaf (3341, 3339, 0))
(.branch 380
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 384
(.branch 382
(.leaf (3341, 3339, 0))
(.branch 383
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 385
(.leaf (3341, 3339, 0))
(.branch 386
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 393
(.branch 390
(.branch 388
(.leaf (3341, 3339, 0))
(.branch 389
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 391
(.leaf (3341, 3339, 0))
(.branch 392
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 396
(.branch 394
(.leaf (3341, 3339, 0))
(.branch 395
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 398
(.branch 397
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 399
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock4 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 450
(.branch 425
(.branch 412
(.branch 406
(.branch 403
(.branch 401
(.leaf (3341, 3339, 0))
(.branch 402
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 404
(.leaf (3341, 3339, 0))
(.branch 405
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 409
(.branch 407
(.leaf (3341, 3339, 0))
(.branch 408
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 410
(.leaf (3341, 3339, 0))
(.branch 411
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 418
(.branch 415
(.branch 413
(.leaf (3341, 3339, 0))
(.branch 414
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 416
(.leaf (3341, 3339, 0))
(.branch 417
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 421
(.branch 419
(.leaf (3341, 3339, 0))
(.branch 420
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 423
(.branch 422
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 424
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 437
(.branch 431
(.branch 428
(.branch 426
(.leaf (3341, 3339, 0))
(.branch 427
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 429
(.leaf (3341, 3339, 0))
(.branch 430
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 434
(.branch 432
(.leaf (3341, 3339, 0))
(.branch 433
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 435
(.leaf (3341, 3339, 0))
(.branch 436
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 443
(.branch 440
(.branch 438
(.leaf (3341, 3339, 0))
(.branch 439
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 441
(.leaf (3341, 3339, 0))
(.branch 442
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 446
(.branch 444
(.leaf (3341, 3339, 0))
(.branch 445
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 448
(.branch 447
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 449
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 475
(.branch 462
(.branch 456
(.branch 453
(.branch 451
(.leaf (3341, 3339, 0))
(.branch 452
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 454
(.leaf (3341, 3339, 0))
(.branch 455
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 459
(.branch 457
(.leaf (3341, 3339, 0))
(.branch 458
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 460
(.leaf (3341, 3339, 0))
(.branch 461
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 468
(.branch 465
(.branch 463
(.leaf (3341, 3339, 0))
(.branch 464
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 466
(.leaf (3341, 3339, 0))
(.branch 467
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 471
(.branch 469
(.leaf (3341, 3339, 0))
(.branch 470
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 473
(.branch 472
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 474
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 487
(.branch 481
(.branch 478
(.branch 476
(.leaf (3341, 3339, 0))
(.branch 477
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 479
(.leaf (3341, 3339, 0))
(.branch 480
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 484
(.branch 482
(.leaf (3341, 3339, 0))
(.branch 483
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 485
(.leaf (3341, 3339, 0))
(.branch 486
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 493
(.branch 490
(.branch 488
(.leaf (3341, 3339, 0))
(.branch 489
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 491
(.leaf (3341, 3339, 0))
(.branch 492
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 496
(.branch 494
(.leaf (3341, 3339, 0))
(.branch 495
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 498
(.branch 497
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 499
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock5 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 550
(.branch 525
(.branch 512
(.branch 506
(.branch 503
(.branch 501
(.leaf (3341, 3339, 0))
(.branch 502
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 504
(.leaf (3341, 3339, 0))
(.branch 505
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 509
(.branch 507
(.leaf (3341, 3339, 0))
(.branch 508
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 510
(.leaf (3341, 3339, 0))
(.branch 511
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 518
(.branch 515
(.branch 513
(.leaf (3341, 3339, 0))
(.branch 514
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 516
(.leaf (3341, 3339, 0))
(.branch 517
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 521
(.branch 519
(.leaf (3341, 3339, 0))
(.branch 520
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 523
(.branch 522
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 524
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 537
(.branch 531
(.branch 528
(.branch 526
(.leaf (3341, 3339, 0))
(.branch 527
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 529
(.leaf (3341, 3339, 0))
(.branch 530
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 534
(.branch 532
(.leaf (3341, 3339, 0))
(.branch 533
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 535
(.leaf (3341, 3339, 0))
(.branch 536
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 543
(.branch 540
(.branch 538
(.leaf (3341, 3339, 0))
(.branch 539
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 541
(.leaf (3341, 3339, 0))
(.branch 542
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 546
(.branch 544
(.leaf (3341, 3339, 0))
(.branch 545
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 548
(.branch 547
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 549
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 575
(.branch 562
(.branch 556
(.branch 553
(.branch 551
(.leaf (3341, 3339, 0))
(.branch 552
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 554
(.leaf (3341, 3339, 0))
(.branch 555
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 559
(.branch 557
(.leaf (3341, 3339, 0))
(.branch 558
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 560
(.leaf (3341, 3339, 0))
(.branch 561
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 568
(.branch 565
(.branch 563
(.leaf (3341, 3339, 0))
(.branch 564
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 566
(.leaf (3341, 3339, 0))
(.branch 567
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 571
(.branch 569
(.leaf (3341, 3339, 0))
(.branch 570
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 573
(.branch 572
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 574
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 587
(.branch 581
(.branch 578
(.branch 576
(.leaf (3341, 3339, 0))
(.branch 577
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 579
(.leaf (3341, 3339, 0))
(.branch 580
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 584
(.branch 582
(.leaf (3341, 3339, 0))
(.branch 583
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 585
(.leaf (3341, 3339, 0))
(.branch 586
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 593
(.branch 590
(.branch 588
(.leaf (3341, 3339, 0))
(.branch 589
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 591
(.leaf (3341, 3339, 0))
(.branch 592
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 596
(.branch 594
(.leaf (3341, 3339, 0))
(.branch 595
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 598
(.branch 597
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 599
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock6 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 650
(.branch 625
(.branch 612
(.branch 606
(.branch 603
(.branch 601
(.leaf (3341, 3339, 0))
(.branch 602
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 604
(.leaf (3341, 3339, 0))
(.branch 605
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 609
(.branch 607
(.leaf (3341, 3339, 0))
(.branch 608
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 610
(.leaf (3341, 3339, 0))
(.branch 611
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 618
(.branch 615
(.branch 613
(.leaf (3341, 3339, 0))
(.branch 614
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 616
(.leaf (3341, 3339, 0))
(.branch 617
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 621
(.branch 619
(.leaf (3341, 3339, 0))
(.branch 620
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 623
(.branch 622
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 624
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 637
(.branch 631
(.branch 628
(.branch 626
(.leaf (3341, 3339, 0))
(.branch 627
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 629
(.leaf (3341, 3339, 0))
(.branch 630
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 634
(.branch 632
(.leaf (3341, 3339, 0))
(.branch 633
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 635
(.leaf (3341, 3339, 0))
(.branch 636
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 643
(.branch 640
(.branch 638
(.leaf (3341, 3339, 0))
(.branch 639
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 641
(.leaf (3341, 3339, 0))
(.branch 642
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 646
(.branch 644
(.leaf (3341, 3339, 0))
(.branch 645
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 648
(.branch 647
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 649
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 675
(.branch 662
(.branch 656
(.branch 653
(.branch 651
(.leaf (3341, 3339, 0))
(.branch 652
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 654
(.leaf (3341, 3339, 0))
(.branch 655
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 659
(.branch 657
(.leaf (3341, 3339, 0))
(.branch 658
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 660
(.leaf (3341, 3339, 0))
(.branch 661
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 668
(.branch 665
(.branch 663
(.leaf (3341, 3339, 0))
(.branch 664
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 666
(.leaf (3341, 3339, 0))
(.branch 667
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 671
(.branch 669
(.leaf (3341, 3339, 0))
(.branch 670
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 673
(.branch 672
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 674
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 687
(.branch 681
(.branch 678
(.branch 676
(.leaf (3341, 3339, 0))
(.branch 677
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 679
(.leaf (3341, 3339, 0))
(.branch 680
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 684
(.branch 682
(.leaf (3341, 3339, 0))
(.branch 683
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 685
(.leaf (3341, 3339, 0))
(.branch 686
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 693
(.branch 690
(.branch 688
(.leaf (3341, 3339, 0))
(.branch 689
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 691
(.leaf (3341, 3339, 0))
(.branch 692
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 696
(.branch 694
(.leaf (3341, 3339, 0))
(.branch 695
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 698
(.branch 697
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 699
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock7 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 750
(.branch 725
(.branch 712
(.branch 706
(.branch 703
(.branch 701
(.leaf (3341, 3339, 0))
(.branch 702
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 704
(.leaf (3341, 3339, 0))
(.branch 705
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 709
(.branch 707
(.leaf (3341, 3339, 0))
(.branch 708
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 710
(.leaf (3341, 3339, 0))
(.branch 711
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 718
(.branch 715
(.branch 713
(.leaf (3341, 3339, 0))
(.branch 714
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 716
(.leaf (3341, 3339, 0))
(.branch 717
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 721
(.branch 719
(.leaf (3341, 3339, 0))
(.branch 720
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 723
(.branch 722
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 724
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 737
(.branch 731
(.branch 728
(.branch 726
(.leaf (3341, 3339, 0))
(.branch 727
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 729
(.leaf (3341, 3339, 0))
(.branch 730
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 734
(.branch 732
(.leaf (3341, 3339, 0))
(.branch 733
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 735
(.leaf (3341, 3339, 0))
(.branch 736
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 743
(.branch 740
(.branch 738
(.leaf (3341, 3339, 0))
(.branch 739
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 741
(.leaf (3341, 3339, 0))
(.branch 742
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 746
(.branch 744
(.leaf (3341, 3339, 0))
(.branch 745
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 748
(.branch 747
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 749
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 775
(.branch 762
(.branch 756
(.branch 753
(.branch 751
(.leaf (3341, 3339, 0))
(.branch 752
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 754
(.leaf (3341, 3339, 0))
(.branch 755
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 759
(.branch 757
(.leaf (3341, 3339, 0))
(.branch 758
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 760
(.leaf (3341, 3339, 0))
(.branch 761
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 768
(.branch 765
(.branch 763
(.leaf (3341, 3339, 0))
(.branch 764
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 766
(.leaf (3341, 3339, 0))
(.branch 767
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 771
(.branch 769
(.leaf (3341, 3339, 0))
(.branch 770
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 773
(.branch 772
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 774
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 787
(.branch 781
(.branch 778
(.branch 776
(.leaf (3341, 3339, 0))
(.branch 777
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 779
(.leaf (3341, 3339, 0))
(.branch 780
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 784
(.branch 782
(.leaf (3341, 3339, 0))
(.branch 783
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 785
(.leaf (3341, 3339, 0))
(.branch 786
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 793
(.branch 790
(.branch 788
(.leaf (3341, 3339, 0))
(.branch 789
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 791
(.leaf (3341, 3339, 0))
(.branch 792
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 796
(.branch 794
(.leaf (3341, 3339, 0))
(.branch 795
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 798
(.branch 797
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 799
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock8 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 850
(.branch 825
(.branch 812
(.branch 806
(.branch 803
(.branch 801
(.leaf (3341, 3339, 0))
(.branch 802
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 804
(.leaf (3341, 3339, 0))
(.branch 805
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 809
(.branch 807
(.leaf (3341, 3339, 0))
(.branch 808
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 810
(.leaf (3341, 3339, 0))
(.branch 811
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 818
(.branch 815
(.branch 813
(.leaf (3341, 3339, 0))
(.branch 814
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 816
(.leaf (3341, 3339, 0))
(.branch 817
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 821
(.branch 819
(.leaf (3341, 3339, 0))
(.branch 820
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 823
(.branch 822
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 824
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 837
(.branch 831
(.branch 828
(.branch 826
(.leaf (3341, 3339, 0))
(.branch 827
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 829
(.leaf (3341, 3339, 0))
(.branch 830
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 834
(.branch 832
(.leaf (3341, 3339, 0))
(.branch 833
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 835
(.leaf (3341, 3339, 0))
(.branch 836
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 843
(.branch 840
(.branch 838
(.leaf (3341, 3339, 0))
(.branch 839
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 841
(.leaf (3341, 3339, 0))
(.branch 842
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 846
(.branch 844
(.leaf (3341, 3339, 0))
(.branch 845
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 848
(.branch 847
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 849
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 875
(.branch 862
(.branch 856
(.branch 853
(.branch 851
(.leaf (3341, 3339, 0))
(.branch 852
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 854
(.leaf (3341, 3339, 0))
(.branch 855
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 859
(.branch 857
(.leaf (3341, 3339, 0))
(.branch 858
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 860
(.leaf (3341, 3339, 0))
(.branch 861
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 868
(.branch 865
(.branch 863
(.leaf (3341, 3339, 0))
(.branch 864
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 866
(.leaf (3341, 3339, 0))
(.branch 867
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 871
(.branch 869
(.leaf (3341, 3339, 0))
(.branch 870
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 873
(.branch 872
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 874
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 887
(.branch 881
(.branch 878
(.branch 876
(.leaf (3341, 3339, 0))
(.branch 877
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 879
(.leaf (3341, 3339, 0))
(.branch 880
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 884
(.branch 882
(.leaf (3341, 3339, 0))
(.branch 883
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 885
(.leaf (3341, 3339, 0))
(.branch 886
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 893
(.branch 890
(.branch 888
(.leaf (3341, 3339, 0))
(.branch 889
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 891
(.leaf (3341, 3339, 0))
(.branch 892
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 896
(.branch 894
(.leaf (3341, 3339, 0))
(.branch 895
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 898
(.branch 897
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 899
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock9 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 950
(.branch 925
(.branch 912
(.branch 906
(.branch 903
(.branch 901
(.leaf (3341, 3339, 0))
(.branch 902
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 904
(.leaf (3341, 3339, 0))
(.branch 905
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 909
(.branch 907
(.leaf (3341, 3339, 0))
(.branch 908
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 910
(.leaf (3341, 3339, 0))
(.branch 911
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 918
(.branch 915
(.branch 913
(.leaf (3341, 3339, 0))
(.branch 914
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 916
(.leaf (3341, 3339, 0))
(.branch 917
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 921
(.branch 919
(.leaf (3341, 3339, 0))
(.branch 920
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 923
(.branch 922
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 924
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 937
(.branch 931
(.branch 928
(.branch 926
(.leaf (3341, 3339, 0))
(.branch 927
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 929
(.leaf (3341, 3339, 0))
(.branch 930
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 934
(.branch 932
(.leaf (3341, 3339, 0))
(.branch 933
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 935
(.leaf (3341, 3339, 0))
(.branch 936
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 943
(.branch 940
(.branch 938
(.leaf (3341, 3339, 0))
(.branch 939
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 941
(.leaf (3341, 3339, 0))
(.branch 942
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 946
(.branch 944
(.leaf (3341, 3339, 0))
(.branch 945
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 948
(.branch 947
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 949
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 975
(.branch 962
(.branch 956
(.branch 953
(.branch 951
(.leaf (3341, 3339, 0))
(.branch 952
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 954
(.leaf (3341, 3339, 0))
(.branch 955
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 959
(.branch 957
(.leaf (3341, 3339, 0))
(.branch 958
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 960
(.leaf (3341, 3339, 0))
(.branch 961
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 968
(.branch 965
(.branch 963
(.leaf (3341, 3339, 0))
(.branch 964
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 966
(.leaf (3341, 3339, 0))
(.branch 967
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 971
(.branch 969
(.leaf (3341, 3339, 0))
(.branch 970
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 973
(.branch 972
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 974
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 987
(.branch 981
(.branch 978
(.branch 976
(.leaf (3341, 3339, 0))
(.branch 977
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 979
(.leaf (3341, 3339, 0))
(.branch 980
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 984
(.branch 982
(.leaf (3341, 3339, 0))
(.branch 983
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 985
(.leaf (3341, 3339, 0))
(.branch 986
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 993
(.branch 990
(.branch 988
(.leaf (3341, 3339, 0))
(.branch 989
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 991
(.leaf (3341, 3339, 0))
(.branch 992
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 996
(.branch 994
(.leaf (3341, 3339, 0))
(.branch 995
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 998
(.branch 997
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 999
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock10 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 1050
(.branch 1025
(.branch 1012
(.branch 1006
(.branch 1003
(.branch 1001
(.leaf (3341, 3339, 0))
(.branch 1002
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1004
(.leaf (3341, 3339, 0))
(.branch 1005
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1009
(.branch 1007
(.leaf (3341, 3339, 0))
(.branch 1008
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1010
(.leaf (3341, 3339, 0))
(.branch 1011
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1018
(.branch 1015
(.branch 1013
(.leaf (3341, 3339, 0))
(.branch 1014
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1016
(.leaf (3341, 3339, 0))
(.branch 1017
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1021
(.branch 1019
(.leaf (3341, 3339, 0))
(.branch 1020
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1023
(.branch 1022
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1024
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1037
(.branch 1031
(.branch 1028
(.branch 1026
(.leaf (3341, 3339, 0))
(.branch 1027
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1029
(.leaf (3341, 3339, 0))
(.branch 1030
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1034
(.branch 1032
(.leaf (3341, 3339, 0))
(.branch 1033
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1035
(.leaf (3341, 3339, 0))
(.branch 1036
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1043
(.branch 1040
(.branch 1038
(.leaf (3341, 3339, 0))
(.branch 1039
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1041
(.leaf (3341, 3339, 0))
(.branch 1042
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1046
(.branch 1044
(.leaf (3341, 3339, 0))
(.branch 1045
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1048
(.branch 1047
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1049
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 1075
(.branch 1062
(.branch 1056
(.branch 1053
(.branch 1051
(.leaf (3341, 3339, 0))
(.branch 1052
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1054
(.leaf (3341, 3339, 0))
(.branch 1055
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1059
(.branch 1057
(.leaf (3341, 3339, 0))
(.branch 1058
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1060
(.leaf (3341, 3339, 0))
(.branch 1061
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1068
(.branch 1065
(.branch 1063
(.leaf (3341, 3339, 0))
(.branch 1064
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1066
(.leaf (3341, 3339, 0))
(.branch 1067
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1071
(.branch 1069
(.leaf (3341, 3339, 0))
(.branch 1070
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1073
(.branch 1072
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1074
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1087
(.branch 1081
(.branch 1078
(.branch 1076
(.leaf (3341, 3339, 0))
(.branch 1077
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1079
(.leaf (3341, 3339, 0))
(.branch 1080
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1084
(.branch 1082
(.leaf (3341, 3339, 0))
(.branch 1083
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1085
(.leaf (3341, 3339, 0))
(.branch 1086
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1093
(.branch 1090
(.branch 1088
(.leaf (3341, 3339, 0))
(.branch 1089
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1091
(.leaf (3341, 3339, 0))
(.branch 1092
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1096
(.branch 1094
(.leaf (3341, 3339, 0))
(.branch 1095
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1098
(.branch 1097
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1099
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock11 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 1150
(.branch 1125
(.branch 1112
(.branch 1106
(.branch 1103
(.branch 1101
(.leaf (3341, 3339, 0))
(.branch 1102
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1104
(.leaf (3341, 3339, 0))
(.branch 1105
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1109
(.branch 1107
(.leaf (3341, 3339, 0))
(.branch 1108
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1110
(.leaf (3341, 3339, 0))
(.branch 1111
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1118
(.branch 1115
(.branch 1113
(.leaf (3341, 3339, 0))
(.branch 1114
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1116
(.leaf (3341, 3339, 0))
(.branch 1117
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1121
(.branch 1119
(.leaf (3341, 3339, 0))
(.branch 1120
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1123
(.branch 1122
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1124
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1137
(.branch 1131
(.branch 1128
(.branch 1126
(.leaf (3341, 3339, 0))
(.branch 1127
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1129
(.leaf (3341, 3339, 0))
(.branch 1130
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1134
(.branch 1132
(.leaf (3341, 3339, 0))
(.branch 1133
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1135
(.leaf (3341, 3339, 0))
(.branch 1136
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1143
(.branch 1140
(.branch 1138
(.leaf (3341, 3339, 0))
(.branch 1139
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1141
(.leaf (3341, 3339, 0))
(.branch 1142
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1146
(.branch 1144
(.leaf (3341, 3339, 0))
(.branch 1145
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1148
(.branch 1147
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1149
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 1175
(.branch 1162
(.branch 1156
(.branch 1153
(.branch 1151
(.leaf (3341, 3339, 0))
(.branch 1152
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1154
(.leaf (3341, 3339, 0))
(.branch 1155
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1159
(.branch 1157
(.leaf (3341, 3339, 0))
(.branch 1158
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1160
(.leaf (3341, 3339, 0))
(.branch 1161
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1168
(.branch 1165
(.branch 1163
(.leaf (3341, 3339, 0))
(.branch 1164
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1166
(.leaf (3341, 3339, 0))
(.branch 1167
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1171
(.branch 1169
(.leaf (3341, 3339, 0))
(.branch 1170
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1173
(.branch 1172
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1174
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1187
(.branch 1181
(.branch 1178
(.branch 1176
(.leaf (3341, 3339, 0))
(.branch 1177
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1179
(.leaf (3341, 3339, 0))
(.branch 1180
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1184
(.branch 1182
(.leaf (3341, 3339, 0))
(.branch 1183
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1185
(.leaf (3341, 3339, 0))
(.branch 1186
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1193
(.branch 1190
(.branch 1188
(.leaf (3341, 3339, 0))
(.branch 1189
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1191
(.leaf (3341, 3339, 0))
(.branch 1192
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1196
(.branch 1194
(.leaf (3341, 3339, 0))
(.branch 1195
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1198
(.branch 1197
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1199
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock12 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 1250
(.branch 1225
(.branch 1212
(.branch 1206
(.branch 1203
(.branch 1201
(.leaf (3341, 3339, 0))
(.branch 1202
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1204
(.leaf (3341, 3339, 0))
(.branch 1205
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1209
(.branch 1207
(.leaf (3341, 3339, 0))
(.branch 1208
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1210
(.leaf (3341, 3339, 0))
(.branch 1211
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1218
(.branch 1215
(.branch 1213
(.leaf (3341, 3339, 0))
(.branch 1214
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1216
(.leaf (3341, 3339, 0))
(.branch 1217
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1221
(.branch 1219
(.leaf (3341, 3339, 0))
(.branch 1220
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1223
(.branch 1222
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1224
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1237
(.branch 1231
(.branch 1228
(.branch 1226
(.leaf (3341, 3339, 0))
(.branch 1227
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1229
(.leaf (3341, 3339, 0))
(.branch 1230
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1234
(.branch 1232
(.leaf (3341, 3339, 0))
(.branch 1233
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1235
(.leaf (3341, 3339, 0))
(.branch 1236
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1243
(.branch 1240
(.branch 1238
(.leaf (3341, 3339, 0))
(.branch 1239
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1241
(.leaf (3341, 3339, 0))
(.branch 1242
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1246
(.branch 1244
(.leaf (3341, 3339, 0))
(.branch 1245
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1248
(.branch 1247
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1249
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 1275
(.branch 1262
(.branch 1256
(.branch 1253
(.branch 1251
(.leaf (3341, 3339, 0))
(.branch 1252
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1254
(.leaf (3341, 3339, 0))
(.branch 1255
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1259
(.branch 1257
(.leaf (3341, 3339, 0))
(.branch 1258
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1260
(.leaf (3341, 3339, 0))
(.branch 1261
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1268
(.branch 1265
(.branch 1263
(.leaf (3341, 3339, 0))
(.branch 1264
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1266
(.leaf (3341, 3339, 0))
(.branch 1267
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1271
(.branch 1269
(.leaf (3341, 3339, 0))
(.branch 1270
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1273
(.branch 1272
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1274
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1287
(.branch 1281
(.branch 1278
(.branch 1276
(.leaf (3341, 3339, 0))
(.branch 1277
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1279
(.leaf (3341, 3339, 0))
(.branch 1280
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1284
(.branch 1282
(.leaf (3341, 3339, 0))
(.branch 1283
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1285
(.leaf (3341, 3339, 0))
(.branch 1286
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1293
(.branch 1290
(.branch 1288
(.leaf (3341, 3339, 0))
(.branch 1289
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1291
(.leaf (3341, 3339, 0))
(.branch 1292
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1296
(.branch 1294
(.leaf (3341, 3339, 0))
(.branch 1295
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1298
(.branch 1297
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1299
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock13 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 1350
(.branch 1325
(.branch 1312
(.branch 1306
(.branch 1303
(.branch 1301
(.leaf (3341, 3339, 0))
(.branch 1302
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1304
(.leaf (3341, 3339, 0))
(.branch 1305
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1309
(.branch 1307
(.leaf (3341, 3339, 0))
(.branch 1308
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1310
(.leaf (3341, 3339, 0))
(.branch 1311
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1318
(.branch 1315
(.branch 1313
(.leaf (3341, 3339, 0))
(.branch 1314
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1316
(.leaf (3341, 3339, 0))
(.branch 1317
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1321
(.branch 1319
(.leaf (3341, 3339, 0))
(.branch 1320
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1323
(.branch 1322
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1324
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1337
(.branch 1331
(.branch 1328
(.branch 1326
(.leaf (3341, 3339, 0))
(.branch 1327
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1329
(.leaf (3341, 3339, 0))
(.branch 1330
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1334
(.branch 1332
(.leaf (3341, 3339, 0))
(.branch 1333
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1335
(.leaf (3341, 3339, 0))
(.branch 1336
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1343
(.branch 1340
(.branch 1338
(.leaf (3341, 3339, 0))
(.branch 1339
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1341
(.leaf (3341, 3339, 0))
(.branch 1342
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1346
(.branch 1344
(.leaf (3341, 3339, 0))
(.branch 1345
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1348
(.branch 1347
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1349
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 1375
(.branch 1362
(.branch 1356
(.branch 1353
(.branch 1351
(.leaf (3341, 3339, 0))
(.branch 1352
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1354
(.leaf (3341, 3339, 0))
(.branch 1355
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1359
(.branch 1357
(.leaf (3341, 3339, 0))
(.branch 1358
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1360
(.leaf (3341, 3339, 0))
(.branch 1361
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1368
(.branch 1365
(.branch 1363
(.leaf (3341, 3339, 0))
(.branch 1364
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1366
(.leaf (3341, 3339, 0))
(.branch 1367
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1371
(.branch 1369
(.leaf (3341, 3339, 0))
(.branch 1370
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1373
(.branch 1372
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1374
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1387
(.branch 1381
(.branch 1378
(.branch 1376
(.leaf (3341, 3339, 0))
(.branch 1377
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1379
(.leaf (3341, 3339, 0))
(.branch 1380
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1384
(.branch 1382
(.leaf (3341, 3339, 0))
(.branch 1383
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1385
(.leaf (3341, 3339, 0))
(.branch 1386
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1393
(.branch 1390
(.branch 1388
(.leaf (3341, 3339, 0))
(.branch 1389
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1391
(.leaf (3341, 3339, 0))
(.branch 1392
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1396
(.branch 1394
(.leaf (3341, 3339, 0))
(.branch 1395
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1398
(.branch 1397
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1399
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock14 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 1450
(.branch 1425
(.branch 1412
(.branch 1406
(.branch 1403
(.branch 1401
(.leaf (3341, 3339, 0))
(.branch 1402
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1404
(.leaf (3341, 3339, 0))
(.branch 1405
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1409
(.branch 1407
(.leaf (3341, 3339, 0))
(.branch 1408
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1410
(.leaf (3341, 3339, 0))
(.branch 1411
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1418
(.branch 1415
(.branch 1413
(.leaf (3341, 3339, 0))
(.branch 1414
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1416
(.leaf (3341, 3339, 0))
(.branch 1417
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1421
(.branch 1419
(.leaf (3341, 3339, 0))
(.branch 1420
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1423
(.branch 1422
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1424
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1437
(.branch 1431
(.branch 1428
(.branch 1426
(.leaf (3341, 3339, 0))
(.branch 1427
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1429
(.leaf (3341, 3339, 0))
(.branch 1430
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1434
(.branch 1432
(.leaf (3341, 3339, 0))
(.branch 1433
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1435
(.leaf (3341, 3339, 0))
(.branch 1436
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1443
(.branch 1440
(.branch 1438
(.leaf (3341, 3339, 0))
(.branch 1439
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1441
(.leaf (3341, 3339, 0))
(.branch 1442
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1446
(.branch 1444
(.leaf (3341, 3339, 0))
(.branch 1445
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1448
(.branch 1447
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1449
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 1475
(.branch 1462
(.branch 1456
(.branch 1453
(.branch 1451
(.leaf (3341, 3339, 0))
(.branch 1452
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1454
(.leaf (3341, 3339, 0))
(.branch 1455
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1459
(.branch 1457
(.leaf (3341, 3339, 0))
(.branch 1458
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1460
(.leaf (3341, 3339, 0))
(.branch 1461
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1468
(.branch 1465
(.branch 1463
(.leaf (3341, 3339, 0))
(.branch 1464
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1466
(.leaf (3341, 3339, 0))
(.branch 1467
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1471
(.branch 1469
(.leaf (3341, 3339, 0))
(.branch 1470
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1473
(.branch 1472
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1474
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1487
(.branch 1481
(.branch 1478
(.branch 1476
(.leaf (3341, 3339, 0))
(.branch 1477
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1479
(.leaf (3341, 3339, 0))
(.branch 1480
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1484
(.branch 1482
(.leaf (3341, 3339, 0))
(.branch 1483
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1485
(.leaf (3341, 3339, 0))
(.branch 1486
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1493
(.branch 1490
(.branch 1488
(.leaf (3341, 3339, 0))
(.branch 1489
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1491
(.leaf (3341, 3339, 0))
(.branch 1492
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1496
(.branch 1494
(.leaf (3341, 3339, 0))
(.branch 1495
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1498
(.branch 1497
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1499
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock15 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 1550
(.branch 1525
(.branch 1512
(.branch 1506
(.branch 1503
(.branch 1501
(.leaf (3341, 3339, 0))
(.branch 1502
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1504
(.leaf (3341, 3339, 0))
(.branch 1505
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1509
(.branch 1507
(.leaf (3341, 3339, 0))
(.branch 1508
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1510
(.leaf (3341, 3339, 0))
(.branch 1511
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1518
(.branch 1515
(.branch 1513
(.leaf (3341, 3339, 0))
(.branch 1514
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1516
(.leaf (3341, 3339, 0))
(.branch 1517
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1521
(.branch 1519
(.leaf (3341, 3339, 0))
(.branch 1520
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1523
(.branch 1522
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1524
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1537
(.branch 1531
(.branch 1528
(.branch 1526
(.leaf (3341, 3339, 0))
(.branch 1527
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1529
(.leaf (3341, 3339, 0))
(.branch 1530
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1534
(.branch 1532
(.leaf (3341, 3339, 0))
(.branch 1533
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1535
(.leaf (3341, 3339, 0))
(.branch 1536
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1543
(.branch 1540
(.branch 1538
(.leaf (3341, 3339, 0))
(.branch 1539
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1541
(.leaf (3341, 3339, 0))
(.branch 1542
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1546
(.branch 1544
(.leaf (3341, 3339, 0))
(.branch 1545
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1548
(.branch 1547
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1549
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 1575
(.branch 1562
(.branch 1556
(.branch 1553
(.branch 1551
(.leaf (3341, 3339, 0))
(.branch 1552
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1554
(.leaf (3341, 3339, 0))
(.branch 1555
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1559
(.branch 1557
(.leaf (3341, 3339, 0))
(.branch 1558
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1560
(.leaf (3341, 3339, 0))
(.branch 1561
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1568
(.branch 1565
(.branch 1563
(.leaf (3341, 3339, 0))
(.branch 1564
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1566
(.leaf (3341, 3339, 0))
(.branch 1567
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1571
(.branch 1569
(.leaf (3341, 3339, 0))
(.branch 1570
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1573
(.branch 1572
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1574
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1587
(.branch 1581
(.branch 1578
(.branch 1576
(.leaf (3341, 3339, 0))
(.branch 1577
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1579
(.leaf (3341, 3339, 0))
(.branch 1580
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1584
(.branch 1582
(.leaf (3341, 3339, 0))
(.branch 1583
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1585
(.leaf (3341, 3339, 0))
(.branch 1586
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1593
(.branch 1590
(.branch 1588
(.leaf (3341, 3339, 0))
(.branch 1589
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1591
(.leaf (3341, 3339, 0))
(.branch 1592
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1596
(.branch 1594
(.leaf (3341, 3339, 0))
(.branch 1595
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1598
(.branch 1597
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1599
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock16 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 1650
(.branch 1625
(.branch 1612
(.branch 1606
(.branch 1603
(.branch 1601
(.leaf (3341, 3339, 0))
(.branch 1602
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1604
(.leaf (3341, 3339, 0))
(.branch 1605
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1609
(.branch 1607
(.leaf (3341, 3339, 0))
(.branch 1608
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1610
(.leaf (3341, 3339, 0))
(.branch 1611
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1618
(.branch 1615
(.branch 1613
(.leaf (3341, 3339, 0))
(.branch 1614
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1616
(.leaf (3341, 3339, 0))
(.branch 1617
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1621
(.branch 1619
(.leaf (3341, 3339, 0))
(.branch 1620
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1623
(.branch 1622
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1624
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1637
(.branch 1631
(.branch 1628
(.branch 1626
(.leaf (3341, 3339, 0))
(.branch 1627
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1629
(.leaf (3341, 3339, 0))
(.branch 1630
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1634
(.branch 1632
(.leaf (3341, 3339, 0))
(.branch 1633
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1635
(.leaf (3341, 3339, 0))
(.branch 1636
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1643
(.branch 1640
(.branch 1638
(.leaf (3341, 3339, 0))
(.branch 1639
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1641
(.leaf (3341, 3339, 0))
(.branch 1642
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1646
(.branch 1644
(.leaf (3341, 3339, 0))
(.branch 1645
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1648
(.branch 1647
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1649
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 1675
(.branch 1662
(.branch 1656
(.branch 1653
(.branch 1651
(.leaf (3341, 3339, 0))
(.branch 1652
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1654
(.leaf (3341, 3339, 0))
(.branch 1655
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1659
(.branch 1657
(.leaf (3341, 3339, 0))
(.branch 1658
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1660
(.leaf (3341, 3339, 0))
(.branch 1661
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1668
(.branch 1665
(.branch 1663
(.leaf (3341, 3339, 0))
(.branch 1664
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1666
(.leaf (3341, 3339, 0))
(.branch 1667
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1671
(.branch 1669
(.leaf (3341, 3339, 0))
(.branch 1670
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1673
(.branch 1672
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1674
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1687
(.branch 1681
(.branch 1678
(.branch 1676
(.leaf (3341, 3339, 0))
(.branch 1677
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1679
(.leaf (3341, 3339, 0))
(.branch 1680
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1684
(.branch 1682
(.leaf (3341, 3339, 0))
(.branch 1683
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1685
(.leaf (3341, 3339, 0))
(.branch 1686
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1693
(.branch 1690
(.branch 1688
(.leaf (3341, 3339, 0))
(.branch 1689
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1691
(.leaf (3341, 3339, 0))
(.branch 1692
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1696
(.branch 1694
(.leaf (3341, 3339, 0))
(.branch 1695
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1698
(.branch 1697
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1699
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock17 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 1750
(.branch 1725
(.branch 1712
(.branch 1706
(.branch 1703
(.branch 1701
(.leaf (3341, 3339, 0))
(.branch 1702
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1704
(.leaf (3341, 3339, 0))
(.branch 1705
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1709
(.branch 1707
(.leaf (3341, 3339, 0))
(.branch 1708
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1710
(.leaf (3341, 3339, 0))
(.branch 1711
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1718
(.branch 1715
(.branch 1713
(.leaf (3341, 3339, 0))
(.branch 1714
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1716
(.leaf (3341, 3339, 0))
(.branch 1717
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1721
(.branch 1719
(.leaf (3341, 3339, 0))
(.branch 1720
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1723
(.branch 1722
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1724
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1737
(.branch 1731
(.branch 1728
(.branch 1726
(.leaf (3341, 3339, 0))
(.branch 1727
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1729
(.leaf (3341, 3339, 0))
(.branch 1730
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1734
(.branch 1732
(.leaf (3341, 3339, 0))
(.branch 1733
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1735
(.leaf (3341, 3339, 0))
(.branch 1736
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1743
(.branch 1740
(.branch 1738
(.leaf (3341, 3339, 0))
(.branch 1739
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1741
(.leaf (3341, 3339, 0))
(.branch 1742
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1746
(.branch 1744
(.leaf (3341, 3339, 0))
(.branch 1745
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1748
(.branch 1747
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1749
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 1775
(.branch 1762
(.branch 1756
(.branch 1753
(.branch 1751
(.leaf (3341, 3339, 0))
(.branch 1752
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1754
(.leaf (3341, 3339, 0))
(.branch 1755
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1759
(.branch 1757
(.leaf (3341, 3339, 0))
(.branch 1758
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1760
(.leaf (3341, 3339, 0))
(.branch 1761
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1768
(.branch 1765
(.branch 1763
(.leaf (3341, 3339, 0))
(.branch 1764
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1766
(.leaf (3341, 3339, 0))
(.branch 1767
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1771
(.branch 1769
(.leaf (3341, 3339, 0))
(.branch 1770
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1773
(.branch 1772
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1774
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1787
(.branch 1781
(.branch 1778
(.branch 1776
(.leaf (3341, 3339, 0))
(.branch 1777
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1779
(.leaf (3341, 3339, 0))
(.branch 1780
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1784
(.branch 1782
(.leaf (3341, 3339, 0))
(.branch 1783
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1785
(.leaf (3341, 3339, 0))
(.branch 1786
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1793
(.branch 1790
(.branch 1788
(.leaf (3341, 3339, 0))
(.branch 1789
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1791
(.leaf (3341, 3339, 0))
(.branch 1792
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1796
(.branch 1794
(.leaf (3341, 3339, 0))
(.branch 1795
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1798
(.branch 1797
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1799
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock18 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 1850
(.branch 1825
(.branch 1812
(.branch 1806
(.branch 1803
(.branch 1801
(.leaf (3341, 3339, 0))
(.branch 1802
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1804
(.leaf (3341, 3339, 0))
(.branch 1805
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1809
(.branch 1807
(.leaf (3341, 3339, 0))
(.branch 1808
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1810
(.leaf (3341, 3339, 0))
(.branch 1811
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1818
(.branch 1815
(.branch 1813
(.leaf (3341, 3339, 0))
(.branch 1814
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1816
(.leaf (3341, 3339, 0))
(.branch 1817
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1821
(.branch 1819
(.leaf (3341, 3339, 0))
(.branch 1820
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1823
(.branch 1822
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1824
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1837
(.branch 1831
(.branch 1828
(.branch 1826
(.leaf (3341, 3339, 0))
(.branch 1827
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1829
(.leaf (3341, 3339, 0))
(.branch 1830
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1834
(.branch 1832
(.leaf (3341, 3339, 0))
(.branch 1833
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1835
(.leaf (3341, 3339, 0))
(.branch 1836
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1843
(.branch 1840
(.branch 1838
(.leaf (3341, 3339, 0))
(.branch 1839
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1841
(.leaf (3341, 3339, 0))
(.branch 1842
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1846
(.branch 1844
(.leaf (3341, 3339, 0))
(.branch 1845
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1848
(.branch 1847
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1849
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 1875
(.branch 1862
(.branch 1856
(.branch 1853
(.branch 1851
(.leaf (3341, 3339, 0))
(.branch 1852
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1854
(.leaf (3341, 3339, 0))
(.branch 1855
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1859
(.branch 1857
(.leaf (3341, 3339, 0))
(.branch 1858
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1860
(.leaf (3341, 3339, 0))
(.branch 1861
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1868
(.branch 1865
(.branch 1863
(.leaf (3341, 3339, 0))
(.branch 1864
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1866
(.leaf (3341, 3339, 0))
(.branch 1867
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1871
(.branch 1869
(.leaf (3341, 3339, 0))
(.branch 1870
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1873
(.branch 1872
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1874
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1887
(.branch 1881
(.branch 1878
(.branch 1876
(.leaf (3341, 3339, 0))
(.branch 1877
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1879
(.leaf (3341, 3339, 0))
(.branch 1880
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1884
(.branch 1882
(.leaf (3341, 3339, 0))
(.branch 1883
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1885
(.leaf (3341, 3339, 0))
(.branch 1886
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1893
(.branch 1890
(.branch 1888
(.leaf (3341, 3339, 0))
(.branch 1889
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1891
(.leaf (3341, 3339, 0))
(.branch 1892
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1896
(.branch 1894
(.leaf (3341, 3339, 0))
(.branch 1895
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1898
(.branch 1897
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1899
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock19 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 1950
(.branch 1925
(.branch 1912
(.branch 1906
(.branch 1903
(.branch 1901
(.leaf (3341, 3339, 0))
(.branch 1902
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1904
(.leaf (3341, 3339, 0))
(.branch 1905
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1909
(.branch 1907
(.leaf (3341, 3339, 0))
(.branch 1908
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1910
(.leaf (3341, 3339, 0))
(.branch 1911
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1918
(.branch 1915
(.branch 1913
(.leaf (3341, 3339, 0))
(.branch 1914
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1916
(.leaf (3341, 3339, 0))
(.branch 1917
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1921
(.branch 1919
(.leaf (3341, 3339, 0))
(.branch 1920
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1923
(.branch 1922
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1924
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1937
(.branch 1931
(.branch 1928
(.branch 1926
(.leaf (3341, 3339, 0))
(.branch 1927
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1929
(.leaf (3341, 3339, 0))
(.branch 1930
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1934
(.branch 1932
(.leaf (3341, 3339, 0))
(.branch 1933
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1935
(.leaf (3341, 3339, 0))
(.branch 1936
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1943
(.branch 1940
(.branch 1938
(.leaf (3341, 3339, 0))
(.branch 1939
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1941
(.leaf (3341, 3339, 0))
(.branch 1942
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1946
(.branch 1944
(.leaf (3341, 3339, 0))
(.branch 1945
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1948
(.branch 1947
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1949
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 1975
(.branch 1962
(.branch 1956
(.branch 1953
(.branch 1951
(.leaf (3341, 3339, 0))
(.branch 1952
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1954
(.leaf (3341, 3339, 0))
(.branch 1955
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1959
(.branch 1957
(.leaf (3341, 3339, 0))
(.branch 1958
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1960
(.leaf (3341, 3339, 0))
(.branch 1961
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1968
(.branch 1965
(.branch 1963
(.leaf (3341, 3339, 0))
(.branch 1964
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1966
(.leaf (3341, 3339, 0))
(.branch 1967
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1971
(.branch 1969
(.leaf (3341, 3339, 0))
(.branch 1970
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1973
(.branch 1972
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1974
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 1987
(.branch 1981
(.branch 1978
(.branch 1976
(.leaf (3341, 3339, 0))
(.branch 1977
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1979
(.leaf (3341, 3339, 0))
(.branch 1980
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1984
(.branch 1982
(.leaf (3341, 3339, 0))
(.branch 1983
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1985
(.leaf (3341, 3339, 0))
(.branch 1986
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 1993
(.branch 1990
(.branch 1988
(.leaf (3341, 3339, 0))
(.branch 1989
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1991
(.leaf (3341, 3339, 0))
(.branch 1992
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 1996
(.branch 1994
(.leaf (3341, 3339, 0))
(.branch 1995
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 1998
(.branch 1997
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 1999
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock20 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 2050
(.branch 2025
(.branch 2012
(.branch 2006
(.branch 2003
(.branch 2001
(.leaf (3341, 3339, 0))
(.branch 2002
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2004
(.leaf (3341, 3339, 0))
(.branch 2005
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2009
(.branch 2007
(.leaf (3341, 3339, 0))
(.branch 2008
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2010
(.leaf (3341, 3339, 0))
(.branch 2011
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2018
(.branch 2015
(.branch 2013
(.leaf (3341, 3339, 0))
(.branch 2014
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2016
(.leaf (3341, 3339, 0))
(.branch 2017
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2021
(.branch 2019
(.leaf (3341, 3339, 0))
(.branch 2020
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2023
(.branch 2022
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2024
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2037
(.branch 2031
(.branch 2028
(.branch 2026
(.leaf (3341, 3339, 0))
(.branch 2027
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2029
(.leaf (3341, 3339, 0))
(.branch 2030
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2034
(.branch 2032
(.leaf (3341, 3339, 0))
(.branch 2033
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2035
(.leaf (3341, 3339, 0))
(.branch 2036
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2043
(.branch 2040
(.branch 2038
(.leaf (3341, 3339, 0))
(.branch 2039
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2041
(.leaf (3341, 3339, 0))
(.branch 2042
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2046
(.branch 2044
(.leaf (3341, 3339, 0))
(.branch 2045
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2048
(.branch 2047
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2049
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 2075
(.branch 2062
(.branch 2056
(.branch 2053
(.branch 2051
(.leaf (3341, 3339, 0))
(.branch 2052
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2054
(.leaf (3341, 3339, 0))
(.branch 2055
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2059
(.branch 2057
(.leaf (3341, 3339, 0))
(.branch 2058
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2060
(.leaf (3341, 3339, 0))
(.branch 2061
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2068
(.branch 2065
(.branch 2063
(.leaf (3341, 3339, 0))
(.branch 2064
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2066
(.leaf (3341, 3339, 0))
(.branch 2067
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2071
(.branch 2069
(.leaf (3341, 3339, 0))
(.branch 2070
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2073
(.branch 2072
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2074
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2087
(.branch 2081
(.branch 2078
(.branch 2076
(.leaf (3341, 3339, 0))
(.branch 2077
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2079
(.leaf (3341, 3339, 0))
(.branch 2080
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2084
(.branch 2082
(.leaf (3341, 3339, 0))
(.branch 2083
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2085
(.leaf (3341, 3339, 0))
(.branch 2086
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2093
(.branch 2090
(.branch 2088
(.leaf (3341, 3339, 0))
(.branch 2089
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2091
(.leaf (3341, 3339, 0))
(.branch 2092
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2096
(.branch 2094
(.leaf (3341, 3339, 0))
(.branch 2095
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2098
(.branch 2097
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2099
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock21 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 2150
(.branch 2125
(.branch 2112
(.branch 2106
(.branch 2103
(.branch 2101
(.leaf (3341, 3339, 0))
(.branch 2102
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2104
(.leaf (3341, 3339, 0))
(.branch 2105
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2109
(.branch 2107
(.leaf (3341, 3339, 0))
(.branch 2108
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2110
(.leaf (3341, 3339, 0))
(.branch 2111
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2118
(.branch 2115
(.branch 2113
(.leaf (3341, 3339, 0))
(.branch 2114
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2116
(.leaf (3341, 3339, 0))
(.branch 2117
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2121
(.branch 2119
(.leaf (3341, 3339, 0))
(.branch 2120
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2123
(.branch 2122
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2124
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2137
(.branch 2131
(.branch 2128
(.branch 2126
(.leaf (3341, 3339, 0))
(.branch 2127
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2129
(.leaf (3341, 3339, 0))
(.branch 2130
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2134
(.branch 2132
(.leaf (3341, 3339, 0))
(.branch 2133
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2135
(.leaf (3341, 3339, 0))
(.branch 2136
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2143
(.branch 2140
(.branch 2138
(.leaf (3341, 3339, 0))
(.branch 2139
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2141
(.leaf (3341, 3339, 0))
(.branch 2142
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2146
(.branch 2144
(.leaf (3341, 3339, 0))
(.branch 2145
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2148
(.branch 2147
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2149
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 2175
(.branch 2162
(.branch 2156
(.branch 2153
(.branch 2151
(.leaf (3341, 3339, 0))
(.branch 2152
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2154
(.leaf (3341, 3339, 0))
(.branch 2155
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2159
(.branch 2157
(.leaf (3341, 3339, 0))
(.branch 2158
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2160
(.leaf (3341, 3339, 0))
(.branch 2161
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2168
(.branch 2165
(.branch 2163
(.leaf (3341, 3339, 0))
(.branch 2164
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2166
(.leaf (3341, 3339, 0))
(.branch 2167
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2171
(.branch 2169
(.leaf (3341, 3339, 0))
(.branch 2170
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2173
(.branch 2172
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2174
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2187
(.branch 2181
(.branch 2178
(.branch 2176
(.leaf (3341, 3339, 0))
(.branch 2177
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2179
(.leaf (3341, 3339, 0))
(.branch 2180
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2184
(.branch 2182
(.leaf (3341, 3339, 0))
(.branch 2183
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2185
(.leaf (3341, 3339, 0))
(.branch 2186
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2193
(.branch 2190
(.branch 2188
(.leaf (3341, 3339, 0))
(.branch 2189
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2191
(.leaf (3341, 3339, 0))
(.branch 2192
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2196
(.branch 2194
(.leaf (3341, 3339, 0))
(.branch 2195
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2198
(.branch 2197
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2199
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock22 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 2250
(.branch 2225
(.branch 2212
(.branch 2206
(.branch 2203
(.branch 2201
(.leaf (3341, 3339, 0))
(.branch 2202
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2204
(.leaf (3341, 3339, 0))
(.branch 2205
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2209
(.branch 2207
(.leaf (3341, 3339, 0))
(.branch 2208
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2210
(.leaf (3341, 3339, 0))
(.branch 2211
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2218
(.branch 2215
(.branch 2213
(.leaf (3341, 3339, 0))
(.branch 2214
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2216
(.leaf (3341, 3339, 0))
(.branch 2217
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2221
(.branch 2219
(.leaf (3341, 3339, 0))
(.branch 2220
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2223
(.branch 2222
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2224
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2237
(.branch 2231
(.branch 2228
(.branch 2226
(.leaf (3341, 3339, 0))
(.branch 2227
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2229
(.leaf (3341, 3339, 0))
(.branch 2230
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2234
(.branch 2232
(.leaf (3341, 3339, 0))
(.branch 2233
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2235
(.leaf (3341, 3339, 0))
(.branch 2236
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2243
(.branch 2240
(.branch 2238
(.leaf (3341, 3339, 0))
(.branch 2239
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2241
(.leaf (3341, 3339, 0))
(.branch 2242
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2246
(.branch 2244
(.leaf (3341, 3339, 0))
(.branch 2245
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2248
(.branch 2247
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2249
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 2275
(.branch 2262
(.branch 2256
(.branch 2253
(.branch 2251
(.leaf (3341, 3339, 0))
(.branch 2252
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2254
(.leaf (3341, 3339, 0))
(.branch 2255
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2259
(.branch 2257
(.leaf (3341, 3339, 0))
(.branch 2258
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2260
(.leaf (3341, 3339, 0))
(.branch 2261
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2268
(.branch 2265
(.branch 2263
(.leaf (3341, 3339, 0))
(.branch 2264
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2266
(.leaf (3341, 3339, 0))
(.branch 2267
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2271
(.branch 2269
(.leaf (3341, 3339, 0))
(.branch 2270
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2273
(.branch 2272
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2274
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2287
(.branch 2281
(.branch 2278
(.branch 2276
(.leaf (3341, 3339, 0))
(.branch 2277
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2279
(.leaf (3341, 3339, 0))
(.branch 2280
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2284
(.branch 2282
(.leaf (3341, 3339, 0))
(.branch 2283
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2285
(.leaf (3341, 3339, 0))
(.branch 2286
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2293
(.branch 2290
(.branch 2288
(.leaf (3341, 3339, 0))
(.branch 2289
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2291
(.leaf (3341, 3339, 0))
(.branch 2292
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2296
(.branch 2294
(.leaf (3341, 3339, 0))
(.branch 2295
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2298
(.branch 2297
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2299
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock23 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 2350
(.branch 2325
(.branch 2312
(.branch 2306
(.branch 2303
(.branch 2301
(.leaf (3341, 3339, 0))
(.branch 2302
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2304
(.leaf (3341, 3339, 0))
(.branch 2305
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2309
(.branch 2307
(.leaf (3341, 3339, 0))
(.branch 2308
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2310
(.leaf (3341, 3339, 0))
(.branch 2311
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2318
(.branch 2315
(.branch 2313
(.leaf (3341, 3339, 0))
(.branch 2314
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2316
(.leaf (3341, 3339, 0))
(.branch 2317
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2321
(.branch 2319
(.leaf (3341, 3339, 0))
(.branch 2320
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2323
(.branch 2322
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2324
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2337
(.branch 2331
(.branch 2328
(.branch 2326
(.leaf (3341, 3339, 0))
(.branch 2327
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2329
(.leaf (3341, 3339, 0))
(.branch 2330
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2334
(.branch 2332
(.leaf (3341, 3339, 0))
(.branch 2333
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2335
(.leaf (3341, 3339, 0))
(.branch 2336
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2343
(.branch 2340
(.branch 2338
(.leaf (3341, 3339, 0))
(.branch 2339
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2341
(.leaf (3341, 3339, 0))
(.branch 2342
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2346
(.branch 2344
(.leaf (3341, 3339, 0))
(.branch 2345
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2348
(.branch 2347
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2349
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 2375
(.branch 2362
(.branch 2356
(.branch 2353
(.branch 2351
(.leaf (3341, 3339, 0))
(.branch 2352
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2354
(.leaf (3341, 3339, 0))
(.branch 2355
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2359
(.branch 2357
(.leaf (3341, 3339, 0))
(.branch 2358
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2360
(.leaf (3341, 3339, 0))
(.branch 2361
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2368
(.branch 2365
(.branch 2363
(.leaf (3341, 3339, 0))
(.branch 2364
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2366
(.leaf (3341, 3339, 0))
(.branch 2367
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2371
(.branch 2369
(.leaf (3341, 3339, 0))
(.branch 2370
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2373
(.branch 2372
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2374
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2387
(.branch 2381
(.branch 2378
(.branch 2376
(.leaf (3341, 3339, 0))
(.branch 2377
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2379
(.leaf (3341, 3339, 0))
(.branch 2380
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2384
(.branch 2382
(.leaf (3341, 3339, 0))
(.branch 2383
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2385
(.leaf (3341, 3339, 0))
(.branch 2386
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2393
(.branch 2390
(.branch 2388
(.leaf (3341, 3339, 0))
(.branch 2389
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2391
(.leaf (3341, 3339, 0))
(.branch 2392
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2396
(.branch 2394
(.leaf (3341, 3339, 0))
(.branch 2395
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2398
(.branch 2397
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2399
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock24 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 2450
(.branch 2425
(.branch 2412
(.branch 2406
(.branch 2403
(.branch 2401
(.leaf (3341, 3339, 0))
(.branch 2402
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2404
(.leaf (3341, 3339, 0))
(.branch 2405
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2409
(.branch 2407
(.leaf (3341, 3339, 0))
(.branch 2408
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2410
(.leaf (3341, 3339, 0))
(.branch 2411
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2418
(.branch 2415
(.branch 2413
(.leaf (3341, 3339, 0))
(.branch 2414
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2416
(.leaf (3341, 3339, 0))
(.branch 2417
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2421
(.branch 2419
(.leaf (3341, 3339, 0))
(.branch 2420
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2423
(.branch 2422
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2424
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2437
(.branch 2431
(.branch 2428
(.branch 2426
(.leaf (3341, 3339, 0))
(.branch 2427
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2429
(.leaf (3341, 3339, 0))
(.branch 2430
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2434
(.branch 2432
(.leaf (3341, 3339, 0))
(.branch 2433
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2435
(.leaf (3341, 3339, 0))
(.branch 2436
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2443
(.branch 2440
(.branch 2438
(.leaf (3341, 3339, 0))
(.branch 2439
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2441
(.leaf (3341, 3339, 0))
(.branch 2442
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2446
(.branch 2444
(.leaf (3341, 3339, 0))
(.branch 2445
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2448
(.branch 2447
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2449
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 2475
(.branch 2462
(.branch 2456
(.branch 2453
(.branch 2451
(.leaf (3341, 3339, 0))
(.branch 2452
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2454
(.leaf (3341, 3339, 0))
(.branch 2455
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2459
(.branch 2457
(.leaf (3341, 3339, 0))
(.branch 2458
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2460
(.leaf (3341, 3339, 0))
(.branch 2461
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2468
(.branch 2465
(.branch 2463
(.leaf (3341, 3339, 0))
(.branch 2464
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2466
(.leaf (3341, 3339, 0))
(.branch 2467
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2471
(.branch 2469
(.leaf (3341, 3339, 0))
(.branch 2470
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2473
(.branch 2472
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2474
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2487
(.branch 2481
(.branch 2478
(.branch 2476
(.leaf (3341, 3339, 0))
(.branch 2477
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2479
(.leaf (3341, 3339, 0))
(.branch 2480
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2484
(.branch 2482
(.leaf (3341, 3339, 0))
(.branch 2483
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2485
(.leaf (3341, 3339, 0))
(.branch 2486
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2493
(.branch 2490
(.branch 2488
(.leaf (3341, 3339, 0))
(.branch 2489
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2491
(.leaf (3341, 3339, 0))
(.branch 2492
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2496
(.branch 2494
(.leaf (3341, 3339, 0))
(.branch 2495
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2498
(.branch 2497
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2499
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock25 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 2550
(.branch 2525
(.branch 2512
(.branch 2506
(.branch 2503
(.branch 2501
(.leaf (3341, 3339, 0))
(.branch 2502
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2504
(.leaf (3341, 3339, 0))
(.branch 2505
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2509
(.branch 2507
(.leaf (3341, 3339, 0))
(.branch 2508
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2510
(.leaf (3341, 3339, 0))
(.branch 2511
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2518
(.branch 2515
(.branch 2513
(.leaf (3341, 3339, 0))
(.branch 2514
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2516
(.leaf (3341, 3339, 0))
(.branch 2517
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2521
(.branch 2519
(.leaf (3341, 3339, 0))
(.branch 2520
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2523
(.branch 2522
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2524
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2537
(.branch 2531
(.branch 2528
(.branch 2526
(.leaf (3341, 3339, 0))
(.branch 2527
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2529
(.leaf (3341, 3339, 0))
(.branch 2530
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2534
(.branch 2532
(.leaf (3341, 3339, 0))
(.branch 2533
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2535
(.leaf (3341, 3339, 0))
(.branch 2536
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2543
(.branch 2540
(.branch 2538
(.leaf (3341, 3339, 0))
(.branch 2539
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2541
(.leaf (3341, 3339, 0))
(.branch 2542
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2546
(.branch 2544
(.leaf (3341, 3339, 0))
(.branch 2545
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2548
(.branch 2547
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2549
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 2575
(.branch 2562
(.branch 2556
(.branch 2553
(.branch 2551
(.leaf (3341, 3339, 0))
(.branch 2552
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2554
(.leaf (3341, 3339, 0))
(.branch 2555
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2559
(.branch 2557
(.leaf (3341, 3339, 0))
(.branch 2558
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2560
(.leaf (3341, 3339, 0))
(.branch 2561
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2568
(.branch 2565
(.branch 2563
(.leaf (3341, 3339, 0))
(.branch 2564
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2566
(.leaf (3341, 3339, 0))
(.branch 2567
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2571
(.branch 2569
(.leaf (3341, 3339, 0))
(.branch 2570
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2573
(.branch 2572
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2574
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2587
(.branch 2581
(.branch 2578
(.branch 2576
(.leaf (3341, 3339, 0))
(.branch 2577
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2579
(.leaf (3341, 3339, 0))
(.branch 2580
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2584
(.branch 2582
(.leaf (3341, 3339, 0))
(.branch 2583
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2585
(.leaf (3341, 3339, 0))
(.branch 2586
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2593
(.branch 2590
(.branch 2588
(.leaf (3341, 3339, 0))
(.branch 2589
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2591
(.leaf (3341, 3339, 0))
(.branch 2592
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2596
(.branch 2594
(.leaf (3341, 3339, 0))
(.branch 2595
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2598
(.branch 2597
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2599
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock26 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 2650
(.branch 2625
(.branch 2612
(.branch 2606
(.branch 2603
(.branch 2601
(.leaf (3341, 3339, 0))
(.branch 2602
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2604
(.leaf (3341, 3339, 0))
(.branch 2605
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2609
(.branch 2607
(.leaf (3341, 3339, 0))
(.branch 2608
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2610
(.leaf (3341, 3339, 0))
(.branch 2611
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2618
(.branch 2615
(.branch 2613
(.leaf (3341, 3339, 0))
(.branch 2614
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2616
(.leaf (3341, 3339, 0))
(.branch 2617
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2621
(.branch 2619
(.leaf (3341, 3339, 0))
(.branch 2620
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2623
(.branch 2622
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2624
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2637
(.branch 2631
(.branch 2628
(.branch 2626
(.leaf (3341, 3339, 0))
(.branch 2627
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2629
(.leaf (3341, 3339, 0))
(.branch 2630
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2634
(.branch 2632
(.leaf (3341, 3339, 0))
(.branch 2633
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2635
(.leaf (3341, 3339, 0))
(.branch 2636
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2643
(.branch 2640
(.branch 2638
(.leaf (3341, 3339, 0))
(.branch 2639
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2641
(.leaf (3341, 3339, 0))
(.branch 2642
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2646
(.branch 2644
(.leaf (3341, 3339, 0))
(.branch 2645
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2648
(.branch 2647
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2649
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 2675
(.branch 2662
(.branch 2656
(.branch 2653
(.branch 2651
(.leaf (3341, 3339, 0))
(.branch 2652
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2654
(.leaf (3341, 3339, 0))
(.branch 2655
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2659
(.branch 2657
(.leaf (3341, 3339, 0))
(.branch 2658
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2660
(.leaf (3341, 3339, 0))
(.branch 2661
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2668
(.branch 2665
(.branch 2663
(.leaf (3341, 3339, 0))
(.branch 2664
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2666
(.leaf (3341, 3339, 0))
(.branch 2667
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2671
(.branch 2669
(.leaf (3341, 3339, 0))
(.branch 2670
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2673
(.branch 2672
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2674
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2687
(.branch 2681
(.branch 2678
(.branch 2676
(.leaf (3341, 3339, 0))
(.branch 2677
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2679
(.leaf (3341, 3339, 0))
(.branch 2680
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2684
(.branch 2682
(.leaf (3341, 3339, 0))
(.branch 2683
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2685
(.leaf (3341, 3339, 0))
(.branch 2686
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2693
(.branch 2690
(.branch 2688
(.leaf (3341, 3339, 0))
(.branch 2689
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2691
(.leaf (3341, 3339, 0))
(.branch 2692
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2696
(.branch 2694
(.leaf (3341, 3339, 0))
(.branch 2695
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2698
(.branch 2697
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2699
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock27 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 2750
(.branch 2725
(.branch 2712
(.branch 2706
(.branch 2703
(.branch 2701
(.leaf (3341, 3339, 0))
(.branch 2702
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2704
(.leaf (3341, 3339, 0))
(.branch 2705
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2709
(.branch 2707
(.leaf (3341, 3339, 0))
(.branch 2708
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2710
(.leaf (3341, 3339, 0))
(.branch 2711
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2718
(.branch 2715
(.branch 2713
(.leaf (3341, 3339, 0))
(.branch 2714
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2716
(.leaf (3341, 3339, 0))
(.branch 2717
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2721
(.branch 2719
(.leaf (3341, 3339, 0))
(.branch 2720
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2723
(.branch 2722
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2724
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2737
(.branch 2731
(.branch 2728
(.branch 2726
(.leaf (3341, 3339, 0))
(.branch 2727
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2729
(.leaf (3341, 3339, 0))
(.branch 2730
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2734
(.branch 2732
(.leaf (3341, 3339, 0))
(.branch 2733
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2735
(.leaf (3341, 3339, 0))
(.branch 2736
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2743
(.branch 2740
(.branch 2738
(.leaf (3341, 3339, 0))
(.branch 2739
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2741
(.leaf (3341, 3339, 0))
(.branch 2742
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2746
(.branch 2744
(.leaf (3341, 3339, 0))
(.branch 2745
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2748
(.branch 2747
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2749
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 2775
(.branch 2762
(.branch 2756
(.branch 2753
(.branch 2751
(.leaf (3341, 3339, 0))
(.branch 2752
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2754
(.leaf (3341, 3339, 0))
(.branch 2755
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2759
(.branch 2757
(.leaf (3341, 3339, 0))
(.branch 2758
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2760
(.leaf (3341, 3339, 0))
(.branch 2761
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2768
(.branch 2765
(.branch 2763
(.leaf (3341, 3339, 0))
(.branch 2764
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2766
(.leaf (3341, 3339, 0))
(.branch 2767
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2771
(.branch 2769
(.leaf (3341, 3339, 0))
(.branch 2770
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2773
(.branch 2772
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2774
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2787
(.branch 2781
(.branch 2778
(.branch 2776
(.leaf (3341, 3339, 0))
(.branch 2777
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2779
(.leaf (3341, 3339, 0))
(.branch 2780
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2784
(.branch 2782
(.leaf (3341, 3339, 0))
(.branch 2783
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2785
(.leaf (3341, 3339, 0))
(.branch 2786
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2793
(.branch 2790
(.branch 2788
(.leaf (3341, 3339, 0))
(.branch 2789
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2791
(.leaf (3341, 3339, 0))
(.branch 2792
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2796
(.branch 2794
(.leaf (3341, 3339, 0))
(.branch 2795
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2798
(.branch 2797
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2799
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock28 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 2850
(.branch 2825
(.branch 2812
(.branch 2806
(.branch 2803
(.branch 2801
(.leaf (3341, 3339, 0))
(.branch 2802
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2804
(.leaf (3341, 3339, 0))
(.branch 2805
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2809
(.branch 2807
(.leaf (3341, 3339, 0))
(.branch 2808
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2810
(.leaf (3341, 3339, 0))
(.branch 2811
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2818
(.branch 2815
(.branch 2813
(.leaf (3341, 3339, 0))
(.branch 2814
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2816
(.leaf (3341, 3339, 0))
(.branch 2817
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2821
(.branch 2819
(.leaf (3341, 3339, 0))
(.branch 2820
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2823
(.branch 2822
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2824
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2837
(.branch 2831
(.branch 2828
(.branch 2826
(.leaf (3341, 3339, 0))
(.branch 2827
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2829
(.leaf (3341, 3339, 0))
(.branch 2830
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2834
(.branch 2832
(.leaf (3341, 3339, 0))
(.branch 2833
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2835
(.leaf (3341, 3339, 0))
(.branch 2836
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2843
(.branch 2840
(.branch 2838
(.leaf (3341, 3339, 0))
(.branch 2839
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2841
(.leaf (3341, 3339, 0))
(.branch 2842
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2846
(.branch 2844
(.leaf (3341, 3339, 0))
(.branch 2845
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2848
(.branch 2847
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2849
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 2875
(.branch 2862
(.branch 2856
(.branch 2853
(.branch 2851
(.leaf (3341, 3339, 0))
(.branch 2852
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2854
(.leaf (3341, 3339, 0))
(.branch 2855
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2859
(.branch 2857
(.leaf (3341, 3339, 0))
(.branch 2858
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2860
(.leaf (3341, 3339, 0))
(.branch 2861
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2868
(.branch 2865
(.branch 2863
(.leaf (3341, 3339, 0))
(.branch 2864
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2866
(.leaf (3341, 3339, 0))
(.branch 2867
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2871
(.branch 2869
(.leaf (3341, 3339, 0))
(.branch 2870
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2873
(.branch 2872
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2874
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2887
(.branch 2881
(.branch 2878
(.branch 2876
(.leaf (3341, 3339, 0))
(.branch 2877
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2879
(.leaf (3341, 3339, 0))
(.branch 2880
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2884
(.branch 2882
(.leaf (3341, 3339, 0))
(.branch 2883
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2885
(.leaf (3341, 3339, 0))
(.branch 2886
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2893
(.branch 2890
(.branch 2888
(.leaf (3341, 3339, 0))
(.branch 2889
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2891
(.leaf (3341, 3339, 0))
(.branch 2892
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2896
(.branch 2894
(.leaf (3341, 3339, 0))
(.branch 2895
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2898
(.branch 2897
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2899
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock29 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 2950
(.branch 2925
(.branch 2912
(.branch 2906
(.branch 2903
(.branch 2901
(.leaf (3341, 3339, 0))
(.branch 2902
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2904
(.leaf (3341, 3339, 0))
(.branch 2905
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2909
(.branch 2907
(.leaf (3341, 3339, 0))
(.branch 2908
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2910
(.leaf (3341, 3339, 0))
(.branch 2911
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2918
(.branch 2915
(.branch 2913
(.leaf (3341, 3339, 0))
(.branch 2914
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2916
(.leaf (3341, 3339, 0))
(.branch 2917
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2921
(.branch 2919
(.leaf (3341, 3339, 0))
(.branch 2920
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2923
(.branch 2922
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2924
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2937
(.branch 2931
(.branch 2928
(.branch 2926
(.leaf (3341, 3339, 0))
(.branch 2927
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2929
(.leaf (3341, 3339, 0))
(.branch 2930
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2934
(.branch 2932
(.leaf (3341, 3339, 0))
(.branch 2933
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2935
(.leaf (3341, 3339, 0))
(.branch 2936
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2943
(.branch 2940
(.branch 2938
(.leaf (3341, 3339, 0))
(.branch 2939
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2941
(.leaf (3341, 3339, 0))
(.branch 2942
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2946
(.branch 2944
(.leaf (3341, 3339, 0))
(.branch 2945
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2948
(.branch 2947
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2949
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 2975
(.branch 2962
(.branch 2956
(.branch 2953
(.branch 2951
(.leaf (3341, 3339, 0))
(.branch 2952
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2954
(.leaf (3341, 3339, 0))
(.branch 2955
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2959
(.branch 2957
(.leaf (3341, 3339, 0))
(.branch 2958
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2960
(.leaf (3341, 3339, 0))
(.branch 2961
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2968
(.branch 2965
(.branch 2963
(.leaf (3341, 3339, 0))
(.branch 2964
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2966
(.leaf (3341, 3339, 0))
(.branch 2967
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2971
(.branch 2969
(.leaf (3341, 3339, 0))
(.branch 2970
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2973
(.branch 2972
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2974
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 2987
(.branch 2981
(.branch 2978
(.branch 2976
(.leaf (3341, 3339, 0))
(.branch 2977
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2979
(.leaf (3341, 3339, 0))
(.branch 2980
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2984
(.branch 2982
(.leaf (3341, 3339, 0))
(.branch 2983
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2985
(.leaf (3341, 3339, 0))
(.branch 2986
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 2993
(.branch 2990
(.branch 2988
(.leaf (3341, 3339, 0))
(.branch 2989
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2991
(.leaf (3341, 3339, 0))
(.branch 2992
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 2996
(.branch 2994
(.leaf (3341, 3339, 0))
(.branch 2995
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 2998
(.branch 2997
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 2999
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock30 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 3050
(.branch 3025
(.branch 3012
(.branch 3006
(.branch 3003
(.branch 3001
(.leaf (3341, 3339, 0))
(.branch 3002
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3004
(.leaf (3341, 3339, 0))
(.branch 3005
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3009
(.branch 3007
(.leaf (3341, 3339, 0))
(.branch 3008
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3010
(.leaf (3341, 3339, 0))
(.branch 3011
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3018
(.branch 3015
(.branch 3013
(.leaf (3341, 3339, 0))
(.branch 3014
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3016
(.leaf (3341, 3339, 0))
(.branch 3017
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3021
(.branch 3019
(.leaf (3341, 3339, 0))
(.branch 3020
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3023
(.branch 3022
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3024
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 3037
(.branch 3031
(.branch 3028
(.branch 3026
(.leaf (3341, 3339, 0))
(.branch 3027
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3029
(.leaf (3341, 3339, 0))
(.branch 3030
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3034
(.branch 3032
(.leaf (3341, 3339, 0))
(.branch 3033
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3035
(.leaf (3341, 3339, 0))
(.branch 3036
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3043
(.branch 3040
(.branch 3038
(.leaf (3341, 3339, 0))
(.branch 3039
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3041
(.leaf (3341, 3339, 0))
(.branch 3042
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3046
(.branch 3044
(.leaf (3341, 3339, 0))
(.branch 3045
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3048
(.branch 3047
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3049
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 3075
(.branch 3062
(.branch 3056
(.branch 3053
(.branch 3051
(.leaf (3341, 3339, 0))
(.branch 3052
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3054
(.leaf (3341, 3339, 0))
(.branch 3055
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3059
(.branch 3057
(.leaf (3341, 3339, 0))
(.branch 3058
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3060
(.leaf (3341, 3339, 0))
(.branch 3061
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3068
(.branch 3065
(.branch 3063
(.leaf (3341, 3339, 0))
(.branch 3064
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3066
(.leaf (3341, 3339, 0))
(.branch 3067
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3071
(.branch 3069
(.leaf (3341, 3339, 0))
(.branch 3070
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3073
(.branch 3072
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3074
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 3087
(.branch 3081
(.branch 3078
(.branch 3076
(.leaf (3341, 3339, 0))
(.branch 3077
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3079
(.leaf (3341, 3339, 0))
(.branch 3080
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3084
(.branch 3082
(.leaf (3341, 3339, 0))
(.branch 3083
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3085
(.leaf (3341, 3339, 0))
(.branch 3086
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3093
(.branch 3090
(.branch 3088
(.leaf (3341, 3339, 0))
(.branch 3089
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3091
(.leaf (3341, 3339, 0))
(.branch 3092
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3096
(.branch 3094
(.leaf (3341, 3339, 0))
(.branch 3095
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3098
(.branch 3097
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3099
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock31 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 3150
(.branch 3125
(.branch 3112
(.branch 3106
(.branch 3103
(.branch 3101
(.leaf (3341, 3339, 0))
(.branch 3102
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3104
(.leaf (3341, 3339, 0))
(.branch 3105
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3109
(.branch 3107
(.leaf (3341, 3339, 0))
(.branch 3108
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3110
(.leaf (3341, 3339, 0))
(.branch 3111
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3118
(.branch 3115
(.branch 3113
(.leaf (3341, 3339, 0))
(.branch 3114
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3116
(.leaf (3341, 3339, 0))
(.branch 3117
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3121
(.branch 3119
(.leaf (3341, 3339, 0))
(.branch 3120
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3123
(.branch 3122
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3124
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 3137
(.branch 3131
(.branch 3128
(.branch 3126
(.leaf (3341, 3339, 0))
(.branch 3127
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3129
(.leaf (3341, 3339, 0))
(.branch 3130
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3134
(.branch 3132
(.leaf (3341, 3339, 0))
(.branch 3133
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3135
(.leaf (3341, 3339, 0))
(.branch 3136
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3143
(.branch 3140
(.branch 3138
(.leaf (3341, 3339, 0))
(.branch 3139
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3141
(.leaf (3341, 3339, 0))
(.branch 3142
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3146
(.branch 3144
(.leaf (3341, 3339, 0))
(.branch 3145
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3148
(.branch 3147
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3149
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 3175
(.branch 3162
(.branch 3156
(.branch 3153
(.branch 3151
(.leaf (3341, 3339, 0))
(.branch 3152
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3154
(.leaf (3341, 3339, 0))
(.branch 3155
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3159
(.branch 3157
(.leaf (3341, 3339, 0))
(.branch 3158
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3160
(.leaf (3341, 3339, 0))
(.branch 3161
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3168
(.branch 3165
(.branch 3163
(.leaf (3341, 3339, 0))
(.branch 3164
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3166
(.leaf (3341, 3339, 0))
(.branch 3167
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3171
(.branch 3169
(.leaf (3341, 3339, 0))
(.branch 3170
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3173
(.branch 3172
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3174
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 3187
(.branch 3181
(.branch 3178
(.branch 3176
(.leaf (3341, 3339, 0))
(.branch 3177
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3179
(.leaf (3341, 3339, 0))
(.branch 3180
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3184
(.branch 3182
(.leaf (3341, 3339, 0))
(.branch 3183
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3185
(.leaf (3341, 3339, 0))
(.branch 3186
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3193
(.branch 3190
(.branch 3188
(.leaf (3341, 3339, 0))
(.branch 3189
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3191
(.leaf (3341, 3339, 0))
(.branch 3192
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3196
(.branch 3194
(.leaf (3341, 3339, 0))
(.branch 3195
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3198
(.branch 3197
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3199
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock32 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 3250
(.branch 3225
(.branch 3212
(.branch 3206
(.branch 3203
(.branch 3201
(.leaf (3341, 3339, 0))
(.branch 3202
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3204
(.leaf (3341, 3339, 0))
(.branch 3205
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3209
(.branch 3207
(.leaf (3341, 3339, 0))
(.branch 3208
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3210
(.leaf (3341, 3339, 0))
(.branch 3211
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3218
(.branch 3215
(.branch 3213
(.leaf (3341, 3339, 0))
(.branch 3214
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3216
(.leaf (3341, 3339, 0))
(.branch 3217
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3221
(.branch 3219
(.leaf (3341, 3339, 0))
(.branch 3220
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3223
(.branch 3222
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3224
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 3237
(.branch 3231
(.branch 3228
(.branch 3226
(.leaf (3341, 3339, 0))
(.branch 3227
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3229
(.leaf (3341, 3339, 0))
(.branch 3230
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3234
(.branch 3232
(.leaf (3341, 3339, 0))
(.branch 3233
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3235
(.leaf (3341, 3339, 0))
(.branch 3236
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3243
(.branch 3240
(.branch 3238
(.leaf (3341, 3339, 0))
(.branch 3239
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3241
(.leaf (3341, 3339, 0))
(.branch 3242
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3246
(.branch 3244
(.leaf (3341, 3339, 0))
(.branch 3245
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3248
(.branch 3247
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3249
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))))
(.branch 3275
(.branch 3262
(.branch 3256
(.branch 3253
(.branch 3251
(.leaf (3341, 3339, 0))
(.branch 3252
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3254
(.leaf (3341, 3339, 0))
(.branch 3255
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3259
(.branch 3257
(.leaf (3341, 3339, 0))
(.branch 3258
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3260
(.leaf (3341, 3339, 0))
(.branch 3261
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3268
(.branch 3265
(.branch 3263
(.leaf (3341, 3339, 0))
(.branch 3264
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3266
(.leaf (3341, 3339, 0))
(.branch 3267
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3271
(.branch 3269
(.leaf (3341, 3339, 0))
(.branch 3270
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3273
(.branch 3272
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3274
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 3287
(.branch 3281
(.branch 3278
(.branch 3276
(.leaf (3341, 3339, 0))
(.branch 3277
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3279
(.leaf (3341, 3339, 0))
(.branch 3280
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3284
(.branch 3282
(.leaf (3341, 3339, 0))
(.branch 3283
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3285
(.leaf (3341, 3339, 0))
(.branch 3286
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3293
(.branch 3290
(.branch 3288
(.leaf (3341, 3339, 0))
(.branch 3289
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3291
(.leaf (3341, 3339, 0))
(.branch 3292
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3296
(.branch 3294
(.leaf (3341, 3339, 0))
(.branch 3295
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3298
(.branch 3297
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3299
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))))

def rowDataBlock33 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 3350
(.branch 3325
(.branch 3312
(.branch 3306
(.branch 3303
(.branch 3301
(.leaf (3341, 3339, 0))
(.branch 3302
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3304
(.leaf (3341, 3339, 0))
(.branch 3305
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3309
(.branch 3307
(.leaf (3341, 3339, 0))
(.branch 3308
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3310
(.leaf (3341, 3339, 0))
(.branch 3311
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3318
(.branch 3315
(.branch 3313
(.leaf (3341, 3339, 0))
(.branch 3314
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3316
(.leaf (3341, 3339, 0))
(.branch 3317
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3321
(.branch 3319
(.leaf (3341, 3339, 0))
(.branch 3320
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3323
(.branch 3322
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))
(.branch 3324
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))))
(.branch 3337
(.branch 3331
(.branch 3328
(.branch 3326
(.leaf (3341, 3339, 0))
(.branch 3327
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3329
(.leaf (3341, 3339, 0))
(.branch 3330
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0)))))
(.branch 3334
(.branch 3332
(.leaf (3341, 3339, 0))
(.branch 3333
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))
(.branch 3335
(.leaf (3341, 3339, 0))
(.branch 3336
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 0))))))
(.branch 3343
(.branch 3340
(.branch 3338
(.leaf (3341, 3339, 0))
(.branch 3339
(.leaf (3341, 3339, 0))
(.leaf (3341, 3339, 383))))
(.branch 3341
(.leaf (3341, 3339, 25106061))
(.branch 3342
(.leaf (3341, 3339, 1645972947327))
(.leaf (3341, 3336, 30345161171478897120014260502911)))))
(.branch 3346
(.branch 3344
(.leaf (3341, 3336, 1988740888896913850183203444899119743))
(.branch 3345
(.leaf (3341, 3336, 130331464438756576253860612224888244076927))
(.leaf (3338, 3336, 741477266241410627368832332929272580604800))))
(.branch 3348
(.branch 3347
(.leaf (3338, 3336, 130331474823351845584268543263067330249087))
(.leaf (3338, 3336, 217442421528996323019480897534055587709569)))
(.branch 3349
(.leaf (3338, 3336, 772510664017155378498371967))
(.leaf (3338, 3336, 463035080409412530841006759))))))))
(.branch 3375
(.branch 3362
(.branch 3356
(.branch 3353
(.branch 3351
(.leaf (3338, 3336, 1704592471227701898344661375))
(.branch 3352
(.leaf (3338, 3335, 30345777723646901143843280781695))
(.leaf (3338, 3335, 50785715202019930073404190687360))))
(.branch 3354
(.leaf (3338, 3335, 30346399111518038666576010346879))
(.branch 3355
(.leaf (3337, 3335, 70830440322869620709315141633151))
(.leaf (3337, 3335, 30345158753628125959584053330303)))))
(.branch 3359
(.branch 3357
(.leaf (3337, 3335, 759956997895608001744521186445433))
(.branch 3358
(.leaf (3337, 3335, 5105300801732440597718958463))
(.leaf (3337, 3335, 463030413383179500280284034))))
(.branch 3360
(.leaf (3337, 3335, 1085622451296781384743387519))
(.branch 3361
(.leaf (3337, 3335, 463035117302901773476758143))
(.leaf (3337, 3335, 154749570194079870963548543))))))
(.branch 3368
(.branch 3365
(.branch 3363
(.leaf (3337, 3335, 463030376489678132951851360))
(.branch 3364
(.leaf (3337, 3335, 11641962709392480312305320319))
(.leaf (3337, 3335, 463035154196388834269136254))))
(.branch 3366
(.leaf (3337, 3335, 772510664088368547622879615))
(.branch 3367
(.leaf (3337, 3335, 463035117302900678260101253))
(.leaf (3337, 3335, 4801860421371426969894322559)))))
(.branch 3371
(.branch 3369
(.leaf (3337, 3335, 463030413383159687596146816))
(.branch 3370
(.leaf (3337, 3335, 1697338916021783747195044223))
(.leaf (3337, 3335, 463035080409416954657309311))))
(.branch 3373
(.branch 3372
(.leaf (3337, 3335, 7872532002613872521631039871))
(.leaf (3337, 3335, 463030376489678141541781378)))
(.branch 3374
(.leaf (3337, 3335, 2005615000168192324757553535))
(.leaf (3337, 3335, 463044598929354573559563903)))))))
(.branch 3387
(.branch 3381
(.branch 3378
(.branch 3376
(.leaf (3337, 3335, 772510663872758715445674367))
(.branch 3377
(.leaf (3337, 3335, 463020950203452069324456830))
(.leaf (3337, 3335, 154749571857878457543360895))))
(.branch 3379
(.leaf (3337, 3335, 463030413383172851670910081))
(.branch 3380
(.leaf (3337, 3335, 154749570193516920270094719))
(.leaf (3337, 3335, 463020950203454268347712127)))))
(.branch 3384
(.branch 3382
(.leaf (3337, 3335, 1393898535299074774297215359))
(.branch 3383
(.leaf (3337, 3335, 463030376489677054915057773))
(.leaf (3337, 3335, 2634256426800145059832332671))))
(.branch 3385
(.leaf (3337, 3335, 463035117302900686850032514))
(.branch 3386
(.leaf (3337, 3335, 772510664595304980611596671))
(.leaf (3337, 3335, 463200713724450368904956027))))))
(.branch 3393
(.branch 3390
(.branch 3388
(.leaf (3337, 3335, 154749570625299534527398271))
(.branch 3389
(.leaf (3337, 3335, 463030413383165176564352127))
(.leaf (3337, 3335, 154749570193516920219631999))))
(.branch 3391
(.leaf (3337, 3335, 463035117302918201726665343))
(.branch 3392
(.leaf (3337, 3335, 1704592470940034472230519167))
(.leaf (3337, 3335, 463030376489699002197935749)))))
(.branch 3396
(.branch 3394
(.leaf (3337, 3335, 154749570337632108328976767))
(.branch 3395
(.leaf (3337, 3335, 463039858116127630204799107))
(.leaf (3337, 3335, 772510664089494448131735935))))
(.branch 3398
(.branch 3397
(.leaf (3337, 3335, 463035117302900678260109423))
(.leaf (3337, 3335, 154749574364413125151752575)))
(.branch 3399
(.leaf (3337, 3335, 463030413383165193744232328))
(.leaf (3337, 3335, 154749570193516920269963647)))))))))

def rowDataBlock34 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 3450
(.branch 3425
(.branch 3412
(.branch 3406
(.branch 3403
(.branch 3401
(.leaf (3337, 3335, 463143934646192603301610111))
(.branch 3402
(.leaf (3337, 3335, 1080786748018885818065027455))
(.leaf (3337, 3335, 463030376489711126890611582))))
(.branch 3404
(.leaf (3337, 3335, 3250808596597445965509493119))
(.branch 3405
(.leaf (3337, 3335, 463020950203452077914396544))
(.leaf (3337, 3335, 772510664663703400002617727)))))
(.branch 3409
(.branch 3407
(.leaf (3337, 3335, 463039821222639474195760508))
(.branch 3408
(.leaf (3337, 3335, 154749570338195058282529151))
(.leaf (3337, 3335, 463030413383212666017754279))))
(.branch 3410
(.leaf (3337, 3335, 10688120236495780919569219967))
(.branch 3411
(.leaf (3337, 3335, 463020950203459787380687487))
(.leaf (3337, 3335, 1085622451297344334747140479))))))
(.branch 3418
(.branch 3415
(.branch 3413
(.leaf (3337, 3335, 463030376489674830121993345))
(.branch 3414
(.leaf (3337, 3335, 154749570049683207153975679))
(.leaf (3337, 3335, 463035117302900686850034303))))
(.branch 3416
(.leaf (3337, 3335, 772510664233609635622027647))
(.branch 3417
(.leaf (3337, 3335, 463035154196388825679200384))
(.leaf (3337, 3335, 8498755577245463603136495999)))))
(.branch 3421
(.branch 3419
(.leaf (3337, 3335, 463030413383227930331512960))
(.branch 3420
(.leaf (3337, 3335, 1391480683659282566597312895))
(.leaf (3337, 3335, 463035117302902885873287807))))
(.branch 3423
(.branch 3422
(.leaf (3337, 3335, 154749570194079870307467647))
(.leaf (3337, 3335, 463030376489724132051584127)))
(.branch 3424
(.leaf (3337, 3335, 10343576381584208075308335487))
(.leaf (3337, 3335, 463049265955605222076123271)))))))
(.branch 3437
(.branch 3431
(.branch 3428
(.branch 3426
(.leaf (3337, 3335, 772510665165010333473964415))
(.branch 3427
(.leaf (3337, 3335, 463035117302900678260100482))
(.leaf (3337, 3335, 1080786748162438056154038655))))
(.branch 3429
(.leaf (3337, 3332, 130331474823350293323515869285880868897151))
(.branch 3430
(.leaf (3337, 3330, 6186544972224565511168026498722175562967755840750464))
(.leaf (3337, 3330, 559797944658845807643505522227456209938154965303679)))))
(.branch 3434
(.branch 3432
(.leaf (3334, 3323, 16459610080899637010187255450391234427927479365210777080249070367360348672505050825087))
(.branch 3433
(.leaf (3332, 3323, 2906488779800431436241581449268834856024901153690825865843613063984610199597628720257))
(.leaf (3332, 3323, 971378796963706032433875055752432309996657418529439971520564041103070540892064514431))))
(.branch 3435
(.leaf (3325, 3321, 74223405948433960149585515251441539420667150107246701307634760279832537686016128))
(.branch 3436
(.leaf (3325, 3321, 10326761652600347673101134519393724165135553133675581721680170342154623))
(.leaf (3325, 3318, 6814562573013302443450905584673970412905885170120088349474717430764839640271406694783))))))
(.branch 3443
(.branch 3440
(.branch 3438
(.leaf (3323, 3318, 13232444365797529044541471316379894850007679071356800))
(.branch 3439
(.leaf (3323, 3318, 559775108695829176184774700542773753867647330615679))
(.leaf (3320, 3318, 933908092285480895635825707811462169209761171440255))))
(.branch 3441
(.leaf (3320, 3318, 130331464438761534058647357629666913550719))
(.branch 3442
(.leaf (3320, 3318, 391666993046685886928483236489414859227777))
(.leaf (3320, 3318, 2323562490582724609629421951)))))
(.branch 3446
(.branch 3444
(.leaf (3320, 3318, 463068155421543314906612610))
(.branch 3445
(.leaf (3320, 3318, 772510664088931497509126527))
(.leaf (3320, 3318, 463039858116127621614862464))))
(.branch 3448
(.branch 3447
(.leaf (3320, 3318, 774928516956799029301543295))
(.leaf (3320, 3315, 130352700932915116361197028829955474129279)))
(.branch 3449
(.leaf (3320, 3311, 12039517813517571269909572054522250139773968319088377674531455))
(.leaf (3320, 3311, 2404191360815462653944948024396853849679952245129555025658239))))))))
(.branch 3475
(.branch 3462
(.branch 3456
(.branch 3453
(.branch 3451
(.leaf (3317, 3311, 8850750132316743362849257649313617410568747034635236288693375))
(.branch 3452
(.leaf (3313, 3311, 2404191169253668680175588946591296944929434743219509004271999))
(.leaf (3313, 3311, 8825641725002513722099629112240247729612444479271196468118145))))
(.branch 3454
(.leaf (3313, 3311, 31488782553124098925685899855875911230481760639))
(.branch 3455
(.leaf (3313, 3311, 463091859487671408840870784))
(.leaf (3313, 3311, 1393898535442627012369318271)))))
(.branch 3459
(.branch 3457
(.leaf (3313, 3311, 463035117302900686850031744))
(.branch 3458
(.leaf (3313, 3311, 774928515655821687011475839))
(.leaf (3313, 3311, 463035080409460823453270655))))
(.branch 3460
(.leaf (3313, 3311, 17166753704461067337896886655))
(.branch 3461
(.leaf (3313, 3310, 30345158753627402568893990633855))
(.leaf (3313, 3310, 517677276936543070813645334054274))))))
(.branch 3468
(.branch 3465
(.branch 3463
(.leaf (3313, 3310, 30345469447562755016740661428607))
(.branch 3464
(.leaf (3312, 3310, 50627258877028294886355931955328))
(.leaf (3312, 3310, 30346391857963264812514077966719))))
(.branch 3466
(.leaf (3312, 3309, 11314045207008582220134127727644967295))
(.branch 3467
(.leaf (3312, 3309, 539148108939982200514596338335872))
(.leaf (3312, 3309, 30345158753627114057042845630847)))))
(.branch 3471
(.branch 3469
(.leaf (3311, 3309, 70988896647935042872641058701953))
(.branch 3470
(.leaf (3311, 3309, 30347022917241104211893278540159))
(.leaf (3311, 3309, 50627258957179397943807128307076))))
(.branch 3473
(.branch 3472
(.leaf (3311, 3309, 1704592470939471522259992959))
(.leaf (3311, 3309, 463228346947072794403209855)))
(.branch 3474
(.leaf (3311, 3309, 774928515728723705811960191))
(.leaf (3311, 3309, 463030376489671540177044352)))))))
(.branch 3487
(.branch 3481
(.branch 3478
(.branch 3476
(.leaf (3311, 3309, 5413576885805384206376698239))
(.branch 3477
(.leaf (3311, 3309, 463030413383168496574073734))
(.leaf (3311, 3309, 772510664088931497509126527))))
(.branch 3479
(.leaf (3311, 3301, 157570701542261519711202986928223690051487731646265373594908295807))
(.branch 3480
(.leaf (3311, 3301, 367772672752650365884289557249592234705071850976162601975391781247))
(.leaf (3311, 3301, 157573990743570115504586647562494687987049922841503405691918812289)))))
(.branch 3484
(.branch 3482
(.leaf (3303, 3301, 474319092839006895381779211877422414822571508430408838965685584255))
(.branch 3483
(.leaf (3303, 3301, 157635079497659648432120160765789311538879369888375706401797767809))
(.leaf (3303, 3301, 263694509526508231417709433957031044981129569252854367737670861183))))
(.branch 3485
(.leaf (3303, 3301, 463020950203452069324456064))
(.branch 3486
(.leaf (3303, 3301, 154749570409408227641393535))
(.leaf (3303, 3301, 463035080409412539430928512))))))
(.branch 3493
(.branch 3490
(.branch 3488
(.leaf (3303, 3301, 774928515655821686843900287))
(.branch 3489
(.leaf (3303, 3300, 30348246350170698331806089806207))
(.leaf (3303, 3300, 70988896662157482553479712932736))))
(.branch 3491
(.leaf (3303, 3300, 30345158753627114057042795364735))
(.branch 3492
(.leaf (3302, 3299, 4641943741342045006860862167594303871))
(.leaf (3302, 3299, 1988761408991019211746087677911302783)))))
(.branch 3496
(.branch 3494
(.leaf (3302, 3299, 3317908037764926333384273455516549503))
(.branch 3495
(.leaf (3301, 3291, 106923306042991905624339097410226542565628161055306860786267920762078078))
(.leaf (3301, 3291, 10326133069859353658926186337223505511387107891781785389809073442128255))))
(.branch 3498
(.branch 3497
(.leaf (3301, 3291, 31084976068309710085411557331273476748647495267217397368300186361595007))
(.leaf (3293, 3291, 262871757247656066493875144922894118733597356274817173509775622527)))
(.branch 3499
(.leaf (3293, 3291, 157562685683345430919867568625130314708703208264466448013676446335))
(.leaf (3293, 3291, 52658550025639408977084488162956836712923827722088647029782806911)))))))))

def rowDataBlock35 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 3550
(.branch 3525
(.branch 3512
(.branch 3506
(.branch 3503
(.branch 3501
(.leaf (3293, 3290, 30345158753627617897251090858367))
(.branch 3502
(.leaf (3293, 3290, 71147352972926678059680727498880))
(.leaf (3293, 3290, 30348887080854805573417555788159))))
(.branch 3504
(.leaf (3292, 3290, 50627258877028294887468328489093))
(.branch 3505
(.leaf (3292, 3290, 30354472318141568993917814178175))
(.leaf (3292, 3285, 134668605457132129329538360375453113374442147149741359487)))))
(.branch 3509
(.branch 3507
(.leaf (3292, 3285, 1312437011726684844220239020857056964826229142126720))
(.branch 3508
(.leaf (3292, 3285, 559769377404246489915262763606323801950919524942207))
(.leaf (3287, 3278, 53499324410622796626958324176354831660025854481906594312267904284053353286631816233343))))
(.branch 3510
(.leaf (3287, 3278, 2906518306782834720168131166939615059803844703005352974221628707701240612499291570815))
(.branch 3511
(.leaf (3287, 3278, 4849128043730268262915372569588637096830495265019795466211658132022342702270827725183))
(.leaf (3280, 3277, 3621346558716005012769344814361387940411421668114609604200249753983))))))
(.branch 3518
(.branch 3515
(.branch 3513
(.leaf (3280, 3277, 157561072468200184831751574047318903702694124080281717592815502724))
(.branch 3514
(.leaf (3280, 3277, 52658550050063556505558743266405301766056262042795718674074435967))
(.leaf (3279, 3277, 50627258914622759309688394678913))))
(.branch 3516
(.leaf (3279, 3277, 30345777723646900580893461184895))
(.branch 3517
(.leaf (3279, 3277, 50785715273058341500155867366015))
(.leaf (3279, 3277, 154749570265293039532638591)))))
(.branch 3521
(.branch 3519
(.leaf (3279, 3277, 463030376489673743495267202))
(.branch 3520
(.leaf (3279, 3277, 774928515944052063029100927))
(.leaf (3279, 3277, 463068192315029263302460545))))
(.branch 3523
(.branch 3522
(.leaf (3279, 3277, 772510666325813137462329727))
(.leaf (3279, 3277, 463030413383161882324437894)))
(.branch 3524
(.leaf (3279, 3277, 1393898535442627012486889855))
(.leaf (3279, 3273, 8541490986591708419129512427815819063697801855)))))))
(.branch 3537
(.branch 3531
(.branch 3528
(.branch 3526
(.leaf (3279, 3273, 19981598029347877091392257432905719747589505407))
(.branch 3527
(.leaf (3279, 3273, 8543228468356881816229485383619410794777608833))
(.leaf (3275, 3273, 19936996554901551800709414186823930599119454591))))
(.branch 3529
(.leaf (3275, 3273, 8541402853458391625420378900375462555678606208))
(.branch 3530
(.leaf (3275, 3273, 14294908005067373077278930723570448273955422591))
(.leaf (3275, 3263, 676747314278883076513859753080232440207427453806350510707936344516268589184)))))
(.branch 3534
(.branch 3532
(.leaf (3275, 3263, 1132559294551113299062518467407402130842878126835361343629640407245597442431))
(.branch 3533
(.leaf (3275, 3263, 676775083023947034073864099445838947753889110794479025024596739986984731777))
(.leaf (3265, 3263, 1579571601834320866565932804050865205512532714575748110183093771087577678207))))
(.branch 3535
(.leaf (3265, 3262, 44349502737188768433882834062554254868364896089496690415991992992864112010527103))
(.branch 3536
(.leaf (3265, 3262, 14822064176565538308696964910749684323589869339901510886844921959559801367103360))
(.leaf (3265, 3262, 30345158753627114057042761941375))))))
(.branch 3543
(.branch 3540
(.branch 3538
(.leaf (3264, 3258, 1312437011726684843672217820844875770393418704814976))
(.branch 3539
(.leaf (3264, 3258, 559797900057362077491442623177012186506197966324095))
(.leaf (3264, 3258, 933908090011033555075267332886282753194299752383103))))
(.branch 3541
(.leaf (3260, 3258, 19981598029347877092628988546371485393968955775))
(.branch 3542
(.leaf (3260, 3257, 559792347171804953756490634440132941610703954968959))
(.leaf (3260, 3256, 86011872040371449595320899214943586677478754201980961151)))))
(.branch 3546
(.branch 3544
(.leaf (3260, 3255, 130352711317501700768516559578817365999999))
(.branch 3545
(.leaf (3259, 3255, 217442421729918943136747344997934073577600))
(.leaf (3258, 3255, 130334133279342480916355284365677594542463))))
(.branch 3548
(.branch 3547
(.leaf (3257, 3255, 218122985917007270784759047438860959024000))
(.leaf (3257, 3255, 664644343359487649655672389691834751)))
(.branch 3549
(.leaf (3257, 3255, 50627258877028294906215860732798))
(.leaf (3257, 3255, 4175636846231773555292373375))))))))
(.branch 3575
(.branch 3562
(.branch 3556
(.branch 3553
(.branch 3551
(.leaf (3257, 3253, 1988741047353238878711877519590505095))
(.branch 3552
(.leaf (3257, 3253, 4662712924125446689461620905993372031))
(.leaf (3257, 3243, 2906488779800065374085646653216819458231261002068273039330442714949242869202661868416))))
(.branch 3554
(.leaf (3255, 3243, 30217651909364050782640051930591224292476232746976676430412295863138597442611937608063))
(.branch 3555
(.leaf (3255, 3243, 2906577592332524226060171959626395182723229654437082008795588284796908683259923071615))
(.leaf (3245, 3243, 4849128030157349111393547817538016308234195440939435045689628322681007322739224084863)))))
(.branch 3559
(.branch 3557
(.leaf (3245, 3242, 44349499203492945652924691566503652810637549934592083068996652708473875961282943))
(.branch 3558
(.leaf (3245, 3232, 455399801702687322357222739322821507140825272626179357577352930947499647660208092836961850161661320397405621089311534487665847688))
(.leaf (3245, 3232, 44354490546450207402614108905784014514613015484463905541278270479859471322382719))))
(.branch 3560
(.leaf (3244, 3232, 73991821769797568075527870455503807729788274646211633501164671841804541172318849))
(.branch 3561
(.leaf (3234, 3232, 44349949749493937168094595895446645513614219835604910237680036744033094997311871))
(.leaf (3234, 3232, 74223405927701761183355265501776768633172452370615375044312433628892026378322559))))))
(.branch 3568
(.branch 3565
(.branch 3563
(.leaf (3234, 3232, 13353840441728921374597883206312062640182661859044710146643665878180981440895))
(.branch 3564
(.leaf (3234, 3219, 190479648672977990748621169553625715734481162607178337904353740502948346220983728725819775))
(.leaf (3234, 3215, 5880584072644661071944304750412725463757069828912376969921956142229035666499121576870705799382526615395172480))))
(.branch 3566
(.leaf (3234, 3215, 3514015737679423475354725647894046972609007243578189866460764147619649732469960065859253821628223517928522111))
(.branch 3567
(.leaf (3221, 3215, 5862236084287049038443295821722830721268387065818910463640183398745504067541802275068612440853839999263514269))
(.leaf (3217, 3215, 3513729610288626915673070729782606298427294291835070129725932113945302069292997665073703139193222229043249535)))))
(.branch 3571
(.branch 3569
(.leaf (3217, 3207, 14731549654389169895238419037325366664035037018608839579841759454962398755076422572555716312189253103747359579626601379529670342421648494199134159742))
(.branch 3570
(.leaf (3217, 3207, 10669546156023733568345265470337268637999261158088536020958744358065684561330012356991))
(.leaf (3217, 3207, 157562685683344684092530891853174378783876933875689888998156600192))))
(.branch 3573
(.branch 3572
(.leaf (3209, 3207, 1839676499276469170626185736501061538993746686650910059631900426623))
(.leaf (3209, 3205, 676719653373607394494464839452677891707645760073117643737850853792633783425)))
(.branch 3574
(.leaf (3209, 3205, 226166750425525805720710332744527756592091784246364797855419561658485244287))
(.leaf (3209, 3205, 1988984436268482698756964895195862930)))))))
(.branch 3587
(.branch 3581
(.branch 3578
(.branch 3576
(.leaf (3207, 3205, 15286152296685286165867000306420023679))
(.branch 3577
(.leaf (3207, 3204, 130335467699638850276432012824064684851583))
(.leaf (3207, 3201, 208132610555928403351678446949827634701307855617923285375))))
(.branch 3579
(.leaf (3207, 3201, 8541403534023084823250115570126307601787323007))
(.branch 3580
(.leaf (3206, 3201, 19981598029347877091392257432905719747555950975))
(.leaf (3203, 3201, 8543486742673456017389831205892480495647655298)))))
(.branch 3584
(.branch 3582
(.leaf (3203, 3201, 2854625716886743113646626568596863044372332927))
(.branch 3583
(.leaf (3203, 3201, 217442421183165393786646312899459852206721))
(.leaf (3203, 3201, 772510664017155378447909247))))
(.branch 3585
(.leaf (3203, 3201, 463035080409412530840994943))
(.branch 3586
(.leaf (3203, 3201, 1699756767733352075094393215))
(.leaf (3203, 3201, 463044635822842720978666370))))))
(.branch 3593
(.branch 3590
(.branch 3588
(.leaf (3203, 3201, 774928515655821686843900287))
(.branch 3589
(.leaf (3203, 3199, 1989024367262389887983112032756892289))
(.leaf (3203, 3199, 4641943737307859546807407561553215871))))
(.branch 3591
(.leaf (3203, 3199, 1988700324077706546842355533216691088))
(.branch 3592
(.leaf (3201, 3199, 9969240313856316609677403405880000895))
(.leaf (3201, 3199, 1988720844171873133148820425410544255)))))
(.branch 3596
(.branch 3594
(.leaf (3201, 3199, 3317908037764926334175781090177712511))
(.branch 3595
(.leaf (3201, 3198, 30345158753627330229824842105215))
(.leaf (3201, 3197, 7331553509718206322744682012303491455))))
(.branch 3598
(.branch 3597
(.leaf (3201, 3197, 1988700482534031575371030737484448383))
(.leaf (3200, 3197, 3317908038381478501387734334599856511)))
(.branch 3599
(.leaf (3199, 3188, 44350407362883714769635615265184040273165493927941388380408367982681891786523007))
(.leaf (3199, 3188, 310902436321901278254935375879041754992969782663376436042733282239504417298514559)))))))))

def rowDataBlock36 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 3650
(.branch 3625
(.branch 3612
(.branch 3606
(.branch 3603
(.branch 3601
(.leaf (3199, 3188, 1579571601940044534324684653780115624326171842707395524982697910567274807679))
(.branch 3602
(.leaf (3190, 3188, 17227563508643179865016043112916407102451058122490231661855979893359233))
(.leaf (3190, 3188, 10325923268028196933879368045555520432216514008345675941852547158835583))))
(.branch 3604
(.leaf (3190, 3188, 37851922684978396763513391926843345963089931684990923734370384961536894))
(.branch 3605
(.leaf (3190, 3188, 772510667630168179505889663))
(.leaf (3190, 3186, 1988720844171807167592010636735744131)))))
(.branch 3609
(.branch 3607
(.leaf (3190, 3186, 3328292632719936028142887505154212223))
(.branch 3608
(.leaf (3190, 3186, 1988863375636160902849119756721521281))
(.leaf (3188, 3186, 48615505831620344713189490836268646783))))
(.branch 3610
(.leaf (3188, 3186, 1988700482534093150602747667571213184))
(.branch 3611
(.leaf (3188, 3186, 664644343364323351134661380380492159))
(.leaf (3188, 3186, 463039821222639482785693824))))))
(.branch 3618
(.branch 3615
(.branch 3613
(.leaf (3188, 3186, 774928515655821687163322751))
(.branch 3614
(.leaf (3188, 3184, 1988720527259147684248440791707353729))
(.leaf (3188, 3184, 13910193631028049051380494525810999679))))
(.branch 3616
(.leaf (3188, 3184, 1988700324077706546842355541806612608))
(.branch 3617
(.leaf (3186, 3184, 9979624909425460620584076294137839999))
(.leaf (3186, 3184, 1989511303549315542909413433469239935)))))
(.branch 3621
(.branch 3619
(.leaf (3186, 3184, 3317908037764926333743998476324110719))
(.branch 3620
(.leaf (3186, 3184, 463030376489674830121993090))
(.leaf (3186, 3184, 1085622451152947671677731199))))
(.branch 3623
(.branch 3622
(.leaf (3186, 3184, 463030413383162986131037076))
(.leaf (3186, 3184, 772510664447249143431496063)))
(.branch 3624
(.leaf (3186, 3184, 463039858116127621614862977))
(.leaf (3186, 3184, 1083204599658115076615242111)))))))
(.branch 3637
(.branch 3631
(.branch 3628
(.branch 3626
(.leaf (3186, 3184, 463035154196394336122241152))
(.branch 3627
(.leaf (3186, 3184, 9760874132851360342552347007))
(.leaf (3186, 3183, 30346396693666543833980713501055))))
(.branch 3629
(.leaf (3186, 3183, 50785715287022526765057804535166))
(.branch 3630
(.leaf (3186, 3183, 30345158753627114057042728321407))
(.leaf (3185, 3183, 70988896647935042872641058702208)))))
(.branch 3634
(.branch 3632
(.leaf (3185, 3183, 30345161171479184224490421748095))
(.branch 3633
(.leaf (3185, 3183, 50627258891213841088972836505217))
(.leaf (3185, 3183, 4486330781872733253225480575))))
(.branch 3635
(.leaf (3185, 3183, 463030413383159687596147327))
(.branch 3636
(.leaf (3185, 3183, 13795059592978279917447676287))
(.leaf (3185, 3179, 8541402853459159663227787511837854717332882302))))))
(.branch 3643
(.branch 3640
(.branch 3638
(.leaf (3185, 3179, 48370446667087744944902057542851047663454912895))
(.branch 3639
(.leaf (3185, 3179, 8543405415187680704230476912129051449643434625))
(.leaf (3181, 3179, 14250306514659927238210871438041606880057360767))))
(.branch 3641
(.leaf (3181, 3179, 8541577078030254987457408565750298653306594961))
(.branch 3642
(.leaf (3181, 3179, 14294908023676565018889140814855740791799546239))
(.leaf (3181, 3174, 559775108695765175933697018018518382384470669787519)))))
(.branch 3646
(.branch 3644
(.leaf (3181, 3172, 4023658898177068772630126401077555061520513580312241813520512))
(.branch 3645
(.leaf (3181, 3172, 2404191169253520045708842074408350017295659852460284331360639))
(.leaf (3176, 3172, 5636874044544128646629188816621886787709791080333300624984452))))
(.branch 3648
(.branch 3647
(.leaf (3174, 3172, 2404191360815479736315780722293541026763626638522725980766591))
(.leaf (3174, 3172, 4011104699554096342565982361018568755479006542940656231186560)))
(.branch 3649
(.leaf (3174, 3172, 3328292631790272073002789907944571263))
(.leaf (3174, 3172, 463289719264617046967517825))))))))
(.branch 3675
(.branch 3662
(.branch 3656
(.branch 3653
(.branch 3651
(.leaf (3174, 3172, 154749570193516920219631999))
(.branch 3652
(.leaf (3174, 3172, 463157788150991950584939135))
(.leaf (3174, 3172, 1080786748956478965571912063))))
(.branch 3654
(.leaf (3174, 3169, 130331464438757196432806074529654901899647))
(.branch 3655
(.leaf (3174, 3165, 4023658898177068772804010690472346427547950103751978941088640))
(.leaf (3174, 3165, 2404926575551193064124769305179479235044722192429863732445567)))))
(.branch 3659
(.branch 3657
(.leaf (3171, 3165, 4011104694709218414551681482135333112459241637773902801207424))
(.branch 3658
(.leaf (3167, 3165, 2404191360815474049625756410635745763436875549961576983363967))
(.leaf (3167, 3165, 803505708674913382631106819867985230492160943619177556412539))))
(.branch 3660
(.leaf (3167, 3165, 2854625716886743119860505280981459638287335807))
(.branch 3661
(.leaf (3167, 3163, 1988862583354724341270411548756476798))
(.leaf (3167, 3163, 8634820020904589825504467804873425279))))))
(.branch 3668
(.branch 3665
(.branch 3663
(.leaf (3167, 3163, 1988700324077706546842355550396548476))
(.branch 3664
(.leaf (3165, 3163, 4662712924433722773319236157400220031))
(.leaf (3165, 3163, 1988720527259157147428153916127117951))))
(.branch 3666
(.leaf (3165, 3163, 3317908038381478501821487273710846335))
(.branch 3667
(.leaf (3165, 3163, 463030376489674838711927425))
(.leaf (3165, 3163, 9760874132851923292421816703)))))
(.branch 3671
(.branch 3669
(.leaf (3165, 3163, 463044525142403537424024703))
(.branch 3670
(.leaf (3165, 3163, 772510665310814371947938175))
(.leaf (3165, 3163, 463020950203452069324466821))))
(.branch 3673
(.branch 3672
(.leaf (3165, 3163, 774928515800499824956801407))
(.leaf (3165, 3163, 463020950203453173131051906)))
(.branch 3674
(.leaf (3165, 3163, 1085622451296781384777007487))
(.leaf (3165, 3163, 463030413383180552547271295)))))))
(.branch 3687
(.branch 3681
(.branch 3678
(.branch 3676
(.leaf (3165, 3163, 1083204599729328245572632959))
(.branch 3677
(.leaf (3165, 3163, 463030376489678158721647233))
(.leaf (3165, 3163, 2005615000024077136681697663))))
(.branch 3679
(.leaf (3165, 3163, 463035154196389929485796734))
(.branch 3680
(.leaf (3165, 3163, 772510665748789435171864959))
(.leaf (3165, 3163, 463035080409412530841004906)))))
(.branch 3684
(.branch 3682
(.leaf (3165, 3163, 774928515872838893954859391))
(.branch 3683
(.leaf (3165, 3163, 463044635822888831747555456))
(.leaf (3165, 3163, 154749570193516920253251967))))
(.branch 3685
(.leaf (3165, 3158, 559769422005740874660494852791404490646495948702079))
(.branch 3686
(.leaf (3165, 3158, 1306591005437677243304611682624456498469401358439533))
(.leaf (3165, 3158, 559769377404246489915261217390201310007014249726335))))))
(.branch 3693
(.branch 3690
(.branch 3688
(.leaf (3160, 3158, 1309514008452023037835810451094625075102095104738174))
(.branch 3689
(.leaf (3160, 3158, 560072243824791732376728415461290532030757629657471))
(.leaf (3160, 3154, 17227563486183709857671759933623636795916411570442919145792573716499334))))
(.branch 3691
(.leaf (3160, 3154, 42772959642137863208017141182059701138253349247))
(.branch 3692
(.leaf (3160, 3154, 8541402853458350981373004415744023111990707074))
(.leaf (3156, 3154, 77116107227993718174341598396582734545838670207)))))
(.branch 3696
(.branch 3694
(.leaf (3156, 3147, 44349953283188594520449942566436609137523977518249178436055252148791890482823551))
(.branch 3695
(.leaf (3156, 3146, 4849128042318557458263167158035237296205418273280154240194751418295047833705724838271))
(.leaf (3156, 3144, 676968601521123841366310213434127198883259935081021047375731329523024593790))))
(.branch 3698
(.branch 3697
(.leaf (3149, 3144, 1583105295963877635640309909444135635412514412564722478369516150765037551999))
(.leaf (3148, 3144, 676726635999789384527341461080359075499372133932839114204920009516744901247)))
(.branch 3699
(.leaf (3146, 3144, 1132559294867461550158480471692590831924278087831514217183462121226326966655))
(.leaf (3146, 3143, 14294908005056988483561861067519627846318293375)))))))))

def rowDataBlock37 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 3750
(.branch 3725
(.branch 3712
(.branch 3706
(.branch 3703
(.branch 3701
(.leaf (3146, 3143, 43558131726813745367475003301521807835264))
(.branch 3702
(.leaf (3146, 3143, 30345161171478753286301077733759))
(.leaf (3145, 3140, 14250306514659927236661028537151255615014764927))))
(.branch 3704
(.leaf (3145, 3140, 8541924166044514344690075094719138694533416065))
(.branch 3705
(.leaf (3145, 3140, 2854625716886743112409895454696500034623635839))
(.leaf (3142, 3129, 87641626327398682695920374237234196266909774168066549580903257675940550123532175001331542458751)))))
(.branch 3709
(.branch 3707
(.leaf (3142, 3129, 12483274255432344655667141178259578946725369034542072255032008911584309470862929293034271999621))
(.branch 3708
(.leaf (3142, 3129, 4172040159196877583385505204953847504457238293708528461743672318988243749089364493957651890559))
(.leaf (3131, 3129, 1292008808733735680544244225041958079101476742450881307583951185483848127264785025))))
(.branch 3710
(.leaf (3131, 3129, 44357623166296270513989936728489680692175345224760428049508858908725660843245951))
(.branch 3711
(.leaf (3131, 3129, 73991821776834114163663769255515552982291564927304101408273445185319732072350849))
(.leaf (3131, 3129, 14040471534287147620894769535))))))
(.branch 3718
(.branch 3715
(.branch 3713
(.leaf (3131, 3127, 1989086561369973048667832777757888645))
(.branch 3714
(.leaf (3131, 3127, 3328292631787854223748498127214084479))
(.leaf (3131, 3124, 559769377404246489915261525666284444794525530980735))))
(.branch 3716
(.leaf (3129, 3124, 3187543613464177895239459036307088574657686935635583))
(.branch 3717
(.leaf (3129, 3124, 559769422005759442314060355573909861969147132248447))
(.leaf (3126, 3124, 933908087744752991483070757918178504366913157530239)))))
(.branch 3721
(.branch 3719
(.leaf (3126, 3124, 130331464438757196432806653242207018877311))
(.branch 3720
(.leaf (3126, 3123, 14294908080890484102463018584943744983400776063))
(.leaf (3126, 3123, 70988896859537644142163325289344))))
(.branch 3723
(.branch 3722
(.leaf (3126, 3123, 30345161171478753286301161750911))
(.leaf (3125, 3123, 50627258881769108117680153362560)))
(.branch 3724
(.leaf (3125, 3123, 30345777723646900580893310648703))
(.leaf (3125, 3121, 304214424727801520367832270073625868959872)))))))
(.branch 3737
(.branch 3731
(.branch 3728
(.branch 3726
(.leaf (3125, 3121, 8614050848277373953340967675550957951))
(.branch 3727
(.leaf (3125, 3121, 1988700324077706546842354446589952898))
(.leaf (3123, 3121, 19320566955769265084659096855305453951))))
(.branch 3729
(.leaf (3123, 3118, 559792347171806298561376377199395051767458047263103))
(.branch 3730
(.leaf (3123, 3118, 933908087744752991604923671860376242359935615042175))
(.leaf (3123, 3118, 130331464438756576253862196929007175205247)))))
(.branch 3734
(.branch 3732
(.leaf (3120, 3118, 391666993168697257200450316386762487693953))
(.branch 3733
(.leaf (3120, 3118, 130332809243643865229245794445474578497919))
(.leaf (3120, 3118, 217442421162962212203579657851882537156736))))
(.branch 3735
(.leaf (3120, 3118, 772510664160707616570343807))
(.branch 3736
(.leaf (3120, 3111, 2404386753996934450455189166052106349910057078835618586296703))
(.leaf (3120, 3109, 17281483376316689250720232100888560104289768211112867912270753625475721))))))
(.branch 3743
(.branch 3740
(.branch 3738
(.leaf (3120, 3109, 10326237970774735670458502033820513327369435195102041250604978236555647))
(.branch 3739
(.leaf (3113, 3109, 24156269774839441455461111432593850141611596153072714307913547404739201))
(.leaf (3111, 3109, 10325923268028295013593868970416612740770136587931235262705230034239871))))
(.branch 3741
(.leaf (3111, 3109, 3451030817877877963069649644830153538168937176573846282284555244083815))
(.branch 3742
(.leaf (3111, 3109, 41974558149864994111939382779142209919))
(.leaf (3111, 3109, 463106081927352247495099007)))))
(.branch 3746
(.branch 3744
(.leaf (3111, 3109, 774928515727597806022427007))
(.branch 3745
(.leaf (3111, 3108, 30345158753627330229824842105215))
(.leaf (3111, 3104, 1682196926058855850276431268552105332447958563487872))))
(.branch 3748
(.branch 3747
(.leaf (3111, 3104, 559769422005736886976510279782096281830331772961151))
(.leaf (3110, 3104, 933908092629846650898809747705117651724681013559935)))
(.branch 3749
(.leaf (3106, 3104, 559775064094274768487857020295279593135374707458431))
(.leaf (3106, 3104, 2063648853314768943710199919511121510388589035198095))))))))
(.branch 3775
(.branch 3762
(.branch 3756
(.branch 3753
(.branch 3751
(.leaf (3106, 3104, 2854625718210778812878865846447154396940665215))
(.branch 3752
(.leaf (3106, 3104, 463030413383200446835786879))
(.leaf (3106, 3104, 772510664520151161829851519))))
(.branch 3754
(.leaf (3106, 3103, 30345469447562898850453760573823))
(.branch 3755
(.leaf (3106, 3103, 70830440318165700971623012565631))
(.leaf (3106, 3103, 30347627380150767129817528533375)))))
(.branch 3759
(.branch 3757
(.leaf (3105, 3103, 111712172175489205681735681901185))
(.branch 3758
(.leaf (3105, 3103, 30347013245834547294859813650815))
(.leaf (3105, 3103, 50785715211501556522888558743946))))
(.branch 3760
(.leaf (3105, 3103, 772510666388582057285648767))
(.branch 3761
(.leaf (3105, 3103, 463044525142378270131423873))
(.leaf (3105, 3103, 774928518245391472682533247))))))
(.branch 3768
(.branch 3765
(.branch 3763
(.leaf (3105, 3103, 463124565564915199682478208))
(.branch 3764
(.leaf (3105, 3103, 154749570193516920253251967))
(.leaf (3105, 3102, 30345161171479041235202286223743))))
(.branch 3766
(.leaf (3105, 3102, 70988896647861255894151492207488))
(.branch 3767
(.leaf (3105, 3102, 30345158753627114057042761941375))
(.leaf (3104, 3095, 893100002677445394853659149598784718154798691817456805501569401215)))))
(.branch 3771
(.branch 3769
(.leaf (3104, 3093, 676747314278884689729018053300974897302743571955812341702937761920548012928))
(.branch 3770
(.leaf (3104, 3093, 1129025600843628449233833140892047618090081836977874700226886270540589302143))
(.leaf (3097, 3093, 24102349881505140176989826155240989882360274100070024528030405733844097))))
(.branch 3773
(.branch 3772
(.leaf (3095, 3093, 10326133892611729441434109790414483147061220140655714416546814359568767))
(.leaf (3095, 3093, 252857497386030294865540948717878405359280663289202257294641017273647232)))
(.branch 3774
(.leaf (3095, 3093, 664644343672599434991713681800233343))
(.leaf (3095, 3093, 463030413383177284077159039)))))))
(.branch 3787
(.branch 3781
(.branch 3778
(.branch 3776
(.leaf (3095, 3093, 1391480684956882208747487615))
(.branch 3777
(.leaf (3095, 3093, 463030376489680349154968193))
(.leaf (3095, 3093, 1080786748018885818031473023))))
(.branch 3779
(.leaf (3095, 3093, 463020950203453181720986494))
(.branch 3780
(.leaf (3095, 3093, 772510663872758715478966655))
(.leaf (3095, 3093, 463020950203452069324456832)))))
(.branch 3784
(.branch 3782
(.leaf (3095, 3093, 774928517958849946675052927))
(.branch 3783
(.leaf (3095, 3093, 463049302849137418679812224))
(.leaf (3095, 3093, 2624585019666204324177969535))))
(.branch 3785
(.leaf (3095, 3093, 463030413383177241127486079))
(.branch 3786
(.leaf (3095, 3093, 2318726788387663278256423295))
(.leaf (3095, 3093, 463030376489707961499714177))))))
(.branch 3793
(.branch 3790
(.branch 3788
(.leaf (3095, 3093, 4794606865875026642728845695))
(.branch 3789
(.leaf (3095, 3093, 463105860566424449607205762))
(.leaf (3095, 3093, 772510664088931497509126527))))
(.branch 3791
(.leaf (3095, 3080, 190524170697941613591720655106856186961883871052599498486957127611373734162555561872261503))
(.branch 3792
(.leaf (3095, 3079, 20892031468491690518187365680150464689097200191233560784494377157968228444120570933398015443327))
(.leaf (3095, 3078, 818170415643425176596194234802423396897233280195508125497541684989875735559006873129414625534607743)))))
(.branch 3796
(.branch 3794
(.leaf (3082, 3078, 6296902265169098355186125691424915340114380624224486629847629611909770817130749609381991641595709820))
(.branch 3795
(.leaf (3081, 3078, 818103926789177038070709875689413182167367318625516341728305409262502290366511710752883873914749311))
(.leaf (3080, 3078, 273418823999943994914044873268747240394625931988528832810401707899280666455581165817097466907919232))))
(.branch 3798
(.branch 3797
(.leaf (3080, 3078, 664644343053629415420799663478604159))
(.leaf (3080, 3071, 262871757983253926126472664027031158067109442191985647556377969023)))
(.branch 3799
(.leaf (3080, 3071, 7237534985946760485575193145707379646333849963623315517932159))
(.leaf (3080, 3071, 2404191360815462653944948024396855029591551757787965218161023)))))))))

def rowDataBlock38 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 3850
(.branch 3825
(.branch 3812
(.branch 3806
(.branch 3803
(.branch 3801
(.leaf (3073, 3068, 18795729401352891529776755014118411310528427072495815638921596133424079044991))
(.branch 3802
(.leaf (3073, 3068, 676719653373604205726780639623411117874715282734797405469726300879307342465))
(.leaf (3073, 3068, 226166750214901222383595959354333789720040019826604794629109548471233216895))))
(.branch 3804
(.leaf (3070, 3068, 217442421162962212198801951136791763298443))
(.branch 3805
(.leaf (3070, 3068, 130332798859049837465655691591593245016447))
(.leaf (3070, 3068, 43558131686724295139961168217984504627328)))))
(.branch 3809
(.branch 3807
(.leaf (3070, 3068, 774928515872838893954859391))
(.branch 3808
(.leaf (3070, 3068, 463035117302912742823238538))
(.leaf (3070, 3068, 1080786748018322868078182783))))
(.branch 3810
(.leaf (3070, 3068, 463030413383165176564351615))
(.branch 3811
(.leaf (3070, 3068, 1085622451730815798881550719))
(.leaf (3070, 3068, 463030376489681418601824897))))))
(.branch 3818
(.branch 3815
(.branch 3813
(.leaf (3070, 3068, 3248390742587915928279646591))
(.branch 3814
(.leaf (3070, 3068, 463035117302954575804695938))
(.leaf (3070, 3068, 772510663872758715445543295))))
(.branch 3816
(.leaf (3070, 3068, 463035154196388825679202429))
(.branch 3817
(.leaf (3070, 3068, 774928516302932658352030079))
(.leaf (3070, 3068, 463049302849097758951800960)))))
(.branch 3821
(.branch 3819
(.leaf (3070, 3068, 13782970334709231606715974015))
(.branch 3820
(.leaf (3070, 3068, 463030413383162977541096063))
(.leaf (3070, 3068, 13122896837272546096260841855))))
(.branch 3823
(.branch 3822
(.leaf (3070, 3066, 1988700324077767716245702867463115911))
(.leaf (3070, 3066, 9969240313548040525675672966279463295)))
(.branch 3824
(.leaf (3070, 3023, 2553992990001834445881795834884301576604268784179275058647796369920739892080287222976339874478031496561124460181446541253099764098833432526123256051022805452094774707381664390980522949375946205015165508693782217537114343132176129838273802600831))
(.leaf (3068, 3021, 18300426978949397526455842271761894253287579376297781160583928725469439815053023874861171561777026442801671635788876616498988006343859362827725235742237892593206707996375999924676294236546368059139332753114102011645081826659078519017916261547846460702848)))))))
(.branch 3837
(.branch 3831
(.branch 3828
(.branch 3826
(.leaf (3068, 3021, 10969091750844335085122832953690794074956853960004349795882977742050285617653927185756700386520358511703513181488895873777728553936945625017364797619124387910085517856885675704826431753896300460395499784599525543166051861667233692696293213416298209804671))
(.branch 3827
(.leaf (3025, 3021, 18357704803856464395045226068851132003252842951650020935226580229307765451416683188134309003897341488522537171919380033523799646810965988967877975331472748769957377200595732886493201018348420936159971102739992893451063952769120427271459644145290815931778))
(.leaf (3023, 3021, 2554305553178399923456536616368721669503250425564896966574982923165351806698032194792664947688042870502283328421932947211590094342196869711739191057840784083623159790748601447867693796205658720096016910304571119779973311691290799211433669624191))))
(.branch 3829
(.leaf (3023, 3021, 4260900192256642010563906511734381226787215785586586748531752021108320048869220798378411189161470017253025353938292304081731445147129147341843784194352536678320426114671918556663307439877225092216103897708155500145436381279402947713548666471039))
(.branch 3830
(.leaf (3023, 3021, 3317908040235970709180978646847914367))
(.leaf (3023, 3020, 30345158753627402568893940498815)))))
(.branch 3834
(.branch 3832
(.leaf (3023, 3002, 520027908058137445107422189728661504403338649787676781107102855174842317193467658418268868319852086970919339863014572671))
(.branch 3833
(.leaf (3023, 3002, 15092740793637451755426792719698257406388695809274502469584238990529784559005871836661886483507819516424453850960691583))
(.leaf (3022, 2996, 1994815567979136278208046083266163810398076043167907747015591317543692004585396351799537389016998011068794061350942046168507679596919368274969297535))))
(.branch 3835
(.leaf (3004, 2996, 1195757878419603303712469678178218055027253254839510919822854675821289274092883134787599846548559292130113661460075099986412989554164899807339020671))
(.branch 3836
(.leaf (3004, 2985, 1571268336769180807156049425581031476811950536570703122479389542498826797698751925863597194127057187149543045389196990359403684369108994585204968741178776606137084025121421064269597451676251454951195007))
(.leaf (2998, 2958, 71347090013951335574471319054413551665573160517206824726186407575913144716895894322556381803644649788689613555965345104570423664370942708083015388720720627039780318826335149427924622905016789766709378256975403481769669505733167433943062032608355229126425773956098675771585827790855424576459731938003777873492632270812529688959))))))
(.branch 3843
(.branch 3840
(.branch 3838
(.leaf (2998, 2958, 38969646415128868765691033779632143326853788555589335146824909902329562542187672580819416763157224848630503689056358900310797635059933905016165465402487827630612301149307784988537632617578440094891262625019935274847936813466764374248981376))
(.branch 3839
(.leaf (2987, 2958, 13024060324921167452888467699358301960469849447226579826417846193581951484839649159936316666913514160785415680592299839634879881448102149650447297007703771374837830831179129300348350608075100320494891434067440334085835136505912168391180671))
(.leaf (2960, 2958, 491881079337831683733350957553730424632654141336262738830461425647830322059840653167231889006511612514243233965029241798388683568797566024522465850788018590040079274198787249488574098001340011080636517184373375))))
(.branch 3841
(.leaf (2960, 2958, 1478136515106614644812508965811236948427192356191137788235659787003517379626834029408632395279773847431063185845502167587379156519443955329016222568150907625781820244985504945928040057918763016281990566233637247))
(.branch 3842
(.leaf (2960, 2958, 80661450865323399730197006290803241147715330614781307534899082518301331958180081131137589236650912943547530937266709412688821429375168797039898690573444252289))
(.leaf (2960, 2958, 154749570194079870206542207)))))
(.branch 3846
(.branch 3844
(.leaf (2960, 2958, 463039821222651581708567424))
(.branch 3845
(.leaf (2960, 2958, 772510667401891973561778559))
(.leaf (2960, 2958, 463035154196388825679207015))))
(.branch 3848
(.branch 3847
(.leaf (2960, 2958, 774928515728160755925713279))
(.leaf (2960, 2934, 18244883248866831928321746344058245531752963288065916128475518161987177869259308976886741718390974272826457204532441612177928263668513646772863)))
(.branch 3849
(.leaf (2960, 2934, 678024095299127151282945012921027326315702634526045569446657461677314287958262330144237543782807531780314764290973069270095560166747121668260223))
(.leaf (2960, 2934, 18244327217242355205453448464966186382323719109627350839299548138442842921942079975307395833612691683971867699680891536530931159337745260675968))))))))
(.branch 3875
(.branch 3862
(.branch 3856
(.branch 3853
(.branch 3851
(.leaf (2936, 2934, 810970875757504005954703092426388097304702143458490979903178798305658235508681619479707757615264043051028139125894883575369362190037184889684351))
(.branch 3852
(.leaf (2936, 2934, 18244325763565079736865221985747667657668389401824506727567219652062615437100983760419742930296337230250487302294227589649004504192117989376128))
(.leaf (2936, 2934, 457668736507618264794251530989448844972526081475885406813444489559102004726391128114564767618589285231242317319162374965448863864008721727291775))))
(.branch 3854
(.leaf (2936, 2933, 30354462646735012076884399817087))
(.branch 3855
(.leaf (2936, 2933, 860022167122752767737607177044607))
(.leaf (2936, 2933, 30346403947221317125092726014335)))))
(.branch 3859
(.branch 3857
(.leaf (2935, 2932, 4662712924123028838325387430958530943))
(.branch 3858
(.leaf (2935, 2932, 1988761567447339536355024060473607038))
(.leaf (2935, 2932, 3328292631790272072643064887875862911))))
(.branch 3860
(.leaf (2934, 2932, 50627258986066999107148308218497))
(.branch 3861
(.leaf (2934, 2932, 30345780141498539810151676903807))
(.leaf (2934, 2932, 50785715230464809433960512684671))))))
(.branch 3868
(.branch 3865
(.branch 3863
(.leaf (2934, 2932, 154749571126606468065657215))
(.branch 3864
(.leaf (2934, 2932, 463030376489673743495277452))
(.leaf (2934, 2932, 774928515511987973778243967))))
(.branch 3866
(.leaf (2934, 2932, 463073006915230285292307330))
(.branch 3867
(.leaf (2934, 2932, 772510664160707616603963775))
(.leaf (2934, 2932, 463030413383161882324449367)))))
(.branch 3871
(.branch 3869
(.leaf (2934, 2932, 2944950364668979198363173247))
(.branch 3870
(.leaf (2934, 2932, 463068155421534497338753665))
(.leaf (2934, 2932, 1083204599657552126595760511))))
(.branch 3873
(.branch 3872
(.leaf (2934, 2932, 463035154196386630950912639))
(.leaf (2934, 2932, 3559084678300088795538129279)))
(.branch 3874
(.leaf (2934, 2931, 30345158753627258453705780887935))
(.leaf (2934, 2931, 50785715282134139583317160167039)))))))
(.branch 3887
(.branch 3881
(.branch 3878
(.branch 3876
(.leaf (2934, 2931, 30346093253285676165394776195455))
(.branch 3877
(.leaf (2933, 2931, 50627258881769108111108853400448))
(.leaf (2933, 2931, 30345161171478897120014645657983))))
(.branch 3879
(.leaf (2933, 2931, 10141667869944363262725886771839))
(.branch 3880
(.leaf (2933, 2931, 1391480683731621634992308607))
(.leaf (2933, 2926, 559769377404257087393148866794444883841396426801535)))))
(.branch 3884
(.branch 3882
(.leaf (2933, 2926, 2430485764372278144396717902992401180991859216811906))
(.branch 3883
(.leaf (2933, 2926, 559820691418948308879109891077945806380961288421759))
(.leaf (2928, 2926, 933908087657980987877666630532418558360510378476159))))
(.branch 3885
(.leaf (2928, 2926, 559786615880287607350646814095273877551338668228991))
(.branch 3886
(.leaf (2928, 2926, 8393412444681681486320147435705907228811075847652479))
(.leaf (2928, 2926, 154749570409408227390194047))))))
(.branch 3893
(.branch 3890
(.branch 3888
(.leaf (2928, 2926, 463058821369047451007124097))
(.branch 3889
(.leaf (2928, 2926, 772510664017155378515083647))
(.leaf (2928, 2926, 463020950203452069324456064))))
(.branch 3891
(.leaf (2928, 2926, 2624585019810319512270668159))
(.branch 3892
(.leaf (2928, 2920, 36687287861076538133017273392801968797834451727522147720))
(.leaf (2928, 2920, 61396162375317076707744886305002221169769646797094977919)))))
(.branch 3896
(.branch 3894
(.leaf (2928, 2918, 157643095356574987473115628315685648787485583649944298636821071995))
(.branch 3895
(.leaf (2922, 2918, 368595425055543554656749191701842902289246518142887059367865090431))
(.leaf (2922, 2916, 676719653373617011014321204058089873208353876306747025085502415862212002945))))
(.branch 3898
(.branch 3897
(.leaf (2920, 2916, 1586638990304881739499849408333635083808246949916009091523889665288957788543))
(.leaf (2920, 2916, 8541402853458411828601805907575585140744585857)))
(.branch 3899
(.leaf (2918, 2916, 31310376595549499412201035866548798000870719871))
(.leaf (2918, 2916, 1988700482534045779363966381442663804)))))))))

def rowDataBlock39 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 3950
(.branch 3925
(.branch 3912
(.branch 3906
(.branch 3903
(.branch 3901
(.leaf (2918, 2916, 7321168924996753691312415778168897919))
(.branch 3902
(.leaf (2918, 2916, 463035080409412539430928512))
(.leaf (2918, 2916, 774928515655821686843900287))))
(.branch 3904
(.leaf (2918, 2916, 463049265955607421099377279))
(.branch 3905
(.leaf (2918, 2916, 18744401898480571758678180223))
(.leaf (2918, 2909, 2404191169253520045708851353042837456972671321837499546796415)))))
(.branch 3909
(.branch 3907
(.leaf (2918, 2909, 5611765636857216088535085170341099169639793970553411673718912))
(.branch 3908
(.leaf (2918, 2909, 2404265016382395520728202882835428176950893596833820736225663))
(.leaf (2911, 2909, 4011104693960929576497894634056931392322384496150643388383873))))
(.branch 3910
(.leaf (2911, 2909, 2404240209110839149833105980277051359700169867951912823816575))
(.branch 3911
(.leaf (2911, 2909, 10451411093221653050861504234844205435589572147707139772579968))
(.leaf (2911, 2909, 12506344669196183198276649343))))))
(.branch 3918
(.branch 3915
(.branch 3913
(.leaf (2911, 2909, 463035117302900686850032255))
(.branch 3914
(.leaf (2911, 2909, 774928515727597806022427007))
(.leaf (2911, 2909, 463030376489689136658067091))))
(.branch 3916
(.leaf (2911, 2909, 9474358714899729920745734527))
(.branch 3917
(.leaf (2911, 2909, 463030413383159687596149385))
(.leaf (2911, 2909, 772510666103729381004870015)))))
(.branch 3921
(.branch 3919
(.leaf (2911, 2909, 463035117302900678260097665))
(.branch 3920
(.leaf (2911, 2909, 154749570194079870256808319))
(.leaf (2911, 2909, 463039821222643872242270336))))
(.branch 3923
(.branch 3922
(.leaf (2911, 2909, 1393898535298511824343794047))
(.leaf (2911, 2909, 463049192168628927237915263)))
(.branch 3924
(.leaf (2911, 2909, 774928515511987973795217791))
(.leaf (2911, 2909, 463030376489678141541778302)))))))
(.branch 3937
(.branch 3931
(.branch 3928
(.branch 3926
(.leaf (2911, 2909, 18688791310561563084574359935))
(.branch 3927
(.leaf (2911, 2909, 463030413383164089937638752))
(.leaf (2911, 2909, 772510664234172585542156671))))
(.branch 3929
(.leaf (2911, 2909, 463020950203452069324456577))
(.branch 3930
(.leaf (2911, 2909, 1085622451297344334747009407))
(.leaf (2911, 2909, 463035117302909448583317125)))))
(.branch 3934
(.branch 3932
(.leaf (2911, 2909, 4476659375315816219911782783))
(.branch 3933
(.leaf (2911, 2909, 463020950203452077914391167))
(.leaf (2911, 2909, 774928516161632220043280767))))
(.branch 3935
(.leaf (2911, 2909, 463030376489674830121992320))
(.branch 3936
(.leaf (2911, 2909, 2624585021467362700149326207))
(.leaf (2911, 2909, 463030413383165167974417535))))))
(.branch 3943
(.branch 3940
(.branch 3938
(.leaf (2911, 2909, 772510663872758715730428287))
(.branch 3939
(.leaf (2911, 2909, 463087266248397055162516097))
(.leaf (2911, 2909, 2010450703302535653397365119))))
(.branch 3941
(.leaf (2911, 2909, 463020950203511279743598720))
(.branch 3942
(.leaf (2911, 2909, 154749570193516920755650943))
(.leaf (2911, 2909, 463035117302900686850032255)))))
(.branch 3946
(.branch 3944
(.leaf (2911, 2909, 774928515871712993980973439))
(.branch 3945
(.leaf (2911, 2905, 8541402853458411987058192363762027983957595277))
(.leaf (2911, 2905, 42862162607043557313156017576062463880808366463))))
(.branch 3948
(.branch 3947
(.leaf (2911, 2905, 8541403534023084823249921879313530357255439742))
(.leaf (2907, 2905, 14250306515994347535815753702848280371994362239)))
(.branch 3949
(.leaf (2907, 2905, 8541490306026690148149159292094646675914556290))
(.leaf (2907, 2905, 19936996538961200439757128532648409412677927295))))))))
(.branch 3975
(.branch 3962
(.branch 3956
(.branch 3953
(.branch 3951
(.leaf (2907, 2905, 463035080409418024104166015))
(.branch 3952
(.leaf (2907, 2905, 1083204599658115076347396479))
(.leaf (2907, 2905, 463030376489678158721647743))))
(.branch 3954
(.leaf (2907, 2905, 154749570409408227390194047))
(.branch 3955
(.leaf (2907, 2905, 463035154196388834269134976))
(.leaf (2907, 2905, 772510668114586614558949759)))))
(.branch 3959
(.branch 3957
(.leaf (2907, 2902, 130342119031910907481248179878864078569855))
(.branch 3958
(.leaf (2907, 2902, 304894989502049760186497011171009820033152))
(.leaf (2907, 2902, 130331474823350293323517812307645153018239))))
(.branch 3960
(.leaf (2904, 2902, 3097932657148547849100757994313556713996929))
(.branch 3961
(.leaf (2904, 2902, 130346153446570299736251117258090754277759))
(.leaf (2904, 2902, 1003154406383409124335733919734166613590655))))))
(.branch 3968
(.branch 3965
(.branch 3963
(.leaf (2904, 2902, 16605812123798184055793582463))
(.branch 3964
(.leaf (2904, 2897, 559769377404249153563549956450712973303415106961791))
(.leaf (2904, 2897, 936831091192278239654546866360360631147959284597377))))
(.branch 3966
(.leaf (2904, 2897, 559780795385788137594316155057868435572199459193215))
(.branch 3967
(.leaf (2899, 2897, 933908088967727818136314051282097731772442126254719))
(.leaf (2899, 2897, 559769422005739540240202517616787674060803272933759)))))
(.branch 3971
(.branch 3969
(.leaf (2899, 2895, 13702949779748189290151259816076378723436612363384037813716603))
(.branch 3970
(.leaf (2899, 2895, 3328292632719936028070548436106084735))
(.leaf (2899, 2895, 1989471214098970338847186835212272255))))
(.branch 3973
(.branch 3972
(.leaf (2897, 2895, 3317908039617000689178282014218846591))
(.leaf (2897, 2895, 1988700482534041001657253498281984896)))
(.branch 3974
(.leaf (2897, 2895, 17934223694851160043554190152297283967))
(.leaf (2897, 2895, 463171789229742800917954688)))))))
(.branch 3987
(.branch 3981
(.branch 3978
(.branch 3976
(.leaf (2897, 2895, 772510664088931497643671935))
(.branch 3977
(.leaf (2897, 2895, 463039821222639474195760769))
(.leaf (2897, 2895, 154749571494494262609903999))))
(.branch 3979
(.leaf (2897, 2895, 463030413383168496574071680))
(.branch 3980
(.leaf (2897, 2895, 154749570193516920319967615))
(.leaf (2897, 2895, 463039858116130933034648191)))))
(.branch 3984
(.branch 3982
(.leaf (2897, 2895, 154749570194079870524719487))
(.branch 3983
(.leaf (2897, 2895, 463030376489681418601826947))
(.leaf (2897, 2895, 1080786748091224887046111615))))
(.branch 3985
(.leaf (2897, 2895, 463020950203452077914391424))
(.branch 3986
(.leaf (2897, 2895, 772510667040759578340950399))
(.leaf (2897, 2895, 463020950203452069324463482))))))
(.branch 3993
(.branch 3990
(.branch 3988
(.leaf (2897, 2895, 154749570265855989267890559))
(.branch 3989
(.leaf (2897, 2895, 463030413383162994720966777))
(.leaf (2897, 2895, 1391480683659282565994250623))))
(.branch 3991
(.leaf (2897, 2895, 463044525142382650998063743))
(.branch 3992
(.leaf (2897, 2895, 7906381925563082138573865343))
(.leaf (2897, 2895, 463030376489695750907692159)))))
(.branch 3996
(.branch 3994
(.leaf (2897, 2895, 2624585019738543393192477055))
(.branch 3995
(.leaf (2897, 2895, 463096600300898360785567872))
(.leaf (2897, 2895, 772510664377724824216338815))))
(.branch 3998
(.branch 3997
(.leaf (2897, 2895, 463020950203452069324456832))
(.leaf (2897, 2895, 154749570337632108329107839)))
(.branch 3999
(.leaf (2897, 2895, 463030413383198247812531074))
(.leaf (2897, 2895, 1085622451296781384743387519)))))))))

def rowDataBlock40 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 4050
(.branch 4025
(.branch 4012
(.branch 4006
(.branch 4003
(.branch 4001
(.leaf (2897, 2890, 559792257968820182334604430619296612266902093431167))
(.branch 4002
(.leaf (2897, 2890, 1685119929246065087997253736659007595882628505340037))
(.leaf (2897, 2890, 559769377404246489915261525666284300397862512034175))))
(.branch 4004
(.leaf (2892, 2890, 3560226530814778085388613190720016248304447732514944))
(.branch 4005
(.leaf (2892, 2890, 559775064094274778872451667028888687627772408889727))
(.leaf (2892, 2890, 933908087744752991462867576476967311305359828648575)))))
(.branch 4009
(.branch 4007
(.leaf (2892, 2890, 10073985920132112248754536831))
(.branch 4008
(.leaf (2892, 2890, 463030376489728727666600101))
(.leaf (2892, 2890, 1083204599730454145395523967))))
(.branch 4010
(.leaf (2892, 2890, 463300049441287303430342271))
(.branch 4011
(.leaf (2892, 2890, 772510663872758715479097727))
(.leaf (2892, 2890, 463039858116127621614863230))))))
(.branch 4018
(.branch 4015
(.branch 4013
(.leaf (2892, 2890, 154749571852811907962569087))
(.branch 4014
(.leaf (2892, 2880, 676719707293497540028059479207101427252218098314557314998681967822299399038))
(.leaf (2892, 2880, 1583105295963877635175963760567458001352902116253903570527198577102354841983))))
(.branch 4016
(.leaf (2892, 2880, 676774975184160365471303045671179125060055319458479146943607342737035035263))
(.branch 4017
(.leaf (2882, 2880, 2938276994649721168318381770682995106703381728635987271628860630745894486399))
(.leaf (2882, 2880, 676719653373604193172578671273735021762863977644423757509716940375008936832)))))
(.branch 4021
(.branch 4019
(.leaf (2882, 2880, 226166751055754051174732246889880953480969206860195509804016362258360631679))
(.branch 4020
(.leaf (2882, 2880, 463039821222639482785699461))
(.leaf (2882, 2880, 772510664088931498633199999))))
(.branch 4023
(.branch 4022
(.leaf (2882, 2880, 463049302849093360905290626))
(.leaf (2882, 2880, 1085622451657913779896779135)))
(.branch 4024
(.leaf (2882, 2878, 1988700482534045705576991190411051136))
(.leaf (2882, 2878, 72655840286636596633141292177505124735)))))))
(.branch 4037
(.branch 4031
(.branch 4028
(.branch 4026
(.leaf (2882, 2873, 2404313864677760620935563044762326422202589186244161004765567))
(.branch 4027
(.leaf (2880, 2869, 133508955610332866825719356603192531900890136416552537384651134185347127961388418))
(.leaf (2880, 2869, 44349499203492629304673497429003758310276595170731413508674283712799551239750015))))
(.branch 4029
(.leaf (2875, 2869, 1676091168436680088758893378579572028116381853409900694015321647833811320467030657))
(.branch 4030
(.leaf (2871, 2869, 10325923268028221549588878711869451926383340619252296046947171699851647))
(.leaf (2871, 2869, 37905842612190216112714394218081829560608147351600553856127327337907329)))))
(.branch 4034
(.branch 4032
(.leaf (2871, 2869, 14294908007694675288935493542242333969677222271))
(.branch 4033
(.leaf (2871, 2869, 463044635822842720978666111))
(.leaf (2871, 2869, 774928515799936875505254783))))
(.branch 4035
(.leaf (2871, 2868, 30345158753627114057042896028031))
(.branch 4036
(.leaf (2871, 2867, 4652328330719070969701404423107903871))
(.leaf (2871, 2867, 1988700482534031575371030720304579199))))))
(.branch 4043
(.branch 4040
(.branch 4038
(.leaf (2870, 2867, 3317908039934948179592532824147296639))
(.branch 4039
(.leaf (2869, 2862, 2405515436962782177599366095761324200213719431969668614586751))
(.leaf (2869, 2861, 789021839426879112715924603380040840651215112605486512406867804543))))
(.branch 4041
(.leaf (2869, 2861, 12064626220837646916859054213738388060228626615620372384389249))
(.branch 4042
(.leaf (2864, 2861, 61204600438395530555465356854036307124626794180033577343))
(.leaf (2863, 2861, 36685048840568146509182804779012677931569366471347733121)))))
(.branch 4046
(.branch 4044
(.leaf (2863, 2861, 134668605440161262228118874994170628966756180648678719871))
(.branch 4045
(.leaf (2863, 2861, 50785715206760743298139932265081))
(.leaf (2863, 2861, 12236754212287374970641711487))))
(.branch 4048
(.branch 4047
(.leaf (2863, 2859, 1988761092078364450768996304481616000))
(.leaf (2863, 2859, 3328292631479578137218277971939230079)))
(.branch 4049
(.leaf (2863, 2859, 1988741047353238878711877519590490753))
(.leaf (2861, 2859, 62022016320670381437335421315233808767))))))))
(.branch 4075
(.branch 4062
(.branch 4056
(.branch 4053
(.branch 4051
(.leaf (2861, 2859, 1988700324077782086259378163134956416))
(.branch 4052
(.leaf (2861, 2859, 664644346138808107005557198250836351))
(.leaf (2861, 2857, 1988740888896923313362912145502579098))))
(.branch 4054
(.leaf (2861, 2857, 3328292631790272076541211840174227839))
(.branch 4055
(.leaf (2861, 2857, 1988700324077706546842352243271729793))
(.leaf (2859, 2857, 16651726372341691594161721412750868863)))))
(.branch 4059
(.branch 4057
(.leaf (2859, 2857, 1988700482534055150309956929701479039))
(.branch 4058
(.leaf (2859, 2857, 3317908048634378378114457742886633855))
(.leaf (2859, 2857, 463030376489673743495267202))))
(.branch 4060
(.leaf (2859, 2857, 774928516304621508195451263))
(.branch 4061
(.leaf (2859, 2857, 463039821222643855062404470))
(.leaf (2859, 2857, 772510663872758715428962687))))))
(.branch 4068
(.branch 4065
(.branch 4063
(.leaf (2859, 2857, 463030413383161882324446626))
(.branch 4064
(.leaf (2859, 2857, 2636674281326744630036660607))
(.leaf (2859, 2856, 30345471865414609855831171203455))))
(.branch 4066
(.leaf (2859, 2856, 70988896643157336155355556545408))
(.branch 4067
(.leaf (2859, 2856, 30345780141498395976438560784767))
(.leaf (2858, 2856, 354308805808425940566551377674881)))))
(.branch 4071
(.branch 4069
(.leaf (2858, 2856, 30345158753627258453705780887935))
(.branch 4070
(.leaf (2858, 2856, 50785715206723849809992513159296))
(.leaf (2858, 2856, 154749571561766782429167999))))
(.branch 4073
(.branch 4072
(.leaf (2858, 2856, 463049192168628927237915520))
(.leaf (2858, 2856, 774928515655821686961209727)))
(.branch 4074
(.leaf (2858, 2856, 463044525142376075403133567))
(.leaf (2858, 2856, 1080786748090661937092821375)))))))
(.branch 4087
(.branch 4081
(.branch 4078
(.branch 4076
(.leaf (2858, 2855, 30345158753629348968357861130623))
(.branch 4077
(.leaf (2858, 2855, 314219355576208185738707695764609))
(.leaf (2858, 2855, 30351331528862066353608811676031))))
(.branch 4079
(.leaf (2857, 2855, 50627258877028294899558661424514))
(.branch 4080
(.leaf (2857, 2855, 30345780141498539810151626441087))
(.leaf (2857, 2854, 664644343361905499422530102961832319)))))
(.branch 4084
(.branch 4082
(.leaf (2857, 2854, 91192078084331635737553264380804))
(.branch 4083
(.leaf (2857, 2854, 30345158753627114057042728321407))
(.leaf (2856, 2854, 273020711082828702430157810369153))))
(.branch 4085
(.leaf (2856, 2854, 30346396693666543833980747055487))
(.branch 4086
(.leaf (2856, 2854, 50627258881695321132610696972423))
(.leaf (2856, 2854, 1083204599657552126612603263))))))
(.branch 4093
(.branch 4090
(.branch 4088
(.leaf (2856, 2854, 463049302849093369495224959))
(.branch 4089
(.leaf (2856, 2854, 774928518471978828917637503))
(.leaf (2856, 2833, 64816865700709899240662535405541774244132356629863149640053349289865250402627273556630190467757260837231433422397702640362455423))))
(.branch 4091
(.leaf (2856, 2833, 151292902318645648821756564206089439081589005549936438868867050462520800375306624757485923400050344694504462468306058739527385982))
(.branch 4092
(.leaf (2856, 2833, 64816870865209193672219564463708835286764127955949414040028462654707882083466799645870894848976033926257164323410075918880801151))
(.leaf (2835, 2822, 10357674647438862319334437271572454017311563866403710450028607562994691993307058851665810413574604592799269089548172370163634929623692385016633863969517348557125094459034808491180415)))))
(.branch 4096
(.branch 4094
(.leaf (2835, 2819, 1747566453094251799300329720492710483293352597558095620979098213607498985285040034217619862989032124597270377687032553263687292930554625686326678427135480884787065976694298027076295693596956426623))
(.branch 4095
(.leaf (2835, 2813, 46270757248240649208554538008275674711305551190749616958428866493440978684127861394292969883047633158020218440062050162274742383791608212738699321175746721203394611362359443934516808756380769683712085567352871536882442240639))
(.leaf (2824, 2813, 2313710983194025745271834105150844163976108486376328517653024099560042669942293961355103847734454558520407834330665268019583))))
(.branch 4098
(.branch 4097
(.leaf (2821, 2812, 64816865700710052553522267209543241564823890947928549122883260799302250797652978441303046023649342253144933518577315341693682047))
(.leaf (2815, 2812, 21662471012279089624100452104810404072576965162382170986656963856650998795710919940974380597496695269574973722569544064984614782)))
(.branch 4099
(.leaf (2815, 2812, 3832301610057811884541743782135455327197211322788011326552987537097418080639))
(.leaf (2814, 2812, 803505707178335706180528497692458085883678431047819588469377)))))))))

def rowDataBlock41 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 4150
(.branch 4125
(.branch 4112
(.branch 4106
(.branch 4103
(.branch 4101
(.leaf (2814, 2812, 30345777723646900580893596451199))
(.branch 4102
(.leaf (2814, 2812, 50785715362617283978015740461695))
(.leaf (2814, 2812, 1085622451657913780115079551))))
(.branch 4104
(.leaf (2814, 2812, 463030376489673743495267455))
(.branch 4105
(.leaf (2814, 2812, 774928515727597805938606463))
(.leaf (2814, 2812, 463063525288786298482395779)))))
(.branch 4109
(.branch 4107
(.leaf (2814, 2812, 772510664808944487968604543))
(.branch 4108
(.leaf (2814, 2812, 463030413383161882324436607))
(.leaf (2814, 2812, 1699756767805128193569980799))))
(.branch 4110
(.leaf (2814, 2810, 1988720527259180740813820887813783680))
(.branch 4111
(.leaf (2814, 2810, 4652328330405959182277381753759859071))
(.leaf (2814, 2810, 1988761408991005044646639060385727362))))))
(.branch 4118
(.branch 4115
(.branch 4113
(.leaf (2812, 2810, 17892685319982881422598848200631714175))
(.branch 4114
(.leaf (2812, 2810, 1988700324077716010022062056271710845))
(.leaf (2812, 2810, 3328292643526523929605718628804591999))))
(.branch 4116
(.leaf (2812, 2809, 30356885334077591569869572079999))
(.branch 4117
(.leaf (2812, 2809, 1307502829003317746469241943425922))
(.leaf (2812, 2809, 30345158753627114057042795495807)))))
(.branch 4121
(.branch 4119
(.leaf (2811, 2808, 12606927118608561212974356420207116671))
(.branch 4120
(.leaf (2811, 2807, 130332798859049839883506823321468568273279))
(.leaf (2811, 2807, 217442421183006937300780622594072461128572))))
(.branch 4123
(.branch 4122
(.leaf (2810, 2807, 8665973802053380939131455416230281599))
(.leaf (2809, 2804, 559775153297255572994943301089955000020262696518015)))
(.branch 4124
(.leaf (2809, 2802, 4023658903790696562574998525516932045600981369829265191668092))
(.leaf (2809, 2802, 61204600444126822068824078706499150977386627821773717887)))))))
(.branch 4137
(.branch 4131
(.branch 4128
(.branch 4126
(.leaf (2806, 2802, 1685119929245384523100677213927781897256118958097280))
(.branch 4127
(.leaf (2804, 2802, 559900974101666996421813054923842552734806605627775))
(.leaf (2804, 2802, 1312437012945576282591808597640768735290884085448832))))
(.branch 4129
(.leaf (2804, 2802, 3328292642919643168231513852317598079))
(.branch 4130
(.leaf (2804, 2801, 30362458482107171309569295057279))
(.leaf (2804, 2801, 152118535057764017876467688866690)))))
(.branch 4134
(.branch 4132
(.leaf (2804, 2801, 30345471865414394245999010709887))
(.branch 4133
(.leaf (2803, 2801, 111712172180193125428258263728769))
(.leaf (2803, 2801, 30345158753627258453705780887935))))
(.branch 4135
(.leaf (2803, 2801, 50785715206760743298139932262528))
(.branch 4136
(.leaf (2803, 2801, 1393898535442627012503339391))
(.leaf (2803, 2801, 463035154196388834269136511))))))
(.branch 4143
(.branch 4140
(.branch 4138
(.leaf (2803, 2801, 774928515655821686894231935))
(.branch 4139
(.leaf (2803, 2801, 463044525142376075403133567))
(.leaf (2803, 2801, 1697338916238800954222248319))))
(.branch 4141
(.leaf (2803, 2797, 8541402853458432190239628871035352931784131964))
(.branch 4142
(.leaf (2803, 2797, 385401608853815472775574818497918072659980124543))
(.leaf (2803, 2797, 8541928249432876910360591866137899956837483908)))))
(.branch 4146
(.branch 4144
(.leaf (2799, 2797, 14250306513335891538663102521770952446548377983))
(.branch 4145
(.leaf (2799, 2797, 8542707155770799424094537431596502165267350145))
(.leaf (2799, 2797, 37130871125591499651770383944521861602104967551))))
(.branch 4148
(.branch 4147
(.leaf (2799, 2797, 463044598929355668776223359))
(.leaf (2799, 2797, 11013321283126726521897615743)))
(.branch 4149
(.leaf (2799, 2795, 1988700324077716010022073047093018752))
(.leaf (2799, 2795, 3328292633965129622273616486103777663))))))))
(.branch 4175
(.branch 4162
(.branch 4156
(.branch 4153
(.branch 4151
(.leaf (2799, 2795, 1989066992013822562196738471798702719))
(.branch 4152
(.leaf (2797, 2795, 3317908038381478501532130997686239615))
(.leaf (2797, 2795, 1988700482534041001657265571435053184))))
(.branch 4154
(.leaf (2797, 2795, 5986748624294603477373638280443003263))
(.branch 4155
(.leaf (2797, 2795, 463035080409412539430929535))
(.leaf (2797, 2795, 772510665167825083291402623)))))
(.branch 4159
(.branch 4157
(.leaf (2797, 2795, 463224786725466559869815686))
(.branch 4158
(.leaf (2797, 2795, 4780099758053886025973956991))
(.leaf (2797, 2795, 463030413383165176564355978))))
(.branch 4160
(.leaf (2797, 2795, 1080786748018322868145291647))
(.branch 4161
(.leaf (2797, 2793, 1988922875986237431118807847118245256))
(.leaf (2797, 2793, 4662712924125446689389844786948735359))))))
(.branch 4168
(.branch 4165
(.branch 4163
(.leaf (2797, 2790, 559769377404246489915277941669989135396327022199167))
(.branch 4164
(.leaf (2795, 2787, 5518613313872367529074269920212191255518802233205059598816421151103))
(.leaf (2795, 2786, 10326028168943726352326372145370359418912983877051947951987163593245055))))
(.branch 4166
(.leaf (2792, 2785, 1129025606412427247421492913079687794741861652594996400204739993058393719167))
(.branch 4167
(.leaf (2789, 2784, 10325922445276211554610365730126829313257351767108467149322058710843775))
(.leaf (2788, 2784, 176156449084247302821261592851638442789104057102328801967749466639237759)))))
(.branch 4171
(.branch 4169
(.leaf (2787, 2784, 257364029675005197431742823122733094834591010193026580863))
(.branch 4170
(.leaf (2786, 2784, 218122986018023177767849217193619411107968))
(.leaf (2786, 2784, 5976364030883392054334400330955948415))))
(.branch 4173
(.branch 4172
(.leaf (2786, 2784, 10141667832239218377150189998462))
(.leaf (2786, 2784, 772510664088368547555705215)))
(.branch 4174
(.leaf (2786, 2768, 53622901507669012865288684789387101215774812806809200430404572148089302608630747552375796693696019103872))
(.leaf (2786, 2768, 197378323508345785212993571313072807473853850723290423945057446333756772415951096373782233390465698300287)))))))
(.branch 4187
(.branch 4181
(.branch 4178
(.branch 4176
(.leaf (2786, 2765, 15096885050667355123731875211875606493270425023475170435400420391395041023887853765086846986871329922297179624263778687))
(.branch 4177
(.leaf (2770, 2765, 115763324480772371818222792240370796931117792753186321491789402326391819766375767825943872554029827450209841739531747456))
(.leaf (2770, 2765, 15091505873582479099159366972115277127575921854408045770861836817411203213526122315073337552100986150469332104957198719))))
(.branch 4179
(.leaf (2767, 2765, 25256916252369686243408438789793348272592561458381138548807074356927212839203132243001858581425188821961162271685021321))
(.branch 4180
(.leaf (2767, 2765, 130331474823352144188945627507028333166975))
(.leaf (2767, 2765, 304214424991552073406134002091079594082943)))))
(.branch 4184
(.branch 4182
(.leaf (2767, 2765, 1085622451297344335084126591))
(.branch 4183
(.leaf (2767, 2765, 463030376489746337032505214))
(.leaf (2767, 2765, 2323562490438327946576855423))))
(.branch 4185
(.leaf (2767, 2765, 463195345721924928015369604))
(.branch 4186
(.leaf (2767, 2765, 772510664667081099723145599))
(.leaf (2767, 2765, 463035080409412530840995712))))))
(.branch 4193
(.branch 4190
(.branch 4188
(.leaf (2767, 2765, 154749570338195058282529151))
(.branch 4189
(.leaf (2767, 2765, 463030413383168462214332544))
(.leaf (2767, 2765, 11627455598336347788265259391))))
(.branch 4191
(.leaf (2767, 2765, 463039821222637279467471487))
(.branch 4192
(.leaf (2767, 2765, 1080786748018885818048315775))
(.leaf (2767, 2765, 463030376489678132951843710)))))
(.branch 4196
(.branch 4194
(.leaf (2767, 2765, 4792189015245729600817267071))
(.branch 4195
(.leaf (2767, 2765, 463035117302900686850031744))
(.leaf (2767, 2765, 772510667257213836001608063))))
(.branch 4198
(.branch 4197
(.leaf (2767, 2765, 463101009072731968778476685))
(.leaf (2767, 2765, 6027711201737551737876709759)))
(.branch 4199
(.leaf (2767, 2765, 463030413383164081347695741))
(.leaf (2767, 2765, 1704592470939471522679751039)))))))))

def rowDataBlock42 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 4250
(.branch 4225
(.branch 4212
(.branch 4206
(.branch 4203
(.branch 4201
(.leaf (2767, 2765, 463035117302902885873287807))
(.branch 4202
(.leaf (2767, 2765, 2624585019666767274148233599))
(.leaf (2767, 2765, 463030376489674830121997686))))
(.branch 4204
(.leaf (2767, 2765, 1391480683515448852878393727))
(.branch 4205
(.leaf (2767, 2765, 463020950203452077914392191))
(.leaf (2767, 2765, 772510665384842290402296191)))))
(.branch 4209
(.branch 4207
(.leaf (2767, 2765, 463035117302900678260097922))
(.branch 4208
(.leaf (2767, 2765, 1085622451368557503838224767))
(.leaf (2767, 2764, 30345161171479761811142799196543))))
(.branch 4210
(.leaf (2767, 2756, 154885051163852893820174150506810082664323435530533153751956084538411133))
(.branch 4211
(.leaf (2767, 2756, 10331091386466554567679815368664436719565218453564934639959108437016959))
(.leaf (2766, 2754, 162804354187373864258247464646572017615279505773594371499455876334767003899202183))))))
(.branch 4218
(.branch 4215
(.branch 4213
(.leaf (2758, 2754, 44349499203493574235665978862012705768837935463287314379476273856982288793796991))
(.branch 4214
(.leaf (2758, 2754, 490148590488873734111052493402278744515454988591649807484987466442334219320361601))
(.leaf (2756, 2754, 21488404327757978244711693507529503745939216163287767758934006213498802471295))))
(.branch 4216
(.leaf (2756, 2754, 1988700324077720750835295600991208320))
(.branch 4217
(.leaf (2756, 2754, 8665973811029655149913910751807275391))
(.leaf (2756, 2751, 130334122894748766264551810367657374581119)))))
(.branch 4221
(.branch 4219
(.leaf (2756, 2751, 218122985917007270642460863652070749569663))
(.branch 4220
(.leaf (2756, 2751, 130331464438756576253862849106528163660159))
(.leaf (2753, 2751, 2664753204078713279188854142813207351197824))))
(.branch 4223
(.branch 4222
(.leaf (2753, 2751, 130331474823352149024648978304614029787519))
(.leaf (2753, 2751, 217442421710191130798162526551487551570561)))
(.branch 4224
(.leaf (2753, 2751, 772510664017155378683511167))
(.leaf (2753, 2751, 463087229354908907743413120)))))))
(.branch 4237
(.branch 4231
(.branch 4228
(.branch 4226
(.leaf (2753, 2751, 1080786751255566575260991871))
(.branch 4227
(.leaf (2753, 2751, 463101267327149009302127486))
(.leaf (2753, 2751, 774928515655821686927655295))))
(.branch 4229
(.leaf (2753, 2751, 463020950203468523344167551))
(.branch 4230
(.leaf (2753, 2751, 3250808594661179600717021567))
(.leaf (2753, 2751, 463030376489681452961563520)))))
(.branch 4234
(.branch 4232
(.leaf (2753, 2751, 13761209670459727014906495359))
(.branch 4233
(.leaf (2753, 2751, 463058784475545052886532737))
(.leaf (2753, 2751, 772510664017155378447909247))))
(.branch 4235
(.leaf (2753, 2751, 463044525142378270131421312))
(.branch 4236
(.leaf (2753, 2751, 154749570266418939187691903))
(.leaf (2753, 2749, 1988821860079012891515933851226408063))))))
(.branch 4243
(.branch 4240
(.branch 4238
(.leaf (2753, 2749, 3328292631479578137002105189842551167))
(.branch 4239
(.leaf (2753, 2744, 2404386753996923054774388713642803714984863836706293046968703))
(.leaf (2751, 2744, 68150530226514716538631735758492921550194451119484069671273599))))
(.branch 4241
(.leaf (2751, 2744, 2404191169253537217282640944919602416957404625404544646316415))
(.branch 4242
(.leaf (2746, 2744, 7237534986319443403093892825907283657912429254540162987133053))
(.leaf (2746, 2744, 559820646817460575466152033955232141959732180025727)))))
(.branch 4246
(.branch 4244
(.leaf (2746, 2744, 936831091456677638874127422762277693654643993674369))
(.branch 4245
(.leaf (2746, 2744, 4799442569153485159745847679))
(.leaf (2746, 2744, 463035117302898483531808896))))
(.branch 4248
(.branch 4247
(.leaf (2746, 2744, 1707010322578700780625985919))
(.leaf (2746, 2744, 463068118528048553237873279)))
(.branch 4249
(.leaf (2746, 2744, 774928515945740912906207615))
(.leaf (2746, 2744, 463030376489674847301863296))))))))
(.branch 4275
(.branch 4262
(.branch 4256
(.branch 4253
(.branch 4251
(.leaf (2746, 2744, 12489419707577744676681089407))
(.branch 4252
(.leaf (2746, 2744, 463030413383178430833428354))
(.leaf (2746, 2744, 772510663872758715462386047))))
(.branch 4254
(.leaf (2746, 2744, 463073006915228077679116929))
(.branch 4255
(.leaf (2746, 2744, 154749570194079870223384959))
(.leaf (2746, 2744, 463044635822846023808516224)))))
(.branch 4259
(.branch 4257
(.leaf (2746, 2744, 2636674277862350615891411327))
(.branch 4258
(.leaf (2746, 2744, 463035117302900686850032255))
(.leaf (2746, 2744, 774928515727597805905117567))))
(.branch 4260
(.leaf (2746, 2741, 130331464438758439208548639494346373136767))
(.branch 4261
(.leaf (2746, 2741, 305575554419146377008880279753792117741958))
(.leaf (2746, 2741, 130331474823350293323515942187899870445951))))))
(.branch 4268
(.branch 4265
(.branch 4263
(.leaf (2743, 2741, 217442421345107757852318249346606355645057))
(.branch 4264
(.leaf (2743, 2741, 130332798859049837465654896424784037413247))
(.leaf (2743, 2741, 392347557760324582452051511483076578315130))))
(.branch 4266
(.leaf (2743, 2741, 1391480684597438663320666495))
(.branch 4267
(.leaf (2743, 2741, 463035117302900686850032769))
(.leaf (2743, 2741, 774928515655821687011475839)))))
(.branch 4271
(.branch 4269
(.leaf (2743, 2741, 463020950203458657804288639))
(.branch 4270
(.leaf (2743, 2741, 1393898535370287943388299647))
(.leaf (2743, 2741, 463030376489683660574764414))))
(.branch 4273
(.branch 4272
(.leaf (2743, 2741, 1699756770041446883569631615))
(.leaf (2743, 2741, 463035117302934776005460609)))
(.branch 4274
(.leaf (2743, 2741, 772510664017155378447909247))
(.leaf (2743, 2741, 463035080409412530840994690)))))))
(.branch 4287
(.branch 4281
(.branch 4278
(.branch 4276
(.leaf (2743, 2741, 1085622451871553287236878719))
(.branch 4277
(.leaf (2743, 2739, 1989629987336658387759384700984951935))
(.leaf (2743, 2739, 3328292631479578141320775757832323455))))
(.branch 4279
(.leaf (2743, 2739, 1988720685715472712777115978795254401))
(.branch 4280
(.leaf (2741, 2739, 4641943737620971334087596517852578175))
(.leaf (2741, 2739, 1988700324077748974353725065185394816)))))
(.branch 4284
(.branch 4282
(.leaf (2741, 2739, 8634820022147365567707174201652412799))
(.branch 4283
(.leaf (2741, 2739, 463058821369035403623858815))
(.leaf (2741, 2739, 774928515511987973828379007))))
(.branch 4285
(.leaf (2741, 2739, 463030376489683651984819072))
(.branch 4286
(.leaf (2741, 2739, 1085622451368557503838093695))
(.leaf (2741, 2739, 463030413383165193744221823))))))
(.branch 4293
(.branch 4290
(.branch 4288
(.leaf (2741, 2739, 772510664088931497995010431))
(.branch 4289
(.leaf (2741, 2739, 463223790601286579554026113))
(.leaf (2741, 2739, 154749570194079870240096639))))
(.branch 4291
(.leaf (2741, 2739, 463035080409426888916665216))
(.branch 4292
(.leaf (2741, 2739, 2012868554941201961994813823))
(.leaf (2741, 2739, 463049376636069664333431423)))))
(.branch 4296
(.branch 4294
(.leaf (2741, 2739, 774928515728160756094009727))
(.branch 4295
(.leaf (2741, 2738, 30345158753628555490398463590783))
(.leaf (2741, 2738, 70830440322906514197453970805895))))
(.branch 4298
(.branch 4297
(.leaf (2741, 2738, 30345161171478753286301128065407))
(.leaf (2740, 2735, 14250306519987223813517761684311493749969584511)))
(.branch 4299
(.leaf (2740, 2734, 559838152902441411620724424842271757362021005001087))
(.leaf (2740, 2731, 6383325958179649354492318146383626343296636946795443233330074550655)))))))))

def rowDataBlock43 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 4350
(.branch 4325
(.branch 4312
(.branch 4306
(.branch 4303
(.branch 4301
(.leaf (2737, 2731, 8863304335790439730351051050780244943721335072317485831096445))
(.branch 4302
(.leaf (2736, 2731, 2404191169253537128079662814445383170026211066187894914744703))
(.leaf (2733, 2731, 803505707178335705917490228286392212714990386547708108145281))))
(.branch 4304
(.leaf (2733, 2731, 2854625723517306201376631430153582305215512959))
(.branch 4305
(.leaf (2733, 2731, 738755007285839938224765636700750229733504))
(.leaf (2733, 2731, 1083204599946345452666290559)))))
(.branch 4309
(.branch 4307
(.leaf (2733, 2731, 463020950203452077914393468))
(.branch 4308
(.leaf (2733, 2731, 774928515655821686927917439))
(.leaf (2733, 2730, 30355363296470697314688570425727))))
(.branch 4310
(.leaf (2733, 2730, 355893369049229600859033694044288))
(.branch 4311
(.leaf (2733, 2730, 30345158753627114057042728321407))
(.leaf (2732, 2730, 70988896657269095373938091819904))))))
(.branch 4318
(.branch 4315
(.branch 4313
(.leaf (2732, 2730, 30353188438921713029636702667135))
(.branch 4314
(.leaf (2732, 2730, 50627258877028294885252125361797))
(.leaf (2732, 2730, 16569544348920951854514504063))))
(.branch 4316
(.leaf (2732, 2730, 463096489620436117551514239))
(.branch 4317
(.leaf (2732, 2730, 4498420040069442494892343679))
(.leaf (2732, 2730, 463030376489677054915052416)))))
(.branch 4321
(.branch 4319
(.leaf (2732, 2730, 154749570265293039314338175))
(.branch 4320
(.leaf (2732, 2730, 463181123282244097951074176))
(.leaf (2732, 2730, 772510664088931497509126527))))
(.branch 4323
(.branch 4322
(.leaf (2732, 2730, 463058821369035395033923712))
(.leaf (2732, 2730, 3250808594514812612827480447)))
(.branch 4324
(.leaf (2732, 2730, 463030413383174015607047040))
(.leaf (2732, 2730, 154749570193516920270094719)))))))
(.branch 4337
(.branch 4331
(.branch 4328
(.branch 4326
(.leaf (2732, 2729, 30352872909282941667259854029183))
(.branch 4327
(.leaf (2732, 2729, 91192078084331635735371420991616))
(.leaf (2732, 2729, 30345158753627114057042862342527))))
(.branch 4329
(.leaf (2731, 2729, 70830440459726014992157715137153))
(.branch 4330
(.leaf (2731, 2729, 30348246350170554216618030793087))
(.leaf (2731, 2729, 50627258914917907265367972970624)))))
(.branch 4334
(.branch 4332
(.leaf (2731, 2729, 154749570193516920303649151))
(.branch 4333
(.leaf (2731, 2729, 463035117302900686850032255))
(.leaf (2731, 2729, 774928516087041351282065791))))
(.branch 4335
(.leaf (2731, 2727, 1988700324077720677048316011913085569))
(.branch 4336
(.leaf (2731, 2727, 4662712925050274941322697036567740799))
(.leaf (2731, 2727, 1988700482534031575371027430359630463))))))
(.branch 4343
(.branch 4340
(.branch 4338
(.leaf (2729, 2727, 3317908046415999499770975978405167487))
(.branch 4339
(.leaf (2729, 2724, 559775108695765165549103303366714764552736377733503))
(.leaf (2729, 2724, 6535843863547331873576368609752275028634674638292607))))
(.branch 4341
(.leaf (2729, 2724, 130342087878129138511188585620377828262271))
(.branch 4342
(.leaf (2726, 2724, 217442421183165393635272330972496954065792))
(.leaf (2726, 2724, 130331474823350911084610267696241540333951)))))
(.branch 4346
(.branch 4344
(.leaf (2726, 2724, 43558131848508203003533678549740541641345))
(.branch 4345
(.leaf (2726, 2724, 1707010322579263730495783295))
(.leaf (2726, 2724, 463035080409414729864250754))))
(.branch 4348
(.branch 4347
(.leaf (2726, 2724, 2010450703301972703393612159))
(.leaf (2726, 2724, 463058821369035403623858815)))
(.branch 4349
(.leaf (2726, 2724, 774928516810994991264432511))
(.leaf (2726, 2721, 130331464438757507126741499879520607469951))))))))
(.branch 4375
(.branch 4362
(.branch 4356
(.branch 4353
(.branch 4351
(.leaf (2726, 2721, 304214424748004701818395962386051793617792))
(.branch 4352
(.leaf (2726, 2721, 130331474823350293323515869285880902386047))
(.leaf (2723, 2721, 217442421284815126297225164688965196776065))))
(.branch 4354
(.leaf (2723, 2721, 130335478084228841436711218160889864651135))
(.branch 4355
(.leaf (2723, 2721, 392347557760324582419050286335210190471296))
(.leaf (2723, 2721, 154749570409408227356705151)))))
(.branch 4359
(.branch 4357
(.leaf (2723, 2721, 463035080409412539430929280))
(.branch 4358
(.leaf (2723, 2721, 774928515655821686843900287))
(.leaf (2723, 2712, 10329294906866417708493850177705737985422732303991432032726702939505023))))
(.branch 4360
(.leaf (2723, 2712, 31084976069910371028684911267135496530450665605915325141269016943198849))
(.branch 4361
(.leaf (2723, 2712, 10325922445275869329199884676038913612412142802087799580505129445949823))
(.leaf (2714, 2712, 24102349891109105831010475968073542337794987338998671730046595942515327))))))
(.branch 4368
(.branch 4365
(.branch 4363
(.leaf (2714, 2712, 10326239616280666011888166018930119201700625239780154373305282880209279))
(.branch 4364
(.leaf (2714, 2711, 1129025600316655614948163678059456226975935447788807234026924301521176756607))
(.leaf (2714, 2711, 50785715244428994696654836663166))))
(.branch 4366
(.leaf (2714, 2711, 30346709805453679626273926676863))
(.branch 4367
(.leaf (2713, 2711, 50627258886473027849904789074603))
(.leaf (2713, 2711, 30345161171478897120014227341695)))))
(.branch 4371
(.branch 4369
(.leaf (2713, 2694, 537500363429256788348071020384254029210333556551922636534708680291253300494905210025352925310606130559975843430783))
(.branch 4370
(.leaf (2713, 2693, 4389561121115095177532553106826767600840092343409224873059895041095219940912460869649549101326271264932185076334975))
(.leaf (2713, 2690, 64816865700709437498402277924091009776115401102302837379885460709397030259162205987138401697458711699743927172925233270859235711))))
(.branch 4373
(.branch 4372
(.leaf (2696, 2690, 1450981821548379045642417516184093381394694356458759591297160795753377722670878007522890592185921659445453251369776838635528585344))
(.leaf (2695, 2690, 64818187812648714657915412032409311789537466025722570292758480920628682271411492208420244264896658426606790901586463147822219647)))
(.branch 4374
(.leaf (2692, 2679, 10357674606974437187597933931058913874939487004636517171667200692039947139844641826311032135489083254684982771504910421951844261854471048245607681754536384262074449152147856195322239))
(.leaf (2692, 2675, 55399450987914377648471096567085142691493973745073943548656369995346524147133461371940165662356568084696838794530195071)))))))
(.branch 4387
(.branch 4381
(.branch 4378
(.branch 4376
(.leaf (2692, 2675, 76960557153615087788401877671704573416215122304320720085067280035444188980359931174898529264013526725017835864447))
(.branch 4377
(.leaf (2681, 2674, 1343567695317837089977458614500495597773794877453241794011520278258600346558979893875515594490904827724159))
(.leaf (2677, 2674, 53615254674080797454116274060232305474876987764035287923286448116970925024910596566570244368179727893119))))
(.branch 4379
(.leaf (2677, 2674, 303626214723651294087391988408847786141498345048114262389897468523260331725345246792953430183965509878143))
(.branch 4380
(.leaf (2676, 2674, 187080750981889596696103775096110772299170022623357))
(.leaf (2676, 2674, 30345469447563402409187095806335)))))
(.branch 4384
(.branch 4382
(.leaf (2676, 2674, 131756897291634976577751185557635))
(.branch 4383
(.leaf (2676, 2674, 772510664666518149803409791))
(.leaf (2676, 2674, 463044525142378270131421825))))
(.branch 4385
(.leaf (2676, 2674, 1707010322579263730495783295))
(.branch 4386
(.leaf (2676, 2674, 463068229208510792176959616))
(.leaf (2676, 2674, 1083204599657552126393975167))))))
(.branch 4393
(.branch 4390
(.branch 4388
(.leaf (2676, 2674, 463049192168628927237915263))
(.branch 4389
(.leaf (2676, 2674, 774928515799936875406033279))
(.leaf (2676, 2674, 463030376489674838711927937))))
(.branch 4391
(.leaf (2676, 2674, 1697338916455818161266033023))
(.branch 4392
(.leaf (2676, 2674, 463030413383162994720967815))
(.leaf (2676, 2674, 772510664591364330987848063)))))
(.branch 4396
(.branch 4394
(.leaf (2676, 2674, 463049265955605213486187137))
(.branch 4395
(.leaf (2676, 2674, 15606030470688655352243945855))
(.leaf (2676, 2674, 463020950203453173131051136))))
(.branch 4398
(.branch 4397
(.leaf (2676, 2674, 7251144131331390175795347839))
(.leaf (2676, 2674, 463049376636069664333431423)))
(.branch 4399
(.leaf (2676, 2674, 774928515511987974131417471))
(.leaf (2676, 2674, 463030376489677046325119625)))))))))

def rowDataBlock44 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 4450
(.branch 4425
(.branch 4412
(.branch 4406
(.branch 4403
(.branch 4401
(.leaf (2676, 2674, 2624585019882095631314911615))
(.branch 4402
(.leaf (2676, 2674, 463030413383162986131030914))
(.leaf (2676, 2674, 772510664088368547555705215))))
(.branch 4404
(.leaf (2676, 2674, 463124750032354832971399809))
(.branch 4405
(.leaf (2676, 2674, 1083204599658115076347396479))
(.leaf (2676, 2674, 463039858116132019661373568)))))
(.branch 4409
(.branch 4407
(.leaf (2676, 2674, 4799442569152922209440760191))
(.branch 4408
(.leaf (2676, 2674, 463035080409412539430929023))
(.leaf (2676, 2674, 774928515945740912990290303))))
(.branch 4410
(.leaf (2676, 2674, 463030376489675933928593268))
(.branch 4411
(.leaf (2676, 2674, 1083204599513718413328318847))
(.leaf (2676, 2674, 463030413383165202334157180))))))
(.branch 4418
(.branch 4415
(.branch 4413
(.leaf (2676, 2674, 772510664089494448049881471))
(.branch 4414
(.leaf (2676, 2672, 1988781612172455608338947088263872640))
(.leaf (2676, 2672, 5976364029334758079191887576043553151))))
(.branch 4416
(.leaf (2676, 2672, 1989064456712622105737932171267474561))
(.branch 4417
(.leaf (2674, 2672, 4652328330405959183716563309664731519))
(.leaf (2674, 2672, 1988821860079012891515932747419821693)))))
(.branch 4421
(.branch 4419
(.leaf (2674, 2672, 3328292632100966008499634417801363839))
(.branch 4420
(.leaf (2674, 2672, 463035117302909482943054465))
(.leaf (2674, 2672, 6367419357193096249135399295))))
(.branch 4423
(.branch 4422
(.leaf (2674, 2672, 463020950203457562587628159))
(.leaf (2674, 2672, 1391480683732184584962441599)))
(.branch 4424
(.leaf (2674, 2669, 130331464438757196432806363885930893279615))
(.leaf (2674, 2668, 14294908038209803925306735475902456740498637183)))))))
(.branch 4437
(.branch 4431
(.branch 4428
(.branch 4426
(.leaf (2674, 2668, 8541490306026649662558123910857612863020664953))
(.branch 4427
(.leaf (2671, 2668, 14250306542599676633057114951736161129189212543))
(.leaf (2670, 2667, 559769422005739540240203136586808181442068506280319))))
(.branch 4429
(.leaf (2670, 2664, 367772673071696781315433766261542124993246454719356869002105979263))
(.branch 4430
(.leaf (2670, 2664, 2063648853314768943588426233726697223513883283490437))
(.leaf (2669, 2664, 117190546353746124243276805484976377271999725951)))))
(.branch 4434
(.branch 4432
(.leaf (2666, 2664, 8541402853458411828601815370755322347045979008))
(.branch 4433
(.leaf (2666, 2664, 20026199519755322932010159618819946297572721023))
(.leaf (2666, 2664, 739435572060088178038671117827117116490369))))
(.branch 4435
(.leaf (2666, 2664, 154749570194079870273651071))
(.branch 4436
(.leaf (2666, 2664, 463035080409468816387412854))
(.leaf (2666, 2664, 10967382100826760258858713471))))))
(.branch 4443
(.branch 4440
(.branch 4438
(.leaf (2666, 2651, 190485469091104307679079639759282583534945293421419796269167461931096065088989239816749439))
(.branch 4439
(.leaf (2666, 2651, 318787101175782704027610098375368398768910212251803055545596764656388526583539608810619519))
(.leaf (2666, 2651, 190479648672977084356079982014519593539377996537746062822121761820815247969894939957985663))))
(.branch 4441
(.leaf (2653, 2650, 29137953087087419398557047879469299635688363523382626720150826725006191812476447803675531673983))
(.branch 4442
(.leaf (2653, 2650, 12483275250078788179841855268893138265358770562104767376624030908331821109676143034354829825940))
(.leaf (2653, 2650, 20826846383223843797318848765111221122617508436834876482833086264101947736414639924589895942527)))))
(.branch 4446
(.branch 4444
(.leaf (2652, 2650, 50627258877028294885260715295618))
(.branch 4445
(.leaf (2652, 2650, 30345471865414538079712176963967))
(.leaf (2652, 2647, 306100158929164612584746401489086720136263631231))))
(.branch 4448
(.branch 4447
(.leaf (2652, 2647, 304894989461643397294759019289593211978367))
(.leaf (2652, 2647, 130331464438756576253860396615056050094463)))
(.branch 4449
(.leaf (2649, 2642, 367772672850730080511102124980985977461733460420125825260232638847))
(.leaf (2649, 2642, 157562698237548904616232457049953808167199153339158741711205630593))))))))
(.branch 4475
(.branch 4462
(.branch 4456
(.branch 4453
(.branch 4451
(.leaf (2649, 2642, 262871757272271776084868743047574076543325021084173123656410333567))
(.branch 4452
(.leaf (2644, 2642, 933908089832045030115497748709856449710147707535999))
(.leaf (2644, 2642, 559769422005739540240204687638633954659240163410303))))
(.branch 4454
(.leaf (2644, 2637, 226166750529603968996083886478551531745239523311898764411990396134695633279))
(.branch 4455
(.leaf (2644, 2636, 61396162432273179874171668237103306889035850740794458495))
(.leaf (2644, 2635, 2404215784963145204048638733991959818456045660494986074915199)))))
(.branch 4459
(.branch 4457
(.leaf (2639, 2635, 4011104696951161926217286558720474418331946272522757988091266))
(.branch 4458
(.leaf (2638, 2635, 2404191360815474049625745818350154354806364770805541609996671))
(.leaf (2637, 2631, 103981973179064515553714963205017192779961314660027784117469369015621092579934847))))
(.branch 4460
(.leaf (2637, 2631, 61396162460751231492695273987286113743672921166526349695))
(.branch 4461
(.leaf (2637, 2631, 15206933078181389160188888674784579515709663939068802))
(.leaf (2633, 2631, 19981598029358261686040199969266045204738015615))))))
(.branch 4468
(.branch 4465
(.branch 4463
(.leaf (2633, 2631, 8541402853458411670145537676571917299117654657))
(.branch 4464
(.leaf (2633, 2631, 247672206513007256236589885937801416903235600767))
(.leaf (2633, 2631, 463167343564421028326081408))))
(.branch 4466
(.leaf (2633, 2631, 5717017266816886506134700415))
(.branch 4467
(.leaf (2633, 2631, 463035154196388834269144456))
(.leaf (2633, 2631, 774928515655821686995157375)))))
(.branch 4471
(.branch 4469
(.leaf (2633, 2631, 463124934499796665283576447))
(.branch 4470
(.leaf (2633, 2631, 154749570626988384387662207))
(.leaf (2633, 2631, 463030376489677054915052416))))
(.branch 4473
(.branch 4472
(.leaf (2633, 2631, 7872532002686211590545408383))
(.leaf (2633, 2631, 463072970021745440703054465)))
(.branch 4474
(.leaf (2633, 2631, 772510664017155378565349759))
(.leaf (2633, 2631, 463105860566423354390549392)))))))
(.branch 4487
(.branch 4481
(.branch 4478
(.branch 4476
(.leaf (2633, 2631, 1393898535442627013140742527))
(.branch 4477
(.leaf (2633, 2631, 463044525142378278721356672))
(.leaf (2633, 2631, 774928515655821686978576767))))
(.branch 4479
(.leaf (2633, 2631, 463035080409416928887505535))
(.branch 4480
(.leaf (2633, 2631, 154749570265855989267890559))
(.leaf (2633, 2631, 463030376489675942518523515)))))
(.branch 4484
(.branch 4482
(.leaf (2633, 2631, 154749572497108129653129599))
(.branch 4483
(.leaf (2633, 2631, 463020950203520204685640321))
(.leaf (2633, 2631, 772510664017155378514952575))))
(.branch 4485
(.leaf (2633, 2631, 463271825922854519226434430))
(.branch 4486
(.leaf (2633, 2631, 154749570265855989401977215))
(.leaf (2633, 2631, 463044488248890131302253442))))))
(.branch 4493
(.branch 4490
(.branch 4488
(.leaf (2633, 2631, 774928515655821686961340799))
(.branch 4489
(.leaf (2633, 2631, 463039821222651538758894207))
(.leaf (2633, 2631, 6027711205044038289296785791))))
(.branch 4491
(.leaf (2633, 2631, 463030376489671540177045119))
(.branch 4492
(.leaf (2633, 2631, 4175636846304112624340500863))
(.leaf (2633, 2631, 463035154196405357008323201)))))
(.branch 4496
(.branch 4494
(.leaf (2633, 2631, 772510664017155378515083647))
(.branch 4495
(.leaf (2633, 2631, 463096415833457615100117888))
(.leaf (2633, 2631, 1697338918261480136948973951))))
(.branch 4498
(.branch 4497
(.leaf (2633, 2631, 463058784475547256204755072))
(.leaf (2633, 2631, 774928515655821687163060607)))
(.branch 4499
(.leaf (2633, 2629, 1988842697085980669053945002772595329))
(.leaf (2633, 2629, 21979022947644955062829775106919629183)))))))))

def rowDataBlock45 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 4550
(.branch 4525
(.branch 4512
(.branch 4506
(.branch 4503
(.branch 4501
(.leaf (2633, 2629, 1988700324077706546842355541806613374))
(.branch 4502
(.leaf (2631, 2629, 5976364029953728098978411426928722303))
(.leaf (2631, 2629, 1989209206565549870675654535737705087))))
(.branch 4504
(.leaf (2631, 2629, 3317908037764926337845370361420317055))
(.branch 4505
(.leaf (2631, 2629, 463030376489675933928587392))
(.leaf (2631, 2629, 154749570772229472370229631)))))
(.branch 4509
(.branch 4507
(.leaf (2631, 2629, 463030413383162986131031428))
(.branch 4508
(.leaf (2631, 2629, 772510664089494447596962175))
(.leaf (2631, 2629, 463087044887468170647896705))))
(.branch 4510
(.leaf (2631, 2629, 1083204599658115076347396479))
(.branch 4511
(.leaf (2631, 2629, 463044525142379365348084608))
(.leaf (2631, 2629, 6352912247357720699089453439))))))
(.branch 4518
(.branch 4515
(.branch 4513
(.leaf (2631, 2629, 463327645770421572919558783))
(.branch 4514
(.leaf (2631, 2629, 774928517602784100751507839))
(.leaf (2631, 2626, 130331464438766175124868495932773533548927))))
(.branch 4516
(.leaf (2631, 2621, 368595425055543554656704590211445841042345685612589900305686069631))
(.branch 4517
(.leaf (2631, 2618, 44349502737186338023651621697153455692977634631186014789293295511716366301135231))
(.leaf (2628, 2618, 73991821756101915173448713775310957913610882350971856462332170982486014240438915)))))
(.branch 4521
(.branch 4519
(.leaf (2623, 2618, 44357609031519751464162996785797091557209520179020476464595148108004475810152831))
(.branch 4520
(.leaf (2620, 2614, 3556430898083565366005417965376214007395885311531567144627625319583219828278897665222237530045219714))
(.leaf (2620, 2614, 49629163706933547549959953855218846831300323205639722644211416765961310871002181206399))))
(.branch 4523
(.branch 4522
(.leaf (2620, 2614, 803505707553941626711532278000434064570822266136571636810879))
(.leaf (2616, 2614, 19936996538961200439444016745729352851632816511)))
(.branch 4524
(.leaf (2616, 2614, 8541577078030376523458644001139659817938256513))
(.leaf (2616, 2614, 14250306517297614041725176002053179620138418559)))))))
(.branch 4537
(.branch 4531
(.branch 4528
(.branch 4526
(.leaf (2616, 2614, 463035154196405365598259070))
(.branch 4527
(.leaf (2616, 2614, 1393898535298511824377217407))
(.leaf (2616, 2613, 30347022917241104211893211300223))))
(.branch 4529
(.leaf (2616, 2613, 50785715220946289508440533314171))
(.branch 4530
(.leaf (2616, 2613, 30345158753627114057042778521983))
(.leaf (2615, 2610, 19981598030692681978370538882518193806239400319)))))
(.branch 4534
(.branch 4532
(.leaf (2615, 2609, 559769422005742209080786878481010769251829865775487))
(.branch 4533
(.leaf (2615, 2609, 933908087920338692713021413476310975861762771845759))
(.leaf (2612, 2609, 31354978080598494894195652697202516100133159295))))
(.branch 4535
(.leaf (2611, 2609, 8541403534023145512022417232082349789898811497))
(.branch 4536
(.leaf (2611, 2609, 59877631190863966781058654654351785862885212543))
(.leaf (2611, 2609, 213044992031270186954216246805890))))))
(.branch 4543
(.branch 4540
(.branch 4538
(.leaf (2611, 2609, 772510663872758715462386047))
(.branch 4539
(.leaf (2611, 2609, 463020950203452069324456577))
(.leaf (2611, 2609, 2627002871305996532497514879))))
(.branch 4541
(.leaf (2611, 2609, 463096600300899447412293760))
(.branch 4542
(.leaf (2611, 2609, 154749570193516920286806399))
(.leaf (2611, 2608, 30345469447562899413403713864063)))))
(.branch 4546
(.branch 4544
(.leaf (2611, 2608, 50785715258503860422700496257152))
(.branch 4545
(.leaf (2611, 2608, 30345158753627114057042778784127))
(.leaf (2610, 2607, 4662712924431304921680006899084231039))))
(.branch 4548
(.branch 4547
(.leaf (2610, 2607, 1988700482534121484801649309258809983))
(.leaf (2610, 2607, 3317908044898797594930200215390519679)))
(.branch 4549
(.leaf (2609, 2606, 4652328330405959182421778416812425599))
(.leaf (2609, 2606, 1988700482534093187496235814990316932))))))))
(.branch 4575
(.branch 4562
(.branch 4556
(.branch 4553
(.branch 4551
(.leaf (2609, 2606, 4641943737307859546663010898500649343))
(.branch 4552
(.leaf (2608, 2604, 217442421183165393635272330972496954065792))
(.leaf (2608, 2604, 130331474823350911084609476751556983390591))))
(.branch 4554
(.leaf (2608, 2600, 13690395571045240066456622356837131148063834419719124216129175))
(.branch 4555
(.leaf (2606, 2600, 184091586627354886391494740482675663152231323256647319935))
(.leaf (2606, 2598, 157561072468201678486422753867471129254008244523128740598331146368)))))
(.branch 4559
(.branch 4557
(.leaf (2602, 2598, 52658550049871994562950507175061244336773187785975279469142671743))
(.branch 4558
(.leaf (2602, 2579, 1195709196366709909388997588130771195929747140549299810641688569199341707932268757861796535412979126383173326030163358501457943191063857831983710591))
(.leaf (2600, 2565, 53948445827467519210274085894270196224372581477221963046013649160142396714676244875773011143619967262489935975253673695375293182986189869924693836393623664074419251668658901102107372045176784037937070841913600311424))))
(.branch 4560
(.leaf (2600, 2565, 1748527729034927601853595737401034221541108227382923366531983413316594558319148310705776668974068407569598069789196468121495915534414817044791463337854314567261842312328597162845003441355064738175))
(.branch 4561
(.leaf (2581, 2565, 2915426223396645558851041052266411189142587075011785405849684514364899632100957376709352856111384529668984111856144909970022418440040934639022237181154342627616841183415519032985814421168512238207))
(.leaf (2567, 2565, 406862060172258308656382372597130527436494791760533744414515950001646577653279540544097329151085029336976011570265421865733800438665239101009735721694635892441498929754689574365139566975))))))
(.branch 4568
(.branch 4565
(.branch 4563
(.leaf (2567, 2565, 5038381208082701061526159317012424222407565255826708749212921642950937307621018301487910653383075881118563225200539636875412554191757511109838761013537260267361552278266856150337983560566))
(.branch 4564
(.leaf (2567, 2565, 20892031528448826914125434480931150197050934878777756227570064076767671080076960370444141003135))
(.leaf (2567, 2565, 463035080409412539430929535))))
(.branch 4566
(.leaf (2567, 2565, 772510668185799784237039999))
(.branch 4567
(.leaf (2567, 2565, 463049265955605213486187392))
(.leaf (2567, 2565, 154749570266418939221311871)))))
(.branch 4571
(.branch 4569
(.leaf (2567, 2565, 463030413383214530033554031))
(.branch 4570
(.leaf (2567, 2565, 1080786748018322868111737215))
(.leaf (2567, 2565, 463020950203458692164027007))))
(.branch 4573
(.branch 4572
(.leaf (2567, 2565, 5112554356433674115894608255))
(.leaf (2567, 2565, 463030376489674847301862272)))
(.branch 4574
(.leaf (2567, 2565, 2318726787159869429878030719))
(.leaf (2567, 2565, 463020950203452077914394229)))))))
(.branch 4587
(.branch 4581
(.branch 4578
(.branch 4576
(.leaf (2567, 2565, 772510664088931497559327103))
(.branch 4577
(.leaf (2567, 2565, 463058636901594657938407552))
(.leaf (2567, 2565, 10690538088279688315846852991))))
(.branch 4579
(.leaf (2567, 2565, 463030413383166280370946944))
(.branch 4580
(.leaf (2567, 2565, 2012868554941201961743024511))
(.leaf (2567, 2564, 30352249103559369466984573895039)))))
(.branch 4584
(.branch 4582
(.leaf (2567, 2564, 436389182158981354630442412606846))
(.branch 4583
(.leaf (2567, 2564, 30345158753627114057042778784127))
(.leaf (2566, 2560, 1312437012508994005223455348257651943884939027482239))))
(.branch 4585
(.leaf (2566, 2560, 559815272337867729585975234541062990704172363415935))
(.branch 4586
(.leaf (2566, 2560, 933908087744072426647975289302688957963642232308351))
(.leaf (2562, 2560, 48459649647871482844991488651753586313222488447))))))
(.branch 4593
(.branch 4590
(.branch 4588
(.leaf (2562, 2560, 8541490306026690306605484283729833715583352960))
(.branch 4589
(.leaf (2562, 2560, 14294908007705059889150539478431585509583028607))
(.leaf (2562, 2560, 463020950203452077914401186))))
(.branch 4591
(.leaf (2562, 2560, 772510665462810858917855615))
(.branch 4592
(.leaf (2562, 2560, 463035080409412530840995198))
(.leaf (2562, 2560, 154749570266418939221311871)))))
(.branch 4596
(.branch 4594
(.leaf (2562, 2559, 30345161171478969459083292246399))
(.branch 4595
(.leaf (2562, 2559, 111236803200403619664944741417088))
(.leaf (2562, 2559, 30345780141498395976438560784767))))
(.branch 4598
(.branch 4597
(.leaf (2561, 2559, 70988896643194229652320543507328))
(.leaf (2561, 2559, 30345158753627330792774845727103)))
(.branch 4599
(.leaf (2561, 2559, 91192078098443394948439218258561))
(.leaf (2561, 2559, 1707010322579263730663489919)))))))))

def rowDataBlock46 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 4650
(.branch 4625
(.branch 4612
(.branch 4606
(.branch 4603
(.branch 4601
(.leaf (2561, 2559, 463270866692164893942939776))
(.branch 4602
(.leaf (2561, 2559, 154749570193516920286675327))
(.leaf (2561, 2559, 463049265955605222076121727))))
(.branch 4604
(.leaf (2561, 2559, 774928518598642568353808767))
(.branch 4605
(.leaf (2561, 2548, 44349499203492208466883503405703408606391041536034467390267847847135767506583935))
(.leaf (2561, 2548, 282070206108684331947856591340315928339264517007707648526616305033110023485457788)))))
(.branch 4609
(.branch 4607
(.leaf (2561, 2548, 44349502737186338023651867183782908147549132908900426429445646438489502093803903))
(.branch 4608
(.leaf (2550, 2544, 1364908199354534400250274732590639228324382633012016383265280757945056872717798905698401127799652991))
(.leaf (2550, 2544, 818120614187879628829590784497619405654776625286005476883116371437373652388786378607931919821832575))))
(.branch 4610
(.leaf (2550, 2528, 31659736853079111610662167889184535479390876394976814678324300653256663356020811871140014629857221468534397078325501647552685200132790576023412885821484221372805252285370139263))
(.branch 4611
(.leaf (2546, 2528, 38664042518108652518506901083565892778981190442658891833085398501860965756264174291792083219833844530022385586345991844397439))
(.leaf (2546, 2523, 1195660133240998237512111184826801761372913771607295384776586432479549275226908330035790799422524795171786798078142908631751347217273303952607150463))))))
(.branch 4618
(.branch 4615
(.branch 4613
(.leaf (2530, 2522, 235480732515757214974731915268844236048118094094324517811075880520067396431958517488040137412546168604664556468063579161018066808844141147004736458260863))
(.branch 4614
(.leaf (2530, 2517, 5135583245236622359402248566465485531818821210443388585662070926445159489986391071437736791123123049927489460287960505658935940959833756011637772571885306239))
(.leaf (2525, 2504, 7744008012331182808841142545702039401372688445900347566463244404896985458571776756908636880565137028721496565073361000827613044872289664595246356371190261447330252143851464564372089901245934915487167691290325735929020799))))
(.branch 4616
(.leaf (2524, 2504, 18245815782949799085063239968051902067546986035954372092435760353894392951350368960599990037078554865317728109737615899900754937734165551842686))
(.branch 4617
(.leaf (2519, 2504, 30533738181334071195336759477421443686959066231261418721242937492269221799816222065402765107435528684071814755882238639884463915255037333340543))
(.leaf (2506, 2504, 105794616913102916560422768213119938533892460411050910901907622698073046647655511614484277454936578908587860984082662015)))))
(.branch 4621
(.branch 4619
(.leaf (2506, 2504, 4091352576758280668783513023324495130273021453057302901964580086725272947199094102860925159032576550277628882846079))
(.branch 4620
(.leaf (2506, 2495, 7109189921825595573742564433646287148935209114541927208350088967155563300371407267242088801244216269621075939507244593529222103761279))
(.leaf (2506, 2495, 44888468766730483099011027263594055885424254991411247232907549444342399))))
(.branch 4623
(.branch 4622
(.leaf (2506, 2495, 10325923268028147989802928567185788370144207942764987985646986201137535))
(.leaf (2497, 2495, 17227563484608157320596048388983211450885803866177733662015204590813312)))
(.branch 4624
(.leaf (2497, 2495, 10326028168943726160764440977416540304749572216462182932990706717753727))
(.leaf (2497, 2495, 176102529190913001542799076583584171973019758279624409510176443737243776)))))))
(.branch 4637
(.branch 4631
(.branch 4628
(.branch 4626
(.leaf (2497, 2495, 772510664088368548176331135))
(.branch 4627
(.leaf (2497, 2495, 463035117302900678260101239))
(.leaf (2497, 2495, 17756709506729279235159032191))))
(.branch 4629
(.leaf (2497, 2495, 463030413383166280370947458))
(.branch 4630
(.leaf (2497, 2495, 154749570193516920269963647))
(.leaf (2497, 2495, 463035080409426888916664959)))))
(.branch 4634
(.branch 4632
(.leaf (2497, 2495, 12506344669196746148146053503))
(.branch 4633
(.leaf (2497, 2495, 463030376489675933928587392))
(.leaf (2497, 2495, 2624585022624224854430122367))))
(.branch 4635
(.leaf (2497, 2495, 463049302849093369495229296))
(.branch 4636
(.leaf (2497, 2495, 772510663872758715445674367))
(.leaf (2497, 2495, 463053969875344009421849470))))))
(.branch 4643
(.branch 4640
(.branch 4638
(.leaf (2497, 2495, 1391480683803960704006947199))
(.branch 4639
(.leaf (2497, 2495, 463030413383165167974416512))
(.leaf (2497, 2495, 5428083995352529380287971711))))
(.branch 4641
(.leaf (2497, 2495, 463237828573544195989373567))
(.branch 4642
(.leaf (2497, 2495, 154749570194079870223384959))
(.leaf (2497, 2495, 463030376489683634804950145)))))
(.branch 4646
(.branch 4644
(.leaf (2497, 2495, 154749570049683207153975679))
(.branch 4645
(.leaf (2497, 2495, 463035117302900686850034044))
(.leaf (2497, 2495, 772510664160707616654360959))))
(.branch 4648
(.branch 4647
(.leaf (2497, 2484, 44353578853364991969507241899907459118809540518992167514006434626874723740352895))
(.leaf (2497, 2484, 103981972875387676293329495615364331245080159888092031837250606363406051443671679)))
(.branch 4649
(.leaf (2497, 2484, 44349502737186338023651621697153467110959174934060176895060695533888740255465855))
(.leaf (2486, 2483, 16565849785939697877041264325802299334656587589301283548619153644734820134003172049279))))))))
(.branch 4675
(.branch 4662
(.branch 4656
(.branch 4653
(.branch 4651
(.leaf (2486, 2477, 230278123108464861315822286091065770719545457677586257523979026376429441824911599038782681873175063321574379553662))
(.branch 4652
(.leaf (2486, 2477, 76960557081943255905082582892167316956212568965160614783007167909233837648088990519524049542489778077291048403327))
(.leaf (2485, 2474, 1129025602315532275757651945588227269575587437358854590081571403545133908351))))
(.branch 4654
(.leaf (2479, 2472, 2906518306782834666248224977134000146690614569969427967676255227010371564468309001088))
(.branch 4655
(.leaf (2479, 2472, 971378795615601722325961567982507822656508413203476838633444252503339251459071869311))
(.leaf (2476, 2472, 103981972889245088886672676650236668385761043064109892364216242091811627744564598)))))
(.branch 4659
(.branch 4657
(.leaf (2474, 2472, 559775108695783753971856855631773264500336602710399))
(.branch 4658
(.leaf (2474, 2472, 187080752718010232726573359361256384231206496961410))
(.leaf (2474, 2472, 3328292631792689925872346289445798271))))
(.branch 4660
(.leaf (2474, 2472, 463158009511931795856097921))
(.branch 4661
(.leaf (2474, 2472, 2318726787303703143010730367))
(.leaf (2474, 2472, 463068192315025934702805631))))))
(.branch 4668
(.branch 4665
(.branch 4663
(.leaf (2474, 2472, 3554248975022193229176963455))
(.branch 4664
(.leaf (2474, 2470, 1988700324077716010022090596329390208))
(.leaf (2474, 2470, 3328292632100966008427858299026604415))))
(.branch 4666
(.leaf (2474, 2470, 1988740888896913850183203436309185151))
(.branch 4667
(.leaf (2472, 2470, 3317908038070784565891171299702604159))
(.leaf (2472, 2470, 1988700482534041001657255688715305854)))))
(.branch 4671
(.branch 4669
(.leaf (2472, 2470, 7300399728569415208828056649827549567))
(.branch 4670
(.leaf (2472, 2470, 463049302849093369495227268))
(.leaf (2472, 2470, 772510667037944828942942591))))
(.branch 4673
(.branch 4672
(.leaf (2472, 2469, 30346093253285819999107959095679))
(.leaf (2472, 2468, 11324429798905009590979781064134689151)))
(.branch 4674
(.leaf (2472, 2468, 1988700482534031575371066991303393408))
(.leaf (2471, 2468, 4652328330405959182277381753759859071)))))))
(.branch 4687
(.branch 4681
(.branch 4678
(.branch 4676
(.leaf (2470, 2448, 4248098725267152462943726629792578581600646159757775234709727868961775490461161498505125869123000815460944728550927710857620078134399))
(.branch 4677
(.leaf (2470, 2448, 1419671700260722418375218888814360005876728529579060936410449672435026138423126283490653624584855287236701898691999557644147795034495))
(.leaf (2470, 2438, 158045572020519982983412798139770921634240383072448723507315460692692201372588801308331438556784241211277257124606578867761230961232121071838297010196293223324467905457463168639))))
(.branch 4679
(.leaf (2450, 2438, 3389040313526221168417844508835053431654211202529808279897153682262296161385723808072098748252274886150502924878094535534086165569505536954435224014929132100397743579660671))
(.branch 4680
(.leaf (2450, 2436, 6208222848363415693752550394797040815944392932402769097731133469189408486104043216307717080180335606613581877379073969026078116099209025384855631558320350379952089049861303476093822))
(.leaf (2440, 2436, 22887266559902458538918097486082917061088468517013789687013254996099036486023638797201785577111283792932530650080387256639022721420475070332289138339423754456135234312474434683797887)))))
(.branch 4684
(.branch 4682
(.leaf (2440, 2434, 12483274255432788718329366285869063568547819325645977984246300576428935514407955377434423918720))
(.branch 4683
(.leaf (2438, 2434, 446779217097154014407793384382858648460692501113009016100027526013286572298348426612513758249343))
(.leaf (2438, 2434, 8541490306027035503709549507162506017187496577))))
(.branch 4685
(.leaf (2436, 2434, 14250306521290490330259159327695815967021990271))
(.branch 4686
(.leaf (2436, 2434, 1988700324077753788953930528171436689))
(.leaf (2436, 2434, 5976364029643034163337451728709747071))))))
(.branch 4693
(.branch 4690
(.branch 4688
(.leaf (2436, 2434, 463120304367033077559394943))
(.branch 4689
(.leaf (2436, 2434, 774928517890451526949798271))
(.leaf (2436, 2433, 30345158753627330229825346142591))))
(.branch 4691
(.leaf (2436, 2424, 2037184992247087167053800826866565888319069633795889775786820660838671516031))
(.branch 4692
(.leaf (2436, 2424, 676719707293492706659724356819173581907332546294233807625511774396205695104))
(.leaf (2435, 2424, 1129025600737082029147285049668200053519920484026864642605594980669739172223)))))
(.branch 4696
(.branch 4694
(.leaf (2426, 2424, 676740331652696284498153684073665551816261311355092467663873258669282886273))
(.branch 4695
(.leaf (2426, 2424, 1579571601835143618942673121475747805849888516566264231945198408687066677631))
(.leaf (2426, 2424, 3451030736080965239520980717271865531842964143586837241243099165819776))))
(.branch 4698
(.branch 4697
(.leaf (2426, 2424, 1080786748018322868865597823))
(.leaf (2426, 2424, 463039858116127630204797567)))
(.branch 4699
(.leaf (2426, 2424, 774928515728160755976110463))
(.leaf (2426, 2424, 463030376489671540177044862)))))))))

def rowDataBlock47 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 4750
(.branch 4725
(.branch 4712
(.branch 4706
(.branch 4703
(.branch 4701
(.leaf (2426, 2424, 1391480683732184584945598847))
(.branch 4702
(.leaf (2426, 2424, 463030413383173938297635712))
(.leaf (2426, 2424, 772510664450626842632520063))))
(.branch 4704
(.leaf (2426, 2424, 463020950203452069324456577))
(.branch 4705
(.leaf (2426, 2424, 2321144638943495351633183103))
(.leaf (2426, 2424, 463238529549802585882298493)))))
(.branch 4709
(.branch 4707
(.leaf (2426, 2424, 154749570193516920387207551))
(.branch 4708
(.leaf (2426, 2424, 463044598929354573559562879))
(.leaf (2426, 2424, 774928515799936875020484991))))
(.branch 4710
(.leaf (2426, 2421, 130331464438764597476675555884888437621119))
(.branch 4711
(.leaf (2426, 2420, 60145240133235949662559297836443821172896825727))
(.leaf (2426, 2420, 8541403534023084823249945564932921000319713408))))))
(.branch 4718
(.branch 4715
(.branch 4713
(.leaf (2423, 2420, 14250306514649542662092134938770306120527446399))
(.branch 4714
(.leaf (2422, 2420, 8542189246008345755753113063538311519230954119))
(.leaf (2422, 2420, 71206409750383103042766714861109682652477063551))))
(.branch 4716
(.leaf (2422, 2418, 43558131686724295224853084445195861164160))
(.branch 4717
(.leaf (2422, 2418, 5976364029334758079408060358662226303))
(.leaf (2422, 2418, 1988700324077706546842352243271739762)))))
(.branch 4721
(.branch 4719
(.leaf (2420, 2418, 31174580684110134792956721156048617855))
(.branch 4720
(.leaf (2420, 2418, 1988720685715482175956827990818488959))
(.leaf (2420, 2418, 3317908038075620269313745005467140479))))
(.branch 4723
(.branch 4722
(.leaf (2420, 2414, 8541402853458472279689813754444878827778670720))
(.leaf (2420, 2414, 145936206910659221189120824985687629252169564543)))
(.branch 4724
(.leaf (2420, 2414, 8545047958172808074193827275424806318511161985))
(.leaf (2416, 2414, 14250306545237363437498665619536551108635787647)))))))
(.branch 4737
(.branch 4731
(.branch 4728
(.branch 4726
(.leaf (2416, 2414, 8541490986591423990026090922763597036851757950))
(.branch 4727
(.leaf (2416, 2414, 14294908096747758709355628263527916814064419199))
(.leaf (2416, 2414, 463039821222639482785694335))))
(.branch 4729
(.leaf (2416, 2414, 774928516086478401261535615))
(.branch 4730
(.leaf (2416, 2414, 463030376489674847301861504))
(.leaf (2416, 2414, 2323562491160874211793109375)))))
(.branch 4734
(.branch 4732
(.leaf (2416, 2414, 463030413383193815406290547))
(.branch 4733
(.leaf (2416, 2414, 772510666031390311906804095))
(.leaf (2416, 2414, 463101414901101590388605569))))
(.branch 4735
(.leaf (2416, 2414, 2639092129502142824244576639))
(.branch 4736
(.leaf (2416, 2414, 463020950203453164541118587))
(.leaf (2416, 2414, 7576345176807725423824601471))))))
(.branch 4743
(.branch 4740
(.branch 4738
(.leaf (2416, 2414, 463035117302900686850032255))
(.branch 4739
(.leaf (2416, 2414, 774928515800499825074045311))
(.leaf (2416, 2414, 463030376489671540177044354))))
(.branch 4741
(.leaf (2416, 2414, 1085622451368557503838093695))
(.branch 4742
(.leaf (2416, 2414, 463030413383167375587606656))
(.leaf (2416, 2414, 772510664450063892628898175)))))
(.branch 4746
(.branch 4744
(.leaf (2416, 2413, 30345469447562898850453760573823))
(.branch 4745
(.leaf (2416, 2413, 819140435265392369539338498671231))
(.leaf (2416, 2413, 30345467029711115787482815463807))))
(.branch 4748
(.branch 4747
(.leaf (2415, 2412, 5986748623049409883025892092466495871))
(.leaf (2415, 2409, 559786437474326029490252918163404494009517493322111)))
(.branch 4749
(.leaf (2415, 2408, 61396162386735058176118872084272760679301893542979371391))
(.leaf (2414, 2408, 933908088266065577504694892246097766284192364036735))))))))
(.branch 4775
(.branch 4762
(.branch 4756
(.branch 4753
(.branch 4751
(.leaf (2411, 2408, 559775153297255562610350829213893657515469024133503))
(.branch 4752
(.leaf (2410, 2406, 4023658898179991776165444499853231467686971870742991809228885))
(.leaf (2410, 2406, 135051729313915151419983894317281280515370514833895063935))))
(.branch 4754
(.leaf (2410, 2406, 218122986018657003058537045614466720268927))
(.branch 4755
(.leaf (2408, 2406, 3317908038075620274066168511293620607))
(.leaf (2408, 2405, 130332798859049837465655184092210235703679)))))
(.branch 4759
(.branch 4757
(.leaf (2408, 2405, 218122986160079273217408172436074574839936))
(.branch 4758
(.leaf (2408, 2405, 30345467029711115787482312016255))
(.leaf (2407, 2405, 50627258877028294911691944035198))))
(.branch 4760
(.leaf (2407, 2405, 30345471865414538079712076366207))
(.branch 4761
(.leaf (2407, 2404, 23313443241220487574323594723105636735))
(.leaf (2407, 2404, 91350534409360164408342305767552))))))
(.branch 4768
(.branch 4765
(.branch 4763
(.leaf (2407, 2404, 30345158753627114057042795364735))
(.branch 4764
(.leaf (2406, 2393, 10669546164144162677960173429015747422121012745361949312382694205725690104685149618559))
(.leaf (2406, 2388, 3513765306220455439612806203005133303321836810227351871246524136990856842694862337983717130774843373828309375))))
(.branch 4766
(.leaf (2406, 2383, 7087008563002162114539951147446500763467089743756971053074189895232836763828471146814634335320803080996047666191580776022946883830143))
(.branch 4767
(.leaf (2395, 2383, 2618163393674289054680929090685408365661131003424385024336248281067023233502682716794853792876782611139854497535179236596697203329))
(.leaf (2390, 2383, 64818187812647326425000563808524905567093589964880809479461044652514005558694562118007382030092744122397371397377478111015141759)))))
(.branch 4771
(.branch 4769
(.leaf (2385, 2383, 108477629291533565302666431902666459926285524799674967548048150565023080376557736589769070423659577544994110237430629123483435136))
(.branch 4770
(.leaf (2385, 2383, 1129025600631358361805276205877286806475793821511939032234533200958228005247))
(.leaf (2385, 2350, 12973125883638798867874416280600280846573900414987415347354772719028723237783047884574423303842565937162699838108031641471480519861272054828514220285776664040599656363679411758790786769081643242283135871855034751))))
(.branch 4773
(.branch 4772
(.leaf (2385, 2350, 680925115520476446138094636674320053161096453865037147891945354095795103237632749907596818201740230514772982937184992626536612314259104792591668395700946662060030311050568517820671277418))
(.leaf (2385, 2350, 406866193478772326042267773096794765222381083268345265514185908168533194880992558133049364809343384275721669085754922540663732661047664366456788296112157827767742138669942622580197359999)))
(.branch 4774
(.leaf (2352, 2350, 951805491350000343405636618933047101014033627290358025425858644623968001524588596258878071017500219603252524409191496521222056078940101298852411645414959507726200419048262509306411156354))
(.leaf (2352, 2350, 406862092590342878637005634044246467068123407149827676738090187207151119972007116864991685112466014015731351067787205323754613160007924230567203539236233908144612994139068508492154143103)))))))
(.branch 4787
(.branch 4781
(.branch 4778
(.branch 4776
(.leaf (2352, 2349, 80269175666892944588568668157828588001691967966719711979285484612271695640306795909222454626660980122752436766127210643335223086190628970749169822340125623764486197681770538415820781911998847))
(.branch 4777
(.leaf (2352, 2349, 70988896643194229658857483731840))
(.leaf (2352, 2349, 30345158753627114057042728321407))))
(.branch 4779
(.leaf (2351, 2349, 132232266384945745373911693853313))
(.branch 4780
(.leaf (2351, 2349, 30345471865414538642662869762431))
(.leaf (2351, 2349, 50627258962067785066165554839680)))))
(.branch 4784
(.branch 4782
(.leaf (2351, 2349, 2636674277862350616594547071))
(.branch 4783
(.leaf (2351, 2349, 463233309121228622272594559))
(.leaf (2351, 2349, 774928516306310358022226303))))
(.branch 4785
(.leaf (2351, 2348, 30345158753627114057042728321407))
(.branch 4786
(.leaf (2351, 2328, 498215074699341655194220982191525551710685796774108846528098347646020540504832960396255033866325278551870336358598475392011404160))
(.leaf (2351, 2328, 64816870865209193672220317157926253415091679007551704586211804848700298826473164842478242226742315097640623462055085803162435967))))))
(.branch 4793
(.branch 4790
(.branch 4788
(.leaf (2350, 2328, 108139168645639273500067478281889465996604450749782588519122113917327936847868721852307394190655663055579042733566081330172601987))
(.branch 4789
(.leaf (2330, 2328, 64818192977147081396363941020128713174085542754508336662660436223121146475939895891531087338088820162148636873354954184337719679))
(.leaf (2330, 2326, 649798067358721582632414687526870939317278373520225000455072564481653065490103741927927937476828448738204746049377912562879557485268501378))))
(.branch 4791
(.leaf (2330, 2326, 128829389486486157001354481383381700249153661732977827847066706574094164884224028688007202132709579911466395174345820222440229927125375))
(.branch 4792
(.leaf (2330, 2319, 10325922445275869329199896116321152481798835642501357009864981145977215))
(.leaf (2328, 2316, 10715077458185274093338393938642952694779119831559478298309672562994459505112851284351)))))
(.branch 4796
(.branch 4794
(.leaf (2328, 2314, 12483654707708641741942244373571437116172457728840423984033171840233174874945603514740380729985))
(.branch 4795
(.leaf (2321, 2314, 20826846303642716167032335471854630071410563386806300372361335379194495987045537108081739039103))
(.leaf (2318, 2314, 2906488779800292592516234556943532831256013780971455669424795031121716024153145804156))))
(.branch 4798
(.branch 4797
(.leaf (2316, 2314, 28161154745000661848455324817622712911085091777873092148414167510427955215076434116991))
(.leaf (2316, 2309, 1129025600421556530428542267904571268085755168795329665044884410382283702655)))
(.branch 4799
(.leaf (2316, 2309, 4011104693960929577375142576609846152911726545430741161804417))
(.leaf (2316, 2309, 559769377404246489915262147054155726713921447526783)))))))))

def rowDataBlock48 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 4850
(.branch 4825
(.branch 4812
(.branch 4806
(.branch 4803
(.branch 4801
(.leaf (2311, 2309, 1309514008800472181562851437681120673117727606377854))
(.branch 4802
(.leaf (2311, 2309, 559769422005763570190064746463007652169511451230591))
(.leaf (2311, 2294, 1650072764220266971925691414325564124773372276537191242806510163125006315157971328599791978946963104502770426216562680201599))))
(.branch 4804
(.leaf (2311, 2294, 1369180175585256389669717005483106796542525536206442748988084208534784486090238490737093081502253697))
(.branch 4805
(.leaf (2311, 2294, 818103861604006376266788212941848166141682460118874858147758747018234665083588434824516818456936831))
(.leaf (2296, 2294, 18841554127514050191418162942154862859031883277445945208069204217270488938651055664753288591114706816)))))
(.branch 4809
(.branch 4807
(.leaf (2296, 2294, 818103926789167347491900732440018196327138541056596865792041121430440418415982631155269203702841727))
(.branch 4808
(.leaf (2296, 2294, 1364908199356523693432824493731988826646807039832142912518548693440321250964099959989267396932076159))
(.leaf (2296, 2294, 774928518249332122255884671))))
(.branch 4810
(.leaf (2296, 2294, 463030376489674847301868659))
(.branch 4811
(.leaf (2296, 2294, 1393898536091989783674290559))
(.leaf (2296, 2294, 463030413383162977541098878))))))
(.branch 4818
(.branch 4815
(.branch 4813
(.leaf (2296, 2294, 772510665174580482732458367))
(.branch 4814
(.leaf (2296, 2294, 463020950203452069324456577))
(.leaf (2296, 2294, 10406440520526135271731888511))))
(.branch 4816
(.leaf (2296, 2294, 463035117302902885873288319))
(.branch 4817
(.leaf (2296, 2294, 154749570193516920320360831))
(.leaf (2296, 2285, 10326239616279342127302800454591115811637000889250620566969453780205951)))))
(.branch 4821
(.branch 4819
(.leaf (2296, 2270, 30533738212598694662924876740378737543032552467883529690517257249853476681727583894313816519617178614520387667171757349376424141926668244550015))
(.branch 4820
(.leaf (2296, 2270, 18244325763564906614239677571438173114768190229903915712763198431186269736096862340809483169905329234641097500697001399124075078236351349330043))
(.leaf (2287, 2270, 42775702558619171380815368310797138102945450635792785098442069638545755797577804930393028271855139008505111679285308475625421288747181503742335))))
(.branch 4823
(.branch 4822
(.leaf (2272, 2269, 1195660228509211970573805975055880385901551877898672428905156705971357560560667334743382369333684868957388670330673610962217992983828136235699798399))
(.leaf (2272, 2269, 1994815570394421360296006050492078135734460362247010846273929691335697013756292990958939494035906457362841962919078651515238182232980749416415560319)))
(.branch 4824
(.leaf (2272, 2269, 233074255345050461454832556570941791379092998152161607557450981735793351832168703376758307885602649801087))
(.leaf (2271, 2262, 5841543582681450703187313279319555616228024186514304139997810196863)))))))
(.branch 4837
(.branch 4831
(.branch 4828
(.branch 4826
(.leaf (2271, 2262, 157580431049951747595311000425121753877509271859555773155488237189))
(.branch 4827
(.leaf (2271, 2262, 52658550025639408811612958792528453586782595201715405607361642879))
(.leaf (2264, 2261, 262871757296504361979600083047354178108389970141391428210772672895))))
(.branch 4829
(.leaf (2264, 2261, 157570676433854578164479931585066526227263316466352748768761152127))
(.branch 4830
(.leaf (2264, 2261, 474319092839198457496281591974980866780972439532455159261036609919))
(.leaf (2263, 2256, 282362863173917426399015355015208073405554634181987598719)))))
(.branch 4834
(.branch 4832
(.leaf (2263, 2256, 36685797129407246324025966566775751557553831647096276095))
(.branch 4833
(.leaf (2263, 2256, 12260524267931050161248367175678751495694204263521583487))
(.leaf (2258, 2248, 317792454554865048601843213643703121172366998958252966031269113359165390671413941142229386))))
(.branch 4835
(.leaf (2258, 2248, 190481614107521293714260826467211597705593583576203913211930680728001277404101311322915199))
(.branch 4836
(.leaf (2258, 2236, 42059336463474502398695003951288581723371277059653945821246767351473352705069905141470356871522915855859660288380512589368760558351677354312348926080))
(.leaf (2250, 2236, 4309790138034126472416928492085354945643118921925462521505159678083091033431743658934865561061710419607614226603623311147391))))))
(.branch 4843
(.branch 4840
(.branch 4838
(.leaf (2250, 2236, 989369915285558847452954243065730013652739764129569399491974437651833227395532806274972394667958363647269800656993894990465))
(.branch 4839
(.leaf (2238, 2236, 1650072763451297766129317733157069126523283026746278220220428499579688925987963807228029437141746739735698282477951960285567))
(.leaf (2238, 2236, 2906489011384264553957076258834999455734116040518182784406972376018996337335072653440))))
(.branch 4841
(.leaf (2238, 2236, 16535495592608498890393860930595432250174881451861161698453815894784175530126568325503))
(.branch 4842
(.leaf (2238, 2231, 560044122585095050840654909604165350070721890419071))
(.leaf (2238, 2231, 936831090931962228919543350780257079382294357017217)))))
(.branch 4846
(.branch 4844
(.leaf (2238, 2231, 559775064094272115224162306580508329167011706962303))
(.branch 4845
(.leaf (2233, 2231, 13317211461110489992790642602676166848576431262205057))
(.leaf (2233, 2231, 559769377404250477599249504219626508021074938036607))))
(.branch 4848
(.branch 4847
(.leaf (2233, 2228, 3635333347942101341641133838144222042002421978935644057679575974271))
(.leaf (2233, 2225, 61396162375317076647768665294547143015184523130080133503)))
(.branch 4849
(.leaf (2233, 2225, 36685421523485492005136537331429859292855339348463128972))
(.leaf (2230, 2225, 85628748332869615857188024306154642367616101013725839743))))))))
(.branch 4875
(.branch 4862
(.branch 4856
(.branch 4853
(.branch 4851
(.leaf (2227, 2225, 36685045917569752857647189728484054850184477168434610815))
(.branch 4852
(.leaf (2227, 2225, 405058287425910634665631456631406403092171984493059506559))
(.leaf (2227, 2225, 392347557760324582414272579624526053049218))))
(.branch 4854
(.leaf (2227, 2225, 1085622452237752231920599423))
(.branch 4855
(.leaf (2227, 2225, 463035117302900686850032769))
(.leaf (2227, 2225, 772510665821128504287494527)))))
(.branch 4859
(.branch 4857
(.leaf (2227, 2225, 463020950203452069324456064))
(.branch 4858
(.leaf (2227, 2225, 1393898539398757810071208319))
(.leaf (2227, 2192, 406862092590343840997423514524606301256782517337634415546907940700501499335289718076405813786712954853613696806192567414573799109347489271206937779897531546226704310727896465404571681151))))
(.branch 4860
(.leaf (2227, 2185, 7744008012328614382725837379127655660514421884870155543082855104136810635233180766690285071238764332390996141913199841799465197186435665074610183982097312410042061617060904775089125307199860719189834831485745334658662783))
(.branch 4861
(.leaf (2227, 2180, 2553940692647426177981755203149884150641829063060455658444829987122425905262798395822177817694942121537288518080466745645898689388469395859252289428467975745818680797864468254280044074247986964896236868338763030403946658671500050111898897613183))
(.leaf (2194, 2172, 3773373122131507934219039097735530780552657968018211308011379177449618386286352319872023740858442573605896248445429149302082396421785093101646531342500790577125194342878792622090078188366749255170249354969057488941709218614118518525327313756773782025762851891661308180676491096294015))))))
(.branch 4868
(.branch 4865
(.branch 4863
(.leaf (2187, 2172, 869052085936004573170092397238684384061404848587804550699331536877314244347838869308962501076614930247177414937276209769296079227090439294702376912185766316391120332404836134583885871607742047289915296335680655734446431074465137115253420529721043424061745140190644697132077118652799))
(.branch 4864
(.leaf (2182, 2169, 81753351667343477118483656711171467560975736051565143554616572876152991100724528819806607422313919594622859218596366891766790465437439425879557013755859151331925304239050258927259532136447962923070802157464287866541851786307102062293153134202586321094704111095667364887157569260773898855435403647))
(.leaf (2174, 2145, 18357704790227042893048022556391771978536677959639712156097490659228099620360144817560934684094101959236241876228100179535909898675363051065080166946685604637797851987142845558565549833642460057231162081663007893471030864331115972904964284382808148738176))))
(.branch 4866
(.leaf (2174, 2145, 3524534031713111087122140151735335355721918645633579924706707989083807006596985518975389912560517296476043413976841640539950497001159115792925898096467150315937057682936414984486170270172104766190873474233752569455313279))
(.branch 4867
(.leaf (2171, 2144, 4634864430473265026485755980181033513606593138168571585102088019763380668215198391951420679121751570766666464921691638672044113787196479153985166895225439362285180173091045887490782921679971330266497407))
(.leaf (2147, 2141, 94729962896169383630213409075995382400061731094131555110946934395286215704963950976309335435965036108902210910159117567824124458569086976073205541393292555823663228502713303423)))))
(.branch 4871
(.branch 4869
(.leaf (2147, 2134, 4768289879002541813232272999145779462609023260864884268115050211383655257757784045484437652103756292657126471095252739250801028756887334791725382510693036498165024062959340414428972865537880165160501490011406719))
(.branch 4870
(.leaf (2146, 2133, 38274273323892145435244253697203897193121199545042321583681667844643543566143862341466097068149794061143106007955211989581980429350328132548614212917070324800641267571967397203670599896811219648708991))
(.leaf (2143, 2133, 2906844724682422429348191176345505179184690422693614202855558817238253837083886945154))))
(.branch 4873
(.branch 4872
(.leaf (2136, 2133, 12634980699330232902341537655912531749119482550427477814333706938400448649184803946879))
(.leaf (2135, 2128, 89450623752898766454786827772530367564767116387435150311500263916710789513746682491529513356038632309119)))
(.branch 4874
(.leaf (2135, 2128, 317792454554865048601789293745535451557278209578238791208172222564158453222856908766909322))
(.leaf (2135, 2128, 110244457740461885485040565773123410682496386106220282239)))))))
(.branch 4887
(.branch 4881
(.branch 4878
(.branch 4876
(.leaf (2130, 2128, 4296823355243160606432325747477542366360862696870280))
(.branch 4877
(.leaf (2130, 2128, 559769377404254460090939068350611174406148803527039))
(.leaf (2130, 2127, 12260524096349116606407016424975290794777560128690520447))))
(.branch 4879
(.leaf (2130, 2127, 70988896643157336157558874768256))
(.branch 4880
(.leaf (2130, 2127, 30345161171478753286301111222655))
(.leaf (2129, 2127, 70830440322906514199652994072958)))))
(.branch 4884
(.branch 4882
(.leaf (2129, 2127, 30345158753627330229824875725183))
(.branch 4883
(.leaf (2129, 2127, 172004803848881260077466240614528))
(.leaf (2129, 2127, 12848470676363014562090320255))))
(.branch 4885
(.leaf (2129, 2127, 463020950203477413926470273))
(.branch 4886
(.leaf (2129, 2127, 1391480683659282566028067199))
(.leaf (2129, 2127, 463039858116128716831523455))))))
(.branch 4893
(.branch 4890
(.branch 4888
(.leaf (2129, 2127, 2318726787376042212059054463))
(.branch 4889
(.leaf (2129, 2127, 463030376489673743495267455))
(.leaf (2129, 2127, 774928515511987973778243967))))
(.branch 4891
(.leaf (2129, 2127, 463082488541683076785177472))
(.branch 4892
(.leaf (2129, 2127, 772510664088368547589325183))
(.leaf (2129, 2124, 130331474823350911084611422869546011066751)))))
(.branch 4896
(.branch 4894
(.leaf (2129, 2120, 55495893127975168119174005428638631941146584636339489985201022))
(.branch 4895
(.leaf (2129, 2120, 2404435793854230763217856191132268094022750254800715263836543))
(.leaf (2126, 2120, 8850750131941137441968443595770431100368075487469119943410303))))
(.branch 4898
(.branch 4897
(.leaf (2122, 2120, 2404215593401436218419220622567240209564710398809173684912511))
(.leaf (2122, 2120, 803505708305153470216086668496497542182498238989481623355520)))
(.branch 4899
(.leaf (2122, 2120, 14294908011666782385401524891219194369468727679))
(.leaf (2122, 2120, 463035117302900686850032767)))))))))

def rowDataBlock49 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 4950
(.branch 4925
(.branch 4912
(.branch 4906
(.branch 4903
(.branch 4901
(.leaf (2122, 2120, 772510664881846507020484991))
(.branch 4902
(.leaf (2122, 2120, 463275939546782956456444032))
(.leaf (2122, 2120, 6957375158465449678728135039))))
(.branch 4904
(.leaf (2122, 2120, 463030413383162977541095552))
(.branch 4905
(.leaf (2122, 2120, 4165965439674856521945186687))
(.leaf (2122, 2105, 818112237895941063673569953913866881913096427633536169276152614882832587119685731357991955966460287)))))
(.branch 4909
(.branch 4907
(.leaf (2122, 2098, 18466044979715492175064511746728698785309395308591155228762053670899333294968226054853154942510388846654342525704003705413482653417855))
(.branch 4908
(.leaf (2122, 2095, 1195660133240989719870809520989366292955553472345327747558339300228393650179175219226023370259968648506654223865430867997251943561734924614332645759))
(.leaf (2107, 2095, 23587950290698744740007819362687952460555983619978263772632300010595802336773549551177449885335782185559850104904080504656537507466549925422911389824))))
(.branch 4910
(.leaf (2100, 2095, 1195684617169750023952117872043191873561194232689937311854634461231316637441025441840009310625087258922396736276648804529469992099755421466941587839))
(.branch 4911
(.leaf (2097, 2095, 1994815570762201753883693191321275756411816741046373295094928969731317110282375667154584160926005457363531747401122090542696746429145649132838257279))
(.leaf (2097, 2095, 3388822996168209172362314195309405475811456668063783812904306554211970777471))))))
(.branch 4918
(.branch 4915
(.branch 4913
(.leaf (2097, 2095, 304214424727801520377258556310710382429313))
(.branch 4914
(.leaf (2097, 2095, 154749570265293039314338175))
(.leaf (2097, 2095, 463044598929354573559563391))))
(.branch 4916
(.leaf (2097, 2095, 772510664089494447780266367))
(.branch 4917
(.leaf (2097, 2093, 1988822335447987940208467966536123009))
(.leaf (2097, 2093, 4652328344321904292005774846838374783)))))
(.branch 4921
(.branch 4919
(.leaf (2097, 2093, 1988700482534031575371049364757612924))
(.branch 4920
(.leaf (2095, 2093, 7290015134541651622392540240057074047))
(.leaf (2095, 2090, 559974365854115371087165566042334240030770767855999))))
(.branch 4923
(.branch 4922
(.leaf (2095, 2090, 2063648853314768943689996738107947503604817188557696))
(.leaf (2095, 2090, 130335446930447072466651767454641770529151)))
(.branch 4924
(.leaf (2092, 2088, 4666583269400426476215991091227861851269005804766080))
(.leaf (2092, 2088, 559769422005740864275901135721748875830807840686463)))))))
(.branch 4937
(.branch 4931
(.branch 4928
(.branch 4926
(.leaf (2092, 2088, 19635283039031667297531219029152349902751157949760639))
(.branch 4927
(.leaf (2090, 2088, 48418198550998439115016337354177577343))
(.leaf (2090, 2088, 1988700324077777419233083435369040774))))
(.branch 4929
(.leaf (2090, 2088, 8614050834400114469912863259735687551))
(.branch 4930
(.leaf (2090, 2088, 463030413383162994720965247))
(.leaf (2090, 2088, 154749570265293039381447039)))))
(.branch 4934
(.branch 4932
(.leaf (2090, 2088, 463030376489730918099911297))
(.branch 4933
(.leaf (2090, 2088, 1699756767661575955481035135))
(.leaf (2090, 2088, 463072822447793920473507979))))
(.branch 4935
(.leaf (2090, 2088, 772510665097174864137159039))
(.branch 4936
(.leaf (2090, 2088, 463035080409412530840994688))
(.leaf (2090, 2088, 774928516087604301302202751))))))
(.branch 4943
(.branch 4940
(.branch 4938
(.leaf (2090, 2088, 463054043662318109531770228))
(.branch 4939
(.leaf (2090, 2088, 1393898535298511824327082367))
(.leaf (2090, 2079, 10325923268028417709018109545643315138278243831313095833690137707020671))))
(.branch 4941
(.leaf (2090, 2079, 24102349905540162729253700166204766368276352947571070585315609509037950))
(.branch 4942
(.leaf (2090, 2079, 10325922445275869329199896116321143187587458862742050301047293626614143))
(.leaf (2081, 2076, 14570061041195705218444201160118664230393890695927807450613693047019892679192019599743)))))
(.branch 4946
(.branch 4944
(.leaf (2081, 2076, 2906548065349782513923042178058160126146785554158801811855552894751571312176369959551))
(.branch 4945
(.leaf (2081, 2076, 4849128030157349112767132746737277342297897626291802430597278857639285968236410110335))
(.leaf (2078, 2075, 82802797256277483067003038301627731949350093183))))
(.branch 4948
(.branch 4947
(.leaf (2078, 2069, 676719707293512033855968363621087020387066458297997634746102578916691478653))
(.leaf (2078, 2069, 1129025600421556530427967582019678952800830924040958396040168711987937673599)))
(.branch 4949
(.leaf (2077, 2069, 4011104693960929576063694333885858638092302386603034996048513))
(.leaf (2071, 2069, 2404337905701569350247828962586835708633041213372949772370303))))))))
(.branch 4975
(.branch 4962
(.branch 4956
(.branch 4953
(.branch 4951
(.leaf (2071, 2069, 803505707551018625615698467599281267510870307746240700285822))
(.branch 4952
(.leaf (2071, 2069, 258130277434020160339166006857830975066433187879562903935))
(.leaf (2071, 2069, 463049265955605222076121727))))
(.branch 4954
(.leaf (2071, 2069, 774928516161632220043280767))
(.branch 4955
(.leaf (2071, 2068, 30345158753627834914458168459647))
(.leaf (2071, 2068, 416661369702337374043921830578307)))))
(.branch 4959
(.branch 4957
(.leaf (2071, 2068, 30345161171478753286301128196479))
(.branch 4958
(.leaf (2070, 2068, 50627259118772875967925854340225))
(.leaf (2070, 2068, 30347646722964024797597406396799))))
(.branch 4960
(.leaf (2070, 2060, 3451030734480304297000300124722373038927739835199353942579464988722305))
(.branch 4961
(.leaf (2070, 2060, 474319092863431042853765679390318778575424726417264534954553901439))
(.leaf (2070, 2059, 10325922445275869329199896116321147164886852808696097757137921912209791))))))
(.branch 4968
(.branch 4965
(.branch 4963
(.leaf (2062, 2059, 24156269774851995658928961790846859914560836115628769297459660021760639))
(.branch 4964
(.leaf (2062, 2059, 10326449418110449429368557551845289186273864225579985321806908825928063))
(.leaf (2061, 2059, 17227563487809479208257882007289908794910721755716156982835090030526592))))
(.branch 4966
(.leaf (2061, 2059, 30345469447562971752472728502655))
(.branch 4967
(.leaf (2061, 2059, 91192078084331635736458047725444))
(.leaf (2061, 2059, 772510664088368547555705215)))))
(.branch 4971
(.branch 4969
(.leaf (2061, 2059, 463054043662320304260055681))
(.branch 4970
(.leaf (2061, 2059, 2010450703302535653414076799))
(.leaf (2061, 2059, 463020950203453181721003904))))
(.branch 4973
(.branch 4972
(.leaf (2061, 2059, 1083204599657552126477730175))
(.leaf (2061, 2059, 463035080409412539430929023)))
(.branch 4974
(.leaf (2061, 2059, 774928516015828182157820287))
(.leaf (2061, 2048, 44349499203492524403758213688748000460396642651906241927077861780129184533709183)))))))
(.branch 4987
(.branch 4981
(.branch 4978
(.branch 4976
(.leaf (2061, 2044, 2462805538105569070056344292412367726568490379529432462003495148294193825254149756117704813366412929))
(.branch 4977
(.leaf (2061, 2044, 818103926789157618970337075796607964172139259330646002213140885213004688151687180287973126532235647))
(.leaf (2050, 2044, 1364908202933272409868940336447277063152251542366621069590865176187844227312346175855594369466696319))))
(.branch 4979
(.leaf (2046, 2044, 818128860109511830829267999165766612967654887876900250315161438107589008222108272982930577936023935))
(.branch 4980
(.leaf (2046, 2033, 1284193248520483666665539246894921236129205809358511164633219716392411355239899926366928506756895726417237986987282586891086372639503503177400648833302911))
(.leaf (2046, 2031, 10559321245464486018854892412452164462942467531208420000037957989099303033849779470192390829891554080242729856)))))
(.branch 4984
(.branch 4982
(.leaf (2046, 2031, 190479663850077804869585304800760835505681035919067950173456394177340369901348647178535295))
(.branch 4983
(.leaf (2035, 2031, 317792454791775663195249562067244785353853015342458022529380359533662701209767020490326657))
(.leaf (2033, 2031, 190481614107521293714260405218045046555394923382482130260278458495992676625989625641501055))))
(.branch 4985
(.leaf (2033, 2031, 699239376881171403141950104264146650610535285436849778838399801287181410642331322961300866))
(.branch 4986
(.leaf (2033, 2031, 664644365028274039134626724180001151))
(.leaf (2033, 2031, 463044598929354573559563136))))))
(.branch 4993
(.branch 4990
(.branch 4988
(.leaf (2033, 2031, 774928515655821686843900287))
(.branch 4989
(.leaf (2033, 2030, 30345467029712556094938140311935))
(.leaf (2033, 2030, 131756897296338896318750439441278))))
(.branch 4991
(.leaf (2033, 2030, 30345158753627114057042778784127))
(.branch 4992
(.leaf (2032, 2030, 71147352977667491286624082265984))
(.leaf (2032, 2030, 30354472318141713109105873322367)))))
(.branch 4996
(.branch 4994
(.leaf (2032, 2028, 217442421162962212208320471078825891923326))
(.branch 4995
(.leaf (2032, 2028, 15286152296685286165723448068213244287))
(.leaf (2032, 2028, 1988720685715472712777115978795254656))))
(.branch 4998
(.branch 4997
(.leaf (2030, 2028, 4662712924125446689462183855946531199))
(.leaf (2030, 2028, 1988700324077871792775775498486612096)))
(.branch 4999
(.leaf (2030, 2028, 13962116602082023851318309313883210111))
(.leaf (2030, 2020, 157561085022402160488936113726871806659869989386757376978148330882)))))))))

def rowDataBlock50 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 5050
(.branch 5025
(.branch 5012
(.branch 5006
(.branch 5003
(.branch 5001
(.leaf (2030, 2020, 7101177321359873785764695233438635428103369763585151899591168426367))
(.branch 5002
(.leaf (2030, 2009, 15091352560722603811510454336159594294946310422981837154666527859832610080242742868069597798397205906268748843531108735))
(.leaf (2022, 2007, 2052764867791943392887047659030787818845596981100479559791295145908629423840481044867098518782972729663578544539430383596926338177))))
(.branch 5004
(.leaf (2022, 2007, 64852629861527419402230229964287326064432506249276389696749430685919826026011370694546777056201396074144680164319239171680895359))
(.branch 5005
(.leaf (2011, 2005, 464454192706495559133938947030698311772863109635847189769162083665560309239268893957677098096593209443906568233878104876568747259212005504))
(.leaf (2009, 2005, 818178987490831045779473388876807167388239093044607113065027057439383843821804645518847554290188671)))))
(.branch 5009
(.branch 5007
(.leaf (2009, 2004, 161402423587114805088677741699081971929599819262805168343506628443442504528060991756575970610966199206271))
(.branch 5008
(.leaf (2007, 2002, 4011104694336535497119073241639283198561305589724749357857937))
(.leaf (2007, 2002, 559769377404249153563549025577828272507273193980287))))
(.branch 5010
(.leaf (2006, 2000, 4023658898549751690323390934553438831041739203420926857117824))
(.branch 5011
(.leaf (2004, 2000, 559780839987282522339543319079159727726991704588671))
(.leaf (2004, 1993, 10654369055303220059978707174141265820187474553256699118701922475975716448080862183807))))))
(.branch 5018
(.branch 5015
(.branch 5013
(.leaf (2002, 1993, 73991821769959327771618986043185921370405436882497003795786828042843866974323582))
(.branch 5014
(.leaf (2002, 1993, 10325922445275918464838163688600377455879344953430692206530506419929471))
(.leaf (1995, 1993, 17281483459626383482393730274796902617176858918178092352180816367780479))))
(.branch 5016
(.leaf (1995, 1993, 2404215593401407695766111701900244357820737744371791616278911))
(.branch 5017
(.leaf (1995, 1992, 369418177309971571943571498745945139482298160614000245171407618431))
(.leaf (1995, 1992, 91350534409360164407238499187863)))))
(.branch 5021
(.branch 5019
(.leaf (1995, 1992, 30351974677398101336329721741695))
(.branch 5020
(.leaf (1994, 1982, 73991821763084541360240729482879465161273944464345887680246917136650911707234945))
(.leaf (1994, 1982, 44354948159840195217362595204122619269475686190866192143493724770235075849355647))))
(.branch 5023
(.branch 5022
(.leaf (1994, 1982, 74223405934576547559462487409827416878188404999362516842427687002039004807758463))
(.leaf (1984, 1982, 4751062083217244406048920186986335616639332995217440696424180560220624257407)))
(.branch 5024
(.leaf (1984, 1974, 230275765391886529896946976184564908114942452194700965574788545100561437196904196158348295181031648875120387097217))
(.leaf (1984, 1974, 385389959652227686801686216677250957758589217508259653178944165433958721069473703497544291936201851112311719068031)))))))
(.branch 5037
(.branch 5031
(.branch 5028
(.branch 5026
(.leaf (1984, 1974, 157562685683344684092530717968884861822684129440229208758452945792))
(.branch 5027
(.leaf (1976, 1974, 262871757444581743449559140026897637316681520233761775966262002047))
(.leaf (1976, 1974, 157561085022402907316272877951395857694229139988525705624381489791))))
(.branch 5029
(.leaf (1976, 1974, 369418177383244014991221809784879571018998355262135162145309655423))
(.branch 5030
(.leaf (1976, 1974, 463030376489724467059034237))
(.leaf (1976, 1974, 3245972890804290006877667711)))))
(.branch 5034
(.branch 5032
(.leaf (1976, 1974, 463030413383162977541096320))
(.branch 5033
(.leaf (1976, 1974, 772510664376598924178162047))
(.leaf (1976, 1974, 463106081927352238905164417))))
(.branch 5035
(.leaf (1976, 1974, 2634256426223684307495420287))
(.branch 5036
(.leaf (1976, 1974, 463044635822861408381370496))
(.leaf (1976, 1974, 154749570193516920270094719))))))
(.branch 5043
(.branch 5040
(.branch 5038
(.leaf (1976, 1971, 130347425559300332492936105499251846283647))
(.branch 5039
(.leaf (1976, 1946, 563248054002050676428398826354455348569148747113915721398121777924982346749988969442578465868809816400061228092786174460548152836628741867363565835465607480344959))
(.leaf (1976, 1946, 336548408157867431265395704585000218038315603966834633132188786470841986909034438266323549180118386992041891603381316381559250630876792107804985138961509584405890))))
(.branch 5041
(.leaf (1973, 1946, 1909407415753116546280932138421727841697106346516812372200194975943470749055527056273837444746894594851112441433819662873010918290511765965403150360749432415191423))
(.branch 5042
(.leaf (1948, 1946, 336548434973528010198569658788145543276479318925495974262708815853351565937924681409124025159923570481914696236316032709201056212029231416378179794166030394130560))
(.leaf (1948, 1946, 561490665695081219374381046405870605917917700242298555076946488857986154484505831398219713322918417346770436474071669627272310675695854345175962699374071172170111)))))
(.branch 5046
(.branch 5044
(.leaf (1948, 1945, 130732233063080675278899024176726510348212702404922282093582581160448192545465035756270337811740824958870448253434775663805832757917940260510028399575423))
(.branch 5045
(.leaf (1948, 1945, 172797085738402639517815563818119))
(.leaf (1948, 1945, 30345158753627114057042728321407))))
(.branch 5048
(.branch 5047
(.leaf (1947, 1934, 12634980701593563991689128728352198377029159612283243910474529153083091061900627149183))
(.leaf (1947, 1934, 2906636877882220552818738837235777935054100702142595691796477162150431611601270276735)))
(.branch 5049
(.leaf (1947, 1934, 4849128029706803109453399271735360672272139653594193468582773543984238618052994466175))
(.leaf (1936, 1926, 35304427827734845264025608885205194611346281098323521849374705538931146197169225530880075095744541192580110869961048960))))))))
(.branch 5075
(.branch 5062
(.branch 5056
(.branch 5053
(.branch 5051
(.leaf (1936, 1926, 15091817309117725322658456306541156877218029895834265909239039979729246962041366167596371194045763101050062686816108927))
(.branch 5052
(.leaf (1936, 1910, 584019063169740988634389728728748070854671126498895911265166967965448487732195336264601909117770583550809646151074811271261664562260859056603193871571923093348347118402727987322313916501546971010))
(.leaf (1928, 1910, 30438470007261276803907896214216414192204071583051274382812252211243457434197959398715518526080002690733600482205753630826771335059279446081919))))
(.branch 5054
(.leaf (1928, 1910, 18251380460223006251416952447162751003156757784002106259659922107219164005696730195702117379377598352815169969974609084826499912669255396430457))
(.branch 5055
(.leaf (1912, 1910, 42585166142421177632761546775077658804110634301168222413386571244287485009203362498710110207773172643555587594930475059831990566396136234418559))
(.leaf (1912, 1897, 22056036477034209267820734372757948454344688395514531111792622481811584460056969023169612831951230213996958141649890503094115728902917266280645783642372060254111465855)))))
(.branch 5059
(.branch 5057
(.leaf (1912, 1897, 154964522422108639657794277953181446465133050749261265181806207868040033820373206043084739150962981777828519741494038340852232338388192728854237077547272134528321127039))
(.branch 5058
(.leaf (1912, 1897, 190479648672977084356082420240897355100792669277390744811113160105537864062871164914893183))
(.leaf (1899, 1884, 287650395365732600954718096915394118620090696430223462572675367041614132254867335713739139963251809220471029839335065056116172025175236638654180515447167))))
(.branch 5060
(.leaf (1899, 1883, 5135373339063891114573044897796134849901656904004829876016070650791917244169128841675496972184768800318965171778800846216218553169216702648071546774528983423))
(.branch 5061
(.leaf (1899, 1878, 10357674607944345530551245674600827876385887685083225383734052915808000302023642232986237391496743208955808118160177215866514084408702149495450829068692312088513308784699730882068863))
(.leaf (1886, 1878, 25178112249426111555530885225786672367281545543555241474717845831091886970850958317915531930252236963281789067884167809))))))
(.branch 5068
(.branch 5065
(.branch 5063
(.leaf (1885, 1878, 15091353763176477723560778695487635130954919583624716408384357433867492554104912021025727208835940069934065291586634111))
(.branch 5064
(.leaf (1880, 1878, 35383231851861173147825456584077573147858687867682607603769096280434422057642794845503426481849217957281394133380825216))
(.leaf (1880, 1878, 85628748115303545721549374495640311338986769732522148223))))
(.branch 5066
(.leaf (1880, 1877, 12260524102080408123753422267562531317833853310678860159))
(.branch 5067
(.leaf (1880, 1877, 50785715239761968447101536764543))
(.leaf (1880, 1877, 30348561879809329238169576538495)))))
(.branch 5071
(.branch 5069
(.leaf (1879, 1874, 42817561112643235188945011889921642041394200959))
(.branch 5070
(.leaf (1879, 1871, 2404191360815479825518750892976660412888076853751588413571455))
(.leaf (1879, 1856, 15637921892370734736128089908386487405545797520648456934259729475809262750632453090428422864898660069941468591653205376358410855907711))))
(.branch 5073
(.branch 5072
(.leaf (1876, 1822, 6227312608060700286212339082923671518130074021107296278170142311478424480045929833851614532487646245943737080990810468190189103483933502814767739944528659968540568632755476433486005925382228598866838968983862263962933330905821515755181782880139416812147289066800068334099544453957412431266431))
(.leaf (1873, 1822, 3732550585019085159605675383532419956706754019352374010416093275468879583136967831968347938337486366275832595799840376548949150084454825019351671737692135478222308982496684865644530635857887634233062321553217977800818543871204436713660989242939092934829697461760469113405364785354813430694271)))
(.branch 5074
(.leaf (1858, 1819, 5261209013644422477693054954628194395944337588889386735057353457849602614346644457987491824118029495101099084331204846906568532579012664570868347321863292724150940889889219756808978966604141864217439631221569948686316203307508418514512217312536020688006396856999334195220826396940128963791827612010397696383))
(.leaf (1824, 1819, 8751348936439241092160728342157407145374808873492467987175273482143069282584772946977223905073671544628788166426255504806480629425393528336582608372494803321055868028967826448989099977342716252630028785926825060967976768271299717061537601704401987733026806308975387792338904066321490884104068)))))))
(.branch 5087
(.branch 5081
(.branch 5078
(.branch 5076
(.leaf (1824, 1819, 66475038305912331746748554594166167734110556864266921293989077751207891770084064109213208304848686100558294824440078147884906555445485161192250556879111108986089559813796278370697071543378318763966442844634792922726802542408286233266647667570349559192928474758020153866878648703))
(.branch 5077
(.leaf (1821, 1819, 52692503413255256281781381179184047977384100768287498284201639091685827832504249386647530169288249379619829739891310326337675000831169390693953396961802916489631055713097709483585239233107398728070096420992))
(.leaf (1821, 1819, 130331474823350911084609837602477293633919))))
(.branch 5079
(.leaf (1821, 1819, 1528550381538647406863471102580674042724993))
(.branch 5080
(.leaf (1821, 1819, 1083204599658115076414439807))
(.leaf (1821, 1819, 463020950203456475960906867)))))
(.branch 5084
(.branch 5082
(.leaf (1821, 1819, 10683284533217322402953298303))
(.branch 5083
(.leaf (1821, 1819, 463039858116127630204797567))
(.leaf (1821, 1819, 774928515511987973794955647))))
(.branch 5085
(.leaf (1821, 1819, 463030376489685790878532994))
(.branch 5086
(.leaf (1821, 1819, 1083204601607892240055599487))
(.leaf (1821, 1819, 463030413383166263191091582))))))
(.branch 5093
(.branch 5090
(.branch 5088
(.leaf (1821, 1819, 772510663872758715462517119))
(.branch 5089
(.leaf (1821, 1819, 463020950203452069324456577))
(.leaf (1821, 1819, 1085622451297344334814249343))))
(.branch 5091
(.leaf (1821, 1819, 463347051745190401017846138))
(.branch 5092
(.leaf (1821, 1819, 1083204599657552126393975167))
(.leaf (1821, 1819, 463049302849093369495224959)))))
(.branch 5096
(.branch 5094
(.leaf (1821, 1819, 774928515727597805905117567))
(.branch 5095
(.leaf (1821, 1819, 463030376489674838711928963))
(.leaf (1821, 1819, 154749570338195058282398079))))
(.branch 5098
(.branch 5097
(.leaf (1821, 1819, 463030413383171765044184444))
(.leaf (1821, 1819, 772510664303696904739357055)))
(.branch 5099
(.leaf (1821, 1819, 463035080409412530840994433))
(.leaf (1821, 1819, 3253226445866374445079003519)))))))))

def rowDataBlock51 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 5150
(.branch 5125
(.branch 5112
(.branch 5106
(.branch 5103
(.branch 5101
(.leaf (1821, 1819, 463068192315025943292740735))
(.branch 5102
(.leaf (1821, 1819, 154749570193516920303649151))
(.leaf (1821, 1819, 463272121070759707169194623))))
(.branch 5104
(.leaf (1821, 1819, 774928515511987973862195583))
(.branch 5105
(.leaf (1821, 1819, 463030376489674847301862270))
(.leaf (1821, 1819, 154749570337632108328976767)))))
(.branch 5109
(.branch 5107
(.leaf (1821, 1819, 463030413383162986131034249))
(.branch 5108
(.leaf (1821, 1819, 772510665101115513844400511))
(.leaf (1821, 1800, 15091965812161889246690624140954985037449649076941590651967976742156987159396777253220937286273936101178995441550688639))))
(.branch 5110
(.leaf (1821, 1800, 35304427827753193250200242167868216012141898894825280748725256286553372978955439980393898139644878071039642215550747520))
(.branch 5111
(.leaf (1821, 1800, 15101982853562545992707829976214824271506553529795852531119930271421404787762479764289126201582688150353927918023541119))
(.leaf (1802, 1799, 3640987419455101834233813022274038219377713608116817070647070056965835361078563306602589089018626005958025353286445902594431))))))
(.branch 5118
(.branch 5115
(.branch 5113
(.leaf (1802, 1791, 336627313107536744906329300041280900346757791563493753422580067948789749130153890028985069948481830127495797972066900965546320309990487250834238487438763484971649))
(.branch 5114
(.leaf (1802, 1791, 563248054420226326526302201194555365495135180294686706322058311638593776552781155800507299732099767699921872923236260675125031481555038304370085531082328102666623))
(.leaf (1801, 1791, 161975517137313512085049142220446544410849336180352559346636684775065735))))
(.branch 5116
(.leaf (1793, 1791, 10326870667277587525359357829213801090802119556522774649118134093807999))
(.branch 5117
(.leaf (1793, 1781, 55635863025092744548426101008133567298695475783112544060710223704126893717545976320133316190875244665830090015126783103))
(.leaf (1793, 1781, 384187503661476887093474834577912307334977938180640903098774355176561066272007064271682321030785735925431707763071)))))
(.branch 5121
(.branch 5119
(.leaf (1793, 1781, 676836740421974807587072627802742266100795684136227082146264248271851422335))
(.branch 5120
(.leaf (1783, 1781, 1579571602045768202181707780501988088608351494055565071006734424429635371391))
(.leaf (1783, 1766, 1195660133241046359967322998998726681077652995379548785099196403230906678214490459831914890103791468062319834431608336661501731434297790043191509375))))
(.branch 5123
(.branch 5122
(.leaf (1783, 1749, 3032400348427190513290225831486848992059698450690843067566794537410189437336413373136432837767572051376780847600487321390196086380328389460567794049096704739283672663027056937618433263865807026377808346562023818472544233922363775))
(.leaf (1783, 1749, 6208412056120454224062871521318705639890610320146219123094642530226172581818349913411108181813637345057535818617684180142508858108977074693712852216920428300767136487663538379096703)))
(.branch 5124
(.leaf (1768, 1749, 10357674606974437191869265953573460284211146612014926469145415884186285110145708035756015256833338154935303509531154512988960227727945479627489659130856392972876359602769784639193471))
(.leaf (1751, 1749, 6208285917615732367245916875673415294462043758638057168848484899993479783895946279287974993162274507258158405510403448349469076464936485822617701625444138886554398145065976659379072)))))))
(.branch 5137
(.branch 5131
(.branch 5128
(.branch 5126
(.leaf (1751, 1749, 2074852575318920149263346410326021724032401603536867876294038714227415405189237124294575836040080036141213943790971072369963106174834145147400254949018139931579190667306754990080383))
(.branch 5127
(.leaf (1751, 1749, 27008293323694148505134860729318686156876939793619776905117834280179405428896020940465340342527675204020142978))
(.leaf (1751, 1749, 772510664088931497777627519))))
(.branch 5129
(.leaf (1751, 1748, 30356283289019351708421507318143))
(.branch 5130
(.leaf (1751, 1748, 91350534409360164410549918958207))
(.leaf (1751, 1748, 30362155041725076128609972781439)))))
(.branch 5134
(.branch 5132
(.leaf (1750, 1746, 1789546956337539457083971948276169001862273))
(.branch 5133
(.leaf (1750, 1746, 130332809243643556953161792152085142110591))
(.leaf (1750, 1740, 17281483376329243453065649201497552146663232258968539350130692559143808))))
(.branch 5135
(.leaf (1748, 1740, 262871757272271776119078086184783700715745517484472843847782629759))
(.branch 5136
(.leaf (1748, 1724, 18245446548877856916762487554365956107345606696059768806417605107444266614864125660915476109830859993718702456954161323790028422701172849049728))
(.leaf (1742, 1724, 30533738198324991077590921843576288271938109682150419843208309479241346501483763868116168147984048528925028911776242368012822664579232007455103))))))
(.branch 5143
(.branch 5140
(.branch 5138
(.leaf (1742, 1724, 4247967910223328190964153969278256551568931952368485010892828878565354921364370472729444349193418762192758268889439820030183210943103))
(.branch 5139
(.leaf (1726, 1724, 7087008555043667991809828700534978539597763099576977206974128917174945485594851236791368950300719182096635789386508047741123372777855))
(.leaf (1726, 1724, 53634948474551607792799895058365930441309106074513337976011218605531543332785076416416882606588215377519))))
(.branch 5141
(.leaf (1726, 1724, 89450623752898766454802004900442657400389357767014159450904894952475224663521641721733340165535956926847))
(.branch 5142
(.leaf (1726, 1724, 463030413383159687596152722))
(.leaf (1726, 1724, 772510666174379600008708479)))))
(.branch 5146
(.branch 5144
(.leaf (1726, 1721, 130332788474456120395999639363791914271103))
(.branch 5145
(.leaf (1726, 1721, 480480690792847644441860316723281802496125))
(.leaf (1726, 1721, 130332798859049219704561217464463838413183))))
(.branch 5148
(.branch 5147
(.leaf (1723, 1720, 31354978080598494909723095924477209883162247551))
(.leaf (1723, 1720, 8541839435735151189468997706077055411233423488)))
(.branch 5149
(.leaf (1723, 1720, 14294908015690812450151881986391044026443694463))
(.leaf (1722, 1720, 91192078088998661982708517767817))))))))
(.branch 5175
(.branch 5162
(.branch 5156
(.branch 5153
(.branch 5151
(.leaf (1722, 1720, 30345158753629850275291399782783))
(.branch 5152
(.leaf (1722, 1720, 10141667846424764566538595273084))
(.leaf (1722, 1720, 1697338916094685766146392447))))
(.branch 5154
(.leaf (1722, 1693, 5135321578574952724687223197595852155204624734349354629212132258771300085402982367663634272718347361335608127903640688007908115737488840178966859795761529215))
(.branch 5155
(.leaf (1722, 1691, 51597479075265168568222716284473302705048019298015874949264713600298896671781148375899839356299233027319723633103378826560403081134513760158782206045524283292483782014))
(.leaf (1722, 1691, 22058973951411960503828209386502258822367044260447788789809308969011968548625284964212635675662588714569860105354960703430198953313407785659518503759465911661688127871)))))
(.branch 5159
(.branch 5157
(.leaf (1695, 1688, 22790012268426474685969981730551300145157102295080938710655985651078798979628932326031400150889559509178936248630140374944083562769385096080431240891057756180695921335606759502250367))
(.branch 5158
(.leaf (1693, 1684, 114521488911434020743239273823899282094366753539202784744513232555762110918443973543108080493195588932844096260030209800409898805346532548447731505656582097078704239588334523981091212022147277276512895))
(.leaf (1693, 1684, 1261500080482289381059836883943737642039021648344650446241364788689848172923783855256876445202236859993967880872621864284798538134656448962575870151569268439853173618648487005829901901741603034628948351))))
(.branch 5160
(.leaf (1690, 1683, 1129025601158331195993153297031165026362448123153759678040417523896784126335))
(.branch 5161
(.leaf (1686, 1683, 157561072468200933120588583167300575784291476641580190625041417088))
(.leaf (1686, 1683, 52658550074679266130717083055099901994559138610688200956395651455))))))
(.branch 5168
(.branch 5165
(.branch 5163
(.leaf (1685, 1676, 8734465814158261251502536292307877256024643018247971987016461010314447058322667667839))
(.branch 5164
(.leaf (1685, 1676, 157583582155022533180130377968120987654169342041234645771725243007))
(.leaf (1685, 1676, 52658550025639408811612958789859613003357439563073995155257229695))))
(.branch 5166
(.leaf (1678, 1631, 39850481611986647446760400458459838343719311920401363820337105407316069993451993116806619492418385193288622854325191538755573497675610917443349650582664997953024829347449232378967344470685432376200688122828842962007517709338332095864179278391076092491811289193049005750717907327))
(.branch 5167
(.leaf (1678, 1622, 295723100779904318384159483338108753831955715248539931695415595975006949773528823818136334792056642455547896715765145700187747970712807307829822874024967927088847310209968403271482441852481671559685520769829513108309066792316700047213159029737101692546560794890141170201995187140430186115171063522799995921231913794208127))
(.leaf (1678, 1622, 98833737624485510128572194896711400995535439922366007659832541556308254322568775385708503750879839032880592221600806300592873584893085480427495681336847238560148450633376219112187667275436048989451630128073998257740103342190111682317203153924905355672105728221264054442723349005486880390403838319996379351986890317170046)))))
(.branch 5171
(.branch 5169
(.leaf (1633, 1622, 95021249503885518352559625558224606940630503723377802287209199216244997568679083395507037835142683757874711420472638366381302591664711232796146204258656448155589772272640734331834018187596290264784006716694968709070666280921696896784147451960861854412052137472312843533720857222827737471))
(.branch 5170
(.leaf (1624, 1601, 7972760654865161540516456494958786190737659740749330686527608580852371294109066178524924072161197138002885627225783092453126490087374953147181515570055775736870850189002806906240219836702738174175157641669945410829155879007170842763842450609562426562780770634210348749092900609425412373635494011467433445766200998008270094146353490258917082126568457307079342376229146690307954169945850239))
(.leaf (1624, 1599, 11444164987945734782570950513096932939980455805757715901133831269880270159567248164670729573338668514205104177221458916700091462335275440527139330190706164906132575147305181601344630426596819941477131452450325960854193413407962118899194459404156897081777093117907848295128425878001372016338315451633184104503263744916832393389527223872726509863582980109122291441611624497403885723414440939846828160))))
(.branch 5173
(.branch 5172
(.leaf (1624, 1599, 14555817356998850561385547751395471805675342177040961662379822766853055294721109597916442219185209780510990713659199384755907967473384188943324206680998862737146716003936623889744255))
(.leaf (1603, 1581, 507511309830198881883098015603891620653636850168612753627410554929565423943262233297834806234390816152735258274822075365118063787135906576263846064160975589470861475545348781411666251530858350342621218254661405598795104715393)))
(.branch 5174
(.leaf (1601, 1581, 138447984845742712732962565556590461889591393783841947211582933029898804157502076293570576602353339452106252349252403879029769479077542846681001404801299933496437433080337121106751463504127343538083990141791321385139355910527))
(.leaf (1601, 1581, 231706809854150073052613393901783656356457311768161640812435043813491050914092272488289588458344464038932070164601590427733745605108096014794027869348194684646457125539473054076197551061795859554118721446440968048500973443478)))))))
(.branch 5187
(.branch 5181
(.branch 5178
(.branch 5176
(.leaf (1583, 1581, 3640987419610819601534401528945036440830532686074379093636238173419240430318148043091087331438741679418464940695492679958911))
(.branch 5177
(.leaf (1583, 1581, 230275783739877091847603341914935566886892275923228631725940765368191137499020583663156355194206882442916403282048))
(.leaf (1583, 1581, 384187505954415566856120435402464426675686950372208463382122018233123560138652667600724061940897240120972409569663))))
(.branch 5179
(.leaf (1583, 1581, 463143565711318812807070335))
(.branch 5180
(.leaf (1583, 1581, 4486330782451445805342589311))
(.leaf (1583, 1580, 30345158753627114057042728321407)))))
(.branch 5184
(.branch 5182
(.leaf (1583, 1578, 3619925808025629089805518137199002222789249))
(.branch 5183
(.leaf (1583, 1578, 130332788474455502634905816288283087274367))
(.leaf (1582, 1578, 217442421162962212184671745179620191700862))))
(.branch 5185
(.leaf (1580, 1578, 130334133279342480916355500538459792277887))
(.branch 5186
(.leaf (1580, 1578, 564530435503290627200582810553480759937655))
(.leaf (1580, 1578, 5976364029334758079408623308077269375))))))
(.branch 5193
(.branch 5190
(.branch 5188
(.leaf (1580, 1578, 463054006768829962112664448))
(.branch 5189
(.leaf (1580, 1578, 4794606865874463692775555455))
(.leaf (1580, 1578, 463030413383164081347691135))))
(.branch 5191
(.leaf (1580, 1578, 1704592471011810591207588223))
(.branch 5192
(.leaf (1580, 1576, 1988700324077720750835291202944696448))
(.leaf (1580, 1576, 7300399728261139124610997853060333951)))))
(.branch 5196
(.branch 5194
(.leaf (1580, 1575, 130332788474455502634905888064402148491647))
(.branch 5195
(.leaf (1578, 1575, 217442421244091850618186339549874860525440))
(.leaf (1578, 1575, 130354149583732132676863269429026771304831))))
(.branch 5198
(.branch 5197
(.leaf (1577, 1572, 61396162381048368154491631764870730887640458109743333759))
(.leaf (1577, 1572, 8541665211163328075338586769983713395471225991)))
(.branch 5199
(.leaf (1577, 1572, 14250306513335891537734647492666923735720984959))
(.leaf (1574, 1568, 42590171959644546547672583749076477395110859706059393186333311)))))))))

def rowDataBlock52 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 5250
(.branch 5225
(.branch 5212
(.branch 5206
(.branch 5203
(.branch 5201
(.leaf (1574, 1568, 2404461942059425421603336833363937314749679142027740842164607))
(.branch 5202
(.leaf (1574, 1567, 52658550025639408845889204157347917075324795867893029424746004863))
(.leaf (1570, 1538, 151139606403240451049865043729903921450913224008071041088250680133642400864109147446339811063659239793841106806965837003648217259929619943669445821602793403290810190059672168490895683585245567))))
(.branch 5204
(.leaf (1570, 1538, 26664111975448613488781743988819440251397128771565567400234408269162095227750805624226424921809243728944980315352173141715146918200102179484022455682072305333726649303976588318198057588950398))
(.branch 5205
(.leaf (1569, 1538, 44625108474730969271085389732073557209448177845716445939724259604270613825177367640745442997436405619076290400698855772443989404975749346943233724203352642753112561297940597883576125489217919))
(.leaf (1540, 1538, 1445479206185725603077068396223614466797789223548312385038102224881298836272431383626455596215602936022863797642508810205232266089632983974816065134633586029194220643745920)))))
(.branch 5209
(.branch 5207
(.leaf (1540, 1538, 2419131972148407946961797459707530143512283423034542504436797070976146530141218127395155770597793374010977104515991186248106973100343773599114897376841940721311342743519615))
(.branch 5208
(.leaf (1540, 1538, 566820285115882478061598459075418833892094525929881345010434660567569925560502842593002396267245479110503279081247109995037201998920058377988136305403348920021129560958))
(.leaf (1540, 1538, 18421618704570563750063571327))))
(.branch 5210
(.leaf (1540, 1538, 463030413383162994720965247))
(.branch 5211
(.leaf (1540, 1538, 2636674278078241923564372351))
(.leaf (1540, 1538, 463030376489681452961563265))))))
(.branch 5218
(.branch 5215
(.branch 5213
(.leaf (1540, 1538, 14062232199040773896026390911))
(.branch 5214
(.leaf (1540, 1538, 463020950203454268347719050))
(.leaf (1540, 1538, 772510664807255638125052287))))
(.branch 5216
(.leaf (1540, 1538, 463049265955605213486193797))
(.branch 5217
(.leaf (1540, 1538, 774928517317931424320323967))
(.leaf (1540, 1535, 130332798859050145741739042270411646632319)))))
(.branch 5221
(.branch 5219
(.leaf (1540, 1535, 391666993026324249162354195224830461019006))
(.branch 5220
(.leaf (1540, 1535, 130331474823350293323515797509761807679871))
(.leaf (1537, 1534, 20026199567524454030841267736796231136347881855))))
(.branch 5223
(.branch 5222
(.leaf (1537, 1534, 8541402853458960325170901622764455058512740480))
(.leaf (1537, 1534, 2854625716886743113027656548375741829816058239)))
(.branch 5224
(.leaf (1536, 1534, 172797085488246343134231744414337))
(.leaf (1536, 1534, 30356916766148830337059124412799)))))))
(.branch 5237
(.branch 5231
(.branch 5228
(.branch 5226
(.leaf (1536, 1534, 50627258895991547789735599472768))
(.branch 5227
(.leaf (1536, 1534, 1083204599657552126696423807))
(.leaf (1536, 1534, 463073006915228086269051519))))
(.branch 5229
(.leaf (1536, 1534, 774928515727597805905117567))
(.branch 5230
(.leaf (1536, 1533, 30345158753627330229824976126335))
(.leaf (1536, 1527, 20130701951182214616081308156300032183776393493397103192245118)))))
(.branch 5234
(.branch 5232
(.leaf (1536, 1527, 2404191360815462653944954665344524114190637266679672059527551))
(.branch 5233
(.leaf (1535, 1527, 4011104695087747338445820483780493281196465957233946991199104))
(.leaf (1529, 1527, 2404215593401213991493317275292229144589650069206224011788671))))
(.branch 5235
(.leaf (1529, 1527, 7224980782478910127409635941036538459331435795844634481984129))
(.branch 5236
(.leaf (1529, 1527, 12260524102035806634701165905172562639244496991409799551))
(.leaf (1529, 1527, 463101451794599637707326079))))))
(.branch 5243
(.branch 5240
(.branch 5238
(.leaf (1529, 1527, 5107718653660463182139883903))
(.branch 5239
(.leaf (1529, 1527, 463030376489673743495267200))
(.leaf (1529, 1527, 774928516159380420212752767))))
(.branch 5241
(.leaf (1529, 1527, 463039858116128716831524481))
(.branch 5242
(.leaf (1529, 1527, 772510664088931497542746495))
(.leaf (1529, 1527, 463030413383161882324435072)))))
(.branch 5246
(.branch 5244
(.leaf (1529, 1527, 154749570768288822713254271))
(.branch 5245
(.leaf (1529, 1521, 36686542495246199352580942159642170407466247462055773056))
(.leaf (1529, 1521, 110244457740417283999965608806220776471371209661426434431))))
(.branch 5248
(.branch 5247
(.leaf (1529, 1500, 5135999375017626815411027262771919379515561540769422704397744279235021041136770746868373785769947801973346868937442549039380705878002870809595690863934177663))
(.leaf (1523, 1500, 18851456309084072991539147591874977393765953517401605468157539768189960823397318000138169975967541622860736700628205625451464104921435559833839751919726166912)))
(.branch 5249
(.leaf (1523, 1500, 5135321169401077769811988756643613200690185795758063489546542811321021183953759536338117309239187352767725671788267694804301743647982887779991033684328120703))
(.leaf (1502, 1500, 8594483245880900212756064098417651034904389164900753855392030611513927082761190412937993999454913859529447942893739762048462379136459972512763680804583713132))))))))
(.branch 5275
(.branch 5262
(.branch 5256
(.branch 5253
(.branch 5251
(.leaf (1502, 1500, 64816865700711132958263741517522503777887714550661122229315924482846567533181756102140442579219088297005873849344107949615677823))
(.branch 5252
(.leaf (1502, 1497, 42585166187915141973227074272308542465728792124320907425609534633143537488217803037131682383634557114498635321105720526923602759671009719157119))
(.leaf (1502, 1497, 565891565337642316986224030301991942946944))))
(.branch 5254
(.leaf (1502, 1497, 130331474823350293323515869848830906335615))
(.branch 5255
(.leaf (1499, 1497, 305575554195326817962788817330219868160641))
(.leaf (1499, 1497, 130334122894750009040294374206448016294271)))))
(.branch 5259
(.branch 5257
(.leaf (1499, 1497, 479800126059005767529063773466685054321279))
(.branch 5258
(.leaf (1499, 1497, 2323562491229272631200907647))
(.leaf (1499, 1496, 30345158753627258453705780887935))))
(.branch 5260
(.leaf (1499, 1496, 50785715206760743298139932268165))
(.branch 5261
(.leaf (1499, 1496, 30348576386919164613719908680063))
(.leaf (1498, 1496, 50627258928734518522773371824253))))))
(.branch 5268
(.branch 5265
(.branch 5263
(.leaf (1498, 1496, 30345161171478897120014227210623))
(.branch 5264
(.leaf (1498, 1496, 91192078103221101664642388656767))
(.leaf (1498, 1496, 5731524377224219208152318335))))
(.branch 5266
(.leaf (1498, 1496, 463030376489683617625084537))
(.branch 5267
(.leaf (1498, 1496, 2017704258794432380918497663))
(.leaf (1498, 1496, 463020950203453164541117057)))))
(.branch 5271
(.branch 5269
(.leaf (1498, 1496, 772510664017155378498240895))
(.branch 5270
(.leaf (1498, 1496, 463039858116127621614863999))
(.leaf (1498, 1496, 154749570410534127263547775))))
(.branch 5273
(.branch 5272
(.leaf (1498, 1496, 463035117302900686850031744))
(.leaf (1498, 1496, 774928515655821686843900287)))
(.branch 5274
(.leaf (1498, 1496, 463101414901120312151048831))
(.leaf (1498, 1496, 1085622451656787879989936511)))))))
(.branch 5287
(.branch 5281
(.branch 5278
(.branch 5276
(.leaf (1498, 1495, 30345158753627689110420382482815))
(.branch 5277
(.leaf (1498, 1494, 8634820026470484298649088130017132927))
(.leaf (1498, 1494, 1988720685715472712777115987385188991))))
(.branch 5279
(.leaf (1497, 1494, 3317908037764926333384273455499575679))
(.branch 5280
(.leaf (1496, 1493, 130332809243643554535310368814133896348031))
(.leaf (1496, 1493, 654024698349803741261776038604075050144650)))))
(.branch 5284
(.branch 5282
(.leaf (1496, 1493, 664644343053629415205189831318503807))
(.branch 5283
(.leaf (1495, 1493, 50627258895917760818955499275391))
(.leaf (1495, 1493, 30348576386919308447432755446143))))
(.branch 5285
(.leaf (1495, 1493, 71147352968222758383458170372735))
(.branch 5286
(.leaf (1495, 1493, 2321144638799098688428769663))
(.leaf (1495, 1493, 463030376489682565358092929))))))
(.branch 5293
(.branch 5290
(.branch 5288
(.leaf (1495, 1493, 154749570194079870206542207))
(.branch 5289
(.leaf (1495, 1493, 463035080409418024104166274))
(.leaf (1495, 1493, 772510664377724823664591231))))
(.branch 5291
(.leaf (1495, 1493, 463082156500288637616720007))
(.branch 5292
(.leaf (1495, 1493, 774928516304621508246110591))
(.leaf (1495, 1490, 130332798859049219704561217464463821701503)))))
(.branch 5296
(.branch 5294
(.leaf (1495, 1489, 19936996538950815845729364941823290741441036671))
(.branch 5295
(.leaf (1495, 1489, 8541403534023084823249931305599795951761817728))
(.leaf (1492, 1489, 25712889553376768995556096261418236418310734207))))
(.branch 5298
(.branch 5297
(.leaf (1491, 1489, 8541402853458452234964697645567467661159235712))
(.leaf (1491, 1489, 2854625716886743113027656549025386076064252287)))
(.branch 5299
(.leaf (1491, 1488, 664644345213979855000365879550607743))
(.leaf (1491, 1482, 5611765636484533170841820636743045573668298141243282370265729)))))))))

def rowDataBlock53 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 5350
(.branch 5325
(.branch 5312
(.branch 5306
(.branch 5303
(.branch 5301
(.leaf (1491, 1482, 2404265207944338128964311491279911162289837600201086688756095))
(.branch 5302
(.leaf (1490, 1482, 5624319839952383529094830409753211993032318218567274805002879))
(.leaf (1484, 1482, 2405047738479904213744896244404623709508116690095162611728767))))
(.branch 5304
(.leaf (1484, 1482, 4023658898177068772892143823606043853087197913333954984740481))
(.branch 5305
(.leaf (1484, 1482, 61204600438440132056444319091529888097740158940160655743))
(.leaf (1484, 1482, 463049192168632230067765376)))))
(.branch 5309
(.branch 5307
(.leaf (1484, 1482, 772510664088368547589325183))
(.branch 5308
(.leaf (1484, 1482, 463030413383161882324435840))
(.leaf (1484, 1482, 154749572356933591301882239))))
(.branch 5310
(.leaf (1484, 1482, 463049376636072949983412865))
(.branch 5311
(.leaf (1484, 1482, 2944950361864081055542083967))
(.leaf (1484, 1482, 463035080409427906823914111))))))
(.branch 5318
(.branch 5315
(.branch 5313
(.leaf (1484, 1482, 4474241524468939020935758207))
(.branch 5314
(.leaf (1484, 1482, 463030376489673743495267200))
(.leaf (1484, 1482, 774928515799936874953245055))))
(.branch 5316
(.leaf (1484, 1482, 463039858116132028251308160))
(.branch 5317
(.leaf (1484, 1482, 772510664088931497542746495))
(.leaf (1484, 1482, 463030413383161882324435838)))))
(.branch 5321
(.branch 5319
(.leaf (1484, 1482, 1085622454180773996120768895))
(.branch 5320
(.leaf (1484, 1482, 463119935432178034597102209))
(.leaf (1484, 1482, 3253226445865811495058735487))))
(.branch 5323
(.branch 5322
(.leaf (1484, 1482, 463092043955124253449192063))
(.leaf (1484, 1482, 5425666143785639191003398527)))
(.branch 5324
(.leaf (1484, 1482, 463030376489673743495268740))
(.leaf (1484, 1482, 774928516304621508195451263)))))))
(.branch 5337
(.branch 5331
(.branch 5328
(.branch 5326
(.leaf (1484, 1482, 463238566443287426176582528))
(.branch 5327
(.leaf (1484, 1482, 772510665461684958960615807))
(.leaf (1484, 1481, 30345161171478897120014345240959))))
(.branch 5329
(.leaf (1484, 1481, 172638629153699294536724427768447))
(.branch 5330
(.leaf (1484, 1481, 30346396693666399437317661065599))
(.leaf (1483, 1480, 11282891418754934064414665774502707583)))))
(.branch 5334
(.branch 5332
(.leaf (1483, 1480, 1989266488527061906231415489488158848))
(.branch 5333
(.leaf (1483, 1480, 28557663067408581668033517293022544255))
(.leaf (1482, 1479, 3317908037764926333672785306627998079))))
(.branch 5335
(.leaf (1482, 1478, 130332798859049837465655184655160189124991))
(.branch 5336
(.leaf (1482, 1471, 5191007002451963019522171630474602374609158704202875840176802472003532226943))
(.leaf (1481, 1468, 32122378024469577644158657446993931530943715810035613136258811858347861736792833196415))))))
(.branch 5343
(.branch 5340
(.branch 5338
(.leaf (1480, 1461, 15091352560722711319258062150770387811316654678909921924226948873336822062466880600012809322109674458831485996722422143))
(.branch 5339
(.leaf (1473, 1460, 21450764828776228144355300158328643543117309739890047203339215901747872640628126197996125322579424566714701007194352705798527))
(.leaf (1470, 1460, 5043687068922233217365734043884616172974337600661009641052874998536674929939850596016978227872162697445804620581374595))))
(.branch 5341
(.leaf (1463, 1460, 4854309514261431431034848692183397018343621356249028473639598057885632569040483422618165764352790289982369898168703))
(.branch 5342
(.leaf (1462, 1451, 4299461138675091697861780648430270457308576655559240786884715802997674578667843446768038008886902763499364259921363071861119))
(.leaf (1462, 1451, 41117896802728948114646646024791815055262435719020997256119630786091625391715358853015812747015205517650756225)))))
(.branch 5346
(.branch 5344
(.leaf (1462, 1451, 1129025600316655614751716905937501460538012750502909409971186744762770129279))
(.branch 5345
(.leaf (1453, 1451, 44834548868543982178346317925306854054765662477552756510084929568047998))
(.leaf (1453, 1451, 10326237148022703071170738488855643681660222556932920655456664624890239))))
(.branch 5348
(.branch 5347
(.leaf (1453, 1448, 971378795615601722113691480039128166870650480211701859003663714711354131739146453375))
(.leaf (1453, 1446, 936831090931962229061678674330884194492325952422529)))
(.branch 5349
(.leaf (1453, 1446, 559775153297252909346654872723381419760457865363839))
(.leaf (1450, 1446, 5819708061952087730866622274340927099006029985153920))))))))
(.branch 5375
(.branch 5362
(.branch 5356
(.branch 5353
(.branch 5351
(.leaf (1448, 1446, 559769377404292919433771167900661974997631674220927))
(.branch 5352
(.leaf (1448, 1443, 580042761062871141764852733487284763239651603553959690020906467711))
(.leaf (1448, 1443, 3932909447460993776011424725834538641602495496782720))))
(.branch 5354
(.leaf (1448, 1443, 130420392907052702246654382259399735443839))
(.branch 5355
(.leaf (1445, 1443, 565891564930568017987933863744168397832831))
(.leaf (1445, 1443, 130331464438757502291038437593785988809087)))))
(.branch 5359
(.branch 5357
(.leaf (1445, 1441, 187080751155433603785059115920673666346827957339265))
(.branch 5358
(.leaf (1445, 1441, 4662712924125446689317505717816525183))
(.leaf (1445, 1426, 3513836698084095637130650040358420709781737863962934618473400987698837247543034453531679379630535587733307775))))
(.branch 5360
(.leaf (1443, 1426, 5862236078823194200811242681495597817424293495662383774964462506752724720060809589686708678625204243907151493))
(.branch 5361
(.leaf (1443, 1426, 3515947797487661258518000272299568170193777069307449307854189315859073125128970251289676561335077734799835519))
(.leaf (1428, 1424, 25256916250011969639378959884174631803486521795941945355365694489735927452106740649769456268720062418722143079816429696))))))
(.branch 5368
(.branch 5365
(.branch 5363
(.leaf (1428, 1424, 3513944905751993885978517234686860345631568321907141126844250663827381959380586955320327417241681858930868607))
(.branch 5364
(.leaf (1428, 1411, 2411584045499199346808906001524293663226142347254853105622844011586920417582648414115747442475752738716763778290191009809988258082251385587057419331658769218326355755008383))
(.leaf (1426, 1411, 1913856867586208291396036744114562954272910841480634454332114739234345886161960200145790706128978048))))
(.branch 5366
(.leaf (1426, 1411, 818103861604062592247851097241335771901882292023732077002034732137623562735120461173312822018310527))
(.branch 5367
(.leaf (1413, 1408, 848935898495600787806252040109772596279260656554287213224387634531315268270366011040820480742418359366680116593023))
(.leaf (1413, 1386, 491871085615877951879660548302925855968732141837932447760586293491245748861989739096229692650710308816602581185246474222504607388712588693977238709335415369630623597469319810648125745317451434289265034865345153)))))
(.branch 5371
(.branch 5369
(.leaf (1413, 1386, 823187952917507730296993517497793180463403632781310906056300126551534404756629485417559999299667820339987242241127495448124666027301991379196839808309995035873045621542390551141851626108592267048854293657354623))
(.branch 5370
(.leaf (1410, 1386, 3593150826670551029136320236202135877226200075493392548487925609096056520353570872671216682160672540960942075396457478047100885803034194190324926336))
(.leaf (1388, 1386, 1195660133240998237512114482359896541299896678594083914197165198391048573433083786083531169751781011518103779768801614824984563836749956654896775551))))
(.branch 5373
(.branch 5372
(.leaf (1388, 1361, 1031872368018436642495893460682620229147866230479297533882489466109177058944527368255857188346455355542293530064050340553536295375032495932518748843193889248183681598820039074946308835121189059989603321037926412584524391772788821285603758079188347835422431860324499839))
(.leaf (1388, 1361, 3665947074921684696296578460909959912375831791825530649279926956978639366453965559391019751476523693399603329981756323118178426576127193694192781300081462405533555401359448491217526245609273885852218621452799127075114926521306214845834121166304619463297)))
(.branch 5374
(.leaf (1388, 1361, 1195684617169744334433904867328381595348417383147227941704261950242572587226841337698106704005175808902174718460639990047501156523973289961517482367))
(.leaf (1363, 1361, 10757563749460409325461706121527683230246703208898224697291761843465709278221887343513468076513550681170059359800994560971915396592944278028328831101)))))))
(.branch 5387
(.branch 5381
(.branch 5378
(.branch 5376
(.leaf (1363, 1361, 1195660133241003893758291162789429641763712462242208959714763928711526527756179601842139362110161704233233448941798598216104494637871693407916654975))
(.branch 5377
(.leaf (1363, 1344, 3032400348427190513290225831486848992059698450678426938951510897560169371140182056360852600919317394825668647183770515811879020466003472423725498514170210391225990200649631346612896348395472569058911732577528573759841807720513919))
(.leaf (1363, 1344, 5880584066653217436569588185363632029384016375688742009643402837346425733904310580114922618022067276951257727))))
(.branch 5379
(.leaf (1363, 1344, 3513872953952109640336306488697894829021364047309905391611667516777371686451936938600644097053786000607805823))
(.branch 5380
(.leaf (1346, 1341, 2977349202172594333792081642741152341364798505985879645994551335130293107780970357079235426764230814059680685504228302586239))
(.leaf (1346, 1341, 989026881419533021537246446247918906091446793547230676175215996718238913564472983820833212275972528204643661473009132045439)))))
(.branch 5384
(.branch 5382
(.leaf (1346, 1341, 18122244740240214576636127927756913438429719211348119274241649638684769638091944674663521573739719358291517581293906510676351))
(.branch 5383
(.leaf (1343, 1341, 217442421183165393720459395113696641352321))
(.leaf (1343, 1341, 130421914250032870712243365333283028271487))))
(.branch 5385
(.leaf (1343, 1341, 305575554195485274311521412142318458175616))
(.branch 5386
(.leaf (1343, 1341, 2017704258291999547523662207))
(.leaf (1343, 1341, 463035080409412539430929788))))))
(.branch 5393
(.branch 5390
(.branch 5388
(.leaf (1343, 1341, 774928515655821686843900287))
(.branch 5389
(.leaf (1343, 1323, 230414558754132334013210830772414461009961845277384658831926749034814850492116511638072068912328408025633690420096))
(.leaf (1343, 1323, 6223303168878122946645849327430947167829749045598295594922424763199387574037664232978586668405706591485091211379071))))
(.branch 5391
(.leaf (1343, 1318, 278386318413771158054200933419442062758353618413897041145515144095269872985168034770484092648346004555950510056835355167250573248455508351))
(.branch 5392
(.leaf (1325, 1317, 42585166145249300720095975214038788293461825601047367721787088722864903417081001854117461964176957929469958321185007644846458702993144087118207))
(.leaf (1325, 1317, 18247858926604486188073803115206491320237592321106756008192640610726681964886796490706693358134252163148320560200680036503300650064369344774272)))))
(.branch 5396
(.branch 5394
(.leaf (1320, 1317, 30438469970384769872106223080964624240578191992646988439274312343189467656572289456166917978983151871451457976519484483855206004686662990233983))
(.branch 5395
(.leaf (1319, 1316, 2404191360815707516127227890638936423444522055667624303460735))
(.leaf (1319, 1313, 29654771461267748780890726667446332837463585149813287889256485096010082025855))))
(.branch 5398
(.branch 5397
(.leaf (1319, 1313, 936831091018734232484382658958676791033920567050881))
(.leaf (1318, 1313, 259803811895680618648110822437426760820417560959)))
(.branch 5399
(.leaf (1315, 1313, 8541402853458391625420393012134678943485591680))
(.leaf (1315, 1313, 14294908005067373077278930723928202968750293375)))))))))

def rowDataBlock54 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 5450
(.branch 5425
(.branch 5412
(.branch 5406
(.branch 5403
(.branch 5401
(.leaf (1315, 1313, 43558131706769020251329232402207769297024))
(.branch 5402
(.leaf (1315, 1313, 774928516016954081963671935))
(.leaf (1315, 1313, 463035080409410336112705664))))
(.branch 5404
(.leaf (1315, 1313, 3250808594226582236675768703))
(.branch 5405
(.leaf (1315, 1310, 130331474823350293323515797509761908670847))
(.leaf (1315, 1301, 10669546176376044907843000063215208540762696480112839877801634458864972333127395311999)))))
(.branch 5409
(.branch 5407
(.leaf (1315, 1301, 2906488779800065374085645052555869483892319284542900248668845749706101278082863136896))
(.branch 5408
(.leaf (1312, 1301, 6784208371572275426399795236554738657176897748634919852345479529351263733753502040447))
(.leaf (1303, 1301, 2906548065349817103534611292683578700796273282951310835290490506686020132700828926591))))
(.branch 5410
(.leaf (1303, 1301, 4849128052400186809782904474829645347436047637552890214145559268063386479626901586303))
(.branch 5411
(.leaf (1303, 1295, 1364908206246439810535669119248919393615024894971096193949806650543716201194996201798526600046641791))
(.leaf (1303, 1295, 110436019700130191671864549563792823914474516564433109375))))))
(.branch 5418
(.branch 5415
(.branch 5413
(.leaf (1303, 1295, 36685421523485492005136537489886184284490513262711865472))
(.branch 5414
(.leaf (1297, 1295, 61204600432753442058862605534540851423384174523456618879))
(.leaf (1297, 1295, 36696252712119925210953878139786467562848704481181237376))))
(.branch 5416
(.leaf (1297, 1295, 12260524101991205142969684366863801596207518377060598143))
(.branch 5417
(.leaf (1297, 1294, 30345467029711259621195377541503))
(.leaf (1297, 1289, 232556758129940780149181639572535477929936534400076218751)))))
(.branch 5421
(.branch 5419
(.leaf (1297, 1286, 10325923268028147989802928611787280101625746556175337783092309624095103))
(.branch 5420
(.leaf (1296, 1286, 114121611803121126449515190438809233099216319602640982866698186635806082))
(.leaf (1291, 1286, 10326766589113873091833165683679203330035229698586622406166808484708735))))
(.branch 5423
(.branch 5422
(.leaf (1288, 1286, 24102349881517694379715233682862700972260875130362647166528931980315263))
(.leaf (1288, 1286, 262871757320928509501584821300688687819827752593311555240834367871)))
(.branch 5424
(.leaf (1288, 1286, 218122985937210452008003512529877452391039))
(.leaf (1288, 1286, 154749570266418939221311871)))))))
(.branch 5437
(.branch 5431
(.branch 5428
(.branch 5426
(.leaf (1288, 1286, 463030376489679236758441860))
(.branch 5427
(.leaf (1288, 1286, 2010450703661979198640030079))
(.leaf (1288, 1286, 463035117302907309689602689))))
(.branch 5429
(.leaf (1288, 1286, 772510664017155378548638079))
(.branch 5430
(.leaf (1288, 1286, 463044598929354564969628542))
(.leaf (1288, 1286, 8790106699556979402097033599)))))
(.branch 5434
(.branch 5432
(.leaf (1288, 1286, 463039821222639482785696393))
(.branch 5433
(.leaf (1288, 1286, 774928515655821686928048511))
(.leaf (1288, 1286, 463035117302907258149995135))))
(.branch 5435
(.leaf (1288, 1286, 3245972891164015027114017151))
(.branch 5436
(.leaf (1288, 1275, 44349499203498618529886154887172437139831129303490820938464002970521221453250943))
(.leaf (1288, 1272, 37579430182677754348660334886918187601956118709150853149525077059358684346800946348831946113407))))))
(.branch 5443
(.branch 5440
(.branch 5438
(.leaf (1288, 1272, 12485828507574426864553961447018141104781520433798331442706668432284257754845963642853281170302))
(.branch 5439
(.leaf (1277, 1272, 20826846301707635844664020515581437644205541807445892732255152621799483733478731806291624198527))
(.leaf (1274, 1270, 53615803622748647681084915890824433838280108431879046945686193345426630748233645169571360468109184925824))))
(.branch 5441
(.leaf (1274, 1270, 125706491792030848024132376873198374610892619106152688634032014475002113622617857169002642130163467747711))
(.branch 5442
(.leaf (1274, 1269, 12260524096349116645011743562000496496778729901917340031))
(.leaf (1272, 1269, 566572129644048257153361704450342973801087)))))
(.branch 5446
(.branch 5444
(.leaf (1272, 1269, 130331464438757196432805858919822741406079))
(.branch 5445
(.leaf (1271, 1268, 14294908011718705353062044915715762271620039039))
(.leaf (1271, 1268, 1988781929085110406209524397204506498))))
(.branch 5448
(.branch 5447
(.leaf (1271, 1268, 71009882182483474126536354099542229375))
(.leaf (1270, 1244, 1994815570033909354398381505292402524541831146816780518662426945024921398870566460646650344490042283645802334202008470505308140907149388155239465599)))
(.branch 5449
(.leaf (1270, 1244, 1195684521901544730896973297357484645850237511961774155522244351865266336573191449331358591868914343996223592156411852979650871856692452485276631423))
(.leaf (1270, 1231, 164386752204281980004431238070065504096010056487043440058265110174896716647715159357680192135611397517783637274612022866795810079664161234432403910107469384509875263171385566877379937306325274644572318803755391))))))))
(.branch 5475
(.branch 5462
(.branch 5456
(.branch 5453
(.branch 5451
(.leaf (1246, 1226, 63653948785650484524428688765840359922683123323818968113407696582425742867729463439971003567829440370202239882657159604779337951708384452663605633060242125769879880046311394659112313188783580228214600219119635576643088154120683903))
(.branch 5452
(.leaf (1246, 1225, 594629567109650209734481198443588719304875321690051909551608445958669181954040102466539371199436291985120359092770423338152414509915695943503600453903918642476672063081814039208772034278142718849379488863826746084548462124832313573759))
(.leaf (1233, 1225, 1394170320213894421931466227108030190488848111528691545449691592534884882792681487557404005773977985659992009790653317306245044213310025178290064183606786819317458721889676453330759785579874258840901919749443517432002655552279372826239))))
(.branch 5454
(.leaf (1228, 1225, 15091969419523296387298462179197181705871323576535987398536217721523667309693346741309981397640769281083327979049648511))
(.branch 5455
(.leaf (1227, 1225, 5043687068922233215174211345029762428586301332848314759899258060254491311778541713856876515862744422189764223212391810))
(.leaf (1227, 1225, 86011872006162106452799555341115881759692653531062337919)))))
(.branch 5459
(.branch 5457
(.leaf (1227, 1224, 664644343359487647711524725517713791))
(.branch 5458
(.leaf (1227, 1222, 304894989765958769521511519695104718602368))
(.leaf (1227, 1222, 130331474823350293323515870411780993712511))))
(.branch 5460
(.leaf (1226, 1212, 446599172784768204720907344561194355678387253150690704333483784069110713442462787012854401))
(.branch 5461
(.leaf (1224, 1212, 190483549187863613266272788622824024345013361823865385132091322776262629949177233775001983))
(.leaf (1224, 1212, 444609879839360642365215259716555893356264539076478041935945659410126272352054909840851583))))))
(.branch 5468
(.branch 5465
(.branch 5463
(.leaf (1214, 1212, 4849128030607895112805489401568098398850852556704898565771800549163251247942323077503))
(.branch 5464
(.leaf (1214, 1212, 676719653373602592511635760372203831836925440208743403369265642440872625024))
(.leaf (1214, 1212, 1132559295289533469086945673822790323574134828304874126895562253030806978943))))
(.branch 5466
(.leaf (1214, 1212, 463210379818352676406493312))
(.branch 5467
(.leaf (1214, 1212, 772510664088931497542746495))
(.leaf (1214, 1212, 463030413383161882324436350)))))
(.branch 5471
(.branch 5469
(.leaf (1214, 1212, 1391480683515448853432631679))
(.branch 5470
(.leaf (1214, 1212, 463035080409424638353801857))
(.leaf (1214, 1212, 6018039795324468418667348351))))
(.branch 5473
(.branch 5472
(.leaf (1214, 1212, 463058600008109821939090047))
(.leaf (1214, 1212, 1085622451369120453758026111)))
(.branch 5474
(.leaf (1214, 1199, 190479648672977990748620854439502988723524100947148006245859868227674904007517312363987327))
(.leaf (1214, 1197, 1369180173681005717426885385674015229103136323764891846592899068656622563912890432842550839548510849)))))))
(.branch 5487
(.branch 5481
(.branch 5478
(.branch 5476
(.leaf (1214, 1197, 818145677878528570597162590797983352586093340196990176240268099363802820979880010277484010917593471))
(.branch 5477
(.leaf (1201, 1197, 1364908199482346471977831332662975218528901088178537092139251113576551386743067136063082843151991423))
(.leaf (1199, 1197, 818103926789161496719572978016239750021060063349074077830856048043646465642774840563854198632874367))))
(.branch 5479
(.leaf (1199, 1187, 35622290952168348471169786444675405594724345735681510464323045516857270328922665577369770676374510116808060008573832292399989623607524368677722849408))
(.branch 5480
(.leaf (1199, 1187, 8749642914878774759975641007734337843578145562844893551881868202523582693008939614591))
(.leaf (1199, 1187, 676740331652693076899167646845629396643236346659713038481496499809928807294)))))
(.branch 5484
(.branch 5482
(.leaf (1189, 1187, 1129025600421556530330079429369728565803009432100732889211766000824289919359))
(.branch 5483
(.leaf (1189, 1182, 818103926789161496719575244881020918114630314263458100354719255788774879541656419314851366190383487))
(.leaf (1189, 1173, 6097443546345864876737988500987254423568744230113639143100616198657528021786149625572069309529391471213189003363899914330676289321253724029311))))
(.branch 5485
(.leaf (1189, 1166, 64817529338928105833909891307133968744554929462570441037130035474575507612623411642147932953709869181210440274758306454384476543))
(.branch 5486
(.leaf (1184, 1166, 369092334417353661268007256370918614793295997010840735253284730659155872834441155269082052029765036775897056094430201075761874047))
(.leaf (1175, 1166, 64818856615372533976224511414528804495128716988139831434996605764020661347952324324798767163933848000835449181273054109465772415))))))
(.branch 5493
(.branch 5490
(.branch 5488
(.leaf (1168, 1166, 281769485264669706166464899701505870669660224327217956423396357789096737782992276688559495080927225609083061885116809705550709377))
(.branch 5489
(.leaf (1168, 1166, 303626214732092771183043031761829593486818176246097805241612672429710930967560355208973382858853994070399))
(.leaf (1168, 1166, 4011104706271157868261485888571932906685821395979411782568832))))
(.branch 5491
(.leaf (1168, 1166, 154749570337632108345819519))
(.branch 5492
(.leaf (1168, 1158, 157567537882986887747103283427677588827699291543745174492908814977))
(.leaf (1168, 1158, 263694509501892521775379520342891758194290646616016076804546560383)))))
(.branch 5496
(.branch 5494
(.leaf (1168, 1158, 157562685683344684092530891853174358580695265382163137123898557312))
(.branch 5495
(.leaf (1160, 1158, 369418177334204157677826676359686823268154376273536588359151911295))
(.leaf (1160, 1158, 157561072468213266732905585477574206167474464857418608803621833347))))
(.branch 5498
(.branch 5497
(.leaf (1160, 1158, 577574503933799560511019035636244501320725660450978550224466608511))
(.leaf (1160, 1158, 463049265955606325882718339)))
(.branch 5499
(.leaf (1160, 1158, 2012868554941201961776644479))
(.leaf (1160, 1158, 463030413383159687596147327)))))))))

def rowDataBlock55 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 5550
(.branch 5525
(.branch 5512
(.branch 5506
(.branch 5503
(.branch 5501
(.leaf (1160, 1158, 10054643107235295389103161727))
(.branch 5502
(.leaf (1160, 1157, 30345158753627329666874922303871))
(.leaf (1160, 1157, 91350534409360164407238499180926))))
(.branch 5504
(.leaf (1160, 1157, 30365249891823289579297688387967))
(.branch 5505
(.leaf (1159, 1155, 217442421324904576609483342049327498331265))
(.leaf (1159, 1155, 130335446930447690227745518754031519596927)))))
(.branch 5509
(.branch 5507
(.leaf (1159, 1152, 61396162381003766660096501937515842179803787716726948223))
(.branch 5508
(.leaf (1157, 1151, 770845816836382083036781278793644086026778019582019830143))
(.leaf (1157, 1150, 2404191169253531485991124922549440861577944331623180183470463))))
(.branch 5510
(.leaf (1154, 1150, 4023658898177068772804010690614244066573089473310543027570562))
(.branch 5511
(.leaf (1153, 1150, 559797900057368708054513946849576043293629860544895))
(.leaf (1152, 1150, 18910378226828086881905159899809036218920153319932032))))))
(.branch 5518
(.branch 5515
(.branch 5513
(.leaf (1152, 1150, 4641943737307859547095637937738547583))
(.branch 5514
(.leaf (1152, 1148, 217442421162962212198801951143367358221694))
(.leaf (1152, 1148, 4652328330405959182277381753759859071))))
(.branch 5516
(.leaf (1152, 1148, 1989873851620867830210790010992394368))
(.branch 5517
(.leaf (1150, 1148, 7290015134544069469426838880242041215))
(.leaf (1150, 1147, 130331464438757504708890222064132758503807)))))
(.branch 5521
(.branch 5519
(.leaf (1150, 1147, 1176698413533132465813459927161520353386368))
(.branch 5520
(.leaf (1150, 1147, 30345161171478753286301111222655))
(.leaf (1149, 1147, 91192078272746679702024578072704))))
(.branch 5523
(.branch 5522
(.leaf (1149, 1147, 30345158753627330792774829146495))
(.leaf (1149, 1147, 273020711054568290509234777292928)))
(.branch 5524
(.leaf (1149, 1147, 1083204600089334740735164799))
(.leaf (1149, 1147, 463049192168630013864641153)))))))
(.branch 5537
(.branch 5531
(.branch 5528
(.branch 5526
(.leaf (1149, 1147, 4801860420792151468126175615))
(.branch 5527
(.leaf (1149, 1147, 463049265955606317292782207))
(.leaf (1149, 1147, 154749571061585748462469503))))
(.branch 5529
(.leaf (1149, 1143, 8541402853458391625420388345108448060408529024))
(.branch 5530
(.leaf (1149, 1143, 14294908005046603889844791412478739635723305343))
(.leaf (1149, 1143, 8546375399686166655139585245702715922593022850)))))
(.branch 5534
(.branch 5532
(.leaf (1145, 1143, 14250306518652803521494489929241460960051265919))
(.branch 5533
(.leaf (1145, 1141, 36685048840568146509182378452270193452875494000659726977))
(.leaf (1145, 1141, 12260524428407212631137186937867481472865529820316959103))))
(.branch 5535
(.leaf (1145, 1141, 1988700482534031575371029625087919231))
(.branch 5536
(.leaf (1143, 1141, 7290015134852345555514017421419741567))
(.leaf (1143, 1141, 1988700324077744196647008887784801150))))))
(.branch 5543
(.branch 5540
(.branch 5538
(.leaf (1143, 1141, 9969240313548040525675672966346637695))
(.branch 5539
(.leaf (1143, 1141, 463049302849094464711885439))
(.leaf (1143, 1141, 9137068410074326876395995519))))
(.branch 5541
(.leaf (1143, 1141, 463030376489677046325117826))
(.branch 5542
(.leaf (1143, 1141, 1083204600018684521547235711))
(.leaf (1143, 1141, 463139120046000403174589057)))))
(.branch 5546
(.branch 5544
(.leaf (1143, 1141, 772510664017155378548507007))
(.branch 5545
(.leaf (1143, 1141, 463086897313515580971485056))
(.leaf (1143, 1141, 1699756767805691143523402111))))
(.branch 5548
(.branch 5547
(.leaf (1143, 1140, 30345471865414538642662029787519))
(.leaf (1143, 1140, 50785715202019930073395600753536)))
(.branch 5549
(.leaf (1143, 1140, 30355717511735628228254645551487))
(.leaf (1142, 1140, 233565086212244953794402867687589))))))))
(.branch 5575
(.branch 5562
(.branch 5556
(.branch 5553
(.branch 5551
(.leaf (1142, 1140, 30345158753627330229824909279615))
(.branch 5552
(.leaf (1142, 1139, 11262122231629070837542267733623112063))
(.leaf (1142, 1139, 91192078117295967391778969944703))))
(.branch 5554
(.leaf (1142, 1139, 30345161171478753286301128065407))
(.branch 5555
(.leaf (1141, 1137, 2134593276395371059035833800228513297400449))
(.leaf (1141, 1137, 130343432683017044038741770738893326516607)))))
(.branch 5559
(.branch 5557
(.leaf (1141, 1137, 304214424727801520367832270071431140672127))
(.branch 5558
(.leaf (1139, 1137, 3317908039002866372885263562626171263))
(.leaf (1139, 1133, 36685797129406459931476012436443012727364733104474237093))))
(.branch 5560
(.leaf (1139, 1133, 574303263708913855410665208919431157965038642106787168639))
(.branch 5561
(.leaf (1139, 1133, 8545069055679557172378363554577722120783988351))
(.leaf (1135, 1133, 14250306573187497426685784511770728874754834815))))))
(.branch 5568
(.branch 5565
(.branch 5563
(.leaf (1135, 1129, 157561085022402907316272877270830900745846672782520986478302921343))
(.branch 5564
(.leaf (1135, 1129, 577574503860143993589570233831218356433591786458841719306765730175))
(.leaf (1135, 1125, 157561085022402160488936113726871460670484331929672755135138169983))))
(.branch 5566
(.leaf (1131, 1125, 578397256114380448922410924719454407625067977167130283516039659903))
(.branch 5567
(.leaf (1131, 1124, 10325922445276481944292357255392271936811560962107088426245740763873663))
(.leaf (1127, 1124, 44834548868556536381438562363028179482855467814564890722325184749961855)))))
(.branch 5571
(.branch 5569
(.leaf (1127, 1124, 559980275551591647282005431974822913305809266934143))
(.branch 5570
(.leaf (1126, 1122, 101839735239962349280706489917045694349242276303715002038026881))
(.leaf (1126, 1122, 130334133279342789192439429929830193299839))))
(.branch 5573
(.branch 5572
(.leaf (1126, 1122, 913660143883202308430736191987216975594111))
(.leaf (1124, 1122, 3317908039311142459980122521199378815)))
(.branch 5574
(.leaf (1124, 1122, 1989186468082903499104050097850089600))
(.leaf (1124, 1122, 4662712924125446689389844786864652671)))))))
(.branch 5587
(.branch 5581
(.branch 5578
(.branch 5576
(.leaf (1124, 1122, 463039858116125426886576508))
(.branch 5577
(.leaf (1124, 1122, 772510664376598923741036927))
(.leaf (1124, 1122, 463030413383161882324435840))))
(.branch 5579
(.leaf (1124, 1122, 1699756767878593162541924735))
(.branch 5580
(.leaf (1124, 1122, 463110970314529577208054401))
(.leaf (1124, 1122, 8207404454646561853004644735)))))
(.branch 5584
(.branch 5582
(.leaf (1124, 1122, 463143750178751849026224767))
(.branch 5583
(.leaf (1124, 1122, 2639092129718597081385075071))
(.leaf (1124, 1122, 463030376489673743495267200))))
(.branch 5585
(.leaf (1124, 1122, 774928519897931060883685759))
(.branch 5586
(.leaf (1124, 1122, 463020950203454268347713153))
(.leaf (1124, 1122, 772510664088931497542746495))))))
(.branch 5593
(.branch 5590
(.branch 5588
(.leaf (1124, 1122, 463030413383161882324435072))
(.branch 5589
(.leaf (1124, 1122, 2935278955451842160156868991))
(.leaf (1124, 1122, 463035154196386630950912641))))
(.branch 5591
(.leaf (1124, 1122, 1391480683659282566111232383))
(.branch 5592
(.leaf (1124, 1122, 463035080409421318344082047))
(.leaf (1124, 1122, 1697338916094122816159351167)))))
(.branch 5596
(.branch 5594
(.leaf (1124, 1116, 36685045917564872527940829990678819963446956472886297215))
(.branch 5595
(.leaf (1124, 1116, 61396162381092969643543888124175520874357107993098649983))
(.leaf (1124, 1115, 2404264633258510304255989617284370315754642679476703016780159))))
(.branch 5598
(.branch 5597
(.leaf (1118, 1115, 4011104699559942348852948268467273985777271246012915558325917))
(.leaf (1118, 1115, 2404191360815474049625745797580975870344896863783336642937215)))
(.branch 5599
(.leaf (1117, 1113, 44996308550160101180339801276003757421297256235416242566895073987855232))
(.leaf (1117, 1113, 130397790838828117903082148551634801852799)))))))))

def rowDataBlock56 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 5650
(.branch 5625
(.branch 5612
(.branch 5606
(.branch 5603
(.branch 5601
(.leaf (1117, 1110, 404675163792291169778211096449365752456101916376052072831))
(.branch 5602
(.leaf (1115, 1110, 1682196925971403281998111721241332792202185720923008))
(.leaf (1115, 1110, 559769377404278417348643727866342887120316779266431))))
(.branch 5604
(.leaf (1112, 1109, 208132610418912624850561493481871661282324180673503166847))
(.branch 5605
(.leaf (1112, 1108, 559769422005742198696193779172449191432632500617599))
(.leaf (1112, 1108, 5426564121510074845950485323779768062388811872535422)))))
(.branch 5609
(.branch 5607
(.leaf (1111, 1108, 13972501191478392627128851923345015167))
(.branch 5608
(.leaf (1110, 1099, 44349499203492525226510320422507564944521050869587078748687916073512350049698175))
(.leaf (1110, 1099, 162804354201177356955036191207848517289185718733022221064038531734382901840511617))))
(.branch 5610
(.leaf (1110, 1099, 1579571601835143618795457768581318357488287685127386170556793009990986498431))
(.branch 5611
(.leaf (1101, 1099, 24156269789308160955897170507480063200309308228727665680241993541685367))
(.leaf (1101, 1099, 10325922445276065009724270429504748817092068878969271946321433245581695))))))
(.branch 5618
(.branch 5615
(.branch 5613
(.leaf (1101, 1099, 31031056174975408806569050640299743476484877008316042584566678132032127))
(.branch 5614
(.leaf (1101, 1099, 774928515944615013016076671))
(.leaf (1101, 1099, 463030376489677029145249664))))
(.branch 5616
(.leaf (1101, 1099, 154749570338195058282398079))
(.branch 5617
(.leaf (1101, 1099, 463030413383162986131031679))
(.leaf (1101, 1099, 772510665886712173810286975)))))
(.branch 5621
(.branch 5619
(.leaf (1101, 1098, 30345777723646900580893310648703))
(.branch 5620
(.leaf (1101, 1098, 70988896643194229685357431947903))
(.leaf (1101, 1098, 30347644305112241734625974681983))))
(.branch 5623
(.branch 5622
(.leaf (1100, 1097, 4662712924123028837895293666544648575))
(.leaf (1100, 1076, 278394802783036492441851911694329849593219991664831384614283838969031824364131180290596932325080753498322154728364068646350404890983924095)))
(.branch 5624
(.leaf (1100, 1076, 465907870633162449463568278753340081684019536141465417160044811003011693227775546237388610346042106049870495353608384469699123632601498239))
(.leaf (1099, 1076, 7087008563639977834427417569163324614922833877577201366221053337552279102297704393144398755796704184631746315235994679150563263840639)))))))
(.branch 5637
(.branch 5631
(.branch 5628
(.branch 5626
(.leaf (1078, 1075, 278457088035045217262357879532059009853378960798203334771545403407953880061869745418770966788613529060173815546464545199791134052150149503))
(.branch 5627
(.leaf (1078, 1075, 465907870198240506788600181503105046822548781248482653239847794020142626424424688194592780801117586574637334244701995067045878537549448321))
(.leaf (1078, 1075, 9915131646997741462058793578146120847288897095261493959530744559196549365698236070499591658275807499389402903525580863496465028284799))))
(.branch 5629
(.leaf (1077, 1074, 3317908037764926333600446237630202239))
(.branch 5630
(.leaf (1077, 1074, 1988741047353248304998123383017111680))
(.leaf (1077, 1074, 664644356634702072755933979900576127)))))
(.branch 5634
(.branch 5632
(.leaf (1076, 1074, 70988896643194229646810100466560))
(.branch 5633
(.leaf (1076, 1074, 30345158753627329666874888683903))
(.leaf (1076, 1074, 375621181519948447170466064302721))))
(.branch 5635
(.leaf (1076, 1074, 154749570194079870173053311))
(.branch 5636
(.leaf (1076, 1074, 463054006768844247173894540))
(.leaf (1076, 1074, 6957375157165035286341747071))))))
(.branch 5643
(.branch 5640
(.branch 5638
(.leaf (1076, 1074, 463035080409412539430929023))
(.branch 5639
(.leaf (1076, 1074, 774928516015828182056829311))
(.leaf (1076, 1074, 463030376489694586971554945))))
(.branch 5641
(.leaf (1076, 1074, 1699756767733352074542252415))
(.branch 5642
(.leaf (1076, 1074, 463030413383164081347691394))
(.leaf (1076, 1074, 772510665097174864522314111)))))
(.branch 5646
(.branch 5644
(.leaf (1076, 1074, 463044488248890122712318593))
(.branch 5645
(.leaf (1076, 1074, 21215446273700534722846916991))
(.leaf (1076, 1074, 463172121271133924371660928))))
(.branch 5648
(.branch 5647
(.leaf (1076, 1074, 1391480683659282565944050047))
(.leaf (1076, 1074, 463035154196388834269135487)))
(.branch 5649
(.leaf (1076, 1074, 774928515944615012999233919))
(.leaf (1076, 1074, 463030376489685790878532480))))))))
(.branch 5675
(.branch 5662
(.branch 5656
(.branch 5653
(.branch 5651
(.leaf (1076, 1074, 4488748633368128798475616639))
(.branch 5652
(.leaf (1076, 1074, 463030413383177284077161091))
(.leaf (1076, 1074, 772510664088931497844212095))))
(.branch 5654
(.leaf (1076, 1073, 30346090835434180769849559548287))
(.branch 5655
(.leaf (1076, 1071, 1348881291175082603200392314889154278130558))
(.leaf (1076, 1071, 130334133279341863155261677462951483736447)))))
(.branch 5659
(.branch 5657
(.leaf (1075, 1067, 74653607623999711888997006696767919570886290762203978123903615))
(.branch 5658
(.leaf (1073, 1067, 2404264633258521744538275129073749899097435946950587586838911))
(.leaf (1073, 1064, 1132559294551113299308100877819765139597019669218230187565821039836062024063))))
(.branch 5660
(.leaf (1069, 1064, 17227563560002426271793744409741251542718269719498141757849265462247552))
(.branch 5661
(.leaf (1069, 1064, 2404191169253588397492878208455082339785655566485500941238655))
(.leaf (1066, 1064, 106867693730379763489970204356164971812922873185149781243015827))))))
(.branch 5668
(.branch 5665
(.branch 5663
(.leaf (1066, 1064, 130331474823350911084609765263408229384575))
(.branch 5664
(.leaf (1066, 1064, 43558131727447570775963739435313775182465))
(.leaf (1066, 1064, 4498420040069442494942675327))))
(.branch 5666
(.leaf (1066, 1064, 463035080409425733570462594))
(.branch 5667
(.leaf (1066, 1064, 1085622451296781385214001535))
(.leaf (1066, 1059, 559775108695765175933697018018518382384470955065727)))))
(.branch 5671
(.branch 5669
(.leaf (1066, 1038, 131141406962328942727041862922741401820631548542813165031704682442361767889913402470471306629337776614365040358174653056363369259686589950028139771003263))
(.branch 5670
(.leaf (1066, 1037, 5135321169401053333517328237694752475061422297444872065533466018411689085545142013545728928204217933556715464246510052950953315830216889112168174653819257215))
(.leaf (1061, 1037, 11986658650545555026985240431483841545925616752590737757439175963713687888058338351152184044890799201793817224566620774624964696562611543317262822805392524162))))
(.branch 5673
(.branch 5672
(.leaf (1040, 1037, 5135321578575319697813935098880847588808050649483696402577773772594935279403843929818276143939871012196463120332250338955595613567478828122009343046258327935))
(.leaf (1039, 1036, 561490665957157054918970636674186978409825738710035927293595853681279311162874211328970927145540321140631749421242959289026556417528350828244477653248582898024831)))
(.branch 5674
(.leaf (1039, 1036, 465907870155086772884816255889133496125191793190355590377828833274865690291682624793675335691090755968240536130456224235108936760032166527))
(.leaf (1039, 1036, 3317908047685371609141920463121875327)))))))
(.branch 5687
(.branch 5681
(.branch 5678
(.branch 5676
(.leaf (1038, 1034, 391666993026324249285025043309497126158464))
(.branch 5677
(.leaf (1038, 1034, 130332798859050145741738897592273634066815))
(.leaf (1038, 1033, 2854625766114909628178596200794698681895813503))))
(.branch 5679
(.leaf (1036, 1033, 217442421162962212203542764363735118056822))
(.branch 5680
(.leaf (1036, 1033, 130342139801098341620558478391017335226751))
(.leaf (1035, 1033, 1171934460457165784407148621093272693966465)))))
(.branch 5684
(.branch 5682
(.leaf (1035, 1033, 30345161171479328902628838080895))
(.branch 5683
(.leaf (1035, 1021, 317792454733184866027310154591169069748750344025821762266324748157744145987495584642040449))
(.leaf (1035, 1021, 30217651884041598650237070471355720681742460602382372675827060668628901359796172620159))))
(.branch 5685
(.leaf (1035, 1021, 2906489011384243848718035887143637893909360974221072612393827778435267973088767058808))
(.branch 5686
(.leaf (1023, 1021, 6799385485418695779111517137336222408799652801245615312008224361082163962216244838783))
(.leaf (1023, 1021, 2906488779800092954111085547660380182383598605633826665974889264306650321486589395072))))))
(.branch 5693
(.branch 5690
(.branch 5688
(.leaf (1023, 1021, 43748037176382925053152525504012028458231217026904224795937320355886808274820965269887))
(.branch 5689
(.leaf (1023, 1021, 463044525142379373938016895))
(.leaf (1023, 1021, 1080786748814052627239207295))))
(.branch 5691
(.leaf (1023, 1021, 463030376489675942518522750))
(.branch 5692
(.leaf (1023, 1021, 1083204600017558621640393087))
(.leaf (1023, 1021, 463039821222682213415322241)))))
(.branch 5696
(.branch 5694
(.leaf (1023, 1021, 772510664017155378498371967))
(.branch 5695
(.leaf (1023, 1021, 463110785847091034840827268))
(.leaf (1023, 1021, 154749570770540622526677375))))
(.branch 5698
(.branch 5697
(.leaf (1023, 1021, 463200861298402967171301504))
(.leaf (1023, 1021, 774928515655821686961471871)))
(.branch 5699
(.leaf (1023, 1021, 463039858116137521514480255))
(.leaf (1023, 1021, 1085622451802591917926056319)))))))))

def rowDataBlock57 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 5750
(.branch 5725
(.branch 5712
(.branch 5706
(.branch 5703
(.branch 5701
(.leaf (1023, 1021, 463030376489674838711928955))
(.branch 5702
(.leaf (1023, 1021, 154749570049683207153975679))
(.leaf (1023, 1021, 463058784475551645661332097))))
(.branch 5704
(.leaf (1023, 1021, 772510664017155378515083647))
(.branch 5705
(.leaf (1023, 1021, 463035154196388825679201660))
(.leaf (1023, 1021, 1391480683731058685122707839)))))
(.branch 5709
(.branch 5707
(.leaf (1023, 1021, 463049302849093369495224448))
(.branch 5708
(.leaf (1023, 1021, 774928515655821686843900287))
(.leaf (1023, 1012, 10326764943610002903315259271626872528294399419850108117968482079998335))))
(.branch 5710
(.leaf (1023, 1011, 1583105296070424055311647490076004817444594678417364398939933397374912758143))
(.branch 5711
(.leaf (1023, 1011, 676719653373599372358446625053724281561390760299275581398816342877426091137))
(.leaf (1014, 1011, 3395890384637947292993146049082965662473942781266933841142039005697780154751))))))
(.branch 5718
(.branch 5715
(.branch 5713
(.leaf (1013, 1011, 676816169982672592463042076764060769990109824889876663738837179016683651713))
(.branch 5714
(.leaf (1013, 1011, 1129025600316655614873933425298809336889600074907497204381936922013638721919))
(.leaf (1013, 1011, 50785715296393472752294643565695))))
(.branch 5716
(.leaf (1013, 1011, 14091246418783301115364639103))
(.branch 5717
(.leaf (1013, 1011, 463020950203452077914392699))
(.leaf (1013, 1011, 774928515655821686894363007)))))
(.branch 5721
(.branch 5719
(.leaf (1013, 1004, 2404338863511293854011393509186925341934105646335982772945279))
(.branch 5720
(.leaf (1013, 1004, 12039517814265860108222994348581531088998147971426851875653763))
(.leaf (1013, 1004, 2404191169253520045708838076339769877560192806857204530348415))))
(.branch 5723
(.branch 5722
(.leaf (1006, 1004, 10476519481781893680507821973693470893747592001386486316337801))
(.leaf (1006, 1004, 2404804071689238595512423398590477372874785163934345242018175)))
(.branch 5724
(.leaf (1006, 1004, 4011104693960929576324350626927252776008138604880523664753281))
(.leaf (1006, 1004, 15962663587474970958681342335)))))))
(.branch 5737
(.branch 5731
(.branch 5728
(.branch 5726
(.leaf (1006, 1004, 463181233962706336890160255))
(.branch 5727
(.leaf (1006, 1004, 6979135821918098611486458239))
(.leaf (1006, 1004, 463035117302900686850032255))))
(.branch 5729
(.leaf (1006, 1004, 774928515800499825243259263))
(.branch 5730
(.leaf (1006, 1003, 30345158753627114057042812338559))
(.leaf (1006, 1003, 536612807748933581160547371385726)))))
(.branch 5734
(.branch 5732
(.leaf (1006, 1003, 30345161171478753286301128196479))
(.branch 5733
(.leaf (1005, 1003, 50627259075736622115549985313674))
(.leaf (1005, 1003, 30345469447562898850453760573823))))
(.branch 5735
(.leaf (1005, 1003, 70830440318165700974917252481663))
(.branch 5736
(.leaf (1005, 1003, 20225336027291756765642621311))
(.leaf (1005, 1003, 463030376489674838711927425))))))
(.branch 5743
(.branch 5740
(.branch 5738
(.leaf (1005, 1003, 1085622451297344334730297727))
(.branch 5739
(.leaf (1005, 1003, 463044635822844911411988350))
(.leaf (1005, 1003, 772510664520151161997164927))))
(.branch 5741
(.leaf (1005, 1003, 463092043955112145936386685))
(.branch 5742
(.leaf (1005, 1003, 774928515800499825242603903))
(.leaf (1005, 1001, 1988720844171811908405244198635111041)))))
(.branch 5746
(.branch 5744
(.leaf (1005, 1001, 5976364029332340227697054980713218431))
(.branch 5745
(.leaf (1005, 1001, 1988700482534031575371029625087918208))
(.leaf (1003, 1001, 4652328330714235266854165570729804159))))
(.branch 5748
(.branch 5747
(.leaf (1003, 1001, 1988700324077730195568256942235124606))
(.leaf (1003, 1001, 9969240313548040525675672967120355711)))
(.branch 5749
(.leaf (1003, 1001, 463035117302905076306608767))
(.leaf (1003, 1001, 5105300802736180364669157759))))))))
(.branch 5775
(.branch 5762
(.branch 5756
(.branch 5753
(.branch 5751
(.leaf (1003, 1001, 463030376489699010787870845))
(.branch 5752
(.leaf (1003, 1001, 1391480684165093099126587775))
(.leaf (1003, 1001, 463035154196412005617697409))))
(.branch 5754
(.leaf (1003, 1001, 772510664017155378531926399))
(.branch 5755
(.leaf (1003, 1001, 463035117302900678260098175))
(.leaf (1003, 1001, 18679119904364371071999672703)))))
(.branch 5759
(.branch 5757
(.leaf (1003, 1001, 463044635822842720978667394))
(.branch 5758
(.leaf (1003, 1001, 774928515655821686894231935))
(.leaf (1003, 999, 1989105655357129523193483008849937025))))
(.branch 5760
(.leaf (1003, 999, 8614050834087002682633237253406589311))
(.branch 5761
(.leaf (1003, 999, 1988700324077706546842358836046529408))
(.leaf (1001, 999, 11282891419063210148056389718856434047))))))
(.branch 5768
(.branch 5765
(.branch 5763
(.leaf (1001, 999, 1990018759930120623677185367822238335))
(.branch 5764
(.leaf (1001, 999, 3317908037764926333600446237563158911))
(.leaf (1001, 999, 463030376489678158721647745))))
(.branch 5766
(.leaf (1001, 999, 2012868557827446372967580031))
(.branch 5767
(.leaf (1001, 999, 463030413383188296373306240))
(.leaf (1001, 999, 772510664089494447512748415)))))
(.branch 5771
(.branch 5769
(.leaf (1001, 999, 463087081780956318066999937))
(.branch 5770
(.leaf (1001, 999, 154749570194079870609981823))
(.leaf (1001, 999, 463044598929357850619609216))))
(.branch 5773
(.branch 5772
(.leaf (1001, 999, 154749570193516920554324351))
(.leaf (1001, 996, 130335446930447692645597085644220872655231)))
(.branch 5774
(.leaf (1001, 989, 1132559297185977472801581714384768257704444133381923219286470277137134780799))
(.leaf (1001, 988, 44349499203492208466884284212181479776764369802125114191668237608020775276970367)))))))
(.branch 5787
(.branch 5781
(.branch 5778
(.branch 5776
(.leaf (998, 984, 6296902265296910426943209274259614786504348544849241535365987517885280195548671486965236116767048576))
(.branch 5777
(.leaf (991, 984, 818103926789252551735349750190001720993744596250254994273392802445565347483587136920291172914626943))
(.leaf (990, 984, 1364908199354534400250274732569907029337343791009917448663189117949819179630270237805001739109073535))))
(.branch 5779
(.leaf (986, 984, 4849128029706803109768513393431959940055158832405629569153061396354180914111145378175))
(.branch 5780
(.leaf (986, 981, 684943676176312830532518131016015433271116178082349663302579192191))
(.leaf (986, 967, 237600369603742897878509113473800790036983306246719303768317673115966850421755065867919009454051339619288148098692799705598853248)))))
(.branch 5784
(.branch 5782
(.leaf (986, 967, 3513729610288610260866832762649381031039692380643337848096572915289322048943165067746021835114140369225318783))
(.branch 5783
(.leaf (983, 967, 5862236080461496257617210211674988885074982923001786776647901877674920640766761545783551807206232692673675392))
(.leaf (969, 967, 3515345166167969043072601053412287101992558327312572913802335307499379345619545047141366877389535141643157887))))
(.branch 5785
(.leaf (969, 960, 567941684108654672505052365872603263163897992353995301337842493429716197632043927294758317781012022815965973289442749933342884941847702190162303))
(.branch 5786
(.leaf (969, 958, 2144178484942365146623046219618670512887555200436292612436240249931955041297699209657985997297551947349995634503257324464822186100050036353))
(.leaf (969, 958, 10327818889278182019163479673702550136983204566203590038349269553840511))))))
(.branch 5793
(.branch 5790
(.branch 5788
(.leaf (962, 952, 1913856868992141080815084529747500672882881746824893093610123150124168851203268515004604309376533374))
(.branch 5789
(.leaf (960, 952, 818103861604010269193118934405789543555924865171905529130682234810205584154123694911581622460481919))
(.leaf (960, 913, 95318652912205631638424539498256025343418012262730532240332311635522480445152606527291728481406823356262110902596463117146426626969283257702873377548495600622599116499933702697537180754086184506174198643984263141854373097215210809044885605441947013487587939993922758900446203640949244287))))
(.branch 5791
(.leaf (954, 913, 18300426978962733552541042077368910464039405483787773675118935620902754731569125759593907199005458850306303501195708713312559202468838101794389706148924139234342198273296859415645092687595930262666991041363304849594467390722412034442775485988896681953405))
(.branch 5792
(.leaf (954, 913, 2553914543970288848551699206449371289101524777403178490747305541940166586452132484510141703120023594864709563826466414563957933999677882658460275883221325502754811715531881176355065981069550712710502570679043686714994679096873626638684975661439))
(.leaf (915, 912, 1175082092439820256665238710284222540565586342382787408128020349012737601405710029289868120203271045390701250775322130808925809669678881142695385603580827370597947084995440588490252052177723204759211209387873441711761503316418619646231547907303014783)))))
(.branch 5796
(.branch 5794
(.leaf (915, 909, 594629567109568556018394950654076995103761618505598695364351983447556910354854902560229903557308890487599813126306266656272542154051430971832060680845254225276000096822359589651532382834829494811192643706712200418046501156798263787903))
(.branch 5795
(.leaf (915, 908, 65219668907492048160938001783377423122923025292940763366735223150063630027723643659048196858147020517356842800561768681600695017858826834780273706712685912823309199362114299490392360065019322192544431747960522394934176007382726251296784767))
(.leaf (914, 888, 12430820982122902388601640570783190588526749768760641828625607036010997556554257049261990190139832769018730225810023905637884450964291007656014839936))))
(.branch 5798
(.branch 5797
(.leaf (911, 888, 1195660133240998237512111184826801761372913771607295384776586440257813394490081367056476122285060254477744404191762807985251664475942951568971530623))
(.leaf (910, 867, 392424058412893750361618684260372940385425067684185364976241392721236873082307676596398632986006787257066755997313323640312332257100408247167982892623867767258635296613569995842253848816688442962869951322325609891415119555990679758988358091806867839)))
(.branch 5799
(.leaf (890, 852, 19616036135799279863589787085171439202735711507700036954141332087026319959387551456058193462535026908688357019108093136963157360343086794013952819970658679062068806040491934028635561049113405752975026251733945809920414472838102582021299925237923336054453723033170359401212762452735479970667117287516284224878789263743))
(.leaf (890, 844, 89060264015591982820157948551175446806957882522248468633791171396010024225042471072003658691651985498077897770968928852473146749238601101322046665839837520581642498823454063970691688492409753902917832250421822749693718839330693370525886009216595397733881747698283759633778240000098155431573260102681702250534814334288625443738464348218014331)))))))))

def rowDataBlock58 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 5850
(.branch 5825
(.branch 5812
(.branch 5806
(.branch 5803
(.branch 5801
(.leaf (869, 844, 194292292403173320352624929555775332376510266133707598898255656017123006650624412332857390460797877228160824333001619297312118070117708658711515833027234809803358095404410710106014393537044118500488151712887301893429407302997275071746734503305828535297691903404253902244464070371904421954916492196826389323467256714570589978699816173951))
(.branch 5802
(.leaf (854, 844, 38969643310096677365194699444933938289937766193350861253512069906722527167159392080612694565382811919902374823935865043493452154860742873149853202463827883617458772221996077382000780348174199900836875500046913974468541302975733293681412735))
(.leaf (846, 844, 169407394415151557849299910313824477568845245325203914409250651908229044654071572610782292127053357635168963007148544575661133037053076320886203583784554543371062026383391503964003814083237579438611999857772512837815571614882760390437241215))))
(.branch 5804
(.leaf (846, 844, 649798067402213776849736982559757146167039256282156477819773638118876421658960057960917976192824994770434686500027422373963834910224351873))
(.branch 5805
(.leaf (846, 844, 263694511219053775327003666936504505925193296780832981018859471231))
(.leaf (846, 844, 463039821222640578002354304)))))
(.branch 5809
(.branch 5807
(.leaf (846, 844, 7906381925562519188570046847))
(.branch 5808
(.leaf (846, 843, 30358132945523362654008761057663))
(.leaf (846, 843, 50785715206723849814390559671168))))
(.branch 5810
(.leaf (846, 843, 30345158753627114057043852525951))
(.branch 5811
(.leaf (845, 842, 5986748624598043857879892996619174271))
(.leaf (845, 842, 1988700482534045742470481554033279615))))))
(.branch 5818
(.branch 5815
(.branch 5813
(.leaf (845, 842, 3317908039612164985755426835106693503))
(.branch 5814
(.leaf (844, 842, 70830440318128807482371786867586))
(.leaf (844, 842, 30345161171479257126509423296895))))
(.branch 5816
(.leaf (844, 842, 700456647828469124789948951496060))
(.branch 5817
(.leaf (844, 842, 772510666107670030511571327))
(.leaf (844, 842, 463030413383161882324436354)))))
(.branch 5821
(.branch 5819
(.leaf (844, 842, 3566338233433104927485329791))
(.branch 5820
(.leaf (844, 842, 463035154196389920895861377))
(.leaf (844, 842, 2627002871305433582544093567))))
(.branch 5823
(.branch 5822
(.leaf (844, 842, 463181418430151467737219711))
(.leaf (844, 842, 2012868556810758757441864063)))
(.branch 5824
(.leaf (844, 841, 30345158753627258453705932145023))
(.leaf (844, 841, 50785715206723849809992513159296)))))))
(.branch 5837
(.branch 5831
(.branch 5828
(.branch 5826
(.leaf (844, 841, 30347940491938047318774263906687))
(.branch 5827
(.leaf (843, 828, 20826846324943777027826032156719231518872928294755232639134886346836970554037152833163726291327))
(.leaf (843, 828, 12483275250078758189690722152679382988498360662833695933171138745651318031388576416660748959872))))
(.branch 5829
(.leaf (843, 828, 4172040163082215366934104496901230132786915441457964189641959788208734685040503001371314815359))
(.branch 5830
(.leaf (830, 828, 445604526341938782562891927241157852873554947982201301403158725355329160277696262275269247))
(.leaf (830, 828, 190479648672998290054548408411188961235350525028734905387197786256190338941268669700702591)))))
(.branch 5834
(.branch 5832
(.leaf (830, 827, 45825351846023164704368722202514160133336900545707029322923548626452207169055466757730278113663))
(.branch 5833
(.leaf (830, 827, 71147352968222758320884791836800))
(.leaf (830, 827, 30346704969750401167757177520511))))
(.branch 5835
(.leaf (829, 825, 217442421386147945987354384179546873069696))
(.branch 5836
(.leaf (829, 825, 130334122894748763846700243477467083440511))
(.leaf (829, 825, 218122986100103554123200784658422288023680))))))
(.branch 5843
(.branch 5840
(.branch 5838
(.leaf (827, 825, 4641943741329955748954635101892837759))
(.branch 5839
(.leaf (827, 822, 559769377404249153563549951615006313486003250004351))
(.leaf (827, 809, 385389957607760689332509310720022589008663515355850554255391825883770148061662705753213609305266248940064937607551))))
(.branch 5841
(.leaf (827, 809, 53619616359607512373408155613444671918342217770640806958352894560032212874420589522739074986406536216704))
(.branch 5842
(.leaf (824, 809, 304186150900949823509794783844175335851485095250092220556076822215496667450554785630376459726582200664447))
(.leaf (811, 809, 53615254674080925266187912109547431901139768676591062021394992405140303881503140718847993046224567468671)))))
(.branch 5846
(.branch 5844
(.leaf (811, 809, 161122455502588501190674723307680518947056836690457735469714842321960782382539200283204899031207767048575))
(.branch 5845
(.leaf (811, 809, 318787101057211604634740901674716281265930554776120543131669592398583399571596925451833989))
(.leaf (811, 809, 2634256426583690802741838207))))
(.branch 5848
(.branch 5847
(.leaf (811, 809, 463030413383165176564352380))
(.leaf (811, 809, 772510664160707616620675455)))
(.branch 5849
(.leaf (811, 809, 463237644106085935427289729))
(.leaf (811, 809, 1085622451297344335602712959))))))))
(.branch 5875
(.branch 5862
(.branch 5856
(.branch 5853
(.branch 5851
(.leaf (811, 809, 463035117302938070245376128))
(.branch 5852
(.leaf (811, 809, 1080786748018322868044562815))
(.leaf (811, 809, 463049265955605222076121727))))
(.branch 5854
(.leaf (811, 809, 774928515873401843891569023))
(.branch 5855
(.leaf (811, 788, 64816865700709437498402421407738505349131208288641718495052923927236032570797891617352435321832497175413926607614640143644688767))
(.leaf (811, 788, 1882857618620468818716025039777552632816741442000421347496687024164698719270016535567520868632423948282314205046099775979872257153)))))
(.branch 5859
(.branch 5857
(.leaf (811, 788, 64816870865209193672219744343208441441664776656576467037551352760471030432905406428440507866496966141342521677121844326223053183))
(.branch 5858
(.leaf (790, 761, 1199336785628303792145360917142754778792400319144058796980626307821887670865752235969670513648124065943208560792943324325806401845576257086845320032065346667292404310415024750522645598415847416343299540761147604234576537895107965231349935488735012307842630015))
(.leaf (790, 758, 202356377907398306023372784921898655306984429272312018808806039370455862121492349365948478276596832936904358921695287984854958273026686156441393339210643733610033699085885381068381379756634722829061424221442004543956105137686856124087134737076934920745909467366498798469503))))
(.branch 5860
(.leaf (790, 755, 1848214184599191749375014473579192490210763492261458005494034154400279552935816012808984473178392589485440966309562874533433041179190360338129320332561226584751417127859547387827870363041222111849211728192445466058928478633547769259346095885549384104867094837939057247751641229125813797247))
(.branch 5861
(.leaf (763, 749, 118837482158905661255037751134792249258257984681529451446104952811082451480617513215668876762067279006281593037480942111279324374329345869207235947159608818044208243925869840776699309752576536177813590679320528881026))
(.leaf (760, 749, 32234933424215539740122259551201251715162175355546079015301642191093160884625972329489214885822144558459044202426485600256945240608871754785223626172462657187417808860692861081413304849386315797031563490288094675327))))))
(.branch 5868
(.branch 5865
(.branch 5863
(.leaf (757, 748, 7755039316857386783209263851073798857742964034429449471068193543164183533189865287376669591398648090717378922201049104822983368983554719259680945386482876665299761685615274107477064320590545294303799749599486012628599167))
(.branch 5864
(.leaf (751, 748, 317792454554865048657165024212674430338945051682592803412830337632027837399544559092827781))
(.leaf (751, 748, 1129025600526457445883922024170848209442080324257940447988040517261989904767))))
(.branch 5866
(.leaf (750, 747, 262871757863240369025545842586588211614255366578118089233473143167))
(.branch 5867
(.leaf (750, 747, 1988700482534126151827899932005565055))
(.leaf (750, 747, 3317908044867365523620219856898621823)))))
(.branch 5871
(.branch 5869
(.leaf (749, 744, 19981598029347877092012436378368024515221062015))
(.branch 5870
(.leaf (749, 733, 818103926789163431799913935329162983904038376233932533905699139730457835082981774716575291743076735))
(.leaf (749, 733, 3011754204177368145444991726320197531659770315205634438603198531639477974011689543444421856594952320))))
(.branch 5873
(.branch 5872
(.leaf (746, 733, 20826846303642716166585323164254662876549544444211967190197979050414257917752933205686121398655))
(.leaf (735, 733, 12483275250078758189690742911838342292511877599904880263734804577418006539774039329459392153733)))
(.branch 5874
(.leaf (735, 733, 29268323391523083952019385926891544250148460257234732882212300077056945555052020957894422888831))
(.leaf (735, 733, 311365604678850543013956768350859815705146314066464401747082085024615745711964799)))))))
(.branch 5887
(.branch 5881
(.branch 5878
(.branch 5876
(.leaf (735, 733, 17125650226016583293847404927))
(.branch 5877
(.leaf (735, 733, 463030376489678132951843457))
(.leaf (735, 733, 1083204599658115076380885375))))
(.branch 5879
(.leaf (735, 733, 463073006915247877478352258))
(.branch 5880
(.leaf (735, 733, 772510664160707616654098815))
(.leaf (735, 730, 130393860270106207038567282004544017990015)))))
(.branch 5884
(.branch 5882
(.leaf (735, 730, 218122985957889002594895780808433185267082))
(.branch 5883
(.leaf (735, 730, 130332788474455502634905671891620034838911))
(.leaf (732, 729, 19981598029347877092012436378368024514146599295))))
(.branch 5885
(.leaf (732, 729, 8541403534023206913848365786944001249069958018))
(.branch 5886
(.leaf (732, 729, 294325365464340443564782437904977629789755998591))
(.leaf (731, 729, 70988896643194229652286183768960))))))
(.branch 5893
(.branch 5890
(.branch 5888
(.leaf (731, 729, 30345158753629124632801540112767))
(.branch 5889
(.leaf (731, 729, 192366441619714221089655552410241))
(.leaf (731, 729, 154749570194079870256808319))))
(.branch 5891
(.leaf (731, 729, 463035154196435073887044735))
(.branch 5892
(.leaf (731, 729, 3248390742587352978292736383))
(.leaf (731, 727, 1988862107985570137799430267746583938)))))
(.branch 5896
(.branch 5894
(.leaf (731, 727, 3328292636729942972955845132568559999))
(.branch 5895
(.leaf (731, 721, 157561072468198689715574672827296159049734510237338764212977993600))
(.leaf (729, 721, 580042760671510093016226366295979750846655379899759311110503661951))))
(.branch 5898
(.branch 5897
(.leaf (729, 721, 157561085022405903394629144284955463504604727633545586553957328537))
(.leaf (723, 721, 262871757665931568156211925093361158806099469501610835619151413631)))
(.branch 5899
(.leaf (723, 721, 36685045917564872527940829990678829445073408177752441471))
(.leaf (723, 721, 61396162381003766662749765632540250882730629931741544831)))))))))

def rowDataBlock59 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 5950
(.branch 5925
(.branch 5912
(.branch 5906
(.branch 5903
(.branch 5901
(.leaf (723, 721, 463030376489682530998354048))
(.branch 5902
(.leaf (723, 721, 1083204599872880483611115903))
(.leaf (723, 721, 463058673795080610629223041))))
(.branch 5904
(.leaf (723, 721, 772510664017155378447909247))
(.branch 5905
(.leaf (723, 721, 463035154196388825679204485))
(.leaf (723, 721, 1080786748163001006174830975)))))
(.branch 5909
(.branch 5907
(.leaf (723, 721, 463039821222639482785694590))
(.branch 5908
(.leaf (723, 721, 774928515655821687011737983))
(.leaf (723, 721, 463020950203467462487245439))))
(.branch 5910
(.leaf (723, 721, 21795730667187895795636568447))
(.branch 5911
(.leaf (723, 720, 30345158753627330229824909279615))
(.leaf (723, 720, 1370489218230565880728518286837377))))))
(.branch 5918
(.branch 5915
(.branch 5913
(.leaf (723, 720, 30349188103383889616082057625983))
(.branch 5914
(.leaf (722, 718, 217442421162962212410662806826644498482050))
(.leaf (722, 718, 130352773625064620947546239468724578943359))))
(.branch 5916
(.leaf (722, 717, 2854625754042819432085121964460731766539354495))
(.branch 5917
(.leaf (720, 717, 478438996591322013689506501706194691752575))
(.leaf (720, 717, 130331464438758431954993505070839274275199)))))
(.branch 5921
(.branch 5919
(.leaf (719, 712, 1209448253871487113765660418391603655892523834697150216055774118271))
(.branch 5920
(.leaf (719, 711, 2404191360815479780917260495915414129816640163213777418912127))
(.leaf (719, 699, 5043687087692225886796518552845913968133907981462512607779485279836258984806572947584250398689679943046625793127941755))))
(.branch 5923
(.branch 5922
(.leaf (714, 699, 384187504556954831766934507224474382423515929218102114048836304525629860215022268386105687596167050468029565436287))
(.leaf (713, 699, 230275783739875453545544107518042057677408352986270062085794583827162715835698393824386407081538220247842818032255)))
(.branch 5924
(.leaf (701, 699, 847733444479324962691352128266805037976918554731497796896940450775653400499264620243889527992992381157065319514495))
(.leaf (701, 698, 20892031586941373090530416034625937590324072538995368033617977006801430178114208911039729303935)))))))
(.branch 5937
(.branch 5931
(.branch 5928
(.branch 5926
(.leaf (701, 698, 572421951626202792147843260819717937558404631308689222141333641570510603933946005415724677))
(.branch 5927
(.leaf (701, 698, 30345161171478753286301127934335))
(.leaf (700, 698, 50627258975847502938683138311809))))
(.branch 5929
(.leaf (700, 698, 30350421207720040371553357070719))
(.branch 5930
(.leaf (700, 698, 213044992031270186956423859995263))
(.leaf (700, 698, 8171136682284308568551326079)))))
(.branch 5934
(.branch 5932
(.leaf (700, 697, 30345158753627329666874922303871))
(.branch 5933
(.leaf (700, 697, 111870628500554627843966382314613))
(.leaf (700, 697, 30360052719724766288475393753471))))
(.branch 5935
(.leaf (699, 694, 14250306515983962936515864612034964048159179135))
(.branch 5936
(.leaf (699, 694, 8542185162619942704491556243856245991422230656))
(.leaf (699, 694, 14294908005046603889227030318583325058818376063))))))
(.branch 5943
(.branch 5940
(.branch 5938
(.leaf (696, 694, 304894989725393950323652911812958096392831))
(.branch 5939
(.leaf (696, 694, 130331464438757196432807448409016159437183))
(.leaf (696, 689, 263694509600163798344800324209504466832064422986716272299692065151))))
(.branch 5941
(.leaf (696, 689, 1309514008539475606134491636204712349213146161807488))
(.branch 5942
(.leaf (696, 689, 559769422005736886976506880282691525493092683284863))
(.leaf (691, 689, 933908087744072426729184156139078891947519266194047)))))
(.branch 5946
(.branch 5944
(.leaf (691, 689, 559929764363716975420589853572935580376830381654399))
(.branch 5945
(.leaf (691, 688, 159284315048170328971163593254648940227104241442638594431))
(.leaf (691, 688, 91192078141000033526487153836160))))
(.branch 5948
(.branch 5947
(.leaf (691, 688, 30345161171478753286301934420351))
(.leaf (690, 688, 50627258886473027847701470840963)))
(.branch 5949
(.leaf (690, 688, 30345467029711259621195411161471))
(.leaf (690, 680, 3451030734480304297000300124722373038907536653758216536493111281387645))))))))
(.branch 5975
(.branch 5962
(.branch 5956
(.branch 5953
(.branch 5951
(.leaf (690, 680, 577574505599430651478236307673544744391491060978891617503690752383))
(.branch 5952
(.leaf (690, 680, 157561072468198689715574586735857490311580102087945662958502084736))
(.leaf (682, 680, 368595425031310968916762722638654478678311951032669828185388548479))))
(.branch 5954
(.leaf (682, 679, 10326133069859353658926311845817456163712880654204556312542035272794495))
(.branch 5955
(.leaf (682, 660, 561490665747250882150999914324478030342256142476402840668731093971000904280915252958685798685406639076901488950833632955914452018756065352740478047569441340785023))
(.leaf (682, 658, 4247881602755992343931118618356342847722580400448868776449935037377407925837519177642051053870864360377876498234882093441950500717438)))))
(.branch 5959
(.branch 5957
(.leaf (681, 658, 29711993259069517244435958616841748674860146463862961867409081617110664988055703226172449164753366511991291300426049373996678415122815))
(.branch 5958
(.leaf (662, 651, 22056036477034262665005548653385006197165642593548775232031189136599763226449553377482506823133078432829805979170931844018000915363173115850930576465102044905859055999))
(.leaf (660, 650, 5306213225563145947384795035410135557850632841581259236546556704928230627043450385187653790471066352483578514787035038559065660571114592675389125557053188833278644577042815))))
(.branch 5960
(.leaf (660, 650, 257295016023878191901194165327057689138658964761453810586767603670481153758032709444705199917804948360500180374363965288041232551836967438178872875955618255295597183104))
(.branch 5961
(.leaf (653, 650, 1129025601892637604648510074098145433044454239689908610597369371705863963007))
(.leaf (652, 650, 157561072468199812148832056869298548888617676550833801048163816306))))))
(.branch 5968
(.branch 5965
(.branch 5963
(.leaf (652, 650, 3741879767539783355334449546887843192387870328297937767809591345535))
(.branch 5964
(.leaf (652, 641, 1129025600316655615706461627839927213839874147505556431952106196814797996415))
(.leaf (652, 641, 120457199269901526802384372241120214594279919582328108692669710487979137))))
(.branch 5966
(.leaf (652, 641, 10326133892611485104176312985259611410066103174341135382171631346516351))
(.branch 5967
(.leaf (643, 622, 785557661165644506198498466145183239147077316493169374462909463689833402959189933709197932853538989301892082291840269532308253851884882114408363585052103541850495))
(.leaf (643, 612, 491866049563839258945946846676603002911820035571752462862018351302077783117243200245018668121125265378716171138326013719115188728466324482771308740828940649279043199487436018790230450257546352013149489418142592)))))
(.branch 5971
(.branch 5969
(.leaf (643, 612, 1153230659707714088694653220625330386053162963196181882246973195769124882528583434381764317918860356522282174818549349871711159178959008215217104407243163653969669619098871211845129895497261282596572863292768639))
(.branch 5970
(.leaf (624, 608, 8026563559849716543649364364902516011696821094041130893281836216508068543402778866639865628350860403549101675317231482929068964100394292778876084007412387893997036283178353672990796743295))
(.leaf (614, 608, 406862060172262158098056138703301224271118772828096404340615445839214721072897909572240316760294776596023216979043544497787514198449193140023807743483216306224880513969221833834010509695))))
(.branch 5973
(.branch 5972
(.leaf (614, 580, 1483987097783125376695848456799725083096054111626832912750371337924062886159310953124559341207823222768548526968808082603966168408919993271131910656045889922040059947843695780701313199657631052483777978392769756376125704828514160273239581422570552286652706536324438175311372173437120396971794414395949494507371773565013366))
(.leaf (610, 580, 81586935170027957746602980397656716999501349633280092536338226892544834972050820481142895900877726576014777336109838854347442323424077442014957631081024820914121528356797558803580566971385665973971763298866731799741019819025170815)))
(.branch 5974
(.leaf (610, 580, 6208222353702553894552791023320832197764660490276158323498615267921687876669898070354282409309727004822771932470697602113835115634151040094037755479858611212586409037016031431689604))
(.leaf (582, 580, 10390092698311132437888688929801665716900824978162752479274235673448638614313229111125969120837815624204217696650660045298653178041156661188867722457871310409569424577127352891474303)))))))
(.branch 5987
(.branch 5981
(.branch 5978
(.branch 5976
(.leaf (582, 579, 22056264058806133169295234420202160669195219394347723794829210011041741692313863208445379246567582357665299092669438293961250791831446688061598679321215290317828194687))
(.branch 5977
(.leaf (582, 579, 36913024487619154874301085461800306510760690456826170268822697423389688611587791532847334643722291253960345864606852510054501593604528484934523362532235922154077488000))
(.leaf (582, 579, 30345158753627114057042728321407))))
(.branch 5979
(.leaf (581, 563, 10577669259490254262890660375522633968010960869628596651086782583820406579019896875383918819933782009599426688))
(.branch 5980
(.leaf (581, 563, 3515163606859806320003935933708411789404476491952360476558726650200297854703775898557499372616283499947622783))
(.leaf (581, 559, 108139168978625627865797222079114582139218031290446079230126788622973272061168460671669634715200030467598607344253091957658551166)))))
(.branch 5984
(.branch 5982
(.leaf (565, 559, 17530909513684583137885074548714546151010761136372182231961108870698253056918873832649838381552042915453936936724874800398719))
(.branch 5983
(.leaf (565, 559, 989158208306173852449523668769981042588985076141603147250773016102436272241522833123527455312603386997008956612295671087743))
(.leaf (561, 559, 1655237263515299757685671153323343262537074824872119021962840565796935770360974166295946848819302072293815529675688999911807))))
(.branch 5985
(.leaf (561, 550, 190479663850079158274436820142241816124538702510146815365304104820747840321986882948563327))
(.branch 5986
(.leaf (561, 549, 338995569606873403761920651675193003527045727574522101056724485051217614305380927661975065788799))
(.leaf (561, 549, 676719707293492706659723231462912837112085489050549733812774429284582228096))))))
(.branch 5993
(.branch 5990
(.branch 5988
(.leaf (552, 549, 1129025600633003866043934120442088830326601614568764468950904446265371525503))
(.branch 5989
(.leaf (551, 549, 676905919645125923727772528880329413539316026933191858297067376210735989377))
(.leaf (551, 549, 2033651297483188391621347993426735996844760515702371508958003134130342789503))))
(.branch 5991
(.leaf (551, 549, 50627258900658574044777867577475))
(.branch 5992
(.leaf (551, 549, 154749570193516920286806399))
(.leaf (551, 549, 463054006768832165430887039)))))
(.branch 5996
(.branch 5994
(.leaf (551, 549, 774928515871150044027552127))
(.branch 5995
(.leaf (551, 546, 130331464438757507126741716052302721253759))
(.leaf (551, 535, 37514245033461193740088297991824620036631547820257272457268510171880922004835333095486209786239))))
(.branch 5998
(.branch 5997
(.leaf (551, 532, 3513729610288610260866920448348793797834280808832343441942688698977859953213492407682670489236618195928940927))
(.leaf (548, 531, 384187503625780955231641282475696469493439569157407723677378969126342604152702787810859828157383231401698470330751)))
(.branch 5999
(.leaf (537, 530, 15091813701755888151060120195075690235411617422748437851874526760644653505493959476666019348062084134492412473830736255))
(.leaf (534, 530, 5043687068922233215178483319101604248720638056770534465691692608872898368441021884936060069289350400130126517400174720)))))))))

def rowDataBlock60 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 6050
(.branch 6025
(.branch 6012
(.branch 6006
(.branch 6003
(.branch 6001
(.leaf (533, 530, 232234351066798970034932426141550138151053197772254117479686136489158821923161827857066331991814357123455))
(.branch 6002
(.leaf (532, 530, 2424639757735501965462873222906505942049251775152256))
(.leaf (532, 530, 15254998518000285872978292622823063935))))
(.branch 6004
(.leaf (532, 525, 61204600432753442028191707979399478212716090846926012799))
(.branch 6005
(.leaf (532, 525, 2051956840215441155610683838891727151177335417279374))
(.leaf (532, 525, 559826333507483537126764697196817220089182987157887)))))
(.branch 6009
(.branch 6007
(.leaf (527, 524, 1485084519839772427543760326493631366461517249466326843775))
(.branch 6008
(.leaf (527, 524, 36685045917565132843951646361517316309785881074265424511))
(.leaf (527, 524, 12260524107767098148054695467880519779568921838702559615))))
(.branch 6010
(.leaf (526, 523, 15265383109251146855572147327876792703))
(.branch 6011
(.leaf (526, 523, 1988740888896928054176139088857333888))
(.leaf (526, 523, 664644343053629415205189831890108799))))))
(.branch 6018
(.branch 6015
(.branch 6013
(.leaf (525, 519, 933908089917455904232856484235346567709289418261119))
(.branch 6014
(.leaf (525, 519, 559837929894989426314493009485088598814316543607167))
(.leaf (525, 500, 103318647002603216434049832837979777272874323961758197136835567067017562012025502835652702470493425937447506315437131555190198607733115076739455))))
(.branch 6016
(.leaf (521, 492, 221609485199223020536560246832958176732581573751019755656361817836028053487371384129275698566324571825441474080578413510519397854542978555667340759149273918082369900513287144320))
(.branch 6017
(.leaf (521, 492, 94729955348247007511023551093689698666017516891372710285583835895487779377857763370832842640361968782490102021584121011426319752845344101615528051735008582874386939889504551295))
(.leaf (502, 492, 347747989935706705989280628623731569344644272675193240288141124664716409023535038011717882269102527404630895073150609484298631537300586604512547012110612963793704834298789429376)))))
(.branch 6021
(.branch 6019
(.leaf (494, 492, 5135636233247087678198769404973697632385597608976585522107530312328721476754178405233939983101393970582917186637907883097841829538669464337763764085406499199))
(.branch 6020
(.leaf (494, 492, 84026810655738991602190086564488480010276446894168720843620393196531790970587564657071614962621887850848584904099691667017561310256059347898651131097200394881))
(.leaf (494, 492, 262871757835368106381734178954220219653698230642877169820372173183))))
(.branch 6023
(.branch 6022
(.leaf (494, 492, 463020950203472981520220799))
(.leaf (494, 492, 1699756768095610369669923199)))
(.branch 6024
(.leaf (494, 491, 30345158753627258453705881616767))
(.leaf (494, 491, 50785715206760743298139932262528)))))))
(.branch 6037
(.branch 6031
(.branch 6028
(.branch 6026
(.leaf (494, 491, 30346090835434036936136426783103))
(.branch 6027
(.leaf (493, 488, 14250306515994347529924658183433846839724802431))
(.leaf (493, 488, 8541403534023125308840980835489494769002807424))))
(.branch 6029
(.leaf (493, 488, 145490192018646468390878057555061153273051414911))
(.branch 6030
(.leaf (490, 488, 304214424950036516229806916731134921343615))
(.leaf (490, 488, 130331464438768942356069450266716330262911)))))
(.branch 6034
(.branch 6032
(.leaf (490, 488, 2911457920116438390315909610608012172395137))
(.branch 6033
(.leaf (490, 488, 1699756767661575955481035135))
(.leaf (490, 488, 463035117302909465763184768))))
(.branch 6035
(.leaf (490, 488, 772510664089494447529591167))
(.branch 6036
(.leaf (490, 482, 36685418600482391227620157038023992967396379640761091460))
(.leaf (490, 482, 61396162392555552676923048712186091860853778872057004415))))))
(.branch 6043
(.branch 6040
(.branch 6038
(.leaf (490, 482, 36688053687934324961292181682222536529497207460501324670))
(.branch 6039
(.leaf (484, 482, 1481827966815387812228027742117271305236227639019741118847))
(.leaf (484, 482, 36685048840568234642314924514414388143052776321509687937))))
(.branch 6041
(.leaf (484, 482, 85628748320247394169075456485063546151884860450775499135))
(.branch 6042
(.leaf (484, 482, 463039858116140772804723327))
(.leaf (484, 482, 1391480684596875713417576831)))))
(.branch 6046
(.branch 6044
(.leaf (484, 482, 463030376489673743495279962))
(.branch 6045
(.leaf (484, 482, 774928515944052063029100927))
(.leaf (484, 482, 463035117302898483531809919))))
(.branch 6048
(.branch 6047
(.leaf (484, 482, 772510664231920785711759743))
(.leaf (484, 482, 463030413383161882324447094)))
(.branch 6049
(.leaf (484, 482, 2636674278872845782332998015))
(.leaf (484, 482, 463214493442277836576457345))))))))
(.branch 6075
(.branch 6062
(.branch 6056
(.branch 6053
(.branch 6051
(.leaf (484, 482, 2017704258219660478976950655))
(.branch 6052
(.leaf (484, 482, 463035117302922737212129919))
(.leaf (484, 482, 154749570265293039280849279))))
(.branch 6054
(.leaf (484, 471, 44349499203492419502842512726581270439529596079111486699932642488959108472963455))
(.branch 6055
(.leaf (484, 471, 74223405934630467456004387675452517443311424141908624727779222981515272666416000))
(.leaf (484, 471, 44350850841496763930895855786554218103040032327145387059708456375617318805897599)))))
(.branch 6059
(.branch 6057
(.leaf (473, 471, 73991822005373582056310314173429736389608678656640975100688246942023824367879042))
(.branch 6058
(.leaf (473, 471, 44349502737186548236859162664445529376568471430241641487606574368759674289258879))
(.leaf (473, 461, 410892225516593969369508375095823379014362375795321960237626182636637332821262110983698317935162629960565785349967324111767011967))))
(.branch 6060
(.leaf (473, 461, 1579571602464549112019954717996024612787441817727718497472506114739366068607))
(.branch 6061
(.leaf (473, 457, 12483274255432226200359858278578055948760926102637657823268655125314088139284336438632144372863))
(.leaf (463, 457, 54201643741857193646589989454443858580714592303842627778346523727456019820697518802522391773567))))))
(.branch 6068
(.branch 6065
(.branch 6063
(.leaf (463, 457, 12483403062151581255247110174632469051663711790205291265999987879283603186831350651508576157824))
(.branch 6064
(.leaf (459, 457, 20826846301707635827419593167449529081825021264235959046176479011476449616769898673631173542271))
(.leaf (459, 457, 8542100432310579390814389354713843764398326401))))
(.branch 6066
(.leaf (459, 457, 71518620184496952059699941701460827709687005567))
(.branch 6067
(.leaf (459, 457, 463186196136865463294427775))
(.leaf (459, 457, 1080786748233651225395790207)))))
(.branch 6071
(.branch 6069
(.leaf (459, 454, 130331464438757196432806074529654901768575))
(.branch 6070
(.leaf (459, 453, 14294908007736213662565832124057536734259315071))
(.leaf (459, 452, 559906214776784673818857060378575950542570418471295))))
(.branch 6073
(.branch 6072
(.leaf (456, 452, 933908087918296998552139829946883342982166714712703))
(.leaf (455, 452, 559769422005739540240203449698594308428045121225087)))
(.branch 6074
(.leaf (454, 451, 12260524107767098149378731166804482973349365807407300991))
(.leaf (454, 451, 43558131666362657458871617124392161443968)))))))
(.branch 6087
(.branch 6081
(.branch 6078
(.branch 6076
(.leaf (454, 451, 7321168916003554518983016564895318399))
(.branch 6077
(.leaf (453, 451, 50627258895880867327496660385920))
(.leaf (453, 451, 30345161171478897120014260502911))))
(.branch 6079
(.leaf (453, 447, 1685119933602359949156373300122256657028660045218688))
(.branch 6080
(.leaf (453, 447, 20026199521068974037221888859972425019029389695))
(.leaf (453, 447, 8541402853458350981373027972236208529033081220)))))
(.branch 6084
(.branch 6082
(.leaf (449, 447, 19981598041295352163498656899977467309366247807))
(.branch 6083
(.leaf (449, 447, 8541665211163611553704062807783623095725523072))
(.leaf (449, 447, 14250306513335891542066228703771931116186894719))))
(.branch 6085
(.leaf (449, 447, 463039821222642768435675777))
(.branch 6086
(.leaf (449, 447, 3248390742587352978612552063))
(.leaf (449, 447, 463336942929438033953358463))))))
(.branch 6093
(.branch 6090
(.branch 6088
(.leaf (449, 447, 2323562490654500728757485951))
(.branch 6089
(.leaf (449, 445, 1988700324077716010022088526155171214))
(.leaf (449, 445, 3328292651599730552992212258614673791))))
(.branch 6091
(.leaf (449, 444, 130332788474455502634905888064402148491647))
(.branch 6092
(.leaf (447, 444, 217442421244408763258798663935596372623488))
(.leaf (447, 444, 130331474823350911084609476751557251891583)))))
(.branch 6096
(.branch 6094
(.leaf (446, 422, 399602058953008122797737008520001628156687871182041838798701744086314572015201373595477528720807423340904526292287338634880369718469531035171226498))
(.branch 6095
(.leaf (446, 422, 278403420240445819934435942546647450636919979525711658242807677503956960558255529153011321879859979977936860759761236956854494439023772031))
(.leaf (446, 422, 464454192793818408306678523290902543497903159458293851797893126467531886747052427701934640832756286916441900178075216700877719593820291200))))
(.branch 6098
(.branch 6097
(.leaf (424, 422, 15637921891707096518226919926835297261034941782274226621201864199891062409782137091740527061293413502375433630134420461544536409178495))
(.leaf (424, 422, 4248054894611895108089021019610687685329643366325471977116754707379845648543503228354282723274860185956105817827287496479824886562944)))
(.branch 6099
(.leaf (424, 422, 7109189913260272728437319269401026125889601398321591403271452031475705228944299041298910185420928397504804323681936004735025354375551))
(.leaf (424, 414, 157562685683346182131709156709230271402707177062699771006451385216)))))))))

def rowDataBlock61 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 6150
(.branch 6125
(.branch 6112
(.branch 6106
(.branch 6103
(.branch 6101
(.leaf (424, 414, 367772672752458804193791245609032872254454491793372120810356932991))
(.branch 6102
(.leaf (424, 414, 157573915418349290864417394080452558067095771537385975149227870588))
(.leaf (416, 414, 3831971142151199100763582288075870498224630582235041760871192854911))))
(.branch 6104
(.leaf (416, 414, 157561072468199439465915498106176204713542598563475804069761581697))
(.branch 6105
(.leaf (416, 414, 263694509526699793354541777039338753401296115095131298855617823103))
(.leaf (416, 414, 463072896234765834445063040)))))
(.branch 6109
(.branch 6107
(.leaf (416, 414, 154749570193516920219631999))
(.branch 6108
(.leaf (416, 414, 463035080409412539430929023))
(.leaf (416, 414, 774928515728160756361134463))))
(.branch 6110
(.leaf (416, 414, 463030376489700123184411044))
(.branch 6111
(.leaf (416, 414, 1391480683515448852878393727))
(.leaf (416, 414, 463030413383213735464600448))))))
(.branch 6118
(.branch 6115
(.branch 6113
(.leaf (416, 414, 772510664303696904873116031))
(.branch 6114
(.leaf (416, 414, 463035154196388825679200897))
(.leaf (416, 414, 2935278955307726972064432511))))
(.branch 6116
(.leaf (416, 414, 463020950203455380744246389))
(.branch 6117
(.leaf (416, 414, 15295336535047132704340509055))
(.leaf (416, 414, 463020950203452077914391167)))))
(.branch 6121
(.branch 6119
(.leaf (416, 414, 774928515728723705862160767))
(.branch 6120
(.leaf (416, 414, 463030376489685825238276731))
(.leaf (416, 414, 3253226445938150564039688575))))
(.branch 6123
(.branch 6122
(.leaf (416, 414, 463030413383159687596148357))
(.leaf (416, 414, 772510664161270566523765119)))
(.branch 6124
(.leaf (416, 414, 463049192168628918647980673))
(.leaf (416, 414, 4500837891708671753477226879)))))))
(.branch 6137
(.branch 6131
(.branch 6128
(.branch 6126
(.leaf (416, 414, 463086860420031831598895476))
(.branch 6127
(.leaf (416, 414, 154749570193516920286675327))
(.leaf (416, 414, 463054043662320312849990271))))
(.branch 6129
(.leaf (416, 414, 774928515727597805955580287))
(.branch 6130
(.leaf (416, 411, 130331464438756576253860612787838197498239))
(.leaf (416, 411, 392347557923059228218571529035063962307201)))))
(.branch 6134
(.branch 6132
(.leaf (416, 411, 130331474823350293323515653676048742023551))
(.branch 6133
(.leaf (413, 411, 217442421183165393743462484972500055687809))
(.leaf (413, 411, 130332788474456120395999639363791412396415))))
(.branch 6135
(.leaf (413, 411, 305575554195485274301818424759547234025600))
(.branch 6136
(.leaf (413, 411, 1393898535370850893408829823))
(.leaf (413, 411, 463115379086365397109118061))))))
(.branch 6143
(.branch 6140
(.branch 6138
(.leaf (413, 411, 774928515655821686961209727))
(.branch 6139
(.leaf (413, 411, 463020950203453181720986239))
(.leaf (413, 411, 1391480683731058685038887295))))
(.branch 6141
(.leaf (413, 407, 8541402853458432190239609944675933297194241145))
(.branch 6142
(.leaf (413, 407, 248608837806018245831677652958235962189637812607))
(.leaf (413, 393, 230444915501811933889720853491667707853985494358602271570838422097075689126918884841098345173546750469026627918212)))))
(.branch 6146
(.branch 6144
(.leaf (409, 393, 384187503590085023386429944033663676246199890885384380476774232243321746795377243440334089431561086492445335683455))
(.branch 6145
(.leaf (409, 391, 989036928931101331894519894912642940620139449666135358546628021675164579714568473371819217122456603786832261072531190907778))
(.leaf (395, 391, 6269717795807513358164397697707670735648713263502302118658488890164306067663643168622353766800488036335394809031136296632703))))
(.branch 6148
(.branch 6147
(.leaf (395, 389, 230282838541620417712290333919328203459694892564394225879593989468765415102773549491876548216606976549040483665025))
(.leaf (393, 389, 76960557369750455216622306160250062833323683493975216515855257712085037534436565827301551656491027450138556629375)))
(.branch 6149
(.leaf (393, 374, 15093504953028971601966665529722205017800675566897477501419763154360204658454820957484031804415496673716873052706242943))
(.leaf (391, 361, 10357674615665872651736119281235288060063897467653011667768330572994335869569931098819284715186810649512344871503652880507080340458413375118809471327977901177837209370681126932251007))))))))
(.branch 6175
(.branch 6162
(.branch 6156
(.branch 6153
(.branch 6151
(.leaf (391, 361, 1445464406558910519584875114987915264313988774707980293577135439065349194191151186089584259673869471572599874873011846467318120702994656830455064755633651878086007404298368))
(.branch 6152
(.leaf (376, 361, 4343852820543232442786986822469253291408837099184069449407200291514102298245169795213854511810862758211280720110584792941533289777497822759323689859351208678107159352770943))
(.leaf (363, 361, 336562137753189293941828270705764404267760661394911023385008301118131087253874001228260730027272762118406892431343775300863825863994198490164055210698177664451201))))
(.branch 6154
(.leaf (363, 361, 563248054001641502529436363465374127882943260005933868016744962618302412295155402784112320024363436255838747171219041161159759462236344366780334951922762032021887))
(.branch 6155
(.leaf (363, 361, 63660280749464074494870736733003269547860494670660821548160492484092156952554712086806656))
(.leaf (363, 361, 2012868556677902568047772031)))))
(.branch 6159
(.branch 6157
(.leaf (363, 354, 2404240209110839194434617644986240408386267879912772411982207))
(.branch 6158
(.leaf (363, 352, 17281483374716028308569311423455929756017153352519635019530548507771778))
(.leaf (363, 352, 10326766589113775107899521570910307374983556845678025144094280275329407))))
(.branch 6160
(.leaf (356, 345, 125426523690947515605548181190524285374737311004670870713590811372537674211110049384583841824519243497855))
(.branch 6161
(.leaf (354, 309, 13260682463623337200695983571369793712326309500134953289121529646359295632523618120761987799444876090412532526008763108726637063813663458913176562972631144420026904942963252006112502343641190567623980078301250069155984620769318604436684469002485979329915440643768554412629230462))
(.leaf (354, 309, 48679170842582475012575175211116838671341318499724895826136891537498997845489865714193047641829625014621231038125788057344202096638804346872663060791958649684096731913283724385427770022885403629773894472023701368768313529688262051855510259972180265427285636144525834789517328767))))))
(.branch 6168
(.branch 6165
(.branch 6163
(.leaf (347, 309, 4260900192652534123727546342566396497696073249208268806096341539787902960413796146760452183639113221472002989364495120768753382915273423027109750395766741562913707817575501556312581079219216364493426850476455732019228073128707783656013912015487))
(.branch 6164
(.leaf (311, 309, 594629567109568556018380876965272430929200562200698425205875171366010929588284525807292153559223728487170888948247181748599039190230193563685838352279528081273537606039416207489710739137934341907133133921392039229733280646905053839743))
(.leaf (311, 309, 995173171974654751128251040992144775748203616856005352772914423628371305961997850759905499510341080596300842139478427631525988096668999280013567996679596423155602228261686438374393049962784026845936069248104688457372864195503868281730))))
(.branch 6166
(.leaf (311, 309, 191065372691370024805830822018244533071573673154520948502598500185731165648913644731886995355035550511178453819101286902596231059587462124379093748462000048329471262730691226920551463051831265665679743))
(.branch 6167
(.leaf (311, 309, 463030413383166263191078017))
(.leaf (311, 309, 772510663872758715496333695)))))
(.branch 6171
(.branch 6169
(.leaf (311, 309, 463020950203452069324456577))
(.branch 6170
(.leaf (311, 309, 1393898535299074774330900863))
(.leaf (311, 309, 463035154196389920895873675))))
(.branch 6173
(.branch 6172
(.leaf (311, 309, 154749570193516920219631999))
(.leaf (311, 309, 463096600300898360785568383)))
(.branch 6174
(.leaf (311, 309, 774928517895518076648161663))
(.leaf (311, 309, 463030376489675942518522752)))))))
(.branch 6187
(.branch 6181
(.branch 6178
(.branch 6176
(.leaf (311, 309, 1699756767732789124588831103))
(.branch 6177
(.leaf (311, 309, 463030413383159687596147839))
(.leaf (311, 309, 772510664088931497676439935))))
(.branch 6179
(.leaf (311, 309, 463214641016226019616424577))
(.branch 6180
(.leaf (311, 309, 1704592470940034472280260991))
(.leaf (311, 309, 463035080409413643237524352)))))
(.branch 6184
(.branch 6182
(.leaf (311, 309, 154749570193516920939610495))
(.branch 6183
(.leaf (311, 306, 130334133279342483334207067428648992637311))
(.leaf (311, 305, 14294908005056988482944099974200392546338668927))))
(.branch 6185
(.leaf (311, 305, 8541402853458350981373018490609753555696812930))
(.branch 6186
(.leaf (308, 305, 19936996548239834925645753717408383683646194047))
(.leaf (307, 293, 53615258946054871285229176874206276998865558489101433689700700938895506567249798627020117578841719767681))))))
(.branch 6193
(.branch 6190
(.branch 6188
(.leaf (307, 293, 89450623828285393868923746303884156395152476185903942380017057889725772299044710739402763195327562318207))
(.branch 6189
(.leaf (307, 293, 317792454554865048581137974646561829462040561706203689869852517312924111558448252767371392))
(.leaf (295, 293, 8734465814154727557478703190674259175613935600472450068140161506573549296463636332927))))
(.branch 6191
(.leaf (295, 285, 989037086539196371922041202950679794185619299147350729321581963092228390508748361661958902538445185955481831272816295477887))
(.branch 6192
(.leaf (295, 285, 2308546482363459455917082595808119180613727863570920471516939582134684139513312924310393385758674871896616120774325490942335))
(.leaf (295, 285, 157562685683344684092530979986307391103757311822472640667773240192)))))
(.branch 6196
(.branch 6194
(.leaf (287, 285, 369418177309780009995276572614359457497002430634092954407814496639))
(.branch 6195
(.leaf (287, 285, 157561085022403279999190309198506845574798016998532350129175729024))
(.leaf (287, 285, 2675592814567568683514652714399797000721880549927240272052442235263))))
(.branch 6198
(.branch 6197
(.leaf (287, 285, 463020950203452069324456830))
(.leaf (287, 285, 7299501164909453302114091391)))
(.branch 6199
(.leaf (287, 282, 130331474823352763158965342536234814210431))
(.leaf (287, 254, 1866356654980453372986070436645974327731122915492235184603080003357508443559893203640710033917536111695002254721149302941815486284299247031833249714957337520852201483882203124618)))))))))

def rowDataBlock62 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 6250
(.branch 6225
(.branch 6212
(.branch 6206
(.branch 6203
(.branch 6201
(.leaf (287, 254, 94737684423290119491134689304084996839024986865070084192669409011296220963884221382921009548526431010613135901618909807805839980459611777014342973124846846706788516181164622207))
(.branch 6202
(.leaf (284, 254, 284678737560065049807271476780268968237669524478105043058008411195248692440889519393680043062191977263663121433670205756564809462786580543423211034965221559987650801767827833985))
(.leaf (256, 254, 94729955348245659594275849285839994056408242776782045768310867520118341831669732580559996030905691754782538781999319709456115107318884408562319235036580483562234124741967217023))))
(.branch 6204
(.leaf (256, 253, 109881212133352357050588106802957530962177529602402401076875536390338643435619263215161164405960088274894040908323631574846280913115728818478269638979395684446709647795955881767666047))
(.branch 6205
(.leaf (256, 251, 158540232823466192058385193035615461887240736426360193752175667943418458853460865931044617236797960005020502475317251272901008518036463936526243839463613434564404525716473840767))
(.leaf (256, 251, 130372509545423294066264146924270602158463)))))
(.branch 6209
(.branch 6207
(.leaf (255, 247, 5636874043423156890622501988599627325845596570033286929121919))
(.branch 6208
(.leaf (253, 247, 2404215784963156644330914956762259174716125684303597225574783))
(.leaf (253, 247, 4023658898546828689136021167410067996270072765589746781978752))))
(.branch 6210
(.leaf (249, 247, 61204600444171423564532859639063351080726335182266630527))
(.branch 6211
(.leaf (249, 247, 8541402853458411987058154584830166122012543356))
(.leaf (249, 247, 2854625804574252459963825542447676727287153023))))))
(.branch 6218
(.branch 6215
(.branch 6213
(.leaf (249, 246, 30345161171478897120014260633983))
(.branch 6214
(.leaf (249, 243, 19981598049229181772296804913824514186797973887))
(.leaf (249, 243, 8542101112875272747100031260438473100360614527))))
(.branch 6216
(.leaf (248, 243, 20026199519744938337675328869234843688487551359))
(.branch 6217
(.leaf (245, 243, 8542362109450761954130318586880161363255034497))
(.leaf (245, 243, 25668288060321251758324580950491641633589625215)))))
(.branch 6221
(.branch 6219
(.leaf (245, 243, 217442421162962212213024390825309819045252))
(.branch 6220
(.leaf (245, 243, 772510664088931497509126527))
(.leaf (245, 239, 8541577078030254987457347119645789126790152320))))
(.branch 6223
(.branch 6222
(.leaf (245, 239, 14294908034383081155057961313324264744426013055))
(.leaf (245, 239, 8542973596864058033320356056851669153308672639)))
(.branch 6224
(.leaf (241, 239, 59788428208725039399653693495117125921433321855))
(.leaf (241, 237, 36685048840568234642314924514414411847118898943655608961)))))))
(.branch 6237
(.branch 6231
(.branch 6228
(.branch 6226
(.leaf (241, 237, 208132610418957226342282590428319053799472877537706639743))
(.branch 6227
(.leaf (241, 237, 1988700482534031575371030720304579199))
(.leaf (239, 237, 3317908038697008141958847712586957183))))
(.branch 6229
(.leaf (239, 232, 2404215784963156599729424570085606608714342882013967630467455))
(.branch 6230
(.leaf (239, 232, 5636874043426079894944893202185445768170823111004273738973825))
(.leaf (239, 232, 559911901466810299127760624240036587791417284100479)))))
(.branch 6234
(.branch 6232
(.leaf (234, 232, 933908087744752991422461213599470205847743187845759))
(.branch 6233
(.leaf (234, 232, 559769422005739540240203449698594524037877281718655))
(.leaf (234, 225, 971378805080601448132319085944457557707991380991040855257693022903923711284606861695))))
(.branch 6235
(.leaf (234, 225, 4023658898177068772804010690472346427543135503548740748116864))
(.branch 6236
(.leaf (234, 225, 2405516394772483823099110092686882380436777811379069596270975))
(.leaf (227, 201, 158045572168401078982443685991755136552955519002855418063451999736459001621678738902307965904876513371206046470677604886478467759734089068030346694041723009762686553200500081538))))))
(.branch 6243
(.branch 6240
(.branch 6238
(.leaf (227, 201, 94729962896169383630213409894343046425525154028289244049198300151200628743368811105330680645537570354366648937545134946890707604067468322629322374776727508591284376076059410815))
(.branch 6239
(.leaf (227, 201, 222104146119760038711583869604406445962153896969338598969188860085405042864070083059532110293637059897312023275635681822303230189603187147398599346537692512002857407830669853311))
(.leaf (203, 201, 128088380373008219531575921964526758403420189888712328413610224477935998374873967650027296138738064063290379810361753253432063723936848352969087))))
(.branch 6241
(.leaf (203, 184, 138453610811054704661351013319738912061448873029720522708546405359903391760145118658186565546010600956762576949355632981068228381656811781064207988331745590007482826331520750310530089814546618290636195884440339498954274046335))
(.branch 6242
(.leaf (203, 184, 416781388630758784808277618110194789574902302470616938327382552602246227590029575986029895483083535986081302797644789651052540438920354958411850511209566669328283442791449606713552460965834425156313923828544567197874123636864))
(.leaf (203, 184, 3513765586188531491846962906485670796203591079415633393549504845834480418645038961352393796809655795429802367)))))
(.branch 6246
(.branch 6244
(.leaf (186, 177, 30438469970384769903250738861647024893368914933010007569103564807055640029028180214826754898896975376284205167094420246868945044679532977586559))
(.branch 6245
(.leaf (186, 169, 6208475620033662238423475810780932252284112734772948840511032530851360496817054257608234920740635579922087465014427880819648713913316543547126768137750062950830411953833300633520775))
(.leaf (186, 169, 68612983028999462829708822516813991369196139946470985874153076881275568874899653457689930652893159737230178805323454439802888331948853494425388674797412319310954626602143046149538175))))
(.branch 6248
(.branch 6247
(.leaf (179, 169, 1913856867459390867798747682634999978115414812753750473225939364882794936700659547792648456290369664))
(.leaf (171, 169, 818195935630140587964217363525215958500112128706987791777832790441479241910006682894432159948996991)))
(.branch 6249
(.leaf (171, 169, 1369180174189270065097204467797243345656647002594837966825099717627734012938513629989219158177284737))
(.leaf (171, 169, 263694509526508231411933540930699155135301448200464948382828331391))))))))
(.branch 6275
(.branch 6262
(.branch 6256
(.branch 6253
(.branch 6251
(.leaf (171, 169, 463054043662321399476715648))
(.branch 6252
(.leaf (171, 169, 9736695616459067759092040063))
(.leaf (171, 169, 463044525142378278721356415))))
(.branch 6254
(.leaf (171, 169, 774928515511987974584336767))
(.branch 6255
(.leaf (171, 169, 463030376489677020555314821))
(.leaf (171, 169, 1083204599729328245488681343)))))
(.branch 6259
(.branch 6257
(.leaf (171, 169, 463030413383162994720964736))
(.branch 6258
(.leaf (171, 169, 772510664304822804646199679))
(.leaf (171, 169, 463053969875344009421849217))))
(.branch 6260
(.leaf (171, 169, 154749570194079870859215231))
(.branch 6261
(.leaf (171, 169, 463035080409414738454185087))
(.leaf (171, 169, 1083204599657552126444437887))))))
(.branch 6268
(.branch 6265
(.branch 6263
(.leaf (171, 169, 463020950203452077914391167))
(.branch 6264
(.leaf (171, 169, 774928515871150044933587327))
(.leaf (171, 168, 30345158753627330229824975864191))))
(.branch 6266
(.leaf (171, 168, 70830440327573540448102487360641))
(.branch 6267
(.leaf (171, 168, 30345161171478753286301127934335))
(.leaf (170, 168, 50627258938363718927046439535488)))))
(.branch 6271
(.branch 6269
(.leaf (170, 168, 30345780141498539810151660061055))
(.branch 6270
(.leaf (170, 168, 10141667832239218378253996589695))
(.leaf (170, 168, 154749570265855989234270591))))
(.branch 6273
(.branch 6272
(.leaf (170, 168, 463030376489674830121992833))
(.leaf (170, 168, 1085622451297344334730297727)))
(.branch 6274
(.leaf (170, 168, 463054043662322503283311488))
(.leaf (170, 168, 772510664881283558056853887)))))))
(.branch 6287
(.branch 6281
(.branch 6278
(.branch 6276
(.leaf (170, 168, 463233419801693055939969152))
(.branch 6277
(.leaf (170, 168, 774928515728160756832076159))
(.leaf (170, 168, 463035154196386630950926463))))
(.branch 6279
(.leaf (170, 168, 1391480683659282565977670015))
(.branch 6280
(.leaf (170, 166, 1988700482534078780589114247830505083))
(.leaf (170, 166, 20582295093631168238108607402425188735)))))
(.branch 6284
(.branch 6282
(.leaf (170, 164, 8541402853458350981373004415744026419115532652))
(.branch 6283
(.leaf (168, 164, 54324745635095421323692094321863770017762378111))
(.leaf (168, 158, 676740493412381127047429685456284166729375395472519844371986002542227033717))))
(.branch 6285
(.leaf (166, 158, 1129025601051784776668925956411106360824601931840162207078723250678954721663))
(.branch 6286
(.leaf (166, 158, 157561072468199812148831882304444237396775667747242830355610153573))
(.leaf (160, 158, 473496340609577711411850451494163062831327975557422437081815187839))))))
(.branch 6293
(.branch 6290
(.branch 6288
(.leaf (160, 155, 10326027346191447691723362463566648138634908944190323959894166036611455))
(.branch 6289
(.leaf (160, 149, 1369180174443899562109256661646700954697292927019860055657149234028104042547602443978247794948244097))
(.leaf (160, 149, 10325923268028147989802917149204244069201464765180314210602271074877823))))
(.branch 6291
(.leaf (157, 149, 86460706620402983753430515477499013665774431663091938697221679817359488))
(.branch 6292
(.leaf (151, 149, 10325922445276065775972040862449177985880989666718163782279836744024447))
(.leaf (151, 142, 2199710123015302749455224719376708365195467706026429289767894253590233372193201675873131368741806943371647)))))
(.branch 6296
(.branch 6294
(.leaf (151, 142, 63660280808749624143020070602475086646499186841991105348611340662232520343179715414005889))
(.branch 6295
(.leaf (151, 142, 2404191169253520045708838076339768945478386531370557266395519))
(.leaf (144, 142, 5611765639844525435239450735291566291526218231178561780121728))))
(.branch 6298
(.branch 6297
(.leaf (144, 142, 2404191360815656112909546601588293796883162815913034808099199))
(.leaf (144, 142, 4011104697335536856922086029874215657384696499079324853273474)))
(.branch 6299
(.leaf (144, 142, 1085622451873805087083987327))
(.leaf (144, 132, 676760956011914349887388659393279327194702957098265022497764761649857626753)))))))))

def rowDataBlock63 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 6350
(.branch 6325
(.branch 6312
(.branch 6306
(.branch 6303
(.branch 6301
(.leaf (144, 132, 1583105295963877635175963760567458001400785477877108752537064151955055575423))
(.branch 6302
(.leaf (144, 132, 676733456866292953486019258467944241664263953073416222652896662214722650751))
(.leaf (134, 132, 22765834755696828278766381289320439481783778408698209823468665274591296291199))))
(.branch 6304
(.leaf (134, 132, 676719653373602592511663068530297359757952076059842707117487913540438131584))
(.branch 6305
(.leaf (134, 132, 1132559302127016280895887080510039681743013668250399596921397677919657984383))
(.leaf (134, 132, 463096489620495542719022721)))))
(.branch 6309
(.branch 6307
(.leaf (134, 132, 772510664088931497542746495))
(.branch 6308
(.leaf (134, 132, 463030413383161882324435072))
(.leaf (134, 132, 154749570769414722888401279))))
(.branch 6310
(.leaf (134, 132, 463035080409415842260779649))
(.branch 6311
(.leaf (134, 132, 154749570193516920437080447))
(.leaf (134, 132, 463086860420028545948910207))))))
(.branch 6318
(.branch 6315
(.branch 6313
(.leaf (134, 132, 2935278955379503091125649791))
(.branch 6314
(.leaf (134, 132, 463030376489673743495267708))
(.leaf (134, 132, 774928515511987973778243967))))
(.branch 6316
(.leaf (134, 132, 463049192168631117671236480))
(.branch 6317
(.leaf (134, 132, 772510666319620687974695295))
(.leaf (134, 132, 463030413383161882324445554)))))
(.branch 6321
(.branch 6319
(.leaf (134, 132, 154749570265855989468561791))
(.branch 6320
(.leaf (134, 128, 8542970194040551320897033475342313123351560831))
(.leaf (134, 128, 25668288054973185993409902770039685097258484095))))
(.branch 6323
(.branch 6322
(.leaf (134, 125, 2404706949783992721427731960774796372439409797772149193179519))
(.leaf (130, 125, 5636874069211353281760484280494763678494194824495668519703679)))
(.branch 6324
(.leaf (130, 125, 2404191169253531485991130234269126214251578637831461710791039))
(.leaf (127, 125, 4023658897804385855284630446371288527038917372315120628085116)))))))
(.branch 6337
(.branch 6331
(.branch 6328
(.branch 6326
(.leaf (127, 125, 130334133279342480916359100040461884195199))
(.branch 6327
(.leaf (127, 124, 14294908005067373077587206806922252991760564607))
(.leaf (127, 120, 5438256134431775238416572532010448721274759144211328))))
(.branch 6329
(.leaf (127, 120, 559769422005736886976513707086794745470328915296639))
(.branch 6330
(.leaf (126, 120, 2803168681803525255465648882319178914488431027356546))
(.leaf (122, 120, 559775108695792991067968189090124420253306251641215)))))
(.branch 6334
(.branch 6332
(.leaf (122, 117, 367772672752650365929849979694172789474343297295113900824629150079))
(.branch 6333
(.leaf (122, 117, 4011104696942392916479392580204984386405644479212012024300671))
(.leaf (122, 117, 130331474823350293323515869848830822318463))))
(.branch 6335
(.leaf (119, 117, 391666993026324249185910687401455705326209))
(.branch 6336
(.leaf (119, 117, 130332809243644792475349438303101591224703))
(.leaf (119, 117, 2735191654010985903402126496907392228196991))))))
(.branch 6343
(.branch 6340
(.branch 6338
(.leaf (119, 117, 1704592471083586710335979903))
(.branch 6339
(.leaf (119, 116, 30345158753627258453705881878911))
(.leaf (119, 116, 50785715206760743298139932263294))))
(.branch 6341
(.leaf (119, 116, 30352292624888659983802837696895))
(.branch 6342
(.leaf (118, 116, 50627258891140054100553305620608))
(.leaf (118, 116, 30345161171478897120014227210623)))))
(.branch 6346
(.branch 6344
(.leaf (118, 116, 70830440360759233052064773767807))
(.branch 6345
(.leaf (118, 116, 18135103285538913842702123391))
(.leaf (118, 116, 463030376489675933928596894))))
(.branch 6348
(.branch 6347
(.leaf (118, 116, 3554248974806020446427742591))
(.leaf (118, 116, 463049265955619528612184705)))
(.branch 6349
(.leaf (118, 116, 772510664017155378498240895))
(.leaf (118, 116, 463020950203452069324456834))))))))
(.branch 6375
(.branch 6362
(.branch 6356
(.branch 6353
(.branch 6351
(.leaf (118, 116, 1085622451514361541807899007))
(.branch 6352
(.leaf (118, 116, 463035117302900686850033022))
(.leaf (118, 116, 774928515655821687112270207))))
(.branch 6354
(.leaf (118, 116, 463020950203471920663298687))
(.branch 6355
(.leaf (118, 116, 154749570265293039314469247))
(.leaf (118, 111, 559769377404286423870399588570546080019756496191871)))))
(.branch 6359
(.branch 6357
(.leaf (118, 111, 6186544972660467223173387032624350535149460800865407))
(.branch 6358
(.leaf (118, 111, 559775108695762512285408592069796513130043064451455))
(.leaf (113, 111, 933908087657980988524960718292700088484159505236607))))
(.branch 6360
(.leaf (113, 111, 559775064094274768487860411332202238853798336463231))
(.branch 6361
(.leaf (113, 111, 187080751069342164974423322440032111658627428713344))
(.leaf (113, 111, 5746031486055292041345040767))))))
(.branch 6368
(.branch 6365
(.branch 6363
(.leaf (113, 111, 463020950203457562587628161))
(.branch 6364
(.leaf (113, 111, 772510664017155378565349759))
(.leaf (113, 111, 463200160322128157618407039))))
(.branch 6366
(.leaf (113, 111, 1080786749243583441884021119))
(.branch 6367
(.leaf (113, 111, 463365535382748972338578304))
(.leaf (113, 111, 774928515655821686843900287)))))
(.branch 6371
(.branch 6369
(.leaf (113, 111, 463044525142380477744611967))
(.branch 6370
(.leaf (113, 111, 3241137187742004272292757887))
(.leaf (113, 66, 2553914543970416037724639854501917178509155258677216856586264531476463698070224033760940423338783186124006986452688205933801553711416645222445910533873835156624059223706068348577860916620851125289971027683385415199173377812869816486412995002751))))
(.branch 6373
(.branch 6372
(.leaf (113, 50, 1284012337459563782372918900430889260140317955936105492972796371240275080831562946383232108429318406645168730618747757597120291885860961861670449493667424850176996707587996586668466438413717174365475067398157891797844319640064839884667419340491133009108485177830628130034851050736795381320291209412450954727009116837840001))
(.leaf (113, 50, 295813864390637041105119539462835364683856030889902065046906088582982028294165196118973902487689749907762088115471096154985189116419043106981510916929003700284516975404706150059519287163910170714946065319065312201353529166859294539806008354793097660754949697012856648186531550263523362853544412472736066905377377653686655)))
(.branch 6374
(.leaf (68, 48, 2119044673632155329943830728375285895184319781939145733431568016425897301312745195498764554992484762094695781618954492396031780869270865368488180154576077122758711162647745295328614432898502958723994877379949893541815909989529527709229399713744991083762816852542284961405750162314685880009102429026928468232465659204965385776335491))
(.leaf (52, 48, 1270146954009724535936742370304177818200188887845147744356851618050479267629535270738959636688360904287612320901865218540301508658801905659465430162299459514190882472572846234352754153607213042105061161263566993807606529853020062826994852698253073349818657400789574583715465004035431857009647142999192032102821561417277689783255423)))))))
(.branch 6387
(.branch 6381
(.branch 6378
(.branch 6376
(.leaf (52, 48, 2977929730039468765490507346429618923310874865273415075133679425459782620428654235526043241380615921664750657749157141605789763105246078559569207846162694459703746194045284687872904814029036585116414101502842846226321642359390658586030134668333551402958666080453328948104031287689664431957055430527567971965507262527813084430402432))
(.branch 6377
(.leaf (50, 48, 1614297743461008196070260036110643016714267991155034789782904294818149774883453468809428057059702991173614791819647))
(.leaf (50, 48, 1988700324077815530206339719302677378))))
(.branch 6379
(.leaf (50, 48, 664644343364323350989983242250158463))
(.branch 6380
(.leaf (50, 48, 463030413383164081347691135))
(.leaf (50, 48, 2627002872314239899024753023)))))
(.branch 6384
(.branch 6382
(.leaf (50, 47, 30345158753628766315156053492095))
(.branch 6383
(.leaf (50, 47, 111712172175526099168779294409602))
(.leaf (50, 47, 30345467029711115787482278396287))))
(.branch 6385
(.leaf (49, 47, 50627258881732214625160457552513))
(.branch 6386
(.leaf (49, 47, 30346396693666543271030961537407))
(.leaf (49, 47, 50785715343432670143539650167423))))))
(.branch 6393
(.branch 6390
(.branch 6388
(.leaf (49, 47, 154749570626988384404373887))
(.branch 6389
(.leaf (49, 41, 36685045917564872527940748940268586686708547980789482111))
(.leaf (49, 41, 61396162392510951185191567173880957595058063988234453375))))
(.branch 6391
(.leaf (49, 41, 36685421523485492005136496845838814466885320073788983927))
(.branch 6392
(.leaf (43, 41, 61204600495307032302115507108145445762065473950166483327))
(.leaf (43, 41, 36685048840568146509181993641084856967068060063222399617)))))
(.branch 6396
(.branch 6394
(.leaf (43, 41, 331211158544793526769594781885088043309731174420502806911))
(.branch 6395
(.leaf (43, 41, 463106266394792976000683390))
(.leaf (43, 41, 1391480683731058685005267327))))
(.branch 6398
(.branch 6397
(.leaf (43, 41, 463035117302900686850033020))
(.leaf (43, 41, 774928515655821686843900287)))
(.branch 6399
(.leaf (43, 41, 463044525142394715561198207))
(.leaf (43, 41, 17436344162161664674934882687)))))))))

def rowDataBlock64 : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 6421
(.branch 6410
(.branch 6405
(.branch 6402
(.branch 6401
(.leaf (43, 41, 463030376489678141541777536))
(.leaf (43, 41, 154749570480621396497990015)))
(.branch 6403
(.leaf (43, 41, 463035117302901790656627329))
(.branch 6404
(.leaf (43, 41, 772510664017155378666668415))
(.leaf (43, 41, 463020950203452069324459657)))))
(.branch 6407
(.branch 6406
(.leaf (43, 41, 1080786747874489154995749247))
(.leaf (43, 41, 463091822594183270011700094)))
(.branch 6408
(.leaf (43, 41, 774928515655821686894363007))
(.branch 6409
(.leaf (43, 41, 463035117302907249560060543))
(.leaf (43, 41, 9741531320027445501685203327))))))
(.branch 6415
(.branch 6412
(.branch 6411
(.leaf (43, 40, 30345158753627114057042812338559))
(.leaf (43, 37, 42772959648758041702338352472435962189826818431)))
(.branch 6413
(.leaf (43, 37, 8541751983166811864236517838091250300903949182))
(.branch 6414
(.leaf (42, 37, 14250306513335891537734647491875979051030020479))
(.leaf (39, 27, 12483402067504042685284513158670789651845024773777126537766277026947734870500968485628090974849)))))
(.branch 6418
(.branch 6416
(.leaf (39, 27, 62643120827787303996235127049863683788014361671316871023790637393552820832141150043334494519679))
(.branch 6417
(.leaf (39, 27, 572421951596675809523757370985859106393032713563426233155098420622690270913307285395538559))
(.leaf (29, 27, 1583105296070424055335880075810259994991760731876581824911033057971490193791))))
(.branch 6419
(.leaf (29, 27, 676719653373602592511635763295206845842438215018793730828353713831199840385))
(.branch 6420
(.leaf (29, 27, 1132559294656014214518281347827106606913872602180157025443577342286788231551))
(.leaf (29, 27, 463096415833458727496647552)))))))
(.branch 6431
(.branch 6426
(.branch 6423
(.branch 6422
(.leaf (29, 27, 772510664232483735665181055))
(.leaf (29, 27, 463030413383161882324435072)))
(.branch 6424
(.leaf (29, 27, 4799442569225261278455398783))
(.branch 6425
(.leaf (29, 27, 463082562328659354443514497))
(.leaf (29, 27, 5418412588795612346940785023)))))
(.branch 6428
(.branch 6427
(.leaf (29, 27, 463176419362503098697187967))
(.leaf (29, 27, 2935278955451842160073113983)))
(.branch 6429
(.leaf (29, 20, 2404191169253531485991134237530005381334793772385896325120383))
(.branch 6430
(.leaf (29, 20, 4023658897804385855284630446269559566370601962845010195842687))
(.leaf (29, 20, 2404289823653963287304098892998222816031506116423989063582079))))))
(.branch 6436
(.branch 6433
(.branch 6432
(.leaf (22, 17, 1129025600949352117090856267396577019704860033909201478095144328754328830335))
(.leaf (22, 17, 676719707293495914258711136490041764897875663917749785181260776005305305729)))
(.branch 6434
(.leaf (22, 17, 226166750636150389106864563448027653888619330876345175675784257167534588287))
(.branch 6435
(.leaf (19, 16, 54324745635085036730288136453959800000304185727))
(.leaf (19, 5, 818112237895950792195131803072729845780926692286810839454151305675278855961518876964607710174642559)))))
(.branch 6439
(.branch 6437
(.leaf (19, 0, 4294296638612292161111213075623066705935383075885156544678501985184106589049786053950837588407970773741305006415329286291839))
(.branch 6438
(.leaf (18, 0, 17632470979356573336920048091567869516532839352542876624778761971794697561236939417316809777002511808667256188))
(.leaf (7, 0, 3513729330320534208632629389584128413199405224913513842716753846086728346654279854582826054050641614399799679))))
(.branch 6440
(.leaf (-1, 0, 5880584067206438078489667680664758766838459578398737756261593239458658039544947846847670901855113965981338492))
(.branch 6441
(.leaf (-1, 0, 268770187198768462194351961979107285406615171665053942115731468970289025103097932971214590501867457741183))
(.leaf (-1, 0, 9508538193878388408978844000399175643620452488643456))))))))

def rowData : Lean.RArray (ℤ × ℤ × ℕ) :=
(.branch 3200 (.branch 1600 (.branch 800 (.branch 400 (.branch 200 (.branch 100 rowDataBlock0 rowDataBlock1) (.branch 300 rowDataBlock2 rowDataBlock3)) (.branch 600 (.branch 500 rowDataBlock4 rowDataBlock5) (.branch 700 rowDataBlock6 rowDataBlock7))) (.branch 1200 (.branch 1000 (.branch 900 rowDataBlock8 rowDataBlock9) (.branch 1100 rowDataBlock10 rowDataBlock11)) (.branch 1400 (.branch 1300 rowDataBlock12 rowDataBlock13) (.branch 1500 rowDataBlock14 rowDataBlock15)))) (.branch 2400 (.branch 2000 (.branch 1800 (.branch 1700 rowDataBlock16 rowDataBlock17) (.branch 1900 rowDataBlock18 rowDataBlock19)) (.branch 2200 (.branch 2100 rowDataBlock20 rowDataBlock21) (.branch 2300 rowDataBlock22 rowDataBlock23))) (.branch 2800 (.branch 2600 (.branch 2500 rowDataBlock24 rowDataBlock25) (.branch 2700 rowDataBlock26 rowDataBlock27)) (.branch 3000 (.branch 2900 rowDataBlock28 rowDataBlock29) (.branch 3100 rowDataBlock30 rowDataBlock31))))) (.branch 4800 (.branch 4000 (.branch 3600 (.branch 3400 (.branch 3300 rowDataBlock32 rowDataBlock33) (.branch 3500 rowDataBlock34 rowDataBlock35)) (.branch 3800 (.branch 3700 rowDataBlock36 rowDataBlock37) (.branch 3900 rowDataBlock38 rowDataBlock39))) (.branch 4400 (.branch 4200 (.branch 4100 rowDataBlock40 rowDataBlock41) (.branch 4300 rowDataBlock42 rowDataBlock43)) (.branch 4600 (.branch 4500 rowDataBlock44 rowDataBlock45) (.branch 4700 rowDataBlock46 rowDataBlock47)))) (.branch 5600 (.branch 5200 (.branch 5000 (.branch 4900 rowDataBlock48 rowDataBlock49) (.branch 5100 rowDataBlock50 rowDataBlock51)) (.branch 5400 (.branch 5300 rowDataBlock52 rowDataBlock53) (.branch 5500 rowDataBlock54 rowDataBlock55))) (.branch 6000 (.branch 5800 (.branch 5700 rowDataBlock56 rowDataBlock57) (.branch 5900 rowDataBlock58 rowDataBlock59)) (.branch 6200 (.branch 6100 rowDataBlock60 rowDataBlock61) (.branch 6300 rowDataBlock62 (.branch 6400 rowDataBlock63 rowDataBlock64)))))))

def height (r : ℕ) : ℤ := if r ≤ radius then (rowData.getImpl r).1 else -1

def divisor (z : GaussianInt) : GaussianInt :=
  let d := rowData.getImpl z.re.toNat
  let c := (d.2.2 >>> (16*(z.im-d.2.1).toNat)) % 65536
  ⟨(c/256 : ℕ),(c%256 : ℕ)-128⟩

def Blocked (z : GaussianInt) : Prop :=
  z.norm ≤ 1 ∨
    1 < (divisor z).norm ∧ (divisor z).norm < z.norm ∧
    ((divisor z).re*z.re+(divisor z).im*z.im) % (divisor z).norm = 0 ∧
    ((divisor z).re*z.im-(divisor z).im*z.re) % (divisor z).norm = 0

instance (z : GaussianInt) : Decidable (Blocked z) :=
  inferInstanceAs (Decidable (_ ∨ _))

lemma prime_not_blocked {z : GaussianInt} (hz : Prime z) : ¬ Blocked z := by
  rintro (h | ⟨ha,haz,hr,hi⟩)
  · have hp : 0 < z.norm := GaussianInt.norm_pos.mpr hz.ne_zero
    have he : z.norm = 1 := by omega
    exact hz.not_unit ((Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) z).mp he)
  · exact not_prime_of_small_divisor
      (gaussian_divisor_of_congruences (divisor z) z (by omega)
        (Int.dvd_of_emod_eq_zero hr) (Int.dvd_of_emod_eq_zero hi)) ha haz hz

def InsideOctant (z : GaussianInt) : Prop :=
  0 ≤ z.im ∧ z.im ≤ z.re ∧ z.im ≤ height z.re.toNat

instance (z : GaussianInt) : Decidable (InsideOctant z) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Inside (z : GaussianInt) : Prop := InsideOctant (OctantReduction.fold z)

instance (z : GaussianInt) : Decidable (Inside z) :=
  inferInstanceAs (Decidable (InsideOctant _))

def lower (r : ℕ) : ℤ := height (r+3)-2

def width (r : ℕ) : ℕ := (height r-lower r+1).toNat

def RowCheck (r : Fin (radius+1)) : Prop :=
  height (r.val+1) ≤ height r.val ∧
    ∀ s : Fin (width r.val),
      let z : GaussianInt := ⟨(r.val : ℤ),lower r.val+(s.val : ℤ)⟩
      InsideOctant z → ∀ a b : Fin 7,
        ((a.val : ℤ)-3)^2+((b.val : ℤ)-3)^2 < 16 →
        let w : GaussianInt := ⟨z.re+((a.val : ℤ)-3),z.im+((b.val : ℤ)-3)⟩
        OctantReduction.InOctant w → InsideOctant w ∨ Blocked z ∨ Blocked w

instance (r : Fin (radius+1)) : Decidable (RowCheck r) :=
  by unfold RowCheck; dsimp; unfold OctantReduction.InOctant; infer_instance

end Erdos952Investigation.Staircase16
