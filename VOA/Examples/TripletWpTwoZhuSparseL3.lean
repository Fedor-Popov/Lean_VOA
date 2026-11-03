/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseL4

/-! # Efficient single-Virasoro certificate for the L(-3) Zhu ledger family -/

namespace VOA.LatGen.WpTwoZhuSparseCompute
open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
set_option maxRecDepth 100000

def l3Entry0SparseQ : SparseRational.Poly ℕ :=
  scaleQ (1547 / 192) (virVacCircleSparseQ 3 0 (vacuumSparseQ))
def l3Entry1SparseQ : SparseRational.Poly ℕ :=
  scaleQ (11413 / 192) (virVacCircleSparseQ 3 2 (reifyVirWordSparseQ [2]))
def l3Entry2SparseQ : SparseRational.Poly ℕ :=
  scaleQ (66329 / 768) (virVacCircleSparseQ 3 3 (reifyVirWordSparseQ [3]))
def l3Entry3SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-26243 / 128) (virVacCircleSparseQ 3 4 (reifyVirWordSparseQ [4]))
def l3Entry4SparseQ : SparseRational.Poly ℕ :=
  scaleQ (31109 / 128) (virVacCircleSparseQ 3 4 (reifyVirWordSparseQ [2, 2]))
def l3Entry5SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-5743 / 48) (virVacCircleSparseQ 3 5 (reifyVirWordSparseQ [5]))
def l3Entry6SparseQ : SparseRational.Poly ℕ :=
  scaleQ (88649 / 384) (virVacCircleSparseQ 3 5 (reifyVirWordSparseQ [3, 2]))
def l3Entry7SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-1959 / 64) (virVacCircleSparseQ 3 6 (reifyVirWordSparseQ [6]))
def l3Entry8SparseQ : SparseRational.Poly ℕ :=
  scaleQ (-3197 / 128) (virVacCircleSparseQ 3 6 (reifyVirWordSparseQ [4, 2]))
def l3Entry9SparseQ : SparseRational.Poly ℕ :=
  scaleQ (30359 / 512) (virVacCircleSparseQ 3 6 (reifyVirWordSparseQ [3, 3]))
def l3Entry10SparseQ : SparseRational.Poly ℕ :=
  scaleQ (25 / 4) (virVacCircleSparseQ 3 6 (reifyVirWordSparseQ [2, 2, 2]))

-- 5 canonical terms; sorted and zero-free
def l3Entry0ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 1], (1547 / 256)), ([0, 2], (1547 / 384)), ([1, 1], (1547 / 768)), ([2], (1547 / 128)),
    ([3], (1547 / 128))]
-- 16 canonical terms; sorted and zero-free
def l3Entry1ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 1], (11413 / 2048)), ([0, 0, 0, 2], (11413 / 3072)), ([0, 0, 1, 1], (11413 / 6144)), ([0, 0, 2], (11413 / 1024)),
    ([0, 0, 3], (11413 / 1024)), ([0, 1], (-11413 / 768)), ([0, 1, 1], (11413 / 1024)), ([0, 1, 2], (11413 / 1536)),
    ([0, 3], (11413 / 256)), ([0, 4], (11413 / 384)), ([1, 1, 1], (11413 / 3072)), ([1, 2], (11413 / 512)),
    ([1, 3], (11413 / 512)), ([2], (-11413 / 384)), ([4], (11413 / 128)), ([5], (11413 / 192))]
-- 18 canonical terms; sorted and zero-free
def l3Entry2ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 1, 1], (66329 / 4096)), ([0, 0, 1, 2], (66329 / 6144)), ([0, 1, 1, 1], (66329 / 12288)), ([0, 1, 2], (66329 / 1024)),
    ([0, 1, 3], (66329 / 2048)), ([0, 2], (-66329 / 1536)), ([0, 2, 2], (66329 / 3072)), ([0, 4], (66329 / 512)),
    ([0, 5], (66329 / 768)), ([1, 1], (-66329 / 3072)), ([1, 1, 2], (66329 / 6144)), ([1, 3], (66329 / 1024)),
    ([1, 4], (66329 / 1536)), ([2, 2], (66329 / 1024)), ([2, 3], (66329 / 1024)), ([3], (-66329 / 512)),
    ([5], (198987 / 512)), ([6], (66329 / 256))]
-- 22 canonical terms; sorted and zero-free
def l3Entry3ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 1, 2], (-78729 / 2048)), ([0, 0, 2, 2], (-26243 / 1024)), ([0, 1, 1, 1], (-78729 / 4096)), ([0, 1, 1, 2], (-26243 / 1024)),
    ([0, 1, 3], (-236187 / 2048)), ([0, 2, 2], (-78729 / 1024)), ([0, 2, 3], (-78729 / 512)), ([0, 3], (78729 / 512)),
    ([0, 5], (-236187 / 512)), ([0, 6], (-78729 / 256)), ([1, 1, 1, 1], (-26243 / 4096)), ([1, 1, 2], (-78729 / 2048)),
    ([1, 1, 3], (-78729 / 1024)), ([1, 2], (78729 / 512)), ([1, 4], (-78729 / 256)), ([1, 5], (-26243 / 128)),
    ([2, 3], (-393645 / 1024)), ([2, 4], (-26243 / 256)), ([3, 3], (-236187 / 1024)), ([4], (78729 / 128)),
    ([6], (-236187 / 128)), ([7], (-78729 / 64))]
-- 39 canonical terms; sorted and zero-free
def l3Entry4ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 1], (93327 / 32768)), ([0, 0, 0, 0, 0, 2], (31109 / 16384)), ([0, 0, 0, 0, 1, 1], (31109 / 32768)), ([0, 0, 0, 0, 2], (93327 / 16384)),
    ([0, 0, 0, 0, 3], (93327 / 16384)), ([0, 0, 0, 1], (-31109 / 2048)), ([0, 0, 0, 1, 1], (93327 / 8192)), ([0, 0, 0, 1, 2], (31109 / 4096)),
    ([0, 0, 0, 3], (93327 / 2048)), ([0, 0, 0, 4], (31109 / 1024)), ([0, 0, 1, 1, 1], (31109 / 8192)), ([0, 0, 1, 2], (279981 / 4096)),
    ([0, 0, 1, 3], (93327 / 4096)), ([0, 0, 2], (-31109 / 1024)), ([0, 0, 2, 2], (31109 / 1024)), ([0, 0, 4], (93327 / 1024)),
    ([0, 0, 5], (31109 / 512)), ([0, 1, 1], (-31109 / 1024)), ([0, 1, 1, 1], (93327 / 8192)), ([0, 1, 1, 2], (93327 / 4096)),
    ([0, 1, 3], (93327 / 512)), ([0, 1, 4], (31109 / 512)), ([0, 2, 2], (93327 / 1024)), ([0, 2, 3], (155545 / 1024)),
    ([0, 3], (-93327 / 512)), ([0, 5], (279981 / 512)), ([0, 6], (93327 / 256)), ([1, 1, 1, 1], (31109 / 8192)),
    ([1, 1, 2], (93327 / 4096)), ([1, 1, 3], (217763 / 4096)), ([1, 2], (-31109 / 256)), ([1, 4], (93327 / 512)),
    ([1, 5], (31109 / 256)), ([2, 3], (93327 / 256)), ([2, 4], (31109 / 256)), ([3, 3], (93327 / 512)),
    ([4], (-31109 / 64)), ([6], (93327 / 64)), ([7], (31109 / 32))]
-- 27 canonical terms; sorted and zero-free
def l3Entry5ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 1, 3], (-5743 / 256)), ([0, 0, 2, 3], (-5743 / 384)), ([0, 1, 1, 2], (-5743 / 256)), ([0, 1, 1, 3], (-5743 / 768)),
    ([0, 1, 2, 2], (-5743 / 384)), ([0, 1, 4], (-5743 / 64)), ([0, 2, 3], (-5743 / 128)), ([0, 2, 4], (-5743 / 96)),
    ([0, 3, 3], (-5743 / 128)), ([0, 4], (5743 / 48)), ([0, 6], (-5743 / 16)), ([0, 7], (-5743 / 24)),
    ([1, 1, 1, 2], (-5743 / 768)), ([1, 1, 4], (-5743 / 192)), ([1, 2, 2], (-5743 / 128)), ([1, 2, 3], (-5743 / 128)),
    ([1, 3], (5743 / 48)), ([1, 5], (-17229 / 64)), ([1, 6], (-5743 / 32)), ([2, 2], (5743 / 96)),
    ([2, 4], (-5743 / 16)), ([2, 5], (-5743 / 48)), ([3, 3], (-5743 / 64)), ([3, 4], (-5743 / 24)),
    ([5], (28715 / 48)), ([7], (-28715 / 16)), ([8], (-28715 / 24))]
-- 49 canonical terms; sorted and zero-free
def l3Entry6ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 1, 1], (88649 / 16384)), ([0, 0, 0, 0, 1, 2], (88649 / 24576)), ([0, 0, 0, 1, 1, 1], (88649 / 49152)), ([0, 0, 0, 1, 2], (88649 / 4096)),
    ([0, 0, 0, 1, 3], (88649 / 8192)), ([0, 0, 0, 2], (-88649 / 6144)), ([0, 0, 0, 2, 2], (88649 / 12288)), ([0, 0, 0, 4], (88649 / 2048)),
    ([0, 0, 0, 5], (88649 / 3072)), ([0, 0, 1, 1], (-88649 / 4096)), ([0, 0, 1, 1, 1], (88649 / 8192)), ([0, 0, 1, 1, 2], (88649 / 8192)),
    ([0, 0, 1, 3], (443245 / 4096)), ([0, 0, 1, 4], (88649 / 2048)), ([0, 0, 2, 2], (88649 / 4096)), ([0, 0, 2, 3], (620543 / 12288)),
    ([0, 0, 3], (-88649 / 2048)), ([0, 0, 5], (265947 / 2048)), ([0, 0, 6], (88649 / 1024)), ([0, 1, 1, 1, 1], (88649 / 24576)),
    ([0, 1, 1, 2], (88649 / 2048)), ([0, 1, 1, 3], (443245 / 12288)), ([0, 1, 2], (-88649 / 1024)), ([0, 1, 2, 2], (88649 / 6144)),
    ([0, 1, 4], (265947 / 1024)), ([0, 1, 5], (88649 / 768)), ([0, 2, 3], (88649 / 512)), ([0, 2, 4], (88649 / 768)),
    ([0, 3, 3], (88649 / 1024)), ([0, 4], (-88649 / 384)), ([0, 6], (88649 / 128)), ([0, 7], (88649 / 192)),
    ([1, 1, 1], (-88649 / 6144)), ([1, 1, 1, 2], (88649 / 12288)), ([1, 1, 3], (88649 / 2048)), ([1, 1, 4], (88649 / 1536)),
    ([1, 2, 2], (88649 / 2048)), ([1, 2, 3], (88649 / 2048)), ([1, 3], (-443245 / 3072)), ([1, 5], (265947 / 1024)),
    ([1, 6], (88649 / 512)), ([2, 2], (-88649 / 1536)), ([2, 4], (88649 / 256)), ([2, 5], (88649 / 768)),
    ([3, 3], (88649 / 512)), ([3, 4], (443245 / 1536)), ([5], (-443245 / 768)), ([7], (443245 / 256)),
    ([8], (443245 / 384))]
-- 33 canonical terms; sorted and zero-free
def l3Entry7ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 1, 4], (-5877 / 1024)), ([0, 0, 2, 4], (-1959 / 512)), ([0, 1, 1, 3], (-5877 / 1024)), ([0, 1, 1, 4], (-1959 / 1024)),
    ([0, 1, 2, 2], (-5877 / 2048)), ([0, 1, 2, 3], (-1959 / 512)), ([0, 1, 5], (-29385 / 1024)), ([0, 2, 2, 2], (-1959 / 1024)),
    ([0, 2, 4], (-5877 / 512)), ([0, 2, 5], (-9795 / 512)), ([0, 3, 4], (-5877 / 512)), ([0, 5], (9795 / 256)),
    ([0, 7], (-29385 / 256)), ([0, 8], (-9795 / 128)), ([1, 1, 1, 3], (-1959 / 1024)), ([1, 1, 2, 2], (-1959 / 2048)),
    ([1, 1, 5], (-9795 / 1024)), ([1, 2, 3], (-5877 / 512)), ([1, 3, 3], (-5877 / 512)), ([1, 4], (9795 / 256)),
    ([1, 6], (-5877 / 64)), ([1, 7], (-1959 / 32)), ([2, 2, 2], (-5877 / 1024)), ([2, 2, 3], (-5877 / 1024)),
    ([2, 3], (9795 / 256)), ([2, 5], (-64647 / 512)), ([2, 6], (-5877 / 128)), ([3, 4], (-17631 / 256)),
    ([3, 5], (-45057 / 512)), ([4, 4], (-1959 / 128)), ([6], (29385 / 128)), ([8], (-88155 / 128)),
    ([9], (-29385 / 64))]
-- 61 canonical terms; sorted and zero-free
def l3Entry8ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 1, 2], (-9591 / 16384)), ([0, 0, 0, 0, 2, 2], (-3197 / 8192)), ([0, 0, 0, 1, 1, 1], (-9591 / 32768)), ([0, 0, 0, 1, 1, 2], (-3197 / 8192)),
    ([0, 0, 0, 1, 3], (-28773 / 16384)), ([0, 0, 0, 2, 2], (-9591 / 8192)), ([0, 0, 0, 2, 3], (-9591 / 4096)), ([0, 0, 0, 3], (9591 / 4096)),
    ([0, 0, 0, 5], (-28773 / 4096)), ([0, 0, 0, 6], (-9591 / 2048)), ([0, 0, 1, 1, 1, 1], (-3197 / 32768)), ([0, 0, 1, 1, 2], (-28773 / 16384)),
    ([0, 0, 1, 1, 3], (-9591 / 8192)), ([0, 0, 1, 2], (15985 / 4096)), ([0, 0, 1, 2, 2], (-3197 / 4096)), ([0, 0, 1, 4], (-9591 / 1024)),
    ([0, 0, 1, 5], (-3197 / 1024)), ([0, 0, 2, 3], (-86319 / 8192)), ([0, 0, 2, 4], (-15985 / 2048)), ([0, 0, 3, 3], (-28773 / 8192)),
    ([0, 0, 4], (9591 / 1024)), ([0, 0, 6], (-28773 / 1024)), ([0, 0, 7], (-9591 / 512)), ([0, 1, 1, 1], (3197 / 4096)),
    ([0, 1, 1, 1, 1], (-9591 / 16384)), ([0, 1, 1, 1, 2], (-3197 / 4096)), ([0, 1, 1, 3], (-47955 / 8192)), ([0, 1, 1, 4], (-3197 / 1024)),
    ([0, 1, 2, 2], (-9591 / 4096)), ([0, 1, 2, 3], (-9591 / 2048)), ([0, 1, 3], (9591 / 1024)), ([0, 1, 5], (-47955 / 2048)),
    ([0, 1, 6], (-9591 / 1024)), ([0, 2, 2], (3197 / 1024)), ([0, 2, 4], (-9591 / 512)), ([0, 2, 5], (-3197 / 256)),
    ([0, 3, 3], (-28773 / 2048)), ([0, 3, 4], (-9591 / 512)), ([0, 5], (15985 / 512)), ([0, 7], (-47955 / 512)),
    ([0, 8], (-15985 / 256)), ([1, 1, 1, 1, 1], (-3197 / 16384)), ([1, 1, 1, 2], (-9591 / 8192)), ([1, 1, 1, 3], (-9591 / 4096)),
    ([1, 1, 2], (3197 / 512)), ([1, 1, 4], (-28773 / 2048)), ([1, 1, 5], (-3197 / 256)), ([1, 2, 3], (-47955 / 4096)),
    ([1, 2, 4], (-3197 / 1024)), ([1, 3, 3], (-28773 / 4096)), ([1, 4], (3197 / 128)), ([1, 6], (-28773 / 512)),
    ([1, 7], (-9591 / 256)), ([2, 3], (9591 / 1024)), ([2, 5], (-9591 / 512)), ([3, 4], (-47955 / 1024)),
    ([3, 5], (-9591 / 256)), ([4, 4], (-3197 / 256)), ([6], (9591 / 128)), ([8], (-28773 / 128)),
    ([9], (-9591 / 64))]
-- 48 canonical terms; sorted and zero-free
def l3Entry9ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 1, 1, 1], (91077 / 32768)), ([0, 0, 0, 1, 1, 2], (30359 / 16384)), ([0, 0, 1, 1, 1, 1], (30359 / 32768)), ([0, 0, 1, 1, 2], (273231 / 16384)),
    ([0, 0, 1, 1, 3], (91077 / 16384)), ([0, 0, 1, 2], (-30359 / 2048)), ([0, 0, 1, 2, 2], (30359 / 4096)), ([0, 0, 1, 4], (273231 / 4096)),
    ([0, 0, 1, 5], (30359 / 1024)), ([0, 0, 2, 4], (30359 / 2048)), ([0, 1, 1, 1], (-30359 / 4096)), ([0, 1, 1, 1, 2], (30359 / 8192)),
    ([0, 1, 1, 3], (273231 / 8192)), ([0, 1, 1, 4], (91077 / 4096)), ([0, 1, 2, 2], (273231 / 8192)), ([0, 1, 2, 3], (30359 / 1024)),
    ([0, 1, 3], (-91077 / 2048)), ([0, 1, 5], (819693 / 4096)), ([0, 1, 6], (91077 / 1024)), ([0, 2, 2], (-30359 / 1024)),
    ([0, 2, 2, 2], (30359 / 4096)), ([0, 2, 4], (273231 / 2048)), ([0, 2, 5], (212513 / 2048)), ([0, 3, 4], (91077 / 2048)),
    ([0, 5], (-151795 / 1024)), ([0, 7], (455385 / 1024)), ([0, 8], (151795 / 512)), ([1, 1, 1, 3], (30359 / 8192)),
    ([1, 1, 2], (-30359 / 2048)), ([1, 1, 2, 2], (30359 / 8192)), ([1, 1, 5], (91077 / 4096)), ([1, 2, 3], (273231 / 4096)),
    ([1, 2, 4], (30359 / 1024)), ([1, 3, 3], (91077 / 4096)), ([1, 4], (-91077 / 1024)), ([1, 6], (91077 / 512)),
    ([1, 7], (30359 / 256)), ([2, 2, 2], (91077 / 4096)), ([2, 2, 3], (91077 / 4096)), ([2, 3], (-30359 / 256)),
    ([2, 5], (819693 / 2048)), ([2, 6], (91077 / 512)), ([3, 4], (91077 / 512)), ([3, 5], (394667 / 2048)),
    ([4, 4], (30359 / 512)), ([6], (-273231 / 512)), ([8], (819693 / 512)), ([9], (273231 / 256))]
-- 83 canonical terms; sorted and zero-free
def l3Entry10ExpectedQ : SparseRational.Poly ℕ :=
  [    ([0, 0, 0, 0, 0, 0, 0, 1], (75 / 8192)), ([0, 0, 0, 0, 0, 0, 0, 2], (25 / 4096)), ([0, 0, 0, 0, 0, 0, 1, 1], (25 / 8192)), ([0, 0, 0, 0, 0, 0, 2], (75 / 4096)),
    ([0, 0, 0, 0, 0, 0, 3], (75 / 4096)), ([0, 0, 0, 0, 0, 1], (-75 / 1024)), ([0, 0, 0, 0, 0, 1, 1], (225 / 4096)), ([0, 0, 0, 0, 0, 1, 2], (75 / 2048)),
    ([0, 0, 0, 0, 0, 3], (225 / 1024)), ([0, 0, 0, 0, 0, 4], (75 / 512)), ([0, 0, 0, 0, 1, 1, 1], (75 / 4096)), ([0, 0, 0, 0, 1, 2], (1125 / 2048)),
    ([0, 0, 0, 0, 1, 3], (225 / 2048)), ([0, 0, 0, 0, 2], (-75 / 512)), ([0, 0, 0, 0, 2, 2], (75 / 256)), ([0, 0, 0, 0, 4], (225 / 512)),
    ([0, 0, 0, 0, 5], (75 / 256)), ([0, 0, 0, 1, 1], (-75 / 256)), ([0, 0, 0, 1, 1, 1], (225 / 2048)), ([0, 0, 0, 1, 1, 2], (225 / 1024)),
    ([0, 0, 0, 1, 3], (225 / 128)), ([0, 0, 0, 1, 4], (75 / 128)), ([0, 0, 0, 2, 2], (225 / 256)), ([0, 0, 0, 2, 3], (375 / 256)),
    ([0, 0, 0, 3], (-225 / 128)), ([0, 0, 0, 5], (675 / 128)), ([0, 0, 0, 6], (225 / 64)), ([0, 0, 1, 1, 1, 1], (75 / 2048)),
    ([0, 0, 1, 1, 2], (1125 / 1024)), ([0, 0, 1, 1, 3], (525 / 1024)), ([0, 0, 1, 2], (-75 / 32)), ([0, 0, 1, 2, 2], (75 / 128)),
    ([0, 0, 1, 4], (675 / 128)), ([0, 0, 1, 5], (75 / 64)), ([0, 0, 2, 3], (225 / 32)), ([0, 0, 2, 4], (375 / 64)),
    ([0, 0, 3, 3], (225 / 128)), ([0, 0, 4], (-75 / 16)), ([0, 0, 6], (225 / 16)), ([0, 0, 7], (75 / 8)),
    ([0, 1, 1, 1], (-75 / 256)), ([0, 1, 1, 1, 1], (75 / 1024)), ([0, 1, 1, 1, 2], (175 / 512)), ([0, 1, 1, 3], (675 / 256)),
    ([0, 1, 1, 4], (225 / 128)), ([0, 1, 2, 2], (375 / 128)), ([0, 1, 2, 3], (375 / 128)), ([0, 1, 3], (-375 / 64)),
    ([0, 1, 5], (1275 / 64)), ([0, 1, 6], (225 / 32)), ([0, 2, 2], (-75 / 32)), ([0, 2, 2, 2], (25 / 32)),
    ([0, 2, 4], (225 / 16)), ([0, 2, 5], (175 / 16)), ([0, 3, 3], (225 / 32)), ([0, 3, 4], (375 / 32)),
    ([0, 5], (-375 / 16)), ([0, 7], (1125 / 16)), ([0, 8], (375 / 8)), ([1, 1, 1, 1, 1], (25 / 1024)),
    ([1, 1, 1, 2], (75 / 512)), ([1, 1, 1, 3], (375 / 512)), ([1, 1, 2], (-225 / 128)), ([1, 1, 2, 2], (25 / 64)),
    ([1, 1, 4], (225 / 128)), ([1, 1, 5], (275 / 64)), ([1, 2, 3], (225 / 32)), ([1, 2, 4], (75 / 32)),
    ([1, 3, 3], (225 / 64)), ([1, 4], (-225 / 16)), ([1, 6], (225 / 8)), ([1, 7], (75 / 4)),
    ([2, 2, 2], (75 / 32)), ([2, 2, 3], (75 / 32)), ([2, 3], (-225 / 16)), ([2, 5], (375 / 8)),
    ([2, 6], (75 / 4)), ([3, 4], (225 / 8)), ([3, 5], (225 / 8)), ([4, 4], (75 / 8)),
    ([6], -75), ([8], 225), ([9], 150)]

macro "close_l3_entry" : tactic => `(tactic|
  (norm_num (config := { maxSteps := 1000000 })
    [l3Entry0ExpectedQ, l3Entry1ExpectedQ, l3Entry2ExpectedQ, l3Entry3ExpectedQ, l3Entry4ExpectedQ, l3Entry5ExpectedQ, l3Entry6ExpectedQ, l3Entry7ExpectedQ, l3Entry8ExpectedQ, l3Entry9ExpectedQ, l3Entry10ExpectedQ, virVacCircleSparseQ, virVacModeSparseQ,
    virVacModeCoefficientQ, omegaSparseQ, voaModeActSparseQ,
    zhuStateActSparseQ, vacuumSparseQ, zhuVir2ExpectedQ, vir3ExpectedQ, zhuVir4ExpectedQ, vir22ExpectedQ, zhuVir5ExpectedQ, vir32ExpectedQ, zhuVir6ExpectedQ, zhuVir42ExpectedQ, zhuVir33ExpectedQ, zhuVir222ExpectedQ,
    aWordActSparseQ, aWordWeightQ, sumSparseIcc, intIccListQ, natRangeQ,
    aFieldActSparseQ, aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ,
    annihilateRawQ, prependRawQ, scaleRawQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply, Int.toNat]))

set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l3Entry0_eq : l3Entry0SparseQ = l3Entry0ExpectedQ := by
  unfold l3Entry0SparseQ
  close_l3_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l3Entry1_eq : l3Entry1SparseQ = l3Entry1ExpectedQ := by
  unfold l3Entry1SparseQ
  rw [reifyZhuVir2SparseQ_eq_expected]
  close_l3_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l3Entry2_eq : l3Entry2SparseQ = l3Entry2ExpectedQ := by
  unfold l3Entry2SparseQ
  rw [reifyVir3SparseQ_eq_expected]
  close_l3_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l3Entry3_eq : l3Entry3SparseQ = l3Entry3ExpectedQ := by
  unfold l3Entry3SparseQ
  rw [reifyZhuVir4SparseQ_eq_expected]
  close_l3_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l3Entry4_eq : l3Entry4SparseQ = l3Entry4ExpectedQ := by
  unfold l3Entry4SparseQ
  rw [reifyVir22SparseQ_eq_expected]
  close_l3_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l3Entry5_eq : l3Entry5SparseQ = l3Entry5ExpectedQ := by
  unfold l3Entry5SparseQ
  rw [reifyZhuVir5SparseQ_eq_expected]
  close_l3_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l3Entry6_eq : l3Entry6SparseQ = l3Entry6ExpectedQ := by
  unfold l3Entry6SparseQ
  rw [reifyVir32SparseQ_eq_expected]
  close_l3_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l3Entry7_eq : l3Entry7SparseQ = l3Entry7ExpectedQ := by
  unfold l3Entry7SparseQ
  rw [reifyZhuVir6SparseQ_eq_expected]
  close_l3_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l3Entry8_eq : l3Entry8SparseQ = l3Entry8ExpectedQ := by
  unfold l3Entry8SparseQ
  rw [reifyZhuVir42SparseQ_eq_expected]
  close_l3_entry
set_option maxHeartbeats 1000000 in
-- One typed ledger column, checked independently.
theorem l3Entry9_eq : l3Entry9SparseQ = l3Entry9ExpectedQ := by
  unfold l3Entry9SparseQ
  rw [reifyZhuVir33SparseQ_eq_expected]
  close_l3_entry
end VOA.LatGen.WpTwoZhuSparseCompute

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuSparseCompute.l3Entry9_eq
end AxiomAudit
