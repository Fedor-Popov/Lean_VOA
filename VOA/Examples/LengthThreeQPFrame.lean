/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The Lee–Yang length-three quasi-primary frame: counting and the rank-one law

Decidable and exact-rational core of the length-three new-tower computation for Lee–Yang
graded unitarity (the quasi-primary frame and the rank-one deflation law).

## Status ladder

**Proven (complete Lean proofs):**

* `a3count_eq_pLe3_shift`, `a3count_vanishes_below_twelve`,
  `u3count_eq_pLe3_shift` — the counting lemma as a partition-count
  identity: the number of Lee–Yang admissible length-three partitions of
  `k + 12` equals the number of partitions of `k` into at most three
  parts (kernel computation for `k < 33`, i.e. weights `12..44`), there
  are none below weight `12`, and the universal three-part count at
  weight `k + 6` equals the same `pLe3 k` (verified for weights
  `6..38`).  That these counts are the DIMENSIONS of the simple-module
  layer, resp. the universal word space, rests on the admissible-basis
  theorem — an external input, like the rational data below.
* `negDef1`, `negDef2`, `negDef3` — negative definiteness of a quadratic
  form in dimensions one to three from explicit LDL data (unit-triangular
  multipliers and negative pivots): complete symbolic proofs.
* `rankOne_w12` … `rankOne_w24` — at every Lee–Yang weight `12..24`, the
  layer-route new-tower block (computed by eliminating `F²` and then the
  derivative symbols) equals the quasi-primary-frame Gram `Ĝ` minus the
  rank-one `Q_M`-exchange `q qᵀ / ρ` (computed by eliminating the
  derivative space and the single quasi-primary line), with `ρ > 0`; the
  two sides come from independent elimination PIPELINES (different
  eliminated subspaces and orders), so each identity kernel-checks the
  elimination bookkeeping of both routes — they do share the underlying
  Shapovalov routine, which is anchored separately (cross-module check
  through weight 11, the weight-six 682/35 anchor, the symbolic
  weight-six universal pivot).  At odd weights the law degenerates to
  `N = Ĝ`.  Weight `13` is absent because its new-tower multiplicity is
  zero (`2a + 3b = 1` has no solutions): there is no block to state.
* `negDef_w12` … `negDef_w24` — every new-tower block at weights `12..24`
  is negative definite as a quadratic form over `ℚ` (via its exact LDL
  data), the finite core of the graded-unitarity sign prediction at
  length three.
* `hatG_indefinite_w20/w22/w24` — at the even weights from twenty on, `Ĝ`
  alone is NOT negative definite (explicit rational directions of positive
  norm; at odd weights it stays negative definite), so
  the single rank-one exchange subtraction is load-bearing: this is the
  Lorentz-deflation structure of the all-weight problem.
* `totallyPositive_w18` … `totallyPositive_w24` — every minor of every
  order of `-N_M` is strictly positive at the multiplicity-`≥2` weights
  `18..24` (the total-positivity law, engine-verified at all weights
  `12..44`; strictly sharper than negative definiteness).

**External data (definitions, not proved here):** the rational matrices
`g*`, `n*`, vectors `q*`, and norms `rho*` are exact outputs of the two
elimination routes of the Python engine at `c = -22/5`; the Lean file
proves their internal identities and sign structure, not their provenance
from the Shapovalov form.  The engine itself re-derives them from the
Virasoro commutation relations in exact rational arithmetic at every run.
The engine's derivative space is `L₋₁` of the length-`≤3` words only;
this equals the full `L₋₁ V_{M-1}`-projection because the complement
`(1-Π)v_f` lies in `L₋₁ F³` by the filtered tower decomposition and the
form is nondegenerate there (independently machine-confirmed: extending
the eliminated space by the length-four `L₋₁`-images at weights `21..24`
leaves every `g`, `q`, `rho` literal unchanged).

**Not claimed:** any statement at weights above `44` (counting) or `24`
(blocks); the all-weight length-three theorem.
-/

namespace VOA.LengthThreeQPFrame

/-! ## Counting: the shift bijection in decidable form -/

/-- Number of Lee–Yang admissible length-three partitions of `n`:
triples `l₁ ≥ l₂ + 2`, `l₂ ≥ l₃ + 2`, `l₃ ≥ 2` with `l₁ + l₂ + l₃ = n`,
enumerated by `(l₂, l₃)` with `l₁ = n - l₂ - l₃`. -/
def a3count (n : ℕ) : ℕ :=
  ((List.range (n + 1)).flatMap fun l3 =>
    (List.range (n + 1)).filterMap fun l2 =>
      if 2 ≤ l3 ∧ l3 + 2 ≤ l2 ∧ 2 * l2 + l3 + 2 ≤ n then some (l2, l3)
      else none).length

/-- Number of partitions of `k` into at most three parts, enumerated by
`(m₂, m₃)` with `m₁ = k - m₂ - m₃ ≥ m₂ ≥ m₃ ≥ 0`. -/
def pLe3 (k : ℕ) : ℕ :=
  ((List.range (k + 1)).flatMap fun m3 =>
    (List.range (k + 1)).filterMap fun m2 =>
      if m3 ≤ m2 ∧ 2 * m2 + m3 ≤ k then some (m2, m3) else none).length

/-- Number of UNIVERSAL length-three words of weight `n`: three parts
each at least two, no gap condition. -/
def u3count (n : ℕ) : ℕ :=
  ((List.range (n + 1)).flatMap fun l3 =>
    (List.range (n + 1)).filterMap fun l2 =>
      if 2 ≤ l3 ∧ l3 ≤ l2 ∧ 2 * l2 + l3 ≤ n then some (l2, l3)
      else none).length

set_option maxRecDepth 40000 in
/-- The counting lemma at Lee–Yang: `a_{k+12,3} = p_{≤3}(k)` for all
weights `12..44` (the shift bijection `λ ↦ λ - (6,4,2)`). -/
theorem a3count_eq_pLe3_shift :
    ∀ k ∈ List.range 33, a3count (k + 12) = pLe3 k := by decide

set_option maxRecDepth 40000 in
/-- No admissible length-three partitions below weight twelve. -/
theorem a3count_vanishes_below_twelve :
    ∀ n ∈ List.range 12, a3count n = 0 := by decide

set_option maxRecDepth 40000 in
/-- The count `p_{≤3}(N-6)` is the UNIVERSAL word-space dimension: the
shift is by `(2,2,2)`, not `(6,4,2)`. -/
theorem u3count_eq_pLe3_shift :
    ∀ k ∈ List.range 33, u3count (k + 6) = pLe3 k := by decide

/-! ## Negative definiteness from LDL data -/

/-- Dimension one. -/
theorem negDef1 {a : ℚ} (ha : a < 0) : ∀ x : ℚ, x ≠ 0 → a * x ^ 2 < 0 := by
  intro x hx
  have hx2 : 0 < x ^ 2 := by positivity
  exact mul_neg_of_neg_of_pos ha hx2

/-- Dimension two: a symmetric form with unit-lower-triangular multiplier
`l` and negative pivots `d0, d1` is negative definite. -/
theorem negDef2 {g00 g01 g11 l d0 d1 : ℚ}
    (h00 : g00 = d0) (h01 : g01 = d0 * l) (h11 : g11 = d0 * l ^ 2 + d1)
    (hd0 : d0 < 0) (hd1 : d1 < 0) :
    ∀ x y : ℚ, ¬(x = 0 ∧ y = 0) →
      g00 * x ^ 2 + 2 * g01 * x * y + g11 * y ^ 2 < 0 := by
  intro x y hxy
  have key : g00 * x ^ 2 + 2 * g01 * x * y + g11 * y ^ 2
      = d0 * (x + l * y) ^ 2 + d1 * y ^ 2 := by
    subst h00; subst h01; subst h11; ring
  rw [key]
  by_cases hy : y = 0
  · have hx : x ≠ 0 := fun hx => hxy ⟨hx, hy⟩
    subst hy
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith [sq_nonneg (x + l * 0)]
  · have hy2 : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg (x + l * y)]

/-- Dimension three: negative definiteness from exact LDL data. -/
theorem negDef3 {g00 g01 g02 g11 g12 g22 l10 l20 l21 d0 d1 d2 : ℚ}
    (h00 : g00 = d0) (h01 : g01 = d0 * l10) (h02 : g02 = d0 * l20)
    (h11 : g11 = d0 * l10 ^ 2 + d1) (h12 : g12 = d0 * l10 * l20 + d1 * l21)
    (h22 : g22 = d0 * l20 ^ 2 + d1 * l21 ^ 2 + d2)
    (hd0 : d0 < 0) (hd1 : d1 < 0) (hd2 : d2 < 0) :
    ∀ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) →
      g00 * x ^ 2 + g11 * y ^ 2 + g22 * z ^ 2
        + 2 * g01 * x * y + 2 * g02 * x * z + 2 * g12 * y * z < 0 := by
  intro x y z hxyz
  have key : g00 * x ^ 2 + g11 * y ^ 2 + g22 * z ^ 2
      + 2 * g01 * x * y + 2 * g02 * x * z + 2 * g12 * y * z
      = d0 * (x + l10 * y + l20 * z) ^ 2 + d1 * (y + l21 * z) ^ 2
        + d2 * z ^ 2 := by
    subst h00; subst h01; subst h02; subst h11; subst h12; subst h22; ring
  rw [key]
  by_cases hz : z = 0
  · subst hz
    by_cases hy : y = 0
    · have hx : x ≠ 0 := fun hx => hxyz ⟨hx, hy, rfl⟩
      subst hy
      have hx2 : 0 < x ^ 2 := by positivity
      nlinarith [sq_nonneg (x + l10 * 0 + l20 * 0), sq_nonneg (0 + l21 * (0 : ℚ))]
    · have hy2 : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg (x + l10 * y + l20 * 0), sq_nonneg (y + l21 * 0)]
  · have hz2 : 0 < z ^ 2 := by positivity
    nlinarith [sq_nonneg (x + l10 * y + l20 * z), sq_nonneg (y + l21 * z)]

/-! ## The exact blocks at weights `12..24`

The `g` matrices are the quasi-primary-frame Grams `Ĝ_M` of the canonical
sections `Δ² σ₂ᵃ σ₃ᵇ` (projected off `L₋₁ V_{M-1}`), the `q` vectors are
the `Q_M`-exchange pairings, `rho` the closed-form `Q_M` norms, and the
`n` matrices the layer-route new-tower blocks — all exact rationals at
`c = -22/5`, produced by two independent eliminations. -/

/-! ### Weight 12 (multiplicity 1) -/

def g12_00 : ℚ := (-(275828333484 : ℚ) / 146965)
def n12_00 : ℚ := (-(51810090750 : ℚ) / 16451)
def q12_0 : ℚ := (-(901236468 : ℚ) / 455)
def rho12 : ℚ := ((1402809672 : ℚ) / 455)

/-- The rank-one law at weight 12: the layer-route new-tower block equals the
quasi-primary-frame Gram minus the `Q_{12}` exchange, and the exchange norm is
positive.  The two sides were computed by independent eliminations. -/
theorem rankOne_w12 :
    n12_00 = g12_00 - q12_0 * q12_0 / rho12 ∧
      (0 : ℚ) < rho12 := by
  refine ⟨?_, ?_⟩ <;>
  norm_num [g12_00, n12_00, q12_0, rho12]

/-- Negative definiteness of the weight-12 block. -/
theorem negDef_w12 : ∀ x : ℚ, x ≠ 0 → n12_00 * x ^ 2 < 0 :=
  negDef1 (by norm_num [n12_00])

/-! ### Weight 14 (multiplicity 1) -/

def g14_00 : ℚ := (-(4144867584 : ℚ) / 665)
def n14_00 : ℚ := (-(398458052608 : ℚ) / 25855)
def q14_0 : ℚ := (-(151911320 : ℚ) / 7)
def rho14 : ℚ := ((7183672133 : ℚ) / 140)

/-- The rank-one law at weight 14: the layer-route new-tower block equals the
quasi-primary-frame Gram minus the `Q_{14}` exchange, and the exchange norm is
positive.  The two sides were computed by independent eliminations. -/
theorem rankOne_w14 :
    n14_00 = g14_00 - q14_0 * q14_0 / rho14 ∧
      (0 : ℚ) < rho14 := by
  refine ⟨?_, ?_⟩ <;>
  norm_num [g14_00, n14_00, q14_0, rho14]

/-- Negative definiteness of the weight-14 block. -/
theorem negDef_w14 : ∀ x : ℚ, x ≠ 0 → n14_00 * x ^ 2 < 0 :=
  negDef1 (by norm_num [n14_00])

/-! ### Weight 15 (multiplicity 1) -/

def g15_00 : ℚ := (-(94386863616 : ℚ) / 455)
def n15_00 : ℚ := (-(94386863616 : ℚ) / 455)

/-- Odd weight 15: no length-two quasi-primary exists, `N = Ĝ` verbatim. -/
theorem rankOne_w15 :
    n15_00 = g15_00 := by norm_num [g15_00, n15_00]

/-- Negative definiteness of the weight-15 block. -/
theorem negDef_w15 : ∀ x : ℚ, x ≠ 0 → n15_00 * x ^ 2 < 0 :=
  negDef1 (by norm_num [n15_00])

/-! ### Weight 16 (multiplicity 1) -/

def g16_00 : ℚ := (-(277122890880 : ℚ) / 11339)
def n16_00 : ℚ := (-(6017646096000 : ℚ) / 62263)
def q16_0 : ℚ := (-(4177525440 : ℚ) / 17)
def rho16 : ℚ := ((28433332895 : ℚ) / 34)

/-- The rank-one law at weight 16: the layer-route new-tower block equals the
quasi-primary-frame Gram minus the `Q_{16}` exchange, and the exchange norm is
positive.  The two sides were computed by independent eliminations. -/
theorem rankOne_w16 :
    n16_00 = g16_00 - q16_0 * q16_0 / rho16 ∧
      (0 : ℚ) < rho16 := by
  refine ⟨?_, ?_⟩ <;>
  norm_num [g16_00, n16_00, q16_0, rho16]

/-- Negative definiteness of the weight-16 block. -/
theorem negDef_w16 : ∀ x : ℚ, x ≠ 0 → n16_00 * x ^ 2 < 0 :=
  negDef1 (by norm_num [n16_00])

/-! ### Weight 17 (multiplicity 1) -/

def g17_00 : ℚ := (-(5210684649500 : ℚ) / 7371)
def n17_00 : ℚ := (-(5210684649500 : ℚ) / 7371)

/-- Odd weight 17: no length-two quasi-primary exists, `N = Ĝ` verbatim. -/
theorem rankOne_w17 :
    n17_00 = g17_00 := by norm_num [g17_00, n17_00]

/-- Negative definiteness of the weight-17 block. -/
theorem negDef_w17 : ∀ x : ℚ, x ≠ 0 → n17_00 * x ^ 2 < 0 :=
  negDef1 (by norm_num [n17_00])

/-! ### Weight 18 (multiplicity 2) -/

def g18_00 : ℚ := (-(1039953172495761694748 : ℚ) / 131456281293)
def g18_01 : ℚ := (-(20722944460445796640 : ℚ) / 43818760431)
def g18_11 : ℚ := (-(3404256144656694016 : ℚ) / 73031267385)
def n18_00 : ℚ := (-(9589282944090515996 : ℚ) / 1134243621)
def n18_01 : ℚ := (-(59586242376169696 : ℚ) / 54011601)
def n18_11 : ℚ := (-(2000453828400896 : ℚ) / 2571981)
def q18_0 : ℚ := (-(4162607626232 : ℚ) / 1539)
def q18_1 : ℚ := (-(8048143123328 : ℚ) / 2565)
def rho18 : ℚ := ((1279145096922 : ℚ) / 95)

/-- The rank-one law at weight 18: the layer-route new-tower block equals the
quasi-primary-frame Gram minus the `Q_{18}` exchange, and the exchange norm is
positive.  The two sides were computed by independent eliminations. -/
theorem rankOne_w18 :
    n18_00 = g18_00 - q18_0 * q18_0 / rho18 ∧
      n18_01 = g18_01 - q18_0 * q18_1 / rho18 ∧
      n18_11 = g18_11 - q18_1 * q18_1 / rho18 ∧
      (0 : ℚ) < rho18 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num [g18_00, g18_01, g18_11, n18_00, n18_01, n18_11, q18_0, q18_1, rho18]

/-- Negative definiteness of the weight-18 block, by its exact LDL data. -/
theorem negDef_w18 : ∀ x y : ℚ, ¬(x = 0 ∧ y = 0) →
    n18_00 * x ^ 2 + 2 * n18_01 * x * y + n18_11 * y ^ 2 < 0 :=
  negDef2 (l := ((2585353491528024 : ℚ) / 19812568066302719))
    (d0 := (-(9589282944090515996 : ℚ) / 1134243621))
    (d1 := (-(12557768480852760000000000 : ℚ) / 19812568066302719))
    (by norm_num [n18_00]) (by norm_num [n18_01]) (by norm_num [n18_11])
    (by norm_num) (by norm_num)

/-! ### Weight 19 (multiplicity 1) -/

def g19_00 : ℚ := (-(59995938288 : ℚ) / 17)
def n19_00 : ℚ := (-(59995938288 : ℚ) / 17)

/-- Odd weight 19: no length-two quasi-primary exists, `N = Ĝ` verbatim. -/
theorem rankOne_w19 :
    n19_00 = g19_00 := by norm_num [g19_00, n19_00]

/-- Negative definiteness of the weight-19 block. -/
theorem negDef_w19 : ∀ x : ℚ, x ≠ 0 → n19_00 * x ^ 2 < 0 :=
  negDef1 (by norm_num [n19_00])

/-! ### Weight 20 (multiplicity 2) -/

def g20_00 : ℚ := (-(385258103927374621097984 : ℚ) / 20559889405125)
def g20_01 : ℚ := (-(5780611443920968039424 : ℚ) / 1370659293675)
def g20_11 : ℚ := (-(9147823240055272448 : ℚ) / 91377286245)
def n20_00 : ℚ := (-(222447001000457443065856 : ℚ) / 10487797898805)
def n20_01 : ℚ := (-(29724495228072949111808 : ℚ) / 3495932632935)
def n20_11 : ℚ := (-(8773925051654066047744 : ℚ) / 1165310877645)
def q20_0 : ℚ := (-(326910690423808 : ℚ) / 14175)
def q20_1 : ℚ := (-(37783813907008 : ℚ) / 945)
def rho20 : ℚ := ((7531423894032 : ℚ) / 35)

/-- The rank-one law at weight 20: the layer-route new-tower block equals the
quasi-primary-frame Gram minus the `Q_{20}` exchange, and the exchange norm is
positive.  The two sides were computed by independent eliminations. -/
theorem rankOne_w20 :
    n20_00 = g20_00 - q20_0 * q20_0 / rho20 ∧
      n20_01 = g20_01 - q20_0 * q20_1 / rho20 ∧
      n20_11 = g20_11 - q20_1 * q20_1 / rho20 ∧
      (0 : ℚ) < rho20 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num [g20_00, g20_01, g20_11, n20_00, n20_01, n20_11, q20_0, q20_1, rho20]

/-- Negative definiteness of the weight-20 block, by its exact LDL data. -/
theorem negDef_w20 : ∀ x y : ℚ, ¬(x = 0 ∧ y = 0) →
    n20_00 * x ^ 2 + 2 * n20_01 * x * y + n20_11 * y ^ 2 < 0 :=
  negDef2 (l := ((608367032362707 : ℚ) / 1517597084136208))
    (d0 := (-(222447001000457443065856 : ℚ) / 10487797898805))
    (d1 := (-(14461636512245639076360000 : ℚ) / 3509443257064981))
    (by norm_num [n20_00]) (by norm_num [n20_01]) (by norm_num [n20_11])
    (by norm_num) (by norm_num)

/-- At the even weights from twenty on, `Ĝ` alone is NOT negative definite:
an explicit rational direction with positive `Ĝ`-norm.  Together with `negDef_w20` and
`rankOne_w20`, the single `Q`-exchange subtraction is load-bearing. -/
theorem hatG_indefinite_w20 :
    g20_00 * (-3 : ℚ) ^ 2 + 2 * g20_01 * (-3 : ℚ) * (7 : ℚ)
      + g20_11 * (7 : ℚ) ^ 2 > 0 ∧ g20_00 < 0 := by
  constructor <;> norm_num [g20_00, g20_01, g20_11]

/-! ### Weight 21 (multiplicity 2) -/

def g21_00 : ℚ := (-(20238331938249329001328 : ℚ) / 76450248225)
def g21_01 : ℚ := (-(672417182106050952032 : ℚ) / 25483416075)
def g21_11 : ℚ := (-(191893782827389527808 : ℚ) / 8494472025)
def n21_00 : ℚ := (-(20238331938249329001328 : ℚ) / 76450248225)
def n21_01 : ℚ := (-(672417182106050952032 : ℚ) / 25483416075)
def n21_11 : ℚ := (-(191893782827389527808 : ℚ) / 8494472025)

/-- Odd weight 21: no length-two quasi-primary exists, `N = Ĝ` verbatim. -/
theorem rankOne_w21 :
    n21_00 = g21_00 ∧
      n21_01 = g21_01 ∧
      n21_11 = g21_11 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [g21_00, g21_01, g21_11, n21_00, n21_01, n21_11]

/-- Negative definiteness of the weight-21 block, by its exact LDL data. -/
theorem negDef_w21 : ∀ x y : ℚ, ¬(x = 0 ∧ y = 0) →
    n21_00 * x ^ 2 + 2 * n21_01 * x * y + n21_11 * y ^ 2 < 0 :=
  negDef2 (l := ((9336201834 : ℚ) / 93666628787))
    (d0 := (-(20238331938249329001328 : ℚ) / 76450248225))
    (d1 := (-(603887314209901521800000 : ℚ) / 30254321098201))
    (by norm_num [n21_00]) (by norm_num [n21_01]) (by norm_num [n21_11])
    (by norm_num) (by norm_num)

/-! ### Weight 22 (multiplicity 2) -/

def g22_00 : ℚ := (-(33901834628193000191885312 : ℚ) / 478261260374625)
def g22_01 : ℚ := (-(1082641316960864584794112 : ℚ) / 31884084024975)
def g22_11 : ℚ := (-(324248412534957408256 : ℚ) / 78726133395)
def n22_00 : ℚ := (-(4669253132800948838187008 : ℚ) / 54775613497059)
def n22_01 : ℚ := (-(1215044323548356957962240 : ℚ) / 18258537832353)
def n22_11 : ℚ := (-(475321769548316357427200 : ℚ) / 6086179277451)
def q22_0 : ℚ := (-(688318846603648 : ℚ) / 3105)
def q22_1 : ℚ := (-(104162865038848 : ℚ) / 207)
def rho22 : ℚ := ((78722607576015 : ℚ) / 23)

/-- The rank-one law at weight 22: the layer-route new-tower block equals the
quasi-primary-frame Gram minus the `Q_{22}` exchange, and the exchange norm is
positive.  The two sides were computed by independent eliminations. -/
theorem rankOne_w22 :
    n22_00 = g22_00 - q22_0 * q22_0 / rho22 ∧
      n22_01 = g22_01 - q22_0 * q22_1 / rho22 ∧
      n22_11 = g22_11 - q22_1 * q22_1 / rho22 ∧
      (0 : ℚ) < rho22 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  norm_num [g22_00, g22_01, g22_11, n22_00, n22_01, n22_11, q22_0, q22_1, rho22]

/-- Negative definiteness of the weight-22 block, by its exact LDL data. -/
theorem negDef_w22 : ∀ x y : ℚ, ¬(x = 0 ∧ y = 0) →
    n22_00 * x ^ 2 + 2 * n22_01 * x * y + n22_11 * y ^ 2 < 0 :=
  negDef2 (l := ((167153463873289680 : ℚ) / 214116149159510077))
    (d0 := (-(4669253132800948838187008 : ℚ) / 54775613497059))
    (d1 := (-(39190615346099912048640000000 : ℚ) / 1498813044116570539))
    (by norm_num [n22_00]) (by norm_num [n22_01]) (by norm_num [n22_11])
    (by norm_num) (by norm_num)

/-- At the even weights from twenty on, `Ĝ` alone is NOT negative definite:
an explicit rational direction with positive `Ĝ`-norm.  Together with `negDef_w22` and
`rankOne_w22`, the single `Q`-exchange subtraction is load-bearing. -/
theorem hatG_indefinite_w22 :
    g22_00 * (-8 : ℚ) ^ 2 + 2 * g22_01 * (-8 : ℚ) * (9 : ℚ)
      + g22_11 * (9 : ℚ) ^ 2 > 0 ∧ g22_00 < 0 := by
  constructor <;> norm_num [g22_00, g22_01, g22_11]

/-! ### Weight 23 (multiplicity 2) -/

def g23_00 : ℚ := (-(914675128829808883712 : ℚ) / 1784992221)
def g23_01 : ℚ := (-(99492456551535738880 : ℚ) / 594997407)
def g23_11 : ℚ := (-(34099081547546624000 : ℚ) / 198332469)
def n23_00 : ℚ := (-(914675128829808883712 : ℚ) / 1784992221)
def n23_01 : ℚ := (-(99492456551535738880 : ℚ) / 594997407)
def n23_11 : ℚ := (-(34099081547546624000 : ℚ) / 198332469)

/-- Odd weight 23: no length-two quasi-primary exists, `N = Ĝ` verbatim. -/
theorem rankOne_w23 :
    n23_00 = g23_00 ∧
      n23_01 = g23_01 ∧
      n23_11 = g23_11 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [g23_00, g23_01, g23_11, n23_00, n23_01, n23_11]

/-- Negative definiteness of the weight-23 block, by its exact LDL data. -/
theorem negDef_w23 : ∀ x y : ℚ, ¬(x = 0 ∧ y = 0) →
    n23_00 * x ^ 2 + 2 * n23_01 * x * y + n23_11 * y ^ 2 < 0 :=
  negDef2 (l := ((182059383360 : ℚ) / 557915630663))
    (d0 := (-(914675128829808883712 : ℚ) / 1784992221))
    (d1 := (-(4333188351811971256431411200 : ℚ) / 36921182690385351))
    (by norm_num [n23_00]) (by norm_num [n23_01]) (by norm_num [n23_11])
    (by norm_num) (by norm_num)

/-! ### Weight 24 (multiplicity 3) -/

def g24_00 : ℚ := (-(4291398351268209949761582233768 : ℚ) / 627198012952583625)
def g24_01 : ℚ := (-(17626235406539262304360970816 : ℚ) / 41813200863505575)
def g24_02 : ℚ := (-(62100566433624620419486208 : ℚ) / 605988418311675)
def g24_11 : ℚ := (-(12601104662744531432450175488 : ℚ) / 36238107415038165)
def g24_12 : ℚ := (-(3144016530026239897463566336 : ℚ) / 12079369138346055)
def g24_22 : ℚ := (-(1483871707828218435771301888 : ℚ) / 20132281897243425)
def n24_00 : ℚ := (-(59912275449505260160698261856 : ℚ) / 8625528850360275)
def n24_01 : ℚ := (-(302769450862944708721606912 : ℚ) / 575035256690685)
def n24_02 : ℚ := (-(15833278722041627021548544 : ℚ) / 41669221499325)
def n24_11 : ℚ := (-(3567487953393706791857453056 : ℚ) / 7858815174772695)
def n24_12 : ℚ := (-(283470624911650507911749632 : ℚ) / 523921011651513)
def n24_22 : ℚ := (-(3562307993913612275507953664 : ℚ) / 4366008430429275)
def q24_0 : ℚ := (-(8008879219547404 : ℚ) / 3375)
def q24_1 : ℚ := (-(7023044229392224 : ℚ) / 2925)
def q24_2 : ℚ := (-(6188312537732864 : ℚ) / 975)
def rho24 : ℚ := ((88198311808698894 : ℚ) / 1625)

/-- The rank-one law at weight 24: the layer-route new-tower block equals the
quasi-primary-frame Gram minus the `Q_{24}` exchange, and the exchange norm is
positive.  The two sides were computed by independent eliminations. -/
theorem rankOne_w24 :
    n24_00 = g24_00 - q24_0 * q24_0 / rho24 ∧
      n24_01 = g24_01 - q24_0 * q24_1 / rho24 ∧
      n24_02 = g24_02 - q24_0 * q24_2 / rho24 ∧
      n24_11 = g24_11 - q24_1 * q24_1 / rho24 ∧
      n24_12 = g24_12 - q24_1 * q24_2 / rho24 ∧
      n24_22 = g24_22 - q24_2 * q24_2 / rho24 ∧
      (0 : ℚ) < rho24 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  norm_num [g24_00, g24_01, g24_02, g24_11, g24_12, g24_22, n24_00, n24_01, n24_02,
    n24_11, n24_12, n24_22, q24_0, q24_1, q24_2, rho24]

/-- Negative definiteness of the weight-24 block, by its exact LDL data. -/
theorem negDef_w24 : ∀ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) →
    n24_00 * x ^ 2 + n24_11 * y ^ 2 + n24_22 * z ^ 2
      + 2 * n24_01 * x * y + 2 * n24_02 * x * z + 2 * n24_12 * y * z < 0 :=
  negDef3 (l10 := ((491083668138426755063160 : ℚ) / 6478403487186987474123947))
    (l20 := ((354399729180646279569696 : ℚ) / 6478403487186987474123947))
    (l21 := ((90312677720585877631409588161806042 : ℚ) / 72996442357387183588634393034951679))
    (d0 := (-(59912275449505260160698261856 : ℚ) / 8625528850360275))
    (d1 := (-(396444953836810662338745049192937675324735488 : ℚ) /
      957515194042090090296678273561435))
    (d2 := (-(11778912979930861377042089015038491599831040000 : ℚ) /
      72996442357387183588634393034951679))
    (by norm_num [n24_00]) (by norm_num [n24_01]) (by norm_num [n24_02])
    (by norm_num [n24_11]) (by norm_num [n24_12]) (by norm_num [n24_22])
    (by norm_num) (by norm_num) (by norm_num)

/-- The weight-24 `Ĝ` is not negative definite: explicit positive direction. -/
theorem hatG_indefinite_w24 :
    g24_00 * (-1 : ℚ) ^ 2 + g24_11 * (4 : ℚ) ^ 2 + g24_22 * (-9 : ℚ) ^ 2
      + 2 * g24_01 * (-1 : ℚ) * (4 : ℚ) + 2 * g24_02 * (-1 : ℚ) * (-9 : ℚ)
      + 2 * g24_12 * (4 : ℚ) * (-9 : ℚ) > 0 ∧ g24_00 < 0 := by
  constructor <;> norm_num [g24_00, g24_01, g24_02, g24_11, g24_12, g24_22]

/-! ## Total positivity of `-N` at weights `18..24`

In the canonical section basis ordered by increasing `a`, every minor of
every order of `-N_M` is strictly positive (the total-positivity law,
verified by the engine at all weights `12..44`).  Here the full minor
lists at the multiplicity-two and -three weights, as exact rational
inequalities.  Odd-order minors of `-N` are `-det` of the `n`-submatrix;
even-order minors are `+det`. -/

/-- Every minor of `-N` at weight 18 is strictly positive. -/
theorem totallyPositive_w18 :
    0 < -n18_00 ∧
      0 < -n18_01 ∧
      0 < -n18_01 ∧
      0 < -n18_11 ∧
      0 < n18_00 * n18_11 - n18_01 * n18_01 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [n18_00, n18_01, n18_11]

/-- Every minor of `-N` at weight 20 is strictly positive. -/
theorem totallyPositive_w20 :
    0 < -n20_00 ∧
      0 < -n20_01 ∧
      0 < -n20_01 ∧
      0 < -n20_11 ∧
      0 < n20_00 * n20_11 - n20_01 * n20_01 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [n20_00, n20_01, n20_11]

/-- Every minor of `-N` at weight 21 is strictly positive. -/
theorem totallyPositive_w21 :
    0 < -n21_00 ∧
      0 < -n21_01 ∧
      0 < -n21_01 ∧
      0 < -n21_11 ∧
      0 < n21_00 * n21_11 - n21_01 * n21_01 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [n21_00, n21_01, n21_11]

/-- Every minor of `-N` at weight 22 is strictly positive. -/
theorem totallyPositive_w22 :
    0 < -n22_00 ∧
      0 < -n22_01 ∧
      0 < -n22_01 ∧
      0 < -n22_11 ∧
      0 < n22_00 * n22_11 - n22_01 * n22_01 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [n22_00, n22_01, n22_11]

/-- Every minor of `-N` at weight 23 is strictly positive. -/
theorem totallyPositive_w23 :
    0 < -n23_00 ∧
      0 < -n23_01 ∧
      0 < -n23_01 ∧
      0 < -n23_11 ∧
      0 < n23_00 * n23_11 - n23_01 * n23_01 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [n23_00, n23_01, n23_11]

/-- Every minor of `-N` at weight 24 is strictly positive. -/
theorem totallyPositive_w24 :
    0 < -n24_00 ∧
      0 < -n24_01 ∧
      0 < -n24_02 ∧
      0 < -n24_01 ∧
      0 < -n24_11 ∧
      0 < -n24_12 ∧
      0 < -n24_02 ∧
      0 < -n24_12 ∧
      0 < -n24_22 ∧
      0 < n24_00 * n24_11 - n24_01 * n24_01 ∧
      0 < n24_00 * n24_12 - n24_02 * n24_01 ∧
      0 < n24_01 * n24_12 - n24_02 * n24_11 ∧
      0 < n24_00 * n24_12 - n24_01 * n24_02 ∧
      0 < n24_00 * n24_22 - n24_02 * n24_02 ∧
      0 < n24_01 * n24_22 - n24_02 * n24_12 ∧
      0 < n24_01 * n24_12 - n24_11 * n24_02 ∧
      0 < n24_01 * n24_22 - n24_12 * n24_02 ∧
      0 < n24_11 * n24_22 - n24_12 * n24_12 ∧
      0 < -(n24_00 * (n24_11 * n24_22 - n24_12 * n24_12)
            - n24_01 * (n24_01 * n24_22 - n24_12 * n24_02)
            + n24_02 * (n24_01 * n24_12 - n24_11 * n24_02)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [n24_00, n24_01, n24_02, n24_11, n24_12, n24_22]

end VOA.LengthThreeQPFrame
