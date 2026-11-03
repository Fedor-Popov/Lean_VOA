/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.Ring

/-!
# Weil parity of the Lee–Yang channel constants and the option-(a) twist at cutoff three

This file formalizes the finite, decidable core of a Weil-parity
computation for the cutoff-three reflection twist: the enriched Lee–Yang
fusion ring at the physical root (Godfard, arXiv:2406.07459, Theorem 4.7
data at `r = 5`), the Hodge bidegrees of the thirteen balanced-tree channels
at cutoff three, the Weil sign rule `sign(X) = sign(κ) = i^(p-q)` on the
five sector classes, and the landing-degree forcing that derives the
option-(a) reflection twist from the flag multiplicities `(1, 5, 6, 1)`.

## Status ladder (proven / external data / not claimed)

**Proven (complete Lean proofs; the fusion-ring computation, the parity
identity, and the landing combinatorics are fully proved):**

* `mul_two_two_eq`, `structConst_two_two_*`, `structConst_two_zero_two`,
  `structConst_zero_zero_zero` — the structure constants of `[2]·[2]` are
  **derived** from the fusion recursion `[k][1] = [k+1] + w_k [k-1]`,
  `[b] = [b-1][1] - w_{b-1}[b-2]` (they are computed, not postulated):
  `[2][2] = uv·[0] + v·[2]`.
* `internal_color_forced`, `internal_color_allphi`, `channels_admissible` —
  the internal color of every multiplicity-one channel is forced by the
  derived structure constants; the all-phi tree admits exactly the internal
  colors `{0, 2}`.
* `k0_channel_bidegree` … `aphiphi_channel_bidegree`, `channel_bidegrees` —
  the bidegrees `(4,4); (3,5)×6; (2,6)×4; (2,6); (1,7)` of the thirteen
  channels, each `p + q = 8` with `p - q` even
  (`sectorBidegree_weight_eight`, `sectorBidegree_diff_even`).
* `channel_sum`, `channel_sum_toMv` — the thirteen channel monomials sum to
  the Feigin–Frenkel/Hodge squeeze polynomial
  `u v⁷ + 5 u² v⁶ + 6 u³ v⁵ + u⁴ v⁴` (at `n = 2`, `N = 3`), both as a
  normal-form identity and as an identity in Mathlib's
  `MvPolynomial (Fin 2) ℤ` through the certified evaluation `toMv`
  (`toMv_addP`, `toMv_mulP`, … prove the list arithmetic is a faithful
  model of actual polynomial arithmetic — an independent verification
  route for the normal-form computations).
* `weil_parity_cutoff_three` — **Theorem A at cutoff three**: for every
  sector, `Xsign = weil (bidegree)` and `kappaSign = weil (bidegree)`.
* `landing_count`, `landing_k2_k3_forced`, `anchored_twist_eq_option_a`,
  `option_c_not_realizable` — exactly six class-uniform landings match the
  flag multiplicities; all force `l(k2) = 2`, `l(k3) = 1`; vacuum-anchored
  ones (`l(k0)` even) force `l(k0) = 0` and induce exactly the option-(a)
  twist `(+, +, -, -, -)`; option (c) admits no landing realization.
* `weil_polarized_twist_option_a` — the bundle: squeeze identity + parity
  + forcing, a proved proposition (not a hypothesis).

**External verified inputs, encoded as data (NOT proven here):**

* `w` — the enriched fusion weights `w₁ = u`, `w₂ = v`, `w₃ = u` at the
  physical root `s = r - 2` of `r = 5` (Godfard Theorem 4.7).
* `Xsign`, `kappaSign` — the recorded channel sign data: the
  Dotsenko–Fateev channel norms `X = (1, C², C⁴, C⁴, C⁶)` with `C² < 0`,
  and the canonical bilinear channel constants
  `κ = (1/125, -1/125, 1/250, 1/125, -1/500)` (exact/certified analytic
  computations carried out outside Lean, not re-derived here).
* `optionA`, `optionC` — the recorded candidate twist tuples of the
  reflection-twist report.

**Not claimed:**

* No claim that the class-uniformity of the landing (hypothesis H-land of
  the Python frame) holds for the actual PBW landing degrees; the theorems
  quantify over all class-uniform landings.
* No claim about the analytic magnitudes `|X|`, `|κ|`, the Rees threshold
  `s* ≈ 8.3687`, or the weight-completed Shapovalov layers — none of the
  certified-numeric content of the Python script is transcribed here.
* No claim connecting the fusion-ring bidegrees to an actual Hodge
  filtration on a space of conformal blocks; the bidegrees are the
  Godfard fusion-ring monomials, taken as the definition of the frame.
-/

namespace VOA
namespace WeilParity

/-! ## §1  Bivariate monomials and normal-form polynomials

Monomials `u^p v^q` are exponent pairs `(p, q) : ℕ × ℕ`.  Polynomials are
key-sorted association lists with nonzero `ℤ` coefficients (all
coefficients appearing in the derived identities are nonnegative; `ℤ` is
used so that the fusion recursion's subtraction is honest rather than
truncated).  Every concrete computation below produces the normal form,
and `toMv` (§6) certifies the arithmetic against `MvPolynomial`. -/

/-- A bivariate monomial `u^p v^q`, encoded as the exponent pair `(p, q)`:
`p` is the `u`-exponent, `q` the `v`-exponent. -/
abbrev Mono : Type := ℕ × ℕ

/-- A bivariate polynomial with `ℤ` coefficients: an association list of
monomial–coefficient pairs.  The arithmetic below keeps lists in normal
form (keys strictly increasing in `MonoLt`, coefficients nonzero). -/
abbrev Poly : Type := List (Mono × ℤ)

/-- Strict lexicographic order on monomials (`u`-exponent first). -/
def MonoLt (m n : Mono) : Prop :=
  m.1 < n.1 ∨ (m.1 = n.1 ∧ m.2 < n.2)

/-- `MonoLt` is decidable, so the normal-form arithmetic is computable by
`decide`/`rfl`. -/
instance : DecidableRel MonoLt := fun m n =>
  inferInstanceAs (Decidable (m.1 < n.1 ∨ (m.1 = n.1 ∧ m.2 < n.2)))

/-- Trichotomy: two monomials with neither strictly below the other are
equal.  Used in the correctness proof of the merging insertion. -/
theorem eq_of_not_monoLt {m n : Mono} (h₁ : ¬ MonoLt m n) (h₂ : ¬ MonoLt n m) :
    m = n := by
  obtain ⟨a, b⟩ := m
  obtain ⟨c, d⟩ := n
  simp only [MonoLt, not_or, not_and, not_lt] at h₁ h₂
  have hac : a = c := le_antisymm h₂.1 h₁.1
  have hbd : b = d := le_antisymm (h₂.2 hac.symm) (h₁.2 hac)
  subst hac
  subst hbd
  rfl

/-- Insert one monomial–coefficient pair into a key-sorted polynomial,
merging equal keys and dropping a cancelled (zero) coefficient. -/
def insertMono (m : Mono) (c : ℤ) : Poly → Poly
  | [] => [(m, c)]
  | (n, d) :: q =>
    if MonoLt m n then (m, c) :: (n, d) :: q
    else if MonoLt n m then (n, d) :: insertMono m c q
    else if c + d = 0 then q else (m, c + d) :: q

/-- Polynomial addition: merge the first list into the second. -/
def addP (p q : Poly) : Poly :=
  p.foldr (fun t acc => insertMono t.1 t.2 acc) q

/-- Polynomial negation. -/
def negP (p : Poly) : Poly :=
  p.map fun t => (t.1, -t.2)

/-- Polynomial subtraction, used by the fusion recursion
`[b] = [b-1][1] - w_{b-1}[b-2]`. -/
def subP (p q : Poly) : Poly :=
  addP p (negP q)

/-- Multiplication by a single monomial with coefficient: shift every
exponent pair and scale every coefficient. -/
def monoMul (m : Mono) (c : ℤ) (p : Poly) : Poly :=
  p.map fun t => ((m.1 + t.1.1, m.2 + t.1.2), c * t.2)

/-- Polynomial multiplication, via `monoMul` and `addP`. -/
def mulP (p q : Poly) : Poly :=
  p.foldr (fun t acc => addP (monoMul t.1 t.2 q) acc) []

/-- Sum of a list of polynomials. -/
def sumP (l : List Poly) : Poly :=
  l.foldr addP []

/-! ## §2  The enriched Lee–Yang fusion ring at the physical root (r = 5)

Colors are `{0, 1, 2, 3}` (encoded as `ℕ`; `[4] = 0` is built into the
multiplication-by-`[1]` rule).  The weights are **external input** (Godfard
Theorem 4.7 at `s = r - 2 = 3`): `w₁ = u`, `w₂ = v`, `w₃ = u`.  Everything
past the weights is *derived* from the recursion, not postulated. -/

/-- A fusion-ring element: a color (in `{0, 1, 2, 3}`) mapped to its
coefficient polynomial.  All constructions below are supported on colors
`≤ 3`. -/
abbrev Elem : Type := ℕ → Poly

/-- **External input** (Godfard arXiv:2406.07459 Theorem 4.7, `r = 5`,
physical root `s = 3`): the enriched fusion weights `w₁ = u`, `w₂ = v`,
`w₃ = u`.  These are the only postulated fusion data; the structure
constants below are derived from them. -/
def w : ℕ → Poly
  | 1 => [((1, 0), 1)]
  | 2 => [((0, 1), 1)]
  | 3 => [((1, 0), 1)]
  | _ => []

/-- The basis delta element `[k]` viewed as an `Elem`: coefficient `1` at
color `k`, zero elsewhere. -/
def deltaE (k : ℕ) : Elem := fun c =>
  if c = k then [((0, 0), 1)] else []

/-- Multiplication by the fundamental color `[1]`:
`[k][1] = [k+1] + w_k [k-1]`, with the truncation `[4] = 0`.  In
color-indexed form, color `c` receives the raise `a (c-1)` for
`1 ≤ c ≤ 3` and the weighted lower `w_{c+1} · a (c+1)` for `c + 1 ≤ 3`. -/
def mulOne (a : Elem) : Elem := fun c =>
  addP (if 1 ≤ c ∧ c ≤ 3 then a (c - 1) else [])
    (if c + 1 ≤ 3 then mulP (w (c + 1)) (a (c + 1)) else [])

/-- The color element `[b]`, built recursively: `[0] = 1`, `[1] = X`,
`[b] = [b-1][1] - w_{b-1}[b-2]`. -/
def colorElem : ℕ → Elem
  | 0 => deltaE 0
  | 1 => deltaE 1
  | b + 2 => fun c =>
      subP (mulOne (colorElem (b + 1)) c) (mulP (w (b + 1)) (colorElem b c))

/-- Right multiplication of an element by the color `[b]`, via the same
recursion: `a·[b] = (a·[b-1])[1] - w_{b-1} (a·[b-2])`. -/
def mulColor (a : Elem) : ℕ → Elem
  | 0 => a
  | 1 => mulOne a
  | b + 2 => fun c =>
      subP (mulOne (mulColor a (b + 1)) c) (mulP (w (b + 1)) (mulColor a b c))

/-- The fusion structure constant `N_{ab}^c`: the coefficient polynomial of
`[c]` in the product `[a]·[b]`, **derived** from the recursion. -/
def structConst (a b c : ℕ) : Poly :=
  mulColor (colorElem a) b c

/-- The recursion collapses `[2]` back to the basis delta at color `2`
(the cancellation `[1][1] - u[0] = [2]` happens honestly in `ℤ`). -/
theorem colorElem_two_eq :
    ∀ c : Fin 4, colorElem 2 (c : ℕ) = deltaE 2 (c : ℕ) := by decide

/-- The recursion collapses `[3]` back to the basis delta at color `3`. -/
theorem colorElem_three_eq :
    ∀ c : Fin 4, colorElem 3 (c : ℕ) = deltaE 3 (c : ℕ) := by decide

/-- **The derived fusion identity `[2][2] = uv·[0] + v·[2]`** on the
color range `{0, 1, 2, 3}`, proved from the recursion by computation. -/
theorem mul_two_two_eq :
    ∀ c : Fin 4,
      structConst 2 2 (c : ℕ)
        = addP (mulP [((1, 1), 1)] (deltaE 0 (c : ℕ)))
            (mulP [((0, 1), 1)] (deltaE 2 (c : ℕ))) := by decide

/-- Derived structure constant `N_{22}^0 = uv` (the monomial `(1, 1)`). -/
theorem structConst_two_two_zero : structConst 2 2 0 = [((1, 1), 1)] := by decide

/-- Derived structure constant `N_{22}^1 = 0`. -/
theorem structConst_two_two_one : structConst 2 2 1 = [] := by decide

/-- Derived structure constant `N_{22}^2 = v` (the monomial `(0, 1)`). -/
theorem structConst_two_two_two : structConst 2 2 2 = [((0, 1), 1)] := by decide

/-- Derived structure constant `N_{22}^3 = 0`. -/
theorem structConst_two_two_three : structConst 2 2 3 = [] := by decide

/-- Derived trivial structure constant `N_{20}^2 = 1` (the monomial
`(0, 0)`). -/
theorem structConst_two_zero_two : structConst 2 0 2 = [((0, 0), 1)] := by decide

/-- Derived trivial structure constant `N_{00}^0 = 1` (the monomial
`(0, 0)`). -/
theorem structConst_zero_zero_zero : structConst 0 0 0 = [((0, 0), 1)] := by decide

/-! ## §3  Channel monomials for the balanced 4-pair tree at cutoff three

Thirteen channels in five sector classes.  Sector labels use the colors
`{0, 2}` directly (the report's labels `(s₁, s₂, s₃, s₄) ∈ {0, 1}⁴` scaled
by `2`).  The internal color of every multiplicity-one channel is *forced*
by the derived structure constants (`internal_color_forced`); the all-phi
label `(2, 2, 2, 2)` splits into two channels, internal `0` and internal
`2` (`internal_color_allphi`). -/

/-- The five sector classes of the cutoff-three block space: the vacuum
comb `k0`, the six `k2` channels, the four `k3` channels, and the two
all-phi channels (internal color `1`-type `aphi0` and phi-type
`aphiphi`). -/
inductive Sector : Type
  /-- The vacuum comb `(0,0,0,0)`, internal color `0`. -/
  | k0 : Sector
  /-- The six two-phi-pair channels, multiplicity `6`. -/
  | k2 : Sector
  /-- The four three-phi-pair channels, multiplicity `4`. -/
  | k3 : Sector
  /-- The all-phi channel with internal color `0`. -/
  | aphi0 : Sector
  /-- The all-phi channel with internal color `2` (phi). -/
  | aphiphi : Sector
deriving DecidableEq

/-- A channel of the balanced 4-pair tree: its sector class, the four
sector colors `s₁ … s₄ ∈ {0, 2}` of the pair fusions, and the internal
color `a ∈ {0, 2}`. -/
structure Channel : Type where
  /-- The sector class of the channel. -/
  sector : Sector
  /-- First pair-fusion sector color. -/
  s1 : ℕ
  /-- Second pair-fusion sector color. -/
  s2 : ℕ
  /-- Third pair-fusion sector color. -/
  s3 : ℕ
  /-- Fourth pair-fusion sector color. -/
  s4 : ℕ
  /-- The internal color of the balanced tree. -/
  internal : ℕ
deriving DecidableEq

/-- The tree monomial of the channel `(s₁, s₂, s₃, s₄)` with internal color
`a`: the product `Π_i N_{22}^{s_i} · N_{s₁s₂}^a · N_{s₃s₄}^a · N_{aa}^0`
(exponent pairs add). -/
def treePoly (s1 s2 s3 s4 a : ℕ) : Poly :=
  mulP (structConst 2 2 s1) (mulP (structConst 2 2 s2)
    (mulP (structConst 2 2 s3) (mulP (structConst 2 2 s4)
      (mulP (structConst s1 s2 a) (mulP (structConst s3 s4 a)
        (structConst a a 0))))))

/-- The tree monomial of a `Channel`. -/
def channelPoly (ch : Channel) : Poly :=
  treePoly ch.s1 ch.s2 ch.s3 ch.s4 ch.internal

/-- The thirteen channels of the cutoff-three block space, with the forced
internal colors: `k0 = (0,0,0,0)ᵃ⁼⁰`; six `k2` (the report's labels
`(0,0,1,1), (0,1,1,0), (0,1,0,1), (1,1,0,0), (1,0,1,0), (1,0,0,1)` scaled
by `2`); four `k3` (`(0,1,1,1), (1,1,1,0), (1,0,1,1), (1,1,0,1)` scaled by
`2`); and the two all-phi channels. -/
def channels : List Channel :=
  [⟨.k0, 0, 0, 0, 0, 0⟩,
   ⟨.k2, 0, 0, 2, 2, 0⟩, ⟨.k2, 0, 2, 2, 0, 2⟩, ⟨.k2, 0, 2, 0, 2, 2⟩,
   ⟨.k2, 2, 2, 0, 0, 0⟩, ⟨.k2, 2, 0, 2, 0, 2⟩, ⟨.k2, 2, 0, 0, 2, 2⟩,
   ⟨.k3, 0, 2, 2, 2, 2⟩, ⟨.k3, 2, 2, 2, 0, 2⟩, ⟨.k3, 2, 0, 2, 2, 2⟩,
   ⟨.k3, 2, 2, 0, 2, 2⟩,
   ⟨.aphi0, 2, 2, 2, 2, 0⟩,
   ⟨.aphiphi, 2, 2, 2, 2, 2⟩]

/-- There are thirteen channels. -/
theorem channels_length : channels.length = 13 := rfl

/-- The sector class sizes are `(1, 6, 4, 1, 1)`. -/
theorem channel_class_sizes :
    (channels.countP fun ch => decide (ch.sector = Sector.k0)) = 1 ∧
    (channels.countP fun ch => decide (ch.sector = Sector.k2)) = 6 ∧
    (channels.countP fun ch => decide (ch.sector = Sector.k3)) = 4 ∧
    (channels.countP fun ch => decide (ch.sector = Sector.aphi0)) = 1 ∧
    (channels.countP fun ch => decide (ch.sector = Sector.aphiphi)) = 1 := by
  decide

/-- An internal color is admissible for a labeled tree when both pair
fusions have nonzero structure constant into it. -/
def ValidInternal (s1 s2 s3 s4 a : ℕ) : Prop :=
  structConst s1 s2 a ≠ [] ∧ structConst s3 s4 a ≠ []

/-- Admissibility of an internal color is decidable (the structure
constants are computable). -/
instance (s1 s2 s3 s4 a : ℕ) : Decidable (ValidInternal s1 s2 s3 s4 a) :=
  inferInstanceAs (Decidable (structConst s1 s2 a ≠ [] ∧ structConst s3 s4 a ≠ []))

/-- Every listed channel carries an admissible internal color. -/
theorem channels_admissible :
    ∀ ch ∈ channels, ValidInternal ch.s1 ch.s2 ch.s3 ch.s4 ch.internal := by
  decide

/-- On every multiplicity-one channel (all sectors except the two
all-phi channels) the internal color is **forced**: among the colors
`{0, 1, 2, 3}` exactly the listed one is admissible. -/
theorem internal_color_forced :
    ∀ ch ∈ channels, ch.sector ≠ Sector.aphi0 → ch.sector ≠ Sector.aphiphi →
      ∀ a : Fin 4,
        ValidInternal ch.s1 ch.s2 ch.s3 ch.s4 (a : ℕ) ↔ (a : ℕ) = ch.internal := by
  decide

/-- The all-phi label `(2, 2, 2, 2)` admits exactly the internal colors
`{0, 2}` — the two all-phi channels. -/
theorem internal_color_allphi :
    ∀ a : Fin 4, ValidInternal 2 2 2 2 (a : ℕ) ↔ (a : ℕ) = 0 ∨ (a : ℕ) = 2 := by
  decide

/-! ## §4  Channel bidegrees and the squeeze polynomial -/

/-- Extract the exponent pair of a coefficient-one monomial; `none` for
anything that is not a single monomial with coefficient `1`. -/
def bidegree? : Poly → Option Mono
  | [(m, c)] => if c = 1 then some m else none
  | _ => none

/-- The recorded Hodge bidegree of each sector class:
`k0 ↦ (4,4)`, `k2 ↦ (3,5)`, `k3 ↦ (2,6)`, `aphi0 ↦ (2,6)`,
`aphiphi ↦ (1,7)`.  Derived from the tree monomials by
`channel_bidegrees`. -/
def sectorBidegree : Sector → Mono
  | .k0 => (4, 4)
  | .k2 => (3, 5)
  | .k3 => (2, 6)
  | .aphi0 => (2, 6)
  | .aphiphi => (1, 7)

/-- Class `k0 = (0,0,0,0)`, internal `0`: bidegree `(4, 4)`. -/
theorem k0_channel_bidegree : bidegree? (treePoly 0 0 0 0 0) = some (4, 4) := by
  decide

/-- All six `k2` channels have bidegree `(3, 5)`. -/
theorem k2_channel_bidegrees :
    ∀ ch ∈ channels, ch.sector = Sector.k2 →
      bidegree? (channelPoly ch) = some (3, 5) := by
  decide

/-- All four `k3` channels have bidegree `(2, 6)`. -/
theorem k3_channel_bidegrees :
    ∀ ch ∈ channels, ch.sector = Sector.k3 →
      bidegree? (channelPoly ch) = some (2, 6) := by
  decide

/-- The all-phi channel with internal color `0` has bidegree `(2, 6)`. -/
theorem aphi0_channel_bidegree : bidegree? (treePoly 2 2 2 2 0) = some (2, 6) := by
  decide

/-- The all-phi channel with internal color `2` has bidegree `(1, 7)`. -/
theorem aphiphi_channel_bidegree : bidegree? (treePoly 2 2 2 2 2) = some (1, 7) := by
  decide

/-- Every channel's tree monomial is a coefficient-one monomial whose
bidegree is the recorded sector bidegree. -/
theorem channel_bidegrees :
    ∀ ch ∈ channels, bidegree? (channelPoly ch) = some (sectorBidegree ch.sector) := by
  decide

/-- Every sector bidegree has total weight `p + q = 8`. -/
theorem sectorBidegree_weight_eight (s : Sector) :
    (sectorBidegree s).1 + (sectorBidegree s).2 = 8 := by
  cases s <;> rfl

/-- Every sector bidegree has even `p - q` (computed in `ℤ`;
`p - q ∈ {0, -2, -4, -6}` here). -/
theorem sectorBidegree_diff_even (s : Sector) :
    (((sectorBidegree s).1 : ℤ) - ((sectorBidegree s).2 : ℤ)) % 2 = 0 := by
  cases s <;> decide

/-- The Feigin–Frenkel/Hodge squeeze polynomial at `n = 2`, `N = 3`:
`u v⁷ + 5 u² v⁶ + 6 u³ v⁵ + u⁴ v⁴`, in normal form. -/
def squeezePoly : Poly :=
  [((1, 7), 1), ((2, 6), 5), ((3, 5), 6), ((4, 4), 1)]

/-- The multiset of the thirteen channel monomials (sector multiplicities
`(1, 6, 4, 1, 1)`) sums to the squeeze polynomial. -/
theorem channel_sum : sumP (channels.map channelPoly) = squeezePoly := by decide

/-! ## §5  The Weil sign and Theorem A at cutoff three -/

/-- The Weil sign of a bidegree with even `p - q`: `i^(p-q) = +1` when
`4 ∣ p - q` and `-1` otherwise.  The difference is taken in `ℤ` (here
`p - q ∈ {0, -2, -4, -6}`), avoiding truncated `ℕ` subtraction. -/
def weil (m : Mono) : ℤ :=
  if (((m.1 : ℤ)) - ((m.2 : ℤ))) % 4 = 0 then 1 else -1

/-- **External verified input** (Dotsenko–Fateev channel norms): the signs of
`X = (1, C², C⁴, C⁴, C⁶)` on the sectors `(k0; k2; k3; aphi0; aphiphi)`,
with `C² < 0`.  Encoded as data; not derived in Lean. -/
def Xsign : Sector → ℤ
  | .k0 => 1
  | .k2 => -1
  | .k3 => 1
  | .aphi0 => 1
  | .aphiphi => -1

/-- **External verified input** (canonical bilinear channel constants): the signs of
`κ = (1/125, -1/125, 1/250, 1/125, -1/500)` on the sectors
`(k0; k2; k3; aphi0; aphiphi)`.  Encoded as data; not derived in Lean. -/
def kappaSign : Sector → ℤ
  | .k0 => 1
  | .k2 => -1
  | .k3 => 1
  | .aphi0 => 1
  | .aphiphi => -1

/-- **Theorem A at cutoff three (Weil parity)**: for every sector, the
recorded Dotsenko–Fateev sign and the recorded bilinear channel-constant
sign both equal the Weil sign `i^(p-q)` of the derived Hodge bidegree. -/
theorem weil_parity_cutoff_three (s : Sector) :
    Xsign s = weil (sectorBidegree s) ∧ kappaSign s = weil (sectorBidegree s) := by
  cases s <;> exact ⟨by decide, by decide⟩

/-! ## §6  The `MvPolynomial` bridge

`toMv` interprets a normal-form list as an element of
`MvPolynomial (Fin 2) ℤ` (variable `0` is `u`, variable `1` is `v`) and is
proved to intertwine every arithmetic operation used above.  This
certifies the list arithmetic against Mathlib's polynomial ring and
restates the squeeze identity there. -/

/-- The monomial `c · u^p v^q` in `MvPolynomial (Fin 2) ℤ` (variable `0`
is `u`, variable `1` is `v`). -/
noncomputable def mvMono (m : Mono) (c : ℤ) : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.C c * MvPolynomial.X 0 ^ m.1 * MvPolynomial.X 1 ^ m.2

/-- The evaluation of a normal-form list in `MvPolynomial (Fin 2) ℤ`. -/
noncomputable def toMv : Poly → MvPolynomial (Fin 2) ℤ
  | [] => 0
  | t :: p => mvMono t.1 t.2 + toMv p

/-- Monomials at the same exponent pair add on coefficients. -/
theorem mvMono_add_same (m : Mono) (c d : ℤ) :
    mvMono m c + mvMono m d = mvMono m (c + d) := by
  simp only [mvMono, map_add, add_mul]

/-- The zero-coefficient monomial vanishes. -/
theorem mvMono_zero (m : Mono) : mvMono m 0 = 0 := by
  simp [mvMono]

/-- Negation of a monomial negates its coefficient. -/
theorem mvMono_neg (m : Mono) (c : ℤ) : mvMono m (-c) = -mvMono m c := by
  simp [mvMono]

/-- Product of monomials: exponent pairs add, coefficients multiply. -/
theorem mvMono_mul (m n : Mono) (c d : ℤ) :
    mvMono m c * mvMono n d = mvMono (m.1 + n.1, m.2 + n.2) (c * d) := by
  simp only [mvMono, map_mul, pow_add]
  ring

/-- The merging insertion is addition of the inserted monomial. -/
theorem toMv_insertMono (m : Mono) (c : ℤ) (q : Poly) :
    toMv (insertMono m c q) = mvMono m c + toMv q := by
  induction q with
  | nil => simp [insertMono, toMv]
  | cons t q ih =>
    obtain ⟨n, d⟩ := t
    by_cases h₁ : MonoLt m n
    · simp [insertMono, h₁, toMv]
    · by_cases h₂ : MonoLt n m
      · simp only [insertMono, if_neg h₁, if_pos h₂, toMv, ih]
        ring
      · have hmn : m = n := eq_of_not_monoLt h₁ h₂
        subst hmn
        by_cases h₃ : c + d = 0
        · simp only [insertMono, if_neg h₁, if_pos h₃, toMv]
          rw [← add_assoc, mvMono_add_same, h₃, mvMono_zero, zero_add]
        · simp only [insertMono, if_neg h₁, if_neg h₃, toMv]
          rw [← add_assoc, mvMono_add_same]

/-- `addP` is polynomial addition. -/
theorem toMv_addP (p q : Poly) : toMv (addP p q) = toMv p + toMv q := by
  induction p with
  | nil => simp [addP, toMv]
  | cons t p ih =>
    change toMv (insertMono t.1 t.2 (addP p q)) = toMv (t :: p) + toMv q
    rw [toMv_insertMono, ih]
    simp only [toMv]
    ring

/-- `negP` is polynomial negation. -/
theorem toMv_negP (p : Poly) : toMv (negP p) = -toMv p := by
  induction p with
  | nil => simp [negP, toMv]
  | cons t p ih =>
    change toMv ((t.1, -t.2) :: negP p) = -toMv (t :: p)
    simp only [toMv, ih, mvMono_neg]
    ring

/-- `subP` is polynomial subtraction (the fusion recursion's subtraction
is honest). -/
theorem toMv_subP (p q : Poly) : toMv (subP p q) = toMv p - toMv q := by
  rw [subP, toMv_addP, toMv_negP, sub_eq_add_neg]

/-- `monoMul` is multiplication by a monomial. -/
theorem toMv_monoMul (m : Mono) (c : ℤ) (p : Poly) :
    toMv (monoMul m c p) = mvMono m c * toMv p := by
  induction p with
  | nil => simp [monoMul, toMv]
  | cons t p ih =>
    change toMv (((m.1 + t.1.1, m.2 + t.1.2), c * t.2) :: monoMul m c p)
      = mvMono m c * toMv (t :: p)
    simp only [toMv, ih, mul_add, mvMono_mul]

/-- `mulP` is polynomial multiplication. -/
theorem toMv_mulP (p q : Poly) : toMv (mulP p q) = toMv p * toMv q := by
  induction p with
  | nil => simp [mulP, toMv]
  | cons t p ih =>
    change toMv (addP (monoMul t.1 t.2 q) (mulP p q)) = toMv (t :: p) * toMv q
    rw [toMv_addP, toMv_monoMul, ih]
    simp only [toMv]
    ring

/-- `sumP` is the sum of the evaluations. -/
theorem toMv_sumP (l : List Poly) : toMv (sumP l) = (l.map toMv).sum := by
  induction l with
  | nil => simp [sumP, toMv]
  | cons p l ih =>
    change toMv (addP p (sumP l)) = ((p :: l).map toMv).sum
    rw [toMv_addP, ih]
    simp

open MvPolynomial in
/-- The squeeze identity in Mathlib's polynomial ring: the thirteen
channel monomials sum to `u v⁷ + 5 u² v⁶ + 6 u³ v⁵ + u⁴ v⁴` in
`MvPolynomial (Fin 2) ℤ` (`u = X 0`, `v = X 1`). -/
theorem channel_sum_toMv :
    toMv (sumP (channels.map channelPoly))
      = X 0 * X 1 ^ 7 + C 5 * X 0 ^ 2 * X 1 ^ 6 + C 6 * X 0 ^ 3 * X 1 ^ 5
        + X 0 ^ 4 * X 1 ^ 4 := by
  rw [channel_sum]
  simp only [squeezePoly, toMv, mvMono, map_one]
  ring

/-! ## §7  Landing-degree forcing (pure combinatorics)

Class sizes `(k0, k2, k3, aphi0, aphiphi) = (1, 6, 4, 1, 1)`; flag
multiplicities `(l = 0, 1, 2, 3) = (1, 5, 6, 1)`.  A class-uniform landing
assigns one degree in `Fin 4` to each sector class; validity means the
induced multiplicity count matches the flag.  All theorems are proved by
enumeration of the `4⁵ = 1024` assignments. -/

/-- A class-uniform landing: one PBW landing degree per sector class. -/
structure Landing : Type where
  /-- Landing degree of the `k0` class (size 1). -/
  k0 : Fin 4
  /-- Landing degree of the `k2` class (size 6). -/
  k2 : Fin 4
  /-- Landing degree of the `k3` class (size 4). -/
  k3 : Fin 4
  /-- Landing degree of the `aphi0` class (size 1). -/
  aphi0 : Fin 4
  /-- Landing degree of the `aphiphi` class (size 1). -/
  aphiphi : Fin 4
deriving DecidableEq

/-- The landing viewed as a map from sector classes to degrees. -/
def Landing.deg (L : Landing) : Sector → Fin 4
  | .k0 => L.k0
  | .k2 => L.k2
  | .k3 => L.k3
  | .aphi0 => L.aphi0
  | .aphiphi => L.aphiphi

/-- The size of each sector class: `(1, 6, 4, 1, 1)`.  Matches the channel
list (`channel_class_sizes`). -/
def classSize : Sector → ℕ
  | .k0 => 1
  | .k2 => 6
  | .k3 => 4
  | .aphi0 => 1
  | .aphiphi => 1

/-- The flag multiplicities of the thirteen PBW words at cutoff three:
lengths `(0, 1, 2, 3)` occur `(1, 5, 6, 1)` times. -/
def flagMult (d : Fin 4) : ℕ :=
  if d = 0 then 1 else if d = 1 then 5 else if d = 2 then 6 else 1

/-- The number of channels a landing sends to the degree `d`. -/
def inducedCount (L : Landing) (d : Fin 4) : ℕ :=
  (if L.k0 = d then classSize .k0 else 0)
    + (if L.k2 = d then classSize .k2 else 0)
    + (if L.k3 = d then classSize .k3 else 0)
    + (if L.aphi0 = d then classSize .aphi0 else 0)
    + (if L.aphiphi = d then classSize .aphiphi else 0)

/-- A landing is uniform-valid when its induced multiplicity count matches
the flag multiplicities `(1, 5, 6, 1)`. -/
def IsUniformLanding (L : Landing) : Prop :=
  ∀ d : Fin 4, inducedCount L d = flagMult d

/-- Validity of a class-uniform landing is decidable (a finite count
check over the four degrees). -/
instance (L : Landing) : Decidable (IsUniformLanding L) :=
  inferInstanceAs (Decidable (∀ d : Fin 4, inducedCount L d = flagMult d))

/-- The six valid class-uniform landings: `k2 ↦ 2` and `k3 ↦ 1` always,
and the three singleton classes permute over the degrees `{0, 1, 3}`. -/
def validLandings : List Landing :=
  [⟨0, 2, 1, 1, 3⟩, ⟨0, 2, 1, 3, 1⟩, ⟨1, 2, 1, 0, 3⟩,
   ⟨1, 2, 1, 3, 0⟩, ⟨3, 2, 1, 0, 1⟩, ⟨3, 2, 1, 1, 0⟩]

/-- Enumeration kernel for `landing_count`: a landing is valid iff it is
one of the six listed, checked over all `4⁵ = 1024` assignments. -/
theorem landing_mem_ker :
    ∀ a b c d e : Fin 4,
      IsUniformLanding ⟨a, b, c, d, e⟩ ↔ (⟨a, b, c, d, e⟩ : Landing) ∈ validLandings := by
  decide

/-- **Exactly six** class-uniform landings match the flag multiplicities:
the list `validLandings` has length `6`, no duplicates, and contains
precisely the valid landings. -/
theorem landing_count :
    validLandings.length = 6 ∧ validLandings.Nodup ∧
      ∀ L : Landing, IsUniformLanding L ↔ L ∈ validLandings := by
  refine ⟨rfl, by decide, fun L => ?_⟩
  obtain ⟨a, b, c, d, e⟩ := L
  exact landing_mem_ker a b c d e

/-- Enumeration kernel for `landing_k2_k3_forced`. -/
theorem landing_forced_ker :
    ∀ a b c d e : Fin 4, IsUniformLanding ⟨a, b, c, d, e⟩ → b = 2 ∧ c = 1 := by
  decide

/-- The multiplicities alone force `l(k2) = 2` and `l(k3) = 1` on every
valid class-uniform landing. -/
theorem landing_k2_k3_forced (L : Landing) (h : IsUniformLanding L) :
    L.k2 = 2 ∧ L.k3 = 1 := by
  obtain ⟨a, b, c, d, e⟩ := L
  exact landing_forced_ker a b c d e h

/-- The opposite-Rees twist sector sign of a landing: `(-1)^l` per sector
class. -/
def twist (L : Landing) (s : Sector) : ℤ :=
  (-1) ^ ((L.deg s : ℕ))

/-- **External recorded data**: the option-(a) twist tuple
`(+1, +1, -1, -1, -1)` on the sectors `(k0; k2; k3; aphi0; aphiphi)`
(an external candidate, recorded here). -/
def optionA : Sector → ℤ
  | .k0 => 1
  | .k2 => 1
  | .k3 => -1
  | .aphi0 => -1
  | .aphiphi => -1

/-- **External recorded data**: the option-(c) twist tuple
`(+1, -1, +1, +1, +1)` on the sectors `(k0; k2; k3; aphi0; aphiphi)`. -/
def optionC : Sector → ℤ
  | .k0 => 1
  | .k2 => -1
  | .k3 => 1
  | .aphi0 => 1
  | .aphiphi => 1

/-- Enumeration kernel for `anchored_twist_eq_option_a`. -/
theorem anchored_ker :
    ∀ a b c d e : Fin 4, IsUniformLanding ⟨a, b, c, d, e⟩ → (a : ℕ) % 2 = 0 →
      a = 0 ∧ twist ⟨a, b, c, d, e⟩ Sector.k0 = 1
        ∧ twist ⟨a, b, c, d, e⟩ Sector.k2 = 1
        ∧ twist ⟨a, b, c, d, e⟩ Sector.k3 = -1
        ∧ twist ⟨a, b, c, d, e⟩ Sector.aphi0 = -1
        ∧ twist ⟨a, b, c, d, e⟩ Sector.aphiphi = -1 := by
  decide

/-- **Anchored landing forcing**: every valid class-uniform landing with
even vacuum degree has `l(k0) = 0`, and its induced twist tuple `(-1)^l`
is exactly option (a) — on both anchored survivors, since
`(-1)¹ = (-1)³`. -/
theorem anchored_twist_eq_option_a (L : Landing) (h : IsUniformLanding L)
    (h0 : (L.k0 : ℕ) % 2 = 0) :
    L.k0 = 0 ∧ ∀ s : Sector, twist L s = optionA s := by
  obtain ⟨a, b, c, d, e⟩ := L
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := anchored_ker a b c d e h h0
  refine ⟨h1, fun s => ?_⟩
  cases s
  exacts [h2, h3, h4, h5, h6]

/-- Enumeration kernel for `option_c_not_realizable`: the forced
`l(k2) = 2` makes the `k2` twist `+1` on every valid landing. -/
theorem twist_k2_ker :
    ∀ a b c d e : Fin 4, IsUniformLanding ⟨a, b, c, d, e⟩ →
      twist ⟨a, b, c, d, e⟩ Sector.k2 = 1 := by
  decide

/-- **Option (c) admits no landing realization**: no valid class-uniform
landing induces the twist tuple `(+1, -1, +1, +1, +1)` (its `k2` sign is
`+1` because `l(k2) = 2` is forced). -/
theorem option_c_not_realizable (L : Landing) (h : IsUniformLanding L) :
    ¬ ∀ s : Sector, twist L s = optionC s := by
  intro hs
  have h1 : twist L Sector.k2 = 1 := by
    obtain ⟨a, b, c, d, e⟩ := L
    exact twist_k2_ker a b c d e h
  have h2 := hs Sector.k2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ## §8  The bundle -/

open MvPolynomial in
/-- **The Weil-polarized option-(a) package** (a proved proposition,
not a hypothesis): (i) the thirteen channel monomials sum to the
Feigin–Frenkel/Hodge squeeze polynomial in `MvPolynomial (Fin 2) ℤ`;
(ii) Weil parity — both recorded channel sign tuples equal `i^(p-q)` of
the derived bidegrees, so the Weil-twisted physical form is
channel-diagonal with positive norms; (iii) every vacuum-anchored valid
class-uniform landing induces exactly the option-(a) twist; (iv) option
(c) admits no landing realization. -/
theorem weil_polarized_twist_option_a :
    toMv (sumP (channels.map channelPoly))
        = X 0 * X 1 ^ 7 + C 5 * X 0 ^ 2 * X 1 ^ 6 + C 6 * X 0 ^ 3 * X 1 ^ 5
            + X 0 ^ 4 * X 1 ^ 4
      ∧ (∀ s : Sector,
          Xsign s = weil (sectorBidegree s) ∧ kappaSign s = weil (sectorBidegree s))
      ∧ (∀ L : Landing, IsUniformLanding L → (L.k0 : ℕ) % 2 = 0 →
          ∀ s : Sector, twist L s = optionA s)
      ∧ ∀ L : Landing, IsUniformLanding L → ¬ ∀ s : Sector, twist L s = optionC s :=
  ⟨channel_sum_toMv, weil_parity_cutoff_three,
    fun L h h0 => (anchored_twist_eq_option_a L h h0).2,
    option_c_not_realizable⟩

end WeilParity
end VOA
