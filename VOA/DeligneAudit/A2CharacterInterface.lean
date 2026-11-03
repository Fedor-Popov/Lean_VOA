/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2Character
import VOA.DeligneAudit.A2Carrier

/-!
# The Demazure-sum interface between the carrier and character sides (A₂)

The remaining A₂ inequality `∑_p dim A2.Carrier p N ≤ dim V_N` (`CarrierCharacterLowerBound`, equal to
the `QuadraticCarrierUpperBound`) is split at the Demazure sum

  `D_N := [q^N] ∑_{n ≥ 0} q^n Hilb_q D(1,nθ) / (q)_n`,

with the carrier side proving `∑_p dim A2.Carrier p N ≤ D_N` and the character side proving
`D_N ≤ dim V_N`.

## Concrete definition of `D_N`

All series are handled through coefficient functions `ℕ → ℕ` (every series here has nonnegative
coefficients), so everything is computable and small values are checked by kernel `decide`.

* `qbinomCoeff n k N = [q^N] [n,k]_q`, by the q-Pascal rule `[n+1,k+1] = q^{n-k}[n,k] + [n,k+1]`
  (the same rule as `DeligneGaussian.qbinom`).
* `partitionsLe n N = [q^N] 1/(q)_n` (partitions of `N` into parts `≤ n`).
* `demazureHilb n N = [q^N] P_{(2n,n,0)}(1,1,1; q, 0)`, the `q`-Whittaker polynomial of `GL₃` at
  `x = 1`, by the Gelfand–Tsetlin branching rule with `t = 0` coefficients
  `ψ_{λ/μ} = ∏_i [λ_i - λ_{i+1}, λ_i - μ_i]_q`.

**Input used to read `demazureHilb n` as `Hilb_q D(1,nθ)`** (not formalized): U7,
`ch_{q} D(1,nθ) = P_{nθ}(x; q, 0)` (Sanderson; Ion; Chari–Ion with Fourier–Littelmann), and the
`t = 0` branching rule (Macdonald VI (7.13′)). An independent check (outside Lean)
compared the identification with the affine Demazure character formula for `n ≤ 7`. It was also
checked numerically (outside Lean) that `∑ q^n demazureHilb n / (q)_n` equals `∏(1+q^r)^8` through `q^15`, and that
`demazureHilb n` sums to `9^n` and equals `8 + q` at `n = 1`. In Lean the definition is simply what
it says; any consumer that needs `D(1,nθ)` itself must state U7 as a hypothesis.

## The character side

`D_N ≤ dim V_N` is split at `F_N := [q^N] ∏_{r ≥ 1}(1+q^r)^8`:

* `StarIdentity` — `D_N = F_N` for all `N` (the paper's A₂ identity, Macdonald `t = 0`).
  **Proved:** `A2.starIdentity` (`A2Headline.lean`, via `starIdentity_of_fourTriangular`);
* `KacWakimotoLowerBound` — `F_N ≤ dim L_{-3/2}(sl₃)_N` (half of KW 1612.07423 Rem. 1 + Ex. 2).
  **Proved** via the AK MLDE: `A2.kacWakimotoLowerBound_of_productMLDE A2.a2ProductMLDE`
  (`DeligneVacuumRelationA2.lean`, `DeligneMLDEProduct.lean`); in fact with equality,
  `A2.finrank_eq_mldeCoeff'` and `A2.productCoeff_eq_mldeCoeff'`.

Both are stated here as named hypothesis structures, never axioms.
-/

namespace VOA.DeligneAudit.A2

open VertexOperatorAlgebra

/-! ## Coefficient arithmetic -/

/-- `[q^N]` of the Gaussian binomial `[n,k]_q`. -/
def qbinomCoeff : ℕ → ℕ → ℕ → ℕ
  | _, 0, N => if N = 0 then 1 else 0
  | 0, _ + 1, _ => 0
  | n + 1, k + 1, N =>
      (if n - k ≤ N then qbinomCoeff n k (N - (n - k)) else 0) + qbinomCoeff n (k + 1) N

/-- Coefficient of a product of two series. -/
def conv (f g : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (N + 1), f i * g (N - i)

/-- `[q^N] 1/(q)_n`: partitions of `N` into parts of size at most `n`. -/
def partitionsLe : ℕ → ℕ → ℕ
  | 0, N => if N = 0 then 1 else 0
  | n + 1, N => ∑ j ∈ Finset.range (N / (n + 1) + 1), partitionsLe n (N - j * (n + 1))

/-- `[q^N] P_{(m₁,m₂)}(1,1; q, 0)`. -/
def gl2Hilb (m₁ m₂ N : ℕ) : ℕ :=
  ∑ ν ∈ Finset.Icc m₂ m₁, qbinomCoeff (m₁ - m₂) (m₁ - ν) N

/-- `[q^N] P_{(l₁,l₂,l₃)}(1,1,1; q, 0)` by Gelfand–Tsetlin branching at `t = 0`. -/
def gl3Hilb (l₁ l₂ l₃ N : ℕ) : ℕ :=
  ∑ m₁ ∈ Finset.Icc l₂ l₁, ∑ m₂ ∈ Finset.Icc l₃ l₂,
    conv (conv (qbinomCoeff (l₁ - l₂) (l₁ - m₁)) (qbinomCoeff (l₂ - l₃) (l₂ - m₂)))
      (gl2Hilb m₁ m₂) N

/-- `[q^N] Hilb_q D(1,nθ)` for `sl₃`, as the `q`-Whittaker polynomial `P_{(2n,n,0)}(1,1,1;q,0)`
(identification: input U7, see the module docstring). -/
def demazureHilb (n N : ℕ) : ℕ := gl3Hilb (2 * n) n 0 N

/-- **The Demazure sum** `D_N = [q^N] ∑_n q^n Hilb_q D(1,nθ)/(q)_n`. -/
def demazureCoeff (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), conv (demazureHilb n) (partitionsLe n) (N - n)

/-- `[q^N] ∏_{r=1}^{R} (1+q^r)^8`. -/
def fermionCoeff : ℕ → ℕ → ℕ
  | 0, N => if N = 0 then 1 else 0
  | R + 1, N =>
      ∑ j ∈ Finset.range 9,
        if j * (R + 1) ≤ N then Nat.choose 8 j * fermionCoeff R (N - j * (R + 1)) else 0

/-- `F_N = [q^N] ∏_{r ≥ 1}(1+q^r)^8` (factors with `r > N` do not contribute). -/
def productCoeff (N : ℕ) : ℕ := fermionCoeff N N

/-! ## Machine checks of the definitions -/

/-- `Hilb D(1,θ) = 8 + q` (the calibration that pins the convention). -/
theorem demazureHilb_one : (List.range 3).map (demazureHilb 1) = [8, 1, 0] := by decide +kernel

/-- The first Demazure-sum coefficients: `1, 8, 36, 128, 394`. -/
theorem demazureCoeff_small :
    (List.range 5).map demazureCoeff = [1, 8, 36, 128, 394] := by decide +kernel

/-- The first coefficients of `∏(1+q^r)^8`: `1, 8, 36, 128, 394`. -/
theorem productCoeff_small :
    (List.range 5).map productCoeff = [1, 8, 36, 128, 394] := by decide +kernel

/-- The star identity holds for `N ≤ 4` by computation. -/
theorem demazureCoeff_eq_productCoeff_of_le_four (N : ℕ) (hN : N ≤ 4) :
    demazureCoeff N = productCoeff N := by
  interval_cases N <;> decide +kernel

/-! ## Named inputs (character side) -/

/-- **(⋆) for A₂**: the Demazure sum equals `∏(1+q^r)^8` (paper's Macdonald `t = 0` argument).
Proved: `A2.starIdentity` (`A2Headline.lean`). -/
structure StarIdentity : Prop where
  eq : ∀ N, demazureCoeff N = productCoeff N

/-- **Kac–Wakimoto, lower half**: `[q^N] ∏(1+q^r)^8 ≤ dim L_{-3/2}(sl₃)_N`.
Proved: `A2.kacWakimotoLowerBound_of_productMLDE A2.a2ProductMLDE`. -/
structure KacWakimotoLowerBound : Prop where
  le : ∀ N : ℕ, productCoeff N ≤ Module.finrank ℂ (W.grading N)

/-- The character side `D_N ≤ dim V_N`, as the target. -/
structure DemazureCharacterBound : Prop where
  le : ∀ N : ℕ, demazureCoeff N ≤ Module.finrank ℂ (W.grading N)

/-- The character side from the two named inputs. -/
theorem demazureCharacterBound_of_inputs (hstar : StarIdentity) (hkw : KacWakimotoLowerBound) :
    DemazureCharacterBound :=
  ⟨fun N => (hstar.eq N).le.trans (hkw.le N)⟩

/-! ## Glue -/

/-- **The split.** A carrier bound by the Demazure sum and the character side give the remaining A₂
inequality.  Stated for any carrier family; the A₂ instance is `A2.Carrier`. -/
theorem carrierCharacterLowerBound_of_demazure
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)] [∀ p N, Module ℂ (Carrier p N)]
    (hcar : ∀ N, (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)) ≤ demazureCoeff N)
    (hchr : ∀ N : ℕ, demazureCoeff N ≤ Module.finrank ℂ (W.grading N)) :
    CarrierCharacterLowerBound W Carrier :=
  fun N => (hcar N).trans (hchr N)

/-- The split for the `A2.Carrier`. -/
theorem carrierCharacterLowerBound_A2Carrier
    (hcar : ∀ N, (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)) ≤ demazureCoeff N)
    (hchr : DemazureCharacterBound) :
    CarrierCharacterLowerBound W Carrier :=
  carrierCharacterLowerBound_of_demazure Carrier hcar hchr.le

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.demazureCoeff_small
#print axioms VOA.DeligneAudit.A2.productCoeff_small
#print axioms VOA.DeligneAudit.A2.demazureCoeff_eq_productCoeff_of_le_four
#print axioms VOA.DeligneAudit.A2.demazureCharacterBound_of_inputs
#print axioms VOA.DeligneAudit.A2.carrierCharacterLowerBound_of_demazure
#print axioms VOA.DeligneAudit.A2.carrierCharacterLowerBound_A2Carrier
end AxiomAudit
