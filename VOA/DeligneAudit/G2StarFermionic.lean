/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2StarReduction
import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# The G₂ deep half split at a fermionic formula

`G2DemazureEqKW` (Demazure sum = Kac–Wakimoto form) is split into two named statements of very
different nature:

* **`G2DemazureFermionic`** (representation theory):
  `Hilb_q D(1,nθ) = ∑_λ dim V(λ) X_{n,λ}(q)`, with
  `X_{n,λ}` the Hatayama–Kuniba–Okado–Takagi–Yamada fermionic sum for `(W^{(2)}_1)^{⊗n}` in
  `G₂^{(1)}` (`W^{(2)}_1 = V(θ) ⊕ ℂ`, the long-root Kirillov–Reshetikhin module):

    `X_{n,λ}(q) = ∑_{m¹ ⊢ N₁, m² ⊢ N₂} q^{Q(m)}
    ∏_{a,j} [p^{(a)}_j + m^{(a)}_j ; m^{(a)}_j]_q`,

  `N₁ = 3n - 2a₁ - 3a₂`, `N₂ = 2n - a₁ - 2a₂` (`λ = a₁ω₁ + a₂ω₂`, `ω₁` short),
  `Q = ∑_{x,y∈m¹} min(x,y) + ∑_{x,y∈m²} min(x,y) - ∑_{x∈m¹,y∈m²} min(x,3y)`,
  `p^{(1)}_j = -2∑_{y∈m¹} min(j,y) + ∑_{y∈m²} min(j,3y)`,
  `p^{(2)}_j = n·min(j,1) - 2∑_{y∈m²} min(j,y) + ∑_{y∈m¹} min(3j,y)`, all `p ≥ 0`.
  This is `D(1,nθ) ≅ W(θ)^{*n}` (Fourier–Littelmann / Chari–Ion) plus `X = M` (HKOTY).
  Checked numerically for every `λ` and `n ≤ 8` (graded multiplicities, not only dimensions;
  outside Lean).
* **`G2FermionicKW`** (a single `q`-series identity, no representation theory):
  `∑_n qⁿ (∑_λ dim V(λ) X_{n,λ}(q)) / (q)_n = θ_{A₂}(q)(q³;q³)⁶/(q;q)⁸`.
  Checked through `q⁸` (it follows numerically from the two checks above).

`g2DemazureEqKW_of_fermionic : G2DemazureFermionic → G2FermionicKW → G2DemazureEqKW`.
-/

namespace VOA.DeligneAudit.G2Star

open PowerSeries VOA.DeligneAudit.DeligneCharacter VOA.DeligneAudit.A2

open scoped BigOperators

/-! ## The fermionic sum -/

/-- `∑_{x ∈ s, y ∈ t} min(x, c·y)`. -/
def minSum (c : ℕ) (s t : Multiset ℕ) : ℤ :=
  ((s.map fun x => (t.map fun y => (min x (c * y) : ℤ)).sum).sum)

/-- The quadratic form `Q(m)`. -/
def fermQ (m1 m2 : Multiset ℕ) : ℤ := minSum 1 m1 m1 + minSum 1 m2 m2 - minSum 3 m1 m2

/-- Vacancy number `p^{(1)}_j`. -/
def vac1 (m1 m2 : Multiset ℕ) (j : ℕ) : ℤ :=
  -2 * (m1.map fun y => (min j y : ℤ)).sum + (m2.map fun y => (min j (3 * y) : ℤ)).sum

/-- Vacancy number `p^{(2)}_j` (with `n` copies of the KR module). -/
def vac2 (n : ℕ) (m1 m2 : Multiset ℕ) (j : ℕ) : ℤ :=
  (n * min j 1 : ℤ) - 2 * (m2.map fun y => (min j y : ℤ)).sum +
    (m1.map fun y => (min (3 * j) y : ℤ)).sum

/-- The binomial data `(p_j + m_j, m_j)` of one configuration, as a list. -/
def binomData (n : ℕ) (m1 m2 : Multiset ℕ) : List (ℤ × ℕ) :=
  (m1.toFinset.sort (· ≤ ·)).map (fun j => (vac1 m1 m2 j, m1.count j)) ++
    (m2.toFinset.sort (· ≤ ·)).map (fun j => (vac2 n m1 m2 j, m2.count j))

/-- `[q^N] ∏ [p + m ; m]_q` for a list of `(p, m)` (all `p ≥ 0` assumed). -/
def binomProdCoeff : List (ℤ × ℕ) → ℕ → ℕ
  | [], N => if N = 0 then 1 else 0
  | (p, m) :: l, N => conv (qbinomCoeff (p.toNat + m) m) (binomProdCoeff l) N

/-- `[q^N]` of the contribution of one configuration `(m¹, m²)`. -/
def configCoeff (n : ℕ) (m1 m2 : Multiset ℕ) (N : ℕ) : ℕ :=
  if (∀ x ∈ binomData n m1 m2, 0 ≤ x.1) ∧ 0 ≤ fermQ m1 m2 ∧ (fermQ m1 m2).toNat ≤ N then
    binomProdCoeff (binomData n m1 m2) (N - (fermQ m1 m2).toNat)
  else 0

/-- `[q^N] X_{n,λ}(q)`, `λ = a₁ω₁ + a₂ω₂`. -/
def g2FermX (n a1 a2 N : ℕ) : ℕ :=
  if 2 * a1 + 3 * a2 ≤ 3 * n ∧ a1 + 2 * a2 ≤ 2 * n then
    ∑ m1 : (3 * n - 2 * a1 - 3 * a2).Partition, ∑ m2 : (2 * n - a1 - 2 * a2).Partition,
      configCoeff n m1.parts m2.parts N
  else 0

/-- Weyl's dimension formula for `G₂`, `λ = a₁ω₁ + a₂ω₂` (`ω₁` short). -/
def g2Dim (a1 a2 : ℕ) : ℕ :=
  (a1 + 1) * (a2 + 1) * (a1 + a2 + 2) * (a1 + 2 * a2 + 3) * (a1 + 3 * a2 + 4) *
    (2 * a1 + 3 * a2 + 5) / 120

/-- `[q^N] ∑_λ dim V(λ) X_{n,λ}(q)` (the fermionic Hilbert series). -/
def g2FermHilb (n N : ℕ) : ℕ :=
  ∑ a1 ∈ Finset.range (3 * n + 1), ∑ a2 ∈ Finset.range (n + 1), g2Dim a1 a2 * g2FermX n a1 a2 N

/-! ## The split -/

/-- **Named (representation theory)**: the Demazure Hilbert series is the fermionic one. -/
structure G2DemazureFermionic : Prop where
  eq : ∀ n N, g2DemazureHilb n N = g2FermHilb n N

/-- **Named (one `q`-series identity)**: the fermionic Demazure sum is the Kac–Wakimoto form. -/
structure G2FermionicKW : Prop where
  eq : ∀ N, ((demazureSumCoeff g2FermHilb N : ℕ) : ℤ) = coeff N g2KW

/-- **`G2DemazureEqKW` from the fermionic split.** -/
theorem g2DemazureEqKW_of_fermionic (h1 : G2DemazureFermionic) (h2 : G2FermionicKW) :
    G2DemazureEqKW := by
  refine ⟨PowerSeries.ext fun N => ?_⟩
  have hf : g2DemazureHilb = g2FermHilb := funext fun n => funext fun M => h1.eq n M
  rw [g2DemazureSeries, coeff_mk, hf]
  exact h2.eq N

end VOA.DeligneAudit.G2Star

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Star.g2DemazureEqKW_of_fermionic
end AxiomAudit
