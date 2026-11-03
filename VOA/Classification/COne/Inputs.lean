/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.Statement
import VOA.Classification.COne.RankOneTheta
import VOA.Classification.COne.WeightPositivity
import VOA.Modularity.ConvergenceBridge
import VOA.Modularity.SquareBracketGrading
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The external inputs of the Gannon–Rayhaun classification (A3)

T. Gannon and B. C. Rayhaun, *Classification of rational `c = 1` vertex operator algebras and
vertex operator superalgebras*, arXiv:2609.00122, use a number of published theorems as black
boxes. This file states each of them as a `Prop`. Nothing here is assumed: every input is a
`def … : Prop`, and `Conditional.lean` takes them as explicit hypotheses.

## Principle

Every input is a **published theorem at its own natural generality**: quantified over all VOAs
(or all modular forms), never "the rest of the paper". The paper's own new steps (Lemmas
3.9–3.11, Proposition 3.12, Theorem 2.18, eq. (3.40)) are *not* inputs; they are proved, or are
recorded as explicit, named gaps in `Conditional.lean`, consuming B1–B4.

## The inputs

| name | content | source |
|---|---|---|
| `IModData` | modular data of a nice VOA | Zhu; DLM; Huang; GR Thm 2.2, (2.35) |
| `ICongruenceGalois` | `Γ(N)`-invariance; `ρ(γ_ℓ)` is a signed permutation | DLN; Coste–Gannon |
| `ISerreStark` | weight-½ θ-type forms are theta series | Serre–Stark 1977 |
| `IVirasoro` | `c = 1` Virasoro composition series of the vacuum character | Kac; Feigin–Fuchs |
| `ITannakian` | factorized `S` ⟹ `V ≅ W^G`, `ch_W = Σ d_a ch_a` | GR Props 2.13, 2.17 |
| `IDongMason` | nice, `c = 1`, `W₁ ≠ 0` ⟹ `W ≅ V_{2m}` | Dong–Mason 2004 Thm 3 |
| `IEnumeration` | `V_{2m}^G` is in the list for finite `G` | GR Prop C.4 (ADE; DN; DVVV) |

## Conventions

* `q = e^{2πiτ}`, `τ` in the upper half plane `0 < Im τ`, functions on `ℍ` are functions
  `ℂ → ℂ` constrained only on `0 < Im τ`.
* `SL(2, ℤ)` acts by `mobius γ τ = (aτ + b)/(cτ + d)`.
* Formal `q`-series are `PowerSeries`; the link to the analytic character is always an explicit
  `HasSum` (see `ModularData.IsModularData.char`).
-/

open Complex Finset Module

noncomputable section

namespace VOA.Classification.COne

open VOA

universe u

/-! ## Shared vocabulary -/

/-- The Möbius action of `SL(2, ℤ)` on `ℂ`: `γ · τ = (aτ + b)/(cτ + d)`. -/
def mobius (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1)

/-- The Jacobi theta function `θ(τ) = Σ_n q^{n²} = θ_{0,1,1}(τ)`, the multiplier reference of
"θ-type" forms (GR (3.10)). -/
def thetaRef (τ : ℂ) : ℂ := rankOneTheta 0 1 1 τ

/-- **Holomorphic θ-type modular form of weight `½` for `Γ₁(N)`** (GR, before Lemma 3.7;
Serre–Stark §1):
* holomorphic on the upper half plane;
* the multiplier system is that of `θ`: `f(γτ) θ(τ) = θ(γτ) f(τ)` for `γ ∈ Γ₁(N)` (cross-multiplied
  form of GR (3.10); `θ` has no zeros on `ℍ`);
* holomorphic at every cusp: for every `γ ∈ SL(2, ℤ)`, `|(cτ + d)^{-1/2} f(γτ)|` is bounded on
  `Im τ ≥ 1`. (For a form with a multiplier, `f|γ` has a Puiseux `q`-expansion, and boundedness
  at `i∞` is exactly the absence of negative powers.) -/
structure IsThetaTypeForm (N : ℕ) (f : ℂ → ℂ) : Prop where
  holo : DifferentiableOn ℂ f {τ : ℂ | 0 < τ.im}
  multiplier : ∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℂ, 0 < τ.im →
    f (mobius γ τ) * thetaRef τ = thetaRef (mobius γ τ) * f τ
  cusps : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ C : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
    ‖f (mobius γ τ)‖ ≤ C * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ)

/-- The graded dimension of a VOA as a formal power series, `Σ_n dim V_n qⁿ` (the vacuum
character without the `q^{-c/24}` shift). -/
def vacuumSeries {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) :
    PowerSeries ℤ :=
  PowerSeries.mk fun n => (finrank ℂ (V.grading n) : ℤ)

/-- Euler's function `∏_{n ≥ 1} (1 - qⁿ) = q^{-1/24} η(τ)` as a formal power series: the
`N`-th coefficient of the infinite product is that of the finite product over `n ≤ N`. -/
def eulerSeries : PowerSeries ℤ :=
  PowerSeries.mk fun N =>
    PowerSeries.coeff N (∏ n ∈ Finset.range N, (1 - PowerSeries.X ^ (n + 1) : PowerSeries ℤ))

/-! ## Modular data of a VOA -/

/-- **Candidate modular data** for a VOA `V`: a finite index set `ι` of simple modules with a
vacuum label, actual `V`-modules `module a`, conformal weights `h a ∈ ℚ`, characters
`ch a : ℂ → ℂ`, an `S`-matrix, `S₀₀` and quantum dimensions `d a`. The data carry no
properties; `IsModularData` says they are the modular data of `V`. -/
structure ModularData {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (V : VertexOperatorAlgebra 𝒱) where
  ι : Type
  [instFintype : Fintype ι]
  [instDecEq : DecidableEq ι]
  vac : ι
  carrier : ι → Type u
  [instACG : ∀ a, AddCommGroup (carrier a)]
  [instMod : ∀ a, Module ℂ (carrier a)]
  module : ∀ a, OrdVModule V (carrier a)
  h : ι → ℚ
  ch : ι → ℂ → ℂ
  S : ι → ι → ℂ
  S00 : ℝ
  d : ι → ℝ

attribute [instance] ModularData.instFintype ModularData.instDecEq ModularData.instACG
  ModularData.instMod

namespace ModularData

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-- `a` has integer conformal weight (`a ∈ Rep(V)_{h ∈ ℤ}`). Decidable: `h a ∈ ℚ`. -/
def IsIntWeight (D : ModularData V) (a : D.ι) : Prop := (D.h a).den = 1

instance (D : ModularData V) : DecidablePred D.IsIntWeight := fun a =>
  inferInstanceAs (Decidable ((D.h a).den = 1))

/-- `Rep(V)_{h∈ℤ}`, as a finset of labels. -/
def intLabels (D : ModularData V) : Finset D.ι := Finset.univ.filter D.IsIntWeight

/-- **The analytic one-point trace function** of the label `a` at the state `v`:
`T_a(v, τ) = Tr_{M_a} o(v) q^{L(0) - c/24} = Σ_n tr_{(M_a)_{h_a + n}} o(v) · q^{h_a + n - c/24}`,
evaluated through `qEvalAt` along the weight shift `h_a - c/24`. Definitionally Zhu's
`traceFun` (`VOA/Modularity/BlockSpanning.lean`) for the bundled family of `D.module`. -/
def trace (D : ModularData V) (a : D.ι) (v : 𝒱) (τ : UpperHalfPlane) : ℂ :=
  qEvalAt (onePoint (D.module a) v) ((D.h a : ℂ) - V.centralCharge / 24) τ

/-- **`S` is Zhu's `S`-matrix on ALL one-point functions** (Zhu 1996, Thm 5.3.3 / (5.3.18a) at
`γ = S`; DLM 2000): for every state `v` of square-bracket weight `n` (`L[0] v = n v`),
every label `a` and every `τ ∈ ℍ`,
`T_a(v, -1/τ) = τⁿ Σ_b S_ab T_b(v, τ)`.

At `v = 𝟙` (`n = 0`) this is the character law `S_transform`; but characters alone do not
determine `S` (`ch_M = ch_{M'}` for the contragredient — machine-checked in
`VOA.Huang.HuangModular.isModularDataWeak_perturbS`), whereas one-point functions of inequivalent
irreducibles are linearly independent, so this clause determines `S` uniquely
(`VOA.Huang.SPinning.S_unique_of_pinned`). -/
def SPinned (D : ModularData V) (S : D.ι → D.ι → ℂ) : Prop :=
  ∀ (n : ℕ) (v : 𝒱), v ∈ sqWeightSpace V (n : ℂ) → ∀ (a : D.ι) (τ : UpperHalfPlane),
    D.trace a v (ModularGroup.S • τ) = (τ : ℂ) ^ n * ∑ b, S a b * D.trace b v τ

/-- **The modular data of a nice VOA** (the content of `IModData`).

* (classification) `module a` is irreducible, every irreducible ordinary module (carrier in
  the universe of `V`) is isomorphic to exactly one `module a`, and `module vac ≅ V`;
* (grading) the weights of `module a` lie in `h a + ℕ`, with `h a` attained, `h vac = 0`;
* (characters, Zhu) `ch a τ = Σ_n dim (module a)_{h a + n} q^{h a + n - c/24}`, an honest
  convergent sum on `ℍ`; for the vacuum also `= Σ_n dim V_n q^{n - c/24}`;
* (S-matrix, Zhu / Huang) `ch a (-1/τ) = Σ_b S a b · ch b τ`;
* (S-pinning, Zhu 5.3.18a at `γ = S`) `S_pinned : D.SPinned D.S` — the same law for the
  one-point function of EVERY square-bracket homogeneous state; this, not `S_transform`, is what
  makes `S` unique (`VOA.Huang.SPinning.S_unique_of_pinned`). It is needed because the
  character-only form does not pin `S` (`VOA.Huang.HuangModular.isModularDataWeak_perturbS`);
* (pseudo-unitarity, GR (2.8) with `ε = +1`, and the remark after Def. 2.4) `S00 > 0`,
  `S vac vac = S00`, `S a vac = S vac a = S00 · d a` with `d a ≥ 1` the categorical
  (= Frobenius–Perron) dimensions;
* (Gannon 2005, (4.2a); GR (2.35)) `|S a b| ≤ S00 · d a · d b`. -/
structure IsModularData (D : ModularData V) : Prop where
  irred : ∀ a, (D.module a).IsIrreducible
  exhaust : ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (N : OrdVModule V M),
    N.IsIrreducible → ∃ a, Nonempty (ModuleEquiv V N (D.module a))
  distinct : ∀ a b, Nonempty (ModuleEquiv V (D.module a) (D.module b)) → a = b
  vac_iso : Nonempty (ModuleEquiv V (D.module D.vac) (adjointModule V))
  weight_support : ∀ a (α : ℂ), (D.module a).weight α ≠ ⊥ → ∃ n : ℕ, α = (D.h a : ℂ) + n
  weight_lowest : ∀ a, (D.module a).weight (D.h a : ℂ) ≠ ⊥
  h_vac : D.h D.vac = 0
  char : ∀ a (τ : ℂ), 0 < τ.im →
    HasSum (fun n : ℕ => (finrank ℂ ((D.module a).weight ((D.h a : ℂ) + n)) : ℂ) *
      cexp (2 * Real.pi * I * ((D.h a : ℂ) + n - V.centralCharge / 24) * τ)) (D.ch a τ)
  char_vac : ∀ τ : ℂ, 0 < τ.im →
    HasSum (fun n : ℕ => (finrank ℂ (V.grading n) : ℂ) *
      cexp (2 * Real.pi * I * ((n : ℂ) - V.centralCharge / 24) * τ)) (D.ch D.vac τ)
  S_transform : ∀ a (τ : ℂ), 0 < τ.im → D.ch a (-1 / τ) = ∑ b, D.S a b * D.ch b τ
  S_pinned : D.SPinned D.S
  S00_pos : 0 < D.S00
  S_vac_vac : D.S D.vac D.vac = D.S00
  d_ge_one : ∀ a, 1 ≤ D.d a
  S_vac_left : ∀ a, D.S D.vac a = D.S00 * D.d a
  S_vac_right : ∀ a, D.S a D.vac = D.S00 * D.d a
  S_bound : ∀ a b, ‖D.S a b‖ ≤ D.S00 * D.d a * D.d b

/-- `N` is a **level** for `D`: `N (h a - c/24) ∈ ℤ` for every `a`. The conductor `C_V` of
GR Theorem 2.3 is the least such `N`; every level is a multiple of it. -/
def IsLevel (D : ModularData V) (N : ℕ) : Prop :=
  0 < N ∧ ∀ a, ∃ k : ℤ, (N : ℂ) * ((D.h a : ℂ) - V.centralCharge / 24) = k

/-- The **Galois symmetry** of `D` at level `N` (Coste–Gannon; DLN): for `ℓ` coprime to `N` and
any `γ ≡ diag(ℓ, ℓ⁻¹) (mod N)`, `ρ(γ)` is a signed permutation matrix:
`ch a (γτ) = ε a · ch (π a) τ`, `ε a = ±1`. -/
def GaloisSymmetric (D : ModularData V) (N : ℕ) : Prop :=
  ∀ ℓ ℓ' : ℤ, ℓ * ℓ' ≡ 1 [ZMOD N] → ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
    γ 0 0 ≡ ℓ [ZMOD N] → γ 1 1 ≡ ℓ' [ZMOD N] → γ 0 1 ≡ 0 [ZMOD N] → γ 1 0 ≡ 0 [ZMOD N] →
    ∃ (π : D.ι ≃ D.ι) (ε : D.ι → ℂ), (∀ a, ε a = 1 ∨ ε a = -1) ∧
      ∀ a (τ : ℂ), 0 < τ.im → D.ch a (mobius γ τ) = ε a * D.ch (π a) τ

end ModularData

/-! ## The inputs -/

/-- **I-ModData.** Every nice VOA has modular data in the sense of
`ModularData.IsModularData`.

*Source.* Zhu (1996, Thms 5.3.2–5.3.3: convergence and `SL₂(ℤ)`-covariance of characters of
`C₂`-cofinite rational VOAs); Dong–Li–Mason (2000, Thm 11.3: rationality of `h_a`, finitely many
irreducibles); Huang (2008: `Rep(V)` is a modular tensor category, the Verlinde formula and
`S_ab/S₀₀ = s̃_ab`, GR Thm 2.2); pseudo-unitarity gives `ε = +1` in GR (2.8) and positive
categorical dimensions `d_a ≥ 1` (ENO 2005 / GR refs [70, 71]); the bound `|S_ab| ≤ S₀₀ d_a d_b`
is Gannon, *Modular data: the algebraic combinatorics of CFT* (2005), (4.2a), quoted as GR (2.35).

*Not vacuous.* Every clause is about the actual irreducible modules of `V` and their actual
graded dimensions (`char` is a `HasSum` of `finrank`s), so it constrains `V`. The `S`-matrix is
pinned by `S_pinned` (Zhu's `S`-law on ALL one-point functions), because one-point functions of
inequivalent irreducibles are linearly independent (`VOA.Huang.SPinning.S_unique_of_pinned`,
via `traceIndependent_of_bottomSeparation` and PBW). It is NOT pinned by `S_transform` alone:
characters do not separate a module from its contragredient (`ch_M = ch_{M'}`), and the
statement without `S_pinned` admits a continuum of `S`-matrices
(`VOA.Huang.HuangModular.isModularDataWeak_perturbS`).

*Not over-strong.* It says nothing specific to `c = 1`; it is the standard modular data package
that every nice VOA has (GR §2.1). It does not imply that `V` is Tannakian or a lattice orbifold. -/
def IModData : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∃ D : ModularData V, D.IsModularData

/-- **I-Congruence/Galois.** For nice `V` with modular data `D` and any level `N` of `D`:
1. (congruence property) every character is invariant under the principal congruence subgroup
   `Γ(N)`;
2. (Galois symmetry) `D.GaloisSymmetric N`.

*Source.* Dong–Lin–Ng, *Congruence property in conformal field theory*, Algebra & Number Theory
9 (2015), Theorem I (the kernel of the character representation contains `Γ(C_V)`) and their
Galois-symmetry results (`ρ(γ_ℓ) = σ_ℓ(S) S⁻¹`); Coste–Gannon (1994) and Ng–Schauenburg (2010)
for the Galois action `σ_ℓ(S_ab) = ε_ℓ(a) S_{π(a), b}`, so `ρ(γ_ℓ)` is a signed permutation matrix
(GR (3.19), (3.31), refs [35, 37, 95]). Stated for every level `N`, which is equivalent to the
conductor version because every level is a multiple of `C_V`.

*Not vacuous / not over-strong.* A statement about the actual characters `D.ch`; true for every
strongly rational VOA (no `c = 1`), and gives no information on which modules exist. -/
def ICongruenceGalois : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ D : ModularData V, D.IsModularData → ∀ N : ℕ, D.IsLevel N →
      (∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ a (τ : ℂ), 0 < τ.im →
        D.ch a (mobius γ τ) = D.ch a τ) ∧ D.GaloisSymmetric N

/-- **I-SerreStark.** For `4 ∣ N`, every holomorphic θ-type weight-½ form for `Γ₁(N)` is a
finite linear combination of the theta series `θ_{n₀,r,t}` (`rankOneTheta n₀ r t`) with
`r, t ≥ 1` and `4 t r² ∣ N`.

*Source.* J.-P. Serre and H. M. Stark, *Modular forms of weight 1/2*, LNM 627 (1977), Theorem A
with Corollaries 1 and 3, in the form quoted by GR in the proof of Lemma 3.9. (Serre–Stark's
basis `θ_{ψ,t} = Σ ψ(n) q^{tn²}` with `4 r(ψ)² t ∣ N` is a combination of the `θ_{n₀,r(ψ),t}`.)

*Not vacuous / not over-strong.* A theorem about modular forms only, at full generality; it
says nothing about VOAs. -/
def ISerreStark : Prop :=
  ∀ (N : ℕ) (f : ℂ → ℂ), 0 < N → 4 ∣ N → IsThetaTypeForm N f →
    ∃ (s : Finset (ℤ × ℕ × ℕ)) (coef : ℤ × ℕ × ℕ → ℂ),
      (∀ p ∈ s, 1 ≤ p.2.1 ∧ 1 ≤ p.2.2 ∧ 4 * p.2.2 * p.2.1 ^ 2 ∣ N) ∧
      ∀ τ : ℂ, 0 < τ.im → f τ = ∑ p ∈ s, coef p * rankOneTheta p.1 p.2.1 p.2.2 τ

/-- `ISerreStark` at levels divisible by `24` — the only levels at which the classification
uses it. -/
def ISerreStark24 : Prop :=
  ∀ (N : ℕ) (f : ℂ → ℂ), 0 < N → 24 ∣ N → IsThetaTypeForm N f →
    ∃ (s : Finset (ℤ × ℕ × ℕ)) (coef : ℤ × ℕ × ℕ → ℂ),
      (∀ p ∈ s, 1 ≤ p.2.1 ∧ 1 ≤ p.2.2 ∧ 4 * p.2.2 * p.2.1 ^ 2 ∣ N) ∧
      ∀ τ : ℂ, 0 < τ.im → f τ = ∑ p ∈ s, coef p * rankOneTheta p.1 p.2.1 p.2.2 τ

theorem iSerreStark24_of_iSerreStark (h : ISerreStark) : ISerreStark24 :=
  fun N f hN h24 hf => h N f hN ((show 4 ∣ 24 by norm_num).trans h24) hf

/-- **I-Virasoro.** For every nontrivial VOA of central charge `1`, `η · ch_V = Σ_h A_h η χ_h`
as formal `q`-series, with `A_h ∈ ℕ` the Jordan–Hölder multiplicities of the irreducible
`c = 1` Virasoro modules `L(1, h)` in `V`, and `A_0 = 1`. Concretely
`eulerSeries · vacuumSeries V = etaVirasoroSum A` (GR (3.5)–(3.7)); `etaVirasoroSum` uses
the `c = 1` irreducible characters GR (3.4).

*Source.* V. Kac (1979) determinant formula and Feigin–Fuchs (1984): at `c = 1`, `L(1,h)` is
degenerate iff `h = μ²/4`, with character `(q^{μ²/4} - q^{(μ/2+1)²})/η`, else `q^h/η`. The
character of a positive-energy Virasoro module with finite-dimensional weight spaces is the sum
of the characters of its composition factors (weight-by-weight Jordan–Hölder); CFT type gives
`A_0 = 1`. For integer weights only integer `μ/2` occur (`exists_nat_of_half_sq_eq`).

*Not vacuous.* A formal identity about the actual graded dimensions of `V`.
*Not over-strong.* It holds for every `c = 1` VOA, rational or not (e.g. the Heisenberg VOA), so
it carries no classification content by itself. The hypothesis `vacuum ≠ 0` excludes the zero
space, for which the identity would fail (`A_0 = 1` but `vacuumSeries = 0`). -/
def IVirasoro : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱),
    V.vacuum ≠ 0 → V.centralCharge = 1 →
      ∃ A : ℕ → ℕ, A 0 = 1 ∧ eulerSeries * vacuumSeries V = etaVirasoroSum A

/-- **I-Tannakian.** If `V` is nice with modular data `D` and `S_ab = S₀₀ d_a d_b` for all
integer-weight labels `a, b`, then there are a nice VOA `W` with the same central charge and a
finite group `G ≤ Aut W` with `V ≅ W^G`, and `W ≅ ⊕_{h_a ∈ ℤ} ℂ^{d_a} ⊗ V_a` as graded spaces:
`dim W_n = Σ_{h_a ∈ ℤ} d_a dim (V_a)_n` (GR (2.18)–(2.19)).

*Source.* GR Proposition 2.17 (`S_ab = S₀₀ d_a d_b` ⟹ `Rep(V)_{h∈ℤ}` symmetric, by Müger 2003
Prop. 2.5 / GR ref [88]; Tannakian by Deligne 2002 and the twist criterion, GR Prop 2.11) and
Proposition 2.13 (the regular algebra gives a conformal extension `W = V_{Rep(G)}`:
Kirillov–Ostrik 2002, Huang–Kirillov–Lepowsky 2015, Creutzig–Kanade–McRae; `W^G ≅ V` and
`Aut(A) ≅ G`: Davydov / DLM Schur–Weyl duality; niceness of `W`: GR Prop 2.7). **Flag:** this
input is a *GR proposition* assembled from published results (approved in the A3 design), not a
single published theorem; it is stated at the natural generality of GR §2.2 (any nice `V`,
no `c = 1`).

*Not vacuous.* The hypothesis is checkable on the data; the conclusion fixes the graded
dimension of `W` in terms of the modules of `V`.
*Not over-strong.* Without the factorization hypothesis nothing is claimed, and the conclusion
does not identify `W`. -/
def ITannakian : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ D : ModularData V, D.IsModularData →
    (∀ a b, D.IsIntWeight a → D.IsIntWeight b → D.S a b = D.S00 * D.d a * D.d b) →
    ∃ (𝒲 : Type u) (_ : AddCommGroup 𝒲) (_ : Module ℂ 𝒲) (W : VertexOperatorAlgebra 𝒲)
      (G : Subgroup (Aut W)), Nice W ∧ Finite G ∧ W.centralCharge = V.centralCharge ∧
      VOAIsomorphic V (orbifoldVOA G) ∧
      ∀ n : ℕ, (finrank ℂ (W.grading n) : ℝ) =
        ∑ a ∈ D.intLabels, D.d a * (finrank ℂ ((D.module a).weight (n : ℂ)) : ℝ)

/-- **I-DongMason.** A nice VOA of central charge `1` with `W₁ ≠ 0` is isomorphic to some
`V_{2m}`.

*Source.* C. Dong and G. Mason, *Rational vertex operator algebras and the effective central
charge*, IMRN 2004: Thm 1 (`W₁` is reductive), Thm 3 (rank `l ≤ c̃`, and `l = c̃` iff `W ≅ V_L`
for a positive-definite even lattice `L` of rank `l`). For pseudo-unitary `W`, `h_min = 0`, so
`c̃ = c = 1`; a nonzero reductive Lie algebra has rank `≥ 1`, hence `l = 1`; the rank-one even
lattices are `√(2m) ℤ`. The last two steps are elementary and are folded into this input.

*Not vacuous / not over-strong.* Applies only to nice `c = 1` VOAs with a weight-one vector; it
says nothing about VOAs with `W₁ = 0` (all exceptional orbifolds have `V₁ = 0`). -/
def IDongMason : Prop :=
  ∀ (𝒲 : Type u) [AddCommGroup 𝒲] [Module ℂ 𝒲] (W : VertexOperatorAlgebra 𝒲), Nice W →
    W.centralCharge = 1 → finrank ℂ (W.grading 1) ≠ 0 →
      ∃ (m : ℕ) (hm : 1 ≤ m), VOAIsomorphic W (V2m m hm)

/-- **I-Enumeration.** For every finite `G ≤ Aut(V_{2m})`, `V_{2m}^G` is in the list of
Theorem 3.1.

*Source.* GR Proposition C.4 (with Example 3.26 of GR ref [12]): `Aut(V₂) ≅ PSL₂(ℂ)` with finite
subgroups cyclic, dihedral, `A₄`, `S₄`, `A₅` (Klein); `Aut(V_{2m}) ≅ ℂ^× ⋊ ℤ₂` for `m ≥ 2`
(Dong–Nagatomo 1999); `V_{2m}^{ℤ_n} ≅ V_{2mn²}`, `V_{2m}^{D_{2n}} ≅ V_{2mn²}⁺` (DVVV 1989,
Dong–Nagatomo). **Flag:** a GR proposition assembling these published facts.

*Not vacuous / not over-strong.* Concerns only orbifolds of rank-one lattice VOAs; it is the
"easy direction" bookkeeping and gives nothing about a general `c = 1` VOA. -/
def IEnumeration : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m) (G : Subgroup (Aut (V2m m hm))), Finite G →
    InCOneList (orbifoldVOA G)

end VOA.Classification.COne
