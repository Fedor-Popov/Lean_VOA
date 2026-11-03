/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeExp
import VOA.Examples.LatticeA1
import VOA.Examples.HeisenbergNVertex
import VOA.Foundations.Locality
import VOA.Core.Dong

/-!
# The genuine lattice vertex operator `Y(eᵅ, z)` for `𝒱(A₁)`  (Gannon §5.2.2; FLM Ch. 8)

The **real** boson-dressed lattice vertex operator, built on the `k = 2` half-current core
`Examples.LatticeExp` (the genuine `cSchur`/`aExp` exponentials, the operator contraction
`alpha_comp_EminusOp`).  This **supersedes the `z⁰`-only placeholder `LatticeVOA.Yeα`** of
`Examples.LatticeA1` (whose `EminusOp := fun t => if t = 0 then id else 0` carried no higher
modes): here `Y(eᵅ,z)` carries the genuine creation series `cSchur N ⊗ eᵅ` at every `zᴺ`.

## What this file proves (all `sorry`-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **§1 — the half-current exponential fields.**  `Eminus`/`Eplus : FormalDist (End B)` — the
  genuine `E⁻(α,z) = ∑_{N≥0} (·cSchur N) zᴺ` and `E⁺(α,z) = ∑_{N≥0} aExp_N z⁻ᴺ`, with their
  vacuum actions (`Eminus_vacuum`, `Eplus_vacuum`) and the field property (`Eminus_isField`
  trivially; `Eplus_isField` via the boson weight grading — the annihilation exponential lowers
  the weight by its `z`-degree, so it is nilpotent on every fixed Fock state).
* **§2 — the field-level OPE contraction.**  `alpha_comp_Eminus_pos` (`αₘ∘E⁻_t = E⁻_t∘αₘ +
  2·E⁻_{t-m}` for the annihilation modes `m ≥ 1`, the `⟨α,α⟩ = 2` contraction) and
  `alpha_comp_Eminus_neg` (the creation modes commute), lifting `LatExp.alpha_comp_EminusOp`
  from the single mode to the field level.
* **§3 — `IsField E⁺`** via `aExp_mem_gradingZN` (the annihilation exponential drops the boson
  weight by exactly its index) and the internal weight decomposition.
* **§4 — the boson dressing** `EE(z) = :E⁻(α,z)E⁺(α,z): = E⁻(α,z)E⁺(α,z)` (`nprod`, since `E⁻`
  is purely creation), with `EE_vacuum` (`E⁺` fixes `|0⟩`, so `EE(z)|0⟩ = E⁻(α,z)|0⟩`).
* **§5 — the genuine lattice vertex operator** `Yeα : ℤ → End LatModule`,
  `Y(eᵅ,z)(p ⊗ e^{nα}) = (EE_{t-2n} p) ⊗ e^{(n+1)α}` (the `z^{α₀} = z^{2n}` sector shift, the
  shift `e^{α}`, and the boson dressing), built from linear combinators (linearity automatic),
  with its defining action `Yeα_tmul`.
* **§6 — genuine creation (VA3 on the generator):** `Yeα_vacuum` (`Y(eᵅ,z)Ω = ∑_N cSchur N ⊗ eᵅ
  zᴺ`, the real Schur series), `Yeα_creation_z0`/`Yeα_mode_neg_one_vacuum` ((eᵅ)₍₋₁₎Ω = eᵅ), and
  `Yeα_creation_nonneg` (the non-negative modes annihilate `Ω`).
* **§7 — the field-level boson OPE** `alphaField_comm_Eminus`: `[α(z₁), E⁻(α,z₂)]` has
  coefficient `2·E⁻_{t+j+1}` on the annihilation modes (`j ≤ -2`) and `0` else — the genuine OPE
  bridge `alpha_comp_EminusOp → field locality`.

* **§8 — the FLM exponential contraction** `Eminus_contraction` / `Eplus_comp_Eminus`:
  `E⁺(α,z₁)E⁻(α,z₂) = (1-z₂/z₁)²·E⁻(α,z₂)E⁺(α,z₁)` at the level of mode coefficients (the
  `(1-z₂/z₁)² = 1 - 2(z₂/z₁) + (z₂/z₁)²` three-term shift, `⟨α,α⟩ = 2`) — the OPE-reordering core
  that the operator-level mutual locality re-sums.  Proved `pbw`-free / axiom-clean by induction on
  the `E⁺`-level (Newton recursion of `aExp`, the single-current contraction `alpha_comp_Eminus_pos`,
  and a second-difference telescope of the residual terms).

## Toward the full `VertexOperatorAlgebra (LatModule)` instance

The OPE core is proved here (§8, the `(1-z₂/z₁)²` exponential contraction).  Building on it:
the field-level reordering as a `FormalDist₂` with the `ι_z` Jacobian; the full
`[Yeα(z₁),Yeα(z₂)]` commutator (the `EE` sector-shifts `z^{α₀}=z^{2n}` + the cocycle); the
diagonal `(z₁-z₂)²`-annihilation `Local Yeα Yeα` (the negative-pairing `ι_z` expansion of
`Foundations.IotaZExpansion`); the boson-dressed all-states `Y` on the free basis `B ⊗ ℂ{ℤ}`; the
conformal vector (the rank-1 Heisenberg Sugawara `ω`, `c = 1 = rank A₁`); and the
VA1–VA5 + VOA1–VOA4 cascade.  The genuine vertex operator, its creation/OPE core, and the
exponential contraction are proved here; the locality and instance assembly build on §5–§8
(`Examples.LatticeA1VOA`).

## References
* Gannon §5.2.2; FLM Ch. 8 (the vertex operator `Y(eᵅ,z)`); Kac §5.4–5.5; Lepowsky–Li Ch. 6.

## Status
The genuine boson-dressed lattice vertex operator `Y(eᵅ,z)` (real higher
modes, real Schur creation series), the half-current fields with `IsField`, the field-level OPE
contraction, the boson current OPE, and the **FLM exponential contraction** `E⁺E⁻` (§8, the
`(1-z₂/z₁)²` OPE core) are all proved `sorry`-free / axiom-clean (`pbw`-free), replacing the
`z⁰`-only placeholder of `Examples.LatticeA1`.  Mutual locality `Local Yeα Yeα` and the full
`VertexOperatorAlgebra` instance build on these.
-/

namespace VOA
namespace LatExp

open scoped BigOperators TensorProduct
open Module (End)
open HeisenbergN (FockN oscN vacuumN)
open LatticeVOA (LatModule LatGrp eVec latState latVacuum)

/-! ## §1  The genuine half-current exponential fields `E⁻(α,z)`, `E⁺(α,z)` -/

/-- The genuine **creation half** `E⁻(α,z) = exp(∑_{n≥1} α₋ₙ/n zⁿ) = ∑_{N≥0} E⁻_N zᴺ`, as a
`FormalDist (End B)`: the `zᵗ` coefficient is `E⁻_t = mulLeft (cSchur t)` for `t ≥ 0`, and `0`
for `t < 0` (only nonnegative powers of `z`). -/
noncomputable def Eminus : FormalDist (End ℂ B) :=
  fun t => if 0 ≤ t then EminusOp t.toNat else 0

@[simp] theorem Eminus_apply (t : ℤ) :
    Eminus t = if 0 ≤ t then EminusOp t.toNat else 0 := rfl

theorem Eminus_nonneg {t : ℤ} (ht : 0 ≤ t) : Eminus t = EminusOp t.toNat := by
  rw [Eminus_apply, if_pos ht]

theorem Eminus_neg {t : ℤ} (ht : t < 0) : Eminus t = 0 := by
  rw [Eminus_apply, if_neg (by omega)]

/-- `E⁻(α,z)` is a field: it is purely lower-truncated (zero for all `t < 0`). -/
theorem Eminus_isField : IsField Eminus := by
  intro x
  exact ⟨0, fun n hn => by rw [Eminus_neg hn, LinearMap.zero_apply]⟩

/-- The genuine **annihilation half** `E⁺(α,z) = exp(-∑_{n≥1} αₙ/n z⁻ⁿ) = ∑_{N≥0} E⁺_{-N} z⁻ᴺ`:
the `zᵗ` coefficient is `aExp_{-t}` for `t ≤ 0`, and `0` for `t > 0` (only nonpositive powers). -/
noncomputable def Eplus : FormalDist (End ℂ B) :=
  fun t => if t ≤ 0 then aExp (-t).toNat else 0

@[simp] theorem Eplus_apply (t : ℤ) :
    Eplus t = if t ≤ 0 then aExp (-t).toNat else 0 := rfl

theorem Eplus_nonpos {t : ℤ} (ht : t ≤ 0) : Eplus t = aExp (-t).toNat := by
  rw [Eplus_apply, if_pos ht]

theorem Eplus_pos {t : ℤ} (ht : 0 < t) : Eplus t = 0 := by
  rw [Eplus_apply, if_neg (by omega)]

/-- Vacuum action of `E⁻(α,z)`: the `zᴺ`-coefficient `E⁻_N` creates the Schur state
`cSchur N` from the vacuum (`E⁻_N |0⟩ = cSchur N`); negative powers act trivially. -/
theorem Eminus_vacuum (t : ℤ) :
    Eminus t (vacuumN 1) = if 0 ≤ t then cSchur t.toNat else 0 := by
  rw [Eminus_apply]; split_ifs with h
  · rw [EminusOp_vacuum]
  · rfl

/-- Vacuum action of `E⁺(α,z)`: the annihilation half fixes the vacuum at `z⁰` and kills it at
every strictly negative power. -/
theorem Eplus_vacuum (t : ℤ) :
    Eplus t (vacuumN 1) = if t = 0 then vacuumN 1 else 0 := by
  rw [Eplus_apply]
  by_cases h : t ≤ 0
  · rw [if_pos h, aExp_vacuum]
    by_cases h0 : t = 0
    · rw [if_pos (by omega : (-t).toNat = 0), if_pos h0]
    · rw [if_neg (by omega : ¬ (-t).toNat = 0), if_neg h0]
  · rw [if_neg h, if_neg (by omega : ¬ t = 0), LinearMap.zero_apply]

/-! ## §2  The field-level OPE contraction `[α(z₁), E⁻(α,z₂)]`

The single-mode operator contraction `alpha_comp_EminusOp` (`[αₘ, E⁻_N] = 2·E⁻_{N-m}`) lifted to
the field level.  Annihilation modes (`m ≥ 1`) contract `E⁻` with the structure constant
`⟨α,α⟩ = 2`, dropping the `z₂`-degree by `m`; creation modes (`m < 0 = X`-multiplication) commute
with `E⁻ = ·cSchur` (both are multiplications on the commutative ring `B`); the zero mode is `0`. -/

/-- **The annihilation-mode field contraction.**  For `m ≥ 1`,
`αₘ ∘ E⁻_t = E⁻_t ∘ αₘ + 2·E⁻_{t-m}` (the `z₂^t`-coefficient form of `[αₘ, E⁻(α,z₂)] =
2·z₂^m·E⁻(α,z₂)`), directly from `alpha_comp_EminusOp` by reindexing onto `ℤ`. -/
theorem alpha_comp_Eminus_pos {m : ℕ} (hm : 1 ≤ m) (t : ℤ) :
    (α (m : ℤ)).comp (Eminus t)
      = (Eminus t).comp (α (m : ℤ)) + (2 : ℂ) • Eminus (t - m) := by
  by_cases ht : 0 ≤ t
  · set N := t.toNat with hN
    have htN : (t : ℤ) = (N : ℤ) := (Int.toNat_of_nonneg ht).symm
    rw [Eminus_nonneg ht, alpha_comp_EminusOp m N hm]
    congr 1
    by_cases hmN : m ≤ N
    · rw [if_pos hmN]
      have : t - m = ((N - m : ℕ) : ℤ) := by rw [htN, Nat.cast_sub hmN]
      rw [Eminus_nonneg (by omega), this, Int.toNat_natCast]
    · rw [if_neg hmN, Eminus_neg (by omega), smul_zero]
  · rw [Eminus_neg (by omega), Eminus_neg (by omega)]
    simp

/-- **The creation-mode commutation.**  For `m < 0` the boson mode `αₘ = X^{·}` is multiplication
by a creation monomial, which commutes with `E⁻_t = ·cSchur t` (both are left-multiplications on
the commutative polynomial ring `B`): `αₘ ∘ E⁻_t = E⁻_t ∘ αₘ`. -/
theorem alpha_comp_Eminus_neg {m : ℤ} (hm : m < 0) (t : ℤ) :
    (α m).comp (Eminus t) = (Eminus t).comp (α m) := by
  refine LinearMap.ext fun q => ?_
  rw [Eminus_apply]
  split_ifs with ht
  · simp only [LinearMap.comp_apply, α, EminusOp, LinearMap.mulLeft_apply,
      HeisenbergN.oscN_apply_neg 1 2 0 hm]
    ring
  · simp

/-! ## §3  `E⁺(α,z)` is a field (the annihilation half lowers the boson weight) -/

open HeisenbergN (gradingWN gradingZN)

/-- The boson mode `αₙ` is `gradingZN`-covariant: it lowers the boson weight by `n`
(`αₙ : F_d → F_{d-n}`; `n > d` annihilates).  The `gradingZN`-input version of
`HeisenbergN.oscN_mem_gradingZN`. -/
theorem alpha_mem_gradingZN (n : ℤ) {d : ℤ} {p : B} (hp : p ∈ gradingZN 1 d) :
    α n p ∈ gradingZN 1 (d - n) := by
  by_cases hd : 0 ≤ d
  · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
    have h := HeisenbergN.oscN_mem_gradingZN 1 2 0 n hp
    rwa [Int.toNat_of_nonneg hd] at h
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, map_zero]
    exact HeisenbergN.zero_mem_gradingZN 1 _

/-- The annihilation exponential `E⁺_{-N} = aExp N` lowers the boson weight by exactly `N`:
`aExp N : F_w → F_{w-N}` (and `aExp N` annihilates everything of weight `< N`). -/
theorem aExp_mem_gradingZN (N : ℕ) {w : ℕ} {p : B} (hp : p ∈ gradingWN 1 w) :
    aExp N p ∈ gradingZN 1 ((w : ℤ) - N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [aExp_zero, LinearMap.id_apply, Nat.cast_zero, sub_zero]
           exact HeisenbergN.mem_gradingZN_of_gradingWN hp
    | (M+1) =>
      rw [aExp_succ, LinearMap.smul_apply, LinearMap.sum_apply]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_)
      simp only [Finset.mem_range] at hm
      rw [LinearMap.comp_apply, LinearMap.neg_apply]
      refine Submodule.neg_mem _ ?_
      have hrec : aExp (M - m) p ∈ gradingZN 1 ((w : ℤ) - (M - m : ℕ)) := ih (M - m) (by omega)
      have h := alpha_mem_gradingZN ((m : ℤ) + 1) hrec
      have hgoal : (w : ℤ) - (M - m : ℕ) - ((m : ℤ) + 1) = (w : ℤ) - ((M + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega : m ≤ M)]; push_cast; ring
      rwa [hgoal] at h

/-- `E⁺(α,z)` is a field: on every fixed Fock state `x` (a finite-weight polynomial) the
annihilation modes `aExp N` annihilate once `N` exceeds the top weight of `x`. -/
theorem Eplus_isField : IsField Eplus := by
  classical
  intro x
  obtain ⟨c, rfl⟩ := (HeisenbergN.gradingWN_isInternal 1).2 x
  obtain ⟨W, hW⟩ := Finset.exists_le c.support
  refine ⟨-(W : ℤ), fun n hn => ?_⟩
  have hn0 : n ≤ 0 := by omega
  rw [Eplus_nonpos hn0, DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun w hw => ?_
  have hwW : (w : ℤ) ≤ (W : ℤ) := by exact_mod_cast hW w hw
  have hmem := aExp_mem_gradingZN (-n).toNat (c w).2
  rw [HeisenbergN.gradingZN_of_neg (by omega : (w : ℤ) - ((-n).toNat : ℤ) < 0),
    Submodule.mem_bot] at hmem
  exact hmem

/-! ## §4  The boson dressing `EE(z) = E⁻(α,z)·E⁺(α,z)` (the normal-ordered exponential)

The full boson factor of the lattice vertex operator is the (same-variable) product
`E⁻(α,z)·E⁺(α,z)`.  Since `E⁻` is purely creation (nonnegative powers, index `≥ 0`) and `E⁺` is
purely annihilation, the Dong normal-ordered product `nprod E⁻ E⁺` *is* the genuine operator
product `E⁻(α,z)E⁺(α,z)` (the `m < 0` reordering branch is vacuous, `E⁻_m = 0`). -/

/-- The boson dressing `EE(z) = :E⁻(α,z)E⁺(α,z): = E⁻(α,z)E⁺(α,z)` as a `FormalDist (End B)`. -/
noncomputable def EE : FormalDist (End ℂ B) := nprod Eminus_isField Eplus_isField

theorem EE_isField : IsField EE := IsField.nprod Eminus_isField Eplus_isField

/-- The vacuum action of the boson dressing: `E⁺(α,z)` fixes `|0⟩` (its `z⁰`-mode is `id`), so
`EE(z)|0⟩ = E⁻(α,z)|0⟩`; the `zᴺ`-coefficient creates the Schur state `cSchur N`. -/
theorem EE_vacuum (t : ℤ) : EE t (vacuumN 1) = if 0 ≤ t then cSchur t.toNat else 0 := by
  classical
  have hsupp : ∀ m : ℤ, m ≠ t →
      normalOrdered Eminus Eplus m (t - m) (vacuumN 1) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, Module.End.mul_apply, Eplus_vacuum, if_neg (by omega), map_zero]
    · rw [if_neg h0, Module.End.mul_apply, Eminus_neg (by omega), LinearMap.zero_apply, map_zero]
  rw [EE, nprod_apply, finsum_eq_single _ t hsupp, normalOrdered_apply]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, if_pos ht, Module.End.mul_apply, show t - t = (0 : ℤ) from by ring,
      Eplus_vacuum, if_pos rfl, Eminus_vacuum, if_pos ht]
  · rw [if_neg ht, if_neg ht, Module.End.mul_apply, Eminus_vacuum, if_neg ht, map_zero]

/-! ## §5  The genuine lattice vertex operator `Y(eᵅ, z)` on `LatModule = B ⊗ ℂ{ℤ}`

`Y(eᵅ, z) = E⁻(α,z) E⁺(α,z) e^{α} z^{α₀}` (the FLM lattice vertex operator), acting on a basis
state `p ⊗ e^{nα}`: the `z^{α₀}` factor multiplies by `z^{⟨α,nα⟩} = z^{2n}` (an index shift by
`2n` on the boson dressing `EE`), `e^{α}` shifts the lattice point `n ↦ n+1` (cocycle `ε(1,n)=1`),
and `EE = E⁻E⁺` dresses the boson factor:
`Y(eᵅ,z)(p ⊗ e^{nα}) = (EE(z)·z^{2n} p) ⊗ e^{(n+1)α}`, i.e. the `zᵗ`-coefficient is
`(EE_{t-2n} p) ⊗ e^{(n+1)α}`.  Unlike the `z⁰`-only stub `LatticeVOA.Yeα`, this carries the
genuine higher modes through `EE = nprod E⁻ E⁺`. -/

/-- The per-sector family `n ↦ (c ↦ c · (EE_{t-2n} · ⊗ e^{(n+1)α}))` building the lattice VO. -/
noncomputable def YeαFam (t : ℤ) (n : ℤ) : ℂ →ₗ[ℂ] (B →ₗ[ℂ] LatModule) :=
  LinearMap.toSpanSingleton ℂ (B →ₗ[ℂ] LatModule)
    (((TensorProduct.mk ℂ B LatGrp).flip (eVec (n + 1))).comp (EE (t - 2 * n)))

/-- The genuine **lattice vertex operator** `Y(eᵅ,z)` as a `FormalDist (End LatModule)`, built
from real combinators (so ℂ-linearity is automatic): the `zᵗ`-coefficient sends the basis state
`p ⊗ e^{nα}` to `(EE_{t-2n} p) ⊗ e^{(n+1)α}`. -/
noncomputable def Yeα (t : ℤ) : LatModule →ₗ[ℂ] LatModule :=
  TensorProduct.lift (Finsupp.lsum ℂ (YeαFam t)).flip

/-- The defining action of `Y(eᵅ,z)` on a basis state `p ⊗ e^{nα}`. -/
theorem Yeα_tmul (t n : ℤ) (p : B) :
    Yeα t (p ⊗ₜ[ℂ] eVec n) = (EE (t - 2 * n) p) ⊗ₜ[ℂ] eVec (n + 1) := by
  rw [Yeα, TensorProduct.lift.tmul]
  change (Finsupp.lsum ℂ (YeαFam t)) (eVec n) p = _
  rw [eVec, Finsupp.lsum_single, YeαFam, LinearMap.toSpanSingleton_apply, one_smul,
    LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]

/-! ## §6  Genuine creation (VA3 on the lattice generator)

`Y(eᵅ,z)Ω = E⁻(α,z)(1⊗eᵅ)` — the genuine Schur creation series `cSchur N ⊗ eᵅ` at `zᴺ`
(the boson part of the state, dressed onto the lattice point `eᵅ`).  Unlike the `z⁰`-only stub,
this records all higher creation modes.  The lowest mode is `(eᵅ)₍₋₁₎Ω = eᵅ`, and the
non-negative creation modes annihilate the vacuum. -/

/-- The genuine creation series: `Y(eᵅ,z)Ω` has `zᵗ`-coefficient `cSchur t ⊗ eᵅ` for `t ≥ 0`
(and `0` for `t < 0`), via the real boson dressing `EE = E⁻E⁺` (`E⁺` fixes `Ω`). -/
theorem Yeα_vacuum (t : ℤ) :
    Yeα t latVacuum = if 0 ≤ t then (cSchur t.toNat) ⊗ₜ[ℂ] eVec 1 else 0 := by
  rw [show latVacuum = (1 : FockN 1) ⊗ₜ[ℂ] eVec 0 from rfl, Yeα_tmul,
    show (t - 2 * 0 : ℤ) = t from by ring]
  change (EE t (vacuumN 1)) ⊗ₜ[ℂ] eVec (0 + 1) = _
  rw [EE_vacuum, show (0 : ℤ) + 1 = 1 from by ring]
  split_ifs with ht
  · rfl
  · rw [TensorProduct.zero_tmul]

/-- **Creation seed** `(eᵅ)₍₋₁₎Ω = eᵅ`: the `z⁰`-coefficient is the lattice generator
`1⊗eᵅ = latState 1`.  Now via the genuine `EE` (`cSchur 0 = 1`), not the stub. -/
theorem Yeα_creation_z0 : Yeα 0 latVacuum = latState 1 := by
  rw [Yeα_vacuum, if_pos le_rfl, Int.toNat_zero, cSchur_zero]
  rfl

theorem Yeα_mode_neg_one_vacuum : mode Yeα (-1) latVacuum = latState 1 := by
  rw [mode_apply, show -(-1 : ℤ) - 1 = 0 from by ring, Yeα_creation_z0]

/-- The non-negative creation modes annihilate the vacuum: `(eᵅ)₍ₙ₎Ω = 0` for `n ≥ 0`
(`Y(eᵅ,z)Ω` has only nonnegative powers of `z`). -/
theorem Yeα_creation_nonneg {n : ℤ} (hn : 0 ≤ n) : mode Yeα n latVacuum = 0 := by
  rw [mode_apply, Yeα_vacuum, if_neg (by omega)]

/-! ## §7  The field-level boson OPE `[α(z₁), E⁻(α,z₂)] = 2·ι₁₂(1/(z₁-z₂))·E⁻(α,z₂)`

The single-mode contraction `alpha_comp_Eminus_pos`/`_neg` assembled into the genuine field
commutator of the boson current `α(z) = currentN 1 2 0` with the creation exponential `E⁻(α,z)`:
only the annihilation modes (`j ≤ -2`, i.e. `α₊`) contract, each dropping the `z₂`-degree by
its index with the structure constant `⟨α,α⟩ = 2`.  This is the genuine field-level OPE the
lattice locality proof consumes (the bridge `alpha_comp_EminusOp → field OPE`). -/

/-- The boson current `α(z) = ∑ₘ αₘ z^{-m-1} = currentN 1 2 0`. -/
noncomputable def alphaField : FormalDist (End ℂ B) := HeisenbergN.currentN 1 2 0

theorem alphaField_apply (j : ℤ) : alphaField j = α (-j - 1) := rfl

/-- **The field-level boson OPE**: `[α(z₁), E⁻(α,z₂)]` has `z₁ʲz₂ᵗ`-coefficient `2·E⁻_{t+j+1}`
for the annihilation modes `j ≤ -2` (`α₊` of index `-j-1 ≥ 1`) and `0` otherwise.  Equivalently
`[α(z₁), E⁻(α,z₂)] = 2·ι₁₂(1/(z₁-z₂))·E⁻(α,z₂)`. -/
theorem alphaField_comm_Eminus (j t : ℤ) :
    bracketDist alphaField Eminus j t
      = if j ≤ -2 then (2 : ℂ) • Eminus (t + j + 1) else 0 := by
  rw [bracketDist_apply, alphaField_apply]
  change (α (-j - 1)).comp (Eminus t) - (Eminus t).comp (α (-j - 1)) = _
  by_cases hj : j ≤ -2
  · rw [if_pos hj]
    have hmval : ((-j - 1).toNat : ℤ) = -j - 1 := Int.toNat_of_nonneg (by omega)
    have hm1 : 1 ≤ (-j - 1).toNat := by omega
    have hc := alpha_comp_Eminus_pos hm1 t
    rw [show (-j - 1 : ℤ) = (((-j - 1).toNat : ℤ)) from hmval.symm, hc,
      show t - ((-j - 1).toNat : ℤ) = t + j + 1 from by rw [hmval]; ring]
    abel
  · rw [if_neg hj]
    rcases (show -j - 1 < 0 ∨ -j - 1 = 0 from by omega) with hlt | heq
    · rw [alpha_comp_Eminus_neg hlt t, sub_self]
    · rw [heq]
      change (oscN 1 2 0 0).comp (Eminus t) - (Eminus t).comp (oscN 1 2 0 0) = 0
      rw [HeisenbergN.oscN_zero, LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]

/-! ## §8  The FLM exponential contraction `E⁺(α,z₁)E⁻(α,z₂) = (1-z₂/z₁)²·E⁻(α,z₂)E⁺(α,z₁)`

The genuine OPE-reordering core of the lattice construction (FLM Ch. 8), at the level of mode
coefficients.  Since `⟨α,α⟩ = 2`, the contraction factor is `(1-z₂/z₁)² = 1 - 2(z₂/z₁) + (z₂/z₁)²`
— a three-term shift, giving the closed identity `Eminus_contraction`.  This is the input the
operator-level mutual locality `Local Yeα Yeα` re-sums (the diagonal `(z₁-z₂)²`-contraction).

Proved here `pbw`-free / axiom-clean (`[propext, Classical.choice, Quot.sound]`) by strong
induction on the `E⁺`-level via the Newton recursion of `aExp`, the single-current contraction
`alpha_comp_Eminus_pos`, and a second-difference telescope of the residual contraction terms. -/

/-- ℤ-extension of `aExp` (the `E⁺` mode coefficient), zero on negative indices. -/
noncomputable def aExpZ (N : ℤ) : Module.End ℂ B := if 0 ≤ N then aExp N.toNat else 0

theorem aExpZ_neg {N : ℤ} (h : N < 0) : aExpZ N = 0 := by rw [aExpZ, if_neg (by omega)]

theorem aExpZ_nonneg {N : ℤ} (h : 0 ≤ N) : aExpZ N = aExp N.toNat := by rw [aExpZ, if_pos h]

theorem aExpZ_zero : aExpZ 0 = LinearMap.id := by rw [aExpZ_nonneg le_rfl]; simp [aExp_zero]

/-- `E⁺` coefficient as the ℤ-extended `aExp`: `Eplus a = aExpZ (-a)`. -/
theorem Eplus_eq_aExpZ (a : ℤ) : Eplus a = aExpZ (-a) := by
  rw [Eplus_apply, aExpZ]
  by_cases h : a ≤ 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- The `aExp` Newton recursion, ℤ-extended: for `N ≥ 1`,
`aExpZ N = N⁻¹ ∑_{m<N} (-α_{m+1}) ∘ aExpZ(N-1-m)`. -/
theorem aExpZ_recursion (N : ℤ) (hN : 1 ≤ N) :
    aExpZ N = (N : ℂ)⁻¹ • ∑ m ∈ Finset.range N.toNat,
      (-(α ((m : ℤ) + 1))).comp (aExpZ (N - 1 - m)) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, N.toNat = K + 1 := ⟨N.toNat - 1, by omega⟩
  have hNK : N = (K : ℤ) + 1 := by omega
  rw [aExpZ_nonneg (by omega), hK, aExp_succ, hNK]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  congr 2
  rw [aExpZ_nonneg (by omega)]
  congr 1
  omega

/-- Reassembly (all `L : ℤ`): for any range `K ≥ L.toNat`, the Newton sum equals `L • aExpZ L`. -/
theorem aExpZ_sum_reassembly (L : ℤ) (K : ℕ) (hK : L.toNat ≤ K) :
    ∑ m ∈ Finset.range K, (-(α ((m : ℤ) + 1))).comp (aExpZ (L - 1 - m))
      = (L : ℂ) • aExpZ L := by
  by_cases hL : 1 ≤ L
  · have hsplit : ∑ m ∈ Finset.range K, (-(α ((m : ℤ) + 1))).comp (aExpZ (L - 1 - m))
        = ∑ m ∈ Finset.range L.toNat, (-(α ((m : ℤ) + 1))).comp (aExpZ (L - 1 - m)) := by
      refine (Finset.sum_subset (s₁ := Finset.range L.toNat) (s₂ := Finset.range K)
        (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
      intro m _ hm
      simp only [Finset.mem_range, not_lt] at hm
      rw [aExpZ_neg (by omega), LinearMap.comp_zero]
    rw [hsplit, aExpZ_recursion L hL, smul_smul, mul_inv_cancel₀ (by
      simp only [ne_eq]; exact_mod_cast (by omega : (L : ℤ) ≠ 0)), one_smul]
  · have hsum0 : ∑ m ∈ Finset.range K, (-(α ((m : ℤ) + 1))).comp (aExpZ (L - 1 - m)) = 0 := by
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [aExpZ_neg (by omega), LinearMap.comp_zero]
    rw [hsum0]
    rcases lt_or_eq_of_le (by omega : L ≤ 0) with hlt | heq
    · rw [aExpZ_neg hlt, smul_zero]
    · subst heq; simp

/-- Single-mode contraction in the `(m:ℤ)+1` index form (for the Newton-sum index). -/
theorem alpha_succ_comp_Eminus (m : ℕ) (c : ℤ) :
    (α ((m : ℤ) + 1)).comp (Eminus c)
      = (Eminus c).comp (α ((m : ℤ) + 1)) + (2 : ℂ) • Eminus (c - ((m : ℤ) + 1)) := by
  have h := alpha_comp_Eminus_pos (m := m + 1) (by omega) c
  rwa [show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 from by push_cast; ring] at h

/-- Second-difference telescoping over a `ℂ`-module:
`∑_{m<K} (f m - 2•f(m+1) + f(m+2)) = f 0 - f 1 - f K + f(K+1)`. -/
theorem sdiff_telescope {M : Type*} [AddCommGroup M] [Module ℂ M] (f : ℕ → M) (K : ℕ) :
    ∑ m ∈ Finset.range K, (f m - (2 : ℂ) • f (m + 1) + f (m + 2))
      = f 0 - f 1 - f K + f (K + 1) := by
  have hrw : ∀ m, f m - (2 : ℂ) • f (m + 1) + f (m + 2)
      = (f m - f (m + 1)) - (f (m + 1) - f (m + 2)) := by
    intro m; rw [two_smul]; abel
  simp_rw [hrw]
  rw [Finset.sum_range_sub' (fun m => f m - f (m + 1)) K]
  abel

/-- `(∑ Fᵢ) ∘ g = ∑ (Fᵢ ∘ g)` for endomorphisms (composition = ring `*`). -/
theorem sum_comp' {ι : Type*} (s : Finset ι) (F : ι → Module.End ℂ B) (g : Module.End ℂ B) :
    (∑ i ∈ s, F i).comp g = ∑ i ∈ s, (F i).comp g := by
  simp only [← Module.End.mul_eq_comp, Finset.sum_mul]

/-- `g ∘ (∑ Fᵢ) = ∑ (g ∘ Fᵢ)` for endomorphisms. -/
theorem comp_sum' {ι : Type*} (s : Finset ι) (g : Module.End ℂ B) (F : ι → Module.End ℂ B) :
    g.comp (∑ i ∈ s, F i) = ∑ i ∈ s, g.comp (F i) := by
  simp only [← Module.End.mul_eq_comp, Finset.mul_sum]

/-- Move `-α_{m+1}` past a left `Eminus c` inside a composition (the contraction, applied form). -/
theorem move_alpha_past_Eminus (m : ℕ) (c : ℤ) (X : Module.End ℂ B) :
    (-(α ((m : ℤ) + 1))).comp ((Eminus c).comp X)
      = (Eminus c).comp ((-(α ((m : ℤ) + 1))).comp X)
        - (2 : ℂ) • ((Eminus (c - ((m : ℤ) + 1))).comp X) := by
  rw [← LinearMap.comp_assoc, LinearMap.neg_comp, alpha_succ_comp_Eminus]
  simp only [LinearMap.neg_comp, LinearMap.add_comp, LinearMap.smul_comp, LinearMap.comp_assoc,
    LinearMap.comp_neg]
  abel

/-- **The FLM `A₁` exponential contraction** (coefficient form): the `z₁`-dominant reordering of
`E⁺(α,z₁)E⁻(α,z₂)`, i.e. `aExpZ N ∘ E⁻_b = E⁻_b ∘ aExpZ N - 2 E⁻_{b-1} ∘ aExpZ(N-1)
+ E⁻_{b-2} ∘ aExpZ(N-2)`, the `(1-z₂/z₁)²` Jacobian (`⟨α,α⟩ = 2`).  Axiom-clean, `pbw`-free. -/
theorem Eminus_contraction (N b : ℤ) :
    (aExpZ N).comp (Eminus b)
      = (Eminus b).comp (aExpZ N)
        - (2 : ℂ) • ((Eminus (b - 1)).comp (aExpZ (N - 1)))
        + (Eminus (b - 2)).comp (aExpZ (N - 2)) := by
  suffices H : ∀ n : ℕ, ∀ N b : ℤ, N.toNat ≤ n →
      (aExpZ N).comp (Eminus b)
        = (Eminus b).comp (aExpZ N)
          - (2 : ℂ) • ((Eminus (b - 1)).comp (aExpZ (N - 1)))
          + (Eminus (b - 2)).comp (aExpZ (N - 2)) by
    exact H N.toNat N b le_rfl
  intro n
  induction n with
  | zero =>
    intro N b hN
    by_cases h0 : N = 0
    · subst h0
      rw [aExpZ_zero, aExpZ_neg (by norm_num : (0:ℤ) - 1 < 0),
          aExpZ_neg (by norm_num : (0:ℤ) - 2 < 0)]
      simp
    · rw [aExpZ_neg (by omega : N < 0), aExpZ_neg (by omega : N - 1 < 0),
          aExpZ_neg (by omega : N - 2 < 0)]
      simp
  | succ n ih =>
    intro N b hN
    by_cases hsmall : N.toNat ≤ n
    · exact ih N b hsmall
    · have hN1 : 1 ≤ N := by omega
      have hNn : N.toNat = n + 1 := by omega
      have hNne : (N : ℂ) ≠ 0 := by
        simp only [ne_eq, Int.cast_eq_zero]; omega
      set f : ℕ → Module.End ℂ B :=
        fun k => -(2 : ℂ) • ((Eminus (b - 1 - (k : ℤ))).comp (aExpZ (N - 1 - (k : ℤ)))) with hf
      have hfK : f N.toNat = 0 := by
        simp only [hf]
        rw [aExpZ_neg (by omega : N - 1 - (N.toNat : ℤ) < 0), LinearMap.comp_zero, smul_zero]
      have hfK1 : f (N.toNat + 1) = 0 := by
        simp only [hf]
        push_cast
        rw [aExpZ_neg (show N - 1 - ((N.toNat : ℤ) + 1) < 0 by omega),
          LinearMap.comp_zero, smul_zero]
      have hLHS : (aExpZ N).comp (Eminus b)
          = (N : ℂ)⁻¹ • ∑ m ∈ Finset.range N.toNat,
              (-(α ((m : ℤ) + 1))).comp ((aExpZ (N - 1 - m)).comp (Eminus b)) := by
        rw [aExpZ_recursion N hN1, LinearMap.smul_comp, sum_comp']
        simp only [LinearMap.comp_assoc]
      have hterm : ∀ m ∈ Finset.range N.toNat,
          (-(α ((m : ℤ) + 1))).comp ((aExpZ (N - 1 - m)).comp (Eminus b))
            = ( (Eminus b).comp ((-(α ((m : ℤ) + 1))).comp (aExpZ (N - 1 - m)))
                - (2 : ℂ) • ((Eminus (b - 1)).comp ((-(α ((m : ℤ) + 1))).comp (aExpZ (N - 1 - 1 - m))))
                + (Eminus (b - 2)).comp ((-(α ((m : ℤ) + 1))).comp (aExpZ (N - 2 - 1 - m))) )
              + (f m - (2 : ℂ) • f (m + 1) + f (m + 2)) := by
        intro m _
        rw [ih (N - 1 - m) b (by omega), LinearMap.comp_add, LinearMap.comp_sub,
          LinearMap.comp_smul, move_alpha_past_Eminus, move_alpha_past_Eminus,
          move_alpha_past_Eminus]
        simp only [hf]
        push_cast
        ring_nf
        module
      have hCol : ∀ (e : Module.End ℂ B) (L : ℤ), L.toNat ≤ N.toNat →
          (∑ m ∈ Finset.range N.toNat, e.comp ((-(α ((m : ℤ) + 1))).comp (aExpZ (L - 1 - (m : ℤ)))))
            = e.comp ((L : ℂ) • aExpZ L) := by
        intro e L hL
        rw [← comp_sum', aExpZ_sum_reassembly L N.toNat hL]
      have hGS : (∑ m ∈ Finset.range N.toNat,
            ( (Eminus b).comp ((-(α ((m : ℤ) + 1))).comp (aExpZ (N - 1 - m)))
              - (2 : ℂ) • ((Eminus (b - 1)).comp ((-(α ((m : ℤ) + 1))).comp (aExpZ (N - 1 - 1 - m))))
              + (Eminus (b - 2)).comp ((-(α ((m : ℤ) + 1))).comp (aExpZ (N - 2 - 1 - m))) ))
          = (Eminus b).comp ((N : ℂ) • aExpZ N)
            - (2 : ℂ) • ((Eminus (b - 1)).comp (((N - 1 : ℤ) : ℂ) • aExpZ (N - 1)))
            + (Eminus (b - 2)).comp (((N - 2 : ℤ) : ℂ) • aExpZ (N - 2)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
          hCol (Eminus b) N le_rfl, hCol (Eminus (b - 1)) (N - 1) (by omega),
          hCol (Eminus (b - 2)) (N - 2) (by omega)]
      rw [hLHS, inv_smul_eq_iff₀ hNne, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
        sdiff_telescope f N.toNat, hfK, hfK1, hGS]
      simp only [hf, LinearMap.comp_smul]
      push_cast
      ring_nf
      module

/-- **The FLM `A₁` exponential contraction** in `E⁺`/`E⁻` coefficient form (the directly-usable
shape for the operator-level locality): `E⁺_a ∘ E⁻_b = E⁻_b ∘ E⁺_a - 2 E⁻_{b-1} ∘ E⁺_{a+1}
+ E⁻_{b-2} ∘ E⁺_{a+2}` — the `z₁`-dominant expansion of `(1-z₂/z₂)²`, `⟨α,α⟩ = 2`. -/
theorem Eplus_comp_Eminus (a b : ℤ) :
    (Eplus a).comp (Eminus b)
      = (Eminus b).comp (Eplus a)
        - (2 : ℂ) • ((Eminus (b - 1)).comp (Eplus (a + 1)))
        + (Eminus (b - 2)).comp (Eplus (a + 2)) := by
  rw [Eplus_eq_aExpZ a, Eplus_eq_aExpZ (a + 1), Eplus_eq_aExpZ (a + 2),
    show (-(a + 1) : ℤ) = -a - 1 from by ring, show (-(a + 2) : ℤ) = -a - 2 from by ring]
  exact Eminus_contraction (-a) b

/-! ## §8′  The `E⁺` contraction companions — the `[α, E⁺]` boson OPE

The creation-mode contraction `[α₋ₖ, E⁺] = 2·E⁺_{N-k}` (the dual of `alpha_comp_EminusOp`), and
the field-level boson OPE `[α(z₁), E⁺(α,z₂)]` it assembles into — the `E⁺` companions of
`alphaField_comm_Eminus`.  These are the boson-current/annihilation-half contractions that, with
`§7`'s `[α, E⁻]`, give the Heisenberg–lattice mutual locality, and the input for the off-diagonal
`e^{-α}` dressing.  All `pbw`-free. -/

/-- **The creation-mode `E⁺` contraction** `[α₋ₖ, aExp_N] = 2·aExp_{N-k}` (the dual of
`alpha_comp_EminusOp`): the creation mode `α₋ₖ` (mult by `X`) contracts the annihilation
exponential `E⁺ = aExp`, dropping its level by `k` (structure constant `⟨α,α⟩ = 2`).  ℤ-extended in
`M`, vacuous for `k > M`.  Proved by strong induction on `M.toNat` via the `aExp` Newton recursion
(`aExpZ_recursion`), the Heisenberg commutator `[α₋ₖ, α_{m+1}] = -2k·δ_{m+1,k}` (`oscN_comm`), and
the reassembly `aExpZ_sum_reassembly`. -/
theorem alphaNeg_comp_aExpZ (k : ℕ) (hk : 1 ≤ k) :
    ∀ M : ℤ, (α (-(k : ℤ))).comp (aExpZ M)
      = (aExpZ M).comp (α (-(k : ℤ))) + (2 : ℂ) • aExpZ (M - k) := by
  have hcomm : ∀ m : ℕ, α (-(k : ℤ)) * α ((m : ℤ) + 1) - α ((m : ℤ) + 1) * α (-(k : ℤ))
      = (if (m : ℤ) + 1 = (k : ℤ) then (-((2 * k : ℕ) : ℂ)) else 0) • LinearMap.id := by
    intro m
    have h := HeisenbergN.oscN_comm 1 2 0 0 (-(k : ℤ)) ((m : ℤ) + 1)
    simp only [true_and] at h
    rw [show α (-(k : ℤ)) = HeisenbergN.oscN 1 2 0 (-(k : ℤ)) from rfl,
      show α ((m : ℤ) + 1) = HeisenbergN.oscN 1 2 0 ((m : ℤ) + 1) from rfl, h]
    by_cases hc : (m : ℤ) + 1 = (k : ℤ)
    · rw [if_pos (show -(k : ℤ) + ((m : ℤ) + 1) = 0 by omega), if_pos hc]
      congr 1; push_cast; ring
    · rw [if_neg (show ¬ (-(k : ℤ) + ((m : ℤ) + 1) = 0) by omega), if_neg hc]
  have hmove : ∀ m : ℕ, (α (-(k : ℤ))).comp (-(α ((m : ℤ) + 1)))
      = (-(α ((m : ℤ) + 1))).comp (α (-(k : ℤ)))
        + (if (m : ℤ) + 1 = (k : ℤ) then ((2 * k : ℕ) : ℂ) else 0) • LinearMap.id := by
    intro m
    have hAB : α (-(k : ℤ)) * α ((m : ℤ) + 1)
        = α ((m : ℤ) + 1) * α (-(k : ℤ))
          + (if (m : ℤ) + 1 = (k : ℤ) then (-((2 * k : ℕ) : ℂ)) else 0) • LinearMap.id :=
      sub_eq_iff_eq_add'.mp (hcomm m)
    rw [LinearMap.comp_neg, LinearMap.neg_comp,
      show (α (-(k : ℤ))).comp (α ((m : ℤ) + 1)) = α (-(k : ℤ)) * α ((m : ℤ) + 1) from rfl,
      show (α ((m : ℤ) + 1)).comp (α (-(k : ℤ))) = α ((m : ℤ) + 1) * α (-(k : ℤ)) from rfl, hAB]
    by_cases hc : (m : ℤ) + 1 = (k : ℤ)
    · rw [if_pos hc, if_pos hc]; push_cast; module
    · rw [if_neg hc, if_neg hc]; simp
  suffices H : ∀ n : ℕ, ∀ M : ℤ, M.toNat ≤ n →
      (α (-(k : ℤ))).comp (aExpZ M)
        = (aExpZ M).comp (α (-(k : ℤ))) + (2 : ℂ) • aExpZ (M - k) by
    exact fun M => H M.toNat M le_rfl
  intro n
  induction n with
  | zero =>
    intro M hM
    by_cases h0 : M = 0
    · subst h0
      rw [aExpZ_zero, LinearMap.comp_id, LinearMap.id_comp,
        aExpZ_neg (show (0 : ℤ) - k < 0 by omega), smul_zero, add_zero]
    · rw [aExpZ_neg (by omega : M < 0), aExpZ_neg (show M - k < 0 by omega),
        LinearMap.comp_zero, LinearMap.zero_comp, smul_zero, add_zero]
  | succ n ih =>
    intro M hM
    by_cases hsmall : M.toNat ≤ n
    · exact ih M hsmall
    · have hM1 : 1 ≤ M := by omega
      have hMne : (M : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      conv_lhs => rw [aExpZ_recursion M hM1]
      rw [LinearMap.comp_smul, comp_sum']
      have hterm : ∀ m ∈ Finset.range M.toNat,
          (α (-(k : ℤ))).comp ((-(α ((m : ℤ) + 1))).comp (aExpZ (M - 1 - m)))
            = (-(α ((m : ℤ) + 1))).comp ((aExpZ (M - 1 - m)).comp (α (-(k : ℤ))))
              + (2 : ℂ) • (-(α ((m : ℤ) + 1))).comp (aExpZ ((M - k) - 1 - m))
              + (if (m : ℤ) + 1 = (k : ℤ) then ((2 * k : ℕ) : ℂ) else 0) • aExpZ (M - 1 - m) := by
        intro m _
        rw [← LinearMap.comp_assoc, hmove m, LinearMap.add_comp, LinearMap.comp_assoc,
          ih (M - 1 - m) (by omega)]
        simp only [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.smul_comp,
          LinearMap.id_comp]
        rw [show M - 1 - (m : ℤ) - k = (M - k) - 1 - m from by ring]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hcol1 : (∑ m ∈ Finset.range M.toNat,
            (-(α ((m : ℤ) + 1))).comp ((aExpZ (M - 1 - m)).comp (α (-(k : ℤ)))))
          = (M : ℂ) • ((aExpZ M).comp (α (-(k : ℤ)))) := by
        simp only [← LinearMap.comp_assoc, ← sum_comp', aExpZ_sum_reassembly M M.toNat le_rfl,
          LinearMap.smul_comp]
      have hcol2 : (∑ m ∈ Finset.range M.toNat,
            (2 : ℂ) • (-(α ((m : ℤ) + 1))).comp (aExpZ ((M - k) - 1 - m)))
          = (2 : ℂ) • (((M - k : ℤ) : ℂ) • aExpZ (M - k)) := by
        rw [← Finset.smul_sum, aExpZ_sum_reassembly (M - k) M.toNat (by omega)]
      have hcol3 : (∑ m ∈ Finset.range M.toNat,
            (if (m : ℤ) + 1 = (k : ℤ) then ((2 * k : ℕ) : ℂ) else 0) • aExpZ (M - 1 - m))
          = ((2 * k : ℕ) : ℂ) • aExpZ (M - k) := by
        by_cases hkM : k ≤ M.toNat
        · rw [Finset.sum_eq_single (k - 1)]
          · rw [if_pos (by omega), show M - 1 - ((k : ℕ) - 1 : ℕ) = M - k from by
                rw [show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 from by omega]; ring]
          · intro b _ hb; rw [if_neg (by omega), zero_smul]
          · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
        · rw [aExpZ_neg (show M - k < 0 by omega), smul_zero]
          refine Finset.sum_eq_zero fun m hm => ?_
          simp only [Finset.mem_range] at hm
          rw [if_neg (by omega), zero_smul]
      rw [hcol1, hcol2, hcol3, inv_smul_eq_iff₀ hMne]
      push_cast
      module

/-! ## §9  Self-commutativity of the two halves and the honest convolution form of `EE`

The structural ingredients the operator-level mutual locality `Local Yeα Yeα` re-sums.  The
boson dressing `EE = E⁻(α,z)E⁺(α,z)` is the *honest* operator convolution (the normal-ordering
correction in `nprod` is vacuous because `E⁻` is creation-only), and each half commutes with
itself: the creation modes `E⁻_a` are left-multiplications on the commutative ring `B`, and the
annihilation modes `E⁺_a` are polynomials in the pairwise-commuting positive boson modes
`{α(j+1)}` (so `[αₘ,αₙ] = 0` for `m,n ≥ 1` lifts to `E⁺_a E⁺_b = E⁺_b E⁺_a`).  With the FLM
exponential contraction `Eplus_comp_Eminus` (§8) these are the inputs to the lattice locality. -/

/-- `EE` is the **honest convolution** `E⁻·E⁺`: `EE_s = ∑ᶠ_m E⁻_m E⁺_{s-m}` (the normal-ordering
correction in `nprod` is vacuous because `E⁻_m = 0` for `m < 0`). -/
theorem EE_apply_conv (s : ℤ) (x : B) :
    EE s x = ∑ᶠ m : ℤ, Eminus m (Eplus (s - m) x) := by
  rw [EE, nprod_apply]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, Module.End.mul_apply]
  · rw [if_neg hm, Module.End.mul_apply, Eminus_neg (show m < 0 by omega)]; simp

/-- The **creation halves commute**: `E⁻_a ∘ E⁻_b = E⁻_b ∘ E⁻_a` (both are left-multiplications
on the commutative ring `B`). -/
theorem Eminus_comm (a b : ℤ) : (Eminus a).comp (Eminus b) = (Eminus b).comp (Eminus a) := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply]
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [Eminus_nonneg ha, Eminus_nonneg hb, EminusOp, EminusOp, LinearMap.mulLeft_apply,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, mul_left_comm]
    · rw [Eminus_neg (show b < 0 by omega)]; simp
  · rw [Eminus_neg (show a < 0 by omega)]; simp

/-- Positive boson modes commute: `[αₘ, αₙ] = 0` for `m, n ≥ 1` (`m + n ≠ 0`). -/
theorem alpha_commute {m n : ℤ} (hm : 1 ≤ m) (hn : 1 ≤ n) : Commute (α m) (α n) := by
  have h := HeisenbergN.oscN_comm 1 2 0 0 m n
  rw [if_neg (by rintro ⟨_, h2⟩; omega), zero_smul] at h
  exact sub_eq_zero.mp h

/-- `E⁺`'s building block `aExp N` commutes with every positive boson mode `α(j+1)` (it is a
polynomial in the pairwise-commuting annihilation modes). -/
theorem aExp_commute_alpha (N j : ℕ) : Commute (aExp N) (α ((j : ℤ) + 1)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [aExp_zero]; exact Commute.one_left _
    | (M + 1) =>
      rw [aExp_succ]
      refine Commute.smul_left ?_ _
      refine Commute.sum_left _ _ _ (fun m hm => ?_)
      refine Commute.mul_left ?_ (ih (M - m) (by simp only [Finset.mem_range] at hm; omega))
      exact (alpha_commute (by omega) (by omega)).neg_left

/-- The **annihilation halves commute**: `aExp M ∘ aExp N = aExp N ∘ aExp M`. -/
theorem aExp_commute (M N : ℕ) : Commute (aExp M) (aExp N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [aExp_zero]; exact Commute.one_right _
    | (K + 1) =>
      rw [aExp_succ]
      refine Commute.smul_right ?_ _
      refine Commute.sum_right _ _ _ (fun m hm => ?_)
      refine Commute.mul_right ?_ (ih (K - m) (by simp only [Finset.mem_range] at hm; omega))
      exact (aExp_commute_alpha M m).neg_right

/-- The **`E⁺` halves commute**: `E⁺_a ∘ E⁺_b = E⁺_b ∘ E⁺_a`. -/
theorem Eplus_comm (a b : ℤ) : (Eplus a).comp (Eplus b) = (Eplus b).comp (Eplus a) := by
  rw [Eplus_eq_aExpZ, Eplus_eq_aExpZ]
  by_cases ha : 0 ≤ -a
  · by_cases hb : 0 ≤ -b
    · rw [aExpZ_nonneg ha, aExpZ_nonneg hb]; exact aExp_commute _ _
    · rw [aExpZ_neg (show -b < 0 by omega)]; simp
  · rw [aExpZ_neg (show -a < 0 by omega)]; simp

/-! ## §10  Reduction of the lattice mutual locality to the single FLM reordering

The operator-level mutual locality `Local Yeα Yeα` reduces — exactly, via the §9 building
blocks — to **one** reordering identity (`EEMaster`).  The route, recorded precisely:

`Y(eᵅ,z)` acts on a sector `e^{nα}` as `EE` shifted by the lattice grading `z^{α₀} = z^{2n}`
(`Yeα_tmul`: `Y(eᵅ,z)(p ⊗ e^{nα}) = (EE_{·-2n} p) ⊗ e^{(n+1)α}`).  On `p ⊗ e^{nα}` the two
orders of `Y(eᵅ,z₁)Y(eᵅ,z₂)` give the boson operators `EE_{j-2n-2}EE_{k-2n}` and
`EE_{k-2n-2}EE_{j-2n}`.  Writing the FLM reordering `EE_c EE_d = T(c,d) - 2T(c+1,d-1) +
T(c+2,d-2)` with the **symmetric** four-fold `T(C,D) = E⁻(z₁)E⁻(z₂)E⁺(z₁)E⁺(z₂)` (`Tv_symm`,
from `Eminus_comm`/`Eplus_comm`), the two orders coincide (`EE_shift_comm`): the `z^{2n}`
sector factors absorb the `z₁^{-2}`/`z₂^{-2}` asymmetry of the two reorderings into the common
`z₁^{2n}z₂^{2n}(z₁-z₂)²`.  Hence the even-lattice operators **commute exactly**
(`bracketDist = 0`, mutual locality with bound `0`) — *no `ι_z`/`negPowJump` expansion is
needed* for the `A₁` diagonal.

The single remaining algebraic crux is the reordering itself, `EEMaster` — the four-fold
re-summation of the contraction `Eplus_comp_Eminus` (§8).  It is recorded here as an explicit
named hypothesis (the project's crux-as-hypothesis discipline), *not* an axiom. -/

/-- The fully normal-ordered **symmetric four-fold operator** `T(C,D) = E⁻(z₁)E⁻(z₂)E⁺(z₁)E⁺(z₂)`,
applied to a vector (a single `finsum` over `ℤ × ℤ`). -/
noncomputable def Tv (C D : ℤ) (x : B) : B :=
  ∑ᶠ pq : ℤ × ℤ, Eminus pq.1 (Eminus pq.2 (Eplus (C - pq.1) (Eplus (D - pq.2) x)))

/-- `T` is **symmetric**, `T(C,D) = T(D,C)`: swap the summation pair (`finsum_comp_equiv` along
`Prod.swap`) and use the self-commutativity of the two halves (`Eminus_comm`/`Eplus_comm`). -/
theorem Tv_symm (C D : ℤ) (x : B) : Tv C D x = Tv D C x := by
  rw [Tv, Tv, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
    (f := fun pq : ℤ × ℤ => Eminus pq.1 (Eminus pq.2 (Eplus (D - pq.1) (Eplus (C - pq.2) x))))]
  refine finsum_congr fun pq => ?_
  obtain ⟨p, q⟩ := pq
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  have hE : ∀ Y, Eminus p (Eminus q Y) = Eminus q (Eminus p Y) := fun Y => by
    have := DFunLike.congr_fun (Eminus_comm p q) Y; simpa [LinearMap.comp_apply] using this
  have hP : ∀ x', Eplus (C - p) (Eplus (D - q) x') = Eplus (D - q) (Eplus (C - p) x') := fun x' => by
    have := DFunLike.congr_fun (Eplus_comm (C - p) (D - q)) x'
    simpa [LinearMap.comp_apply] using this
  rw [hE, hP]

/-- **The single remaining crux** (`EEMaster`): the four-fold re-summation of the FLM
contraction `Eplus_comp_Eminus` (§8) into the symmetric normal-ordered form,
`EE_c EE_d = T(c,d) - 2 T(c+1,d-1) + T(c+2,d-2)`.  Recorded as a named hypothesis, not an
axiom; discharging it closes the lattice mutual locality below. -/
def EEMaster : Prop :=
  ∀ (c d : ℤ) (x : B),
    EE c (EE d x) = Tv c d x - 2 • Tv (c + 1) (d - 1) x + Tv (c + 2) (d - 2) x

/-- The **shifted self-commutativity of `EE`** `EE_{a-2}EE_b = EE_{b-2}EE_a`, from the
reordering `EEMaster` and the symmetry `Tv_symm`.  (The encoded content: `(z₁-z₂)²EE(z₁)EE(z₂)`
is symmetric in `z₁ ↔ z₂`.) -/
theorem EE_shift_comm (hmaster : EEMaster) (a b : ℤ) (x : B) :
    EE (a - 2) (EE b x) = EE (b - 2) (EE a x) := by
  rw [hmaster (a - 2) b x, hmaster (b - 2) a x,
    show a - 2 + 1 = a - 1 from by ring, show a - 2 + 2 = a from by ring,
    show b - 2 + 1 = b - 1 from by ring, show b - 2 + 2 = b from by ring,
    Tv_symm (a - 2) b x, Tv_symm (a - 1) (b - 1) x, Tv_symm a (b - 2) x]
  abel

/-- **The pointwise mutual-locality identity** for the genuine lattice vertex operator: on every
basis state `p ⊗ e^{nα}`, `[Y(eᵅ,z₁), Y(eᵅ,z₂)]` vanishes — the even-`A₁`-lattice operators
commute *exactly*.  Reduced (via `EE_shift_comm`) to the single crux `EEMaster`; the operator
identity `bracketDist Yeα Yeα = 0`, hence `Local Yeα Yeα`, follows by routine `TensorProduct`
linearity over the spanning states `p ⊗ e^{nα}`. -/
theorem Yeα_bracket_on_state (hmaster : EEMaster) (j k n : ℤ) (p : B) :
    bracketDist Yeα Yeα j k (p ⊗ₜ[ℂ] eVec n) = 0 := by
  rw [bracketDist_apply, LinearMap.sub_apply]
  simp only [Module.End.mul_apply, Yeα_tmul]
  rw [show j - 2 * (n + 1) = j - 2 * n - 2 from by ring,
    show k - 2 * (n + 1) = k - 2 * n - 2 from by ring,
    EE_shift_comm hmaster (j - 2 * n) (k - 2 * n) p, sub_self]

/-! ## §11  The discharge of `EEMaster` — the four-fold FLM reordering (`ι_z`-free)

`EE c (EE d x)` re-summed into the symmetric normal-ordered `T(C,D)` via the contraction
`Eplus_comp_Eminus`.  The bookkeeping is genuine (`finsum_curry` for the nested↔product bridge,
`finsum_int_succ_shift`/`Equiv.addRight` for the `q`-reindex, finite-support side conditions
throughout), but the algebra is *exact* — no `ι_z` expansion enters (the even-`A₁` diagonal). -/

/-- `E⁺(·)y` has finite support. -/
theorem Eplus_support_finite (y : B) :
    (Function.support (fun t : ℤ => Eplus t y)).Finite := by
  obtain ⟨B0, hB0⟩ := Eplus_isField y
  apply Set.Finite.subset (Set.finite_Icc B0 0)
  intro t ht
  rw [Function.mem_support] at ht
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    exact ht (hB0 t (by omega))
  · by_contra h
    exact ht (by rw [Eplus_pos (show 0 < t by omega)]; rfl)

/-- For fixed `b`, `q ↦ E⁺_{b-q} y` has finite support. -/
theorem Eplus_shift_support_finite (b : ℤ) (y : B) :
    (Function.support (fun q : ℤ => Eplus (b - q) y)).Finite := by
  obtain ⟨B0, hB0⟩ := Eplus_isField y
  apply Set.Finite.subset (Set.finite_Icc b (b - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    exact hq (by rw [Eplus_pos (show 0 < b - q by omega)]; rfl)
  · by_contra h
    exact hq (hB0 (b - q) (by omega))

/-- The doubly-shifted `E⁺E⁺` operator on `x` has finite joint support in `(p,q)`. -/
theorem EplusEplus_support_finite (a b : ℤ) (x : B) :
    (Function.support
      (fun pq : ℤ × ℤ => Eplus (a - pq.1) (Eplus (b - pq.2) x))).Finite := by
  set Sq := Function.support (fun q : ℤ => Eplus (b - q) x) with hSq
  have hSqfin : Sq.Finite := Eplus_shift_support_finite b x
  set P := ⋃ q ∈ Sq, Function.support (fun p : ℤ => Eplus (a - p) (Eplus (b - q) x)) with hP
  have hPfin : P.Finite := hSqfin.biUnion (fun q _ => Eplus_shift_support_finite a (Eplus (b - q) x))
  apply Set.Finite.subset (hPfin.prod hSqfin)
  intro pq hpq
  rw [Function.mem_support] at hpq
  have hq : pq.2 ∈ Sq := by
    rw [hSq, Function.mem_support]; intro h; exact hpq (by rw [h, map_zero])
  refine Set.mem_prod.mpr ⟨?_, hq⟩
  rw [hP]; exact Set.mem_biUnion hq (Function.mem_support.mpr hpq)

/-- The full four-fold integrand has finite joint support in `(p,q)`. -/
theorem fourfold_support_finite (a b : ℤ) (x : B) :
    (Function.support
      (fun pq : ℤ × ℤ => Eminus pq.1 (Eminus pq.2 (Eplus (a - pq.1) (Eplus (b - pq.2) x))))).Finite := by
  apply Set.Finite.subset (EplusEplus_support_finite a b x)
  intro pq hpq
  rw [Function.mem_support] at hpq ⊢
  intro h; exact hpq (by rw [h, map_zero, map_zero])

/-- Bridge: `Tv` (product `finsum`) equals the `q`-outer nested form. -/
theorem Tv_eq_nestQ (C D : ℤ) (x : B) :
    Tv C D x = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      Eminus p (Eminus q (Eplus (C - p) (Eplus (D - q) x))) := by
  rw [Tv, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
      (f := fun pq : ℤ × ℤ => Eminus pq.1 (Eminus pq.2 (Eplus (C - pq.1) (Eplus (D - pq.2) x))))]
  rw [finsum_curry _ ((fourfold_support_finite C D x).preimage
      ((Equiv.prodComm ℤ ℤ).injective.injOn))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]

/-- The `EE`-defining marginal `q ↦ E⁻_q E⁺_{s-q} x` has finite support. -/
theorem EE_marg_support_finite (s : ℤ) (x : B) :
    (Function.support (fun q : ℤ => Eminus q (Eplus (s - q) x))).Finite := by
  apply Set.Finite.subset (Eplus_shift_support_finite s x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h; exact hq (by rw [h, map_zero])

/-- LHS expansion of `EE c (EE d x)` into the `q`-outer, `p`-inner double `finsum`. -/
theorem EE_nest (c d : ℤ) (x : B) :
    EE c (EE d x) = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      Eminus p (Eplus (c - p) (Eminus q (Eplus (d - q) x))) := by
  rw [EE_apply_conv d x, map_finsum (EE c) (EE_marg_support_finite d x)]
  refine finsum_congr fun q => ?_
  rw [EE_apply_conv c]

/-- The pointwise reordering of the inner integrand via `Eplus_comp_Eminus`. -/
theorem inner_reorder (c d p q : ℤ) (x : B) :
    Eminus p (Eplus (c - p) (Eminus q (Eplus (d - q) x)))
      = Eminus p (Eminus q (Eplus (c - p) (Eplus (d - q) x)))
        - (2 : ℂ) • Eminus p (Eminus (q - 1) (Eplus (c - p + 1) (Eplus (d - q) x)))
        + Eminus p (Eminus (q - 2) (Eplus (c - p + 2) (Eplus (d - q) x))) := by
  have h := DFunLike.congr_fun (Eplus_comp_Eminus (c - p) q) (Eplus (d - q) x)
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.comp_apply] at h
  rw [h, map_add, map_sub, map_smul]

/-- term B sum, reindexed `q ↦ q+1`. -/
theorem termB (c d : ℤ) (x : B) :
    (∑ᶠ q : ℤ, ∑ᶠ p : ℤ, Eminus p (Eminus (q - 1) (Eplus (c - p + 1) (Eplus (d - q) x))))
      = Tv (c + 1) (d - 1) x := by
  rw [Tv_eq_nestQ,
    ← finsum_int_succ_shift (fun q : ℤ =>
      ∑ᶠ p : ℤ, Eminus p (Eminus (q - 1) (Eplus (c - p + 1) (Eplus (d - q) x))))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  rw [show q + 1 - 1 = q from by ring, show d - (q + 1) = d - 1 - q from by ring,
    show c - p + 1 = c + 1 - p from by ring]

/-- term C sum, reindexed `q ↦ q+2`. -/
theorem termC (c d : ℤ) (x : B) :
    (∑ᶠ q : ℤ, ∑ᶠ p : ℤ, Eminus p (Eminus (q - 2) (Eplus (c - p + 2) (Eplus (d - q) x))))
      = Tv (c + 2) (d - 2) x := by
  rw [Tv_eq_nestQ,
    ← finsum_comp_equiv (Equiv.addRight (2 : ℤ))
      (f := fun q : ℤ =>
        ∑ᶠ p : ℤ, Eminus p (Eminus (q - 2) (Eplus (c - p + 2) (Eplus (d - q) x))))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.coe_addRight]
  rw [show q + 2 - 2 = q from by ring, show d - (q + 2) = d - 2 - q from by ring,
    show c - p + 2 = c + 2 - p from by ring]

/-- Split a single `finsum` of `u - 2•v + w` (all finite support). -/
theorem finsum_split3 (u v w : ℤ → B)
    (hu : (Function.support u).Finite) (hv : (Function.support v).Finite)
    (hw : (Function.support w).Finite) :
    (∑ᶠ i, (u i - (2 : ℂ) • v i + w i))
      = (∑ᶠ i, u i) - (2 : ℂ) • (∑ᶠ i, v i) + (∑ᶠ i, w i) := by
  have hv2 : (Function.support (fun i => (2 : ℂ) • v i)).Finite :=
    hv.subset (Function.support_smul_subset_right (fun _ => (2 : ℂ)) v)
  have huv : (Function.support (fun i => u i - (2 : ℂ) • v i)).Finite :=
    (hu.union hv2).subset (Function.support_sub u (fun i => (2 : ℂ) • v i))
  rw [finsum_add_distrib huv hw, finsum_sub_distrib hu hv2, ← smul_finsum' (2 : ℂ) hv]

/-- **`EEMaster` is a theorem** (B1): the four-fold re-summation of the FLM contraction. -/
theorem eeMaster : EEMaster := by
  intro c d x
  have pA : ∀ q : ℤ, (Function.support
      (fun p => Eminus p (Eminus q (Eplus (c - p) (Eplus (d - q) x))))).Finite := fun q => by
    apply Set.Finite.subset (Eplus_shift_support_finite c (Eplus (d - q) x))
    intro p hp; rw [Function.mem_support] at hp ⊢
    intro h; exact hp (by rw [h, map_zero, map_zero])
  have pB : ∀ q : ℤ, (Function.support
      (fun p => Eminus p (Eminus (q - 1) (Eplus (c - p + 1) (Eplus (d - q) x))))).Finite := fun q => by
    apply Set.Finite.subset (Eplus_shift_support_finite (c + 1) (Eplus (d - q) x))
    intro p hp; rw [Function.mem_support] at hp ⊢
    intro h; exact hp (by rw [show c - p + 1 = c + 1 - p from by ring, h, map_zero, map_zero])
  have pC : ∀ q : ℤ, (Function.support
      (fun p => Eminus p (Eminus (q - 2) (Eplus (c - p + 2) (Eplus (d - q) x))))).Finite := fun q => by
    apply Set.Finite.subset (Eplus_shift_support_finite (c + 2) (Eplus (d - q) x))
    intro p hp; rw [Function.mem_support] at hp ⊢
    intro h; exact hp (by rw [show c - p + 2 = c + 2 - p from by ring, h, map_zero, map_zero])
  have qSA : (Function.support
      (fun q => ∑ᶠ p, Eminus p (Eminus q (Eplus (c - p) (Eplus (d - q) x))))).Finite := by
    apply Set.Finite.subset (Eplus_shift_support_finite d x)
    intro q hq; rw [Function.mem_support] at hq ⊢
    exact fun h => hq (finsum_eq_zero_of_forall_eq_zero fun p => by
      rw [h, map_zero, map_zero, map_zero])
  have qSB : (Function.support
      (fun q => ∑ᶠ p, Eminus p (Eminus (q - 1) (Eplus (c - p + 1) (Eplus (d - q) x))))).Finite := by
    apply Set.Finite.subset (Eplus_shift_support_finite d x)
    intro q hq; rw [Function.mem_support] at hq ⊢
    exact fun h => hq (finsum_eq_zero_of_forall_eq_zero fun p => by
      rw [h, map_zero, map_zero, map_zero])
  have qSC : (Function.support
      (fun q => ∑ᶠ p, Eminus p (Eminus (q - 2) (Eplus (c - p + 2) (Eplus (d - q) x))))).Finite := by
    apply Set.Finite.subset (Eplus_shift_support_finite d x)
    intro q hq; rw [Function.mem_support] at hq ⊢
    exact fun h => hq (finsum_eq_zero_of_forall_eq_zero fun p => by
      rw [h, map_zero, map_zero, map_zero])
  rw [EE_nest,
    show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ, Eminus p (Eplus (c - p) (Eminus q (Eplus (d - q) x))))
        = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
            (Eminus p (Eminus q (Eplus (c - p) (Eplus (d - q) x)))
              - (2 : ℂ) • Eminus p (Eminus (q - 1) (Eplus (c - p + 1) (Eplus (d - q) x)))
              + Eminus p (Eminus (q - 2) (Eplus (c - p + 2) (Eplus (d - q) x))))
      from finsum_congr fun q => finsum_congr fun p => inner_reorder c d p q x,
    show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
            (Eminus p (Eminus q (Eplus (c - p) (Eplus (d - q) x)))
              - (2 : ℂ) • Eminus p (Eminus (q - 1) (Eplus (c - p + 1) (Eplus (d - q) x)))
              + Eminus p (Eminus (q - 2) (Eplus (c - p + 2) (Eplus (d - q) x)))))
        = ∑ᶠ q : ℤ,
            ((∑ᶠ p, Eminus p (Eminus q (Eplus (c - p) (Eplus (d - q) x))))
              - (2 : ℂ) • (∑ᶠ p, Eminus p (Eminus (q - 1) (Eplus (c - p + 1) (Eplus (d - q) x))))
              + (∑ᶠ p, Eminus p (Eminus (q - 2) (Eplus (c - p + 2) (Eplus (d - q) x)))))
      from finsum_congr fun q => finsum_split3 _ _ _ (pA q) (pB q) (pC q),
    finsum_split3 _ _ _ qSA qSB qSC, ← Tv_eq_nestQ, termB, termC]
  module

/-! ## §12  Operator-level mutual locality `Local Yeα Yeα` (the even-`A₁` diagonal commutes) -/

/-- **The lattice vertex operator commutes with itself**: `[Y(eᵅ,z₁), Y(eᵅ,z₂)] = 0` as
operators on `LatModule` (the even-`A₁` cocycle is trivial, so the operators commute exactly).
From `Yeα_bracket_on_state eeMaster` by `TensorProduct`/`Finsupp` linearity over `p ⊗ e^{nα}`. -/
theorem Yeα_bracket_zero : bracketDist Yeα Yeα = 0 := by
  refine FormalDist₂.ext fun j k => ?_
  refine LinearMap.ext fun y => ?_
  change bracketDist Yeα Yeα j k y = 0
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add y1 y2 h1 h2 => rw [map_add, h1, h2, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, h1, h2, add_zero]
      | single n a =>
          rw [(Finsupp.smul_single_one n a).symm]
          erw [TensorProduct.tmul_smul, map_smul, Yeα_bracket_on_state eeMaster, smul_zero]

/-- **`Local Yeα Yeα`** (the main lattice mutual-locality input, bound `N = 0`): the genuine
boson-dressed lattice vertex operator is mutually local with itself, `pbw`-free. -/
theorem latticeA1_local : Local Yeα Yeα := local_of_bracketDist_eq_zero Yeα_bracket_zero

/-! ## §13  The field-level boson OPE `[α(z₁), E⁺(α,z₂)]` (the `E⁺` companion)

The `E⁺` companion of `alphaField_comm_Eminus` (§7): the boson current contracted with the
annihilation half.  Built on the §8′ contraction `alphaNeg_comp_aExpZ` and the §9
`aExp_commute_alpha` (the positive modes commute with `E⁺`).  With `[α, E⁻]` this is the
Heisenberg–lattice locality datum. -/

/-- `E⁺ = aExpZ` commutes with positive boson modes (`[α_p, aExp] = 0` for `p ≥ 1`). -/
theorem aExpZ_commute_alphaPos (M : ℤ) {p : ℤ} (hp : 1 ≤ p) : Commute (aExpZ M) (α p) := by
  by_cases hM : 0 ≤ M
  · rw [aExpZ_nonneg hM]
    have h := aExp_commute_alpha M.toNat (p - 1).toNat
    rwa [show ((p - 1).toNat : ℤ) + 1 = p from by omega] at h
  · rw [aExpZ_neg (by omega)]; exact Commute.zero_left _

/-- **The field-level boson OPE `[α(z₁), E⁺(α,z₂)]`** (the `E⁺` companion of
`alphaField_comm_Eminus`): the `z₁ʲz₂ᵗ`-coefficient is `2·E⁺_{t+j+1}` for the *creation* modes
`j ≥ 0` (`α₋` of index `j+1 ≥ 1`) and `0` otherwise — the `z₂`-dominant `2·ι₂₁(1/(z₁-z₂))·E⁺`. -/
theorem alphaField_comm_Eplus (j t : ℤ) :
    bracketDist alphaField Eplus j t
      = if 0 ≤ j then (2 : ℂ) • Eplus (t + j + 1) else 0 := by
  rw [bracketDist_apply, alphaField_apply]
  change (α (-j - 1)).comp (Eplus t) - (Eplus t).comp (α (-j - 1)) = _
  by_cases hj : 0 ≤ j
  · rw [if_pos hj, show -j - 1 = -((j + 1).toNat : ℤ) from by omega, Eplus_eq_aExpZ t,
      Eplus_eq_aExpZ (t + j + 1), alphaNeg_comp_aExpZ (j + 1).toNat (by omega) (-t),
      show -t - ((j + 1).toNat : ℤ) = -(t + j + 1) from by omega]
    abel
  · rw [if_neg hj]
    rcases (show -j - 1 = 0 ∨ 1 ≤ -j - 1 from by omega) with h0 | h1
    · rw [h0, show α (0 : ℤ) = (0 : End ℂ B) from HeisenbergN.oscN_zero 1 2 0,
        LinearMap.zero_comp, LinearMap.comp_zero, sub_zero]
    · rw [Eplus_eq_aExpZ t,
        show (α (-j - 1)).comp (aExpZ (-t)) = (aExpZ (-t)).comp (α (-j - 1)) from
          (aExpZ_commute_alphaPos (-t) h1).eq.symm, sub_self]

/-! ## §14  The Heisenberg–lattice mutual locality `Local αLat Yeα`

The second `VA4` generator-locality datum of the `A₁` lattice VOA: the boson current `α(z)`
(Fock dressing plus the `z^{α₀}`-grading zero mode) is mutually local with the lattice vertex
operator `Y(eᵅ,z)`.  The boson commutator `[α(z₁), EE(z₂)]` is `2·EE` away from the zero mode,
where the `α₀`-grading on the lattice factor supplies the missing charge; the combined commutator
`[α(z₁), Y(eᵅ,z₂)] = 2·Y(eᵅ,z₂)` is a clean `δ`-commutator and telescopes under one `(z₁-z₂)`. -/

open LatticeVOA (zGradeOp)

/-- Operator Leibniz on vectors: `f(g(h x)) - g(h(f x)) = [f,g](h x) + g([f,h]x)`. -/
theorem leibniz_vec (f g h : End ℂ B) (x : B) :
    f (g (h x)) - g (h (f x)) = (f * g - g * f) (h x) + g ((f * h - h * f) x) := by
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub]
  abel

/-- **The boson-current/dressing commutator** `[α(z₁), EE(z₂)]`: the `z₁ʲz₂ᵗ`-coefficient is
`2·EE_{t+j+1}` except at `j = -1` (the `α₀` zero mode, which is `0` on the boson factor). -/
theorem alphaField_comm_EE (j t : ℤ) :
    bracketDist alphaField EE j t = if j = -1 then 0 else (2 : ℂ) • EE (t + j + 1) := by
  refine LinearMap.ext fun x => ?_
  have hsupp1 : (Function.support
      (fun m : ℤ => alphaField j (Eminus m (Eplus (t - m) x)))).Finite := by
    apply Set.Finite.subset (EE_marg_support_finite t x)
    intro m hm; rw [Function.mem_support] at hm ⊢
    intro h; exact hm (by rw [h, map_zero])
  have hsupp2 : (Function.support
      (fun m : ℤ => Eminus m (Eplus (t - m) (alphaField j x)))).Finite :=
    EE_marg_support_finite t (alphaField j x)
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    show EE t ((alphaField j) x) = ∑ᶠ m : ℤ, Eminus m (Eplus (t - m) (alphaField j x)) from
      EE_apply_conv t (alphaField j x),
    show (alphaField j) (EE t x) = ∑ᶠ m : ℤ, alphaField j (Eminus m (Eplus (t - m) x)) from by
      rw [EE_apply_conv t x, map_finsum (alphaField j) (EE_marg_support_finite t x)],
    ← finsum_sub_distrib hsupp1 hsupp2,
    show (∑ᶠ m : ℤ, (alphaField j (Eminus m (Eplus (t - m) x))
            - Eminus m (Eplus (t - m) (alphaField j x))))
          = ∑ᶠ m : ℤ, ((bracketDist alphaField Eminus j m) (Eplus (t - m) x)
              + Eminus m ((bracketDist alphaField Eplus j (t - m)) x)) from
        finsum_congr fun m => by
          rw [bracketDist_apply, bracketDist_apply]
          exact leibniz_vec (alphaField j) (Eminus m) (Eplus (t - m)) x]
  simp only [alphaField_comm_Eminus, alphaField_comm_Eplus]
  rcases (show j ≤ -2 ∨ j = -1 ∨ 0 ≤ j from by omega) with hj | hj | hj
  · -- j ≤ -2 : the E⁺ commutator drops; reindex m ↦ m + (j+1)
    rw [if_neg (by omega : ¬ j = -1),
      show (∑ᶠ m : ℤ, ((if j ≤ -2 then (2 : ℂ) • Eminus (m + j + 1) else 0) (Eplus (t - m) x)
              + Eminus m ((if 0 ≤ j then (2 : ℂ) • Eplus (t - m + j + 1) else 0) x)))
          = ∑ᶠ m : ℤ, (2 : ℂ) • Eminus (m + j + 1) (Eplus (t - m) x) from
        finsum_congr fun m => by
          rw [if_pos hj, if_neg (by omega : ¬ 0 ≤ j), LinearMap.smul_apply,
            LinearMap.zero_apply, map_zero, add_zero],
      show ((2 : ℂ) • EE (t + j + 1)) x = (2 : ℂ) • EE (t + j + 1) x from rfl,
      EE_apply_conv (t + j + 1) x, smul_finsum' (2 : ℂ)
        (EE_marg_support_finite (t + j + 1) x),
      ← finsum_comp_equiv (Equiv.addRight (j + 1))
        (f := fun m : ℤ => (2 : ℂ) • Eminus m (Eplus (t + j + 1 - m) x))]
    refine finsum_congr fun m => ?_
    simp only [Equiv.coe_addRight]
    rw [show m + (j + 1) = m + j + 1 from by ring,
      show t + j + 1 - (m + j + 1) = t - m from by ring]
  · -- j = -1 : both commutators drop
    subst hj
    rw [if_pos rfl]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    rw [if_neg (by omega : ¬ (-1 : ℤ) ≤ -2), if_neg (by omega : ¬ (0 : ℤ) ≤ -1)]
    simp
  · -- 0 ≤ j : the E⁻ commutator drops; already in EE form
    rw [if_neg (by omega : ¬ j = -1),
      show (∑ᶠ m : ℤ, ((if j ≤ -2 then (2 : ℂ) • Eminus (m + j + 1) else 0) (Eplus (t - m) x)
              + Eminus m ((if 0 ≤ j then (2 : ℂ) • Eplus (t - m + j + 1) else 0) x)))
          = ∑ᶠ m : ℤ, (2 : ℂ) • Eminus m (Eplus (t + j + 1 - m) x) from
        finsum_congr fun m => by
          rw [if_neg (by omega : ¬ j ≤ -2), if_pos hj, LinearMap.zero_apply, zero_add,
            LinearMap.smul_apply, map_smul, show t - m + j + 1 = t + j + 1 - m from by ring],
      show ((2 : ℂ) • EE (t + j + 1)) x = (2 : ℂ) • EE (t + j + 1) x from rfl,
      EE_apply_conv (t + j + 1) x, smul_finsum' (2 : ℂ)
        (EE_marg_support_finite (t + j + 1) x)]

/-- `zGradeOp` acts by `2n` on `p ⊗ e^{nα}`. -/
theorem zGradeOp_tmul (p : B) (n : ℤ) :
    zGradeOp (p ⊗ₜ[ℂ] eVec n) = ((2 * n : ℤ) : ℂ) • (p ⊗ₜ[ℂ] eVec n) := by
  rw [zGradeOp, LinearMap.lTensor_tmul, LatticeVOA.zGradeL_eVec, TensorProduct.tmul_smul]

/-- The **boson current** `α(z)` on `LatModule`: the boson dressing on the Fock factor plus the
zero-mode `α₀ = z^{α₀}`-grading `zGradeOp` on the lattice factor (the `z₁⁻¹`-coefficient). -/
noncomputable def alphaLat (j : ℤ) : End ℂ LatModule :=
  LinearMap.rTensor LatGrp (alphaField j) + (if j = -1 then zGradeOp else 0)

theorem alphaLat_tmul (j : ℤ) (p : B) (n : ℤ) :
    alphaLat j (p ⊗ₜ[ℂ] eVec n)
      = (alphaField j p) ⊗ₜ[ℂ] eVec n
        + (if j = -1 then ((2 * n : ℤ) : ℂ) • (p ⊗ₜ[ℂ] eVec n) else 0) := by
  rw [alphaLat, LinearMap.add_apply, LinearMap.rTensor_tmul]
  congr 1
  by_cases hj : j = -1
  · rw [if_pos hj, if_pos hj, zGradeOp_tmul]
  · rw [if_neg hj, if_neg hj, LinearMap.zero_apply]

/-- **The Heisenberg–lattice commutator** `[α(z₁), Y(eᵅ,z₂)] = 2·Y(eᵅ,z₂)` translated:
`bracketDist αLat Yeα j t = 2·Yeα_{t+j+1}` — the `α₀` zero-mode cancels the `z₁⁻¹` defect of the
boson commutator (`alphaField_comm_EE`), giving a clean δ-commutator. -/
theorem alphaLat_comm_Yeα_tmul (j t : ℤ) (p : B) (n : ℤ) :
    bracketDist alphaLat Yeα j t (p ⊗ₜ[ℂ] eVec n)
      = (2 : ℂ) • Yeα (t + j + 1) (p ⊗ₜ[ℂ] eVec n) := by
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    Yeα_tmul, alphaLat_tmul, alphaLat_tmul]
  by_cases hj : j = -1
  · -- j = -1 : boson commutator vanishes; the `α₀` grading supplies the `2·Yeα` charge
    subst hj
    rw [if_pos rfl, if_pos rfl, map_add, map_smul, Yeα_tmul, Yeα_tmul, Yeα_tmul]
    have hbz : alphaField (-1) (EE (t - 2 * n) p) = EE (t - 2 * n) (alphaField (-1) p) := by
      have h0 := alphaField_comm_EE (-1) (t - 2 * n)
      rw [if_pos rfl] at h0
      have hp := LinearMap.congr_fun h0 p
      rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.zero_apply] at hp
      exact sub_eq_zero.mp hp
    rw [hbz, show ((2 * (n + 1) : ℤ) : ℂ) = ((2 * n : ℤ) : ℂ) + (2 : ℂ) from by push_cast; ring,
      add_smul, show (t + -1 + 1 - 2 * n) = (t - 2 * n) from by ring]
    abel
  · -- j ≠ -1 : boson commutator `2·EE_{t+j+1}` carries the charge; grading absent
    rw [if_neg hj, if_neg hj, add_zero, add_zero, Yeα_tmul, Yeα_tmul,
      ← TensorProduct.sub_tmul]
    have hbe : alphaField j (EE (t - 2 * n) p) - EE (t - 2 * n) (alphaField j p)
        = (2 : ℂ) • EE (t - 2 * n + j + 1) p := by
      have h0 := alphaField_comm_EE j (t - 2 * n)
      rw [if_neg hj] at h0
      have hp := LinearMap.congr_fun h0 p
      rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.smul_apply] at hp
      exact hp
    rw [hbe, TensorProduct.smul_tmul', show (t - 2 * n + j + 1) = (t + j + 1 - 2 * n) from by ring]

/-- **Operator lift**: `bracketDist αLat Yeα j t = 2 · Yeα_{t+j+1}` on all of `LatModule`. -/
theorem alphaLat_comm_Yeα (j t : ℤ) :
    bracketDist alphaLat Yeα j t = (2 : ℂ) • Yeα (t + j + 1) := by
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y1 y2 h1 h2 => rw [map_add, map_add, h1, h2]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, map_add, h1, h2]
      | single n a =>
          rw [show (Finsupp.single n a : LatGrp) = a • eVec n from
            (Finsupp.smul_single_one n a).symm]
          erw [TensorProduct.tmul_smul, map_smul, map_smul, alphaLat_comm_Yeα_tmul,
            LinearMap.smul_apply]

/-- **The Heisenberg–lattice mutual locality** `Local αLat Yeα` with bound `N = 1`:
the commutator `2·Yeα_{t+j+1}` telescopes to `0` under `mulBySub` (the genuine second `VA4`
generator-locality datum of the `A₁` lattice VOA), `pbw`-free. -/
theorem latticeHL_local : Local alphaLat Yeα := by
  refine ⟨1, ?_⟩
  rw [mulBySubPow_one]
  funext m n
  rw [mulBySub_apply, alphaLat_comm_Yeα, alphaLat_comm_Yeα,
    show n + (m - 1) + 1 = (n - 1) + m + 1 from by ring, sub_self]
  rfl

end LatExp
end VOA
