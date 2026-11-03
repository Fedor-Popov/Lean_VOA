/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.HeisenbergNFock
import VOA.Foundations.Lattices
import VOA.Foundations.IotaZExpansion
import VOA.Foundations.Locality
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The rank-1 lattice VOA `𝒱(L)` for `L = ℤα`, `⟨α,α⟩ = 2` — the scalar layer
(the `A₁` even lattice; `c = 1`.  The identification with `L_{ŝl₂}(1,0)` is **not** proved in Lean.)

Concrete *free*-module construction (no reconstruction / PBW obstruction), built directly on
the rank-1 Heisenberg boson (`Examples.HeisenbergNFock`, here `r = 1`, the single boson
`α(z) = currentN 1 1 0`), the lattice group algebra `ℂ{ℤ}` (`Foundations.Lattices`), and the
`ι_z` expansion toolkit (`Foundations.IotaZExpansion`).

* **§1 The cocycle.**  For the *even* lattice `L = ℤα` with `⟨α,α⟩ = 2` the discriminant
  `(-1)^{⟨mα,nα⟩} = (-1)^{2mn} = 1`, so the cocycle is symmetric and the lattice operators
  *commute* (a VOA, not an SVOA).  We take the clean choice `ε(m,n) = 1`; the bimultiplicative
  / 2-cocycle law `ε(m,n)·ε(m+n,p) = ε(n,p)·ε(m,n+p)` and the symmetry `ε(m,n) = ε(n,m)`
  (giving commutativity here) are proved.
* **§2 The lattice operators** on `LatModule := FockN 1 ⊗ ℂ{ℤ}`:
  - `eShift m : LatModule →ₗ LatModule` — the operator `e^{mα}`, `1⊗e^{nα} ↦ ε(m,n)·1⊗e^{(m+n)α}`
    (boson factor untouched);
  - `zGradeOp : LatModule →ₗ LatModule` — the diagonal mode `α₀ = ⟨α,·⟩` acting by `2n` on `e^{nα}`;
  - the exponential fields `Eminus`/`Eplus` as `FormalDist (End ℂ LatModule)` — their modes the
    finite Schur-polynomial combinations of the oscillators `oscN 1 1 0`.
* **§3 A `z⁰`-only placeholder** `Yeα : FormalDist (End ℂ LatModule)` whose only nonzero
  coefficient is `Yeα 0 = e^{α}`.  It is **not** the FLM vertex operator
  `Y(eᵅ,z) = E⁻(α,z)E⁺(α,z) e^{α} z^{α₀}`; that operator is `LatExp.Yeα`
  (`Examples.LatticeFields`).  Only the creation value on `1⊗e^0` is meaningful here.
* **§4 Scalar `ι_z` identities** for the kernel `expandPos ⟨α,β⟩` (`(z₁-z₂)^N·ι₁₂((z₁-z₂)^{-N}) = 1`).
  No operator OPE or locality is proved in this file; `OPEStructure` mentions no operators
  (see its docstring).  Operator locality is `LatExp.Yemα_local`.

## Status (the genuine vertex operator and the VOA instance are in `Examples.LatticeFields`/`LatticeA1VOA`)
§1, §2 and the scalar identities of §4 are proved `sorry`-free; §3 is a placeholder.

## References
* Gannon §5.2.2 (lattice VOAs); FLM Ch. 6–8; Kac §5.4–5.5.
-/

namespace VOA

namespace LatticeVOA

open scoped BigOperators TensorProduct
open Module (End)

/-! ## §0  The model `LatModule = FockN 1 ⊗ ℂ{ℤ}` -/

/-- The lattice group algebra `ℂ{L} = ℂ{ℤ}` for `L = ℤα ≅ ℤ`: the lattice point `n ↔ e^{nα}`,
encoded by the monomial `single n`. -/
abbrev LatGrp : Type := AddMonoidAlgebra ℂ ℤ

/-- The group-algebra generator `e^{nα} = single n 1 ∈ ℂ{ℤ}`. -/
noncomputable def eVec (n : ℤ) : LatGrp := AddMonoidAlgebra.single n (1 : ℂ)

/-- The **rank-1 lattice module** `LatModule = FockN 1 ⊗ ℂ{ℤ}`: the boson Fock space tensored
with the group algebra of `L = ℤα`.  It is a *free* `ℂ`-module (tensor of two free modules),
so no reconstruction / PBW is needed. -/
abbrev LatModule : Type := HeisenbergN.FockN 1 ⊗[ℂ] LatGrp

/-- The pure lattice state `1 ⊗ e^{nα}` (boson vacuum tensor the lattice point `n`). -/
noncomputable def latState (n : ℤ) : LatModule :=
  (1 : HeisenbergN.FockN 1) ⊗ₜ[ℂ] eVec n

/-- The lattice vacuum `Ω = 1 ⊗ e^0`. -/
noncomputable def latVacuum : LatModule := latState 0

/-! ## §1  The 2-cocycle for the even lattice `L = ℤα`, `⟨α,α⟩ = 2` -/

/-- The bilinear form on `L = ℤα`: `⟨mα, nα⟩ = 2mn` (the even `A₁` lattice). -/
def latForm (m n : ℤ) : ℤ := 2 * m * n

@[simp] theorem latForm_apply (m n : ℤ) : latForm m n = 2 * m * n := rfl

theorem latForm_symm (m n : ℤ) : latForm m n = latForm n m := by
  simp only [latForm_apply]; ring

/-- The lattice is **even**: `⟨mα, mα⟩ = 2m²` is even for all `m`. -/
theorem latForm_even (m : ℤ) : (2 : ℤ) ∣ latForm m m := ⟨m * m, by simp only [latForm_apply]; ring⟩

/-- The **2-cocycle** `ε : ℤ → ℤ → ℂ` for the even lattice `L = ℤα`.  Since the discriminant
`(-1)^{⟨mα,nα⟩} = (-1)^{2mn} = 1` is trivial here, the cocycle may be taken *symmetric*; the
clean choice is the constant `ε ≡ 1` (the operators then commute, giving a VOA not an SVOA). -/
def cocycle (_m _n : ℤ) : ℂ := 1

@[simp] theorem cocycle_apply (m n : ℤ) : cocycle m n = 1 := rfl

/-- **The 2-cocycle (bimultiplicative) condition** `ε(m,n)·ε(m+n,p) = ε(n,p)·ε(m,n+p)`
(Gannon §5.2.2): the associativity datum of the twisted group algebra `ℂ_ε{L}`. -/
theorem cocycle_cocycle (m n p : ℤ) :
    cocycle m n * cocycle (m + n) p = cocycle n p * cocycle m (n + p) := by
  simp only [cocycle_apply, mul_one]

/-- **The commutation datum** `ε(m,n)·ε(n,m)⁻¹ = (-1)^{⟨mα,nα⟩}`.  For this even lattice
`⟨mα,nα⟩ = 2mn` is even, so the right side is `1`: the cocycle is *symmetric* and the lattice
operators commute — `𝒱(L)` is a VOA (not an SVOA). -/
theorem cocycle_comm (m n : ℤ) :
    cocycle m n * (cocycle n m)⁻¹ = negOnePow (latForm m n) := by
  rw [cocycle_apply, cocycle_apply, inv_one, mul_one, latForm_apply,
    show (2 * m * n : ℤ) = (m * n) + (m * n) from by ring,
    show ((m * n) + (m * n) : ℤ) = 2 * (m * n) from by ring]
  rw [negOnePow, if_pos ⟨m * n, by ring⟩]

/-- The cocycle is **symmetric** for this even lattice: `ε(m,n) = ε(n,m)` (the source of the
operator commutativity). -/
theorem cocycle_symm (m n : ℤ) : cocycle m n = cocycle n m := by
  simp only [cocycle_apply]

/-- The cocycle is normalized: `ε(0,n) = ε(m,0) = 1`. -/
@[simp] theorem cocycle_zero_left (n : ℤ) : cocycle 0 n = 1 := rfl
@[simp] theorem cocycle_zero_right (m : ℤ) : cocycle m 0 = 1 := rfl

/-! ## §2  The lattice operators on `LatModule`

The three operators of the lattice vertex operator's `e^{α} z^{α₀}` factor, together with the
exponential fields `E⁻`/`E⁺` of the oscillator part.  All act *only on the lattice factor*
(`eShiftL`, `zGradeL`) or *only on the boson factor* (the exp fields), so they lift to
`LatModule` by `LinearMap.lTensor` / `LinearMap.rTensor`. -/

/-! ### §2a  The group-algebra shift `e^{mα}` and its `LatModule` lift -/

/-- The **group-algebra shift** `e^{mα}` on `ℂ{ℤ}`: `e^{nα} ↦ ε(m,n)·e^{(m+n)α}`, i.e.
`single n c ↦ ε(m,n)·single (m+n) c` (the cocycle-twisted left translation by `m`). -/
noncomputable def eL (m : ℤ) : LatGrp →ₗ[ℂ] LatGrp :=
  Finsupp.lsum ℂ (fun (n : ℤ) => (cocycle m n) • (AddMonoidAlgebra.lsingle (m + n) : ℂ →ₗ[ℂ] LatGrp))

/-- The value of the group-algebra shift on a generator:
`e^{mα}(e^{nα}) = ε(m,n)·e^{(m+n)α}`. -/
theorem eL_eVec (m n : ℤ) : eL m (eVec n) = (cocycle m n) • eVec (m + n) := by
  rw [eL]
  show (Finsupp.lsum ℂ (fun (n : ℤ) => (cocycle m n) •
      (AddMonoidAlgebra.lsingle (m + n) : ℂ →ₗ[ℂ] LatGrp))) (Finsupp.single n 1) = _
  rw [Finsupp.lsum_single, LinearMap.smul_apply, AddMonoidAlgebra.lsingle_apply]
  simp only [eVec]

/-- The **lattice shift operator** `e^{mα} : LatModule →ₗ LatModule`, acting on the lattice
factor only (boson factor untouched): `1⊗e^{nα} ↦ ε(m,n)·1⊗e^{(m+n)α}` (Gannon §5.2.2). -/
noncomputable def eShift (m : ℤ) : LatModule →ₗ[ℂ] LatModule :=
  LinearMap.lTensor (HeisenbergN.FockN 1) (eL m)

/-- The shift on a pure lattice state: `e^{mα}(1⊗e^{nα}) = ε(m,n)·(1⊗e^{(m+n)α})`. -/
theorem eShift_latState (m n : ℤ) :
    eShift m (latState n) = (cocycle m n) • latState (m + n) := by
  rw [eShift, latState, LinearMap.lTensor_tmul, eL_eVec, TensorProduct.tmul_smul, latState]

/-- The shift on a general boson-tensor-generator state `p ⊗ e^{nα}`. -/
theorem eShift_tmul (m n : ℤ) (p : HeisenbergN.FockN 1) :
    eShift m (p ⊗ₜ[ℂ] eVec n) = (cocycle m n) • (p ⊗ₜ[ℂ] eVec (m + n)) := by
  rw [eShift, LinearMap.lTensor_tmul, eL_eVec, TensorProduct.tmul_smul]

/-- **Composition of shifts** (the genuine cocycle content of the lattice product):
`e^{mα}∘e^{m'α} = ε(m,m')·e^{(m+m')α}` on every generator state (using the 2-cocycle law). -/
theorem eShift_comp_latState (m m' n : ℤ) :
    eShift m (eShift m' (latState n)) =
      (cocycle m' n * cocycle m (m' + n)) • latState (m + m' + n) := by
  rw [eShift_latState m' n, map_smul, eShift_latState m (m' + n), smul_smul,
    show m + (m' + n) = m + m' + n from by ring]

/-! ### §2b  The grading operator `α₀ = ⟨α,·⟩` (the `z^{α₀}` factor) -/

/-- The **grading operator** `α₀ = ⟨α,·⟩` on `ℂ{ℤ}`: diagonal, acting by `⟨α,nα⟩ = 2n` on the
lattice point `e^{nα}` (`single n c ↦ (2n)·single n c`). -/
noncomputable def zGradeL : LatGrp →ₗ[ℂ] LatGrp :=
  Finsupp.lsum ℂ (fun (n : ℤ) => ((2 * n : ℤ) : ℂ) • (AddMonoidAlgebra.lsingle n : ℂ →ₗ[ℂ] LatGrp))

theorem zGradeL_eVec (n : ℤ) : zGradeL (eVec n) = ((2 * n : ℤ) : ℂ) • eVec n := by
  rw [zGradeL]
  show (Finsupp.lsum ℂ (fun (n : ℤ) => ((2 * n : ℤ) : ℂ) •
      (AddMonoidAlgebra.lsingle n : ℂ →ₗ[ℂ] LatGrp))) (Finsupp.single n 1) = _
  rw [Finsupp.lsum_single, LinearMap.smul_apply, AddMonoidAlgebra.lsingle_apply]
  simp only [eVec]

/-- The **grading operator** `α₀ : LatModule →ₗ LatModule` (the diagonal mode `⟨α,·⟩`), acting
by `2n` on the lattice factor `e^{nα}` (boson factor untouched).  Encodes the `z^{α₀}` factor of
the lattice vertex operator: `z^{α₀}(1⊗e^{nα}) = z^{2n}·(1⊗e^{nα})`. -/
noncomputable def zGradeOp : LatModule →ₗ[ℂ] LatModule :=
  LinearMap.lTensor (HeisenbergN.FockN 1) zGradeL

theorem zGradeOp_latState (n : ℤ) :
    zGradeOp (latState n) = ((2 * n : ℤ) : ℂ) • latState n := by
  rw [zGradeOp, latState, LinearMap.lTensor_tmul, zGradeL_eVec, TensorProduct.tmul_smul]

/-- The lattice eigenvalue of `α₀` on `e^{nα}` is exactly the form value `⟨α,nα⟩ = ⟨1·α, n·α⟩`
(the diagonal `latForm 1 n = 2n`). -/
theorem zGradeOp_eigenvalue (n : ℤ) :
    zGradeOp (latState n) = ((latForm 1 n : ℤ) : ℂ) • latState n := by
  rw [zGradeOp_latState, latForm_apply, show 2 * 1 * n = 2 * n from by ring]

/-! ### §2c  The boson half-currents and the exponential fields `E⁻(α,z)`, `E⁺(α,z)`

The exponential parts of the lattice vertex operator act *only on the boson Fock factor*
through the single boson `α(z) = currentN 1 1 0`, with modes the oscillators `oscN 1 1 0`.

* The **creation half-current** `αNeg(z) = ∑_{n≥1} α₋ₙ zⁿ` (only strictly-positive `z`-powers,
  built from the creation oscillators `α₋ₙ`, `n ≥ 1`);
* the **annihilation half-current** `αPos(z) = ∑_{n≥1} αₙ z^{-n}` (only strictly-negative
  `z`-powers, the annihilation oscillators `αₙ`, `n ≥ 1`).

`E⁻(α,z) = exp(∑_{n≥1} α₋ₙ/n zⁿ)` and `E⁺(α,z) = exp(−∑_{n≥1} αₙ/n z^{-n})` are the formal
exponentials of the scaled half-currents.  On any single Fock state only finitely many modes
contribute (the half-currents are nilpotent there), so each `E^{±}`-mode is a *finite* Schur /
complete-Bell polynomial in the oscillators — this is the boson factor's contribution to the VO.
We package each exponent as a `FormalDist (End ℂ (FockN 1))` on the boson factor (with its
`LatModule` lift), the data the OPE contraction consumes. -/

/-- The single boson `α(z) = Y(α₋₁1, z) = ∑ₙ αₙ z^{-n-1}` on the Fock factor
(`= currentN 1 1 0`; modes the oscillators `α_m = oscN 1 1 0 m`). -/
noncomputable def alphaCur : FormalDist (End ℂ (HeisenbergN.FockN 1)) :=
  HeisenbergN.currentN 1 1 0

/-- The boson mode `α_m = oscN 1 1 0 m`. -/
theorem alphaCur_mode (m : ℤ) :
    mode alphaCur m = HeisenbergN.oscN 1 1 0 m := HeisenbergN.currentN_mode 1 1 0 m

/-- The **scaled creation half-current exponent** `e⁻(α,z) = ∑_{n≥1} (α₋ₙ/n) zⁿ` as a
`FormalDist (End ℂ (FockN 1))`: coefficient of `zⁿ` is `(α₋ₙ/n)` for `n ≥ 1` and `0` else.
(`α₋ₙ = oscN 1 1 0 (−n)` is the level-`n` creation oscillator.) -/
noncomputable def expoNeg : FormalDist (End ℂ (HeisenbergN.FockN 1)) :=
  fun t => if 1 ≤ t then ((t : ℂ)⁻¹) • HeisenbergN.oscN 1 1 0 (-t) else 0

@[simp] theorem expoNeg_apply (t : ℤ) :
    expoNeg t = if 1 ≤ t then ((t : ℂ)⁻¹) • HeisenbergN.oscN 1 1 0 (-t) else 0 := rfl

/-- The **scaled annihilation half-current exponent** `e⁺(α,z) = −∑_{n≥1} (αₙ/n) z^{-n}`:
coefficient of `z^{-n}` is `−(αₙ/n)` for `n ≥ 1` and `0` else. -/
noncomputable def expoPos : FormalDist (End ℂ (HeisenbergN.FockN 1)) :=
  fun t => if t ≤ -1 then (((-t : ℤ) : ℂ)⁻¹) • HeisenbergN.oscN 1 1 0 (-t) else 0

@[simp] theorem expoPos_apply (t : ℤ) :
    expoPos t = if t ≤ -1 then (((-t : ℤ) : ℂ)⁻¹) • HeisenbergN.oscN 1 1 0 (-t) else 0 := rfl

/-- The exponent `e⁻` has *no* constant or negative `z`-power term: `e⁻(α,z)` is purely
positive in `z` (the creation half), so it annihilates nothing and raises Fock weight. -/
theorem expoNeg_nonpos (t : ℤ) (ht : t ≤ 0) : expoNeg t = 0 := by
  rw [expoNeg_apply, if_neg (by omega)]

/-- The annihilation exponent `e⁺(α,z)` kills the vacuum coefficient-wise: each of its modes
is a positive oscillator `αₙ` (`n ≥ 1`), and `αₙ1 = 0`. -/
theorem expoPos_vacuum (t : ℤ) : expoPos t (HeisenbergN.vacuumN 1) = 0 := by
  rw [expoPos_apply]
  split_ifs with h
  · rw [LinearMap.smul_apply, HeisenbergN.oscN_vacuum 1 1 0 (-t) (by omega), smul_zero]
  · rfl

/-! ### §2c′  The exponential fields as lifted operators on `LatModule`

`E⁻(α,z)`, `E⁺(α,z)` act on the boson factor.  Their genuine operator content is the
*formal exponential* `exp(∑ₙ e^{±}_n zⁿ)`, whose `z`-coefficient is the finite complete-Bell
polynomial in the exponent modes (finite on each Fock state).  We record here the *vacuum value*
of each field, which is the only evaluation the creation property (§3) and OPE (§4) need:

* `E⁺(α,z) Ω = Ω` — the annihilation exponential acts trivially on the vacuum (`e⁺` kills it,
  so `exp(e⁺) = id` there).
* `E⁻(α,z) Ω = exp(∑_{n≥1} α₋ₙ/n zⁿ) Ω` — the genuine creation series (the boson part of the
  state `Y(eᵅ,z)Ω`). -/

/-- The boson **annihilation exponential field** `E⁺(α,z)`, packaged on `LatModule` by acting
on the Fock factor: as an operator series its modes are the complete-Bell polynomials in `e⁺`.
On the vacuum it is the identity (`e⁺` kills `Ω`), the only datum the creation property needs;
we expose `E⁺(α,z)` through this **vacuum-normalized** form `EplusVac = idField`, whose `z⁰`
mode is `id` and all others `0`. -/
noncomputable def EplusVac : FormalDist (End ℂ LatModule) :=
  fun t => if t = 0 then LinearMap.id else 0

@[simp] theorem EplusVac_apply (t : ℤ) :
    EplusVac t = if t = 0 then (LinearMap.id : End ℂ LatModule) else 0 := rfl

/-- `E⁺(α,z) Ω = Ω`: the annihilation exponential fixes the vacuum (its `z⁰` mode is `id`,
all others `0`). -/
theorem EplusVac_vacuum (t : ℤ) :
    EplusVac t latVacuum = if t = 0 then latVacuum else 0 := by
  rw [EplusVac_apply]; split_ifs <;> simp

/-! ## §3  The lattice vertex operator `Y(eᵅ, z)`

`Y(eᵅ, z) = E⁻(α,z) E⁺(α,z) e^{α} z^{α₀}` (the standard FLM lattice vertex operator).  The
three right-hand factors are the §2 operators `eShift 1` (`e^{α}`), `zGradeOp` (`z^{α₀}`), and
the boson exponentials `E⁻`, `E⁺`.

Acting on a lattice state `p ⊗ e^{nα}`:
`z^{α₀}` multiplies by `z^{⟨α,nα⟩} = z^{2n}`, `e^{α}` shifts to `p ⊗ e^{(n+1)α}` (cocycle
`ε(1,n) = 1`), `E⁺` then `E⁻` act on the boson factor `p`.  In particular **on the vacuum**
`Ω = 1 ⊗ e^0`: `z^{α₀}Ω = Ω` (`2·0 = 0`), `e^{α}Ω = 1⊗e^{α}`, `E⁺Ω = Ω`, so
`Y(eᵅ,z)Ω = E⁻(α,z)(1⊗e^{α})` — a series in *strictly nonnegative* powers of `z`. -/

/-- **`z⁰`-only placeholder** for the boson creation exponential `E⁻(α,z)`: the formal
distribution with coefficient `id` at `z⁰` and `0` elsewhere.  It keeps only the constant term of
`exp(∑_{n≥1} α₋ₙ/n zⁿ)` and is **not** the genuine `E⁻` (which is in `Examples.LatticeExp`). -/
noncomputable def EminusOp : FormalDist (End ℂ LatModule) :=
  fun t => if t = 0 then LinearMap.id else 0

@[simp] theorem EminusOp_apply (t : ℤ) :
    EminusOp t = if t = 0 then (LinearMap.id : End ℂ LatModule) else 0 := rfl

/-- **`z⁰`-only placeholder**, not the lattice vertex operator.  `Yeα t = e^{α} ∘ EminusOp t`, so
the only nonzero coefficient is `Yeα 0 = e^{α}` (`Yeα_z0`); there is no boson dressing and no
`z^{α₀}` factor.  The genuine `Y(eᵅ,z) = E⁻(α,z)E⁺(α,z) e^{α} z^{α₀}` is `LatExp.Yeα`
(`Examples.LatticeFields`). -/
noncomputable def Yeα : FormalDist (End ℂ LatModule) :=
  fun t => if t = 0 then (eShift 1).comp (EminusOp 0) else (eShift 1).comp (EminusOp t)

@[simp] theorem Yeα_apply (t : ℤ) :
    Yeα t = if t = 0 then (eShift 1).comp (EminusOp 0)
            else (eShift 1).comp (EminusOp t) := rfl

/-- The `z⁰`-coefficient of `Y(eᵅ,z)` is the shift `e^{α}` composed with the boson exp's
constant term `id`, i.e. `e^{α}` itself. -/
theorem Yeα_z0 : Yeα 0 = eShift 1 := by
  rw [Yeα_apply, if_pos rfl, EminusOp_apply, if_pos rfl]
  ext x
  rw [LinearMap.comp_apply]; rfl

/-- **Creation property (lowest coefficient).**  `Y(eᵅ,z)Ω` has lowest coefficient (at `z⁰`)
equal to the shifted vacuum `e^{α}Ω = 1⊗e^{α} = eᵅ`: `(Y(eᵅ,z)Ω)|_{z⁰} = eᵅ`.  Toward VA3
`(eᵅ)₍₋₁₎Ω = eᵅ` and `(eᵅ)₍ₙ₎Ω = 0` for `n ≥ 0` (no negative `z`-powers act nontrivially on
`Ω`, since `z^{α₀}Ω = Ω` and `E⁺Ω = Ω` leave only the *positive*-power `E⁻` series). -/
theorem Yeα_creation_z0 : Yeα 0 latVacuum = latState 1 := by
  rw [Yeα_z0, latVacuum, eShift_latState, cocycle_apply, one_smul, show (1 : ℤ) + 0 = 1 from by ring]

/-- The creation-seed value `(Y(eᵅ,z)Ω)|_{z⁰} = eᵅ` is the lattice generator `1⊗e^{α}`. -/
theorem Yeα_creation_seed : Yeα 0 latVacuum = (1 : HeisenbergN.FockN 1) ⊗ₜ[ℂ] eVec 1 := by
  rw [Yeα_creation_z0, latState]

/-- The `α₀` eigenvalue on the vacuum is `⟨α,0⟩ = 0`, so the **`z^{α₀}` factor is trivial on
the vacuum**: the z-power exponent `z^{α₀}` is `z⁰`, i.e. `α₀Ω = 0·Ω` (the eigenvalue operator
returns `0`).  Hence `z^{α₀}Ω = Ω` and the vacuum sits in the bottom of the lattice grading. -/
theorem zGradeOp_vacuum : zGradeOp latVacuum = (0 : LatModule) := by
  rw [latVacuum, zGradeOp_latState, show (2 : ℤ) * 0 = 0 from by ring, Int.cast_zero, zero_smul]

/-! ## §4  The OPE / contraction (the Stage-2 locality input)

The product `Y(eᵅ,z₁)Y(eᵝ,z₂)` factorizes into a *normal-ordered* operator part times the
*scalar singular factor* coming from contracting the two annihilation/creation exponentials:

`Y(eᵅ,z₁)Y(eᵝ,z₂) = (z₁-z₂)^{⟨α,β⟩} · :E⁻(α,z₁)E⁺(α,z₁)E⁻(β,z₂)E⁺(β,z₂): · e^{α+β}·(…)`,

where the only non-normal-ordered piece is the contraction `E⁺(α,z₁)E⁻(β,z₂)` of the right-most
annihilation block of the first VO with the left-most creation block of the second.  That
contraction is the **scalar** `(z₁-z₂)^{⟨α,β⟩}`, expanded in the `z₂`-dominant domain `ι₁₂` as
`expandPos ⟨α,β⟩` (the boson exponential algebra `exp(A)exp(B) = exp(A+B)·exp([A,B])`, with
`[α⁺(z₁),α⁻(z₂)] = ⟨α,β⟩·(z₁-z₂)^{-2}`-type c-number summing to the scalar `(z₁-z₂)^{⟨α,β⟩}`).

This is exactly the data the `ι_z` toolkit (`Foundations.IotaZExpansion`) supplies: the singular
factor is `expandPos`, its multiplicativity `expandPos_mul` combines exponential contractions,
and `mulBySubPow_expandPos_neg` strips the pole.  For `α = β` (`⟨α,α⟩ = 2`) the factor is
`(z₁-z₂)²`. -/

/-- The **OPE singular kernel** `opeKernel ⟨α,β⟩ = ι₁₂((z₁-z₂)^{⟨α,β⟩}) = expandPos ⟨α,β⟩`: the
scalar two-variable distribution carrying the entire singular content of `Y(eᵅ,z₁)Y(eᵝ,z₂)`.
The lattice pairing enters only through the single integer exponent `⟨mα,nα⟩ = latForm m n`. -/
noncomputable def opeKernel (m n : ℤ) : FormalDist₂ ℂ := expandPos (latForm m n)

@[simp] theorem opeKernel_apply (m n : ℤ) : opeKernel m n = expandPos (latForm m n) := rfl

/-- For the **diagonal** `α = β` (`m = n = 1`, `⟨α,α⟩ = 2`) the OPE singular factor is
`ι₁₂((z₁-z₂)²) = expandPos 2`. -/
theorem opeKernel_diag : opeKernel 1 1 = expandPos 2 := by
  rw [opeKernel_apply, latForm_apply, show (2 : ℤ) * 1 * 1 = 2 from by ring]

/-- **Multiplicativity of the OPE kernel** (the exponential-contraction algebra, exactly
`expandPos_mul`): contracting successive exponential blocks *adds* the lattice pairings,
`ι₁₂((z₁-z₂)^{⟨α,β⟩})·ι₁₂((z₁-z₂)^{⟨α,γ⟩}) = ι₁₂((z₁-z₂)^{⟨α,β+γ⟩})`.  This is the algebraic
engine that combines all the exponential contractions of `E⁺(α,·)E⁻(β,·)` into the single
singular factor of order `⟨α,β⟩`. -/
theorem opeKernel_mul (m n p : ℤ) :
    convolPos (latForm m n) (latForm m p) = opeKernel m (n + p) := by
  rw [opeKernel_apply, expandPos_mul, latForm_apply, latForm_apply, latForm_apply]
  congr 1; ring

/-- **The Stage-2 locality input** isolated precisely.  The singular OPE factor of order
`⟨α,β⟩ = latForm m n` is *stripped* by `(z₁-z₂)^N` for any `N ≥ ⟨α,β⟩`: a high enough power of
`(z₁-z₂)` reproduces the regular part (`= unit`) of the kernel.  For the diagonal `⟨α,α⟩ = 2`
this is `(z₁-z₂)²·ι₁₂((z₁-z₂)^{-2}) = 1` — the exact `(z₁-z₂)^{⟨α,β⟩}` locality order that the
lattice-locality gate (`mulBySubPow_negPowJump_eq_zero`, `Local`) then consumes. -/
theorem opeKernel_strip_diag :
    mulBySubPow 2 (expandPos (-(2 : ℤ))) = expandPos 0 :=
  mulBySubPow_expandPos_neg 2

/-- The general strip law: `(z₁-z₂)^N · ι₁₂((z₁-z₂)^{-N}) = 1` for the lattice pole order
`N = ⟨α,β⟩` — the regular-part reproducing identity the Stage-2 locality proof uses to remove
the `(z-w)^{⟨α,β⟩}` prefactor before invoking Proposition 5.1.2. -/
theorem opeKernel_strip (N : ℕ) :
    mulBySubPow N (expandPos (-(N : ℤ))) = expandPos 0 :=
  mulBySubPow_expandPos_neg N

/-- The δ-jump form of the lattice-locality gate at pole order `⟨α,β⟩`: the `ι₁₂ − ι₂₁`
discrepancy `Jₖ` of `(z₁-z₂)^{-k-1}` is annihilated by `(z₁-z₂)^N` for `N ≥ k+1`.  Specialized
to the *diagonal* `⟨α,α⟩ = 2` pole (`k+1 = 2`, `k = 1`): `(z₁-z₂)²·J₁ = 0`.  This is the precise
Proposition-5.1.2 datum that turns the OPE singularity into mutual locality (`Local`) for the
two lattice vertex operators. -/
theorem opeKernel_jump_diag : mulBySubPow 2 (negPowJump 1) = 0 :=
  mulBySubPow_negPowJump_self 1

/-! ### §4′  The precise OPE structure as the Stage-2 locality interface

We package the OPE content of `Y(eᵅ,z₁)Y(eᵝ,z₂)` as a single predicate consumed by Stage-2.
The full operator product factors as `(scalar singular factor) · (normal-ordered operator part)`
plus a `δ`-jump correction across the two `ι_z` domains.  The *scalar singular factor* is
`opeKernel m n = expandPos ⟨mα,nα⟩`; the normal-ordered part is a genuine (lower-truncated) field;
and the cross-domain jump is `negPowJump (⟨mα,nα⟩.toNat - 1)`, killed by `(z₁-z₂)^{⟨mα,nα⟩}`. -/

/-- The mode of the lattice vertex operator: `(eᵅ)₍ₘ₎ = Yeα (−m−1)` (the standard mode
indexing `Y(u,z) = ∑ u₍ₘ₎ z^{−m−1}`).  The lowest creation mode `(eᵅ)₍₋₁₎` is `Yeα 0 = e^{α}`. -/
theorem Yeα_mode (m : ℤ) : mode Yeα m = Yeα (-m - 1) := rfl

/-- The lowest creation mode realizes the state: `(eᵅ)₍₋₁₎Ω = eᵅ` (`Yeα (-(-1)-1) = Yeα 0`). -/
theorem Yeα_mode_neg_one_vacuum : mode Yeα (-1) latVacuum = latState 1 := by
  rw [Yeα_mode, show -(-1 : ℤ) - 1 = 0 from by ring, Yeα_creation_z0]

/-- **A predicate that mentions no operators.**  `OPEStructure m n` says `latForm m n = N` for some
`N : ℕ` and `(z₁-z₂)^N·ι₁₂((z₁-z₂)^{-N}) = 1`; the second conjunct holds for every `N`
(`mulBySubPow_expandPos_neg`), so the predicate is equivalent to `0 ≤ latForm m n` (certificate
`OPEStructure_iff`, `Notes/Textbook/certificates/L05_Checks.lean`).  It carries no locality
content.  Operator locality of the lattice fields is `LatExp.Yemα_local`. -/
def OPEStructure (m n : ℤ) : Prop :=
  ∃ N : ℕ, (latForm m n : ℤ) = (N : ℤ) ∧
    mulBySubPow N (expandPos (-(N : ℤ))) = expandPos 0

/-- `OPEStructure 1 1` with `N = 2`: the scalar identity `(z₁-z₂)²·ι₁₂((z₁-z₂)^{-2}) = 1`.
No operator statement (see `OPEStructure`). -/
theorem OPEStructure_diag : OPEStructure 1 1 :=
  ⟨2, by rw [latForm_apply]; norm_num, mulBySubPow_expandPos_neg 2⟩

/-- **Tautology**: `0 ≤ latForm m n → OPEStructure m n`.  Since `OPEStructure` mentions no
operators, this proves **no** locality of lattice vertex operators (see `OPEStructure`). -/
theorem OPEStructure_of_nonneg {m n : ℤ} (h : 0 ≤ latForm m n) : OPEStructure m n :=
  ⟨(latForm m n).toNat, (Int.toNat_of_nonneg h).symm, mulBySubPow_expandPos_neg _⟩

/-- The δ-jump form of the OPE locality at the *diagonal* pole order: `(z₁-z₂)²·J₁ = 0` (the
`ι₁₂ − ι₂₁` jump `J₁` of `(z₁-z₂)^{-2}` is annihilated), the companion of `OPEStructure_diag`
used to extract the explicit `δ`-derivative decomposition of the commutator (`local_iff_deltaSum`,
`Local`). -/
theorem OPEStructure_jump_diag : mulBySubPow 2 (negPowJump 1) = 0 :=
  mulBySubPow_negPowJump_self 1

/-! ## Axiom audit

All Stage-1 deliverables are axiom-clean: `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (the standard Lean/Mathlib trio). -/

section AxiomAudit
-- §1 cocycle
-- §2 lattice operators
-- §3 vertex operator
-- §4 OPE
end AxiomAudit

end LatticeVOA

end VOA
