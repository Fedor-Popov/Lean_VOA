/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuRingInstance
import VOA.Core.SuperEvenPart
import VOA.Examples.TripletW2
import VOA.Examples.SymplecticFermionVirasoroB

/-!
# The super Zhu algebra `A(V)` of a `ℤ`-graded vertex operator superalgebra

The `Modules/Zhu*` layer builds Zhu's associative algebra `A(𝒱) = 𝒱 / O(𝒱)` for a **bosonic**
`VertexOperatorAlgebra`.  This file builds its super analogue, for a `SuperNearVOA` (hence for a
`SuperVertexOperatorAlgebra`, via `toSuperNearVOA`) whose conformal weights are integers.

## ⚠ Which super Zhu algebra?  The literature, and why the obvious reference is the wrong one

There are two Zhu-type algebras for a vertex operator superalgebra — an untwisted one and a
`σ`-twisted one, `σ` the parity involution — and the standard reference gives a formula that is
**not** applicable here.

* **Kac–Wang** (*Vertex operator superalgebras and their representations*, hep-th/9312065,
  Def. 1.7) define, for homogeneous `a`,
  `a ∘ b = Res_z Y(a,z)(1+z)^{deg a}/z² · b` for `a` even and
  `a ∘ b = Res_z Y(a,z)(1+z)^{deg a − 1/2}/z · b` for `a` odd,
  and `a ∗ b = 0` whenever either factor is odd.  The half-shift makes `a ∘ 𝟙 = a` for odd `a`,
  so their `O(V)` contains **all of `V₁̄`** and `A(V) = V₀̄ / O₀̄(V)` is an ordinary (ungraded)
  algebra.  ⚠ This is correct only because Kac–Wang *define* the parity by the weight — their
  §1 reads `V₀̄ = ⊕_{n ∈ ℤ₊} Vₙ`, `V₁̄ = ⊕_{n ∈ ½+ℤ₊} Vₙ` — i.e. **spin–statistics is an axiom
  of their SVOA**, exactly the axiom this library deliberately refuses (`SpinStatistics` is a
  predicate, never a field, and it is *false* for symplectic fermions).  Adamović–Milas
  (arXiv:1006.5134, §2) repeat the definition with the same standing assumption.
  Applied verbatim to symplectic fermions — odd fields of integer weight `1` — the Kac–Wang
  recipe would put `χ^±` into `O(V)` and delete precisely the zero modes the super theory is
  wanted for.  **Do not use it here.**

* **Dong–Zhao** (*Modularity of trace functions in orbifold theory for `ℤ`-graded vertex operator
  superalgebras*, arXiv:math/0601571) treat exactly this library's setting.  Their Def. 2.1 asks
  for a **`ℤ × ℤ₂`-graded** space `V = ⊕ₙ (V₀̄,ₙ ⊕ V₁̄,ₙ)` — weight and parity independent, which
  is the shape of `SuperVertexAlgebra` and the shape of symplectic fermions.  For an automorphism
  `g` of order `T` and `u ∈ Vʳ` their §3 sets
  `u ∘_g v = Res_z (1+z)^{wt u − 1 + δ_r + r/T} / z^{1+δ_r} · Y(u,z)v`,
  `u ∗_g v = Res_z Y(u,z)(1+z)^{wt u}/z · v` for `r = 0` and `0` for `r > 0`,
  `A_g(V) = V/O_g(V)`; Thm 3.1 gives associativity and the unit `[𝟙]`, Thm 3.2 the bijection
  with irreducible `g`-twisted modules, Thm 3.3 semisimplicity in the `g`-rational case.

**Answer to the NS-versus-Ramond question.**  The untwisted (Neveu–Schwarz) case *is* the right
one for an integer-graded VOSA such as symplectic fermions — but in the **Dong–Zhao** form, not the
Kac–Wang form.  At `g = 1` one has `T = 1`, `r = 0`, `δ₀ = 1`, so the exponents collapse to
`(1+z)^{wt u}/z²` and `(1+z)^{wt u}/z`: **the ordinary Zhu formulas, applied to all of `V`, odd
part included, with no half-integer shift for odd elements.**  The `−1/2` of Kac–Wang reappears in
Dong–Zhao only as the `r/T = 1/2` of the `σ`-twisted (Ramond) algebra `A_σ(V)`.  So the shift is
governed by the *weight* (equivalently, by the twist), never by the parity — the same lesson
`Modularity/GammaThetaStatement.lean` records for modularity.  Consequently `superA` below is an
associative **superalgebra**, not an ordinary algebra: the odd part survives.

## The integrality hypothesis

`SuperNearVOA.grading` is `ℂ`-valued, and `(1+z)^h` for `h ∉ ℤ` is an infinite binomial series;
the Zhu sum is then finite only through `regularity`, with no uniform bound, so it cannot be
written as a `Finset.range` sum.  Rather than build a second, weaker apparatus, every definition
here is gated on the **explicit** hypothesis `V.IntegralWeights` (`Core.SuperEvenPart`), reusing
the vocabulary that file already fixed.  This is not a loss: the whole Dong–Zhao theory is stated
for `ℤ`-graded VOSAs, and symplectic fermions are `ℤ`-graded in both parities.

## Main definitions

* `superZhuFamily`, `superZhuMul` — the Zhu product `u ∗ v = Σ_m C(wt u, m) u₍ₘ₋₁₎v`, and
  `superNormalMul` — the normally ordered product `u₍₋₁₎v`.
* `superO`, `superA`, `superMk`, `superOne` — `O(V) = span{(L₋₁u + L₀u) ∗ v}`, the quotient
  `A(V) = V/O(V)`, the projection and the unit; the same shape as the bosonic `O` / `A` / `mk`
  / `one` of `Modules.ZhuAlgebra`.
* `SuperZhuRingData` — the three facts of Dong–Zhao Thm 3.1 (`O` a left ideal, a right ideal, and
  `∗` associative modulo `O`), bundled as **named hypotheses**, exactly as `ZhuRingData` bundled
  them on the bosonic side before they were discharged.
* `SuperZhuRingData.AsRing`, `.AsAlgebra` — the `Ring` and `ℂ`-algebra structure on `superA`
  obtained from that data.
* `SympFerm.chiStateSF` — the weight-one odd symplectic-fermion state `χᵃ = χᵃ₋₁|0⟩`, the
  generator the whole exercise is aimed at.

## Main results

* `superZhuMul_vacuum_left`, `superZhuMul_vacuum_right` — the unit laws `𝟙 ∗ v = v`,
  `v ∗ 𝟙 = v`, **unconditional** (only the vacuum axioms are used).
* `superZhuMul_add_left` / `_smul_left` / `_add_right` / `_smul_right` — bilinearity, the
  prerequisite for descent.
* `superZhuMul_mem_parity` — the Zhu product of parity-homogeneous elements is
  parity-homogeneous, so `superA` is a genuine **superalgebra**.  This needs
  `SuperNearVOA.wtProj_mem_parity`: the weight and parity gradings *are* compatible, because
  `ω` is even, even though nothing links weight to parity.
* `superO_mem_of_L`, `superMk_L_eq_zero` — `(L₋₁u + L₀u) ∗ v ∈ O(V)`, i.e. the defining
  relations do die in `A(V)`.
* `VertexOperatorAlgebra.superZhuMul_toSuper`, `.superO_toSuper`,
  `.superZhuRingData_toSuper` — **coherence and non-vacuity**: on a bosonic VOA read as a super
  one the whole construction *is* the bosonic Zhu construction, and `SuperZhuRingData` is
  therefore **discharged unconditionally** there, by transport from the proved
  `Modules.ZhuRingInstance.zhuRingData_holds`.  So the hypothesis class is inhabited and the
  definitions are not vacuous.
* `superZhuMul_gradingZ_one` — `u ∗ v = u₍₋₁₎v + u₍₀₎v` for `wt u = 1`, the slice `χ^±` live in.
* **The symplectic-fermion application** (§9): `SympFerm.sympFerm_integralWeights` gates the
  construction on `SF`; `chiStateSF_mem_gradingZ_one` and `chiStateSF_mem_parity_one` exhibit
  `χᵃ` as odd of *integer* weight `1` (spin–statistics violated); and
  `superZhuMul_chiStateSF_add_comm`, `superZhuMul_chiStateSF_self` prove
  `χᵃ ∗ χᵇ + χᵇ ∗ χᵃ = 0` and `χᵃ ∗ χᵃ = 0` — the defining relations of the exterior algebra
  `Λ(χ⁺, χ⁻)` — **already in `𝒱`**, hence unconditionally in `A(V)`.  `chiStateSF_sq_eq_zero`
  and `chiStateSF_anticomm` restate them in the ring, given `SuperZhuRingData`.
* `superZhuMul_chiStateSF_zero_one`, `superZhuMul_chiStateSF_one_zero` — the products are
  computed outright: `χ⁰ ∗ χ¹ = −ω` and `χ¹ ∗ χ⁰ = ω`.  So the super Zhu product on `SF` is a
  concrete, non-trivial operation, not a formal shell.

## Status

Definitions, bilinearity, unit laws, parity, quotient bookkeeping, the bilinear descent, the
`Ring`/`Algebra` instances from `SuperZhuRingData`, the bosonic coherence + non-vacuity, and the
symplectic-fermion relations — all `sorry`-free, `native_decide`-free, and axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only; `VOA.pbw` is not used).

⚠ **Not proved, and not claimed:** that `[χᵃ] ≠ 0` in `A(SF)`.  That needs `O(SF)` computed, and
without it the exterior relations above are compatible with `A(SF)` being trivial in those
degrees.  Nor is `A(SF)` shown to be non-semisimple: "contains a nonzero nilpotent" does **not**
imply "not semisimple" (`M₂(ℂ)` is semisimple and full of nilpotents); the correct obstruction is
a nonzero *nilpotent ideal*, i.e. a nonzero Jacobson radical, which `Λ(χ⁺,χ⁻)` supplies only once
`[χᵃ] ≠ 0` is known.

⚠ `SuperZhuRingData` is **not** discharged in this file for a genuinely super algebra, and it is
not claimed to be.  The bosonic proof (`ZhuRightIdeal`, `ZhuAssociator`, `ZhuRingResidue`) runs off
the Borcherds/Jacobi identity `Core.Borcherds.VertexOperatorAlgebra.jacobi`;
`Core.SuperVertexAlgebra` axiomatizes super-*locality* only, so the super Zhu theorem needs the
super Borcherds identity `Core/SuperBorcherds.superJacobi`.  The discharge from that identity is
`Modules/SuperZhuRingDischarge` (`SuperNearVOA.superZhuRingData_holds`).

## A note on the imports

§9 imports `Examples.TripletW2` and `Examples.SymplecticFermionVirasoroB`, so this file in
`Modules/` depends on `Examples/`.  That is against the usual direction of the library.  It costs
nothing (no cycle is possible — nothing in `Examples/` can import this file) and it keeps the
super Zhu algebra and its one worked example together.  To make the layering clean, split §9
into `Examples/SympFermSuperZhu.lean` and drop the two imports; nothing before §9 uses them.

## References
* Dong–Zhao, arXiv:math/0601571, Def. 2.1, §3 (3.1)–(3.2), Thms 3.1–3.3 — the definition used.
* Kac–Wang, hep-th/9312065, Def. 1.7, Rem. 1.1, Thm 1.1 — the `½ℤ`-graded (spin–statistics)
  variant, recorded above and deliberately *not* used.
* Adamović–Milas, arXiv:1006.5134, §2; van Ekeren, arXiv:1111.0682 (twisted modularity).
* Zhu, Thm 2.1.1–2.1.2; Gannon §5.3.2, eqs. (5.3.8)–(5.3.10) — the bosonic original mirrored here.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §0  The missing mode API on the super side

`Core.VertexAlgebra` has `smul_add_left` … `smul_vacuum_left`; the super file stops at
`smul_mem_grading` / `smul_mem_parity`.  These are the same one-line proofs. -/

namespace SuperVertexAlgebra

variable (V : SuperVertexAlgebra 𝒱)

/-- `(u₁ + u₂)₍ₙ₎v = u₁₍ₙ₎v + u₂₍ₙ₎v`. -/
@[simp] theorem smul_add_left (u₁ u₂ : 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul (u₁ + u₂) n v = V.smul u₁ n v + V.smul u₂ n v := by
  simp only [smul_def, map_add, mode_add, LinearMap.add_apply]

/-- `(c • u)₍ₙ₎v = c • (u₍ₙ₎v)`. -/
@[simp] theorem smul_smul_left (c : ℂ) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul (c • u) n v = c • V.smul u n v := by
  simp only [smul_def, map_smul, mode_smul, LinearMap.smul_apply]

/-- `0₍ₙ₎v = 0`. -/
@[simp] theorem smul_zero_left (n : ℤ) (v : 𝒱) : V.smul 0 n v = 0 := by
  simp only [smul_def, map_zero, mode_zero, LinearMap.zero_apply]

/-- `u₍ₙ₎(v₁ + v₂) = u₍ₙ₎v₁ + u₍ₙ₎v₂`. -/
@[simp] theorem smul_add_right (u : 𝒱) (n : ℤ) (v₁ v₂ : 𝒱) :
    V.smul u n (v₁ + v₂) = V.smul u n v₁ + V.smul u n v₂ :=
  map_add (mode (V.Y u) n) v₁ v₂

/-- `u₍ₙ₎(c • v) = c • (u₍ₙ₎v)`. -/
@[simp] theorem smul_smul_right (u : 𝒱) (c : ℂ) (n : ℤ) (v : 𝒱) :
    V.smul u n (c • v) = c • V.smul u n v :=
  map_smul (mode (V.Y u) n) c v

/-- `u₍ₙ₎0 = 0`. -/
@[simp] theorem smul_zero_right (u : 𝒱) (n : ℤ) : V.smul u n (0 : 𝒱) = 0 :=
  map_zero (mode (V.Y u) n)

/-- **VA2 in mode form**: `𝟙₍ₙ₎v = δ_{n,−1} v`. -/
@[simp] theorem smul_vacuum_left (n : ℤ) (v : 𝒱) :
    V.smul V.vacuum n v = if n = -1 then v else 0 := by
  rw [smul_def, V.vacuum_Y, mode_one]
  split_ifs <;> simp

end SuperVertexAlgebra

namespace SuperNearVOA

variable (V : SuperNearVOA 𝒱)

/-! ## §1  The Zhu product (Dong–Zhao (3.2) at `g = 1`)

Verbatim the shape of `VOA.zhuFamily` / `VOA.zhuMul`, with the `ℤ`-grading
supplied by `gradingZ` and the integrality hypothesis. -/

/-- The weight-`k` slice of the super Zhu product `· ∗ v`: on `uₖ ∈ 𝒱ₖ`,
`Σ_{m=0}^{k} C(k,m) (uₖ)₍ₘ₋₁₎ v`.  Dong–Zhao (3.2) at `g = 1`; **no parity case split** —
that is the whole point (see the module docstring). -/
noncomputable def superZhuFamily (v : 𝒱) (k : ℤ) : (V.gradingZ k) →ₗ[ℂ] 𝒱 where
  toFun uk := ∑ m ∈ Finset.range (k.toNat + 1), cbz k m • V.smul (uk : 𝒱) ((m : ℤ) - 1) v
  map_add' a b := by
    simp only [Submodule.coe_add, SuperVertexAlgebra.smul_add_left, smul_add,
      Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [SetLike.val_smul, SuperVertexAlgebra.smul_smul_left, smul_comm c,
      RingHom.id_apply, Finset.smul_sum]

/-- **The super Zhu product** `u ∗ v = Res_z(Y(u,z) v (1+z)^{wt u}/z)`, extended bilinearly over
the weight decomposition of `u` (Dong–Zhao (3.2) at `g = 1`). -/
noncomputable def superZhuMul (hV : V.IntegralWeights) (u v : 𝒱) : 𝒱 :=
  letI := DirectSum.IsInternal.chooseDecomposition V.gradingZ (V.gradingZ_isInternal hV)
  (DFinsupp.lsum ℂ (V.superZhuFamily v)) (DirectSum.decompose V.gradingZ u)

/-- The **normally ordered product** `u · v = u₍₋₁₎v` (Dong–Zhao / Zhu 5.3.10a). -/
def superNormalMul (u v : 𝒱) : 𝒱 := V.smul u (-1) v

@[simp] theorem superNormalMul_def (u v : 𝒱) : V.superNormalMul u v = V.smul u (-1) v := rfl

/-- The super Zhu product collapses on a weight-homogeneous left factor. -/
theorem superZhuMul_homogeneous (hV : V.IntegralWeights) {k : ℤ} {u : 𝒱}
    (hu : u ∈ V.gradingZ k) (v : 𝒱) :
    V.superZhuMul hV u v
      = ∑ m ∈ Finset.range (k.toNat + 1), cbz k m • V.smul u ((m : ℤ) - 1) v := by
  letI := DirectSum.IsInternal.chooseDecomposition V.gradingZ (V.gradingZ_isInternal hV)
  change (DFinsupp.lsum ℂ (V.superZhuFamily v)) (DirectSum.decompose V.gradingZ u) = _
  rw [DirectSum.decompose_of_mem V.gradingZ hu]
  exact DFinsupp.lsum_single ℂ (V.superZhuFamily v) k ⟨u, hu⟩

/-! ## §2  Bilinearity -/

/-- The weight slice is additive in the right factor. -/
theorem superZhuFamily_add (v₁ v₂ : 𝒱) :
    V.superZhuFamily (v₁ + v₂) = V.superZhuFamily v₁ + V.superZhuFamily v₂ := by
  funext k
  refine LinearMap.ext fun uk => ?_
  simp only [Pi.add_apply, LinearMap.add_apply, superZhuFamily, LinearMap.coe_mk, AddHom.coe_mk,
    SuperVertexAlgebra.smul_add_right, smul_add, Finset.sum_add_distrib]

/-- The weight slice is homogeneous in the right factor. -/
theorem superZhuFamily_smul (c : ℂ) (v : 𝒱) :
    V.superZhuFamily (c • v) = c • V.superZhuFamily v := by
  funext k
  refine LinearMap.ext fun uk => ?_
  simp only [Pi.smul_apply, LinearMap.smul_apply, superZhuFamily, LinearMap.coe_mk, AddHom.coe_mk,
    SuperVertexAlgebra.smul_smul_right, Finset.smul_sum, smul_comm c]

/-- **`(u₁ + u₂) ∗ v = u₁ ∗ v + u₂ ∗ v`.** -/
theorem superZhuMul_add_left (hV : V.IntegralWeights) (u₁ u₂ v : 𝒱) :
    V.superZhuMul hV (u₁ + u₂) v = V.superZhuMul hV u₁ v + V.superZhuMul hV u₂ v := by
  letI := DirectSum.IsInternal.chooseDecomposition V.gradingZ (V.gradingZ_isInternal hV)
  exact map_add ((DFinsupp.lsum ℂ (V.superZhuFamily v)).comp
    (DirectSum.decomposeLinearEquiv V.gradingZ).toLinearMap) u₁ u₂

/-- **`(c • u) ∗ v = c • (u ∗ v)`.** -/
theorem superZhuMul_smul_left (hV : V.IntegralWeights) (c : ℂ) (u v : 𝒱) :
    V.superZhuMul hV (c • u) v = c • V.superZhuMul hV u v := by
  letI := DirectSum.IsInternal.chooseDecomposition V.gradingZ (V.gradingZ_isInternal hV)
  exact map_smul ((DFinsupp.lsum ℂ (V.superZhuFamily v)).comp
    (DirectSum.decomposeLinearEquiv V.gradingZ).toLinearMap) c u

/-- **`u ∗ (v₁ + v₂) = u ∗ v₁ + u ∗ v₂`.** -/
theorem superZhuMul_add_right (hV : V.IntegralWeights) (u v₁ v₂ : 𝒱) :
    V.superZhuMul hV u (v₁ + v₂) = V.superZhuMul hV u v₁ + V.superZhuMul hV u v₂ := by
  letI := DirectSum.IsInternal.chooseDecomposition V.gradingZ (V.gradingZ_isInternal hV)
  change (DFinsupp.lsum ℂ (V.superZhuFamily (v₁ + v₂))) (DirectSum.decompose V.gradingZ u) = _
  rw [superZhuFamily_add, map_add, LinearMap.add_apply]
  rfl

/-- **`u ∗ (c • v) = c • (u ∗ v)`.** -/
theorem superZhuMul_smul_right (hV : V.IntegralWeights) (c : ℂ) (u v : 𝒱) :
    V.superZhuMul hV u (c • v) = c • V.superZhuMul hV u v := by
  letI := DirectSum.IsInternal.chooseDecomposition V.gradingZ (V.gradingZ_isInternal hV)
  change (DFinsupp.lsum ℂ (V.superZhuFamily (c • v))) (DirectSum.decompose V.gradingZ u) = _
  rw [superZhuFamily_smul, map_smul, LinearMap.smul_apply]
  rfl

/-- The super Zhu product as a `ℂ`-bilinear map `𝒱 →ₗ 𝒱 →ₗ 𝒱`. -/
noncomputable def superZhuMulₗ (hV : V.IntegralWeights) : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱 where
  toFun u :=
    { toFun := fun v => V.superZhuMul hV u v
      map_add' := fun v₁ v₂ => V.superZhuMul_add_right hV u v₁ v₂
      map_smul' := fun c v => V.superZhuMul_smul_right hV c u v }
  map_add' u₁ u₂ := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    exact V.superZhuMul_add_left hV u₁ u₂ v
  map_smul' c u := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
    exact V.superZhuMul_smul_left hV c u v

@[simp] theorem superZhuMulₗ_apply (hV : V.IntegralWeights) (u v : 𝒱) :
    V.superZhuMulₗ hV u v = V.superZhuMul hV u v := rfl

/-! ## §3  The unit laws -/

/-- **Left unit:** `𝟙 ∗ v = v`.  The vacuum's only weight slice is at `0`, where `C(0,m) = δ_{m,0}`
and `𝟙₍₋₁₎v = v`. -/
theorem superZhuMul_vacuum_left (hV : V.IntegralWeights) (v : 𝒱) :
    V.superZhuMul hV V.vacuum v = v := by
  have hmem : V.vacuum ∈ V.gradingZ 0 := by
    change V.vacuum ∈ V.grading (((0 : ℤ) : ℂ))
    rw [Int.cast_zero]
    exact V.vacuum_mem
  rw [V.superZhuMul_homogeneous hV hmem v,
    show (0 : ℤ).toNat + 1 = 1 from rfl, Finset.sum_range_one]
  simp only [Nat.cast_zero, cbz_zero, one_smul, zero_sub]
  rw [SuperVertexAlgebra.smul_vacuum_left, if_pos rfl]

/-- **Right unit:** `v ∗ 𝟙 = v`.  On each weight only the `m = 0` term survives (`v₍ₘ₋₁₎𝟙 = 0`
for `m ≥ 1` by creation, `v₍₋₁₎𝟙 = v`), so the product reassembles the weight decomposition. -/
theorem superZhuMul_vacuum_right (hV : V.IntegralWeights) (v : 𝒱) :
    V.superZhuMul hV v V.vacuum = v := by
  letI := DirectSum.IsInternal.chooseDecomposition V.gradingZ (V.gradingZ_isInternal hV)
  letI : ∀ (i : ℤ) (x : V.gradingZ i), Decidable (x ≠ 0) := fun _ _ => Classical.dec _
  change (DFinsupp.lsum ℂ (V.superZhuFamily V.vacuum)) (DirectSum.decompose V.gradingZ v) = v
  have hfam : V.superZhuFamily V.vacuum = fun k => (V.gradingZ k).subtype := by
    funext k
    refine LinearMap.ext fun uk => ?_
    change ∑ m ∈ Finset.range (k.toNat + 1),
        cbz k m • V.smul (uk : 𝒱) ((m : ℤ) - 1) V.vacuum = (uk : 𝒱)
    rw [Finset.sum_eq_single 0 (fun m _ hm => ?_) (fun h0 => ?_)]
    · simp only [Nat.cast_zero, cbz_zero, one_smul, zero_sub]
      exact V.smul_neg_one_vacuum (uk : 𝒱)
    · rw [V.smul_vacuum_eq_zero (uk : 𝒱) (by omega : (0 : ℤ) ≤ (m : ℤ) - 1), smul_zero]
    · exact absurd (Finset.mem_range.mpr (by omega)) h0
  rw [hfam, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
  exact DirectSum.sum_support_decompose V.gradingZ v

/-! ## §4  `O(V)` and the super Zhu algebra `A(V)`

Zhu's `O(𝒱) = span{(L₋₁u + L₀u) ∗ v}` (Gannon 5.3.8c), the form `Modules.ZhuAlgebra.O` uses; it is
the same subspace as `span{u ∘ v}`, since `u ∘ 𝟙 = L₋₁u + L₀u`. -/

/-- `O(V) := span{(L₋₁u + L₀u) ∗ v}`, the super analogue of `VOA.O`. -/
def superO (hV : V.IntegralWeights) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ u v : 𝒱, x = V.superZhuMul hV (V.L (-1) u + V.L 0 u) v}

/-- The generators of `O(V)` are in `O(V)`. -/
theorem superO_mem_of_L (hV : V.IntegralWeights) (u v : 𝒱) :
    V.superZhuMul hV (V.L (-1) u + V.L 0 u) v ∈ V.superO hV :=
  Submodule.subset_span ⟨u, v, rfl⟩

/-- **The super Zhu algebra** `A(V) := V / O(V)` as a `ℂ`-module.  Its associative structure
descends from `∗` once `SuperZhuRingData` is available. -/
abbrev superA (hV : V.IntegralWeights) : Type u := 𝒱 ⧸ V.superO hV

/-- The canonical projection `V → A(V)`, `u ↦ [u]`. -/
def superMk (hV : V.IntegralWeights) : 𝒱 →ₗ[ℂ] V.superA hV := (V.superO hV).mkQ

/-- The unit `[𝟙] ∈ A(V)`. -/
def superOne (hV : V.IntegralWeights) : V.superA hV := V.superMk hV V.vacuum

theorem superMk_surjective (hV : V.IntegralWeights) : Function.Surjective (V.superMk hV) :=
  Submodule.mkQ_surjective _

theorem superMk_eq_iff (hV : V.IntegralWeights) {u v : 𝒱} :
    V.superMk hV u = V.superMk hV v ↔ u - v ∈ V.superO hV := by
  rw [superMk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]

theorem superMk_eq_zero_iff (hV : V.IntegralWeights) {u : 𝒱} :
    V.superMk hV u = 0 ↔ u ∈ V.superO hV := by
  rw [superMk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- **The defining relation dies in `A(V)`**: `[(L₋₁u + L₀u) ∗ v] = 0`. -/
theorem superMk_L_eq_zero (hV : V.IntegralWeights) (u v : 𝒱) :
    V.superMk hV (V.superZhuMul hV (V.L (-1) u + V.L 0 u) v) = 0 :=
  (V.superMk_eq_zero_iff hV).mpr (V.superO_mem_of_L hV u v)

/-- `[L₋₁u + L₀u] = 0` — the `v = 𝟙` case, i.e. `u ∘ 𝟙 ∈ O(V)`. -/
theorem superMk_L_vacuum_eq_zero (hV : V.IntegralWeights) (u : 𝒱) :
    V.superMk hV (V.L (-1) u + V.L 0 u) = 0 := by
  have h := V.superMk_L_eq_zero hV u V.vacuum
  rwa [V.superZhuMul_vacuum_right hV] at h

/-! ## §5  Parity: `A(V)` is a *super*algebra

This is where the super theory differs from the bosonic one in substance, and it is why the
Kac–Wang recipe had to be rejected: the odd part is not thrown away, so `∗` had better respect
the `ℤ₂`-grading.  It does — but the proof needs the fact, which is *not* an axiom, that the
weight and parity gradings are compatible: `SuperNearVOA.wtProj_mem_parity`, itself a consequence
of `ω` being even. -/

/-- **Every parity-homogeneous state is a sum of bi-homogeneous ones.**  The weight components of
a parity-homogeneous state are again parity-homogeneous (`wtProj_mem_parity`), and with integral
weights the non-integer components vanish. -/
theorem parity_le_iSup_gradingZ_inf (hV : V.IntegralWeights) (p : ZMod 2) :
    V.parity p ≤ ⨆ k : ℤ, (V.gradingZ k ⊓ V.parity p) := by
  intro u hu
  obtain ⟨s, hsum, -⟩ := V.exists_sum_wtProj u
  rw [← hsum]
  refine Submodule.sum_mem _ fun h _ => ?_
  by_cases hh : ∃ k : ℤ, (k : ℂ) = h
  · obtain ⟨k, rfl⟩ := hh
    exact Submodule.mem_iSup_of_mem k
      ⟨V.wtProj_mem (k : ℂ) u, V.wtProj_mem_parity (k : ℂ) hu⟩
  · have hz : V.wtProj h u = 0 := by
      have hmem := V.wtProj_mem h u
      rw [hV h hh, Submodule.mem_bot] at hmem
      exact hmem
    rw [hz]
    exact Submodule.zero_mem _

/-- The Zhu product of a **bi-homogeneous** left factor with a parity-homogeneous right factor is
parity-homogeneous.  Direct from the collapsed formula and `smul_mem_parity`. -/
theorem superZhuMul_mem_parity_of_gradingZ (hV : V.IntegralWeights) {k : ℤ} {p q : ZMod 2}
    {u v : 𝒱} (hk : u ∈ V.gradingZ k) (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) :
    V.superZhuMul hV u v ∈ V.parity (p + q) := by
  rw [V.superZhuMul_homogeneous hV hk v]
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  exact V.smul_mem_parity hu hv ((m : ℤ) - 1)

/-- **The Zhu product respects parity**: `|u ∗ v| = |u| + |v|`.  Hence `O(V)` is spanned by
`ℤ₂`-homogeneous elements and `A(V)` is an associative **superalgebra**, not merely an algebra —
the structural difference from Kac–Wang's `A(V) = V₀̄/O₀̄(V)`. -/
theorem superZhuMul_mem_parity (hV : V.IntegralWeights) {p q : ZMod 2} {u v : 𝒱}
    (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) :
    V.superZhuMul hV u v ∈ V.parity (p + q) := by
  have hsub : (⨆ k : ℤ, (V.gradingZ k ⊓ V.parity p))
      ≤ Submodule.comap ((V.superZhuMulₗ hV).flip v) (V.parity (p + q)) := by
    refine iSup_le fun k => ?_
    intro x hx
    rw [Submodule.mem_inf] at hx
    change V.superZhuMul hV x v ∈ V.parity (p + q)
    exact V.superZhuMul_mem_parity_of_gradingZ hV hx.1 hx.2 hv
  exact hsub (V.parity_le_iSup_gradingZ_inf hV p hu)

/-! ## §6  Descent of the product, and the `Ring` structure

The two-sided-ideal property and associativity modulo `O(V)` are Dong–Zhao Thm 3.1.  They are
**not proved here** (see the Status section: the super Borcherds identity does not exist in this
repository), so they are bundled as explicit named hypotheses and everything downstream is
parametric in them — the same discipline `Modules.ZhuRing.ZhuRingData` used on the bosonic side
before `ZhuRingInstance` discharged it. -/

/-- Right-lift: `O ≤ ker (B.compr₂ mk).flip`. -/
theorem superDescend_right_ker (hV : V.IntegralWeights) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ V.superO hV → B u v ∈ V.superO hV) :
    V.superO hV ≤ LinearMap.ker (B.compr₂ (V.superMk hV)).flip := by
  intro v hv
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.flip_apply, LinearMap.compr₂_apply, LinearMap.zero_apply, superMk]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hright u hv)

/-- Left-lift. -/
theorem superDescend_left_ker (hV : V.IntegralWeights) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ V.superO hV → ∀ v, B u v ∈ V.superO hV)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ V.superO hV → B u v ∈ V.superO hV) :
    V.superO hV ≤ LinearMap.ker
      (((V.superO hV).liftQ (B.compr₂ (V.superMk hV)).flip
        (V.superDescend_right_ker hV B hright)).flip) := by
  intro u hu
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun vb => ?_
  refine Submodule.Quotient.induction_on _ vb fun v => ?_
  simp only [LinearMap.flip_apply, Submodule.liftQ_apply, LinearMap.compr₂_apply,
    LinearMap.zero_apply, superMk]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hleft hu v)

/-- **Generic descent** of a `ℂ`-bilinear map to `A(V)`, given that `O(V)` is a two-sided ideal
for it. -/
noncomputable def superDescendBilin (hV : V.IntegralWeights) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ V.superO hV → ∀ v, B u v ∈ V.superO hV)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ V.superO hV → B u v ∈ V.superO hV) :
    V.superA hV →ₗ[ℂ] V.superA hV →ₗ[ℂ] V.superA hV :=
  (V.superO hV).liftQ
    (((V.superO hV).liftQ (B.compr₂ (V.superMk hV)).flip
      (V.superDescend_right_ker hV B hright)).flip)
    (V.superDescend_left_ker hV B hleft hright)

theorem superDescendBilin_apply (hV : V.IntegralWeights) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ V.superO hV → ∀ v, B u v ∈ V.superO hV)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ V.superO hV → B u v ∈ V.superO hV) (u v : 𝒱) :
    V.superDescendBilin hV B hleft hright (V.superMk hV u) (V.superMk hV v)
      = V.superMk hV (B u v) := by
  simp only [superDescendBilin, superMk, Submodule.mkQ_apply, Submodule.liftQ_apply,
    LinearMap.flip_apply, LinearMap.compr₂_apply]

/-! ## §7  Two tools: weight-`1` elements, and extension from the homogeneous pieces -/

/-- **The Zhu product of a weight-`1` element**: `u ∗ v = u₍₋₁₎v + u₍₀₎v` (`C(1,0) = C(1,1) = 1`).
This is the slice the symplectic-fermion generators `χ^±` live in — they have conformal weight `1`
and are odd, the configuration that makes spin–statistics fail and that Kac–Wang's axioms exclude
outright. -/
theorem superZhuMul_gradingZ_one (hV : V.IntegralWeights) {u : 𝒱} (hu : u ∈ V.gradingZ 1)
    (v : 𝒱) : V.superZhuMul hV u v = V.smul u (-1) v + V.smul u 0 v := by
  have hc1 : cbz 1 1 = 1 := by
    rw [cbz_apply_nonneg _ (by norm_num), show ((1 : ℤ)).toNat = 1 from rfl, gBinom]
    norm_num
  rw [V.superZhuMul_homogeneous hV hu v, show (1 : ℤ).toNat + 1 = 2 from rfl,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.cast_zero, Nat.cast_one, cbz_zero, hc1, one_smul, zero_sub, sub_self]

/-- **Two linear maps that agree on every weight space are equal.**  The engine of the bosonic
coherence below: with integral weights the `ℤ`-graded pieces span `𝒱`. -/
theorem eq_of_eq_on_gradingZ (hV : V.IntegralWeights) {f g : 𝒱 →ₗ[ℂ] 𝒱}
    (h : ∀ (k : ℤ), ∀ u ∈ V.gradingZ k, f u = g u) : f = g := by
  have htop : (⨆ k : ℤ, V.gradingZ k) = ⊤ := by
    have hint := V.gradingZ_isInternal hV
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint
    exact hint.2
  have hker : (⨆ k : ℤ, V.gradingZ k) ≤ LinearMap.ker (f - g) := by
    refine iSup_le fun k => fun x hx => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact h k x hx
  refine LinearMap.ext fun u => ?_
  have hu : u ∈ LinearMap.ker (f - g) := by
    refine hker ?_
    rw [htop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hu
  exact hu

end SuperNearVOA

/-- **The content of Dong–Zhao Thm 3.1**, bundled as named hypotheses: `O(V)` is a two-sided
ideal for the super Zhu product and the product is associative modulo `O(V)`.

⚠ This is a *hypothesis class*, not a theorem.  It is discharged unconditionally in the bosonic
case (`superZhuRingData_toSuper`, by transport from `Modules.ZhuRingInstance.zhuRingData_holds`),
so it is inhabited and the consumers below are not vacuous; for a genuinely super algebra it is
open here, blocked on the missing super Borcherds/Jacobi identity. -/
structure SuperZhuRingData (V : SuperNearVOA 𝒱) (hV : V.IntegralWeights) : Prop where
  /-- `O` is a left ideal: `u ∈ O ⟹ u ∗ v ∈ O`. -/
  left_ideal : ∀ {u : 𝒱}, u ∈ V.superO hV → ∀ v, V.superZhuMul hV u v ∈ V.superO hV
  /-- `O` is a right ideal: `v ∈ O ⟹ u ∗ v ∈ O`. -/
  right_ideal : ∀ (u : 𝒱) {v : 𝒱}, v ∈ V.superO hV → V.superZhuMul hV u v ∈ V.superO hV
  /-- `∗` is associative mod `O`: `(u∗v)∗w − u∗(v∗w) ∈ O`. -/
  assoc : ∀ u v w : 𝒱,
    V.superZhuMul hV (V.superZhuMul hV u v) w - V.superZhuMul hV u (V.superZhuMul hV v w)
      ∈ V.superO hV

namespace SuperZhuRingData

variable {V : SuperNearVOA 𝒱} {hV : V.IntegralWeights} (hZ : SuperZhuRingData V hV)

/-- The descended super Zhu product on `A(V)`: `[u]·[v] = [u ∗ v]`. -/
noncomputable def superAmul : V.superA hV →ₗ[ℂ] V.superA hV →ₗ[ℂ] V.superA hV :=
  V.superDescendBilin hV (V.superZhuMulₗ hV)
    (fun {_} hu v => hZ.left_ideal hu v)
    (fun u {_} hv => hZ.right_ideal u hv)

@[simp] theorem superAmul_mk (u v : 𝒱) :
    hZ.superAmul (V.superMk hV u) (V.superMk hV v) = V.superMk hV (V.superZhuMul hV u v) := by
  rw [superAmul, V.superDescendBilin_apply]; rfl

/-- Associativity of the descended product. -/
theorem superAmul_assoc (p q r : V.superA hV) :
    hZ.superAmul (hZ.superAmul p q) r = hZ.superAmul p (hZ.superAmul q r) := by
  obtain ⟨u, rfl⟩ := V.superMk_surjective hV p
  obtain ⟨v, rfl⟩ := V.superMk_surjective hV q
  obtain ⟨w, rfl⟩ := V.superMk_surjective hV r
  rw [superAmul_mk, superAmul_mk, superAmul_mk, superAmul_mk, V.superMk_eq_iff hV]
  exact hZ.assoc u v w

/-- Left unit `[𝟙]·[v] = [v]`. -/
theorem superAmul_one_left (p : V.superA hV) :
    hZ.superAmul (V.superMk hV V.vacuum) p = p := by
  obtain ⟨v, rfl⟩ := V.superMk_surjective hV p
  rw [superAmul_mk, V.superZhuMul_vacuum_left hV]

/-- Right unit `[v]·[𝟙] = [v]`. -/
theorem superAmul_one_right (p : V.superA hV) :
    hZ.superAmul p (V.superMk hV V.vacuum) = p := by
  obtain ⟨v, rfl⟩ := V.superMk_surjective hV p
  rw [superAmul_mk, V.superZhuMul_vacuum_right hV]

/-- **The super Zhu algebra as a `Ring`** (Dong–Zhao Thm 3.1), on the existing quotient
`AddCommGroup` so that there is no additive diamond: multiplication `[u]·[v] = [u ∗ v]`,
unit `[𝟙]`. -/
@[reducible] noncomputable def AsRing : Ring (V.superA hV) :=
  { (inferInstance : AddCommGroup (V.superA hV)) with
    mul := fun p q => hZ.superAmul p q
    one := V.superMk hV V.vacuum
    mul_assoc := hZ.superAmul_assoc
    one_mul := hZ.superAmul_one_left
    mul_one := hZ.superAmul_one_right
    left_distrib := fun p q r => by
      change hZ.superAmul p (q + r) = hZ.superAmul p q + hZ.superAmul p r
      rw [map_add]
    right_distrib := fun p q r => by
      change hZ.superAmul (p + q) r = hZ.superAmul p r + hZ.superAmul q r
      rw [map_add]; rfl
    zero_mul := fun p => by
      change hZ.superAmul 0 p = 0
      rw [map_zero]; rfl
    mul_zero := fun p => by
      change hZ.superAmul p 0 = 0
      rw [map_zero] }

/-- Under `AsRing`, the product is `superAmul`. -/
theorem AsRing_mul_eq (p q : V.superA hV) :
    (letI := hZ.AsRing; p * q) = hZ.superAmul p q := rfl

/-- **`A(V)` is a `ℂ`-algebra**: the `ℂ`-bilinearity of `∗` makes scalars central. -/
@[reducible] noncomputable def AsAlgebra : @Algebra ℂ (V.superA hV) _ hZ.AsRing.toSemiring :=
  letI := hZ.AsRing
  @Algebra.ofModule ℂ (V.superA hV) _ hZ.AsRing.toSemiring
    (inferInstance : Module ℂ (V.superA hV))
    (fun c p q => by
      change hZ.superAmul (c • p) q = c • hZ.superAmul p q
      rw [map_smul]; rfl)
    (fun c p q => by
      change hZ.superAmul p (c • q) = c • hZ.superAmul p q
      rw [map_smul])

end SuperZhuRingData

/-! ## §8  Bosonic coherence and non-vacuity

A `VertexOperatorAlgebra` read as a super one (`toSuper`, purely even, `ℤ`-weights) has integral
weights, and on it the super Zhu construction **is** the bosonic one — same product, same `O`,
same quotient.  Consequently `SuperZhuRingData` is discharged there by transport from the proved
`Modules.ZhuRingInstance.zhuRingData_holds`, so the hypothesis class is inhabited and nothing
above is vacuous. -/

namespace VertexOperatorAlgebra

variable (W : VertexOperatorAlgebra 𝒱)

/-- The Virasoro modes survive `toSuper` and `toSuperNearVOA`. -/
@[simp] theorem toSuperNearVOA_L (n : ℤ) : W.toSuper.toSuperNearVOA.L n = W.L n := rfl

/-- The `n`-th products survive `toSuper` and `toSuperNearVOA`. -/
@[simp] theorem toSuperNearVOA_smul (u : 𝒱) (n : ℤ) (v : 𝒱) :
    W.toSuper.toSuperNearVOA.smul u n v = W.smul u n v := rfl

/-- **A bosonic VOA has integral weights**, so the whole `superZhu` apparatus applies to it. -/
theorem toSuper_integralWeights : W.toSuper.toSuperNearVOA.IntegralWeights := fun _ hh =>
  W.toPreVertexAlgebra.gradingC_of_not_int hh

/-- Its transferred `ℤ`-grading is the original `ℤ`-grading. -/
theorem toSuperNearVOA_gradingZ (k : ℤ) :
    W.toSuper.toSuperNearVOA.gradingZ k = W.grading k :=
  W.toPreVertexAlgebra.gradingC_intCast k

/-- **The super Zhu product of a bosonic algebra is Zhu's product.**  Both sides are `ℂ`-linear
in the left factor and agree on every weight space, where each collapses to the same finite sum. -/
theorem superZhuMul_toSuper (u v : 𝒱) :
    W.toSuper.toSuperNearVOA.superZhuMul W.toSuper_integralWeights u v = zhuMul W u v := by
  have key : ∀ w : 𝒱,
      (W.toSuper.toSuperNearVOA.superZhuMulₗ W.toSuper_integralWeights).flip w
        = (zhuMulₗ W).flip w := by
    intro w
    refine W.toSuper.toSuperNearVOA.eq_of_eq_on_gradingZ W.toSuper_integralWeights
      (fun k x hx => ?_)
    have hx' : x ∈ W.grading k := by rwa [W.toSuperNearVOA_gradingZ k] at hx
    change W.toSuper.toSuperNearVOA.superZhuMul W.toSuper_integralWeights x w = zhuMul W x w
    rw [W.toSuper.toSuperNearVOA.superZhuMul_homogeneous W.toSuper_integralWeights hx w,
      zhuMul_homogeneous W hx' w]
    rfl
  exact congrArg (fun f => f u) (key v)

/-- **`O(V)` of the super construction is Zhu's `O(V)`.** -/
theorem superO_toSuper :
    W.toSuper.toSuperNearVOA.superO W.toSuper_integralWeights = O W := by
  have hset : {x : 𝒱 | ∃ u v : 𝒱, x = W.toSuper.toSuperNearVOA.superZhuMul
        W.toSuper_integralWeights (W.toSuper.toSuperNearVOA.L (-1) u
          + W.toSuper.toSuperNearVOA.L 0 u) v}
      = {x : 𝒱 | ∃ u v : 𝒱, x = zhuMul W (W.L (-1) u + W.L 0 u) v} := by
    ext x
    simp only [Set.mem_setOf_eq, toSuperNearVOA_L, superZhuMul_toSuper]
  rw [SuperNearVOA.superO, VOA.O, hset]

/-- The two quotients are the same `ℂ`-module. -/
noncomputable def superA_linearEquiv_A :
    W.toSuper.toSuperNearVOA.superA W.toSuper_integralWeights ≃ₗ[ℂ] A W :=
  Submodule.quotEquivOfEq _ _ W.superO_toSuper

/-- **`SuperZhuRingData` is inhabited**: on a bosonic algebra it is Dong–Zhao Thm 3.1 read
through `toSuper`, and there it *is* Zhu Thm 2.1.1–2.1.2, already proved in this library
(`Modules.ZhuRingInstance.zhuRingData_holds`).  So the definitions above are not vacuous, and the
`Ring`/`Algebra` consumers have at least one genuine instance. -/
theorem superZhuRingData_toSuper :
    SuperZhuRingData W.toSuper.toSuperNearVOA W.toSuper_integralWeights where
  left_ideal := by
    intro u hu v
    rw [W.superO_toSuper] at hu ⊢
    rw [W.superZhuMul_toSuper]
    exact (zhuRingData_holds W).left_ideal hu v
  right_ideal := by
    intro u v hv
    rw [W.superO_toSuper] at hv ⊢
    rw [W.superZhuMul_toSuper]
    exact (zhuRingData_holds W).right_ideal u hv
  assoc := by
    intro u v w
    rw [W.superO_toSuper]
    rw [W.superZhuMul_toSuper, W.superZhuMul_toSuper, W.superZhuMul_toSuper,
      W.superZhuMul_toSuper]
    exact (zhuRingData_holds W).assoc u v w

end VertexOperatorAlgebra

/-! ## §9  The application: the `χ` generators inside `A(SF)`

Symplectic fermions are the reason the super Zhu algebra was wanted, and they are the sanity
check on the definition: `χ^±` have conformal weight `1` **and** are odd, so spin–statistics fails
and the Kac–Wang recipe is inapplicable (see the module docstring).  Under the Dong–Zhao
definition used here, `χ^±` survive into `A(V)` — and they satisfy the exterior-algebra relations
of `Λ(χ⁺, χ⁻)`.

⚠ Scope.  What is proved is that the relations hold; **not** that `[χ^a] ≠ 0`, which needs `O(V)`
computed, and **not** that `A(V)` fails to be semisimple.  On the latter, note that "contains a
nonzero nilpotent" does *not* imply "not semisimple" — `M₂(ℂ)` is semisimple and full of
nilpotents.  The correct obstruction is a nonzero nilpotent *ideal* (equivalently a nonzero
Jacobson radical), which is what `Λ(χ⁺, χ⁻)` supplies once `[χ^a] ≠ 0` is known. -/

namespace SympFerm

open VOA.SympFerm

/-- **Symplectic fermions have integral weights** — the gate every definition above passes
through.  Both parities carry integer weights (`Examples.SymplecticFermionGrading`), which is
exactly the configuration Kac–Wang's axioms exclude and Dong–Zhao's admit. -/
theorem sympFerm_integralWeights : sympFermSVOA.toSuperNearVOA.IntegralWeights :=
  fun _ hh => gradingSF_eq_bot_of_not_intCast hh

/-- The weight-one odd state `χᵃ = χᵃ₋₁|0⟩`, as the one-letter word `[(0,a)]`. -/
noncomputable def chiStateSF (a : Fin 2) : FockSF := stWordSF [((0 : ℕ), a)]

/-- `χᵃ` has conformal weight `1`. -/
theorem chiStateSF_mem_gradingZ_one (a : Fin 2) :
    chiStateSF a ∈ sympFermSVOA.toSuperNearVOA.gradingZ 1 := by
  have h := stWordSF_mem_gradingSF [((0 : ℕ), a)]
  rw [show ((sfWeight [((0 : ℕ), a)] : ℕ) : ℂ) = ((1 : ℤ) : ℂ) from by
    rw [show sfWeight [((0 : ℕ), a)] = 1 from rfl]; norm_num] at h
  exact h

/-- ⚠ `χᵃ` is **odd** and of **integer** weight: spin–statistics fails, which is precisely why
the Kac–Wang formula (which reads parity off the weight) cannot be used. -/
theorem chiStateSF_mem_parity_one (a : Fin 2) : chiStateSF a ∈ sympFermSVOA.parity 1 := by
  have h := stWordSF_mem_evenOdd [((0 : ℕ), a)]
  rw [show ((([((0 : ℕ), a)] : SFWord).length : ℕ) : ZMod 2) = 1 from by norm_num] at h
  exact h

/-- The vertex operator of `χᵃ` is the generator field `χᵃ(z)`. -/
theorem YSF_chiStateSF (a : Fin 2) : YSF (chiStateSF a) = chi a := by
  rw [chiStateSF, YSF_word, YwordSF_singleton, sfGenField_zero_eq]

/-- Hence the modes of `χᵃ` are the honest modes `χᵃ_n`. -/
theorem smul_chiStateSF (a : Fin 2) (n : ℤ) (v : FockSF) :
    sympFermSVOA.toSuperNearVOA.smul (chiStateSF a) n v = chiM a n v := by
  change mode (YSF (chiStateSF a)) n v = _
  rw [YSF_chiStateSF]
  rfl

/-- `χᵃ = χᵃ₋₁|0⟩` in mode notation. -/
theorem chiM_neg_one_vacSF (a : Fin 2) : chiM a (-1) vacSF = chiStateSF a := by
  have h := YwordSF_vacuum_base [((0 : ℕ), a)]
  rw [YwordSF_singleton, sfGenField_zero_eq] at h
  rw [chiM_def, show (-(-1 : ℤ) - 1) = 0 from by ring]
  exact h

/-- **The Zhu product of two `χ`'s is the normally ordered product.**  The weight is `1`, so
`χᵃ ∗ v = χᵃ₍₋₁₎v + χᵃ₍₀₎v`, and the zero mode `χᵃ_0` vanishes on `FockSF`
(`SympFerm.VirB.chiM_zero_mode`, the CAR's factor of the mode number). -/
theorem superZhuMul_chiStateSF (a b : Fin 2) :
    sympFermSVOA.toSuperNearVOA.superZhuMul sympFerm_integralWeights
        (chiStateSF a) (chiStateSF b)
      = chiM a (-1) (chiStateSF b) := by
  rw [sympFermSVOA.toSuperNearVOA.superZhuMul_gradingZ_one sympFerm_integralWeights
      (chiStateSF_mem_gradingZ_one a),
    smul_chiStateSF, smul_chiStateSF,
    show (chiM a 0 : Module.End ℂ FockSF) = 0 from VirB.chiM_zero_mode a]
  simp

/-- Creation in word form: `χᵃ₋₁` prepends a letter. -/
theorem chiM_neg_one_stWordSF (a : Fin 2) (l : SFWord) :
    chiM a (-1) (stWordSF l) = stWordSF (((0 : ℕ), a) :: l) := by
  rw [chiM_def, show (-(-1 : ℤ) - 1) = 0 from by ring, chi, if_pos (le_refl (0 : ℤ)),
    show ((0 : ℤ).toNat) = 0 from rfl, creSF, creBase, stWordSF_cons]
  rfl

/-- **`χ⁰ ∗ χ¹ = −ω`.**  The Zhu product of the two symplectic fermions is (minus) the
conformal vector — `ωSF = −χ⁰₋₁χ¹₋₁|0⟩` by definition.  So the product is a completely explicit
element of `𝒱`, and by Dong–Zhao Thm 3.1 its class `[ω]` is central in `A(V)`. -/
theorem superZhuMul_chiStateSF_zero_one :
    sympFermSVOA.toSuperNearVOA.superZhuMul sympFerm_integralWeights
      (chiStateSF 0) (chiStateSF 1) = -ωSF := by
  rw [superZhuMul_chiStateSF, chiStateSF, chiM_neg_one_stWordSF, ωSF, neg_neg]

/-- **The `χ`'s anticommute for the Zhu product**: `χᵃ ∗ χᵇ + χᵇ ∗ χᵃ = 0`, already at the
level of `𝒱` (so a fortiori in `A(V)`).  The CAR coefficient `carC a b (−1) (−1)` vanishes
because the mode numbers do not add to `0`. -/
theorem superZhuMul_chiStateSF_add_comm (a b : Fin 2) :
    sympFermSVOA.toSuperNearVOA.superZhuMul sympFerm_integralWeights
        (chiStateSF a) (chiStateSF b)
      + sympFermSVOA.toSuperNearVOA.superZhuMul sympFerm_integralWeights
        (chiStateSF b) (chiStateSF a) = 0 := by
  rw [superZhuMul_chiStateSF, superZhuMul_chiStateSF, ← chiM_neg_one_vacSF,
    ← chiM_neg_one_vacSF]
  have h := chiM_anticomm_apply a b (-1) (-1) vacSF
  rwa [show carC a b (-1) (-1) = 0 from by
    rw [carC_apply, if_neg (by omega : ¬ ((-1 : ℤ) + (-1) = 0))], zero_smul] at h

/-- And so `χ¹ ∗ χ⁰ = ω`, by the anticommutation relation. -/
theorem superZhuMul_chiStateSF_one_zero :
    sympFermSVOA.toSuperNearVOA.superZhuMul sympFerm_integralWeights
      (chiStateSF 1) (chiStateSF 0) = ωSF := by
  have h := superZhuMul_chiStateSF_add_comm 0 1
  rw [superZhuMul_chiStateSF_zero_one] at h
  linear_combination (norm := module) h

/-- **Each `χᵃ` squares to zero for the Zhu product**, again already in `𝒱`.  Together with
`superZhuMul_chiStateSF_add_comm` these are exactly the defining relations of the exterior
algebra `Λ(χ⁺, χ⁻)`. -/
theorem superZhuMul_chiStateSF_self (a : Fin 2) :
    sympFermSVOA.toSuperNearVOA.superZhuMul sympFerm_integralWeights
      (chiStateSF a) (chiStateSF a) = 0 := by
  have h := superZhuMul_chiStateSF_add_comm a a
  have h2 : (2 : ℂ) • (sympFermSVOA.toSuperNearVOA.superZhuMul sympFerm_integralWeights
      (chiStateSF a) (chiStateSF a)) = 0 := by rw [two_smul]; exact h
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by norm_num)
  · exact h3

/-- The relations, pushed to `A(V)`: `[χᵃ ∗ χᵇ] + [χᵇ ∗ χᵃ] = 0` and `[χᵃ ∗ χᵃ] = 0`. -/
theorem superMk_superZhuMul_chiStateSF_self (a : Fin 2) :
    sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights
      (sympFermSVOA.toSuperNearVOA.superZhuMul sympFerm_integralWeights
        (chiStateSF a) (chiStateSF a)) = 0 := by
  rw [superZhuMul_chiStateSF_self, map_zero]

/-- **In the ring `A(SF)`, `[χᵃ]² = 0`** — conditional on `SuperZhuRingData`, i.e. on
Dong–Zhao Thm 3.1 for symplectic fermions, which is not proved in this repository (it is blocked
on the missing super Borcherds identity).  The *relation* itself is unconditional; only the ring
structure carrying it is hypothetical. -/
theorem chiStateSF_sq_eq_zero
    (hZ : SuperZhuRingData sympFermSVOA.toSuperNearVOA sympFerm_integralWeights)
    (a : Fin 2) :
    letI := hZ.AsRing
    (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF a))
      * (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF a))
      = 0 := by
  letI := hZ.AsRing
  rw [hZ.AsRing_mul_eq, hZ.superAmul_mk, superZhuMul_chiStateSF_self, map_zero]

/-- **In the ring `A(SF)`, `[χᵃ][χᵇ] + [χᵇ][χᵃ] = 0`** — same conditionality. -/
theorem chiStateSF_anticomm
    (hZ : SuperZhuRingData sympFermSVOA.toSuperNearVOA sympFerm_integralWeights)
    (a b : Fin 2) :
    letI := hZ.AsRing
    (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF a))
        * (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF b))
      + (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF b))
        * (sympFermSVOA.toSuperNearVOA.superMk sympFerm_integralWeights (chiStateSF a))
      = 0 := by
  letI := hZ.AsRing
  rw [hZ.AsRing_mul_eq, hZ.AsRing_mul_eq, hZ.superAmul_mk, hZ.superAmul_mk, ← map_add,
    superZhuMul_chiStateSF_add_comm, map_zero]

end SympFerm

end VOA


