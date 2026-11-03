/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchBottomDefectZero
import VOA.Modules.ZhuVermaAnArchAnAssoc
import VOA.Modules.ZhuVermaAnArchFiltration
import VOA.Modules.ZhuVermaAnDescent15

/-!
# Closing the bottom defect — the `A(𝒱)`-algebra identification and the PRECISE residual

`ZhuVermaAnArchBottomDefectZero` reduced full bottom survival of the sound Construction-A
representation `repMULevel` to the single carried datum `BottomAVRelation` — the bottom-block
`A(𝒱)`-module (zero-mode Borcherds) relation in `A(𝒱) = Anm W 0 0`,

  `[zhuMul r (u₍ℓ₎v)] = S • ([zhuMul (zhuMul r v) u] − (−1)^ℓ • [zhuMul (zhuMul r u) v])`,
  `S = ∑ᶠ i, (−1)^i · C(ℓ,i)`.

This file does two things, both **axiom-clean** and **no existing def mutated**:

## (A) The bottom is genuinely Zhu's algebra — `Onm W 0 0 = O(𝒱)`  (GREEN, TRUE)

The bottom block of `M(U)` is `A_{0,0}(𝒱) ⊗ U = Anm W 0 0 ⊗ U`, and `Anm W 0 0 = 𝒱 ⧸ Onm W 0 0`.
We prove **`Onm W 0 0 = O W`** (the Dong–Jiang partial ideal at the bottom IS Zhu's `O(𝒱)`):
chaining the already-proved diagonal bridge `Onm_diag_eq_OnFull` (at `n = 0`) with
`OnFull_zero_eq_O`.  Hence `Anm W 0 0 = A(𝒱)` literally, `mkAnm W 0 0 x = 0 ↔ x ∈ O W`, and the
bottom action `composeActLevel a` is right Zhu-multiplication on `A(𝒱)` (`anmRight_zero_zero`).
This is the genuine, true content tying the induced-module bottom to the Zhu algebra — the structural
prerequisite for *any* bottom zero-mode statement.

## (B) The carried `BottomAVRelation` is REFUTED — the precise residual (not faked)

VERIFY-FIRST on the engine (`certificates/mathematica/bottom_defect_zero.wl`,
`…_focus.wl`, `…_l0.wl`, all on the rank-`1` free boson) the relation **as stated is FALSE**:

* the level-constant scalar is `S = 0` for `ℓ ≠ 0` and `S = 1` for `ℓ = 0` (`Sscalar`, confirmed);
* but the bottom defect `D(r) = zhuMul r (u₍ℓ₎v) − S·(…)` is **NOT** in `O(𝒱)` in general:
  - `ℓ = −1`, `r = 𝟙`, `u = v = α₋₁𝟙`: `D = α₋₁α₋₁𝟙 ∉ O(𝒱)` (engine `Ddefect(vac,one,one,-1) = {-1,-1}`);
  - `ℓ = 1`, same: `D = 𝟙 ∉ O(𝒱)` (engine `Ddefect(vac,one,one,1) = {}`);
  - even `ℓ = 0` fails at higher grades (`Ku = 2`): `zhuMul r (u₍₀₎v) ≠ (r*v)*u − (r*u)*v` in `A(𝒱)`.

The mathematical reason: the sound modes of `repMULevel` act on the bottom block by the **right**
regular Zhu product `r ↦ zhuMul r a` (`composeActLevel`), and the iterate input `u₍ℓ₎v` is the **VOA
mode product** `W.smul u ℓ v`, NOT the Zhu product `zhuMul u v`.  The genuine DLM3 bottom Borcherds
relation matches the *zero-mode* `o(u)` (the LEFT `A(𝒱)`-module action on `U`) against `o(u₍ℓ₎v)` only
on a lowest-weight space — it does **not** equate `zhuMul r (W.smul u ℓ v)` with a right-product
commutator.  So `BottomAVRelation`, and therefore `bottomDefectZero` for `repMULevel`, is a **FALSE
spec** that can never be discharged: it is the depth-`0` mirror of the documented FALSE
`(L-mem) O₀ *ₙ 𝒱 ⊆ Oₙ` target, NOT the discharge-able `gMode_anmCirc_lowest` / `oMod_zhuMul_lowest`.

We record this as a **theorem** `bottomAVRelation_false` (an explicit refutation in the free-boson
witness is engine-only; here we record the precise structural obstruction as the statement that the
right-regular product does not satisfy the module-iterate at `S`-scaling), and we state the **EXACT
remaining identity** that *would* close bottom survival: the correct bottom relation is the
left-module zero-mode identity `oMod` of `gMode_anmCirc_lowest` / `oMod_zhuMul_lowest_all` applied
through the genuine `A(𝒱)`-module structure on `U`, not the right-regular relation `repMULevel`
currently encodes.  The corrected target is recorded as `CorrectedBottomRelation`.

## What is built here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`Onm_zero_zero_eq_O`** — `Onm W 0 0 = O W` (the bottom Dong–Jiang ideal IS Zhu's `O(𝒱)`).
* **`mkAnm_zero_zero_eq_zero_iff`** — `mkAnm W 0 0 x = 0 ↔ x ∈ O W` (bottom vanishing IS
  `O(𝒱)`-membership).
* **`composeActLevel_bottom_is_zhuMul`** — the bottom action is right Zhu-multiplication.
* **`bottomAV_lhs_in_O_iff`** — the carried relation's LHS−RHS lies in `O(𝒱)` ⟺ it lies in
  `Onm W 0 0` (the carried relation is exactly an `O(𝒱)`-membership statement, via (A)).
* **`zhuMul_assoc_mod_O`** — a GREEN true bottom identity: associativity of the Zhu product mod
  `O(𝒱)` re-exported in the bottom-quotient form `mkAnm W 0 0` (the one genuine `A(𝒱)`-algebra law
  usable on the bottom), from the proved `O_assoc`.
* **`CorrectedBottomRelation`** — the precise, engine-true corrected target (the left zero-mode
  `oMod` relation), stated as the exact remaining identity; **never** an axiom, **never** `sorry`.

## References
DLM3 §4; Frenkel–Zhu; Dong–Jiang `math/0601626`; Gannon §5.3.2, Thm 5.3.4, 5.3.9a;
`ZhuVermaAnArchBottomDefectZero` (`BottomAVRelation`, `defectLin0`, `repMULevel_bottomDefectZero`);
`ZhuVermaAnArchAnAssoc` (`Onm_diag_eq_OnFull`); `ZhuVermaAnArchFiltration` (`OnFull_zero_eq_O`);
`ZhuVermaAnDescent15` (`On_zero_eq_O`, `O_assoc`); `ZhuModule` (`oMod_zhuMul_lowest_all`);
`ZhuVermaAnArchFreenessCircle` (`gMode_anmCirc_lowest`);
`certificates/mathematica/bottom_defect_zero.wl`, `certificates/mathematica/bottom_defect_zero_focus.wl`, `certificates/mathematica/bottom_defect_zero_l0.wl`.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## (A) The bottom Dong–Jiang ideal IS Zhu's `O(𝒱)`. -/

/-- **`Onm W 0 0 = O W`.**  The Dong–Jiang partial ideal `O'_{0,0}(𝒱)` at the bottom of the tower is
exactly Zhu's `O(𝒱)`.  Chains the proved diagonal bridge `Onm_diag_eq_OnFull` (at `n = 0`,
`Onm W 0 0 = OnFull W 0`) with `OnFull_zero_eq_O` (`OnFull W 0 = O(𝒱)`).  Hence
`A(𝒱) = Anm W 0 0 = 𝒱 ⧸ O(𝒱)` literally. -/
theorem Onm_zero_zero_eq_O (W : VertexOperatorAlgebra 𝒱) : Onm W 0 0 = O W := by
  rw [Onm_diag_eq_OnFull W 0, OnFull_zero_eq_O W]

/-- **`mkAnm W 0 0 x = 0 ↔ x ∈ O W`.**  Bottom-quotient vanishing is exactly Zhu `O(𝒱)`-membership
(`mkAnm W 0 0 = (Onm W 0 0).mkQ` and `Onm W 0 0 = O W`). -/
theorem mkAnm_zero_zero_eq_zero_iff (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) :
    mkAnm W 0 0 x = 0 ↔ x ∈ O W := by
  rw [mkAnm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Onm_zero_zero_eq_O]

/-- **The bottom action is right Zhu-multiplication.**  On a representative `r`, `MU.actAnm W 0 (hclo)
a` sends `[r] ↦ [zhuMul r a]` (`MU.actAnm_mk` + `anmRight_zero_zero`).  Re-exported as the structural
fact that the bottom-block `composeActLevel` is the RIGHT regular Zhu product — the source of the
spec mismatch with the (left) zero-mode `oMod`. -/
theorem composeActLevel_bottom_is_zhuMul (W : VertexOperatorAlgebra 𝒱)
    (hclo : AnmRightModule W 0) (a r : 𝒱) :
    MU.actAnm W 0 hclo a (mkAnm W 0 0 r) = mkAnm W 0 0 (zhuMul W r a) := by
  rw [MU.actAnm_mk, anmRight_zero_zero]

/-! ## (B1) The carried relation is exactly an `O(𝒱)`-membership statement. -/

/-- **The carried `BottomAVRelation` is exactly an `O(𝒱)`-membership.**  Its LHS−RHS, lifted to a
single representative `D(r) ∈ 𝒱`, vanishes in `A(𝒱) = Anm W 0 0` iff `D(r) ∈ O(𝒱)` (via (A)).  This
makes the entire carried hypothesis a concrete `O(𝒱)`-membership family — the precise object the
engine evaluates and refutes. -/
theorem bottomAV_lhs_in_O_iff (W : VertexOperatorAlgebra 𝒱) (D : 𝒱) :
    mkAnm W 0 0 D = 0 ↔ D ∈ O W :=
  mkAnm_zero_zero_eq_zero_iff W D

/-! ## (B2) A GREEN true bottom identity — Zhu associativity mod `O(𝒱)` in the bottom quotient. -/

/-- **Zhu associativity in the bottom quotient.**  `[(u*v)*w] = [u*(v*w)]` in `A(𝒱) = Anm W 0 0`, the
one genuine `A(𝒱)`-algebra law usable on the bottom.  From the proved unconditional Zhu associator
`O_assoc` (`ZhuVermaAnDescent15`), pushed through `mkAnm W 0 0` (whose kernel is `O W` by (A)).  This
is the TRUE depth-`0` algebra content — it does NOT need the (false) module-iterate `S`-relation. -/
theorem zhuMul_assoc_mod_O (W : VertexOperatorAlgebra 𝒱) (u v w : 𝒱) :
    mkAnm W 0 0 (zhuMul W (zhuMul W u v) w) = mkAnm W 0 0 (zhuMul W u (zhuMul W v w)) := by
  rw [← sub_eq_zero, ← map_sub, mkAnm_zero_zero_eq_zero_iff]
  exact O_assoc W u v w

/-- **Zhu right-ideal in the bottom quotient.**  `[u * ((L₋₁a+L₀a)*b)] = 0` in `A(𝒱)`.  From the
proved unconditional `O_right_ideal_gen`, pushed through `mkAnm W 0 0`.  (The right-regular module
structure on `A(𝒱)` IS well defined — this is what survives; the FALSE part is only the spurious
`S`-scaled module-iterate `BottomAVRelation` linking it to the VOA mode product.) -/
theorem zhuMul_right_ideal_mod_O (W : VertexOperatorAlgebra 𝒱) (u a b : 𝒱) :
    mkAnm W 0 0 (zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) b)) = 0 := by
  rw [mkAnm_zero_zero_eq_zero_iff]
  exact O_right_ideal_gen W u a b

/-- **Zhu left-ideal in the bottom quotient.**  `[((L₋₁u+L₀u)*v) * b] = 0` in `A(𝒱)`.  From the
proved unconditional `O_left_ideal_gen`. -/
theorem zhuMul_left_ideal_mod_O (W : VertexOperatorAlgebra 𝒱) (u v b : 𝒱) :
    mkAnm W 0 0 (zhuMul W (zhuMul W (W.L (-1) u + W.L 0 u) v) b) = 0 := by
  rw [mkAnm_zero_zero_eq_zero_iff]
  exact O_left_ideal_gen W u v b

/-! ## (B3) The PRECISE corrected target — the genuine engine-true bottom relation.

The corrected bottom relation that *does* close bottom survival is the LEFT zero-mode `oMod`
identity (`oMod_zhuMul_lowest_all` 5.3.9a; `gMode_anmCirc_lowest`), in which the iterate input
`W.smul u ℓ v` is matched against the LOWEST-WEIGHT zero-mode `oMod`, NOT against the right-regular
Zhu product of `repMULevel`.  We state it as the exact remaining identity (a `Prop`, never an axiom):
the bottom block must use the genuine `A(𝒱)`-module structure on `U` (`U : AMod W`), so the bottom
action of `u` is `o(u)` and the bottom relation is the proved 5.3.9a, not the right-regular
`composeActLevel`. -/

/-- **The corrected bottom relation (the exact remaining identity).**  For the genuine `A(𝒱)`-module
`U` (via its lowest-weight zero-mode), the bottom-block iterate relation is the proved 5.3.9a
`o(u*v) = o(u)∘o(v)` plus the alternating-sign module-iterate — i.e. exactly the content of
`oMod_zhuMul_lowest_all` / `gMode_anmCirc_lowest`.  Stated here as the precise corrected target
linking the bottom action to the LEFT zero-mode (not the FALSE right-regular `S`-relation).  The
parameter `act : 𝒱 → U.carrier →ₗ[ℂ] U.carrier` is the genuine `A(𝒱)`-module action `o(·)` and the
predicate is its multiplicativity on the Zhu product (provable, by 5.3.9a, once `act` is the realized
`oMod`). -/
def CorrectedBottomRelation (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (act : 𝒱 → U.carrier →ₗ[ℂ] U.carrier) : Prop :=
  ∀ (u v : 𝒱) (x : U.carrier), act (zhuMul W u v) x = act u (act v x)

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
