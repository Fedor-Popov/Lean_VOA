/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean
v4.35.0-rc3 with the module system), files:
  CFSG/Monster/Spin/SignedPerm.lean
  CFSG/Monster/Spin/Coords.lean
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.SpinMatrixLaws

/-!
# Axiom's Monster port: the spin matrices under a change of coefficient ring

The signed permutation matrices `spm R σ ε` and the spin matrices `qmatR R s a δ` have entries in
`{0, 1, −1}`, so every ring homomorphism `f : R →+* S` carries them to the same matrices over `S`:

* `map_sgnR` — `f (sgnR R t) = sgnR S t`;
* `map_spm` — `(spm R σ ε).map f = spm S σ ε`;
* `map_qmatR` — `(qmatR R s a δ).map f = qmatR S s a δ`.

This is what reads Axiom's rational `Rmat c = qmatR ℚ 0 c.1.1 c.1.2` as a complex matrix.

## Port notes
* Namespace `CFSG.Monster.Spin` ↦ `VOA.Moonshine.MonsterGriess.Spin`; module-system syntax
  dropped; statements and proofs verbatim.  `sgnR`, `spm`, `qmatR` and `spm_apply` were already
  ported (`Spin.lean`, `SpinMatrixLaws.lean`) and are used, not repeated.
-/

namespace VOA.Moonshine.MonsterGriess.Spin

open Matrix

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

variable {R : Type*} [CommRing R]

/-! ### From `CFSG/Monster/Spin/SignedPerm.lean` -/

theorem map_sgnR {S : Type*} [CommRing S] (f : R →+* S) (t : ZMod 2) :
    f (sgnR R t) = sgnR S t := by
  rcases zmod2_cases t with rfl | rfl
  · simp
  · simp

theorem map_spm {ι : Type*} [DecidableEq ι] {S : Type*} [CommRing S] (f : R →+* S)
    (σ : ι → ι) (ε : ι → ZMod 2) : (spm R σ ε).map f = spm S σ ε := by
  ext i j
  simp only [Matrix.map_apply, spm_apply]
  split_ifs
  · exact map_sgnR f _
  · exact map_zero f

/-! ### From `CFSG/Monster/Spin/Coords.lean` -/

theorem map_qmatR {S : Type*} [CommRing S] (f : R →+* S) (s : ZMod 2) (a : Code.C)
    (δ : Cocode) : (qmatR R s a δ).map f = qmatR S s a δ :=
  map_spm f _ _

end VOA.Moonshine.MonsterGriess.Spin
