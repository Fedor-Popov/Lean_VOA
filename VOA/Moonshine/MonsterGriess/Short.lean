/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean
v4.35.0-rc3 with the module system), files:
  CFSG/Monster/SpinLattice/Cocode.lean
  CFSG/Monster/Griess/Short.lean
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
import VOA.Moonshine.MonsterGriess.Lattice
import VOA.Moonshine.MonsterGriess.Spin
import Mathlib.Order.PiLex

/-!
# Axiom's Monster port, part 4: short coordinates `ShortIdx` and the vectors `uvec`

Fourth layer of the definitional closure of Axiom Math's `CFSG.Monster.Griess.AutO`:

* `phi0 : C × Cocode → Λ/2Λ`, `phi0 (a, δ) = lamT a + lamCocode δ` (the source proves it is a linear
  isomorphism `phi0Equiv`; not ported);
* `IsShortCoord p` — `phi0 p` is the class of a minimal Leech vector — and
  `ShortIdx = {p : C × Cocode // IsShortCoord p}`, the index set of `SpaceX` (98280 elements in the
  source, `card_shortIdx`; not ported);
* `uvec c` — the lexicographically smaller of the two minimal vectors `±u` in the class `phi0 c`
  (determined uniquely by the source's `eq_uvec`).

## Port notes
* Namespaces `CFSG.Monster.SpinLattice`, `CFSG.Monster.Griess` ↦ `….SpinLattice`,
  `VOA.Moonshine.MonsterGriess`.  Module-system syntax and the source's
  `attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent …` (instances of Axiom's own
  library, absent here) dropped.
* **`phi0` is the underlying function of the source's bundled linear map** (see its docstring).
  Every use of `phi0` in the closure is through its values, so `IsShortCoord`, `ShortIdx`, `uvec`
  are the same objects as in the source.
* Omitted: `IsShort`, `coordOf`, `centralCoord`, `rep` (they go through the extraspecial group `Q`,
  needed for `Xlift`, not for `AutO`), `card_shortIdx`, `uvec_spec`, `eq_uvec`.
-/

namespace VOA.Moonshine.MonsterGriess.SpinLattice

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code
  VOA.Moonshine.MonsterGriess.Spin

/-! ### From `CFSG/Monster/SpinLattice/Cocode.lean` -/
noncomputable def lamCocode : Cocode →ₗ[ZMod 2] L2 := C.liftQ lamVecLin le_ker_lamVecLin

theorem lamCocode_mk (x : Fin 24 → ZMod 2) : lamCocode (Submodule.Quotient.mk x) = lamVec x := rfl

def lamX (a : C) : L2 := lamCodeCls a.2

noncomputable def lamT (a : C) : L2 := lamX a + lamCocode (thetaD a)

/-- **Port adaptation.**  In the source, `phi0` is the bundled `ZMod 2`-linear map
`(AddMonoidHom.toZModLinearMap 2 lamTHom).coprod lamCocode : C × Cocode →ₗ[ZMod 2] L2`, whose
bundling needs additivity of `lamT` (`lamT_add`, resting on the theta-cocycle identities
`thetaD_add`, `θ_add_left`, `lamCodeCls_add`).  Only the values of `phi0` enter `IsShortCoord`
and hence `ShortIdx`, so we port the underlying function.  `phi0_apply` below is `rfl` exactly as
in the source (`CFSG/Monster/SpinLattice/Cocode.lean`, `phi0_apply`). -/
noncomputable def phi0 (p : C × Cocode) : L2 := lamT p.1 + lamCocode p.2

theorem phi0_apply (a : C) (δ : Cocode) : phi0 (a, δ) = lamT a + lamCocode δ := rfl

end VOA.Moonshine.MonsterGriess.SpinLattice

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
  VOA.Moonshine.MonsterGriess.SpinLattice

/-! ### From `CFSG/Monster/Griess/Short.lean` -/
def IsShortCoord (p : C × Cocode) : Prop := ∃ u ∈ minVecs, classOf u = phi0 p

abbrev ShortIdx : Type := {p : C × Cocode // IsShortCoord p}

noncomputable instance : Fintype ShortIdx := Fintype.ofFinite _

noncomputable instance : DecidableEq ShortIdx := Classical.decEq _

def LexLE (u v : Fin 24 → ℤ) : Prop := toLex u ≤ toLex v

noncomputable def uvec (c : ShortIdx) : Fin 24 → ℤ :=
  open Classical in
  if LexLE c.2.choose (-c.2.choose) then c.2.choose else -c.2.choose

end VOA.Moonshine.MonsterGriess
