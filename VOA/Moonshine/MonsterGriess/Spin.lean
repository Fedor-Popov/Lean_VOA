/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean
v4.35.0-rc3 with the module system), files:
  CFSG/Monster/Lagrangian.lean
  CFSG/Monster/Spin/Pairing.lean
  CFSG/Monster/Spin/SignedPerm.lean
  CFSG/Monster/Spin/Defs.lean
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
import VOA.Moonshine.MonsterGriess.Golay
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Axiom's Monster port, part 3: the cocode, the pairing, and the 4096-dimensional spin module

Third layer of the definitional closure of Axiom Math's `CFSG.Monster.Griess.AutO`:

* `sgn : ZMod 2 → ℚ` (`0 ↦ 1`, `1 ↦ -1`);
* `Cocode = (Fin 24 → ZMod 2) ⧸ C`, the pairing `pair : C → Cocode →ₗ ZMod 2` (well defined by
  self-orthogonality `dotProduct_eq_zero`), the cocycle class `thetaD a : Cocode`;
* `μ₀ : C → ZMod 2` (first `ψ`-coordinate, `μ₀ Ω = 1`), `C₀ = ker μ₀` (2048 words),
  `π₀ : C → C₀`, `shift a c = π₀ (c + a)`;
* `SpinIdx = ZMod 2 × C₀` (4096 elements) and the signed permutation matrices
  `qmatR R s a δ = spm R (qPerm a δ) (qSign s a δ)` on it, which give the `Rmat` of the product.

## Port notes
* Namespaces `CFSG.Monster`, `CFSG.Monster.Spin` ↦ `VOA.Moonshine.MonsterGriess`, `….Spin`.
* Module-system syntax dropped.  The source's `public noncomputable section` of
  `Spin/Defs.lean` and `Spin/Coords.lean` becomes the named `noncomputable section SpinMatrices`;
  the `variable (R …)` blocks of `Spin/SignedPerm.lean` sit in `section SignedPerm`.
* Omitted: the `Parker`/`Xmat`/`Dmat`/`Q` extraspecial-group layer, the cardinality lemmas, and all
  algebraic identities of `qmatR`/`spm` (none is needed to state `AutO`).
-/

namespace VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/Lagrangian.lean` -/
def sgn (t : ZMod 2) : ℚ := if t = 0 then 1 else -1

end VOA.Moonshine.MonsterGriess

namespace VOA.Moonshine.MonsterGriess.Spin

open VOA.Moonshine.MonsterGriess.Code

/-! ### From `CFSG/Monster/Spin/Pairing.lean` -/
private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

def ΩC : C := ⟨Ω, Ω_mem_C⟩

@[simp] theorem coe_ΩC : (ΩC : Fin 24 → ZMod 2) = Ω := rfl

def μ₀ : C →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj 0 ∘ₗ ψ) ∘ₗ C.subtype

@[simp] theorem μ₀_ΩC : μ₀ ΩC = 1 := by decide

def C₀ : Submodule (ZMod 2) C := LinearMap.ker μ₀

theorem mem_C₀ {d : C} : d ∈ C₀ ↔ μ₀ d = 0 := LinearMap.mem_ker

instance : DecidablePred (· ∈ C₀) := fun _ => decidable_of_iff _ mem_C₀.symm

@[simp] theorem μ₀_coe (c : C₀) : μ₀ (c : C) = 0 := mem_C₀.1 c.2

def π₀ : C →ₗ[ZMod 2] C₀ :=
  LinearMap.codRestrict C₀ (LinearMap.id + μ₀.smulRight ΩC) fun u => by
    rw [mem_C₀, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_add,
      map_smul, μ₀_ΩC, smul_eq_mul, mul_one, ← two_mul, two_eq_zero', zero_mul]

abbrev Cocode : Type := (Fin 24 → ZMod 2) ⧸ C

noncomputable instance : DecidableEq Cocode := Classical.decEq _

def dotL (a : Fin 24 → ZMod 2) : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := a ⬝ᵥ x
  map_add' x y := dotProduct_add a x y
  map_smul' c x := by rw [dotProduct_smul, RingHom.id_apply]

def pair (a : C) : Cocode →ₗ[ZMod 2] ZMod 2 :=
  C.liftQ (dotL a) fun _ hx => LinearMap.mem_ker.2 (dotProduct_eq_zero a.2 hx)

theorem pair_mk (a : C) (x : Fin 24 → ZMod 2) :
    pair a (Submodule.Quotient.mk x) = (a : Fin 24 → ZMod 2) ⬝ᵥ x := rfl

noncomputable def θL (a : C) : C →ₗ[ZMod 2] ZMod 2 where
  toFun := θ a
  map_add' := θ_add_right a
  map_smul' c e := by rw [θ_smul_right, smul_eq_mul, RingHom.id_apply]

theorem θL_apply (a u : C) : θL a u = θ a u := rfl

theorem exists_pair_eq (f : C →ₗ[ZMod 2] ZMod 2) : ∃ δ : Cocode, ∀ u : C, pair u δ = f u := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨Submodule.Quotient.mk fun i => g fun j => if i = j then 1 else 0, fun u => ?_⟩
  rw [pair_mk, ← hg, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.pi_apply_eq_sum_univ g (u : Fin 24 → ZMod 2)]
  simp only [dotProduct, smul_eq_mul]

noncomputable def thetaD (a : C) : Cocode := (exists_pair_eq (θL a)).choose

section SignedPerm

open Matrix

/-! ### From `CFSG/Monster/Spin/SignedPerm.lean` -/
variable (R : Type*) [CommRing R]

def sgnR (t : ZMod 2) : R := if t = 0 then 1 else -1

variable {R}

variable {ι : Type*} [DecidableEq ι]

variable (R) in
def spm (σ : ι → ι) (ε : ι → ZMod 2) : Matrix ι ι R :=
  Matrix.of fun i j => if j = σ i then sgnR R (ε i) else 0

end SignedPerm

noncomputable section SpinMatrices

open Matrix

/-! ### From `CFSG/Monster/Spin/Defs.lean` -/
abbrev SpinIdx : Type := ZMod 2 × C₀

def shift (a : C) (c : C₀) : C₀ := π₀ ((c : C) + a)

/-! ### From `CFSG/Monster/Spin/Coords.lean` -/
def qPerm (a : C) (δ : Cocode) (i : SpinIdx) : SpinIdx :=
  (i.1 + pair ΩC δ, shift a i.2)

def qSign (s : ZMod 2) (a : C) (δ : Cocode) (i : SpinIdx) : ZMod 2 :=
  s + i.1 * μ₀ a + pair (shift a i.2) δ

variable (R : Type*) [CommRing R]

def qmatR (s : ZMod 2) (a : C) (δ : Cocode) : Matrix SpinIdx SpinIdx R :=
  spm R (qPerm a δ) (qSign s a δ)

end SpinMatrices

end VOA.Moonshine.MonsterGriess.Spin
