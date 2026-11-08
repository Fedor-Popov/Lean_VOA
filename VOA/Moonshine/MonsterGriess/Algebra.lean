/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean
v4.35.0-rc3 with the module system), files:
  CFSG/Monster/Griess/Space.lean
  CFSG/Monster/Griess/Trilinear.lean
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
import VOA.Moonshine.MonsterGriess.Short
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Axiom's Monster port, part 5: the rational Griess algebra `SpaceB`, its form and product

Fifth layer of the definitional closure of Axiom Math's `CFSG.Monster.Griess.AutO`:

* `symMat` — symmetric `24 × 24` rational matrices (dimension 300);
* `SpaceX = ShortIdx → ℚ` (98280), `SpaceW = Matrix SpinIdx (Fin 24) ℚ` (4096 · 24 = 98304),
  `SpaceB = symMat × SpaceX × SpaceW` (196884);
* `bform u v = tr(A_u A_v) + ∑_c x_u(c) x_v(c) + ∑_{j,i} N_u(j,i) N_v(j,i)` — positive definite;
* the product `gmul = LinearMap.mk₂ ℚ gmulFun …` with components `gmulA`, `gmulX`,
  `gmulW = gmulWHalf u v + gmulWHalf v u`, built from `Umat c = u_c u_cᵀ` (`u_c = uvec c`, a
  minimal Leech vector in coordinates of norm 32), `Rmat c = qmatR ℚ 0 c.1.1 c.1.2` (a signed
  permutation matrix on `SpinIdx`), `qf c M = u_cᵀ M u_c`, and the structure constants
  `tau d e c = [c.1 = d.1 + e.1] · sgn (pair e.1.1 d.1.2)`.

## Port notes
* Namespace `CFSG.Monster.Griess` ↦ `VOA.Moonshine.MonsterGriess`.  Module-system syntax and the
  source's `attribute [-instance] …` line dropped.  All definitions verbatim except `gmul`.
* **`gmul`**: same `LinearMap.mk₂ ℚ gmulFun gmulFun_add_left gmulFun_smul_left _ _`, but the
  right-linearity fields are proved directly (`gmulFun_add_right`, `gmulFun_smul_right`) rather
  than through commutativity `gmulFun_comm` (whose proof needs `pair_eq_zero_of_isShortCoord`).
  Proof irrelevance makes the two terms equal; commutativity itself is *not* ported.
* Omitted: `PairIdx`, `basisA`, `basisB`, `gramDiag`, `tensor`, `Xlift`, `BR`, the trilinear form
  `T`/`Tex` and all identities (commutativity, invariance `bform_gmul_assoc`, the unit `oneB`).
-/

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin Matrix Module

/-! ### From `CFSG/Monster/Griess/Space.lean` -/
def symMat : Submodule ℚ (Matrix (Fin 24) (Fin 24) ℚ) where
  carrier := {A | Aᵀ = A}
  add_mem' {A B} hA hB := by
    change (A + B)ᵀ = A + B
    rw [transpose_add, hA, hB]
  zero_mem' := transpose_zero
  smul_mem' c A hA := by
    change (c • A)ᵀ = c • A
    rw [transpose_smul, hA]

theorem mem_symMat {A : Matrix (Fin 24) (Fin 24) ℚ} : A ∈ symMat ↔ Aᵀ = A := Iff.rfl

abbrev SpaceX : Type := ShortIdx → ℚ

abbrev SpaceW : Type := Matrix SpinIdx (Fin 24) ℚ

abbrev SpaceB : Type := symMat × SpaceX × SpaceW

noncomputable def bform : LinearMap.BilinForm ℚ SpaceB :=
  LinearMap.mk₂ ℚ (fun u v => trace ((u.1 : Matrix (Fin 24) (Fin 24) ℚ) *
      (v.1 : Matrix (Fin 24) (Fin 24) ℚ)) +
      ∑ c, u.2.1 c * v.2.1 c + ∑ j, ∑ i, u.2.2 j i * v.2.2 j i)
    (fun u u' v => by
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, trace_add,
        Pi.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      ring)
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Matrix.smul_mul, trace_smul,
        Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_assoc])
    (fun u v v' => by
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, trace_add,
        Pi.add_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
      ring)
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Matrix.mul_smul, trace_smul,
        Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_left_comm])

theorem bform_apply (u v : SpaceB) :
    bform u v = trace ((u.1 : Matrix (Fin 24) (Fin 24) ℚ) * (v.1 : Matrix (Fin 24) (Fin 24) ℚ)) +
      ∑ c, u.2.1 c * v.2.1 c + ∑ j, ∑ i, u.2.2 j i * v.2.2 j i := rfl

/-! ### From `CFSG/Monster/Griess/Trilinear.lean` -/
noncomputable def uQ (c : ShortIdx) : Fin 24 → ℚ := fun i => (uvec c i : ℚ)

noncomputable def Umat (c : ShortIdx) : Matrix (Fin 24) (Fin 24) ℚ := vecMulVec (uQ c) (uQ c)

noncomputable def Rmat (c : ShortIdx) : Matrix SpinIdx SpinIdx ℚ := qmatR ℚ 0 c.1.1 c.1.2

noncomputable def qf (c : ShortIdx) (M : Matrix (Fin 24) (Fin 24) ℚ) : ℚ :=
  uQ c ⬝ᵥ (M *ᵥ uQ c)

noncomputable def tau (d e c : ShortIdx) : ℚ :=
  open Classical in if c.1 = d.1 + e.1 then sgn (pair e.1.1 d.1.2) else 0

theorem Umat_symm (c : ShortIdx) : (Umat c)ᵀ = Umat c := by
  ext i j
  simp [Umat, vecMulVec_apply, mul_comm]

abbrev Am (u : SpaceB) : Matrix (Fin 24) (Fin 24) ℚ := (u.1 : Matrix (Fin 24) (Fin 24) ℚ)

abbrev xs (u : SpaceB) : SpaceX := u.2.1

abbrev Nm (u : SpaceB) : SpaceW := u.2.2

theorem Am_symm (u : SpaceB) : (Am u)ᵀ = Am u := u.1.2

noncomputable def gmulA (u v : SpaceB) : Matrix (Fin 24) (Fin 24) ℚ :=
  (2 : ℚ) • (Am u * Am v + Am v * Am u) + (8 : ℚ)⁻¹ • ∑ c, (xs u c * xs v c) • Umat c +
    (trace ((Nm u)ᵀ * Nm v) / 8) • (1 : Matrix (Fin 24) (Fin 24) ℚ) +
    (2 : ℚ)⁻¹ • ((Nm u)ᵀ * Nm v + (Nm v)ᵀ * Nm u)

theorem gmulA_symm (u v : SpaceB) : (gmulA u v)ᵀ = gmulA u v := by
  simp only [gmulA, transpose_add, transpose_smul, transpose_mul, Am_symm, transpose_sum,
    Umat_symm, transpose_one, transpose_transpose]
  rw [add_comm (Am v * Am u), add_comm ((Nm v)ᵀ * Nm u)]

noncomputable def gmulX (u v : SpaceB) (c : ShortIdx) : ℚ :=
  (xs v c * qf c (Am u) + xs u c * qf c (Am v)) / 8 +
    ∑ d, ∑ e, xs u d * xs v e * tau d e c +
    (trace ((Nm u)ᵀ * Rmat c * Nm v) - qf c ((Nm u)ᵀ * Rmat c * Nm v) / 4) / 8

noncomputable def gmulWHalf (u v : SpaceB) : SpaceW :=
  (trace (Am u) / 8) • Nm v + Nm v * Am u +
    (8 : ℚ)⁻¹ • ∑ c, xs u c • (Rmat c * Nm v - (4 : ℚ)⁻¹ • (Rmat c * Nm v * Umat c))

noncomputable def gmulW (u v : SpaceB) : SpaceW := gmulWHalf u v + gmulWHalf v u

noncomputable def gmulFun (u v : SpaceB) : SpaceB :=
  (⟨gmulA u v, gmulA_symm u v⟩, gmulX u v, gmulW u v)

theorem gmulWHalf_add_left (u u' v : SpaceB) :
    gmulWHalf (u + u') v = gmulWHalf u v + gmulWHalf u' v := by
  simp only [gmulWHalf, Am, xs, Nm, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply,
    trace_add, add_div, add_smul, Matrix.mul_add, Finset.sum_add_distrib, smul_add]
  abel

theorem gmulWHalf_add_right (u v v' : SpaceB) :
    gmulWHalf u (v + v') = gmulWHalf u v + gmulWHalf u v' := by
  simp only [gmulWHalf, Am, xs, Nm, Prod.snd_add, smul_add, Matrix.add_mul, Matrix.mul_add,
    add_sub_add_comm, Finset.sum_add_distrib]
  abel

theorem gmulFun_add_left (u u' v : SpaceB) :
    gmulFun (u + u') v = gmulFun u v + gmulFun u' v := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · change gmulA (u + u') v = gmulA u v + gmulA u' v
    simp only [gmulA, Am, xs, Nm, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply,
      Matrix.add_mul, Matrix.mul_add, transpose_add, trace_add, add_mul, add_smul, add_div,
      Finset.sum_add_distrib, smul_add]
    abel
  · funext c
    change gmulX (u + u') v c = gmulX u v c + gmulX u' v c
    simp only [gmulX, Am, xs, Nm, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply,
      Matrix.add_mul, transpose_add, trace_add, add_mul, mul_add,
      Finset.sum_add_distrib, add_mulVec, dotProduct_add, qf]
    ring
  · change gmulWHalf (u + u') v + gmulWHalf v (u + u') =
      gmulWHalf u v + gmulWHalf v u + (gmulWHalf u' v + gmulWHalf v u')
    rw [gmulWHalf_add_left, gmulWHalf_add_right, add_add_add_comm]

theorem gmulFun_zero_left (v : SpaceB) : gmulFun 0 v = 0 := by
  have h := gmulFun_add_left 0 0 v
  rw [add_zero] at h
  exact left_eq_add.1 h

noncomputable def gmulAdd (v : SpaceB) : SpaceB →+ SpaceB where
  toFun u := gmulFun u v
  map_zero' := gmulFun_zero_left v
  map_add' u u' := gmulFun_add_left u u' v

theorem gmulFun_smul_left (t : ℚ) (u v : SpaceB) : gmulFun (t • u) v = t • gmulFun u v :=
  map_rat_smul (gmulAdd v) t u

/-! #### Port adaptation: linearity in the second argument

The source obtains the last two fields of `LinearMap.mk₂` from commutativity `gmulFun_comm`,
whose proof needs `tau_comm` and `Rmat_symm`, i.e. `pair a δ = 0` for short `(a, δ)`
(`pair_eq_zero_of_isShortCoord`, resting on the quadratic form of `Λ/2Λ`).  We prove additivity
and homogeneity in the second argument directly from the formulas instead.  The function packaged
by `LinearMap.mk₂` is the same `gmulFun`; only the (proof-irrelevant) proofs differ, so `gmul` is
the same bilinear map as in the source. -/

theorem gmulFun_add_right (u v v' : SpaceB) :
    gmulFun u (v + v') = gmulFun u v + gmulFun u v' := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · change gmulA u (v + v') = gmulA u v + gmulA u v'
    simp only [gmulA, Am, xs, Nm, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply,
      Matrix.add_mul, Matrix.mul_add, transpose_add, trace_add, mul_add, add_smul, add_div,
      Finset.sum_add_distrib, smul_add]
    abel
  · funext c
    change gmulX u (v + v') c = gmulX u v c + gmulX u v' c
    simp only [gmulX, Am, xs, Nm, Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply,
      Matrix.mul_add, trace_add, add_mul, mul_add,
      Finset.sum_add_distrib, add_mulVec, dotProduct_add, qf]
    ring
  · change gmulWHalf u (v + v') + gmulWHalf (v + v') u =
      gmulWHalf u v + gmulWHalf v u + (gmulWHalf u v' + gmulWHalf v' u)
    rw [gmulWHalf_add_right, gmulWHalf_add_left, add_add_add_comm]

theorem gmulFun_zero_right (u : SpaceB) : gmulFun u 0 = 0 := by
  have h := gmulFun_add_right u 0 0
  rw [add_zero] at h
  exact left_eq_add.1 h

/-- `gmulFun u` as an additive map (port adaptation, mirrors the source's `gmulAdd`). -/
noncomputable def gmulAddRight (u : SpaceB) : SpaceB →+ SpaceB where
  toFun v := gmulFun u v
  map_zero' := gmulFun_zero_right u
  map_add' v v' := gmulFun_add_right u v v'

theorem gmulFun_smul_right (t : ℚ) (u v : SpaceB) : gmulFun u (t • v) = t • gmulFun u v :=
  map_rat_smul (gmulAddRight u) t v

/-- Axiom's Griess product on `SpaceB` (source: `CFSG/Monster/Griess/Trilinear.lean`, `gmul`).
Same underlying function `gmulFun`; the right-linearity proofs are the port's own (see above). -/
noncomputable def gmul : SpaceB →ₗ[ℚ] SpaceB →ₗ[ℚ] SpaceB :=
  LinearMap.mk₂ ℚ gmulFun gmulFun_add_left gmulFun_smul_left gmulFun_add_right
    gmulFun_smul_right

theorem gmul_apply (u v : SpaceB) : gmul u v = gmulFun u v := rfl

end VOA.Moonshine.MonsterGriess
