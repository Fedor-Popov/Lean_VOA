/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SkewIntertwiner
import VOA.Core.ReconstructionExistence

/-!
# M8d (generic part): block fields on a direct sum `V × M`

The moonshine vertex operator is written in block form on `V♮ = V_Λ^+ × TP` (DGM CMP 1996,
eq. (4.17)): `Y♮(u) = diag(Y(u), Y^T(u))` for untwisted states and `Y♮(t) = offdiag(W̄(t), W(t))`
for twisted states.  This file is the module-agnostic algebra of such block fields, for an
arbitrary pair of `ℂ`-modules `V`, `M`; it is what turns the four-block data into the
`End ℂ (V × M)`-valued notions (`IsField`, `Local`, `Reconstruction.DCovariant`) consumed by
`Reconstruction.reconstruct`.

## Main definitions and results

* `blockOp a c d b : End ℂ (V × M)` — the operator matrix `[[a, c], [d, b]]`, with
  `blockOp_mul` (matrix multiplication) and `blockOp_sub`.
* `blockF a c d b : FormalDist (End ℂ (V × M))` — the block field, coefficientwise `blockOp`.
* `mulBySubPow_blockF₂` — `(z₁−z₂)ᴺ` acts blockwise on two-variable block distributions.
* `isField_blockF` — a block field is a field when its four blocks are lower-truncated.
* `dCovariant_blockF` — `T`-covariance for `T = diag(T_V, T_M)` from the four block
  covariances.
* `local_diag_diag` — `diag(a,b)` and `diag(a',b')` are local if `a ~ a'` and `b ~ b'`.
* `local_diag_off` — `diag(a,b)` and `offdiag(c',d')` are local if
  `(z₁−z₂)ᴺ (a c' − c' b) = 0` and `(z₁−z₂)ᴺ (b d' − d' a) = 0` (two `Hom`-valued relations: the
  intertwining localities of `c'` and `d'`).
* `WeakModule.local_YM` — mutual locality of the fields of a weak module, from the module
  commutator formula (the `ℓ = 0` slice of the module Jacobi identity); `act_comm` is that
  commutator formula for all `m, n`.

## Status
`sorry`-free; no hypotheses beyond those displayed.  All statements are generic.
-/

namespace VOA.Moonshine.VnatBlock

open Module (End)
open SkewIntertwiner

universe u v w

section Block

variable {V : Type u} {M : Type v} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]

@[simp] theorem formalDist_zero_apply {X : Type*} [AddCommGroup X] (k : ℤ) :
    (0 : FormalDist X) k = 0 := rfl

/-- The block operator `[[a, c], [d, b]]` on `V × M`: `(x, y) ↦ (a x + c y, d x + b y)`. -/
def blockOp (a : End ℂ V) (c : M →ₗ[ℂ] V) (d : V →ₗ[ℂ] M) (b : End ℂ M) : End ℂ (V × M) :=
  (a.coprod c).prod (d.coprod b)

@[simp] theorem blockOp_apply (a : End ℂ V) (c : M →ₗ[ℂ] V) (d : V →ₗ[ℂ] M) (b : End ℂ M)
    (x : V × M) : blockOp a c d b x = (a x.1 + c x.2, d x.1 + b x.2) := rfl

theorem blockOp_ext_iff {X Y : End ℂ (V × M)} :
    X = Y ↔ ∀ x : V × M, (X x).1 = (Y x).1 ∧ (X x).2 = (Y x).2 :=
  ⟨fun h _ => h ▸ ⟨rfl, rfl⟩, fun h => LinearMap.ext fun x => Prod.ext (h x).1 (h x).2⟩

/-- Matrix multiplication of block operators. -/
theorem blockOp_mul (a : End ℂ V) (c : M →ₗ[ℂ] V) (d : V →ₗ[ℂ] M) (b : End ℂ M)
    (a' : End ℂ V) (c' : M →ₗ[ℂ] V) (d' : V →ₗ[ℂ] M) (b' : End ℂ M) :
    blockOp a c d b * blockOp a' c' d' b'
      = blockOp (a * a' + c ∘ₗ d') (a ∘ₗ c' + c ∘ₗ b') (d ∘ₗ a' + b ∘ₗ d')
          (d ∘ₗ c' + b * b') := by
  refine blockOp_ext_iff.2 fun x => ⟨?_, ?_⟩ <;>
    simp only [Module.End.mul_apply, blockOp_apply, map_add, LinearMap.add_apply,
      LinearMap.comp_apply] <;> abel

theorem blockOp_sub (a : End ℂ V) (c : M →ₗ[ℂ] V) (d : V →ₗ[ℂ] M) (b : End ℂ M)
    (a' : End ℂ V) (c' : M →ₗ[ℂ] V) (d' : V →ₗ[ℂ] M) (b' : End ℂ M) :
    blockOp a c d b - blockOp a' c' d' b' = blockOp (a - a') (c - c') (d - d') (b - b') := by
  refine blockOp_ext_iff.2 fun x => ⟨?_, ?_⟩ <;>
    simp only [LinearMap.sub_apply, blockOp_apply, Prod.fst_sub, Prod.snd_sub] <;> abel

theorem blockOp_add (a : End ℂ V) (c : M →ₗ[ℂ] V) (d : V →ₗ[ℂ] M) (b : End ℂ M)
    (a' : End ℂ V) (c' : M →ₗ[ℂ] V) (d' : V →ₗ[ℂ] M) (b' : End ℂ M) :
    blockOp a c d b + blockOp a' c' d' b' = blockOp (a + a') (c + c') (d + d') (b + b') := by
  refine blockOp_ext_iff.2 fun x => ⟨?_, ?_⟩ <;>
    simp only [LinearMap.add_apply, blockOp_apply, Prod.fst_add, Prod.snd_add] <;> abel

theorem blockOp_smul (r : ℂ) (a : End ℂ V) (c : M →ₗ[ℂ] V) (d : V →ₗ[ℂ] M) (b : End ℂ M) :
    r • blockOp a c d b = blockOp (r • a) (r • c) (r • d) (r • b) := by
  refine blockOp_ext_iff.2 fun x => ⟨?_, ?_⟩ <;>
    simp only [LinearMap.smul_apply, blockOp_apply, Prod.smul_fst, Prod.smul_snd, smul_add]

theorem blockOp_zsmul (r : ℤ) (a : End ℂ V) (c : M →ₗ[ℂ] V) (d : V →ₗ[ℂ] M) (b : End ℂ M) :
    r • blockOp a c d b = blockOp (r • a) (r • c) (r • d) (r • b) := by
  refine blockOp_ext_iff.2 fun x => ⟨?_, ?_⟩ <;>
    simp only [LinearMap.smul_apply, blockOp_apply, Prod.smul_fst, Prod.smul_snd, smul_add]

@[simp] theorem blockOp_zero :
    blockOp (0 : End ℂ V) (0 : M →ₗ[ℂ] V) (0 : V →ₗ[ℂ] M) (0 : End ℂ M) = 0 := by
  refine blockOp_ext_iff.2 fun x => ⟨?_, ?_⟩ <;> simp

/-- The block field `[[a(z), c(z)], [d(z), b(z)]]`, coefficientwise `blockOp`. -/
def blockF (a : FormalDist (End ℂ V)) (c : FormalDist (M →ₗ[ℂ] V)) (d : FormalDist (V →ₗ[ℂ] M))
    (b : FormalDist (End ℂ M)) : FormalDist (End ℂ (V × M)) :=
  fun n => blockOp (a n) (c n) (d n) (b n)

@[simp] theorem blockF_apply (a : FormalDist (End ℂ V)) (c : FormalDist (M →ₗ[ℂ] V))
    (d : FormalDist (V →ₗ[ℂ] M)) (b : FormalDist (End ℂ M)) (n : ℤ) :
    blockF a c d b n = blockOp (a n) (c n) (d n) (b n) := rfl

/-- The two-variable block distribution. -/
def blockF₂ (A : FormalDist₂ (End ℂ V)) (C : FormalDist₂ (M →ₗ[ℂ] V))
    (D : FormalDist₂ (V →ₗ[ℂ] M)) (B : FormalDist₂ (End ℂ M)) : FormalDist₂ (End ℂ (V × M)) :=
  fun m n => blockOp (A m n) (C m n) (D m n) (B m n)

/-- `(z₁ − z₂)ᴺ` acts blockwise. -/
theorem mulBySubPow_blockF₂ (N : ℕ) (A : FormalDist₂ (End ℂ V)) (C : FormalDist₂ (M →ₗ[ℂ] V))
    (D : FormalDist₂ (V →ₗ[ℂ] M)) (B : FormalDist₂ (End ℂ M)) :
    mulBySubPow N (blockF₂ A C D B)
      = blockF₂ (mulBySubPow N A) (mulBySubPow N C) (mulBySubPow N D) (mulBySubPow N B) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [mulBySubPow_succ, LinearMap.comp_apply, ih]
    refine FormalDist₂.ext fun m n => ?_
    simp only [mulBySub_apply, blockF₂, blockOp_sub]

theorem mulBySubPow_blockF₂_eq_zero {N : ℕ} {A : FormalDist₂ (End ℂ V)}
    {C : FormalDist₂ (M →ₗ[ℂ] V)} {D : FormalDist₂ (V →ₗ[ℂ] M)} {B : FormalDist₂ (End ℂ M)}
    (hA : mulBySubPow N A = 0) (hC : mulBySubPow N C = 0) (hD : mulBySubPow N D = 0)
    (hB : mulBySubPow N B = 0) : mulBySubPow N (blockF₂ A C D B) = 0 := by
  rw [mulBySubPow_blockF₂, hA, hB, hC, hD]
  refine FormalDist₂.ext fun m n => ?_
  exact blockOp_zero

/-! ### Fields -/

/-- Lower truncation of a `Hom`-valued distribution (the `IsField` condition, for
`X →ₗ Y`-valued distributions). -/
def Trunc {X : Type*} {Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (f : FormalDist (X →ₗ[ℂ] Y)) : Prop :=
  ∀ x : X, ∃ B : ℤ, ∀ n : ℤ, n < B → f n x = 0

theorem trunc_zero {X : Type*} {Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] : Trunc (0 : FormalDist (X →ₗ[ℂ] Y)) :=
  fun _ => ⟨0, fun _ _ => rfl⟩

/-- A block field is a field when its four blocks are lower-truncated. -/
theorem isField_blockF {a : FormalDist (End ℂ V)} {c : FormalDist (M →ₗ[ℂ] V)}
    {d : FormalDist (V →ₗ[ℂ] M)} {b : FormalDist (End ℂ M)}
    (ha : Trunc a) (hc : Trunc c) (hd : Trunc d) (hb : Trunc b) :
    IsField (blockF a c d b) := by
  intro x
  obtain ⟨Ba, hBa⟩ := ha x.1
  obtain ⟨Bc, hBc⟩ := hc x.2
  obtain ⟨Bd, hBd⟩ := hd x.1
  obtain ⟨Bb, hBb⟩ := hb x.2
  refine ⟨min (min Ba Bc) (min Bd Bb), fun n hn => ?_⟩
  rw [blockF_apply, blockOp_apply, hBa n (by omega), hBc n (by omega), hBd n (by omega),
    hBb n (by omega), add_zero]
  simp

/-! ### Translation covariance -/

/-- `T`-covariance of a `Hom`-valued distribution, for a pair of translation operators. -/
def HomCov {X : Type*} {Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (TX : End ℂ X) (TY : End ℂ Y) (f : FormalDist (X →ₗ[ℂ] Y)) : Prop :=
  ∀ m : ℤ, TY ∘ₗ f m - f m ∘ₗ TX = (m + 1 : ℤ) • f (m + 1)

theorem homCov_zero {X : Type*} {Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (TX : End ℂ X) (TY : End ℂ Y) : HomCov TX TY (0 : FormalDist (X →ₗ[ℂ] Y)) :=
  fun m => by
    change TY ∘ₗ (0 : X →ₗ[ℂ] Y) - (0 : X →ₗ[ℂ] Y) ∘ₗ TX = (m + 1 : ℤ) • (0 : X →ₗ[ℂ] Y)
    simp

/-- `T`-covariance of a block field with respect to the diagonal translation
`diag(T_V, T_M)`, from the covariance of its four blocks. -/
theorem dCovariant_blockF {TV : End ℂ V} {TM : End ℂ M} {a : FormalDist (End ℂ V)}
    {c : FormalDist (M →ₗ[ℂ] V)} {d : FormalDist (V →ₗ[ℂ] M)} {b : FormalDist (End ℂ M)}
    (ha : Reconstruction.DCovariant TV a) (hc : HomCov TM TV c) (hd : HomCov TV TM d)
    (hb : Reconstruction.DCovariant TM b) :
    Reconstruction.DCovariant (blockOp TV 0 0 TM) (blockF a c d b) := by
  intro m
  rw [blockF_apply, blockF_apply, blockOp_mul, blockOp_mul, blockOp_sub, blockOp_zsmul,
    ← ha m, ← hb m, ← hc m, ← hd m]
  congr 1 <;> simp [LinearMap.comp_zero, LinearMap.zero_comp]

/-! ### Locality -/

/-- The commutator of two block fields, blockwise. -/
theorem bracketDist_blockF (a : FormalDist (End ℂ V)) (c : FormalDist (M →ₗ[ℂ] V))
    (d : FormalDist (V →ₗ[ℂ] M)) (b : FormalDist (End ℂ M))
    (a' : FormalDist (End ℂ V)) (c' : FormalDist (M →ₗ[ℂ] V))
    (d' : FormalDist (V →ₗ[ℂ] M)) (b' : FormalDist (End ℂ M)) :
    bracketDist (blockF a c d b) (blockF a' c' d' b')
      = blockF₂ (fun m n => a m * a' n + c m ∘ₗ d' n - (a' n * a m + c' n ∘ₗ d m))
          (fun m n => a m ∘ₗ c' n + c m ∘ₗ b' n - (a' n ∘ₗ c m + c' n ∘ₗ b m))
          (fun m n => d m ∘ₗ a' n + b m ∘ₗ d' n - (d' n ∘ₗ a m + b' n ∘ₗ d m))
          (fun m n => d m ∘ₗ c' n + b m * b' n - (d' n ∘ₗ c m + b' n * b m)) := by
  refine FormalDist₂.ext fun m n => ?_
  rw [bracketDist_apply, blockF_apply, blockF_apply, blockOp_mul, blockOp_mul, blockOp_sub]
  rfl

/-- The diagonal block field `diag(a, b)`. -/
def diagF (a : FormalDist (End ℂ V)) (b : FormalDist (End ℂ M)) : FormalDist (End ℂ (V × M)) :=
  blockF a 0 0 b

/-- The off-diagonal block field `offdiag(c, d) = [[0, c], [d, 0]]`. -/
def offF (c : FormalDist (M →ₗ[ℂ] V)) (d : FormalDist (V →ₗ[ℂ] M)) :
    FormalDist (End ℂ (V × M)) :=
  blockF 0 c d 0

/-- **Diagonal–diagonal locality.** -/
theorem local_diag_diag {a a' : FormalDist (End ℂ V)} {b b' : FormalDist (End ℂ M)}
    (ha : Local a a') (hb : Local b b') : Local (diagF a b) (diagF a' b') := by
  obtain ⟨Na, hNa⟩ := ha
  obtain ⟨Nb, hNb⟩ := hb
  refine ⟨max Na Nb, ?_⟩
  rw [diagF, diagF, bracketDist_blockF]
  refine mulBySubPow_blockF₂_eq_zero ?_ ?_ ?_ ?_
  · refine mulBySubPow_eq_zero_of_le (le_max_left Na Nb) ?_
    convert hNa using 2
    refine FormalDist₂.ext fun m n => ?_
    change a m * a' n + (0 : M →ₗ[ℂ] V) ∘ₗ (0 : V →ₗ[ℂ] M) - (a' n * a m + (0 : M →ₗ[ℂ] V) ∘ₗ 0)
      = a m * a' n - a' n * a m
    simp
  · convert map_zero (mulBySubPow (𝒲 := M →ₗ[ℂ] V) (max Na Nb)) using 2
    refine FormalDist₂.ext fun m n => ?_
    change a m ∘ₗ (0 : M →ₗ[ℂ] V) + (0 : M →ₗ[ℂ] V) ∘ₗ b' n
      - (a' n ∘ₗ (0 : M →ₗ[ℂ] V) + (0 : M →ₗ[ℂ] V) ∘ₗ b m) = 0
    simp
  · convert map_zero (mulBySubPow (𝒲 := V →ₗ[ℂ] M) (max Na Nb)) using 2
    refine FormalDist₂.ext fun m n => ?_
    change (0 : V →ₗ[ℂ] M) ∘ₗ a' n + b m ∘ₗ (0 : V →ₗ[ℂ] M)
      - ((0 : V →ₗ[ℂ] M) ∘ₗ a m + b' n ∘ₗ (0 : V →ₗ[ℂ] M)) = 0
    simp
  · refine mulBySubPow_eq_zero_of_le (le_max_right Na Nb) ?_
    convert hNb using 2
    refine FormalDist₂.ext fun m n => ?_
    change (0 : V →ₗ[ℂ] M) ∘ₗ (0 : M →ₗ[ℂ] V) + b m * b' n - ((0 : V →ₗ[ℂ] M) ∘ₗ 0 + b' n * b m)
      = b m * b' n - b' n * b m
    simp

/-- **Diagonal–off-diagonal locality.**  `diag(a(z₁), b(z₁))` and `offdiag(c'(z₂), d'(z₂))`
are mutually local as soon as the two `Hom`-valued intertwining commutators
`a c' − c' b` (in `Hom(M, V)`) and `b d' − d' a` (in `Hom(V, M)`) are killed by a power of
`(z₁ − z₂)`. -/
theorem local_diag_off {a : FormalDist (End ℂ V)} {b : FormalDist (End ℂ M)}
    {c' : FormalDist (M →ₗ[ℂ] V)} {d' : FormalDist (V →ₗ[ℂ] M)}
    (hc : ∃ N : ℕ, mulBySubPow N
      ((fun m n => a m ∘ₗ c' n - c' n ∘ₗ b m) : FormalDist₂ (M →ₗ[ℂ] V)) = 0)
    (hd : ∃ N : ℕ, mulBySubPow N
      ((fun m n => b m ∘ₗ d' n - d' n ∘ₗ a m) : FormalDist₂ (V →ₗ[ℂ] M)) = 0) :
    Local (diagF a b) (offF c' d') := by
  obtain ⟨Nc, hNc⟩ := hc
  obtain ⟨Nd, hNd⟩ := hd
  refine ⟨max Nc Nd, ?_⟩
  rw [diagF, offF, bracketDist_blockF]
  refine mulBySubPow_blockF₂_eq_zero ?_ ?_ ?_ ?_
  · convert map_zero (mulBySubPow (𝒲 := End ℂ V) (max Nc Nd)) using 2
    refine FormalDist₂.ext fun m n => ?_
    change a m * (0 : End ℂ V) + (0 : M →ₗ[ℂ] V) ∘ₗ d' n
      - ((0 : End ℂ V) * a m + c' n ∘ₗ (0 : V →ₗ[ℂ] M)) = 0
    simp
  · refine mulBySubPow_eq_zero_of_le (le_max_left Nc Nd) ?_
    convert hNc using 2
    refine FormalDist₂.ext fun m n => ?_
    change a m ∘ₗ c' n + (0 : M →ₗ[ℂ] V) ∘ₗ (0 : End ℂ M) - ((0 : End ℂ V) ∘ₗ (0 : M →ₗ[ℂ] V)
      + c' n ∘ₗ b m) = a m ∘ₗ c' n - c' n ∘ₗ b m
    simp
  · refine mulBySubPow_eq_zero_of_le (le_max_right Nc Nd) ?_
    convert hNd using 2
    refine FormalDist₂.ext fun m n => ?_
    change (0 : V →ₗ[ℂ] M) ∘ₗ (0 : End ℂ V) + b m ∘ₗ d' n - (d' n ∘ₗ a m
      + (0 : End ℂ M) ∘ₗ (0 : V →ₗ[ℂ] M)) = b m ∘ₗ d' n - d' n ∘ₗ a m
    simp
  · convert map_zero (mulBySubPow (𝒲 := End ℂ M) (max Nc Nd)) using 2
    refine FormalDist₂.ext fun m n => ?_
    change (0 : V →ₗ[ℂ] M) ∘ₗ c' n + b m * (0 : End ℂ M)
      - (d' n ∘ₗ (0 : M →ₗ[ℂ] V) + (0 : End ℂ M) * b m) = 0
    simp

end Block

/-! ## Locality of the fields of a weak module -/

section ModuleLocality

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- **The module commutator formula** (the `ℓ = 0` slice of the module Jacobi identity), for
`J` past the truncation of `u₍ⱼ₎v`:
`u₍ₘ₎ v₍ₙ₎ x − v₍ₙ₎ u₍ₘ₎ x = ∑_{r<J} C(m,r) (u₍ᵣ₎v)₍ₘ₊ₙ₋ᵣ₎ x`. -/
theorem act_comm (A : WeakModule W M) (u v : 𝒱) (m n : ℤ) (x : M) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → W.smul u j v = 0) :
    A.act u m (A.act v n x) - A.act v n (A.act u m x)
      = ∑ r ∈ Finset.range J, gBinom m r • A.act (W.smul u r v) (m + n - r) x := by
  have hj := A.jacobi u v x 0 m n
  have hl : (∑ᶠ i : ℤ, (negOnePow i * cbz 0 i) •
        (mode (A.YM u) (0 + m - i) (mode (A.YM v) (n + i) x)
          - negOnePow 0 • mode (A.YM v) (0 + n - i) (mode (A.YM u) (m + i) x)))
      = A.act u m (A.act v n x) - A.act v n (A.act u m x) := by
    rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    simp [negOnePow]
  rw [← hl, hj]
  rw [finsum_int_eq_sum_range _ J]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [WeakModule.act_def, cbz, if_pos (by positivity), Int.toNat_natCast, zero_add]
  · intro i hi
    by_contra hcon
    apply hi
    rcases not_and_or.1 hcon with h | h
    · rw [cbz, if_neg h, zero_smul]
    · rw [zero_add, show i = ((i.toNat : ℕ) : ℤ) by omega,
        hJ i.toNat (by omega), map_zero, mode_zero, LinearMap.zero_apply, smul_zero]

/-- The commutator distribution `[Y_M(u,z₁), Y_M(v,z₂)]` is a finite sum of jump
distributions. -/
theorem bracketDist_YM_eq_sum (A : WeakModule W M) (u v : 𝒱) (J : ℕ)
    (hJ : ∀ j : ℕ, J ≤ j → W.smul u j v = 0) :
    bracketDist (A.YM u) (A.YM v)
      = ∑ r ∈ Finset.range J,
          jumpDist r (fun k => A.YM (W.smul u r v) (k + r + 1)) := by
  refine FormalDist₂.ext fun a b => ?_
  rw [fd2_finset_sum_apply]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sum_apply, bracketDist_apply]
  have hc := act_comm A u v (-a - 1) (-b - 1) x J hJ
  simp only [WeakModule.act_def, mode_apply, show -(-a - 1) - 1 = a by ring,
    show -(-b - 1) - 1 = b by ring] at hc
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hc]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [jumpDist, LinearMap.smul_apply,
    show -(-a - 1 + (-b - 1) - (r : ℤ)) - 1 = a + b + r + 1 by ring]

/-- **Locality of module fields**: for a weak module, `Y_M(u,z)` and `Y_M(v,z)` are mutually
local. -/
theorem local_YM (A : WeakModule W M) (u v : 𝒱) : Local (A.YM u) (A.YM v) := by
  obtain ⟨N, hN⟩ := W.regularity u v
  refine ⟨N.toNat, ?_⟩
  rw [bracketDist_YM_eq_sum A u v N.toNat (fun j hj => hN _ (by omega)), map_sum]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [Finset.mem_range] at hr
  exact mulBySubPow_eq_zero_of_le (by omega : r + 1 ≤ N.toNat) (mulBySubPow_jumpDist r _)

end ModuleLocality

/-! ## Translation covariance of module fields and of the skew field -/

section Covariance

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

theorem gBinom_zero_left {r : ℕ} (hr : r ≠ 0) : gBinom 0 r = 0 := by
  rw [gBinom, Finset.prod_eq_zero (Finset.mem_range.2 (Nat.pos_of_ne_zero hr)) (by simp),
    zero_div]

/-- Module fields are `L₋₁ᴹ`-covariant: `[L₋₁ᴹ, Y_M(u)ₘ] = (m+1) Y_M(u)ₘ₊₁` (z-power indexing). -/
theorem dCovariant_YM (A : WeakModule W M) (u : 𝒱) :
    Reconstruction.DCovariant (Lm1 A) (A.YM u) := by
  intro m
  refine LinearMap.ext fun x => ?_
  have h := act_Lm1 A u (-m - 1) x
  simp only [WeakModule.act_def, mode_apply] at h
  rw [show -(-m - 1) - 1 = m by ring, show -(-m - 1 - 1) - 1 = m + 1 by ring] at h
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, h, LinearMap.smul_apply,
    sub_add_cancel_left, ← neg_smul]
  congr 1
  ring

/-- The fields of a VOA are `L₋₁`-covariant (the adjoint-module case of `dCovariant_YM`). -/
theorem dCovariant_Y (u : 𝒱) : Reconstruction.DCovariant (W.L (-1)) (W.Y u) := by
  have h := dCovariant_YM (adjointWeakModule W) u
  have e : Lm1 (adjointWeakModule W) = W.L (-1) := by
    rw [VertexOperatorAlgebra.L_def]; rfl
  rw [e] at h
  exact h

/-- The skew field is translation covariant: `L₋₁ᴹ W(t,z) − W(t,z) L₋₁ = ∂_z W(t,z)`, from the
intertwining commutator formula at `u = ω`, `m = 0` and `W(L₋₁t, z) = ∂_z W(t,z)`. -/
theorem homCov_Wsk (A : WeakModule W M) (t : M) : HomCov (W.L (-1)) (Lm1 A) (Wsk A t) := by
  intro m
  refine LinearMap.ext fun φ => ?_
  obtain ⟨J0, hJ0⟩ := A.truncation W.conformalVector t
  have hc := wMode_comm A W.conformalVector 0 t (-m - 1) φ (J0.toNat + 1)
    (fun j hj => hJ0 _ (by omega))
  rw [Finset.sum_eq_single 0 (fun r _ hr => by rw [gBinom_zero_left hr, zero_smul])
    (fun h => absurd (Finset.mem_range.2 (Nat.succ_pos _)) h)] at hc
  rw [gBinom_zero, one_smul, Nat.cast_zero, sub_zero, zero_add, smul_omega_zero] at hc
  have hL : A.act W.conformalVector 0 t = Lm1 A t := rfl
  rw [hL, wMode_Lm1] at hc
  change Lm1 A (wMode A t (-m - 1) φ) - wMode A t (-m - 1) (W.L (-1) φ)
    = ((m + 1 : ℤ) • wModeLin A t (-(m + 1) - 1)) φ
  have hL' : ∀ y, Lm1 A y = A.act W.conformalVector 0 y := fun _ => rfl
  rw [hL', hc, LinearMap.smul_apply, wModeLin_apply, ← Int.cast_smul_eq_zsmul ℂ,
    show -m - 1 - 1 = -(m + 1) - 1 by ring]
  push_cast
  ring_nf

end Covariance

end VOA.Moonshine.VnatBlock
