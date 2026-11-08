/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineLRFinOrderIsing
import VOA.Moonshine.NondegLeech
import VOA.Moonshine.MonsterGriess.LeechMatch

/-!
# The untwisted weight-two Griess algebra of `V_Λ⁺` in Conway's coordinates

The weight-two space of `V_Λ⁺` is spanned by the quadratic states `h_a(−1)h_b(−1)𝟙` (the
`S²𝔥` block) and the vectors `x_β = e^β + e^{−β}`, `β` a minimal Leech vector.  The library
writes the quadratic states in an orthonormal frame of `𝔥` (`chargeCoord`), which depends on a
noncomputable lattice basis and has irrational entries.  This file restates the `S²𝔥` block in
**Conway's integer coordinates** of the Leech lattice, through the lattice vectors
`8eᵢ ∈ Λ` (`conwayAxis i`, norm `8`, `⟨8eᵢ, β⟩ = βᵢ`):

  `conwayQuad A = ⅛ Σᵢⱼ Aᵢⱼ (8eᵢ)(−1)(8eⱼ)(−1)𝟙`   (`conwayQuad_eq_sum_dV`),

so that the structure constants are rational, and evaluates the Griess product `u₍₁₎v` and the
invariant form `plusForm` (= `leechBV`, the `V_Λ⁺` block of `natForm`) on the whole block.

## Main results
* `conwayFrame` — the frame coordinates of the Conway axes; `conwayFrame_transpose_mul`:
  `FᵀF = 8·1` (the axes are orthogonal of norm `8`); `conwayFrame_mulVec`: `F y_β = 8·β`.
* `frameQuad M = Σ_{a,b} M_{ab} h_a(−1)h_b(−1)𝟙` and
  ⭐ `frameQuad_one_frameQuad` — `Q(M)₍₁₎Q(N) = Q((M + Mᵀ)(N + Nᵀ))`.
* ⭐ `conwayQuad_one_conwayQuad` — `Q_C(A)₍₁₎Q_C(B) = Q_C((A + Aᵀ)(B + Bᵀ))`; for symmetric `A, B`
  this is `2·Q_C(AB + BA)` (`conwayQuad_one_conwayQuad_of_symm`), the `symMat` product
  `gmulA = 2(AB + BA)` of the rational Griess algebra.
* ⭐ `conwayQuad_one_frameX0P` — `Q_C(A)₍₁₎x_β = ⅛ (y_βᵀ A y_β) x_β`, `y_β` the integer coordinates
  of `β` (Axiom's `qf c A / 8`); `frameX0P_one_conwayQuad` for minimal `β`.
* ⭐ `dV_self_eq_conwayQuad` — `β(−1)²𝟙 = Q_C(⅛ y_β y_βᵀ)` (Axiom's `Umat c / 8`).
* forms: `plusForm_conwayQuad_conwayQuad` (`tr(ABᵀ) + tr(AB)`), `plusForm_conwayQuad_frameX0P`
  (`= 0` for `β ≠ 0`), ⭐ `plusForm_frameX0P_frameX0P` (`2ε(α,α)` on `β = ±α`, else `0`).
* transport to `V♮`: `vnat_smul_untwisted`, `natForm_untwisted`.

## Status
No hypotheses beyond those displayed.  The products of the `x_α` among themselves are the
lemmas `frameX0P_one_frameX0P_self`, `…_of_form_neg_two`, `…_of_form_two`, `…_of_form_small` of
`MoonshineLRFinOrderIsing`, used unchanged.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.GriessDictionary

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop VOA.Moonshine.TrialityTw
open VOA.LatGen VOA.IntegralLattice HeisenbergN VOA.Moonshine.SigmaExist
open VOA.Moonshine.ConwayNorton.M8
open VOA.Moonshine.MonsterGriess.LeechMatch (vec eight_mul_form)
open Matrix

/-! ## §1  The Conway axes `8eᵢ` -/

theorem eight_smul_mem_leechCarrier (x : Fin 24 → ℤ) : (8 : ℤ) • x ∈ Leech.carrier := by
  refine Or.inl (Leech.mem_subA2.2 ⟨(4 : ℤ) • x, ?_, ?_⟩)
  · refine ⟨?_, ?_⟩
    · have : (4 : ℤ) • x = (2 : ℤ) • ((2 : ℤ) • x) := by rw [smul_smul]; norm_num
      rw [this]
      exact two_smul_mem_preimageOfCode _root_.Code.golay _
    · refine ⟨∑ i, x i, ?_⟩
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp
  · rw [smul_smul]; norm_num

/-- The Conway axis `8eᵢ ∈ Λ`: the lattice vector with `8` in coordinate `i`, norm `8`. -/
def conwayAxis (i : Fin 24) : leech.carrier :=
  (⟨(8 : ℤ) • Pi.single i 1, eight_smul_mem_leechCarrier _⟩ : ↥Leech.carrier)

theorem vec_conwayAxis (i : Fin 24) : vec (conwayAxis i) = (8 : ℤ) • Pi.single i 1 := rfl

/-- `⟨8eᵢ, β⟩ = βᵢ`. -/
theorem form_conwayAxis (i : Fin 24) (β : leech.carrier) : leech.form (conwayAxis i) β = vec β i := by
  have h := eight_mul_form (conwayAxis i) β
  have hd : vec (conwayAxis i) ⬝ᵥ vec β = 8 * vec β i := by
    rw [vec_conwayAxis, smul_dotProduct, single_one_dotProduct, smul_eq_mul]
  omega

theorem form_conwayAxis_conwayAxis (i j : Fin 24) :
    leech.form (conwayAxis i) (conwayAxis j) = if i = j then 8 else 0 := by
  rw [form_conwayAxis, vec_conwayAxis]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- The integer coordinates of a lattice vector, as an additive map. -/
def vecHom : leech.carrier →+ (Fin 24 → ℤ) where
  toFun := vec
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `8β = Σᵢ βᵢ · 8eᵢ` in `Λ`. -/
theorem eight_smul_eq_sum_conwayAxis (β : leech.carrier) :
    (8 : ℤ) • β = ∑ i, vec β i • conwayAxis i := by
  have h : vecHom ((8 : ℤ) • β) = vecHom (∑ i, vec β i • conwayAxis i) := by
    rw [map_zsmul, map_sum]
    simp only [map_zsmul]
    funext j
    change (8 : ℤ) * vec β j = (∑ i, vec β i • vec (conwayAxis i)) j
    simp [vec_conwayAxis, Finset.sum_apply, Pi.single_apply]
    ring
  exact Subtype.val_injective h

/-- The frame coordinate in direction `a`, as an additive map of the lattice. -/
noncomputable def chargeCoordHom (a : Fin (rank leech)) : leech.carrier →+ ℂ where
  toFun α := chargeCoord leech α a
  map_zero' := chargeCoord_zero leech a
  map_add' α β := chargeCoord_add leech α β a

theorem sum_vec_mul_chargeCoord (β : leech.carrier) (a : Fin (rank leech)) :
    ∑ i, (vec β i : ℂ) * chargeCoord leech (conwayAxis i) a = 8 * chargeCoord leech β a := by
  have h := congrArg (chargeCoordHom a) (eight_smul_eq_sum_conwayAxis β)
  rw [map_zsmul, map_sum] at h
  simp only [map_zsmul, zsmul_eq_mul] at h
  change ((8 : ℤ) : ℂ) * chargeCoord leech β a
    = ∑ i, ((vec β i : ℤ) : ℂ) * chargeCoord leech (conwayAxis i) a at h
  push_cast at h
  exact h.symm

/-! ## §2  The Conway frame matrix -/

/-- `F_{a i} = (8eᵢ)_a`: the orthonormal-frame coordinates of the Conway axes. -/
noncomputable def conwayFrame : Matrix (Fin (rank leech)) (Fin 24) ℂ :=
  Matrix.of fun a i => chargeCoord leech (conwayAxis i) a

/-- The Conway axes are orthogonal of norm `8`: `FᵀF = 8·1`. -/
theorem conwayFrame_transpose_mul :
    conwayFrameᵀ * conwayFrame = (8 : ℂ) • (1 : Matrix (Fin 24) (Fin 24) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, conwayFrame, Matrix.of_apply]
  rw [sum_chargeCoord leech leech_posDef, form_conwayAxis_conwayAxis]
  by_cases h : i = j <;> simp [h]

/-- `Fᵀ β = y_β`: the frame vector of `β` read in Conway coordinates. -/
theorem conwayFrame_transpose_mulVec (β : leech.carrier) :
    conwayFrameᵀ *ᵥ chargeCoord leech β = fun i => (vec β i : ℂ) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, conwayFrame, Matrix.of_apply]
  rw [sum_chargeCoord leech leech_posDef, form_conwayAxis]

/-- `F y_β = 8·β` in frame coordinates. -/
theorem conwayFrame_mulVec (β : leech.carrier) :
    conwayFrame *ᵥ (fun i => (vec β i : ℂ)) = (8 : ℂ) • chargeCoord leech β := by
  funext a
  simp only [Matrix.mulVec, dotProduct, conwayFrame, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [← sum_vec_mul_chargeCoord β a]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ## §3  Quadratic states with a matrix of coefficients in the frame -/

/-- `Q(M) = Σ_{a,b} M_{ab} h_a(−1)h_b(−1)𝟙` for a complex matrix `M` in the orthonormal frame. -/
noncomputable def frameQuad : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ →ₗ[ℂ] VPlus where
  toFun M := ∑ a, ∑ b, M a b • qP a b
  map_add' M N := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem frameQuad_apply (M : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ) :
    frameQuad M = ∑ a, ∑ b, M a b • qP a b := rfl

theorem qP_eq_frameQuad (a b : Fin (rank leech)) : qP a b = frameQuad (Matrix.single a b 1) := by
  classical
  rw [frameQuad_apply]
  simp only [Matrix.single_apply, ite_smul, one_smul, zero_smul, ite_and]
  simp

theorem frameQuad_mem_grading_two (M : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ) :
    frameQuad M ∈ leechVOAPlus.grading 2 :=
  Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (qP_mem_grading a b)

/-- The four contractions of `qP a b · qP c d`, as a coefficient matrix. -/
noncomputable def quadContraction (a b c d : Fin (rank leech)) :
    Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ :=
  (if b = c then Matrix.single a d 1 else 0) + (if b = d then Matrix.single a c 1 else 0) +
    (if a = c then Matrix.single b d 1 else 0) + (if a = d then Matrix.single b c 1 else 0)

theorem qP_one_qP (a b c d : Fin (rank leech)) :
    leechVOAPlus.smul (qP a b) 1 (qP c d) = frameQuad (quadContraction a b c d) := by
  rw [quadState_one_quadState, quadContraction]
  simp only [map_add, apply_ite frameQuad, map_zero, ← qP_eq_frameQuad]

/-- ⭐ **The `S²𝔥` Griess product in the frame**: `Q(M)₍₁₎Q(N) = Q((M + Mᵀ)(N + Nᵀ))`. -/
theorem frameQuad_one_frameQuad (M N : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ) :
    leechVOAPlus.smul (frameQuad M) 1 (frameQuad N) = frameQuad ((M + Mᵀ) * (N + Nᵀ)) := by
  classical
  calc leechVOAPlus.smul (frameQuad M) 1 (frameQuad N)
      = ∑ a, ∑ b, ∑ c, ∑ d, (M a b * N c d) • frameQuad (quadContraction a b c d) := by
        rw [frameQuad_apply M, smul_sum_left]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_sum_left]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [PreVertexAlgebra.smul_smul_left, frameQuad_apply N, smul_sum_right', Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [smul_sum_right', Finset.smul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [PreVertexAlgebra.smul_smul_right, qP_one_qP, smul_smul]
    _ = frameQuad (∑ a, ∑ b, ∑ c, ∑ d, (M a b * N c d) • quadContraction a b c d) := by
        simp only [map_sum, map_smul]
    _ = frameQuad ((M + Mᵀ) * (N + Nᵀ)) := by
        congr 1
        ext x y
        simp only [Matrix.sum_apply, Matrix.smul_apply, quadContraction, Matrix.add_apply,
          Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul]
        simp only [apply_ite (fun m : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ => m x y),
          Matrix.single_apply, Matrix.zero_apply, mul_add, add_mul, Finset.sum_add_distrib]
        simp only [mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
          Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring_nf


theorem qP_comm (a b : Fin (rank leech)) : qP a b = qP b a := by
  apply Subtype.ext
  change quadSt leech leech_even leech_posDef a b = quadSt leech leech_even leech_posDef b a
  rw [quadSt_eq, quadSt_eq, mul_comm]

theorem frameQuad_transpose (M : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ) :
    frameQuad Mᵀ = frameQuad M := by
  rw [frameQuad_apply, frameQuad_apply, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    rw [Matrix.transpose_apply, qP_comm]

/-! ## §4  Rank-one states and the lattice letters `α(−1)β(−1)𝟙` -/

theorem isingQuad_eq_frameQuad (u v : Fin (rank leech) → ℂ) :
    isingQuad u v = frameQuad (vecMulVec u v) := by
  simp only [isingQuad, isingQuadRow, frameQuad_apply, Finset.smul_sum, smul_smul, vecMulVec_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]

/-- `α(−1)β(−1)𝟙 = Q(α βᵀ)` in frame coordinates. -/
theorem dV_eq_frameQuad (α β : leech.carrier) :
    (dV α β : VPlus) = frameQuad (vecMulVec (chargeCoord leech α) (chargeCoord leech β)) := by
  rw [← isingQuad_chargeCoord, isingQuad_eq_frameQuad]

/-! ## §5  The `S²𝔥` block in Conway coordinates -/

/-- `A ↦ ⅛ F A Fᵀ`: a Conway-coordinate matrix read in the orthonormal frame. -/
noncomputable def conwayToFrame :
    Matrix (Fin 24) (Fin 24) ℂ →ₗ[ℂ] Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ where
  toFun A := (8 : ℂ)⁻¹ • (conwayFrame * A * conwayFrameᵀ)
  map_add' A B := by rw [Matrix.mul_add, Matrix.add_mul, smul_add]
  map_smul' c A := by rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm, RingHom.id_apply]

theorem conwayToFrame_apply (A : Matrix (Fin 24) (Fin 24) ℂ) :
    conwayToFrame A = (8 : ℂ)⁻¹ • (conwayFrame * A * conwayFrameᵀ) := rfl

theorem conwayToFrame_transpose (A : Matrix (Fin 24) (Fin 24) ℂ) :
    (conwayToFrame A)ᵀ = conwayToFrame Aᵀ := by
  simp only [conwayToFrame_apply, transpose_smul, transpose_mul, transpose_transpose,
    Matrix.mul_assoc]

theorem conwayToFrame_mul (A B : Matrix (Fin 24) (Fin 24) ℂ) :
    conwayToFrame A * conwayToFrame B = conwayToFrame (A * B) := by
  have key : conwayFrame * A * conwayFrameᵀ * (conwayFrame * B * conwayFrameᵀ)
      = (8 : ℂ) • (conwayFrame * (A * B) * conwayFrameᵀ) := by
    calc conwayFrame * A * conwayFrameᵀ * (conwayFrame * B * conwayFrameᵀ)
        = conwayFrame * A * (conwayFrameᵀ * conwayFrame) * B * conwayFrameᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (8 : ℂ) • (conwayFrame * (A * B) * conwayFrameᵀ) := by
          rw [conwayFrame_transpose_mul]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [conwayToFrame_apply, conwayToFrame_apply, conwayToFrame_apply, Matrix.smul_mul,
    Matrix.mul_smul, key, smul_smul, smul_smul]
  congr 1
  norm_num

theorem trace_conwayToFrame (A : Matrix (Fin 24) (Fin 24) ℂ) :
    trace (conwayToFrame A) = trace A := by
  rw [conwayToFrame_apply, trace_smul, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc,
    conwayFrame_transpose_mul, Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_smul,
    smul_eq_mul]
  norm_num

/-- **The `S²𝔥` state of a Conway-coordinate matrix**:
`Q_C(A) = ⅛ Σᵢⱼ Aᵢⱼ (8eᵢ)(−1)(8eⱼ)(−1)𝟙` (`conwayQuad_eq_sum_dV`). -/
noncomputable def conwayQuad : Matrix (Fin 24) (Fin 24) ℂ →ₗ[ℂ] VPlus := frameQuad ∘ₗ conwayToFrame

theorem conwayQuad_apply (A : Matrix (Fin 24) (Fin 24) ℂ) :
    conwayQuad A = frameQuad (conwayToFrame A) := rfl

/-- `Q_C(A)` is a rational combination of the lattice letters `(8eᵢ)(−1)(8eⱼ)(−1)𝟙`. -/
theorem conwayQuad_eq_sum_dV (A : Matrix (Fin 24) (Fin 24) ℂ) :
    conwayQuad A = (8 : ℂ)⁻¹ • ∑ i, ∑ j, A i j • (dV (conwayAxis i) (conwayAxis j) : VPlus) := by
  have h : conwayFrame * A * conwayFrameᵀ = ∑ i, ∑ j, A i j •
      vecMulVec (chargeCoord leech (conwayAxis i)) (chargeCoord leech (conwayAxis j)) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
      conwayFrame, Matrix.of_apply, Matrix.transpose_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [dV_eq_frameQuad, conwayQuad_apply, conwayToFrame_apply, h, map_smul, map_sum]

theorem conwayQuad_mem_grading_two (A : Matrix (Fin 24) (Fin 24) ℂ) :
    conwayQuad A ∈ leechVOAPlus.grading 2 :=
  frameQuad_mem_grading_two _

theorem conwayQuad_transpose (A : Matrix (Fin 24) (Fin 24) ℂ) : conwayQuad Aᵀ = conwayQuad A := by
  rw [conwayQuad_apply, conwayQuad_apply, ← conwayToFrame_transpose, frameQuad_transpose]

/-- ⭐ **The `S²𝔥` Griess product in Conway coordinates**: `Q_C(A)₍₁₎Q_C(B) = Q_C((A + Aᵀ)(B + Bᵀ))`. -/
theorem conwayQuad_one_conwayQuad (A B : Matrix (Fin 24) (Fin 24) ℂ) :
    leechVOAPlus.smul (conwayQuad A) 1 (conwayQuad B) = conwayQuad ((A + Aᵀ) * (B + Bᵀ)) := by
  rw [conwayQuad_apply, conwayQuad_apply, frameQuad_one_frameQuad, conwayToFrame_transpose,
    conwayToFrame_transpose, ← map_add, ← map_add, conwayToFrame_mul, ← conwayQuad_apply]

/-- ⭐ For symmetric `A, B`: `Q_C(A)₍₁₎Q_C(B) = 2 Q_C(AB + BA)` (Axiom's `gmulA = 2(AB + BA)`). -/
theorem conwayQuad_one_conwayQuad_of_symm {A B : Matrix (Fin 24) (Fin 24) ℂ} (hA : Aᵀ = A)
    (hB : Bᵀ = B) :
    leechVOAPlus.smul (conwayQuad A) 1 (conwayQuad B) = (2 : ℂ) • conwayQuad (A * B + B * A) := by
  rw [conwayQuad_one_conwayQuad, hA, hB, map_add,
    show conwayQuad (B * A) = conwayQuad (A * B) by
      rw [← conwayQuad_transpose (A * B), transpose_mul, hA, hB],
    ← two_smul ℂ A, ← two_smul ℂ B, Matrix.smul_mul, Matrix.mul_smul, map_smul, map_smul]
  module

/-! ## §6  The action on the charged vectors `x_β` -/

theorem frameQuad_one_frameX0P (M : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ)
    (β : leech.carrier) :
    leechVOAPlus.smul (frameQuad M) 1 (frameX0P β)
      = (chargeCoord leech β ⬝ᵥ (M *ᵥ chargeCoord leech β)) • frameX0P β := by
  rw [frameQuad_apply]
  simp only [smul_sum_left, PreVertexAlgebra.smul_smul_left, smul_qP_frameX0P, smul_smul,
    ← Finset.sum_smul]
  congr 1
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- ⭐ **`S²𝔥` on `x_β` in Conway coordinates**: `Q_C(A)₍₁₎x_β = ⅛ (y_βᵀ A y_β) x_β`. -/
theorem conwayQuad_one_frameX0P (A : Matrix (Fin 24) (Fin 24) ℂ) (β : leech.carrier) :
    leechVOAPlus.smul (conwayQuad A) 1 (frameX0P β)
      = ((8 : ℂ)⁻¹ * ((fun i => (vec β i : ℂ)) ⬝ᵥ (A *ᵥ fun i => (vec β i : ℂ)))) • frameX0P β := by
  rw [conwayQuad_apply, frameQuad_one_frameX0P, conwayToFrame_apply]
  congr 1
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, ← mulVec_transpose, conwayFrame_transpose_mulVec]

theorem frameX0P_one_conwayQuad {β : leech.carrier} (hβ : leech.form β β = 4)
    (A : Matrix (Fin 24) (Fin 24) ℂ) :
    leechVOAPlus.smul (frameX0P β) 1 (conwayQuad A)
      = ((8 : ℂ)⁻¹ * ((fun i => (vec β i : ℂ)) ⬝ᵥ (A *ᵥ fun i => (vec β i : ℂ)))) • frameX0P β := by
  rw [plus_one_comm (frameX0P_mem_grading_two hβ) (conwayQuad_mem_grading_two A),
    conwayQuad_one_frameX0P]

/-- ⭐ **`β(−1)²𝟙` in Conway coordinates**: `β(−1)²𝟙 = Q_C(⅛ y_β y_βᵀ)` (Axiom's `Umat c / 8`). -/
theorem dV_self_eq_conwayQuad (β : leech.carrier) :
    (dV β β : VPlus)
      = conwayQuad ((8 : ℂ)⁻¹ • vecMulVec (fun i => (vec β i : ℂ)) (fun i => (vec β i : ℂ))) := by
  rw [dV_eq_frameQuad, conwayQuad_apply, conwayToFrame_apply]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, vecMul_transpose,
    conwayFrame_mulVec, smul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul, smul_smul]
  norm_num

/-! ## §7  The invariant form on the block -/

theorem uForm_X_mul_X {r : ℕ} (a b c d : Fin r) :
    Nondeg.uForm r (MvPolynomial.X (0, a) * MvPolynomial.X (0, b))
        (MvPolynomial.X (0, c) * MvPolynomial.X (0, d))
      = (if a = c ∧ b = d then 1 else 0) + (if a = d ∧ b = c then 1 else 0) := by
  classical
  rw [Nondeg.uForm_X_mul, show (MvPolynomial.X (0, b) : FockN r) = MvPolynomial.X (0, b) * 1 from
    (mul_one _).symm, Nondeg.uForm_X_mul, Nondeg.uForm_one]
  simp only [Nondeg.uVar, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply,
    Prod.mk.injEq, true_and]
  by_cases hac : a = c <;> by_cases had : a = d <;> by_cases hbc : b = c <;>
    by_cases hbd : b = d <;> by_cases hcd : c = d <;>
    simp_all [show ∀ x y : Fin r, x = y ↔ y = x from fun x y => eq_comm]

theorem plusForm_qP_qP (a b c d : Fin (rank leech)) :
    plusForm (qP a b) (qP c d)
      = (if a = c ∧ b = d then 1 else 0) + (if a = d ∧ b = c then 1 else 0) := by
  rw [plusForm_apply]
  change Nondeg.latForm leech (quadSt leech leech_even leech_posDef a b)
    (quadSt leech leech_even leech_posDef c d) = _
  rw [quadSt_eq, quadSt_eq]
  change Nondeg.latForm leech (latStateGen leech _ 0) (latStateGen leech _ 0) = _
  rw [Nondeg.latForm_state, if_pos (add_zero 0), Nondeg.chSign_zero, one_mul, uForm_X_mul_X]

theorem plusForm_frameQuad_frameQuad (M N : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ) :
    plusForm (frameQuad M) (frameQuad N) = ∑ a, ∑ b, M a b * (N a b + N b a) := by
  classical
  simp only [frameQuad_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    plusForm_qP_qP, smul_eq_mul]
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_and,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- **The form on the `S²𝔥` block**: `⟨Q_C(A), Q_C(B)⟩ = tr(ABᵀ) + tr(AB)`. -/
theorem plusForm_conwayQuad_conwayQuad (A B : Matrix (Fin 24) (Fin 24) ℂ) :
    plusForm (conwayQuad A) (conwayQuad B) = trace (A * Bᵀ) + trace (A * B) := by
  have h1 : ∀ X Y : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ,
      ∑ a, ∑ b, X a b * (Y a b + Y b a) = trace (X * Yᵀ) + trace (X * Y) := by
    intro X Y
    simp only [trace, diag, Matrix.mul_apply, Matrix.transpose_apply, mul_add,
      Finset.sum_add_distrib]
  rw [conwayQuad_apply, conwayQuad_apply, plusForm_frameQuad_frameQuad, h1,
    conwayToFrame_transpose, conwayToFrame_mul, conwayToFrame_mul, trace_conwayToFrame,
    trace_conwayToFrame]

theorem plusForm_conwayQuad_conwayQuad_of_symm {A B : Matrix (Fin 24) (Fin 24) ℂ}
    (hB : Bᵀ = B) : plusForm (conwayQuad A) (conwayQuad B) = 2 * trace (A * B) := by
  rw [plusForm_conwayQuad_conwayQuad, hB]
  ring

theorem plusForm_qP_frameX0P (a b : Fin (rank leech)) {β : leech.carrier} (hβ : β ≠ 0) :
    plusForm (qP a b) (frameX0P β) = 0 := by
  rw [plusForm_apply]
  change Nondeg.latForm leech (quadSt leech leech_even leech_posDef a b)
    (latStateGen leech (vacuumN (rank leech)) β
      + latStateGen leech (vacuumN (rank leech)) (-β)) = 0
  rw [quadSt_eq]
  change Nondeg.latForm leech (latStateGen leech _ 0) _ = 0
  rw [map_add, Nondeg.latForm_state, Nondeg.latForm_state, zero_add, zero_add, if_neg hβ,
    if_neg (neg_ne_zero.mpr hβ)]
  ring

theorem plusForm_conwayQuad_frameX0P (A : Matrix (Fin 24) (Fin 24) ℂ) {β : leech.carrier}
    (hβ : β ≠ 0) : plusForm (conwayQuad A) (frameX0P β) = 0 := by
  rw [conwayQuad_apply, frameQuad_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    plusForm_qP_frameX0P _ _ hβ, smul_zero, Finset.sum_const_zero]

theorem plusForm_frameX0P_conwayQuad (A : Matrix (Fin 24) (Fin 24) ℂ) {β : leech.carrier}
    (hβ : β ≠ 0) : plusForm (frameX0P β) (conwayQuad A) = 0 := by
  rw [plusForm_apply, Nondeg.latForm_symm, ← plusForm_apply, plusForm_conwayQuad_frameX0P A hβ]

theorem chSign_of_normFour {α : leech.carrier} (hα : leech.form α α = 4) :
    Nondeg.chSign leech α = latticeCocycle leech α α := by
  rw [Nondeg.chSign, LatGen.halfNorm, hα]
  norm_num

open Classical in
/-- ⭐ **The form on the charged block**: `⟨x_α, x_β⟩ = 2ε(α,α)` if `β = ±α`, else `0`
(`α` minimal). -/
theorem plusForm_frameX0P_frameX0P {α : leech.carrier} (hα : leech.form α α = 4)
    (β : leech.carrier) :
    plusForm (frameX0P α) (frameX0P β)
      = if β = α ∨ β = -α then 2 * latticeCocycle leech α α else 0 := by
  classical
  have hne : α ≠ -α := by
    intro h
    have h' := congrArg (fun γ => leech.form α γ) h
    simp only [map_neg] at h'
    omega
  have key : ∀ γ δ : leech.carrier, γ + δ = 0 ↔ δ = -γ := fun γ δ => by
    rw [eq_neg_iff_add_eq_zero, add_comm]
  rw [plusForm_apply]
  change Nondeg.latForm leech (latStateGen leech (vacuumN (rank leech)) α
      + latStateGen leech (vacuumN (rank leech)) (-α))
    (latStateGen leech (vacuumN (rank leech)) β
      + latStateGen leech (vacuumN (rank leech)) (-β)) = _
  simp only [map_add, LinearMap.add_apply, Nondeg.latForm_state, vacuumN, Nondeg.uForm_one,
    MvPolynomial.coeff_zero_one, mul_one, key, neg_neg, neg_inj, neg_eq_iff_eq_neg,
    Nondeg.chSign_neg, chSign_of_normFour hα]
  by_cases h1 : β = α
  · subst h1
    simp [hne]
    ring
  · by_cases h2 : β = -α
    · subst h2
      simp [hne, Ne.symm hne]
      ring
    · simp [h1, h2]

/-! ## §8  Transport to `V♮` -/

theorem vnat_smul_untwisted (u v : VPlus) (n : ℤ) :
    VnatVOA.smul ((u, 0) : Vnat) n ((v, 0) : Vnat) = (leechVOAPlus.smul u n v, 0) := by
  rw [VnatVOA_smul_inl, map_zero]

theorem natForm_untwisted (u v : VPlus) :
    SimpleNat.natForm ((u, 0) : Vnat) ((v, 0) : Vnat) = plusForm u v := by
  simp [SimpleNat.natForm_apply, leechBV_eq_plusForm]

end VOA.Moonshine.GriessDictionary
