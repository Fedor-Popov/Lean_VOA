/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.FrameSectors
import VOA.Moonshine.TwistedHeisenberg

/-!
# The Golay frame of the twisted sector: `T = T₊ ⊕ T₋`, `2048 + 2048`  (Moonshine step M8e)

Let `L` be even unimodular, `χ : L → ℤ/2` a character, and `w ∈ L` with `(-1)^{⟨w,α⟩} = (-1)^{χ α}`
for all `α` (for the Leech lattice and `χ = β`: `w = 8e₀`, since `⟨8e₀, x⟩ = x₀`).  On the
extraspecial module `T` (`IntegralLattice.ExtraT`, `e_α e_β = ε(α,β) e_{α+β}`):

* `e_w e_α = (-1)^{⟨w,α⟩} e_α e_w` (`eT_comm_sign`), so `e_w` commutes with `e_α` for `α ∈ ker χ`
  and anticommutes for `α ∉ ker χ`: it is (up to a scalar) the central element of the
  subgroup `Λ̂₀/K` attached to the radical `{0, w}` of `Λ₀/2Λ = w^⊥`;
* `e_w² = ε(w,w)` (`eT_mul_self`), a sign; so `J := c⁻¹ e_w` with `c² = ε(w,w)` is an
  involution (`frameJ_mul_self`), and `T = T₊ ⊕ T₋` with `T_± = ker(J ∓ 1)` (`frameT_isCompl`);
* each `T_±` is `e_α`-stable for `α ∈ ker χ` (`eT_mem_frameT`), and any `e_u` with `χ u ≠ 0` swaps
  `T₊` and `T₋` injectively, so `dim T₊ = dim T₋` (`finrank_frameT_eq`).

For the Leech lattice: `dim T₊ = dim T₋ = 2048` (`finrank_leechFrameT_plus`,
`finrank_leechFrameT_minus`).  On the twisted carrier `S[θ] ⊗ T` the split is `id ⊗ J`
(`twFrame_isCompl`).

*Which eigenspace is FLM's `T₀`* (the one paired with `V₃⁺` by triality) is a convention that
depends on the normalisation of `c` and of the cocycle; it is **not** fixed here — `T₊`/`T₋`
are labelled by the eigenvalue of `J` only.  Pinning it is part of M8g.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
Unconditional.  `T` is the abstract Wedderburn–Artin module of `ExtraspecialModule.lean`;
we work with `Rep (cocMat L) _` throughout (the `ExtraT` abbrev times out on scalar actions).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.FrameT

open VOA.IntegralLattice VOA.LatGen Module
open scoped TensorProduct

variable (L : VOA.IntegralLattice) (hEven : L.Even) (hU : IsUnit (gramMat L).det)

/-- The extraspecial module, as a `Rep` (avoiding the slow `ExtraT` abbrev). -/
abbrev TT : Type := Extraspecial.Rep (cocMat L) (isUnit_det_cocMat L hEven hU)

/-- `e_w e_w = ε(w,w)`. -/
theorem eT_mul_self (w : L.carrier) :
    eT L hEven hU w * eT L hEven hU w = latticeCocycle L w w • (1 : End ℂ (TT L hEven hU)) := by
  rw [eT_mul]
  congr 1
  have h := eT_add_two_nsmul L hEven hU 0 w
  rw [zero_add, eT_zero, two_nsmul] at h
  exact h

/-- `e_w e_α = (-1)^{⟨w,α⟩} e_α e_w`. -/
theorem eT_comm_sign (w α : L.carrier) :
    eT L hEven hU w * eT L hEven hU α
      = ((-1 : ℂ) ^ (L.form w α)) • (eT L hEven hU α * eT L hEven hU w) := by
  rw [eT_mul, eT_mul, latticeCocycle_swap_sign L hEven w α, add_comm w α, smul_smul]

theorem latticeCocycle_ne_zero' (α β : L.carrier) : latticeCocycle L α β ≠ 0 := by
  intro h
  have := latticeCocycle_sq L α β
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- A square root `c` of `ε(w,w)`. -/
noncomputable def sqrtEps (w : L.carrier) : ℂ :=
  (IsAlgClosed.exists_eq_mul_self (latticeCocycle L w w)).choose

theorem sqrtEps_mul_self (w : L.carrier) : sqrtEps L w * sqrtEps L w = latticeCocycle L w w :=
  (IsAlgClosed.exists_eq_mul_self (latticeCocycle L w w)).choose_spec.symm

theorem sqrtEps_ne_zero (w : L.carrier) : sqrtEps L w ≠ 0 := by
  intro h
  have := sqrtEps_mul_self L w
  rw [h, zero_mul] at this
  exact latticeCocycle_ne_zero' L w w this.symm

/-- The frame involution `J = c⁻¹ e_w` on `T`. -/
noncomputable def frameJ (w : L.carrier) : End ℂ (TT L hEven hU) :=
  (sqrtEps L w)⁻¹ • eT L hEven hU w

theorem frameJ_mul_self (w : L.carrier) : frameJ L hEven hU w * frameJ L hEven hU w = 1 := by
  rw [frameJ, smul_mul_smul_comm, eT_mul_self, smul_smul, ← mul_inv, sqrtEps_mul_self,
    inv_mul_cancel₀ (latticeCocycle_ne_zero' L w w), one_smul]

theorem frameJ_frameJ (w : L.carrier) (x : TT L hEven hU) :
    frameJ L hEven hU w (frameJ L hEven hU w x) = x := by
  rw [← Module.End.mul_apply, frameJ_mul_self, Module.End.one_apply]

theorem frameJ_comm_sign (w α : L.carrier) :
    frameJ L hEven hU w * eT L hEven hU α
      = ((-1 : ℂ) ^ (L.form w α)) • (eT L hEven hU α * frameJ L hEven hU w) := by
  rw [frameJ, smul_mul_assoc, eT_comm_sign, mul_smul_comm, smul_comm]

/-- The two frame eigenspaces `T_± = ker(J ∓ 1)` (`s = 0 ↦ T₊`, `s = 1 ↦ T₋`). -/
noncomputable def frameT (w : L.carrier) (s : ZMod 2) : Submodule ℂ (TT L hEven hU) :=
  Module.End.eigenspace (frameJ L hEven hU w) (Extraspecial.sgn s)

theorem mem_frameT {w : L.carrier} {s : ZMod 2} {x : TT L hEven hU} :
    x ∈ frameT L hEven hU w s ↔ frameJ L hEven hU w x = Extraspecial.sgn s • x :=
  Module.End.mem_eigenspace_iff

theorem frameT_zero_eq (w : L.carrier) :
    frameT L hEven hU w 0 = LinearMap.ker (frameJ L hEven hU w - 1) := by
  ext x
  rw [mem_frameT, Extraspecial.sgn_zero, one_smul, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]

theorem frameT_one_eq (w : L.carrier) :
    frameT L hEven hU w 1 = LinearMap.ker (frameJ L hEven hU w + 1) := by
  ext x
  rw [mem_frameT, Extraspecial.sgn_one, neg_one_smul, LinearMap.mem_ker, LinearMap.add_apply,
    Module.End.one_apply, add_eq_zero_iff_eq_neg]

/-- **`T = T₊ ⊕ T₋`.** -/
theorem frameT_isCompl (w : L.carrier) :
    IsCompl (frameT L hEven hU w 0) (frameT L hEven hU w 1) := by
  rw [frameT_zero_eq, frameT_one_eq]
  exact isCompl_ker_sub_one_ker_add_one _ (frameJ_frameJ L hEven hU w)

variable (χ : L.carrier →+ ZMod 2)

/-- `e_α` maps `T_s` to `T_{s + χ α}` when `(-1)^{⟨w,·⟩} = (-1)^{χ}`. -/
theorem eT_mem_frameT {w : L.carrier} (hw : ∀ α, (-1 : ℂ) ^ (L.form w α) = chiSign L χ α)
    (α : L.carrier) {s : ZMod 2} {x : TT L hEven hU} (hx : x ∈ frameT L hEven hU w s) :
    eT L hEven hU α x ∈ frameT L hEven hU w (s + χ α) := by
  rw [mem_frameT] at hx ⊢
  have h := congrArg (fun f : End ℂ (TT L hEven hU) => f x) (frameJ_comm_sign L hEven hU w α)
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [h, hx, map_smul, smul_smul, hw, Extraspecial.sgn_add, chiSign, mul_comm]

/-- `T₊` and `T₋` have the same dimension, as soon as some `e_u` has `χ u ≠ 0`. -/
theorem finrank_frameT_eq {w : L.carrier} (hw : ∀ α, (-1 : ℂ) ^ (L.form w α) = chiSign L χ α)
    {u : L.carrier} (hu : χ u = 1) :
    finrank ℂ (frameT L hEven hU w 0) = finrank ℂ (frameT L hEven hU w 1) := by
  have hinj : Function.Injective (eT L hEven hU u) := by
    intro x y hxy
    have h := congrArg (eT L hEven hU u) hxy
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, eT_mul_self] at h
    simp only [LinearMap.smul_apply, Module.End.one_apply] at h
    exact smul_right_injective _ (latticeCocycle_ne_zero' L u u) h
  have hmap : ∀ s : ZMod 2, (frameT L hEven hU w s).map (eT L hEven hU u)
      ≤ frameT L hEven hU w (s + 1) := by
    rintro s _ ⟨x, hx, rfl⟩
    have := eT_mem_frameT L hEven hU χ hw u hx
    rwa [hu] at this
  have hle : ∀ s : ZMod 2, finrank ℂ (frameT L hEven hU w s) ≤ finrank ℂ (frameT L hEven hU w (s + 1)) := by
    intro s
    have h1 := Submodule.finrank_mono (hmap s)
    rwa [← (Submodule.equivMapOfInjective _ hinj (frameT L hEven hU w s)).finrank_eq] at h1
  exact le_antisymm (hle 0) (by have := hle 1; rwa [show (1 : ZMod 2) + 1 = 0 from rfl] at this)

/-- `dim T₊ + dim T₋ = dim T`. -/
theorem finrank_frameT_add (w : L.carrier) :
    finrank ℂ (frameT L hEven hU w 0) + finrank ℂ (frameT L hEven hU w 1)
      = finrank ℂ (TT L hEven hU) :=
  Submodule.finrank_add_eq_of_isCompl (frameT_isCompl L hEven hU w)

/-- The split of a twisted carrier `F ⊗ T` by `id ⊗ J`. -/
noncomputable def twFrame (F : Type*) [AddCommGroup F] [Module ℂ F] (w : L.carrier) (s : ZMod 2) :
    Submodule ℂ (F ⊗[ℂ] TT L hEven hU) :=
  Module.End.eigenspace (LinearMap.lTensor F (frameJ L hEven hU w)) (Extraspecial.sgn s)

/-- **`F ⊗ T = (F ⊗ T₊) ⊕ (F ⊗ T₋)`** (as eigenspaces of `id ⊗ J`). -/
theorem twFrame_isCompl (F : Type*) [AddCommGroup F] [Module ℂ F] (w : L.carrier) :
    IsCompl (twFrame L hEven hU F w 0) (twFrame L hEven hU F w 1) := by
  have hz : twFrame L hEven hU F w 0 = LinearMap.ker (LinearMap.lTensor F (frameJ L hEven hU w) - 1) := by
    ext x
    rw [twFrame, Module.End.mem_eigenspace_iff, Extraspecial.sgn_zero, one_smul, LinearMap.mem_ker,
      LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have ho : twFrame L hEven hU F w 1 = LinearMap.ker (LinearMap.lTensor F (frameJ L hEven hU w) + 1) := by
    ext x
    rw [twFrame, Module.End.mem_eigenspace_iff, Extraspecial.sgn_one, neg_one_smul, LinearMap.mem_ker,
      LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]
  rw [hz, ho]
  refine isCompl_ker_sub_one_ker_add_one _ fun x => ?_
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← Module.End.mul_eq_comp, frameJ_mul_self,
    Module.End.one_eq_id, LinearMap.lTensor_id, LinearMap.id_apply]

end VOA.Moonshine.FrameT

/-! ## The Leech lattice -/

namespace VOA.Moonshine

open VOA.IntegralLattice VOA.LatGen Module FrameT

/-- The coordinate vector `e₀ ∈ ℤ²⁴`. -/
def e0 : Fin 24 → ℤ := Pi.single 0 1

/-- `w = 8e₀ = 2·(4e₀)`, with `4e₀ ∈ A`. -/
theorem eightE0_mem : (8 : ℤ) • e0 ∈ Leech.carrier := by
  refine Or.inl (Leech.mem_subA2.2 ⟨(4 : ℤ) • e0, ⟨?_, ?_⟩, ?_⟩)
  · rw [show (4 : ℤ) • e0 = (2 : ℤ) • ((2 : ℤ) • e0) by rw [smul_smul]; norm_num]
    exact two_smul_mem_preimageOfCode Code.golay _
  · exact ⟨1, by decide +kernel⟩
  · rw [smul_smul]; norm_num

/-- The frame vector `w = 8e₀ ∈ Λ₀`. -/
noncomputable def frameW : leech.carrier := (⟨_, eightE0_mem⟩ : ↥Leech.carrier)

theorem leech_form_frameW (α : leech.carrier) :
    leech.form frameW α = (Subtype.val (show ↥Leech.carrier from α)) 0 := by
  change ((((8 : ℤ) • e0) ⬝ᵥ (Subtype.val (show ↥Leech.carrier from α))) / 8) = _
  rw [smul_dotProduct, e0, single_dotProduct, one_mul, smul_eq_mul,
    Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0)]

theorem frameW_sign (α : leech.carrier) :
    (-1 : ℂ) ^ (leech.form frameW α) = chiSign leech frameChar α := by
  rw [leech_form_frameW, Extraspecial.neg_one_zpow_eq_sgn, chiSign, frameChar_apply]
  rfl

theorem frameChar_uVec : frameChar ⟨Leech.uVec, Or.inr (by simp)⟩ = 1 := by
  change (((Leech.uVec 0 : ℤ)) : ZMod 2) = 1
  rw [show Leech.uVec 0 = 5 from by simp [Leech.uVec]]
  decide

/-- The Leech frame eigenspaces `T_± ⊆ T`. -/
noncomputable abbrev leechFrameT (s : ZMod 2) : Submodule ℂ (TT leech leech_even leech_isUnit_det_gramMat) :=
  frameT leech leech_even leech_isUnit_det_gramMat frameW s

theorem leechFrameT_isCompl : IsCompl (leechFrameT 0) (leechFrameT 1) :=
  frameT_isCompl _ _ _ _

/-- **`dim T₊ = 2048`.** -/
theorem finrank_leechFrameT_plus : finrank ℂ (leechFrameT 0) = 2048 := by
  have h1 := finrank_frameT_add leech leech_even leech_isUnit_det_gramMat frameW
  have h2 := finrank_frameT_eq leech leech_even leech_isUnit_det_gramMat frameChar frameW_sign
    frameChar_uVec
  have h3 : finrank ℂ (TT leech leech_even leech_isUnit_det_gramMat) = 4096 := finrank_leechT
  rw [h3] at h1
  change finrank ℂ (frameT leech leech_even leech_isUnit_det_gramMat frameW 0) = 2048
  omega

/-- **`dim T₋ = 2048`.** -/
theorem finrank_leechFrameT_minus : finrank ℂ (leechFrameT 1) = 2048 := by
  have h2 := finrank_frameT_eq leech leech_even leech_isUnit_det_gramMat frameChar frameW_sign
    frameChar_uVec
  rw [← h2]; exact finrank_leechFrameT_plus

/-- `e_α` preserves `T_±` for `α ∈ Λ₀` and swaps them for `α ∉ Λ₀`. -/
theorem eT_mem_leechFrameT (α : leech.carrier) {s : ZMod 2}
    {x : TT leech leech_even leech_isUnit_det_gramMat} (hx : x ∈ leechFrameT s) :
    eT leech leech_even leech_isUnit_det_gramMat α x ∈ leechFrameT (s + frameChar α) :=
  eT_mem_frameT leech leech_even leech_isUnit_det_gramMat frameChar frameW_sign α hx

/-- The split of the twisted carrier `S[θ] ⊗ T = (S[θ] ⊗ T₊) ⊕ (S[θ] ⊗ T₋)`. -/
theorem leechTw_frame_isCompl :
    IsCompl (twFrame leech leech_even leech_isUnit_det_gramMat (TwistedHeisenberg.FockT 24) frameW 0)
      (twFrame leech leech_even leech_isUnit_det_gramMat (TwistedHeisenberg.FockT 24) frameW 1) :=
  twFrame_isCompl _ _ _ _ _

end VOA.Moonshine
