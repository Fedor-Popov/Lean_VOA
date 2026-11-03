/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteGoodGhost

/-!
# Reducing `ZeroModesPreserve` to the factors

`ZeroModesPreserve Gh` (`ConcreteGoodInterpreted`) asks that the six relative constraints of the
actual BRST complex be `R`-homogeneous. On pure tensors the total current zero mode is the sum of
the factor current zero modes and the ghost current zero mode (`totalCurrentZero_tmul`,
`tensorCurrentMode_tmul`), and the antighost zero mode acts on the ghost factor only
(`antighostZero_tmul`; the matter is purely even). Hence:

* `tensorDeg_preserve_sum`, `tensorDeg_shift_right` (generic): `T ⊗ 1 + 1 ⊗ S` preserves the
  tensor grading if `T` and `S` preserve the factor gradings; `1 ⊗ S` shifts it if `S` does.
* `bZeroMode_preserve` — **proved**: the `B = L_1(sl₂)` current zero modes preserve `bDeg` (all of
  `B` sits in `R = 0`, and zero modes preserve conformal weight).
* `zeroModesPreserve_of_factors`: `ZeroModesPreserve Gh` from four factor statements:
  - `AZeroModesPreserveLayers` — the `A` current zero modes preserve the layers of `affineFlag`;
  - `UZeroModesPreserveLayers` — the `U` current zero modes preserve the layers of
    `auxiliaryFlag`;
  - the ghost current zero modes preserve `Gh.deg`;
  - the antighost zero modes map `Gh.deg i` to `Gh.deg (ghDown i)`.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly
open scoped TensorProduct

noncomputable section

/-! ### Generic tensor-operator lemmas -/

section Generic

universe u v w

variable {ι : Type w} [AddCommGroup ι]
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : Type v} [AddCommGroup W] [Module ℂ W]

theorem tensorDeg_induction (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W) (a : ι)
    (Φ : V ⊗[ℂ] W → Prop) (h0 : Φ 0) (hadd : ∀ x y, Φ x → Φ y → Φ (x + y))
    (hsmul : ∀ (c : ℂ) x, Φ x → Φ (c • x))
    (htmul : ∀ b, ∀ x ∈ dV b, ∀ y ∈ dW (a - b), Φ (x ⊗ₜ[ℂ] y)) :
    ∀ z ∈ tensorDeg dV dW a, Φ z := by
  intro z hz
  refine Submodule.iSup_induction _ (motive := Φ) hz ?_ h0 hadd
  intro b z hz
  rw [Submodule.map₂_eq_span_image2] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      exact htmul b x hx y hy
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

/-- `T ⊗ 1 + 1 ⊗ S` preserves the tensor grading. -/
theorem tensorDeg_preserve_sum (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W)
    (F : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W) (T : V →ₗ[ℂ] V) (S : W →ₗ[ℂ] W)
    (hF : ∀ x y, F (x ⊗ₜ[ℂ] y) = T x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] S y)
    (hT : ∀ i, ∀ x ∈ dV i, T x ∈ dV i) (hS : ∀ i, ∀ y ∈ dW i, S y ∈ dW i) (a : ι) :
    ∀ z ∈ tensorDeg dV dW a, F z ∈ tensorDeg dV dW a := by
  refine tensorDeg_induction dV dW a (fun z => F z ∈ tensorDeg dV dW a)
    (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
    (fun c x hx => by simpa only [map_smul] using Submodule.smul_mem _ c hx) ?_
  intro b x hx y hy
  rw [hF]
  have e : b + (a - b) = a := by abel
  refine Submodule.add_mem _ ?_ ?_
  · simpa only [e] using tmul_mem_tensorDeg dV dW (hT b x hx) hy
  · simpa only [e] using tmul_mem_tensorDeg dV dW hx (hS _ y hy)

/-- `1 ⊗ S` shifts the tensor grading by `δ` if `S` does. -/
theorem tensorDeg_shift_right (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W)
    (F : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W) (S : W →ₗ[ℂ] W) (δ : ι)
    (hF : ∀ x y, F (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] S y)
    (hS : ∀ i, ∀ y ∈ dW i, S y ∈ dW (i + δ)) (a : ι) :
    ∀ z ∈ tensorDeg dV dW a, F z ∈ tensorDeg dV dW (a + δ) := by
  refine tensorDeg_induction dV dW a (fun z => F z ∈ tensorDeg dV dW (a + δ))
    (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
    (fun c x hx => by simpa only [map_smul] using Submodule.smul_mem _ c hx) ?_
  intro b x hx y hy
  rw [hF]
  have e : b + (a - b + δ) = a + δ := by abel
  simpa only [e] using tmul_mem_tensorDeg dV dW hx (hS _ y hy)

end Generic

/-! ### The factor statements -/

/-- The `A` current zero mode. -/
def aZero (a : Fin 3) : Module.End ℂ ASpace := mode (ASVA.Y (aAction.current a)) 0

/-- The `B` current zero mode. -/
def bZero (a : Fin 3) : Module.End ℂ BSpace := mode (BSVA.Y (bAction.current a)) 0

/-- The `U` current zero mode. -/
def uZero (a : Fin 3) : Module.End ℂ USpace := mode (USVA.Y (uAction.current a)) 0

/-- The ghost current zero mode. -/
def ghZero (a : Fin 3) : Module.End ℂ Sl2GhostSpace := mode (ghostCurrentField a) 0

/-- The antighost zero mode `b_0` of the `a`-th pair. -/
def antiZero (a : Fin 3) : Module.End ℂ Sl2GhostSpace := mode (sl2GhostSVA.Y (bGhost a)) 0

/-- **OPEN (factor `A`)**: the current zero modes preserve the orthogonal layers of the corrected
flag. Mathematically: `J₀` preserves each corrected filtration step (Li-goodness of zero modes)
and is skew for the invariant form, hence preserves `F_p ∩ F_{p-1}^⊥`. -/
def AZeroModesPreserveLayers : Prop := ∀ a i, ∀ x ∈ aDeg i, aZero a x ∈ aDeg i

/-- **OPEN (factor `U`)**: the same for the ordinary PBW layers of `auxiliaryFlag`. -/
def UZeroModesPreserveLayers : Prop := ∀ a i, ∀ x ∈ uDeg i, uZero a x ∈ uDeg i

/-- The `B` current zero modes preserve `bDeg` (everything is in `R = 0`). -/
theorem bZero_preserve (a : Fin 3) (i : (ℤ × ℤ) × ℂ) (x : BSpace) (hx : x ∈ bDeg i) :
    bZero a x ∈ bDeg i := by
  unfold bDeg trivialDeg at hx ⊢
  split_ifs at hx ⊢ with h
  · have hw := BSVA.grading_mode (bAction.current a) (bAction.current_weight a) x hx 0
    have e : (1 : ℂ) + i.2 - ((0 : ℤ) : ℂ) - 1 = i.2 := by push_cast; ring
    rw [e] at hw
    exact hw
  · simp only [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem matter_mem_parity_zero (x : MatterSpace) : x ∈ matterSVA.parity 0 := by
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul w z =>
      induction w using TensorProduct.induction_on with
      | zero => rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
      | add w w' hw hw' => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ hw hw'
      | tmul x y =>
          have hx : x ∈ ASVA.parity 0 := by
            change x ∈ (ParityGrading.even ASpace).parity 0; simp [ParityGrading.even]
          have hy : y ∈ BSVA.parity (0 - 0) := by
            change y ∈ (ParityGrading.even BSpace).parity (0 - 0); simp [ParityGrading.even]
          have hz : z ∈ USVA.parity (0 - 0) := by
            change z ∈ (ParityGrading.even USpace).parity (0 - 0); simp [ParityGrading.even]
          exact TensorVA.tmul_mem_tenParity abSVA USVA
            (TensorVA.tmul_mem_tenParity ASVA BSVA hx hy) hz

/-- The matter current zero mode on pure triple tensors. -/
theorem matterZero_tmul (a : Fin 3) (x : ASpace) (y : BSpace) (z : USpace) :
    mode (matterSVA.Y (leeYangMatterAction.toAffineSl2Action.current a)) 0
        ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) =
      ((aZero a x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] bZero a y) ⊗ₜ[ℂ] z) +
        (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] uZero a z := by
  have h1 := tensorCurrentMode_tmul
    (tensorAffineAction aAction.toAffineSl2Action bAction.toAffineSl2Action
      aParityCompatible bParityCompatible abTensorGrading) uAction.toAffineSl2Action a 0
    (x ⊗ₜ[ℂ] y) z
  have h2 : mode ((TensorVA.tensorSVA ASVA BSVA aParityCompatible bParityCompatible
      abTensorGrading).Y ((tensorAffineAction aAction.toAffineSl2Action bAction.toAffineSl2Action
        aParityCompatible bParityCompatible abTensorGrading).current a)) 0 (x ⊗ₜ[ℂ] y) =
      aZero a x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] bZero a y :=
    tensorCurrentMode_tmul aAction.toAffineSl2Action bAction.toAffineSl2Action a 0 x y
  refine h1.trans ?_
  change mode ((TensorVA.tensorSVA ASVA BSVA aParityCompatible bParityCompatible
      abTensorGrading).Y ((tensorAffineAction aAction.toAffineSl2Action bAction.toAffineSl2Action
        aParityCompatible bParityCompatible abTensorGrading).current a)) 0 (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z +
      (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] uZero a z = _
  rw [h2]

theorem matterDeg_zero_preserve (hA0 : AZeroModesPreserveLayers)
    (hU0 : UZeroModesPreserveLayers) (a : Fin 3) (i : (ℤ × ℤ) × ℂ) :
    ∀ x ∈ matterDeg i,
      mode (matterSVA.Y (leeYangMatterAction.toAffineSl2Action.current a)) 0 x ∈ matterDeg i := by
  let AB : Module.End ℂ (ASpace ⊗[ℂ] BSpace) :=
    TensorProduct.map (aZero a) LinearMap.id + TensorProduct.map LinearMap.id (bZero a)
  have hAB : ∀ j, ∀ w ∈ tensorDeg aDeg bDeg j, AB w ∈ tensorDeg aDeg bDeg j :=
    tensorDeg_preserve_sum aDeg bDeg AB (aZero a) (bZero a)
      (fun x y => by simp [AB, TensorProduct.map_tmul]) (hA0 a)
      (fun j y hy => bZero_preserve a j y hy)
  exact tensorDeg_preserve_sum _ uDeg _ AB (uZero a)
    (fun w z => by
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' =>
          rw [TensorProduct.add_tmul, map_add, hw, hw', map_add, TensorProduct.add_tmul,
            TensorProduct.add_tmul]
          abel
      | tmul x y =>
          rw [matterZero_tmul]
          simp [AB, TensorProduct.map_tmul])
    hAB (hU0 a) i

/-- **`ZeroModesPreserve` from the factors.** -/
theorem zeroModesPreserve_of_factors {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA0 : AZeroModesPreserveLayers) (hU0 : UZeroModesPreserveLayers)
    (hG0 : ∀ a i, ∀ y ∈ Gh.deg i, ghZero a y ∈ Gh.deg i)
    (hb0 : ∀ a i, ∀ y ∈ Gh.deg i, antiZero a y ∈ Gh.deg (ghDown i)) :
    ZeroModesPreserve Gh := by
  intro a i x hx
  constructor
  · refine tensorDeg_preserve_sum matterDeg Gh.deg _
      (mode (matterSVA.Y (leeYangMatterAction.toAffineSl2Action.current a)) 0) (ghZero a)
      (fun m g => totalCurrentZero_tmul _ a m g) (matterDeg_zero_preserve hA0 hU0 a)
      (hG0 a) i x hx
  · have hshift : ∀ j, ghDown j = j + ((0, -1), 0) := by
      rintro ⟨⟨j1, j2⟩, j3⟩
      simp only [ghDown, Prod.mk_add_mk, add_zero]
      rfl
    rw [hshift]
    refine tensorDeg_shift_right matterDeg Gh.deg _ (antiZero a) ((0, -1), 0)
      (fun m g => ?_) (fun j y hy => by rw [← hshift]; exact hb0 a j y hy) i x hx
    rw [antighostZero_tmul a (matter_mem_parity_zero m) g]
    simp [koszul, antiZero]

end

end VOA.ConcreteHodge
