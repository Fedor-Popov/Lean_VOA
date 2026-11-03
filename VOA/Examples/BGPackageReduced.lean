/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BGPackageLambda

/-!
# The Beem–Garner package with `Λ` constructed, and the closed form of `E = [Λ, Q]`

With `Λ = lamBRST n` (`BGPackageLambda`), the operator `E = [Λ, Q]` has a closed form. The actual
BRST charge anticommutes with the actual antighost modes into the actual total current modes
(`brstQ_bB`: `{Q, b^a_{(k)}} = J^a_{tot,(k)}`, from the proved Cartan state identity and the
zero-mode commutator of the BRST superalgebra), hence

  `E = Σ_{m=1}^{N} (1/m) Σ_{a,b} K^{ab} (b^a_{(-m)} J^b_{tot,(m)} - J^a_{tot,(-m)} b^b_{(m)})`

(`brstE_eq`).

* `B_E_of_transpose` (generic): super-skewness of such an operator follows from `B`-skewness of
  the two mode families — for the antighosts **only for nonzero modes** (`k ≠ 0`).
* **DEAD END** `antighostZero_transpose_inconsistent`: skewness of the antighost **zero** modes,
  `B(b^a_{(0)} u, v) = -B(u, b^a_{(0)} v)` on ghost number `0`, is incompatible with `P_eq` at
  the vacuum for any positive product form (the relative vacuum would be `B`-isotropic, since
  `b^a_{(0)}(1 ⊗ c^a_0|0⟩) = 1 ⊗ |0⟩`). A global mode-transpose reduction of `B_E` must exclude
  `b_0` (and, by a hand computation recorded in the report, the full ghost current, whose modes
  contain `c_0 b_m`); the clause `B_E` is therefore kept as stated.
* `BGReducedData Gh hA BB RB` — the remaining data with `Λ` fixed: `B`, `ρ` with `P_eq`, `ρ_deg`,
  `ρ² = s`, `ρ_D` and `B_E` for the constructed `Λ`.
* `BGReducedData.toGlobal` — the global package (hence `InterpretedBGPackage`), with `Λ_maps`
  and `Λ_shift` **proved**.
* `leeYang_gradedUnitary_of_affine_bgReduced` and the specialization
  `leeYang_gradedUnitary_of_affine_bgReduced_colour` to `ghostFormC bgColourWeight` (`hG`, `hs`
  proved).

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### Generic algebra -/

section GenericRing

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The commutator of a Casimir contraction with an element `Q` whose anticommutators with the
two families are `T`, `T'`. -/
theorem casContract_comm_Q (Q : A) (X X' T T' : Fin 3 → A)
    (hX : ∀ a, Q * X a + X a * Q = T a) (hX' : ∀ a, Q * X' a + X' a * Q = T' a) :
    casContract X X' * Q - Q * casContract X X' = casContract X T' - casContract T X' := by
  have key : ∀ p q, X p * X' q * Q - Q * (X p * X' q) = X p * T' q - T p * X' q := by
    intro p q
    have h1 : Q * X p = T p - X p * Q := eq_sub_of_add_eq (hX p)
    have h2 : Q * X' q = T' q - X' q * Q := eq_sub_of_add_eq (hX' q)
    rw [← mul_assoc, h1, sub_mul, mul_assoc (X p) Q, h2, mul_sub, ← mul_assoc]
    abel
  unfold casContract
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← Finset.sum_sub_distrib, ← smul_sub, key]

end GenericRing

section GenericForm

variable {K : Type*} [AddCommGroup K] [Module ℂ K]

/-- The closed form of `E` on a module: `Σ_m c_m Σ K^{ab} (X^a_{-m} Y^b_m - Y^a_{-m} X^b_m)`. -/
def closedE (X Y : Fin 3 → ℤ → Module.End ℂ K) (S : Finset ℕ) (c : ℕ → ℂ) :
    Module.End ℂ K :=
  ∑ m ∈ S, c m • (casContract (fun a => X a (-(m : ℤ))) (fun b => Y b m) -
    casContract (fun a => Y a (-(m : ℤ))) (fun b => X b m))

/-- **Super-skewness of `E` from the mode transposes** (generic). -/
theorem B_E_of_transpose (B : LinearMap.BilinForm ℂ K) (G : ℤ → Submodule ℂ K)
    (X Y : Fin 3 → ℤ → Module.End ℂ K)
    (hYg : ∀ a k g, ∀ u ∈ G g, Y a k u ∈ G g)
    (hX : ∀ a k g, k ≠ 0 → ∀ u ∈ G g, ∀ v,
      B (X a k u) v = -((-1 : ℂ) ^ g) * B u (X a (-k) v))
    (hY : ∀ a k u v, B (Y a k u) v = -B u (Y a (-k) v))
    (S : Finset ℕ) (hS : ∀ m ∈ S, m ≠ 0) (c : ℕ → ℂ) (g : ℤ) (u : K) (hu : u ∈ G g) (v : K) :
    B (closedE X Y S c u) v = -((-1 : ℂ) ^ g) * B u (closedE X Y S c v) := by
  have t1 : ∀ p q (m : ℤ), m ≠ 0 →
      B (X p (-m) (Y q m u)) v = (-1 : ℂ) ^ g * B u (Y q (-m) (X p m v)) := by
    intro p q m hm
    rw [hX p (-m) g (neg_ne_zero.mpr hm) _ (hYg q m g u hu), neg_neg, hY]
    ring
  have t2 : ∀ p q (m : ℤ), m ≠ 0 →
      B (Y p (-m) (X q m u)) v = (-1 : ℂ) ^ g * B u (X q (-m) (Y p m v)) := by
    intro p q m hm
    rw [hY, neg_neg, hX q m g hm u hu]
    ring
  unfold closedE casContract
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.mul_apply, map_sum, map_smul, map_sub, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hS m hm
  simp only [t1 _ _ _ hm0, t2 _ _ _ hm0]
  have c00 : casimir 0 0 = 0 := rfl
  have c01 : casimir 0 1 = 1 := rfl
  have c02 : casimir 0 2 = 0 := rfl
  have c10 : casimir 1 0 = 1 := rfl
  have c11 : casimir 1 1 = 0 := rfl
  have c12 : casimir 1 2 = 0 := rfl
  have c20 : casimir 2 0 = 0 := rfl
  have c21 : casimir 2 1 = 0 := rfl
  have c22 : casimir 2 2 = 1 / 2 := rfl
  simp only [Fin.sum_univ_three, c00, c01, c02, c10, c11, c12, c20, c21, c22]
  ring

end GenericForm

section GenericSVA

universe uM
variable {M : Type uM} [AddCommGroup M] [Module ℂ M] {V : SuperVertexAlgebra M} {k : ℂ}

/-- The anticommutator of the BRST charge with every antighost mode (generic matter). -/
theorem semiInfiniteQ_antighost_mode (A : AffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)
    (hcomm : ZeroModeCommutator (matterGhostSVA V hV hg)) (a : Fin 3) (n : ℤ) :
    semiInfiniteQ A * mode (TensorVA.tenY V sl2GhostSVA (tensorAntighost V a)) n +
        mode (TensorVA.tenY V sl2GhostSVA (tensorAntighost V a)) n * semiInfiniteQ A =
      mode (TensorVA.tenY V sl2GhostSVA (totalCurrentState A a)) n := by
  have h := hcomm (brstState_odd A) (tensorAntighost_odd (V := V) a) n
  change semiInfiniteQ A * mode (TensorVA.tenY V sl2GhostSVA (tensorAntighost V a)) n -
      koszul 1 1 • (mode (TensorVA.tenY V sl2GhostSVA (tensorAntighost V a)) n *
        semiInfiniteQ A) =
    mode (TensorVA.tenY V sl2GhostSVA (semiInfiniteQ A (tensorAntighost V a))) n at h
  simpa only [koszul_one_one, neg_one_smul, sub_neg_eq_add, semiInfiniteQ_tensorAntighost]
    using h

end GenericSVA

/-! ### The modes on the BRST space -/

/-- The matter action of the Lee–Yang complex. -/
abbrev leeYangA : AffineSl2Action matterSVA (-4) := leeYangMatterAction.toAffineSl2Action

/-- The antighost mode `b^a_{(m)}` on the BRST space. -/
def bB (a : Fin 3) (m : ℤ) : Module.End ℂ BRSTSpace := (antiMode a m).lTensor MatterSpace

/-- The total current mode `J^a_{tot,(m)}` on the BRST space. -/
def JT (a : Fin 3) (m : ℤ) : Module.End ℂ BRSTSpace :=
  mode (TensorVA.tenY matterSVA sl2GhostSVA (totalCurrentState leeYangA a)) m

theorem bB_eq_mode (a : Fin 3) (m : ℤ) :
    bB a m = mode (TensorVA.tenY matterSVA sl2GhostSVA (tensorAntighost matterSVA a)) m := by
  apply TensorProduct.ext'
  intro x y
  rw [mode_apply]
  change _ = TensorVA.tenY matterSVA sl2GhostSVA (matterSVA.vacuum ⊗ₜ[ℂ] bGhost a) (-m - 1)
    (x ⊗ₜ[ℂ] y)
  rw [tenY_right_unit_parity matterSVA sl2GhostSVA (bGhost_odd a) (matter_mem_parity_zero x) y
    (-m - 1)]
  simp [bB, koszul, antiMode, gMode]

/-- **`{Q, b^a_{(m)}} = J^a_{tot,(m)}` on the BRST space.** -/
theorem brstQ_bB (a : Fin 3) (m : ℤ) : brstQ * bB a m + bB a m * brstQ = JT a m := by
  change semiInfiniteQ leeYangA * bB a m + bB a m * semiInfiniteQ leeYangA = JT a m
  rw [bB_eq_mode]
  exact semiInfiniteQ_antighost_mode leeYangA matterParityCompatible matterGhostTensorGrading
    (matterGhost_zeroModeCommutator leeYangMatterAction.translation
      matterParityCompatible matterGhostTensorGrading) a m

theorem bB_ghost (a : Fin 3) (m g : ℤ) (u : BRSTSpace) (hu : u ∈ leeYangBRSTComplex.ghost g) :
    bB a m u ∈ leeYangBRSTComplex.ghost (g - 1) := by
  rw [bB_eq_mode, mode_apply]
  have h := tenY_mem_matterGhostGrading matterSVA (tensorAntighost_ghost (V := matterSVA) a) hu
    (-m - 1)
  rwa [show -1 + g = g - 1 by ring] at h

theorem JT_ghost (a : Fin 3) (m g : ℤ) (u : BRSTSpace) (hu : u ∈ leeYangBRSTComplex.ghost g) :
    JT a m u ∈ leeYangBRSTComplex.ghost g := by
  rw [JT, mode_apply]
  have h := tenY_mem_matterGhostGrading matterSVA (totalCurrentState_ghost leeYangA a) hu
    (-m - 1)
  rwa [zero_add] at h

/-- `Λ` on the BRST space as a combination of BRST antighost modes. -/
theorem lamBRST_eq (n : ℤ) :
    lamBRST n = ∑ m ∈ Finset.Icc 1 n.toNat, (1 / (m : ℂ)) •
      casContract (fun a => bB a (-(m : ℤ))) (fun b => bB b m) := by
  apply TensorProduct.ext'
  intro x y
  simp only [lamBRST_tmul, lamG, lamTerm, casContract, bB, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, LinearMap.lTensor_tmul, TensorProduct.tmul_sum,
    TensorProduct.tmul_smul]

/-- `E = [Λ, Q]` on the BRST space. -/
def brstE (n : ℤ) : Module.End ℂ BRSTSpace := lamBRST n * brstQ - brstQ * lamBRST n

/-- **The closed form of `E = [Λ, Q]`.** -/
theorem brstE_eq (n : ℤ) :
    brstE n = closedE bB JT (Finset.Icc 1 n.toNat) (fun m => 1 / (m : ℂ)) := by
  have hterm : ∀ m : ℕ, casContract (fun a => bB a (-(m : ℤ))) (fun b => bB b m) * brstQ -
      brstQ * casContract (fun a => bB a (-(m : ℤ))) (fun b => bB b m) =
      casContract (fun a => bB a (-(m : ℤ))) (fun b => JT b m) -
        casContract (fun a => JT a (-(m : ℤ))) (fun b => bB b m) := fun m =>
    casContract_comm_Q brstQ _ _ _ _ (fun a => brstQ_bB a _) (fun a => brstQ_bB a _)
  apply LinearMap.ext
  intro z
  have hz : ∀ m : ℕ, casContract (fun a => bB a (-(m : ℤ))) (fun b => bB b m) (brstQ z) -
      brstQ (casContract (fun a => bB a (-(m : ℤ))) (fun b => bB b m) z) =
      casContract (fun a => bB a (-(m : ℤ))) (fun b => JT b m) z -
        casContract (fun a => JT a (-(m : ℤ))) (fun b => bB b m) z := fun m =>
    LinearMap.congr_fun (hterm m) z
  simp only [brstE, closedE, lamBRST_eq, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← smul_sub, hz]

/-! ### Dead end: the antighost zero modes are not `B`-skew -/

/-- **DEAD END (machine-checked).** No bilinear form `B` and conjugation `ρ` with `ρ_maps`,
`ρ_deg` and `P_eq` at weight `0` can make an antighost zero mode `B`-skew on ghost number `0`:
`B(b^a_{(0)} ρ|0⟩, 1 ⊗ c^a_0|0⟩) = 0` forces `B(ρ|0⟩, |0⟩) = 0`, contradicting positivity of the
product form at the vacuum. -/
theorem antighostZero_transpose_inconsistent
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (B : LinearMap.BilinForm ℂ BRSTSpace) (ρ : BRSTSpace →ₗ⋆[ℂ] BRSTSpace)
    (ρ_maps : ∀ x ∈ relativeWeight 0, ρ x ∈ relativeWeight 0)
    (ρ_deg : ∀ x ∈ relativeWeight 0, x ∈ brstDeg Gh ((0, 0), ((0 : ℤ) : ℂ)) →
      ρ x ∈ brstDeg Gh ((0, -0), ((0 : ℤ) : ℂ)))
    (P_eq : ∀ x ∈ relativeWeight 0, x ∈ brstDeg Gh ((0, 0), ((0 : ℤ) : ℂ)) →
      ∀ y ∈ relativeWeight 0, matterGhostForm hA BB RB PG x y = Complex.I ^ (0 : ℤ) * B (ρ x) y)
    (a : Fin 3)
    (B_b0 : ∀ u ∈ leeYangBRSTComplex.ghost 0, ∀ v,
      B (bB a 0 u) v = -((-1 : ℂ) ^ (0 : ℤ)) * B u (bB a 0 v)) : False := by
  set vac : BRSTSpace :=
    ((ASVA.vacuum ⊗ₜ[ℂ] BSVA.vacuum) ⊗ₜ[ℂ] USVA.vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum with hvac
  have hvdeg : vac ∈ brstDeg Gh ((0, 0), ((0 : ℤ) : ℂ)) := by
    rw [Int.cast_zero]; exact brstVacuum_mem_std hs
  have hvrel : vac ∈ relativeWeight 0 := by
    refine ⟨vacuum_mem_relativeCarrier leeYangA, ?_⟩
    have := brstDeg_le_weight Gh _ hvdeg
    simpa [wtIndex] using this
  have hρrel := ρ_maps vac hvrel
  have hρghost : ρ vac ∈ leeYangBRSTComplex.ghost 0 := by
    have := brstDeg_le_ghost Gh _ (ρ_deg vac hvrel hvdeg)
    simpa [ghIndex] using this
  set w : BRSTSpace :=
    ((ASVA.vacuum ⊗ₜ[ℂ] BSVA.vacuum) ⊗ₜ[ℂ] USVA.vacuum) ⊗ₜ[ℂ] cGhost a with hw
  have hbw : bB a 0 w = vac := by
    rw [hw, hvac, bB, LinearMap.lTensor_tmul]
    congr 1
    have := bGhost_cGhost_product a a 0 le_rfl
    simpa using this
  have hbρ : bB a 0 (ρ vac) = 0 := by
    have h := ((mem_relativeCarrier _ _).mp hρrel.1).2 a
    rwa [antighostZero_eq] at h
  have h1 := B_b0 (ρ vac) hρghost w
  rw [hbρ, hbw, map_zero, LinearMap.zero_apply] at h1
  have h2 : B (ρ vac) vac = 0 := by
    have : (-1 : ℂ) ^ (0 : ℤ) = 1 := zpow_zero _
    rw [this] at h1
    linear_combination h1
  have h3 := P_eq vac hvrel hvdeg vac hvrel
  rw [h2, mul_zero] at h3
  have hpos := weakGU_matterGhostForm hA hB hG
  have hne : vac ≠ 0 := by
    intro h0
    apply leeYangBRSTComplex_vacuum_not_exact
    have : brstSVA.vacuum = vac := rfl
    rw [this, h0]
    exact Submodule.zero_mem _
  obtain ⟨r, hr, hr'⟩ := hpos vac Submodule.mem_top hne
  rw [h3] at hr'
  have : (r : ℂ) = 0 := hr'.symm
  exact absurd (Complex.ofReal_eq_zero.mp this) hr.ne'

/-! ### The reduced package -/

/-- **The remaining Beem–Garner data**, with `Λ = lamBRST` constructed: a bilinear form and a
conjugation with `P_eq`, `ρ_deg`, `ρ² = s`, `ρ_D` and `B_E` for the constructed `Λ`. -/
structure BGReducedData {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) where
  B : LinearMap.BilinForm ℂ BRSTSpace
  ρ : BRSTSpace →ₗ⋆[ℂ] BRSTSpace
  ρ_maps : ∀ n : ℤ, ∀ x ∈ relativeWeight n, ρ x ∈ relativeWeight n
  P_eq : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ∀ y ∈ relativeWeight n, matterGhostForm hA BB RB PG x y = Complex.I ^ j * B (ρ x) y
  ρ_deg : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ρ x ∈ brstDeg Gh ((j, -g), (n : ℂ))
  s : ℂ
  hs : s ≠ 0
  ρ_sq : ∀ n : ℤ, ∀ x ∈ relativeWeight n, ρ (ρ x) = s • x
  κ : ℂ
  hκ : κ ≠ 0
  /-- `ρ Q = κ (-1)^{gh} [Λ, Q] ρ` on relative states. -/
  ρ_D : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ρ (brstQ x) = (κ * (-1 : ℂ) ^ g) • brstE n (ρ x)
  /-- Super-skewness of `B` for `E = [Λ, Q]` on relative states. -/
  B_E : ∀ (n j g : ℤ), ∀ u ∈ relativeWeight n, u ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ∀ v ∈ relativeWeight n, B (brstE n u) v = -((-1 : ℂ) ^ g) * B u (brstE n v)

namespace BGReducedData

variable {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
  {hA : GradedUnitary affineForm affineRealStructure affineFlag}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

/-- **The global package from the reduced data**, with `Λ = lamBRST` (for a standard ghost
grading). -/
def toGlobal (R : BGReducedData Gh hA BB RB) (hs : Gh.IsStd) : GlobalBGPackage Gh hA BB RB where
  Λ := lamBRST
  Λ_maps := fun n x hx => lamBRST_mem_relativeWeight n hx
  Λ_shift := fun n j g x _ hx => lamBRST_shift hs n j g _ hx
  B := R.B
  ρ := R.ρ
  ρ_maps := R.ρ_maps
  P_eq := R.P_eq
  ρ_deg := R.ρ_deg
  s := R.s
  hs := R.hs
  ρ_sq := R.ρ_sq
  κ := R.κ
  hκ := R.hκ
  ρ_D := fun n j g x hxr hx => by
    rw [R.ρ_D n j g x hxr hx]
    rfl
  B_E := fun n j g u hur hu v hv => R.B_E n j g u hur hu v hv

end BGReducedData

/-- **Affine GU ⇒ Lee–Yang GU from the reduced Beem–Garner data** (`Λ` constructed, `Λ_maps`,
`Λ_shift` proved), for an arbitrary positive ghost form with the standard grading.
`#print axioms`-clean, conditional on: `hA` (the hypothesis), `hB`, `hG`, `hs`, `R` (the reduced
data) and the downstream `symbols`, `character`, `vacuumNormalized`, `creationAdjoint`,
`wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_bgReduced
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (R : BGReducedData Gh hA BB RB)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB hG Gh hs
        ((R.toGlobal hs).toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized
      (sp2Kahler hA hB hG Gh hs
        ((R.toGlobal hs).toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2)
      (sp2GUData0 hA hB hG Gh hs
        ((R.toGlobal hs).toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2
        ((R.toGlobal hs).toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).conj0))
    (creationAdjoint : HarmonicCreationAdjoint
      (sp2Kahler hA hB hG Gh hs
        ((R.toGlobal hs).toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2)
      (sp2GUData0 hA hB hG Gh hs
        ((R.toGlobal hs).toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2
        ((R.toGlobal hs).toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).conj0))
    (wordsReal : HarmonicWordsReal
      (sp2Kahler hA hB hG Gh hs
        ((R.toGlobal hs).toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2)
      (sp2GUData0 hA hB hG Gh hs
        ((R.toGlobal hs).toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2
        ((R.toGlobal hs).toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).conj0)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_globalBGPackage hA hB hG Gh hs (R.toGlobal hs) symbols
    character vacuumNormalized creationAdjoint wordsReal

/-! ### The Beem–Garner colour-weighted ghost form -/

/-- The Beem–Garner colour-weighted ghost form: mode norms `n` for `b_{-n}`, `1/n` for `c_{-n}` on
the `e`, `f` colours, with the `b^h` norms doubled and the `c^h` norms halved. -/
abbrev bgPG : SesqForm Sl2GhostSpace := ghostFormC bgColourWeight

theorem bgPG_pos : IsPosOn bgPG ⊤ := ghostFormC_pos _ fun a s => bgColourWeight_pos a s

/-- The standard ghost grading, orthogonal for `bgPG`. -/
abbrev bgGh : GhostRGrading bgPG := ghostRGradingC bgColourWeight

theorem bgGh_isStd : bgGh.IsStd := ghostRGradingC_isStd _

/-- **Affine GU ⇒ Lee–Yang GU for the Beem–Garner colour-weighted ghost form** from the reduced
data; ghost positivity and the standard grading are proved. `#print axioms`-clean, conditional
on: `hA` (the hypothesis), `hB`, `R` (the reduced data for `bgGh`) and the downstream `symbols`,
`character`, `vacuumNormalized`, `creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_bgReduced_colour
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (R : BGReducedData bgGh hA BB RB)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd ((R.toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
        (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd ((R.toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
        (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((R.toGlobal bgGh_isStd).toInterpreted hB bgPG_pos (stdZ bgGh_isStd)
          (stdD hA hB bgGh_isStd)).sp2
        ((R.toGlobal bgGh_isStd).toInterpreted hB bgPG_pos (stdZ bgGh_isStd)
          (stdD hA hB bgGh_isStd)).conj0))
    (creationAdjoint : HarmonicCreationAdjoint
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd ((R.toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
        (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((R.toGlobal bgGh_isStd).toInterpreted hB bgPG_pos (stdZ bgGh_isStd)
          (stdD hA hB bgGh_isStd)).sp2
        ((R.toGlobal bgGh_isStd).toInterpreted hB bgPG_pos (stdZ bgGh_isStd)
          (stdD hA hB bgGh_isStd)).conj0))
    (wordsReal : HarmonicWordsReal
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd ((R.toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
        (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        ((R.toGlobal bgGh_isStd).toInterpreted hB bgPG_pos (stdZ bgGh_isStd)
          (stdD hA hB bgGh_isStd)).sp2
        ((R.toGlobal bgGh_isStd).toInterpreted hB bgPG_pos (stdZ bgGh_isStd)
          (stdD hA hB bgGh_isStd)).conj0)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_bgReduced hA hB bgPG_pos bgGh bgGh_isStd R symbols character
    vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
