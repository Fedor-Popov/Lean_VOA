/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.KoszulConcreteBlocks
import VOA.Examples.TwoSeriesHodgeInputs

/-!
# Level-generic port: the symbol module `gr_r L_k(sl₂)`, leading Koszul data, blocks
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval VOA.InvariantSymbol
open VOA.GradedUnitaryCohomology VOA.LeeYangTransferAssembly Sl2CosetConcrete MvPolynomial
open VOA.LeadingKoszul DirectSum
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w uB

variable (L : CosetLevels)

/-! ## Port of `SymbolModelGr` -/


/-! ### The corrected filtration of `(ASpace L)`, all weights at once -/

/-- The corrected piece `F_p` of the simple affine factor (all conformal weights). -/
def aFil (p : ℕ) : Submodule ℂ (ASpace L) := ⨆ m : ℤ, (affineFlag L).piece p m

/-- `F_{p-1}`, with `F_{-1} = 0`. -/
def aFilLT : ℕ → Submodule ℂ (ASpace L)
  | 0 => ⊥
  | q + 1 => (aFil L) q

/-- **The nonnegative current modes preserve the corrected pieces.** -/
theorem aMode_aFil (a : Fin 3) (m : ℕ) (p : ℕ) : ∀ x ∈ (aFil L) p, (aMode L) a m x ∈ (aFil L) p := by
  intro x hx
  refine Submodule.iSup_induction _ (motive := fun x => (aMode L) a m x ∈ (aFil L) p) hx ?_
    (by beta_reduce; rw [map_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
  intro d y hy
  have h := (aMode_flag L) a m p d y hy
  rw [eN_natCast, add_zero] at h
  exact Submodule.mem_iSup_of_mem _ h

theorem aMode_aFilLT (a : Fin 3) (m : ℕ) (p : ℕ) : ∀ x ∈ (aFilLT L) p, (aMode L) a m x ∈ (aFilLT L) p := by
  cases p with
  | zero =>
    intro x hx
    rw [aFilLT, Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _
  | succ q => exact (aMode_aFil L) a m q

/-! ### The associated graded piece and its induced action -/

/-- The kernel `F_{r-1}` inside `F_r`. -/
def grKer (r : ℕ) : Submodule ℂ ((aFil L) r) := ((aFilLT L) r).comap ((aFil L) r).subtype

/-- **`gr_r A = F_r / F_{r-1}`** for the actual simple affine factor. -/
abbrev GrA (r : ℕ) : Type := (aFil L) r ⧸ (grKer L) r

/-- The restriction of `J^a_m` (`m ≥ 0`) to `F_r`. -/
def aModeRestr (r : ℕ) (k : Fin 3 × ℕ) : Module.End ℂ ((aFil L) r) :=
  ((aMode L) k.1 k.2).restrict ((aMode_aFil L) k.1 k.2 r)

theorem aModeRestr_ker (r : ℕ) (k : Fin 3 × ℕ) : (grKer L) r ≤ ((grKer L) r).comap ((aModeRestr L) r k) := by
  intro x hx
  exact (aMode_aFilLT L) k.1 k.2 r _ hx

/-- **The induced action** of the nonnegative current modes on `gr_r A`:
`(a, m) ↦ [J^a_m]`. -/
def grRho (r : ℕ) (k : Fin 3 × ℕ) : Module.End ℂ ((GrA L) r) :=
  ((grKer L) r).mapQ ((grKer L) r) ((aModeRestr L) r k) ((aModeRestr_ker L) r k)

@[simp] theorem grRho_mk (r : ℕ) (k : Fin 3 × ℕ) (x : (aFil L) r) :
    (grRho L) r k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(aMode L) k.1 k.2 x, (aMode_aFil L) k.1 k.2 r x x.2⟩ := rfl

/-- The conformal grading of `gr_r A`: the image of `(affineFlag L).piece r d`. -/
def grDeg (r : ℕ) (d : ℤ) : Submodule ℂ ((GrA L) r) :=
  (((affineFlag L).piece r d).comap ((aFil L) r).subtype).map ((grKer L) r).mkQ

/-! ### Commutation of the Cartan modes -/

/-! ### The two remaining inputs, on the concrete module -/

/-- **The leading Koszul embedding into the concrete `gr_r A ⊗ L_1`** (OPEN): an injective map
`H⁰(Q⁻)_{(2r,0)}(n) ↪ (gr_r A ⊗ L_1)^{g[t]}_n`. -/
structure GrKoszulEmbedding {K : Type*} [AddCommGroup K] [Module ℂ K] (C : KahlerComplex K)
    (n : ℤ) (r : ℕ) where
  ι : C.leadCohom (2 * (r : ℤ), 0) →ₗ[ℂ] (GrA L) r ⊗[ℂ] BSpace
  injective : Function.Injective ι
  inv : ∀ v, IsInv ((grRho L) r) bMode (ι v)
  weight : ∀ v, ι v ∈ tensorWeight ((grDeg L) r) bWeight n

/-! ### Input (A) at `r = 0` -/

/-! ### The endpoint -/

/-! ### Input (A) from strictness and cyclicity of an image -/


/-! ## Port of `SymbolModelKoszul` -/


/-! ### The concrete package on `gr_r A ⊗ L_1` -/

/-- The diagonal action `J^a_m ⊗ 1 + 1 ⊗ J^a_m` on `gr_r A ⊗ L_1`. -/
def grDiag (r : ℕ) (k : Fin 3 × ℕ) : Module.End ℂ ((GrA L) r ⊗[ℂ] BSpace) :=
  ((grRho L) r k).rTensor BSpace + (bMode k).lTensor ((GrA L) r)

theorem isInv_iff_grDiag (r : ℕ) (x : (GrA L) r ⊗[ℂ] BSpace) :
    IsInv ((grRho L) r) bMode x ↔ ∀ k, (grDiag L) r k x = 0 := Iff.rfl

/-- **The concrete leading Koszul data at weight `n`, degree `r`** (OPEN): a `LeadModel` of the
leading complex at `(2r, 0)`; Koszul `H₀` in `c`-count zero identified with `N0`, embedded
injectively in `gr_r A ⊗ L_1` in total weight `n`; Koszul `H₀` in `c`-count one embedded
injectively in `Π_{(a,m)} gr_r A ⊗ L_1`, so that `d̄_CE` becomes the diagonal action. -/
structure GrLeadKoszulData {K : Type*} [AddCommGroup K] [Module ℂ K] (C : KahlerComplex K)
    (n : ℤ) (r : ℕ) where
  X : ℕ → Type
  Y : ℕ → Type
  Z : ℕ → Type
  G : ℕ → Type
  [xacg : ∀ p, AddCommGroup (X p)]
  [xmod : ∀ p, Module ℂ (X p)]
  [yacg : ∀ p, AddCommGroup (Y p)]
  [ymod : ∀ p, Module ℂ (Y p)]
  [zacg : ∀ p, AddCommGroup (Z p)]
  [zmod : ∀ p, Module ℂ (Z p)]
  [gacg : ∀ p, AddCommGroup (G p)]
  [gmod : ∀ p, Module ℂ (G p)]
  Bc : LeadingBicomplex ℂ X Y Z G
  LM : LeadModel C Bc (2 * (r : ℤ), 0)
  N0 : Type
  [nacg : AddCommGroup N0]
  [nmod : Module ℂ N0]
  e0 : Bc.KH0 ≃ₗ[ℂ] N0
  j : N0 →ₗ[ℂ] (GrA L) r ⊗[ℂ] BSpace
  j_injective : Function.Injective j
  j_weight : ∀ y, j y ∈ tensorWeight ((grDeg L) r) bWeight n
  e1 : Bc.KH1 →ₗ[ℂ] (Fin 3 × ℕ → (GrA L) r ⊗[ℂ] BSpace)
  e1_injective : Function.Injective e1
  intertwine : ∀ v k, e1 (Bc.dbar v) k = (grDiag L) r k (j (e0 v))

attribute [instance] GrLeadKoszulData.xacg GrLeadKoszulData.xmod GrLeadKoszulData.yacg
  GrLeadKoszulData.ymod GrLeadKoszulData.zacg GrLeadKoszulData.zmod GrLeadKoszulData.gacg
  GrLeadKoszulData.gmod GrLeadKoszulData.nacg GrLeadKoszulData.nmod

section
variable {L}

/-- **Concrete Koszul data gives the Koszul embedding.** -/
def GrLeadKoszulData.toGrKoszulEmbedding {K : Type*} [AddCommGroup K] [Module ℂ K]
    {C : KahlerComplex K} {n : ℤ} {r : ℕ} (D : (GrLeadKoszulData L) C n r) :
    (GrKoszulEmbedding L) C n r where
  ι := D.j ∘ₗ (jointKer fun k => (grDiag L) r k ∘ₗ D.j).subtype ∘ₗ
    (leadCohomEquivJointKer D.LM D.e0 D.e1 D.e1_injective (fun k => (grDiag L) r k ∘ₗ D.j)
      D.intertwine).toLinearMap
  injective := D.j_injective.comp (Subtype.val_injective.comp (LinearEquiv.injective _))
  inv v := by
    have h := (leadCohomEquivJointKer D.LM D.e0 D.e1 D.e1_injective
      (fun k => (grDiag L) r k ∘ₗ D.j) D.intertwine v).2
    rw [mem_jointKer] at h
    exact ((isInv_iff_grDiag L) r _).mpr h
  weight v := D.j_weight _

end
/-- OPEN (leading Koszul data): the concrete Koszul data for the endpoint geometry. -/
abbrev EndpointGrLeadKoszul (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :=
  ∀ n (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (r : ℕ),
    (GrLeadKoszulData L) (((endpointKahler L) hA).model n hp) n r


/-! ## Port of `KoszulConcreteBlocks` -/


/-! ### The bigrading of a Kähler complex is internal -/

/-! ### Antighost-count blocks -/

/-! ### Specialization: the concrete Koszul data -/

section Concrete

variable {K : Type} [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K] {C : KahlerComplex K}

/-- **`(GrLeadKoszulData L)` from the antighost-count blocks.** The bicomplex and the `LeadModel`
are the actual block components of `Q⁻` (proved); only Koszul exactness `hK` and the symbol maps
`S` (with weight condition `hw`) are inputs. -/
def grLeadKoszulData_of_blocks (n : ℤ) (r : ℕ) (B : KoszulBlocks C)
    (hK : B.KExact (2 * (r : ℤ), 0))
    (S : B.KoszulSymbolMaps (2 * (r : ℤ), 0) ((GrA L) r ⊗[ℂ] BSpace) ((grDiag L) r))
    (hw : ∀ x, S.π0 x ∈ tensorWeight ((grDeg L) r) bWeight n) : (GrLeadKoszulData L) C n r where
  X := B.XB (2 * (r : ℤ), 0)
  Y := B.YB (2 * (r : ℤ), 0)
  Z := B.ZB (2 * (r : ℤ), 0)
  G := B.GB (2 * (r : ℤ), 0)
  Bc := B.bicomplex _ hK
  LM := B.leadModel _ hK rfl
  N0 := LinearMap.range S.π0
  e0 := S.e0 B hK
  j := (LinearMap.range S.π0).subtype
  j_injective := Subtype.val_injective
  j_weight y := by
    obtain ⟨x, hx⟩ := y.2
    rw [Submodule.subtype_apply, ← hx]
    exact hw x
  e1 := S.e1 B hK
  e1_injective := S.e1_injective B hK
  intertwine v k := S.intertwine_dbar B hK v k

end Concrete


end

end VOA.TwoSeries
