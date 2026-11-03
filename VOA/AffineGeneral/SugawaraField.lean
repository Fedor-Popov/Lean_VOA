/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.AffineGeneral.Grading
import VOA.Core.ReconstructionExistence
import VOA.Core.FieldOps

/-!
# Quadratic Sugawara field on the actual sl3 vacuum

*General-`𝔤` port* of `VOA/Examples/AffineSl3SugawaraField.lean` (generated mechanically from that file):
the index type is `ι`, the Lie data is `D : LieData κ ι`, the dual Coxeter number is `D.h`.  Where the
text below says sl₃, `Fin 8`, `6` or `3`, read `𝔤`, `ι`, `2 * D.h` and `D.h`.

The field is defined from the actual inverse trace tensor and normal ordered
current pairs, with denominator 2(k+3). Its lower truncation follows from
that of the currents. The definitions exist even at critical level, where
Lean's inverse-of-zero convention gives zero; covariance will require
k+3 nonzero. No Virasoro or vertex-algebra axiom is asserted by definition.
-/
namespace VOA.AffineGeneral
open VOA Module
noncomputable section

open LieData
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι)
/-- **The Sugawara field** `T(z) = (1/(2(k+3))) ∑_{a,b} κ⁻¹(a,b) :J^a(z) J^b(z):`
(Gannon §5.2.2, eq. 5.2.6).  Each `:J^a J^b:` is `nprod (Jfield a) (Jfield b)`; the prefactor
`1/(2(k+h^∨)) = 1/(2(k+3))`. -/
noncomputable def sugawaraField (k : ℂ) : FormalDist (End ℂ (Vacuum D k)) :=
  (2 * (k + D.h))⁻¹ •
    ∑ a : ι, ∑ b : ι,
      kappaInv D a b • nprod (Jfield_isField D k a) (Jfield_isField D k b)

/-- A scalar multiple of a field is a field. -/
theorem IsField.smulC {k : ℂ} {f : FormalDist (End ℂ (Vacuum D k))} (hf : IsField f)
    (c : ℂ) : IsField (c • f) := by
  intro x
  obtain ⟨B, hB⟩ := hf x
  exact ⟨B, fun n hn => by
    show (c • f n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

/-- A finite sum of fields is a field (uniform lower-truncation bound over the finite index). -/
theorem IsField.finsetSum {k : ℂ} {ι : Type*} (s : Finset ι)
    (F : ι → FormalDist (End ℂ (Vacuum D k))) (hF : ∀ i ∈ s, IsField (F i)) :
    IsField (∑ i ∈ s, F i) := by
  classical
  intro x
  induction s using Finset.induction with
  | empty => exact ⟨0, fun n _ => by rw [Finset.sum_empty]; rfl⟩
  | insert i s hi ih =>
      obtain ⟨B₁, hB₁⟩ := hF i (Finset.mem_insert_self i s) x
      obtain ⟨B₂, hB₂⟩ := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      refine ⟨min B₁ B₂, fun n hn => ?_⟩
      rw [Finset.sum_insert hi]
      show (F i n + (∑ j ∈ s, F j) n) x = 0
      rw [LinearMap.add_apply, hB₁ n (by omega), hB₂ n (by omega), add_zero]

/-- The Sugawara field is a field (`IsField`): a finite ℂ-combination of `nprod`s of fields. -/
theorem sugawaraField_isField (k : ℂ) : IsField (sugawaraField D k) := by
  rw [sugawaraField]
  refine IsField.smulC D ?_ _
  refine IsField.finsetSum D _ _ fun a _ => ?_
  refine IsField.finsetSum D _ _ fun b _ => ?_
  exact IsField.smulC D (IsField.nprod (Jfield_isField D k a) (Jfield_isField D k b)) _

/-- **The Sugawara modes** `Lₙ := mode (T) (n+1) = T₍ₙ₊₁₎` (the conformal-weight-`2` shift,
`CONVENTIONS` §5), endomorphisms of `Vacuum k`. -/
noncomputable def Lsug (k : ℂ) (n : ℤ) : End ℂ (Vacuum D k) :=
  mode (sugawaraField D k) (n + 1)

/-- The mode index of a weight-two field is shifted by one. -/
theorem Lsug_def (k : ℂ) (n : ℤ) : Lsug D k n = mode (sugawaraField D k) (n + 1) := rfl

/-- **The conformal vector** `ω = L₋₂|0⟩`, the weight-`2` Sugawara state.  In the field
indexing `Lsug k (-2) = mode T (-1) = T₀`, so `ω = (sugawaraField k) 0 |0⟩` — the constant
term of `T(z)|0⟩`, the state created by the Sugawara field (Gannon §5.2.2). -/
noncomputable def omegaA (k : ℂ) : Vacuum D k := Lsug D k (-2) (vacuumA D k)

/-- The quadratic Sugawara state is the constant term on the vacuum. -/
theorem omegaA_eq (k : ℂ) : omegaA D k = (sugawaraField D k) 0 (vacuumA D k) := by
  rw [omegaA, Lsug_def, mode_apply, show -(-2 + 1) - 1 = (0 : ℤ) from by ring]


/-- The proposed translation operator is the Sugawara mode L minus one. -/
def Ltrans (k : ℂ) : End ℂ (Vacuum D k) := Lsug D k (-1)

/-- Translation is coefficient minus one of the quadratic field. -/
theorem Ltrans_eq (k : ℂ) : Ltrans D k=(sugawaraField D k) (-1) := by
  rw [Ltrans,Lsug_def,mode_apply]
  norm_num
/-- Negative powers of a current field kill the vacuum, by the nonnegative-mode
annihilation relations of the actual induced module. -/
theorem Jfield_vacuum_neg (k : ℂ) (a : ι) {q : ℤ} (hq : q < 0) :
    Jfield D k a q (vacuumA D k) = 0 := by
  exact AffineLie.vacuum_pos_annihilate κ D.invariant k (D.generator a)
    (-q-1) (by omega)

/-- The quadratic candidate translation annihilates the actual vacuum. -/
theorem Ltrans_vacuum (k : ℂ) : Ltrans D k (vacuumA D k) = 0 := by
  have hz : ∀ a b : ι,
      nprod (Jfield_isField D k a) (Jfield_isField D k b) (-1) (vacuumA D k) = 0 := by
    intro a b
    exact nprod_vacuum_neg_gen (Jfield_isField D k a) (Jfield_isField D k b) (vacuumA D k)
      (fun q hq => Jfield_vacuum_neg D k a hq) (fun q hq => Jfield_vacuum_neg D k b hq) (by norm_num)
  rw [Ltrans_eq, sugawaraField]
  show (2 * (k + D.h))⁻¹ • (Reconstruction.evalAt (-1) (vacuumA D k)
      (∑ a : ι, ∑ b : ι,
        kappaInv D a b • nprod (Jfield_isField D k a) (Jfield_isField D k b))) = 0
  refine smul_eq_zero_of_right _ ?_
  rw [map_sum]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  rw [map_sum]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [map_smul]
  show kappaInv D a b • (nprod (Jfield_isField D k a) (Jfield_isField D k b) (-1) (vacuumA D k)) = 0
  rw [hz a b, smul_zero]
end
end VOA.AffineGeneral
