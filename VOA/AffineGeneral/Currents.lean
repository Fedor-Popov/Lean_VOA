/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov, Leonardo Rastelli
-/
import VOA.AffineGeneral.LieData
import VOA.Foundations.FormalCalculus
import VOA.Foundations.Locality

/-!
# Current fields on the universal affine vacuum module `V^k(𝔤)`

*General-`𝔤` port* of `VOA/Examples/AffineSl3VacuumCurrents.lean` (generated mechanically from that file):
the index type is `ι`, the Lie data is `D : LieData κ ι`, the dual Coxeter number is `D.h`.  Where the
text below says sl₃, `Fin 8`, `6` or `3`, read `𝔤`, `ι`, `2 * D.h` and `D.h`.

General-`𝔤` port of `VOA/Examples/AffineSl3VacuumCurrents.lean` (indices `ι`, Lie data `D`).

These endomorphisms act on the induced vacuum quotient itself, which is nonzero by
`AffineLie.vacuumVector_ne_zero` (relative PBW, through the theorem `VOA.pbw`). The
current commutator yields two-term delta locality with bound two, with the
actual matrix trace form and all eight structure constants. No PBW basis,
simple quotient, or vertex-algebra reconstruction is assumed.
-/
namespace VOA.AffineGeneral
open VOA VOA.AffineLie
noncomputable section

open LieData
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι)
/-- The vacuum module `V^k(𝔤)`. -/
abbrev Vacuum (k : ℂ) := vacuumSpace κ D.invariant k

set_option maxHeartbeats 4000000
set_option maxRecDepth 2048
/-- The affine current **mode** `J^a_m` on the *single* module `𝒱(𝔰𝔩₃, k)`: the action of the
loop generator `eₐ ⊗ tᵐ`. These are genuine endomorphisms of one module — the structure
constants and the central charge both act here. -/
noncomputable def J (k : ℂ) (a : ι) (m : ℤ) : Module.End ℂ (Vacuum D k) :=
  vacuumRho κ D.invariant k (ofLoop κ D.invariant (D.generator a) m)

/-- The current modes are linear in the colour, matching `∑_c (·) J^c`. -/
theorem J_eq (k : ℂ) (a : ι) (m : ℤ) :
    J D k a m = vacuumRho κ D.invariant k
      (ofLoop κ D.invariant (D.generator a) m) := rfl

/-- The loop element of the structure-constant bracket expands as a sum of basis loop modes:
`(⁅eₐ, e_b⁆) ⊗ tᵖ = ∑_c f^{ab}_c (e_c ⊗ tᵖ)`. -/
theorem ofLoop_bracket_eq (a b : ι) (p : ℤ) :
    ofLoop κ D.invariant ⁅D.generator a, D.generator b⁆ p
      = ∑ c, structureConstant D a b c • ofLoop κ D.invariant (D.generator c) p := by
  rw [← ofLoopₗ_apply, generator_bracket, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, ofLoopₗ_apply]

/-- **The FULL affine commutator on `𝒱(𝔰𝔩₃, k)` (the technical heart).**
On the *single* level-`k` vacuum module,
`⁅J^a_m, J^b_n⁆ = ∑_c f^{ab}_c J^c_{m+n} + m·k·κ(a,b)·δ_{m+n,0}·id`.
Both the non-abelian structure-constant term and the central term act on the **same** `End`.
Proof: `vacuumRho.map_lie` turns the operator commutator into `ρ ⁅eₐ⊗tᵐ, e_b⊗tⁿ⁆`; the
defining `affine_bracket` (Gannon §3.2.2) splits it into the loop bracket and the cocycle; the
loop bracket expands by `ofLoop_bracket_eq` into the `∑_c f^{ab}_c`-sum, and the cocycle term
acts as `k·id` via `vacuum_acts_central` — the genuine level-`k` centre. -/
theorem current_comm (k : ℂ) (a b : ι) (m n : ℤ) :
    J D k a m * J D k b n - J D k b n * J D k a m
      = (∑ c, structureConstant D a b c • J D k c (m + n))
        + (if m + n = 0 then ((m : ℂ) * k * formTable D a b) • LinearMap.id else 0) := by
  -- Operator commutator = ρ of the Lie bracket.
  have hml := (vacuumRho κ D.invariant k).map_lie
      (ofLoop κ D.invariant (D.generator a) m) (ofLoop κ D.invariant (D.generator b) n)
  rw [LieRing.of_associative_ring_bracket] at hml
  -- `J a m * J b n - J b n * J a m = vacuumRho ⁅eₐ⊗tᵐ, e_b⊗tⁿ⁆`.
  rw [J_eq, J_eq]
  rw [show vacuumRho κ D.invariant k (ofLoop κ D.invariant (D.generator a) m) * vacuumRho κ D.invariant k (ofLoop κ D.invariant (D.generator b) n)
        - vacuumRho κ D.invariant k (ofLoop κ D.invariant (D.generator b) n) * vacuumRho κ D.invariant k (ofLoop κ D.invariant (D.generator a) m)
      = vacuumRho κ D.invariant k ⁅ofLoop κ D.invariant (D.generator a) m, ofLoop κ D.invariant (D.generator b) n⁆ from hml.symm]
  -- Apply the affine bracket (Gannon §3.2.2).
  rw [affine_bracket κ D.invariant (D.generator a) (D.generator b) m n, map_add]
  congr 1
  · -- Structure-constant term: ρ ((⁅eₐ,e_b⁆) ⊗ t^{m+n}) = ∑_c f^{ab}_c J^c_{m+n}.
    rw [ofLoop_bracket_eq, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, J_eq]
  · -- Central term: ρ (if m+n=0 then m·κ(eₐ,e_b) • C) = if m+n=0 then m·k·κ(a,b) • id.
    by_cases hmn : m + n = 0
    · rw [if_pos hmn, if_pos hmn, map_smul, vacuum_acts_central, form_generator_eq_table,
        smul_smul]
      congr 1
      ring
    · rw [if_neg hmn, if_neg hmn, map_zero]

/-- The full affine commutator stated with the Lie bracket `⁅·,·⁆` of `End ℂ 𝒱(𝔰𝔩₃, k)`. -/
theorem current_lie_comm (k : ℂ) (a b : ι) (m n : ℤ) :
    ⁅J D k a m, J D k b n⁆
      = (∑ c, structureConstant D a b c • J D k c (m + n))
        + (if m + n = 0 then ((m : ℂ) * k * formTable D a b) • LinearMap.id else 0) := by
  rw [Ring.lie_def (J D k a m) (J D k b n)]; exact current_comm D k a b m n

/-! ## §6  The current fields and `(z₁-z₂)²` locality (bound `N = 2`) -/

/-- The **current field** `J^a(z) = ∑_m J^a_m z^{-m-1}` as a formal distribution of
`End ℂ 𝒱(𝔰𝔩₃, k)`. Its `zʲ`-coefficient is `J^a_{-j-1}`, so its `m`-th mode is `J^a_m`. -/
noncomputable def Jfield (k : ℂ) (a : ι) : FormalDist (Module.End ℂ (Vacuum D k)) :=
  fun j => J D k a (-j - 1)

/-- The coefficient index is the negative mode index minus one. -/
@[simp] theorem Jfield_apply (k : ℂ) (a : ι) (j : ℤ) : Jfield D k a j = J D k a (-j - 1) := rfl

/-- The modes of the current field are the current modes: `mode (J^a(z)) m = J^a_m`. -/
theorem Jfield_mode (k : ℂ) (a : ι) (m : ℤ) : mode (Jfield D k a) m = J D k a m := by
  rw [mode_apply, Jfield_apply, show -(-m - 1) - 1 = m from by ring]

/-- The **non-abelian OPE coefficient** `c⁰(z₂) = ∑_c f^{ab}_c J^c(z₂)`: the `∂⁰δ`-piece of the
commutator (the simple-pole / structure-constant term, `∼ 1/(z₁-z₂)`). -/
noncomputable def opeCoeff0 (k : ℂ) (a b : ι) :
    FormalDist (Module.End ℂ (Vacuum D k)) :=
  fun j => ∑ c, structureConstant D a b c • Jfield D k c j

/-- The **central OPE coefficient** `c¹(z₂) = k·κ(a,b)·id`: the `∂¹δ`-piece (the double-pole /
central term, `∼ k·κ(a,b)/(z₁-z₂)²`). -/
noncomputable def opeCoeff1 (k : ℂ) (a b : ι) :
    FormalDist (Module.End ℂ (Vacuum D k)) :=
  fun t => if t = 0 then (k * formTable D a b) • LinearMap.id else 0

/-- The commutator distribution of two current fields decomposes as a sum of a `∂⁰δ` term (the
non-abelian structure-constant currents) and a `∂¹δ` term (the central charge):
`[J^a(z₁), J^b(z₂)] = (∑_c f^{ab}_c J^c(z₂))·δ(z₁/z₂) + k·κ(a,b)·∂_{z₂}δ(z₁/z₂)`. -/
theorem bracketDist_Jfield_eq (k : ℂ) (a b : ι) :
    bracketDist (Jfield D k a) (Jfield D k b)
      = deltaDeriv 0 (opeCoeff0 D k a b) + deltaDeriv 1 (opeCoeff1 D k a b) := by
  refine FormalDist₂.ext fun m n => ?_
  rw [bracketDist_apply, Jfield_apply, Jfield_apply, current_comm]
  show (∑ c, structureConstant D a b c • J D k c ((-m - 1) + (-n - 1)))
      + (if (-m - 1) + (-n - 1) = 0 then
          (((-m - 1 : ℤ) : ℂ) * k * formTable D a b) • LinearMap.id else 0)
    = deltaDeriv 0 (opeCoeff0 D k a b) m n + deltaDeriv 1 (opeCoeff1 D k a b) m n
  rw [deltaDeriv_apply, deltaDeriv_apply]
  simp only [opeCoeff0, opeCoeff1]
  -- `(-m-1)+(-n-1) = -(m+n+2)`, and `J^c_{-(m+n+2)} = Jfield c (m+n+1)`.
  rw [Finset.range_zero, Finset.prod_empty, one_smul,
    Finset.range_one, Finset.prod_singleton, Nat.cast_zero, sub_zero, Nat.cast_one]
  congr 1
  · -- Structure-constant term.
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Jfield_apply, show -(m + n + 1 + 0) - 1 = -m - 1 + (-n - 1) from by ring]
  · -- Central term: index `(-m-1)+(-n-1)=0 ↔ m+n+1+1=0`, and scalar `(-m-1)`.
    by_cases hmn : (-m - 1) + (-n - 1) = 0
    · rw [if_pos hmn, if_pos (by omega : m + n + 1 + 1 = 0),
        ← Int.cast_smul_eq_zsmul ℂ (-m - 1 : ℤ)
          ((k * formTable D a b) • LinearMap.id : Module.End ℂ (Vacuum D k)),
        smul_smul, mul_assoc]
    · rw [if_neg hmn, if_neg (by omega : ¬ m + n + 1 + 1 = 0)]
      exact (smul_zero _).symm

/-- **Self/mutual locality with bound `N = 2`**: two factors of `(z₁-z₂)` annihilate the
commutator of any two current fields, `(z₁-z₂)²·[J^a(z₁), J^b(z₂)] = 0`. The commutator is the
sum of a `∂⁰δ` term (killed by `(z₁-z₂)¹`) and a `∂¹δ` central term (killed by `(z₁-z₂)²`);
both are killed by `mulBySubPow 2`. This is the Stage-1.5 input to the vertex-algebra locality
axiom VA4. -/
theorem Jfield_self_local (k : ℂ) (a b : ι) :
    mulBySubPow 2 (bracketDist (Jfield D k a) (Jfield D k b)) = 0 := by
  rw [bracketDist_Jfield_eq, map_add,
    mulBySubPow_deltaDeriv_eq_zero (by norm_num : 0 + 1 ≤ 2) (opeCoeff0 D k a b),
    mulBySubPow_deltaDeriv_eq_zero (by norm_num : 1 + 1 ≤ 2) (opeCoeff1 D k a b), add_zero]

/-- The current fields are **mutually local** (`Local` with `N = 2`) for every pair of colours
`a, b` — the locality hypothesis behind VA4. -/
theorem Jfield_local (k : ℂ) (a b : ι) : Local (Jfield D k a) (Jfield D k b) :=
  ⟨2, Jfield_self_local D k a b⟩


end
end VOA.AffineGeneral
