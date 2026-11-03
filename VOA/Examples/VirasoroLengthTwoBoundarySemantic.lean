/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroLengthTwoBoundary

/-!
# The conditional real-structure bridge for boundary Virasoro length two

This reusable bridge accepts an arbitrary `RealStructure` on a boundary simple Virasoro VOA and
proves that it automatically fixes the rational Virasoro tower generators.  More generally, every
step of the length filtration is stable because its defining creation monomials are fixed and
conjugation only changes their coefficients.  The canonical structure used by the bounded theorem
is constructed separately in `VirasoroBoundaryRealStructure`; no existence axiom is introduced.
-/

set_option linter.style.longLine false

namespace VOA

namespace VirGradedUnitarity

open VOA.VirModule VOA.VirSimple VOA.VirGoodFil
open VOA.VirQuotForm VOA.VertexOperatorAlgebra

variable {c : ℂ} (R : RealStructure (virasoroSimple c))

/-- A real structure commutes with every power of every Virasoro mode. -/
theorem rho_L_pow (k : ℤ) (r : ℕ)
    (x : VirUniv c ⧸ maxIdealVir c) :
    R.rho (((virasoroSimple c).L k ^ r) x) =
      ((virasoroSimple c).L k ^ r) (R.rho x) := by
  induction r with
  | zero => simp
  | succ r ih =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [R.rho_L, ih]

/-- Every quotient creation word has real structure constants and is fixed by `rho`. -/
theorem rho_mkQ_negWordVir (w : List ℕ) :
    R.rho ((maxIdealVir c).mkQ (negWordVir c w)) =
      (maxIdealVir c).mkQ (negWordVir c w) := by
  induction w with
  | nil => exact R.map_vacuum
  | cons i w ih =>
      rw [negWordVir_cons, ← virasoroVOA_L_eq_Lop, mkQ_L, R.rho_L, ih]

/-- The rational quasi-primary `Q_{2m}` is fixed after passage to the simple quotient. -/
theorem rho_lengthTwoQSimple (m : ℕ) :
    R.rho (lengthTwoQSimple c m) = lengthTwoQSimple c m := by
  rw [lengthTwoQSimple, lengthTwoQ_eq_explicit]
  simp only [map_add, map_smul, map_sum, R.map_add, R.antilinear]
  simp_rw [rho_mkQ_negWordVir R]
  simp
  rw [map_ofNat]

/-- Every retained boundary tower is fixed by any supplied real structure. -/
theorem rho_boundaryLengthLETwoTowerAt {n N : ℕ}
    (R : RealStructure (virasoroSimple (boundaryCharge n)))
    (m : BoundaryLengthLETwoTowerIndex n N) :
    R.rho (boundaryLengthLETwoTowerAt n N m) = boundaryLengthLETwoTowerAt n N m := by
  by_cases hm : m.1.1 = 1
  · rw [boundaryLengthLETwoTowerAt, dif_pos hm, boundaryLengthOneTowerAt,
      rho_L_pow, R.map_omega]
  · rw [boundaryLengthLETwoTowerAt, dif_neg hm, rho_L_pow,
      rho_lengthTwoQSimple]

/-- The real structure fixes the retained tower generating set pointwise. -/
theorem fixes_boundaryLengthLETwoTowerAt {n N : ℕ}
    (R : RealStructure (virasoroSimple (boundaryCharge n))) :
    R.Fixes (Set.range (boundaryLengthLETwoTowerAt n N)) := by
  rintro _ ⟨m, rfl⟩
  exact rho_boundaryLengthLETwoTowerAt R m

/-- The complex span of a pointwise-fixed family is stable under the anti-linear real structure. -/
theorem rho_mem_span_of_fixes_range {ι : Type*}
    (v : ι → (VirUniv c ⧸ maxIdealVir c))
    (hfix : ∀ i, R.rho (v i) = v i) {x : VirUniv c ⧸ maxIdealVir c}
    (hx : x ∈ Submodule.span ℂ (Set.range v)) :
    R.rho x ∈ Submodule.span ℂ (Set.range v) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [hfix i]
      exact Submodule.subset_span (Set.mem_range_self i)
  | zero => rw [R.map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [R.map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [R.antilinear]; exact Submodule.smul_mem _ _ hx

/-- In fact every step of the Virasoro length filtration is stable: its defining creation
monomials are fixed and complex conjugation only changes their coefficients.  This does not use
the length-two basis theorem. -/
theorem rho_mem_goodFil {p : ℕ} {N : ℤ}
    {x : VirUniv c ⧸ maxIdealVir c} (hx : x ∈ goodFil c p N) :
    R.rho x ∈ goodFil c p N := by
  rw [goodFil] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  rw [virFil] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨w, hw, henergy, hlength, rfl⟩ := hy
      refine ⟨negWordVir c w, Submodule.subset_span ?_, ?_⟩
      · exact ⟨w, hw, henergy, hlength, rfl⟩
      · exact (rho_mkQ_negWordVir R w).symm
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
      obtain ⟨y', hy'mem, hy'⟩ := hy
      obtain ⟨z', hz'mem, hz'⟩ := hz
      refine ⟨y' + z', Submodule.add_mem _ hy'mem hz'mem, ?_⟩
      rw [map_add, hy', hz', map_add, R.map_add]
  | smul a y _ hy =>
      obtain ⟨y', hy'mem, hy'⟩ := hy
      refine ⟨(starRingEnd ℂ) a • y', Submodule.smul_mem _ _ hy'mem, ?_⟩
      rw [map_smul, hy', map_smul, R.antilinear]

/-- Every step of the Virasoro graded flag is `rho`-stable for an arbitrary supplied real
structure.  Thus real-structure existence, not filtration compatibility, is the remaining datum. -/
theorem rhoStableOn_vir_pieceIn {p : ℕ} {N : ℤ} :
    RhoStableOn R ((virGradedFlag c).pieceIn p N) := by
  intro x hx
  have hrho : R.rho (x : VirUniv c ⧸ maxIdealVir c) ∈ goodFil c p N :=
    rho_mem_goodFil R hx
  have hgr : R.rho (x : VirUniv c ⧸ maxIdealVir c) ∈
      (virasoroSimple c).grading N := goodFil_le_grading c p N hrho
  exact ⟨⟨R.rho (x : VirUniv c ⧸ maxIdealVir c), hgr⟩, hrho, rfl⟩

/-- Consequently, the boundary length-two filtration step is stable under every supplied real
structure. -/
theorem rho_mem_goodFil_two {n N : ℕ} (hn : 2 ≤ n) (hN : 2 ≤ N)
    (R : RealStructure (virasoroSimple (boundaryCharge n)))
    {x : VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)}
    (hx : x ∈ goodFil (boundaryCharge n) 2 (N : ℤ)) :
    R.rho x ∈ goodFil (boundaryCharge n) 2 (N : ℤ) := by
  rw [goodFil_two_eq_span_boundaryTowers n N hn hN] at hx ⊢
  exact rho_mem_span_of_fixes_range R _ (rho_boundaryLengthLETwoTowerAt R) hx

/-- `RhoStableOn` for the `p=2` step, in the weight-space subtype used by graded unitarity. -/
theorem rhoStableOn_boundary_pieceIn_two {n N : ℕ} (hn : 2 ≤ n) (hN : 2 ≤ N)
    (R : RealStructure (virasoroSimple (boundaryCharge n))) :
    RhoStableOn R ((virGradedFlag (boundaryCharge n)).pieceIn 2 (N : ℤ)) := by
  intro x hx
  have hrho : R.rho (x : VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)) ∈
      goodFil (boundaryCharge n) 2 (N : ℤ) := rho_mem_goodFil_two hn hN R hx
  have hgr : R.rho (x : VirUniv (boundaryCharge n) ⧸ maxIdealVir (boundaryCharge n)) ∈
      (virasoroSimple (boundaryCharge n)).grading (N : ℤ) :=
    goodFil_le_grading (boundaryCharge n) 2 (N : ℤ) hrho
  exact ⟨⟨R.rho x, hgr⟩, hrho, rfl⟩

end VirGradedUnitarity

end VOA
