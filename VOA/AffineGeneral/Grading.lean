/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov, Leonardo Rastelli
-/
import VOA.AffineGeneral.Currents
import VOA.Core.Dong

/-!
# Positive grading and regularity of the universal affine vacuum `V^k(𝔤)`

*General-`𝔤` port* of `VOA/Examples/AffineSl3VacuumGrading.lean` (generated mechanically from that file):
the index type is `ι`, the Lie data is `D : LieData κ ι`, the dual Coxeter number is `D.h`.  Where the
text below says sl₃, `Fin 8`, `6` or `3`, read `𝔤`, `ι`, `2 * D.h` and `D.h`.

General-`𝔤` port of `VOA/Examples/AffineSl3VacuumGrading.lean`.  Vacuum nonvanishing is
`AffineLie.vacuumVector_ne_zero` (relative PBW), not a free-field realization.

General creation-word spanning gives the internal nonnegative integer energy
grading and finite-dimensional pieces. The bottom line is the vacuum line,
proved nonzero by `AffineLie.vacuumVector_ne_zero` (relative PBW, through the theorem `VOA.pbw`).
This cyclic vacuum quotient has a one-dimensional bottom.
Current mode covariance then implies lower truncation on all vacuum states.
No ordered-word independence or simple-quotient claim is made here.
-/
namespace VOA.AffineGeneral
open VOA VOA.AffineLie Module
noncomputable section

open LieData
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι)
set_option maxHeartbeats 4000000
set_option maxRecDepth 2048
/-- The energy operator `ℓ₀` on `Vacuum k` (the AffineLie `ell0Op`). -/
noncomputable def ell0OpA (k : ℂ) : End ℂ (Vacuum D k) :=
  ell0Op κ D.invariant k

/-- The VOA `ℤ`-grading on `Vacuum k`: the `ℓ₀`-eigenspace of eigenvalue `-n` (so the
energy-`d` piece is `grading d`, `|0⟩ ∈ grading 0`). -/
noncomputable def gradingZA (k : ℂ) (n : ℤ) : Submodule ℂ (Vacuum D k) :=
  Module.End.eigenspace (ell0OpA D k) (-(n : ℂ))

/-- The grading uses minus the affine degree eigenvalue. -/
theorem gradingZA_def (k : ℂ) (n : ℤ) :
    gradingZA D k n = Module.End.eigenspace (ell0OpA D k) (-(n : ℂ)) := rfl

/-- The reindexing `n : ℤ ↦ -(n : ℂ)` is injective: it distinguishes the VOA degrees. -/
theorem negCast_injective : Function.Injective (fun n : ℤ => (-(n : ℂ))) := by
  intro a b h
  simp only [neg_inj] at h
  exact_mod_cast h

/-- Off the image of `n ↦ -(n:ℂ)` — i.e. at any non-integer eigenvalue — the `ℓ₀`-eigenspace
is `⊥`. (Every nonzero energy is `-(d)` for `d : ℕ ⊆ ℤ`.) -/
theorem eigenspace_eq_bot_of_not_int (k : ℂ) (μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ -(n : ℂ)) :
    Module.End.eigenspace (ell0OpA D k) μ = ⊥ := by
  refine eigenspace_eq_bot_of_not_energy κ D.invariant k μ ?_
  intro d
  exact hμ (d : ℤ) ∘ (by intro h; rwa [Int.cast_natCast])

/-- **The `ℓ₀`-eigenspaces of `Vacuum k` are `iSupIndep`** — the spectral decomposition
of the energy operator. -/
theorem eigenspaces_iSupIndep_A (k : ℂ) :
    iSupIndep (fun μ : ℂ => Module.End.eigenspace (ell0OpA D k) μ) :=
  Module.End.eigenspaces_iSupIndep (ell0OpA D k)

/-- **The VOA grading is `iSupIndep`**: reindex the eigenspace independence along the
injection `n ↦ -(n:ℂ)`. -/
theorem gradingZA_iSupIndep (k : ℂ) : iSupIndep (gradingZA D k) :=
  (eigenspaces_iSupIndep_A D k).comp negCast_injective

/-- **The VOA grading spans `Vacuum k`**: every energy eigenspace appears at an integer
degree, and the eigenspaces span (`AffineLie.iSup_eigenspace_eq_top`). -/
theorem gradingZA_iSup_eq_top (k : ℂ) : ⨆ n : ℤ, gradingZA D k n = ⊤ := by
  rw [eq_top_iff, ← iSup_eigenspace_eq_top κ D.invariant k]
  refine iSup_le fun μ => ?_
  by_cases h : ∃ n : ℤ, μ = -(n : ℂ)
  · obtain ⟨n, rfl⟩ := h
    exact le_iSup (gradingZA D k) n
  · simp only [not_exists] at h
    rw [show ell0Op κ D.invariant k = ell0OpA D k from rfl,
      eigenspace_eq_bot_of_not_int D k μ h]
    exact bot_le

/-- **VA1/VA5 grading datum**: `Vacuum k` is the internal direct sum of its VOA-graded
pieces `gradingZA k n` (Gannon §3.2 `ℓ₀`-grading, reindexed to the VOA convention). -/
theorem gradingZA_isInternal (k : ℂ) : DirectSum.IsInternal (gradingZA D k) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradingZA_iSupIndep D k) (gradingZA_iSup_eq_top D k)

/-- Each VOA-graded piece is finite-dimensional (`AffineLie.eigenspace_finiteDimensional`
for finite-dimensional `𝔰𝔩₃`). -/
theorem gradingZA_finiteDimensional (k : ℂ) (n : ℤ) :
    FiniteDimensional ℂ (gradingZA D k n) :=
  eigenspace_finiteDimensional κ D.invariant k (-(n : ℂ))

/-- The **vacuum vector** `|0⟩ ∈ Vacuum k`. -/
noncomputable def vacuumA (k : ℂ) : Vacuum D k :=
  vacuumVector κ D.invariant k

/-- The vacuum is nonzero: `AffineLie.vacuumVector_ne_zero`, i.e. relative PBW (the
`affineVacuum` field of the theorem `VOA.pbw`). -/
theorem vacuumA_ne_zero (k : ℂ) : vacuumA D k ≠ 0 :=
  vacuumVector_ne_zero κ D.invariant k

/-- **Degree `0` is `ℂ·|0⟩`** (CFT-type, part 1): the top energy piece is spanned by the
vacuum (`AffineLie.eigenspace_zero_eq`). -/
theorem gradingZA_zero_eq_span_vacuum (k : ℂ) :
    gradingZA D k 0 = Submodule.span ℂ {vacuumA D k} := by
  rw [gradingZA_def, ell0OpA, show (-(0 : ℤ) : ℂ) = 0 from by norm_num,
    eigenspace_zero_eq κ D.invariant k]
  rfl

/-- The vacuum lies in degree `0`: `|0⟩ ∈ grading 0`. -/
theorem vacuumA_mem_gradingZA_zero (k : ℂ) : vacuumA D k ∈ gradingZA D k 0 := by
  rw [gradingZA_zero_eq_span_vacuum]
  exact Submodule.mem_span_singleton_self _

/-- **CFT-type, part 1** in the `Submodule.span` shape `ℂ ∙ |0⟩` (the `vacuum_grade` field). -/
theorem gradingZA_zero_eq_smul_vacuum (k : ℂ) :
    gradingZA D k 0 = (ℂ ∙ vacuumA D k) :=
  gradingZA_zero_eq_span_vacuum D k

/-- **CFT-type, part 2 / positivity**: `grading n = ⊥` for `n < 0` (the energies are `≥ 0`,
so there are no negative-energy = positive-degree-below-zero states). -/
theorem gradingZA_positivity (k : ℂ) (n : ℤ) (hn : n < 0) : gradingZA D k n = ⊥ := by
  rw [gradingZA_def]
  refine eigenspace_eq_bot_of_not_energy κ D.invariant k (-(n : ℂ)) ?_
  intro d hd
  -- `-(n:ℂ) = -(d:ℂ)` forces `n = d ≥ 0`, contradicting `n < 0`.
  have : (n : ℂ) = (d : ℂ) := by rw [neg_inj] at hd; exact hd
  have : n = (d : ℤ) := by exact_mod_cast this
  omega

/-! ## §B  The current fields are `IsField` (regularity / lower-truncation)

For the `nprod`/`dong_neg`/`goddard_uniqueness` machine the current fields `Jfield k a`
must be **fields**: lower-truncated on every state.  Via `Jfield k a j = J k a (-j-1)` this
is the regularity statement *high positive current modes annihilate every state*, which we
derive from the energy grading: `J^a_m` shifts the `ℓ₀`-energy by `-m` (it lands in degree
`(energy) - m`), and degrees below `0` vanish (`gradingZA_positivity`). -/

/-- **The energy shift of a current mode.**  `ell0Op (J^a_m v) = (m - energy(v))·(J^a_m v)`
when `v` is an `ell0Op`-eigenvector: `J^a_m` lowers the energy by `m`.  Stated as the
operator commutator `⁅ell0Op, J^a_m⁆ = m • J^a_m`. -/
theorem ell0Op_comm_J (k : ℂ) (a : ι) (m : ℤ) (v : Vacuum D k) :
    ell0OpA D k (J D k a m v) = J D k a m (ell0OpA D k v) + (m : ℂ) • J D k a m v := by
  rw [ell0OpA, ell0Op, J]
  rw [vacuumRho_comm κ D.invariant k (ell0 κ D.invariant)
    (ofLoop κ D.invariant (D.generator a) m) v]
  rw [ell0_lie_ofLoop, map_smul, LinearMap.smul_apply]

/-- A current mode maps the energy-`n` (degree-`n`) piece into the degree-`(n-m)` piece:
`J^a_m : gradingZA k n → gradingZA k (n - m)` (the VA1 mode-grading, restricted to currents). -/
theorem J_mem_gradingZA (k : ℂ) (a : ι) (m n : ℤ) {v : Vacuum D k}
    (hv : v ∈ gradingZA D k n) : J D k a m v ∈ gradingZA D k (n - m) := by
  rw [gradingZA_def, Module.End.mem_eigenspace_iff] at hv ⊢
  rw [ell0Op_comm_J, hv, map_smul]
  push_cast
  module

/-- **Regularity on graded pieces**: a current mode `J^a_m` with `m > n` annihilates the
energy-`n` piece (it would land in negative degree `n - m < 0`, which is `⊥`). -/
theorem J_gradingZA_eq_zero (k : ℂ) (a : ι) {m n : ℤ} (hmn : n < m) {v : Vacuum D k}
    (hv : v ∈ gradingZA D k n) : J D k a m v = 0 := by
  have hmem : J D k a m v ∈ gradingZA D k (n - m) := J_mem_gradingZA D k a m n hv
  rw [gradingZA_positivity D k (n - m) (by omega), Submodule.mem_bot] at hmem
  exact hmem

/-- **Regularity for an arbitrary state**: for every `x : Vacuum k` there is a bound `B`
with `J^a_m x = 0` for all `m ≥ B`.  Decompose `x` into finitely many graded pieces (the
internal direct sum is supported on finitely many degrees) and take `B` above the top one. -/
theorem J_regularity (k : ℂ) (a : ι) (x : Vacuum D k) :
    ∃ B : ℤ, ∀ m : ℤ, B ≤ m → J D k a m x = 0 := by
  classical
  -- Decompose `x` along the internal direct sum `gradingZA` (surjectivity of `coeAddMonoidHom`).
  obtain ⟨c, rfl⟩ := (gradingZA_isInternal D k).2 x
  -- `c : ⨁ n, gradingZA k n`; its support is a finite set of degrees, bounded above.
  obtain ⟨Dd, hD⟩ := Finset.exists_le c.support
  refine ⟨Dd + 1, fun m hm => ?_⟩
  rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun n hn => ?_
  exact J_gradingZA_eq_zero D k a (by have := hD n hn; omega : n < m) (c n).2

/-- **The current field is a field** (`IsField`): lower-truncated on every state.  Via
`Jfield k a j = J k a (-j-1)`, low `j` means high positive mode `-j-1`, killed by
regularity.  This is the VA5-regularity input that lets `Jfield k a` enter the
`nprod`/`dong_neg` reconstruction machine. -/
theorem Jfield_isField (k : ℂ) (a : ι) : IsField (Jfield D k a) := by
  intro x
  obtain ⟨B, hB⟩ := J_regularity D k a x
  refine ⟨-B, fun j hj => ?_⟩
  rw [Jfield_apply]
  exact hB (-j - 1) (by omega)


end
end VOA.AffineGeneral
