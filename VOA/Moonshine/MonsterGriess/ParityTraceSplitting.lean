/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), file:
  CFSG/Monster/Parity/TraceSplitting.lean
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.GriessTrilinear
import Mathlib.LinearAlgebra.Trace

/-!
# Axiom's Monster port (parity-centralizer closure): parity automorphisms split `SpaceB`

`IsParityAut f` — `f ∈ GL_ℚ(SpaceB)` preserves the Griess product, the form, and commutes with
the parity involution `xB`.  For `u` with no spinor part, `Lw u : SpaceW → SpaceW` is the action
`N ↦ (u * N)_W`; its trace form is
`tr(Lw u ∘ Lw v) = 4096 · bform u v + 512 · sigmaF u v` (`trace_Lw_eq_bform_sigmaF`), where
`sigmaF u v = 5 tr(A_u) tr(A_v) + x_u · x_v`.  A parity automorphism conjugates `Lw` and therefore
preserves `sigmaF` (`sigmaF_map`) and the operator `phiOp` (`phiOp_map`), whence it preserves the
blocks `scalarLine = ℚ·1`, `subA = symMat`, `subX = SpaceX` (`map_scalarLine`, `map_subA`,
`map_subX`), and `SpaceW` (`apply_inW`, `resWEquiv`).

## Port notes
* Namespace `CFSG.Monster.Parity` ↦ `VOA.Moonshine.MonsterGriess.Parity`.  Module-system syntax
  and the source's `attribute [-instance] …` line dropped.  Bodies verbatim except as listed.
* `phi0` is a function in our port (`Short.lean`): in `ne_zero_of_isShortCoord`, `map_zero` is
  applied after `← phi0Lin_apply`.
* Renamed use: the source's `qf_zero` ↦ our `qf_zero_mat` (`GriessTrilinear.lean`).
* Drift: `dite_eq_left h` ↦ `dif_pos h`; `ite_eq_left h`/`ite_eq_right h` ↦ `if_pos h`/`if_neg h`;
  `Basis` ↦ `Module.Basis`.
* Omitted (not reached): `gmul_inA_inW`, `gmul_inA_tensor`, `gmul_Xlift_inW`,
  `gmul_Xlift_tensor`, `trace_Lw_mul_Lw_split`, `tracelessA`, `subW` and their invariance,
  `mem_iff_of_maps`, and the summary theorem `parity_centralizer_trace_splitting`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.MonsterGriess.Parity

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
  VOA.Moonshine.MonsterGriess.SpinLattice Matrix Module

theorem classOf_ne_zero_of_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : classOf u ≠ 0 := by
  intro h
  simp only [classOf, dif_pos hu.1] at h
  rw [Submodule.Quotient.mk_eq_zero, mem_two_range_iff] at h
  obtain ⟨w, hw⟩ := h
  have hw' : (2 : ℤ) • (w : Fin 24 → ℤ) = u := hw
  have hw0 : (w : Fin 24 → ℤ) ≠ 0 := fun h0 => minVecs_ne_zero hu (by rw [← hw', h0, smul_zero])
  have h32 := normSq_ge w.2 hw0
  have hu32 := (mem_minVecs_iff.1 hu).2
  rw [← hw', normSq_two_smul] at hu32
  omega

theorem ne_zero_of_isShortCoord {p : C × Cocode} (h : IsShortCoord p) : p ≠ 0 := by
  rintro rfl
  obtain ⟨u, hu, hcl⟩ := h
  rw [← phi0Lin_apply, map_zero] at hcl
  exact classOf_ne_zero_of_minVecs hu hcl

theorem trace_Rmat (c : ShortIdx) : trace (Rmat c) = 0 := by
  rw [Rmat, trace_qmatR (two_ne_zero : (2 : ℚ) ≠ 0)]
  exact if_neg fun h => ne_zero_of_isShortCoord c.2 (Prod.ext h.1 h.2)

theorem trace_Rmat_mul_Rmat (c d : ShortIdx) :
    trace (Rmat c * Rmat d) = if c = d then 4096 else 0 := by
  have h := trace_transpose_TDR_mul (two_ne_zero : (2 : ℚ) ≠ 0) c.1 d.1
  rw [TDR_eq_qmatR, TDR_eq_qmatR] at h
  change trace ((Rmat c)ᵀ * Rmat d) = _ at h
  rw [Rmat_symm] at h
  rw [h]
  by_cases hcd : c = d
  · rw [if_pos (congrArg Subtype.val hcd), if_pos hcd]
  · rw [if_neg (fun h' => hcd (Subtype.ext h')), if_neg hcd]

noncomputable def inWₗ : SpaceW →ₗ[ℚ] SpaceB :=
  LinearMap.inr ℚ symMat (SpaceX × SpaceW) ∘ₗ LinearMap.inr ℚ SpaceX SpaceW

theorem inWₗ_apply (N : SpaceW) : inWₗ N = inW N := rfl

/-- `Lw u : N ↦ (u * N)_W`. -/
noncomputable def Lw (u : SpaceB) : Module.End ℚ SpaceW := projW ∘ₗ gmul u ∘ₗ inWₗ

theorem Lw_apply (u : SpaceB) (N : SpaceW) : Lw u N = (gmul u (inW N)).2.2 := rfl

theorem gmulWHalf_inW_left (N : SpaceW) (u : SpaceB) : gmulWHalf (inW N) u = 0 := by
  simp [gmulWHalf]

theorem Lw_apply' (u : SpaceB) (N : SpaceW) :
    Lw u N = (trace (Am u) / 8) • N + N * Am u +
      (8 : ℚ)⁻¹ • ∑ c, xs u c • (Rmat c * N - (4 : ℚ)⁻¹ • (Rmat c * N * Umat c)) := by
  change gmulWHalf u (inW N) + gmulWHalf (inW N) u = _
  rw [gmulWHalf_inW_left, add_zero]
  rfl

theorem gmul_inW_eq {u : SpaceB} (hu : Nm u = 0) (N : SpaceW) :
    gmul u (inW N) = inW (Lw u N) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun c => ?_) rfl)
  · change gmulA u (inW N) = 0
    simp [gmulA, hu]
  · change gmulX u (inW N) c = 0
    simp [gmulX, hu, qf_zero_mat]

theorem sum_smul_single_smul {M : Type*} [AddCommGroup M] [Module ℚ M] (c₀ : ShortIdx) (a : ℚ)
    (F : ShortIdx → M) : ∑ c, (a • (Pi.single c₀ 1 : SpaceX)) c • F c = a • F c₀ := by
  rw [Finset.sum_eq_single c₀]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

noncomputable def lr (P : Matrix SpinIdx SpinIdx ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    Module.End ℚ SpaceW where
  toFun N := P * N * M
  map_add' N N' := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c N := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem lr_apply (P : Matrix SpinIdx SpinIdx ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ) (N : SpaceW) :
    lr P M N = P * N * M := rfl

theorem lr_mul_lr (P P' : Matrix SpinIdx SpinIdx ℚ) (M M' : Matrix (Fin 24) (Fin 24) ℚ) :
    lr P M * lr P' M' = lr (P * P') (M' * M) := by
  refine LinearMap.ext fun N => ?_
  rw [Module.End.mul_apply, lr_apply, lr_apply, lr_apply]
  simp only [Matrix.mul_assoc]

private noncomputable def wEquiv : SpaceW ≃ₗ[ℚ] (SpinIdx × Fin 24 → ℚ) where
  toFun N k := N k.1 k.2
  invFun f := Matrix.of fun i j => f (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem wEquiv_symm_single (k : SpinIdx × Fin 24) :
    wEquiv.symm (Pi.single k 1) = Matrix.single k.1 k.2 (1 : ℚ) := by
  obtain ⟨a, b⟩ := k
  ext i j
  change (Pi.single (a, b) (1 : ℚ) : SpinIdx × Fin 24 → ℚ) (i, j) = _
  rw [Pi.single_apply, Matrix.single_apply]
  by_cases h1 : a = i
  · by_cases h2 : b = j
    · subst h1 h2
      simp
    · rw [if_neg (fun h => h2 (congrArg Prod.snd h).symm), if_neg (fun h => h2 h.2)]
  · rw [if_neg (fun h => h1 (congrArg Prod.fst h).symm), if_neg (fun h => h1 h.1)]

theorem trace_eq_sum (F : Module.End ℚ SpaceW) :
    LinearMap.trace ℚ SpaceW F = ∑ k : SpinIdx × Fin 24, F (Matrix.single k.1 k.2 1) k.1 k.2 := by
  rw [LinearMap.trace_eq_matrix_trace ℚ (Basis.ofEquivFun wEquiv), Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Basis.ofEquivFun_repr_apply,
    Basis.coe_ofEquivFun]
  change wEquiv (F (wEquiv.symm (Pi.single k 1))) k = _
  rw [wEquiv_symm_single]
  rfl

theorem lr_single_apply (P : Matrix SpinIdx SpinIdx ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ)
    (i : SpinIdx) (j : Fin 24) : (P * Matrix.single i j (1 : ℚ) * M) i j = P i i * M j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [mul_single_apply_same, mul_one]
  · intro b _ hb
    rw [mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
  · simp

theorem trace_lr (P : Matrix SpinIdx SpinIdx ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    LinearMap.trace ℚ SpaceW (lr P M) = trace P * trace M := by
  rw [trace_eq_sum, Fintype.sum_prod_type]
  simp only [lr_apply, lr_single_apply]
  rw [Matrix.trace, Matrix.trace, Finset.sum_mul_sum]
  rfl

noncomputable def MA (A : Matrix (Fin 24) (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ :=
  A + (trace A / 8) • (1 : Matrix (Fin 24) (Fin 24) ℚ)

noncomputable def Kc (c : ShortIdx) : Matrix (Fin 24) (Fin 24) ℚ :=
  1 - (4 : ℚ)⁻¹ • Umat c

theorem Lw_eq (u : SpaceB) :
    Lw u = lr 1 (MA (Am u)) + ∑ c, (xs u c / 8) • lr (Rmat c) (Kc c) := by
  refine LinearMap.ext fun N => ?_
  rw [Lw_apply', LinearMap.add_apply, LinearMap.sum_apply, lr_apply, MA, Matrix.one_mul,
    Finset.smul_sum]
  simp only [LinearMap.smul_apply, lr_apply, Kc, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_smul, Matrix.mul_add]
  congr 1
  · exact add_comm _ _
  · refine Finset.sum_congr rfl fun c _ => ?_
    module

theorem trace_MA_mul_MA (A B : Matrix (Fin 24) (Fin 24) ℚ) :
    trace (MA B * MA A) = trace (A * B) + 5 / 8 * trace A * trace B := by
  simp only [MA, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, trace_add, trace_smul, trace_one, Fintype.card_fin,
    smul_eq_mul]
  rw [trace_mul_comm B A]
  push_cast
  ring

theorem Umat_mul_Umat (c : ShortIdx) : Umat c * Umat c = (32 : ℚ) • Umat c := by
  rw [Umat, vecMulVec_mul_vecMulVec, uQ_dotProduct_self, vecMulVec_smul]

theorem trace_Umat (c : ShortIdx) : trace (Umat c) = 32 := by
  rw [Umat, trace_vecMulVec, uQ_dotProduct_self]

theorem trace_Kc_mul_Kc (c : ShortIdx) : trace (Kc c * Kc c) = 72 := by
  simp only [Kc, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, Umat_mul_Umat, smul_smul, trace_sub, trace_smul, trace_one, Fintype.card_fin,
    trace_Umat, smul_eq_mul]
  norm_num

theorem trace_one_spin : trace (1 : Matrix SpinIdx SpinIdx ℚ) = 4096 := by
  rw [trace_one, card_spinIdx]
  norm_num

theorem sum_sum_trace_Rmat (x y : SpaceX) :
    ∑ c, ∑ d, y d / 8 * (x c / 8 * (trace (Rmat c * Rmat d) * trace (Kc d * Kc c))) =
      4608 * (x ⬝ᵥ y) := by
  rw [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single c]
  · rw [trace_Rmat_mul_Rmat, if_pos rfl, trace_Kc_mul_Kc]
    ring
  · intro d _ hd
    rw [trace_Rmat_mul_Rmat, if_neg (Ne.symm hd), zero_mul, mul_zero, mul_zero]
  · simp

theorem trace_Lw_mul_Lw (u v : SpaceB) :
    LinearMap.trace ℚ SpaceW (Lw u * Lw v) =
      4096 * (trace (Am u * Am v) + 5 / 8 * trace (Am u) * trace (Am v)) +
        4608 * (xs u ⬝ᵥ xs v) := by
  rw [Lw_eq u, Lw_eq v, add_mul, mul_add, mul_add, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_mul_sum]
  simp only [mul_smul_comm, smul_mul_assoc, lr_mul_lr, map_add, map_sum,
    map_smul, trace_lr, smul_eq_mul, Matrix.one_mul, Matrix.mul_one, trace_Rmat, zero_mul,
    mul_zero, Finset.sum_const_zero, add_zero, zero_add, trace_one_spin, trace_MA_mul_MA,
    sum_sum_trace_Rmat]

noncomputable def oneA : symMat := ⟨1, transpose_one⟩

theorem coe_oneA : (oneA : Matrix (Fin 24) (Fin 24) ℚ) = 1 := rfl

theorem coe_smul_oneA (c : ℚ) :
    ((c • oneA : symMat) : Matrix (Fin 24) (Fin 24) ℚ) = c • (1 : Matrix (Fin 24) (Fin 24) ℚ) :=
  rfl

/-- ⭐ **Parity automorphisms**: `ℚ`-linear automorphisms of `SpaceB` preserving the Griess
product and the form and commuting with the parity involution `xB`. -/
structure IsParityAut (f : SpaceB ≃ₗ[ℚ] SpaceB) : Prop where
  map_gmul : ∀ u v, f (gmul u v) = gmul (f u) (f v)
  map_bform : ∀ u v, bform (f u) (f v) = bform u v
  map_xB : ∀ u, f (xB u) = xB (f u)

noncomputable def resW (f : SpaceB ≃ₗ[ℚ] SpaceB) : Module.End ℚ SpaceW :=
  projW ∘ₗ f.toLinearMap ∘ₗ inWₗ

theorem resW_apply (f : SpaceB ≃ₗ[ℚ] SpaceB) (N : SpaceW) : resW f N = (f (inW N)).2.2 := rfl

noncomputable def sigmaF (u v : SpaceB) : ℚ :=
  5 * trace (Am u) * trace (Am v) + xs u ⬝ᵥ xs v

noncomputable def phiOp (u : SpaceB) : SpaceB := ((5 * trace (Am u)) • oneA, xs u, 0)

theorem bform_phiOp (u v : SpaceB) : bform (phiOp u) v = sigmaF u v := by
  rw [bform_apply, sigmaF]
  change trace ((5 * trace (Am u)) • (1 : Matrix (Fin 24) (Fin 24) ℚ) * Am v) +
    ∑ c, xs u c * xs v c + ∑ j, ∑ i, (0 : SpaceW) j i * v.2.2 j i = _
  simp only [Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul, Matrix.zero_apply,
    zero_mul, Finset.sum_const_zero, add_zero, dotProduct]

theorem bform_of_Nm (u v : SpaceB) (hv : Nm v = 0) :
    bform u v = trace (Am u * Am v) + xs u ⬝ᵥ xs v := by
  rw [bform_apply]
  change _ + _ + ∑ j, ∑ i, u.2.2 j i * (Nm v) j i = _
  rw [hv]
  simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, dotProduct]

theorem trace_Lw_eq_bform_sigmaF (u : SpaceB) {v : SpaceB} (hv : Nm v = 0) :
    LinearMap.trace ℚ SpaceW (Lw u * Lw v) = 4096 * bform u v + 512 * sigmaF u v := by
  rw [trace_Lw_mul_Lw, bform_of_Nm u v hv, sigmaF]
  ring

namespace IsParityAut

variable {f : SpaceB ≃ₗ[ℚ] SpaceB}

theorem symm (hf : IsParityAut f) : IsParityAut f.symm :=
  ⟨fun u v => f.injective (by
      rw [LinearEquiv.apply_symm_apply, hf.map_gmul, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]),
    fun u v => by rw [← hf.map_bform, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply],
    fun u => f.injective (by
      rw [LinearEquiv.apply_symm_apply, hf.map_xB, LinearEquiv.apply_symm_apply])⟩

theorem map_W (hf : IsParityAut f) {u : SpaceB} (hu : u.1 = 0 ∧ u.2.1 = 0) :
    (f u).1 = 0 ∧ (f u).2.1 = 0 := by
  have hx : xB u = (-1 : ℚ) • u := End.mem_eigenspace_iff.1 (mem_eigenspace_xB_neg_one.2 hu)
  refine mem_eigenspace_xB_neg_one.1 (End.mem_eigenspace_iff.2 ?_)
  change xB (f u) = (-1 : ℚ) • f u
  rw [← hf.map_xB, hx, map_smul]

theorem map_AX (hf : IsParityAut f) {u : SpaceB} (hu : Nm u = 0) : Nm (f u) = 0 := by
  have hx : xB u = (1 : ℚ) • u := End.mem_eigenspace_iff.1 (mem_eigenspace_xB_one.2 hu)
  refine mem_eigenspace_xB_one.1 (End.mem_eigenspace_iff.2 ?_)
  change xB (f u) = (1 : ℚ) • f u
  rw [← hf.map_xB, hx, map_smul]

theorem apply_inW (hf : IsParityAut f) (N : SpaceW) : f (inW N) = inW (resW f N) := by
  obtain ⟨h1, h2⟩ := hf.map_W (u := inW N) ⟨rfl, rfl⟩
  exact Prod.ext h1 (Prod.ext h2 rfl)

theorem resW_resW_symm (hf : IsParityAut f) (N : SpaceW) : resW f (resW f.symm N) = N := by
  rw [resW_apply, ← hf.symm.apply_inW, LinearEquiv.apply_symm_apply]

theorem resW_symm_resW (hf : IsParityAut f) (N : SpaceW) : resW f.symm (resW f N) = N := by
  rw [resW_apply, ← hf.apply_inW, LinearEquiv.symm_apply_apply]

noncomputable def resWEquiv (hf : IsParityAut f) : SpaceW ≃ₗ[ℚ] SpaceW :=
  { resW f with
    invFun := resW f.symm
    left_inv := hf.resW_symm_resW
    right_inv := hf.resW_resW_symm }

theorem resWEquiv_apply (hf : IsParityAut f) (N : SpaceW) : hf.resWEquiv N = resW f N := rfl

theorem resWEquiv_symm_apply (hf : IsParityAut f) (N : SpaceW) :
    hf.resWEquiv.symm N = resW f.symm N := rfl

theorem resW_Lw (hf : IsParityAut f) {u : SpaceB} (hu : Nm u = 0) (N : SpaceW) :
    resW f (Lw u N) = Lw (f u) (resW f N) := by
  have h := hf.map_gmul u (inW N)
  rw [gmul_inW_eq hu, hf.apply_inW, hf.apply_inW] at h
  exact congrArg (fun w : SpaceB => w.2.2) h

theorem Lw_map (hf : IsParityAut f) {u : SpaceB} (hu : Nm u = 0) :
    Lw (f u) = hf.resWEquiv.conj (Lw u) := by
  refine LinearMap.ext fun N => ?_
  rw [LinearEquiv.conj_apply_apply, resWEquiv_apply, resWEquiv_symm_apply, hf.resW_Lw hu,
    hf.resW_resW_symm]

theorem trace_Lw_map (hf : IsParityAut f) {u v : SpaceB} (hu : Nm u = 0) (hv : Nm v = 0) :
    LinearMap.trace ℚ SpaceW (Lw (f u) * Lw (f v)) = LinearMap.trace ℚ SpaceW (Lw u * Lw v) := by
  rw [hf.Lw_map hu, hf.Lw_map hv, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    ← LinearEquiv.conj_comp, LinearMap.trace_conj']

theorem sigmaF_map (hf : IsParityAut f) {u v : SpaceB} (hu : Nm u = 0) (hv : Nm v = 0) :
    sigmaF (f u) (f v) = sigmaF u v := by
  have h1 := hf.trace_Lw_map hu hv
  rw [trace_Lw_eq_bform_sigmaF _ (hf.map_AX hv), trace_Lw_eq_bform_sigmaF _ hv,
    hf.map_bform] at h1
  linarith

theorem phiOp_map (hf : IsParityAut f) {u : SpaceB} (hu : Nm u = 0) :
    phiOp (f u) = f (phiOp u) := by
  set w := phiOp (f u) - f (phiOp u) with hw_def
  have hw : Nm w = 0 := by
    have h1 : Nm (f (phiOp u)) = 0 := hf.map_AX (u := phiOp u) rfl
    change (0 : SpaceW) - Nm (f (phiOp u)) = 0
    rw [h1, sub_zero]
  have hperp : ∀ v, Nm v = 0 → bform w (f v) = 0 := by
    intro v hv
    rw [hw_def, map_sub, LinearMap.sub_apply, bform_phiOp, hf.map_bform, bform_phiOp,
      hf.sigmaF_map hu hv, sub_self]
  have h0 := hperp (f.symm w) (hf.symm.map_AX hw)
  rw [LinearEquiv.apply_symm_apply] at h0
  by_contra hne
  exact (bform_self_pos (sub_ne_zero.2 hne)).ne' h0

end IsParityAut

noncomputable def scalarLine : Submodule ℚ SpaceB := ℚ ∙ inA oneA

noncomputable def subA : Submodule ℚ SpaceB where
  carrier := {u | u.2.1 = 0 ∧ u.2.2 = 0}
  add_mem' {u v} hu hv := ⟨by change u.2.1 + v.2.1 = 0; rw [hu.1, hv.1, add_zero],
    by change u.2.2 + v.2.2 = 0; rw [hu.2, hv.2, add_zero]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c u hu := ⟨by change c • u.2.1 = 0; rw [hu.1, smul_zero],
    by change c • u.2.2 = 0; rw [hu.2, smul_zero]⟩

noncomputable def subX : Submodule ℚ SpaceB where
  carrier := {u | u.1 = 0 ∧ u.2.2 = 0}
  add_mem' {u v} hu hv := ⟨by change u.1 + v.1 = 0; rw [hu.1, hv.1, add_zero],
    by change u.2.2 + v.2.2 = 0; rw [hu.2, hv.2, add_zero]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c u hu := ⟨by change c • u.1 = 0; rw [hu.1, smul_zero],
    by change c • u.2.2 = 0; rw [hu.2, smul_zero]⟩

theorem mem_subA {u : SpaceB} : u ∈ subA ↔ xs u = 0 ∧ Nm u = 0 := Iff.rfl

theorem mem_subX {u : SpaceB} : u ∈ subX ↔ u.1 = 0 ∧ Nm u = 0 := Iff.rfl

theorem trace_coe_smul_oneA (c : ℚ) :
    trace ((c • oneA : symMat) : Matrix (Fin 24) (Fin 24) ℚ) = 24 * c := by
  rw [coe_smul_oneA, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

namespace IsParityAut

variable {f : SpaceB ≃ₗ[ℚ] SpaceB}

private theorem trace_eq_of_phiOp {v : SpaceB} {B : symMat} (h : (phiOp v).1 = B) :
    120 * trace (Am v) = trace (B : Matrix (Fin 24) (Fin 24) ℚ) := by
  rw [← h]
  change 120 * trace (Am v) =
    trace (((5 * trace (Am v)) • oneA : symMat) : Matrix (Fin 24) (Fin 24) ℚ)
  rw [trace_coe_smul_oneA]
  ring

theorem map_subX (hf : IsParityAut f) {u : SpaceB} (hu : u ∈ subX) : f u ∈ subX := by
  obtain ⟨h1, h2⟩ := mem_subX.1 hu
  have hphi : phiOp u = u := by
    refine Prod.ext ?_ (Prod.ext rfl h2.symm)
    change ((5 * trace ((u.1 : symMat) : Matrix (Fin 24) (Fin 24) ℚ)) • oneA : symMat) = u.1
    rw [h1, Submodule.coe_zero, trace_zero, mul_zero, zero_smul]
  have h := hf.phiOp_map h2
  rw [hphi] at h
  have h1' : (phiOp (f u)).1 = (f u).1 := congrArg Prod.fst h
  have htr := trace_eq_of_phiOp h1'
  have htr0 : trace (Am (f u)) = 0 := by
    change 120 * trace (Am (f u)) = trace (Am (f u)) at htr
    linarith
  refine ⟨?_, hf.map_AX h2⟩
  rw [← h1']
  change ((5 * trace (Am (f u))) • oneA : symMat) = 0
  rw [htr0, mul_zero, zero_smul]

theorem phiOp_smul_oneA (a : ℚ) : phiOp (a • inA oneA) = (120 : ℚ) • (a • inA oneA) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change ((5 * trace (((a • oneA : symMat)) : Matrix (Fin 24) (Fin 24) ℚ)) • oneA : symMat) =
      (120 : ℚ) • (a • oneA)
    rw [trace_coe_smul_oneA, smul_smul]
    congr 1
    ring
  · change (a • (0 : SpaceX)) = (120 : ℚ) • (a • (0 : SpaceX))
    simp
  · change (0 : SpaceW) = (120 : ℚ) • (a • (0 : SpaceW))
    simp

theorem map_scalarLine (hf : IsParityAut f) {u : SpaceB} (hu : u ∈ scalarLine) :
    f u ∈ scalarLine := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
  have h : phiOp (f (a • inA oneA)) = (120 : ℚ) • f (a • inA oneA) := by
    rw [hf.phiOp_map (u := a • inA oneA) (by simp), phiOp_smul_oneA]
    exact map_smul f (120 : ℚ) (a • inA oneA)
  have h1 : (phiOp (f (a • inA oneA))).1 = (120 : ℚ) • (f (a • inA oneA)).1 :=
    congrArg Prod.fst h
  have h2 : xs (f (a • inA oneA)) = (120 : ℚ) • xs (f (a • inA oneA)) :=
    congrArg (fun w : SpaceB => w.2.1) h
  have hx : xs (f (a • inA oneA)) = 0 := by
    have : (119 : ℚ) • xs (f (a • inA oneA)) = 0 := by
      rw [show (119 : ℚ) = 120 - 1 by norm_num, sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  have hN : Nm (f (a • inA oneA)) = 0 := hf.map_AX (by simp)
  refine Submodule.mem_span_singleton.2 ⟨trace (Am (f (a • inA oneA))) / 24, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (trace (Am (f (a • inA oneA))) / 24) • oneA = (f (a • inA oneA)).1
    have h1' : ((5 * trace (Am (f (a • inA oneA)))) • oneA : symMat) =
        (120 : ℚ) • (f (a • inA oneA)).1 := h1
    have e : (f (a • inA oneA)).1 = (120 : ℚ)⁻¹ • ((5 * trace (Am (f (a • inA oneA)))) • oneA) := by
      rw [h1', smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
    rw [e, smul_smul]
    congr 1
    ring
  · change (trace (Am (f (a • inA oneA))) / 24) • (0 : SpaceX) = xs (f (a • inA oneA))
    rw [hx, smul_zero]
  · change (trace (Am (f (a • inA oneA))) / 24) • (0 : SpaceW) = Nm (f (a • inA oneA))
    rw [hN, smul_zero]

theorem map_subA (hf : IsParityAut f) {u : SpaceB} (hu : u ∈ subA) : f u ∈ subA := by
  obtain ⟨h1, h2⟩ := mem_subA.1 hu
  have h := hf.phiOp_map h2
  have hmem : phiOp u ∈ scalarLine := by
    refine Submodule.mem_span_singleton.2 ⟨5 * trace (Am u), ?_⟩
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · change (5 * trace (Am u)) • (0 : SpaceX) = xs u
      rw [h1, smul_zero]
    · change (5 * trace (Am u)) • (0 : SpaceW) = 0
      rw [smul_zero]
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 (hf.map_scalarLine hmem)
  have hx : xs (phiOp (f u)) = xs (f (phiOp u)) := congrArg (fun w : SpaceB => w.2.1) h
  refine ⟨?_, hf.map_AX h2⟩
  change xs (phiOp (f u)) = 0
  rw [hx, ← hb]
  change b • (0 : SpaceX) = 0
  rw [smul_zero]

end IsParityAut

end VOA.Moonshine.MonsterGriess.Parity
