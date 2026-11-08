/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Parity/ShortLines.lean
  CFSG/Monster/Parity/RecoversLattice.lean
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
import VOA.Moonshine.MonsterGriess.ParityTraceSplitting
import VOA.Moonshine.MonsterGriess.ParityRealExtension
import VOA.Moonshine.MonsterGriess.VisiblePair

/-!
# Axiom's Monster port (parity-centralizer closure): parity automorphisms permute the short lines and recover `Co₀`

For a parity automorphism `f` (`IsParityAut f`):

* `resA f`, `resX f` — its blocks on `symMat` and `SpaceX` (`apply_inA`, `apply_inX`);
  `resA f` preserves the Jordan product and the trace form;
* ⭐ `exists_line`, `lineMap`, `lineSign` — `f` sends each short basis vector `e_c` of `SpaceX`
  to `± e_{lineMap c}`, with `qf (lineMap c) (resA f A) = qf c A`; `lineMap` is a bijection;
* ⭐ `exists_latticeO` — there is `g ∈ latticeO = Co₀` with `resA f = thetaA (mat g)` and
  `u_c g = ± u_{lineMap c}` (the real orthogonal conjugation of `exists_real_orthogonal_conj` is
  rational with denominators dividing 8, and preserves the Leech lattice because it permutes the
  minimal vectors up to sign).

## Port notes
* Namespace `CFSG.Monster.Parity` ↦ `VOA.Moonshine.MonsterGriess.Parity`.  Module-system syntax
  and the source's `attribute [-instance] …` line dropped.  Bodies verbatim except as listed.
* Renamed use: the source's `qf_zero` ↦ our `qf_zero_mat`.
* Drift: `push Not at hc` ↦ `push_neg at hc`.
* `SpinLattice.phi0_injective`, `SpinLattice.phi0_bijective` are our `LatticeQuadratic.lean`
  statements for the function `phi0` (same values as the source's bundled map).
* Omitted (not reached): `sgn_eq_one_or_neg_one`, the summary theorem
  `parity_centralizer_recovers_lattice`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.MonsterGriess.Parity

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
  VOA.Moonshine.MonsterGriess.ScalarKernel VOA.Moonshine.MonsterGriess.Visible Matrix Module

noncomputable section

/-! ### From `CFSG/Monster/Parity/ShortLines.lean` -/

theorem gmul_inA_inA (A B : symMat) : gmul (inA A) (inA B) = inA ((4 : ℚ) • jordanQ A B) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun c => ?_) ?_)
  · change gmulA (inA A) (inA B) = (4 : ℚ) • ((1 / 2 : ℚ) •
      ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ) +
        (B : Matrix (Fin 24) (Fin 24) ℚ) * (A : Matrix (Fin 24) (Fin 24) ℚ)))
    simp only [gmulA, Am_inA, xs_inA, Nm_inA, Pi.zero_apply, mul_zero, zero_smul,
      Finset.sum_const_zero, smul_zero, add_zero, transpose_zero, Matrix.zero_mul, trace_zero,
      zero_div, smul_smul]
    norm_num
  · change gmulX (inA A) (inA B) c = 0
    simp [gmulX, qf_zero_mat]
  · change gmulWHalf (inA A) (inA B) + gmulWHalf (inA B) (inA A) = 0
    simp [gmulWHalf]

theorem gmul_inA_inX (A : symMat) (x : SpaceX) :
    gmul (inA A) (inX x) = inX (fun c => x c * qf c A / 8) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (funext fun c => ?_) ?_)
  · change gmulA (inA A) (inX x) = 0
    simp [gmulA]
  · change gmulX (inA A) (inX x) c = x c * qf c A / 8
    simp [gmulX, qf_zero_mat]
  · change gmulWHalf (inA A) (inX x) + gmulWHalf (inX x) (inA A) = 0
    simp [gmulWHalf]

theorem bform_inA_inA (A B : symMat) :
    bform (inA A) (inA B) =
      trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ)) := by
  rw [bform_apply]
  simp

theorem bform_inX_inX (x y : SpaceX) : bform (inX x) (inX y) = x ⬝ᵥ y := by
  rw [bform_apply]
  simp [dotProduct]

theorem eq_zero_of_trace_mul_self {M : Matrix (Fin 24) (Fin 24) ℚ} (hM : Mᵀ = M)
    (h : trace (M * M) = 0) : M = 0 := by
  have hs : trace (M * M) = ∑ i, ∑ j, M i j ^ 2 := by
    simp only [trace, diag, mul_apply, sq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← transpose_apply M i j, hM]
  rw [hs] at h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (M i j)).1 h i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (M i j)).1 h1 j
    (Finset.mem_univ _)
  simpa using h2

theorem eq_of_forall_trace_mul_eq {M M' : symMat}
    (h : ∀ B : symMat, trace ((M : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ)) =
      trace ((M' : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ))) : M = M' := by
  have hD := h (M - M')
  have h0 : ((M - M' : symMat) : Matrix (Fin 24) (Fin 24) ℚ) = 0 := by
    refine eq_zero_of_trace_mul_self (M - M').2 ?_
    rw [Submodule.coe_sub] at hD ⊢
    rw [Matrix.sub_mul, trace_sub, hD, sub_self]
  exact sub_eq_zero.1 (Subtype.ext h0)

def UmatS (c : ShortIdx) : symMat := ⟨Umat c, Umat_symm c⟩

theorem coe_UmatS (c : ShortIdx) : (UmatS c : Matrix (Fin 24) (Fin 24) ℚ) = Umat c := rfl

theorem eq_of_forall_qf_eq {d d' : ShortIdx} (h : ∀ B : symMat, qf d B = qf d' B) : d = d' := by
  have hU : UmatS d = UmatS d' := eq_of_forall_trace_mul_eq fun B => by
    rw [coe_UmatS, coe_UmatS, trace_Umat_mul, trace_Umat_mul, h]
  have hv : vecMulVec (uQ d) (uQ d) = vecMulVec (uQ d') (uQ d') := congrArg Subtype.val hU
  have hcl : classOf (uvec d) = classOf (uvec d') := by
    refine (classOf_eq_iff (uvec_mem d) (uvec_mem d')).2 ?_
    rcases eq_or_eq_neg_of_vecMulVec_eq hv with h1 | h1
    · exact Or.inl (funext fun i => Int.cast_injective (α := ℚ) (congrFun h1 i))
    · refine Or.inr (funext fun i => Int.cast_injective (α := ℚ) ?_)
      rw [Pi.neg_apply, Int.cast_neg]
      exact congrFun h1 i
  rw [classOf_uvec, classOf_uvec] at hcl
  exact Subtype.ext (SpinLattice.phi0_injective hcl)

/-- The `symMat`-block of an automorphism of `SpaceB`. -/
def resA (f : SpaceB ≃ₗ[ℚ] SpaceB) : symMat →ₗ[ℚ] symMat :=
  LinearMap.fst ℚ symMat (SpaceX × SpaceW) ∘ₗ f.toLinearMap ∘ₗ
    LinearMap.inl ℚ symMat (SpaceX × SpaceW)

theorem resA_apply (f : SpaceB ≃ₗ[ℚ] SpaceB) (A : symMat) : resA f A = (f (inA A)).1 := rfl

/-- The `SpaceX`-block of an automorphism of `SpaceB`. -/
def resX (f : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceX →ₗ[ℚ] SpaceX :=
  (LinearMap.fst ℚ SpaceX SpaceW ∘ₗ LinearMap.snd ℚ symMat (SpaceX × SpaceW)) ∘ₗ f.toLinearMap ∘ₗ
    (LinearMap.inr ℚ symMat (SpaceX × SpaceW) ∘ₗ LinearMap.inl ℚ SpaceX SpaceW)

theorem resX_apply (f : SpaceB ≃ₗ[ℚ] SpaceB) (x : SpaceX) : resX f x = (f (inX x)).2.1 := rfl

namespace IsParityAut

variable {f : SpaceB ≃ₗ[ℚ] SpaceB}

theorem apply_inA (hf : IsParityAut f) (A : symMat) : f (inA A) = inA (resA f A) := by
  obtain ⟨h1, h2⟩ := mem_subA.1 (hf.map_subA (u := inA A) ⟨rfl, rfl⟩)
  exact Prod.ext rfl (Prod.ext h1 h2)

theorem apply_inX (hf : IsParityAut f) (x : SpaceX) : f (inX x) = inX (resX f x) := by
  obtain ⟨h1, h2⟩ := mem_subX.1 (hf.map_subX (u := inX x) ⟨rfl, rfl⟩)
  exact Prod.ext h1 (Prod.ext rfl h2)

theorem resA_resA_symm (hf : IsParityAut f) (B : symMat) : resA f (resA f.symm B) = B := by
  rw [resA_apply, ← hf.symm.apply_inA, LinearEquiv.apply_symm_apply]

theorem resA_surjective (hf : IsParityAut f) : Function.Surjective (resA f) :=
  fun B => ⟨resA f.symm B, hf.resA_resA_symm B⟩

theorem resX_injective (hf : IsParityAut f) : Function.Injective (resX f) := fun x y h => by
  have h' : f (inX x) = f (inX y) := by rw [hf.apply_inX x, hf.apply_inX y, h]
  exact congrArg (fun w : SpaceB => w.2.1) (f.injective h')

theorem resA_jordanQ (hf : IsParityAut f) (A B : symMat) :
    resA f (jordanQ A B) = jordanQ (resA f A) (resA f B) := by
  have h := hf.map_gmul (inA A) (inA B)
  rw [gmul_inA_inA A B, hf.apply_inA ((4 : ℚ) • jordanQ A B), hf.apply_inA A, hf.apply_inA B,
    gmul_inA_inA (resA f A) (resA f B)] at h
  have h1 : resA f ((4 : ℚ) • jordanQ A B) = (4 : ℚ) • jordanQ (resA f A) (resA f B) :=
    congrArg Prod.fst h
  rw [map_smul] at h1
  exact smul_right_injective _ (by norm_num : (4 : ℚ) ≠ 0) h1

theorem resA_trace (hf : IsParityAut f) (A B : symMat) :
    trace ((resA f A : Matrix (Fin 24) (Fin 24) ℚ) * (resA f B : Matrix (Fin 24) (Fin 24) ℚ)) =
      trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (B : Matrix (Fin 24) (Fin 24) ℚ)) := by
  have h := hf.map_bform (inA A) (inA B)
  rwa [hf.apply_inA A, hf.apply_inA B, bform_inA_inA, bform_inA_inA] at h

theorem resX_eigen (hf : IsParityAut f) (A : symMat) (x : SpaceX) :
    resX f (fun c => x c * qf c A / 8) = fun c => resX f x c * qf c (resA f A) / 8 := by
  have h := hf.map_gmul (inA A) (inX x)
  rw [gmul_inA_inX A x, hf.apply_inX (fun c => x c * qf c A / 8), hf.apply_inA A,
    hf.apply_inX x, gmul_inA_inX (resA f A) (resX f x)] at h
  exact congrArg (fun w : SpaceB => w.2.1) h

theorem resX_single_apply (hf : IsParityAut f) (c d : ShortIdx) (A : symMat) :
    resX f (Pi.single c 1) d * (qf c A - qf d (resA f A)) = 0 := by
  have h := congrFun (hf.resX_eigen A (Pi.single c 1)) d
  have e : (fun e => (Pi.single c 1 : SpaceX) e * qf e A / 8) =
      (qf c A / 8) • (Pi.single c 1 : SpaceX) := by
    funext e
    by_cases he : e = c
    · subst he
      simp
    · simp [he]
  rw [e, map_smul, Pi.smul_apply, smul_eq_mul] at h
  linear_combination 8 * h

theorem exists_line (hf : IsParityAut f) (c : ShortIdx) :
    ∃ d : ShortIdx, ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧
      resX f (Pi.single c 1) = ε • Pi.single d 1 ∧ ∀ A : symMat, qf d (resA f A) = qf c A := by
  set y := resX f (Pi.single c 1) with hy_def
  have hy0 : y ≠ 0 := fun h0 => by
    have h1 : resX f (Pi.single c 1) = resX f 0 := by rw [← hy_def, h0, map_zero]
    have := congrFun (hf.resX_injective h1) c
    simp at this
  obtain ⟨d, hd⟩ : ∃ d, y d ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy0 (funext hc)
  have hchar : ∀ e, y e ≠ 0 → ∀ A, qf e (resA f A) = qf c A := fun e he A => by
    have := (mul_eq_zero.1 (hf.resX_single_apply c e A)).resolve_left he
    linarith
  have hsupp : ∀ e, e ≠ d → y e = 0 := by
    intro e he
    by_contra hye
    exact he (eq_of_forall_qf_eq fun B => by
      obtain ⟨A, rfl⟩ := hf.resA_surjective B
      rw [hchar e hye, hchar d hd])
  have hy : y = y d • Pi.single d 1 := by
    funext e
    by_cases he : e = d
    · subst he
      simp
    · simp [he, hsupp e he]
  have hnorm : y d * y d = 1 := by
    have h := hf.map_bform (inX (Pi.single c 1)) (inX (Pi.single c 1))
    rw [hf.apply_inX, bform_inX_inX, bform_inX_inX, ← hy_def, hy, smul_dotProduct,
      dotProduct_smul, single_dotProduct_single, single_dotProduct_single] at h
    simpa [smul_eq_mul] using h
  exact ⟨d, y d, mul_self_eq_one_iff.1 hnorm, hy, hchar d hd⟩

/-- The short line `lineMap c` to which `f` sends the line of `e_c`. -/
def lineMap (hf : IsParityAut f) (c : ShortIdx) : ShortIdx := (hf.exists_line c).choose

def lineSign (hf : IsParityAut f) (c : ShortIdx) : ℚ :=
  (hf.exists_line c).choose_spec.choose

theorem lineSign_eq (hf : IsParityAut f) (c : ShortIdx) :
    hf.lineSign c = 1 ∨ hf.lineSign c = -1 :=
  (hf.exists_line c).choose_spec.choose_spec.1

theorem resX_single (hf : IsParityAut f) (c : ShortIdx) :
    resX f (Pi.single c 1) = hf.lineSign c • Pi.single (hf.lineMap c) 1 :=
  (hf.exists_line c).choose_spec.choose_spec.2.1

theorem qf_lineMap (hf : IsParityAut f) (c : ShortIdx) (A : symMat) :
    qf (hf.lineMap c) (resA f A) = qf c A :=
  (hf.exists_line c).choose_spec.choose_spec.2.2 A

theorem lineSign_ne_zero (hf : IsParityAut f) (c : ShortIdx) : hf.lineSign c ≠ 0 := by
  rcases hf.lineSign_eq c with h | h <;> rw [h] <;> norm_num

theorem lineMap_injective (hf : IsParityAut f) : Function.Injective hf.lineMap := by
  intro c c' h
  have h1 : resX f (hf.lineSign c' • Pi.single c 1) = resX f (hf.lineSign c • Pi.single c' 1) := by
    rw [map_smul, map_smul, hf.resX_single, hf.resX_single, h, smul_smul, smul_smul, mul_comm]
  have h2 := congrFun (hf.resX_injective h1) c
  by_contra hne
  rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, smul_zero,
    smul_eq_mul, mul_one] at h2
  exact hf.lineSign_ne_zero c' h2

theorem lineMap_bijective (hf : IsParityAut f) : Function.Bijective hf.lineMap :=
  Finite.injective_iff_bijective.1 hf.lineMap_injective

theorem resA_UmatS (hf : IsParityAut f) (c : ShortIdx) :
    resA f (UmatS c) = UmatS (hf.lineMap c) := by
  refine eq_of_forall_trace_mul_eq fun B => ?_
  obtain ⟨A, rfl⟩ := hf.resA_surjective B
  rw [hf.resA_trace, coe_UmatS, coe_UmatS, trace_Umat_mul, trace_Umat_mul, hf.qf_lineMap]

theorem apply_Xlift (hf : IsParityAut f) {r : Q} (hr : IsShortCoord (coordOf r)) :
    f (inX (Xlift r)) = inX ((sgn (centralCoord r) * hf.lineSign ⟨coordOf r, hr⟩) •
      Xlift (rep (hf.lineMap ⟨coordOf r, hr⟩).1)) := by
  rw [hf.apply_inX, Xlift_eq hr, map_smul, hf.resX_single, Xlift_rep_eq, smul_smul]

end IsParityAut

/-! ### From `CFSG/Monster/Parity/RecoversLattice.lean` -/

def intVec (K : Type*) [Field K] (u : Fin 24 → ℤ) : Fin 24 → K := fun i => (u i : K)

variable {K : Type*} [Field K]

theorem intVec_zero : intVec K 0 = 0 := by
  funext i
  simp [intVec]

theorem intVec_add (u v : Fin 24 → ℤ) : intVec K (u + v) = intVec K u + intVec K v := by
  funext i
  simp [intVec]

theorem intVec_neg (u : Fin 24 → ℤ) : intVec K (-u) = -intVec K u := by
  funext i
  simp [intVec]

theorem intVec_rat (u : Fin 24 → ℤ) : intVec ℚ u = ratVec u := rfl

theorem uQ_eq_intVec (c : ShortIdx) : uQ c = intVec ℚ (uvec c) := rfl

def latPre (M : Matrix (Fin 24) (Fin 24) K) : AddSubgroup (Fin 24 → ℤ) where
  carrier := {v | ∃ w ∈ codeLattice C, intVec K v ᵥ* M = intVec K w}
  zero_mem' := ⟨0, zero_mem_codeLattice, by rw [intVec_zero, zero_vecMul]⟩
  add_mem' := by
    rintro a b ⟨w, hw, h⟩ ⟨w', hw', h'⟩
    exact ⟨w + w', add_mem_codeLattice allOnes_mem_C hw hw', by
      rw [intVec_add, add_vecMul, h, h', intVec_add]⟩
  neg_mem' := by
    rintro a ⟨w, hw, h⟩
    exact ⟨-w, neg_mem_codeLattice allOnes_mem_C hw, by rw [intVec_neg, neg_vecMul, h, intVec_neg]⟩

theorem forall_mem_codeLattice_of_minVecs (M : Matrix (Fin 24) (Fin 24) K)
    (h : ∀ u ∈ minVecs, ∃ w ∈ codeLattice C, intVec K u ᵥ* M = intVec K w)
    {v : Fin 24 → ℤ} (hv : v ∈ codeLattice C) :
    ∃ w ∈ codeLattice C, intVec K v ᵥ* M = intVec K w := by
  have hle : AddSubgroup.closure latticeGens ≤ latPre M := by
    rw [AddSubgroup.closure_le]
    intro u hu
    exact h u (mem_minVecs_iff.2 (latticeGens_mem hu))
  have hv' : v ∈ AddSubgroup.closure latticeGens := by
    rw [closure_latticeGens]
    exact hv
  exact hle hv'

theorem exists_shortIdx_of_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    ∃ c : ShortIdx, u = uvec c ∨ u = -uvec c := by
  obtain ⟨p, hp⟩ := SpinLattice.phi0_bijective.2 (classOf u)
  have hc : IsShortCoord p := ⟨u, hu, hp.symm⟩
  exact ⟨⟨p, hc⟩, (classOf_eq_iff (uvec_mem _) hu).1 ((classOf_uvec _).trans hp)⟩

theorem minVecs_of_uvec (M : Matrix (Fin 24) (Fin 24) K)
    (h : ∀ c : ShortIdx, ∃ c' : ShortIdx, intVec K (uvec c) ᵥ* M = intVec K (uvec c') ∨
      intVec K (uvec c) ᵥ* M = -intVec K (uvec c')) :
    ∀ u ∈ minVecs, ∃ w ∈ codeLattice C, intVec K u ᵥ* M = intVec K w := by
  intro u hu
  obtain ⟨c, hc⟩ := exists_shortIdx_of_minVecs hu
  obtain ⟨c', hc'⟩ := h c
  have hmem : uvec c' ∈ codeLattice C := (uvec_mem c').1
  have hmem' : -uvec c' ∈ codeLattice C := neg_mem_codeLattice allOnes_mem_C hmem
  rcases hc with rfl | rfl <;> rcases hc' with h1 | h1
  · exact ⟨_, hmem, h1⟩
  · exact ⟨_, hmem', by rw [h1, intVec_neg]⟩
  · exact ⟨_, hmem', by rw [intVec_neg, neg_vecMul, h1, intVec_neg]⟩
  · exact ⟨_, hmem, by rw [intVec_neg, neg_vecMul, h1, neg_neg]⟩

def castVec (x : Fin 24 → ℚ) : Fin 24 → ℝ := fun i => (x i : ℝ)

theorem castVec_injective : Function.Injective castVec := fun _ _ h =>
  funext fun i => Rat.cast_injective (congrFun h i)

theorem castVec_intVec (u : Fin 24 → ℤ) : castVec (intVec ℚ u) = intVec ℝ u := by
  funext i
  simp [castVec, intVec]

theorem castVec_neg (x : Fin 24 → ℚ) : castVec (-x) = -castVec x := by
  funext i
  simp [castVec]

theorem castVec_vecMul (x : Fin 24 → ℚ) (g : Matrix (Fin 24) (Fin 24) ℚ) :
    castVec (x ᵥ* g) = castVec x ᵥ* castR g := by
  funext j
  simp [castVec, vecMul, dotProduct, castR_apply, Rat.cast_sum, Rat.cast_mul]

theorem castR_Umat (c : ShortIdx) :
    castR (Umat c) = vecMulVec (intVec ℝ (uvec c)) (intVec ℝ (uvec c)) := by
  ext i j
  simp [castR_apply, Umat, uQ, vecMulVec_apply, intVec]

theorem conj_vecMulVec (G : Matrix (Fin 24) (Fin 24) ℝ) (a : Fin 24 → ℝ) :
    Gᵀ * vecMulVec a a * G = vecMulVec (a ᵥ* G) (a ᵥ* G) := by
  rw [mul_vecMulVec, mulVec_transpose, vecMulVec_mul]

section Real

variable {f : SpaceB ≃ₗ[ℚ] SpaceB} (hf : IsParityAut f) {G : Matrix (Fin 24) (Fin 24) ℝ}
  (hG : ∀ A : symMat, castR (resA f A) = Gᵀ * castR A * G)
include hf hG

theorem realVec_uvec_mul (c : ShortIdx) :
    intVec ℝ (uvec c) ᵥ* G = intVec ℝ (uvec (hf.lineMap c)) ∨
      intVec ℝ (uvec c) ᵥ* G = -intVec ℝ (uvec (hf.lineMap c)) := by
  have h := hG (UmatS c)
  rw [hf.resA_UmatS, coe_UmatS, coe_UmatS, castR_Umat, castR_Umat, conj_vecMulVec] at h
  exact eq_or_eq_neg_of_vecMulVec_eq h

theorem real_mem_codeLattice {v : Fin 24 → ℤ} (hv : v ∈ codeLattice C) :
    ∃ w ∈ codeLattice C, intVec ℝ v ᵥ* G = intVec ℝ w :=
  forall_mem_codeLattice_of_minVecs G
    (minVecs_of_uvec G fun c => ⟨hf.lineMap c, realVec_uvec_mul hf hG c⟩) hv

theorem exists_row (i : Fin 24) : ∃ w ∈ codeLattice C, ∀ j, G i j = (w j : ℝ) / 8 := by
  obtain ⟨w, hw, h⟩ := real_mem_codeLattice hf hG
    (smul_eight_mem_codeLattice (C := C) (Pi.single i 1 : Fin 24 → ℤ))
  refine ⟨w, hw, fun j => ?_⟩
  have e : intVec ℝ ((8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ)) = (8 : ℝ) • Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [intVec]
    · simp [intVec, hk]
  have hj := congrFun h j
  rw [e, smul_vecMul, single_one_vecMul] at hj
  simp only [Pi.smul_apply, Matrix.row, smul_eq_mul, intVec] at hj
  linarith

theorem exists_rat_of_real :
    ∃ g : Matrix (Fin 24) (Fin 24) ℚ, castR g = G ∧ ∀ i j, ∃ k : ℤ, g i j = k / 8 := by
  choose w _ hwG using exists_row hf hG
  refine ⟨Matrix.of fun i j => (w i j : ℚ) / 8, ?_, fun i j => ⟨w i j, rfl⟩⟩
  ext i j
  rw [castR_apply, hwG i j, of_apply]
  push_cast
  rfl

end Real

namespace IsParityAut

variable {f : SpaceB ≃ₗ[ℚ] SpaceB}

theorem exists_rat_matrix (hf : IsParityAut f) :
    ∃ g : Matrix (Fin 24) (Fin 24) ℚ, g * gᵀ = 1 ∧
      (∀ A : symMat, (resA f A : Matrix (Fin 24) (Fin 24) ℚ) =
        gᵀ * (A : Matrix (Fin 24) (Fin 24) ℚ) * g) ∧
      (∀ c : ShortIdx, uQ c ᵥ* g = uQ (hf.lineMap c) ∨ uQ c ᵥ* g = -uQ (hf.lineMap c)) ∧
      ∀ i j, ∃ k : ℤ, g i j = k / 8 := by
  obtain ⟨G, hGo, hG⟩ := exists_real_orthogonal_conj (resA f) hf.resA_jordanQ hf.resA_trace
  obtain ⟨g, hgG, hg8⟩ := exists_rat_of_real hf hG
  refine ⟨g, ?_, fun A => ?_, fun c => ?_, hg8⟩
  · apply castR_injective
    rw [map_mul, castR_transpose, hgG, map_one]
    exact (mem_orthogonalGroup_iff _ _).1 hGo
  · apply castR_injective
    rw [hG, map_mul, map_mul, castR_transpose, hgG]
  · rcases realVec_uvec_mul hf hG c with h | h
    · left
      apply castVec_injective
      rw [castVec_vecMul, hgG, uQ_eq_intVec, uQ_eq_intVec, castVec_intVec, castVec_intVec, h]
    · right
      apply castVec_injective
      rw [castVec_vecMul, hgG, uQ_eq_intVec, uQ_eq_intVec, castVec_neg, castVec_intVec,
        castVec_intVec, h]

theorem image_latticeQ_eq (hf : IsParityAut f) {g : Matrix (Fin 24) (Fin 24) ℚ}
    (hg : g * gᵀ = 1)
    (hu : ∀ c : ShortIdx, uQ c ᵥ* g = uQ (hf.lineMap c) ∨ uQ c ᵥ* g = -uQ (hf.lineMap c)) :
    (fun x => x ᵥ* g) '' latticeQ = latticeQ := by
  have hgt : gᵀ * g = 1 := mul_eq_one_comm.1 hg
  have h1 : ∀ v ∈ codeLattice C, ∃ w ∈ codeLattice C, intVec ℚ v ᵥ* g = intVec ℚ w :=
    fun v hv => forall_mem_codeLattice_of_minVecs g
      (minVecs_of_uvec g fun c => ⟨hf.lineMap c, hu c⟩) hv
  have hut : ∀ d : ShortIdx, ∃ c : ShortIdx, intVec ℚ (uvec d) ᵥ* gᵀ = intVec ℚ (uvec c) ∨
      intVec ℚ (uvec d) ᵥ* gᵀ = -intVec ℚ (uvec c) := by
    intro d
    obtain ⟨c, rfl⟩ := hf.lineMap_bijective.2 d
    refine ⟨c, ?_⟩
    have hback : ∀ x : Fin 24 → ℚ, (x ᵥ* g) ᵥ* gᵀ = x := fun x => by
      rw [vecMul_vecMul, hg, vecMul_one]
    rcases hu c with h | h
    · left
      rw [← uQ_eq_intVec, ← uQ_eq_intVec, ← h, hback]
    · right
      have h' : uQ (hf.lineMap c) = -(uQ c ᵥ* g) := by rw [h, neg_neg]
      rw [← uQ_eq_intVec, ← uQ_eq_intVec, h', neg_vecMul, hback]
  have h2 : ∀ w ∈ codeLattice C, ∃ v ∈ codeLattice C, intVec ℚ w ᵥ* gᵀ = intVec ℚ v :=
    fun w hw => forall_mem_codeLattice_of_minVecs gᵀ (minVecs_of_uvec gᵀ hut) hw
  ext y
  constructor
  · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨w, hw, h⟩ := h1 v hv
    exact ⟨w, hw, h.symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, h⟩ := h2 w hw
    refine ⟨ratVec v, ⟨v, hv, rfl⟩, ?_⟩
    change intVec ℚ v ᵥ* g = intVec ℚ w
    rw [← h, vecMul_vecMul, hgt, vecMul_one]

/-- ⭐ **A parity automorphism recovers an element of `Co₀`**: its `symMat` block is `thetaA g` for
some `g ∈ latticeO`, and `g` maps each short vector `u_c` to `± u_{lineMap c}`. -/
theorem exists_latticeO (hf : IsParityAut f) :
    ∃ g : latticeO, (∀ A : symMat, resA f A = thetaA (mat g) A) ∧
      (∀ c : ShortIdx, uQ c ᵥ* mat g = uQ (hf.lineMap c) ∨
        uQ c ᵥ* mat g = -uQ (hf.lineMap c)) ∧
      ∀ i j, ∃ k : ℤ, mat g i j = k / 8 := by
  obtain ⟨g, hg, hA, hu, h8⟩ := hf.exists_rat_matrix
  refine ⟨mkO g hg (hf.image_latticeQ_eq hg hu), fun A => Subtype.ext ?_, ?_, ?_⟩
  · rw [hA, coe_thetaA, mat_mkO]
  · rw [mat_mkO]
    exact hu
  · rw [mat_mkO]
    exact h8

end IsParityAut

end

end VOA.Moonshine.MonsterGriess.Parity
