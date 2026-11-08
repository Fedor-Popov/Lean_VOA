/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Griess/DyadicCoords.lean
  CFSG/Monster/Griess/Parity.lean (the part not ported in `GriessTrilinear.lean`: `xB_xB`,
    `xB_mul_self`, `xB_ne_one`, `bform_xB`, `isDyadicVec_xB`, `xB_mem_BR_iff`, `map_xB_BR`,
    `projAX`, `eigenspace_xB_one`, `eigenspace_xB_neg_one`, `finrank_eigenspace_xB_one`,
    `finrank_eigenspace_xB_neg_one`)
  CFSG/Monster/Griess/FourGroup.lean
  CFSG/Monster/Generated/Data.lean
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
import VOA.Moonshine.MonsterGriess.TrialityMatrix
import VOA.Moonshine.MonsterGriess.VisibleAction

/-!
# Axiom's Monster port: the triality four-group `{1, xB, yB, zB}` and `Gmat = ⟨Gvis, tauB⟩`

* ⭐ `yB := tauB * xB * tauB⁻¹`, `zB := tauB ^ 2 * xB * (tauB ^ 2)⁻¹` (the source's
  `Griess/FourGroup.lean`); in the basis `tbasis` all of `xB`, `yB`, `zB` are diagonal with signs
  `oddSign ![1,-1,-1]`, `![-1,1,-1]`, `![-1,-1,1]` on the odd triples (`coe_xB`, `coe_yB`,
  `coe_zB`), whence the Klein four-group relations `xB * yB = zB`, `yB * zB = xB`, … ,
  `yB * yB = 1`, `zB * zB = 1`, the triality action `tauB * xB * tauB⁻¹ = yB`,
  `tauB * yB * tauB⁻¹ = zB`, `tauB * zB * tauB⁻¹ = xB`, and `fourGroupB = {1, xB, yB, zB}`
  (`card_fourGroupB = 4`, `fourGroupB_eq_closure`);
* `yB`, `zB` preserve `bform` and the dyadic lattice `BR`; their `-1`-eigenspaces have dimension
  98304;
* ⭐ `Generated.Gmat := Subgroup.closure (Gvis ∪ {tauB})` (the source's `Generated/Data.lean`),
  with `Hmat = Gvis ≤ Gmat`, `tauB ∈ Gmat`, `Vmat = fourGroupB ≤ Gmat`, `xmat = rhoEquiv zQ = xB`;
* port additions: `Generated.Gmat_eq_closure_insert`, `Generated.Gmat_le_AutO_iff`
  (`Gmat ≤ AutO ↔ tauB ∈ AutO`), `Generated.tauB_mem_AutO_iff` (`tauB ∈ AutO ↔ IsAlgAut tauB`),
  `Generated.Gmat_le_AutO_of_isAlgAut`, `xB_mem_AutO`.

**Not proved here:** `tauB ∈ AutO` and `Gmat ≤ AutO`.  In the source they rest on `tauB_gmul`
(`Griess/ProductInvariance.lean`, with `Griess/Invariance/*`, `Griess/Grading.lean`,
`Octad/ThreeOctad.lean`, `Spin/FourierPauli.lean`), which is not ported.  This file reduces both
to the single named statement `IsAlgAut tauB`.

## Port notes
* Namespaces `CFSG.Monster.Griess`, `CFSG.Monster.Generated` ↦ `VOA.Moonshine.MonsterGriess`,
  `VOA.Moonshine.MonsterGriess.Generated`.  Module-system syntax, `@[expose]` and the source's
  `attribute [-instance] …` line dropped.  Bodies verbatim except as listed.
* `DyadicCoords.lean`: its private `basisB_mem_BR` is not repeated (the public `basisB_mem_BR` of
  `TrialityBasis.lean`, same statement, is used).
* `Parity.lean`: `parityMap`, `xB`, `xB_apply`, `mem_eigenspace_xB_one`,
  `mem_eigenspace_xB_neg_one`, `projW` are already ported (`GriessTrilinear.lean`) and used.
* **Omitted:** `isElementaryAbelian_fourGroupB` (its statement uses `IsElementaryAbelian` of the
  source's `CFSG.Foundations.Basic`, which is not imported, as in the earlier rounds).  In the
  summary `rational_triality_four_group` the conjunct `IsElementaryAbelian 2 fourGroupB` is
  replaced by its content `(∀ g ∈ fourGroupB, ∀ h ∈ fourGroupB, g * h = h * g) ∧
  (∀ g ∈ fourGroupB, g * g = 1)` (`mul_comm_of_mem_fourGroupB`, `sq_of_mem_fourGroupB`).
* `Generated/Data.lean`: in `generated_rational_group_data` the conjunct
  `(zQ : GL SpinIdx ℚ) = -1` is proved by our `coe_zQ : (zQ : GL SpinIdx ℚ) = zU`
  (`zU := -1` by definition), as the source's `coe_zQ`.
* **Added (not in the source files ported here):** `Generated.Gmat_eq_closure_insert`,
  `Generated.tauB_mem_AutO_iff`, `Generated.Gmat_le_AutO_iff`,
  `Generated.Gmat_le_AutO_of_isAlgAut`, `xB_mem_AutO` (short proofs from `bform_tauB`,
  `Visible.Gvis_le_AutO`, `Visible.rhoEquiv_zQ`, `Visible.rhoQ_le_Gvis`).  The source proves
  `Gmat_le_AutO` (`Generated/Centralizer.lean`) from `tauB_mem_AutO` (`Griess/AutFinite.lean`).
-/

set_option linter.style.longLine false
set_option linter.style.show false

namespace VOA.Moonshine.MonsterGriess

open Matrix Module

/-! ### From `CFSG/Monster/Griess/DyadicCoords.lean` -/

def IsDyadicVec (u : SpaceB) : Prop :=
  (∀ i j, (u.1 : Matrix (Fin 24) (Fin 24) ℚ) i j ∈ dyadic) ∧ (∀ c, u.2.1 c ∈ dyadic) ∧
    ∀ j i, u.2.2 j i ∈ dyadic

noncomputable def dyadicVecs : Submodule dyadic SpaceB where
  carrier := {u | IsDyadicVec u}
  add_mem' {_ _} hu hv :=
    ⟨fun i j => add_mem (hu.1 i j) (hv.1 i j), fun c => add_mem (hu.2.1 c) (hv.2.1 c),
      fun j i => add_mem (hu.2.2 j i) (hv.2.2 j i)⟩
  zero_mem' := ⟨fun _ _ => zero_mem _, fun _ => zero_mem _, fun _ _ => zero_mem _⟩
  smul_mem' c _ hu :=
    ⟨fun i j => mul_mem c.2 (hu.1 i j), fun d => mul_mem c.2 (hu.2.1 d),
      fun j i => mul_mem c.2 (hu.2.2 j i)⟩

theorem mem_dyadicVecs {u : SpaceB} : u ∈ dyadicVecs ↔ IsDyadicVec u := Iff.rfl

private theorem ite_mem_dyadic (p : Prop) [Decidable p] : (if p then (1 : ℚ) else 0) ∈ dyadic := by
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem isDyadicVec_basisB (k : BIdx) : IsDyadicVec (basisB k) := by
  rcases k with z | c | ⟨j, i⟩
  · rw [basisB_inl]
    refine ⟨fun k l => ?_, fun _ => zero_mem _, fun _ _ => zero_mem _⟩
    rw [basisA_apply]
    exact ite_mem_dyadic _
  · rw [basisB_inr_inl]
    refine ⟨fun _ _ => zero_mem _, fun d => ?_, fun _ _ => zero_mem _⟩
    change (Pi.single c 1 : SpaceX) d ∈ dyadic
    rw [Pi.single_apply]
    exact ite_mem_dyadic _
  · rw [basisB_inr_inr]
    refine ⟨fun _ _ => zero_mem _, fun _ => zero_mem _, fun j' i' => ?_⟩
    simp only [tensor, vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp [one_mem, zero_mem]

theorem BR_le_dyadicVecs : BR ≤ dyadicVecs :=
  Submodule.span_le.2 (Set.range_subset_iff.2 isDyadicVec_basisB)

private theorem smul_mem_BR {c : ℚ} (hc : c ∈ dyadic) {v : SpaceB} (hv : v ∈ BR) : c • v ∈ BR :=
  Submodule.smul_mem BR (⟨c, hc⟩ : dyadic) hv

theorem symMat_eq_sum (A : symMat) : A = ∑ z, symEntry A z • basisA z := by
  conv_lhs => rw [← basisA.sum_repr A]
  rfl

theorem mem_BR_of_isDyadicVec {u : SpaceB} (hu : IsDyadicVec u) : u ∈ BR := by
  have hdec : u = ((u.1, 0, 0) : SpaceB) + (0, u.2.1, 0) + (0, 0, u.2.2) := by
    ext <;> simp
  rw [hdec]
  refine add_mem (add_mem ?_ ?_) ?_
  · have h : ((u.1, 0, 0) : SpaceB) = ∑ z, symEntry u.1 z • basisB (Sum.inl z) := by
      simp only [basisB_inl]
      conv_lhs => rw [symMat_eq_sum u.1]
      ext
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum]
      · simp [Prod.snd_sum]
    rw [h]
    refine Submodule.sum_mem _ fun z _ => smul_mem_BR ?_ (basisB_mem_BR _)
    induction z using Sym2.ind with | h i j => rw [symEntry_mk]; exact hu.1 i j
  · have h : ((0, u.2.1, 0) : SpaceB) = ∑ c, u.2.1 c • basisB (Sum.inr (Sum.inl c)) := by
      simp only [basisB_inr_inl]
      ext
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [h]
    exact Submodule.sum_mem _ fun c _ => smul_mem_BR (hu.2.1 c) (basisB_mem_BR _)
  · have h : ((0, 0, u.2.2) : SpaceB) =
        ∑ j, ∑ i, u.2.2 j i • basisB (Sum.inr (Sum.inr (j, i))) := by
      simp only [basisB_inr_inr]
      ext
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Prod.fst_sum]
      · simp only [Prod.snd_sum, Prod.smul_snd, Matrix.sum_apply,
          Matrix.smul_apply, tensor, vecMulVec_apply, Pi.single_apply, smul_eq_mul]
        simp
    rw [h]
    exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ =>
      smul_mem_BR (hu.2.2 j i) (basisB_mem_BR _)

theorem mem_BR_iff {u : SpaceB} : u ∈ BR ↔ IsDyadicVec u :=
  ⟨fun h => BR_le_dyadicVecs h, mem_BR_of_isDyadicVec⟩

/-! ### From `CFSG/Monster/Griess/Parity.lean` (the part not ported earlier) -/

theorem xB_xB (u : SpaceB) : xB (xB u) = u := by simp [xB_apply]

theorem xB_mul_self : xB * xB = 1 := LinearEquiv.ext xB_xB

theorem xB_ne_one : xB ≠ 1 := by
  intro h
  have h1 := congrArg (fun f : SpaceB ≃ₗ[ℚ] SpaceB =>
    (f ((0, 0, Matrix.of fun _ _ => (1 : ℚ)) : SpaceB)).2.2 (0, 0) 0) h
  simp only [xB_apply, LinearEquiv.coe_one, id_eq, Matrix.neg_apply, Matrix.of_apply] at h1
  norm_num at h1

theorem bform_xB (u v : SpaceB) : bform (xB u) (xB v) = bform u v := by
  simp only [bform_apply, xB_apply, Matrix.neg_apply, neg_mul_neg]

theorem isDyadicVec_xB {u : SpaceB} (hu : IsDyadicVec u) : IsDyadicVec (xB u) :=
  ⟨hu.1, hu.2.1, fun j i => by
    change -(u.2.2 j i) ∈ dyadic
    exact neg_mem (hu.2.2 j i)⟩

theorem xB_mem_BR_iff {u : SpaceB} : xB u ∈ BR ↔ u ∈ BR := by
  refine ⟨fun h => ?_, fun h => mem_BR_iff.2 (isDyadicVec_xB (mem_BR_iff.1 h))⟩
  rw [← xB_xB u]
  exact mem_BR_iff.2 (isDyadicVec_xB (mem_BR_iff.1 h))

theorem map_xB_BR : BR.map ((xB : SpaceB →ₗ[ℚ] SpaceB).restrictScalars dyadic) = BR := by
  ext u
  refine ⟨?_, fun h => ⟨xB u, xB_mem_BR_iff.2 h, xB_xB u⟩⟩
  rintro ⟨v, hv, rfl⟩
  exact xB_mem_BR_iff.2 hv

noncomputable def projAX : SpaceB →ₗ[ℚ] symMat × SpaceX :=
  LinearMap.prod (LinearMap.fst ℚ symMat (SpaceX × SpaceW))
    (LinearMap.fst ℚ SpaceX SpaceW ∘ₗ LinearMap.snd ℚ symMat (SpaceX × SpaceW))

theorem eigenspace_xB_one : End.eigenspace (xB : End ℚ SpaceB) 1 = LinearMap.ker projW := by
  ext u
  rw [mem_eigenspace_xB_one, LinearMap.mem_ker]
  rfl

theorem eigenspace_xB_neg_one :
    End.eigenspace (xB : End ℚ SpaceB) (-1) = LinearMap.ker projAX := by
  ext u
  rw [mem_eigenspace_xB_neg_one, LinearMap.mem_ker, Prod.ext_iff]
  rfl

theorem finrank_eigenspace_xB_one : finrank ℚ (End.eigenspace (xB : End ℚ SpaceB) 1) = 98580 := by
  rw [eigenspace_xB_one]
  have hsurj : LinearMap.range projW = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro N
    exact ⟨(0, 0, N), rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker projW
  rw [hsurj, finrank_top, finrank_W, finrank_B] at h
  omega

theorem finrank_eigenspace_xB_neg_one :
    finrank ℚ (End.eigenspace (xB : End ℚ SpaceB) (-1)) = 98304 := by
  rw [eigenspace_xB_neg_one]
  have hsurj : LinearMap.range projAX = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨A, x⟩
    exact ⟨(A, x, 0), rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker projAX
  rw [hsurj, finrank_top, finrank_prod, finrank_A, finrank_X, finrank_B] at h
  omega

/-! ### From `CFSG/Monster/Griess/FourGroup.lean` -/

open VOA.Moonshine.MonsterGriess.Spin

def oddSign (s : Fin 3 → ℚ) : TIdx → ℚ
  | .inr (.inr (.inl (_, _, k))) => s k
  | _ => 1

noncomputable def oddSignMat (s : Fin 3 → ℚ) : Matrix TIdx TIdx ℚ :=
  diag2 1 (diag2 1 (diag2 (kron1 C₀ (kron1 (Fin 24) (diagonal s))) 1))

def sgnX : Fin 3 → ℚ := ![1, -1, -1]

def sgnY : Fin 3 → ℚ := ![-1, 1, -1]

def sgnZ : Fin 3 → ℚ := ![-1, -1, 1]

theorem oddSign_odd (s : Fin 3 → ℚ) (c : C₀) (i : Fin 24) (k : Fin 3) :
    oddSign s (.inr (.inr (.inl (c, i, k)))) = s k := rfl

theorem oddSignMat_eq_diagonal (s : Fin 3 → ℚ) : oddSignMat s = diagonal (oddSign s) := by
  ext x y
  rcases x with i | q | ⟨c, i, k⟩ | o <;> rcases y with j | q' | ⟨c', i', k'⟩ | o'
  all_goals try simp [oddSignMat, diag2, diagonal_apply, oddSign, one_apply]
  simp only [kron1_apply, one_apply, diagonal_apply]
  by_cases hc : c = c' <;> by_cases hi : i = i' <;> by_cases hk : k = k' <;> simp [hc, hi, hk]

theorem oddSignMat_mul (s t : Fin 3 → ℚ) : oddSignMat s * oddSignMat t = oddSignMat (s * t) := by
  rw [oddSignMat, oddSignMat, oddSignMat, diag2_mul, diag2_mul, diag2_mul, kron1_mul, kron1_mul,
    diagonal_mul_diagonal, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul]
  rfl

theorem oddSignMat_one : oddSignMat (fun _ => 1) = 1 := by
  rw [oddSignMat, diagonal_one, kron1_one, kron1_one, diag2_one, diag2_one, diag2_one]

theorem tauMat_transpose_conj (s : Fin 3 → ℚ) :
    tauMatᵀ * oddSignMat s * tauMat = oddSignMat ![s 2, s 0, s 1] := by
  simp only [tauMat, oddSignMat, diag2_transpose, diag2_mul, transpose_one, Matrix.mul_one,
    pairBlock_transpose_mul, octBlock_transpose_mul, oddBlock, kron1_transpose, kron1_mul,
    cyc3_conj_diagonal]

private theorem apply_tbasis_of_coe {g : SpaceB ≃ₗ[ℚ] SpaceB} {s : Fin 3 → ℚ}
    (hg : (g : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat s)) (t : TIdx) :
    g (tbasis t) = oddSign s t • tbasis t := by
  have h := LinearMap.congr_fun hg (tbasis t)
  rw [oddSignMat_eq_diagonal, toLin_diagonal_self] at h
  exact h

private theorem coe_mul_of_coe {g h : SpaceB ≃ₗ[ℚ] SpaceB} {s t : Fin 3 → ℚ}
    (hg : (g : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat s))
    (hh : (h : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat t)) :
    ((g * h : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) =
      toLin tbasis tbasis (oddSignMat (s * t)) := by
  rw [LinearEquiv.coe_toLinearMap_mul, hg, hh, ← oddSignMat_mul, Matrix.toLin_mul tbasis tbasis]
  rfl

theorem coe_conj_tauB {g : SpaceB ≃ₗ[ℚ] SpaceB} {G : Matrix TIdx TIdx ℚ}
    (hg : (g : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis G) :
    ((tauB * g * tauB⁻¹ : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) =
      toLin tbasis tbasis (tauMatᵀ * G * tauMat) := by
  rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul, coe_tauB, hg,
    Matrix.toLin_mul tbasis tbasis tbasis, Matrix.toLin_mul tbasis tbasis tbasis]
  rfl

private theorem eq_of_coe {g h : SpaceB ≃ₗ[ℚ] SpaceB} {s : Fin 3 → ℚ}
    (hg : (g : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat s))
    (hh : (h : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat s)) : g = h :=
  LinearEquiv.toLinearMap_injective (hg.trans hh.symm)

private theorem ne_of_coe {g h : SpaceB ≃ₗ[ℚ] SpaceB} {s t : Fin 3 → ℚ}
    (hg : (g : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat s))
    (hh : (h : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat t)) {k : Fin 3}
    (hk : s k ≠ t k) : g ≠ h := by
  intro hgh
  have e := congrArg (fun f : SpaceB ≃ₗ[ℚ] SpaceB => f (tbasis (.inr (.inr (.inl (0, 0, k))))))
    hgh
  simp only [apply_tbasis_of_coe hg, apply_tbasis_of_coe hh, oddSign_odd] at e
  exact hk ((smul_left_inj (tbasis.ne_zero _)).1 e)

private theorem coe_one_eq : ((1 : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) =
    toLin tbasis tbasis (oddSignMat fun _ => 1) := by
  rw [oddSignMat_one, Matrix.toLin_one]
  rfl

private theorem xB_mk (a : symMat) (b : SpaceX) (c : SpaceW) : xB (a, b, c) = (a, b, -c) := rfl

theorem xB_tbasis (t : TIdx) : xB (tbasis t) = oddSign sgnX t • tbasis t := by
  rcases t with i | ⟨p, k⟩ | ⟨c, i, k⟩ | o
  · rw [tbasis_diag, xB_mk, neg_zero]
    exact (one_smul ℚ _).symm
  · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    · rw [tbasis_pair_zero, xB_mk, neg_zero]
      exact (one_smul ℚ _).symm
    · rw [tbasis_pair_one, xB_mk, neg_zero]
      exact (one_smul ℚ _).symm
    · rw [tbasis_pair_two, xB_mk, neg_zero]
      exact (one_smul ℚ _).symm
  · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    · rw [tbasis_odd_zero, xB_mk, neg_zero]
      exact (one_smul ℚ _).symm
    · rw [tbasis_odd_one, xB_mk, oddSign_odd]
      simp [sgnX]
    · rw [tbasis_odd_two, xB_mk, oddSign_odd]
      simp [sgnX]
  · rw [tbasis_oct, xB_mk, neg_zero]
    exact (one_smul ℚ _).symm

theorem coe_xB : (xB : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat sgnX) := by
  refine tbasis.ext fun t => ?_
  rw [LinearEquiv.coe_coe, xB_tbasis, oddSignMat_eq_diagonal, toLin_diagonal_self]

/-- ⭐ The triality conjugate `yB = tauB · xB · tauB⁻¹` of the parity involution. -/
noncomputable def yB : SpaceB ≃ₗ[ℚ] SpaceB := tauB * xB * tauB⁻¹

/-- ⭐ The second triality conjugate `zB = tauB² · xB · tauB⁻²` of the parity involution. -/
noncomputable def zB : SpaceB ≃ₗ[ℚ] SpaceB := tauB ^ 2 * xB * (tauB ^ 2)⁻¹

theorem zB_eq : zB = tauB * yB * tauB⁻¹ := by
  rw [zB, yB, pow_two, _root_.mul_inv_rev]
  simp only [mul_assoc]

theorem coe_yB : (yB : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat sgnY) := by
  rw [yB, coe_conj_tauB coe_xB, tauMat_transpose_conj]
  rfl

theorem coe_zB : (zB : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat sgnZ) := by
  rw [zB_eq, coe_conj_tauB coe_yB, tauMat_transpose_conj]
  rfl

theorem yB_tbasis (t : TIdx) : yB (tbasis t) = oddSign sgnY t • tbasis t :=
  apply_tbasis_of_coe coe_yB t

theorem zB_tbasis (t : TIdx) : zB (tbasis t) = oddSign sgnZ t • tbasis t :=
  apply_tbasis_of_coe coe_zB t

theorem sgnX_mul_sgnY : sgnX * sgnY = sgnZ := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnY_mul_sgnX : sgnY * sgnX = sgnZ := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnY_mul_sgnZ : sgnY * sgnZ = sgnX := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnZ_mul_sgnY : sgnZ * sgnY = sgnX := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnZ_mul_sgnX : sgnZ * sgnX = sgnY := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnX_mul_sgnZ : sgnX * sgnZ = sgnY := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnX_mul_sgnX : sgnX * sgnX = fun _ => 1 := by
  funext k; fin_cases k <;> norm_num [sgnX]

theorem sgnY_mul_sgnY : sgnY * sgnY = fun _ => 1 := by
  funext k; fin_cases k <;> norm_num [sgnY]

theorem sgnZ_mul_sgnZ : sgnZ * sgnZ = fun _ => 1 := by
  funext k; fin_cases k <;> norm_num [sgnZ]

theorem xB_mul_yB : xB * yB = zB :=
  eq_of_coe (sgnX_mul_sgnY ▸ coe_mul_of_coe coe_xB coe_yB) coe_zB

theorem yB_mul_xB : yB * xB = zB :=
  eq_of_coe (sgnY_mul_sgnX ▸ coe_mul_of_coe coe_yB coe_xB) coe_zB

theorem yB_mul_zB : yB * zB = xB :=
  eq_of_coe (sgnY_mul_sgnZ ▸ coe_mul_of_coe coe_yB coe_zB) coe_xB

theorem zB_mul_yB : zB * yB = xB :=
  eq_of_coe (sgnZ_mul_sgnY ▸ coe_mul_of_coe coe_zB coe_yB) coe_xB

theorem zB_mul_xB : zB * xB = yB :=
  eq_of_coe (sgnZ_mul_sgnX ▸ coe_mul_of_coe coe_zB coe_xB) coe_yB

theorem xB_mul_zB : xB * zB = yB :=
  eq_of_coe (sgnX_mul_sgnZ ▸ coe_mul_of_coe coe_xB coe_zB) coe_yB

theorem yB_mul_self : yB * yB = 1 :=
  eq_of_coe (sgnY_mul_sgnY ▸ coe_mul_of_coe coe_yB coe_yB) coe_one_eq

theorem zB_mul_self : zB * zB = 1 :=
  eq_of_coe (sgnZ_mul_sgnZ ▸ coe_mul_of_coe coe_zB coe_zB) coe_one_eq

theorem xB_ne_yB : xB ≠ yB := ne_of_coe coe_xB coe_yB (k := 0) (by norm_num [sgnX, sgnY])

theorem xB_ne_zB : xB ≠ zB := ne_of_coe coe_xB coe_zB (k := 0) (by norm_num [sgnX, sgnZ])

theorem yB_ne_zB : yB ≠ zB := ne_of_coe coe_yB coe_zB (k := 1) (by norm_num [sgnY, sgnZ])

theorem one_ne_xB : (1 : SpaceB ≃ₗ[ℚ] SpaceB) ≠ xB :=
  ne_of_coe coe_one_eq coe_xB (k := 1) (by norm_num [sgnX])

theorem one_ne_yB : (1 : SpaceB ≃ₗ[ℚ] SpaceB) ≠ yB :=
  ne_of_coe coe_one_eq coe_yB (k := 0) (by norm_num [sgnY])

theorem one_ne_zB : (1 : SpaceB ≃ₗ[ℚ] SpaceB) ≠ zB :=
  ne_of_coe coe_one_eq coe_zB (k := 0) (by norm_num [sgnZ])

theorem conj_tauB_xB : tauB * xB * tauB⁻¹ = yB := rfl

theorem conj_tauB_yB : tauB * yB * tauB⁻¹ = zB := zB_eq.symm

theorem conj_tauB_zB : tauB * zB * tauB⁻¹ = xB := by
  have h : tauB * zB * tauB⁻¹ = tauB ^ 3 * xB * (tauB ^ 3)⁻¹ := by
    rw [zB]
    group
  rw [h, tauB_pow_three, inv_one, one_mul, mul_one]

noncomputable def fourGroupB : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) where
  carrier := {1, xB, yB, zB}
  mul_mem' := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp [xB_mul_self, yB_mul_self, zB_mul_self, xB_mul_yB, yB_mul_xB, yB_mul_zB, zB_mul_yB,
        zB_mul_xB, xB_mul_zB]
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro a (rfl | rfl | rfl | rfl)
    · simp
    · rw [inv_eq_of_mul_eq_one_right xB_mul_self]; simp
    · rw [inv_eq_of_mul_eq_one_right yB_mul_self]; simp
    · rw [inv_eq_of_mul_eq_one_right zB_mul_self]; simp

theorem mem_fourGroupB {g : SpaceB ≃ₗ[ℚ] SpaceB} :
    g ∈ fourGroupB ↔ g = 1 ∨ g = xB ∨ g = yB ∨ g = zB := Iff.rfl

theorem fourGroupB_eq_closure : fourGroupB = Subgroup.closure {xB, yB} := by
  apply le_antisymm
  · rintro g (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [← xB_mul_yB]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))

theorem sq_of_mem_fourGroupB {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ fourGroupB) : g * g = 1 := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact one_mul 1
  · exact xB_mul_self
  · exact yB_mul_self
  · exact zB_mul_self

theorem mul_comm_of_mem_fourGroupB {g h : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ fourGroupB)
    (hh : h ∈ fourGroupB) : g * h = h * g := by
  rcases hg with rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl <;>
    simp only [one_mul, mul_one, xB_mul_yB, yB_mul_xB, yB_mul_zB, zB_mul_yB, zB_mul_xB, xB_mul_zB]

theorem card_fourGroupB : Nat.card fourGroupB = 4 := by
  change Set.ncard ({1, xB, yB, zB} : Set (SpaceB ≃ₗ[ℚ] SpaceB)) = 4
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair yB_ne_zB]
  · rintro (h | h)
    · exact xB_ne_yB h
    · exact xB_ne_zB h
  · rintro (h | h | h)
    · exact one_ne_xB h
    · exact one_ne_yB h
    · exact one_ne_zB h

theorem bform_yB (u v : SpaceB) : bform (yB u) (yB v) = bform u v := by
  change bform (tauB (xB (tauB.symm u))) (tauB (xB (tauB.symm v))) = bform u v
  rw [bform_tauB, bform_xB, bform_tauB_symm]

theorem bform_zB (u v : SpaceB) : bform (zB u) (zB v) = bform u v := by
  rw [zB_eq]
  change bform (tauB (yB (tauB.symm u))) (tauB (yB (tauB.symm v))) = bform u v
  rw [bform_tauB, bform_yB, bform_tauB_symm]

theorem yB_mem_BR_iff {u : SpaceB} : yB u ∈ BR ↔ u ∈ BR := by
  change tauB (xB (tauB.symm u)) ∈ BR ↔ u ∈ BR
  rw [tauB_mem_BR_iff, xB_mem_BR_iff, tauB_symm_mem_BR_iff]

theorem zB_mem_BR_iff {u : SpaceB} : zB u ∈ BR ↔ u ∈ BR := by
  rw [zB_eq]
  change tauB (yB (tauB.symm u)) ∈ BR ↔ u ∈ BR
  rw [tauB_mem_BR_iff, yB_mem_BR_iff, tauB_symm_mem_BR_iff]

theorem bform_of_mem_fourGroupB {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ fourGroupB) (u v : SpaceB) :
    bform (g u) (g v) = bform u v := by
  rcases hg with rfl | rfl | rfl | rfl
  · rfl
  · exact bform_xB u v
  · exact bform_yB u v
  · exact bform_zB u v

theorem mem_BR_iff_of_mem_fourGroupB {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ fourGroupB)
    {u : SpaceB} : g u ∈ BR ↔ u ∈ BR := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact xB_mem_BR_iff
  · exact yB_mem_BR_iff
  · exact zB_mem_BR_iff

theorem map_BR_of_mem_fourGroupB {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ fourGroupB) :
    BR.map ((g : SpaceB →ₗ[ℚ] SpaceB).restrictScalars dyadic) = BR := by
  ext u
  refine ⟨?_, fun h => ⟨g.symm u, (mem_BR_iff_of_mem_fourGroupB hg).1 (by simpa using h),
    g.apply_symm_apply u⟩⟩
  rintro ⟨v, hv, rfl⟩
  exact (mem_BR_iff_of_mem_fourGroupB hg).2 hv

theorem eigenspace_conj_eq_map (e g : SpaceB ≃ₗ[ℚ] SpaceB) (μ : ℚ) :
    End.eigenspace ((e * g * e⁻¹ : SpaceB ≃ₗ[ℚ] SpaceB) : End ℚ SpaceB) μ =
      (End.eigenspace (g : End ℚ SpaceB) μ).map (e : SpaceB →ₗ[ℚ] SpaceB) := by
  ext u
  rw [End.mem_eigenspace_iff, Submodule.mem_map_equiv, End.mem_eigenspace_iff]
  change e (g (e.symm u)) = μ • u ↔ g (e.symm u) = μ • e.symm u
  constructor
  · intro h
    rw [← map_smul, ← h, LinearEquiv.symm_apply_apply]
  · intro h
    rw [h, map_smul, LinearEquiv.apply_symm_apply]

theorem finrank_eigenspace_conj (e g : SpaceB ≃ₗ[ℚ] SpaceB) (μ : ℚ) :
    finrank ℚ (End.eigenspace ((e * g * e⁻¹ : SpaceB ≃ₗ[ℚ] SpaceB) : End ℚ SpaceB) μ) =
      finrank ℚ (End.eigenspace (g : End ℚ SpaceB) μ) := by
  rw [eigenspace_conj_eq_map, LinearEquiv.finrank_map_eq]

theorem finrank_eigenspace_yB_neg_one :
    finrank ℚ (End.eigenspace (yB : End ℚ SpaceB) (-1)) = 98304 := by
  rw [yB, finrank_eigenspace_conj, finrank_eigenspace_xB_neg_one]

theorem finrank_eigenspace_zB_neg_one :
    finrank ℚ (End.eigenspace (zB : End ℚ SpaceB) (-1)) = 98304 := by
  rw [zB_eq, finrank_eigenspace_conj, finrank_eigenspace_yB_neg_one]

/-- The source's `rational_triality_four_group`, with the conjunct
`IsElementaryAbelian 2 fourGroupB` replaced by its content (commutativity and exponent 2), see the
port notes. -/
theorem rational_triality_four_group :
    yB = tauB * xB * tauB⁻¹ ∧ zB = tauB ^ 2 * xB * (tauB ^ 2)⁻¹ ∧
    (∀ t : TIdx, xB (tbasis t) = oddSign ![1, -1, -1] t • tbasis t) ∧
    (∀ t : TIdx, yB (tbasis t) = oddSign ![-1, 1, -1] t • tbasis t) ∧
    (∀ t : TIdx, zB (tbasis t) = oddSign ![-1, -1, 1] t • tbasis t) ∧
    (∀ g : SpaceB ≃ₗ[ℚ] SpaceB, g ∈ fourGroupB ↔ g = 1 ∨ g = xB ∨ g = yB ∨ g = zB) ∧
    fourGroupB = Subgroup.closure {xB, yB} ∧
    Nat.card fourGroupB = 4 ∧
    ((∀ g ∈ fourGroupB, ∀ h ∈ fourGroupB, g * h = h * g) ∧ (∀ g ∈ fourGroupB, g * g = 1)) ∧
    xB * yB = zB ∧ yB * zB = xB ∧ zB * xB = yB ∧
    yB * xB = zB ∧ zB * yB = xB ∧ xB * zB = yB ∧
    tauB * xB * tauB⁻¹ = yB ∧ tauB * yB * tauB⁻¹ = zB ∧ tauB * zB * tauB⁻¹ = xB ∧
    (∀ g ∈ fourGroupB, ∀ u v : SpaceB, bform (g u) (g v) = bform u v) ∧
    (∀ g ∈ fourGroupB, BR.map ((g : SpaceB →ₗ[ℚ] SpaceB).restrictScalars dyadic) = BR) ∧
    finrank ℚ (End.eigenspace (xB : End ℚ SpaceB) (-1)) = 98304 ∧
    finrank ℚ (End.eigenspace (yB : End ℚ SpaceB) (-1)) = 98304 ∧
    finrank ℚ (End.eigenspace (zB : End ℚ SpaceB) (-1)) = 98304 :=
  ⟨rfl, rfl, xB_tbasis, yB_tbasis, zB_tbasis, fun _ => Iff.rfl, fourGroupB_eq_closure,
    card_fourGroupB,
    ⟨fun _ hg _ hh => mul_comm_of_mem_fourGroupB hg hh, fun _ hg => sq_of_mem_fourGroupB hg⟩,
    xB_mul_yB, yB_mul_zB, zB_mul_xB,
    yB_mul_xB, zB_mul_yB, xB_mul_zB, conj_tauB_xB, conj_tauB_yB, conj_tauB_zB,
    fun _ hg => bform_of_mem_fourGroupB hg, fun _ hg => map_BR_of_mem_fourGroupB hg,
    finrank_eigenspace_xB_neg_one,
    finrank_eigenspace_yB_neg_one, finrank_eigenspace_zB_neg_one⟩

/-- Port addition: the parity involution lies in `AutO` (it is Axiom's extraspecial generator
`rhoEquiv zQ ∈ Gvis`). -/
theorem xB_mem_AutO : xB ∈ AutO :=
  Visible.rhoEquiv_zQ ▸ Visible.Gvis_le_AutO (Visible.rhoQ_le_Gvis (Visible.mem_rhoQ.2 ⟨zQ, rfl⟩))

end VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/Generated/Data.lean` -/

namespace VOA.Moonshine.MonsterGriess.Generated

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin
  VOA.Moonshine.MonsterGriess.Visible

/-- ⭐ **Axiom's generated group** `Gmat = ⟨Gvis, tauB⟩ ≤ GL_ℚ(SpaceB)` (the source's `Gmat`). -/
noncomputable def Gmat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  Subgroup.closure ((Gvis : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ∪ {tauB})

noncomputable def Hmat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := Gvis

noncomputable def Qmat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := rhoQ

noncomputable def xmat : SpaceB ≃ₗ[ℚ] SpaceB := rhoEquiv zQ

noncomputable def xmatTau : SpaceB ≃ₗ[ℚ] SpaceB := tauB * xmat * tauB⁻¹

noncomputable def xmatTau2 : SpaceB ≃ₗ[ℚ] SpaceB := tauB ^ 2 * xmat * (tauB ^ 2)⁻¹

noncomputable def Vmat : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) := fourGroupB

theorem xmat_eq_xB : xmat = xB := rhoEquiv_zQ

theorem xmatTau_eq : xmatTau = yB := by rw [xmatTau, xmat_eq_xB, yB]

theorem xmatTau2_eq : xmatTau2 = zB := by rw [xmatTau2, xmat_eq_xB, zB]

theorem mem_Vmat {g : SpaceB ≃ₗ[ℚ] SpaceB} :
    g ∈ Vmat ↔ g = 1 ∨ g = xmat ∨ g = xmatTau ∨ g = xmatTau2 := by
  rw [xmat_eq_xB, xmatTau_eq, xmatTau2_eq]
  exact rational_triality_four_group.2.2.2.2.2.1 g

theorem Hmat_le_Gmat : Hmat ≤ Gmat := fun _ hg =>
  Subgroup.subset_closure (Set.mem_union_left _ hg)

theorem tauB_mem_Gmat : tauB ∈ Gmat := Subgroup.subset_closure (Set.mem_union_right _ rfl)

theorem Qmat_le_Hmat : Qmat ≤ Hmat := rhoQ_le_Gvis

theorem xmat_mem_Qmat : xmat ∈ Qmat := mem_rhoQ.2 ⟨zQ, rfl⟩

theorem Vmat_le_Gmat : Vmat ≤ Gmat := by
  intro g hg
  rcases mem_Vmat.1 hg with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact Hmat_le_Gmat (Qmat_le_Hmat xmat_mem_Qmat)
  · exact mul_mem (mul_mem tauB_mem_Gmat (Hmat_le_Gmat (Qmat_le_Hmat xmat_mem_Qmat)))
      (inv_mem tauB_mem_Gmat)
  · exact mul_mem (mul_mem (pow_mem tauB_mem_Gmat 2)
      (Hmat_le_Gmat (Qmat_le_Hmat xmat_mem_Qmat))) (inv_mem (pow_mem tauB_mem_Gmat 2))

theorem generated_rational_group_data :
    Gmat = Subgroup.closure ((Gvis : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ∪ {tauB}) ∧ Hmat = Gvis ∧
    Qmat = rhoQ ∧ xmat = rhoEquiv zQ ∧ (zQ : GL SpinIdx ℚ) = -1 ∧
    xmatTau = tauB * xmat * tauB⁻¹ ∧ xmatTau2 = tauB ^ 2 * xmat * (tauB ^ 2)⁻¹ ∧
    (∀ g, g ∈ Vmat ↔ g = 1 ∨ g = xmat ∨ g = xmatTau ∨ g = xmatTau2) ∧
    Hmat ≤ Gmat ∧ tauB ∈ Gmat ∧ Qmat ≤ Hmat ∧ xmat ∈ Qmat ∧ Vmat ≤ Gmat :=
  ⟨rfl, rfl, rfl, rfl, coe_zQ, rfl, rfl, fun _ => mem_Vmat, Hmat_le_Gmat, tauB_mem_Gmat,
    Qmat_le_Hmat, xmat_mem_Qmat, Vmat_le_Gmat⟩

/-! ### Port additions: `Gmat ≤ AutO` reduced to `IsAlgAut tauB` -/

/-- `Gmat` in the generator shape `⟨insert tauB Gvis⟩`. -/
theorem Gmat_eq_closure_insert :
    Gmat = Subgroup.closure (insert tauB (Gvis : Set (SpaceB ≃ₗ[ℚ] SpaceB))) := by
  rw [Gmat, Set.union_singleton]

/-- `tauB` is in `AutO` exactly when it preserves the Griess product (it preserves `bform` by
`bform_tauB`). -/
theorem tauB_mem_AutO_iff : tauB ∈ AutO ↔ IsAlgAut tauB :=
  ⟨fun h => h.1, fun h => ⟨h, bform_tauB⟩⟩

/-- `Gmat ≤ AutO` exactly when `tauB ∈ AutO` (`Gvis ≤ AutO` is `Visible.Gvis_le_AutO`). -/
theorem Gmat_le_AutO_iff : Gmat ≤ AutO ↔ tauB ∈ AutO := by
  refine ⟨fun h => h tauB_mem_Gmat, fun h => ?_⟩
  rw [Gmat, Subgroup.closure_le]
  rintro g (hg | rfl)
  · exact Gvis_le_AutO hg
  · exact h

/-- `Gmat ≤ AutO`, conditional on the source's `tauB_gmul` (not ported). -/
theorem Gmat_le_AutO_of_isAlgAut (h : IsAlgAut tauB) : Gmat ≤ AutO :=
  Gmat_le_AutO_iff.2 (tauB_mem_AutO_iff.2 h)

end VOA.Moonshine.MonsterGriess.Generated
