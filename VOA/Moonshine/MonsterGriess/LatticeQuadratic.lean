/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean
v4.35.0-rc3 with the module system), files:
  CFSG/Monster/CodeLattice.lean
  CFSG/Monster/CodeLatticeUnimodular.lean
  CFSG/Monster/Code/LatticeBasic.lean
  CFSG/Monster/SpinLattice/Lambda.lean
  CFSG/Monster/SpinLattice/Cocode.lean
  CFSG/Monster/Griess/Short.lean
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
import VOA.Moonshine.MonsterGriess.Short
import VOA.Moonshine.MonsterGriess.CodeCocycle
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Axiom's Monster port: the quadratic form on `Λ/2Λ` and the coordinate isomorphism `phi0Equiv`

`L2 = Λ/2Λ` (Leech lattice in Conway's `√8`-scaled integer coordinates, `Λ = codeLattice C`)
carries the quadratic form `qL(ū) = (u·u/16) mod 2` with polar form `bL(ū, v̄) = (u·v/8) mod 2`.
Axiom Math's coordinate map `phi0 : C × Cocode → L2`, `phi0 (a, δ) = lamT a + lamCocode δ`,
is a `ZMod 2`-linear isomorphism, and in its coordinates

* `qL_phi0` — `qL (phi0 (a, δ)) = pair a δ`;
* `bL_phi0` — `bL (phi0 (a, δ)) (phi0 (b, ε)) = pair a ε + pair b δ`.

## Main results
* `lamT_add` — additivity of `lamT` (from `lamCodeCls_add` and `thetaD_add`); `phi0_add`,
  `phi0Lin` (the bundled linear map, with `phi0Lin_apply : phi0Lin p = phi0 p` by `rfl`).
* `qL_cls`, `bL_cls` — the quadratic and polar forms on representatives.
* `phi0_injective`, `finrank_L2` (`= 24`), `phi0_bijective`, `phi0Equiv`.
* `pair_eq_zero_of_isShortCoord` — `pair a δ = 0` whenever `phi0 (a, δ)` is the class of a
  minimal vector (`qL` of a norm-`4` class vanishes).

## Port notes
* Namespaces `CFSG.Monster`, `CFSG.Monster.Code`, `CFSG.Monster.SpinLattice`,
  `CFSG.Monster.Griess` ↦ `VOA.Moonshine.MonsterGriess`, `….Code`, `….SpinLattice`,
  `VOA.Moonshine.MonsterGriess`.  Module-system syntax dropped.  Bodies verbatim except as
  listed here.
* **`phi0`.** Our `Short.lean` ports `phi0` as the underlying function of the source's bundled
  map.  Here the bundled map is `phi0Lin` (the source's definition of `phi0`, verbatim), and
  `phi0Lin_apply` is `rfl`; `phi0_injective`, `phi0_bijective` are stated for the function and
  proved through `phi0Lin`.  `phi0Equiv` is the source's definition, over `phi0Lin`.
* **Rank of `Λ`.** The source proves `finrank (ZMod 2) L2 = 24` from a `ℤ`-basis of
  `codeLatticeSubgroup` of size 24 obtained through the index `[ℤ²⁴ : Λ] = 2³⁶`
  (`nonempty_basis_codeLattice`, which needs the mod-4 residue machinery).  We obtain the basis
  from `Submodule.basisOfPid` and bound its size below by the 24 independent vectors `8eᵢ ∈ Λ`
  (`smul_eight_mem_codeLattice`, from the same source file), above by `Submodule.finrank_le`.
* `qL_classOf_minVecs` reads `u·u = 32` directly off `codeForm u u = 4` instead of the source's
  `mem_minVecs_iff`/`normSq` route.
* Omitted: unimodularity, nondegeneracy of `bL`, `lamSum_single`, `lamCode_of_P_zero/one`,
  `Pint_eq`, `lamVec_eq_sum`, `phi0_thetaD`.
-/

namespace VOA.Moonshine.MonsterGriess

open Module

variable {C : Submodule (ZMod 2) (Fin 24 → ZMod 2)}

/-! ### From `CFSG/Monster/CodeLattice.lean` -/
theorem smul_eight_mem_codeLattice (x : Fin 24 → ℤ) : (8 : ℤ) • x ∈ codeLattice C := by
  refine ⟨0, .inl rfl, 0, C.zero_mem, fun i => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, bitLift, ZMod.val_zero, Nat.cast_zero,
      mul_zero, add_zero]
    exact (Int.modEq_zero_iff_dvd.2 (Dvd.dvd.mul_right (by norm_num) _))
  · simp only [Pi.smul_apply, smul_eq_mul, mul_zero, ← Finset.mul_sum]
    exact Int.modEq_zero_iff_dvd.2 (Dvd.intro _ rfl)

theorem sum_mul_self_emod_sixteen (hC4 : ∀ d ∈ C, weight d % 4 = 0) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLattice C) : (∑ i, u i * u i) % 16 = 0 := by
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hu
  set b : Fin 24 → ℤ := fun i => bitLift (d i) with hbdef
  have hb : ∀ i, b i = 0 ∨ b i = 1 := fun i => bitLift_zero_or_one (d i)
  set k : Fin 24 → ℤ := fun i => (u i - m - 2 * b i) / 4 with hkdef
  have huk : ∀ i, u i = m + 2 * b i + 4 * k i := by
    intro i
    have h := hud i
    unfold Int.ModEq at h
    simp only [hkdef, hbdef]
    omega
  have hsq : ∀ i, u i * u i =
      m + 4 * b i + 16 * (k i * k i) + 4 * m * b i + 8 * m * k i + 16 * (b i * k i) := by
    intro i
    rw [huk i]
    have hm2 : m * m = m := by rcases hm with rfl | rfl <;> norm_num
    have hb2 : b i * b i = b i := by rcases hb i with h | h <;> rw [h] <;> norm_num
    linear_combination hm2 + 4 * hb2
  have hw : weight d = ∑ i, b i := rfl
  have hw4 : (∑ i, b i) % 4 = 0 := hw ▸ hC4 d hd
  have hsum : ∑ i, u i = 24 * m + 2 * ∑ i, b i + 4 * ∑ i, k i := by
    rw [Finset.sum_congr rfl (fun i _ => huk i)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  have hsq_sum : ∑ i, u i * u i = 24 * m + 4 * ∑ i, b i + 16 * ∑ i, (k i * k i) +
      4 * m * ∑ i, b i + 8 * m * ∑ i, k i + 16 * ∑ i, (b i * k i) := by
    rw [Finset.sum_congr rfl (fun i _ => hsq i)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  rw [hsq_sum]
  unfold Int.ModEq at hus
  rw [hsum] at hus
  rcases hm with rfl | rfl
  · simp only [zero_mul, add_zero, mul_zero] at hus ⊢
    omega
  · simp only [mul_one] at hus ⊢
    omega

theorem sum_mul_emod_eight (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    (∑ i, u i * v i) % 8 = 0 := by
  have h1 := sum_mul_self_emod_sixteen hC4 (add_mem_codeLattice hΩ hu hv)
  have h2 := sum_mul_self_emod_sixteen hC4 hu
  have h3 := sum_mul_self_emod_sixteen hC4 hv
  have e : ∑ i, (u + v) i * (u + v) i =
      ∑ i, u i * u i + ∑ i, v i * v i + 2 * ∑ i, u i * v i := by
    simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e] at h1
  omega

/-! ### From `CFSG/Monster/CodeLatticeUnimodular.lean` -/
def hInt (u v : Fin 24 → ℤ) : ℤ := (∑ i, u i * v i) / 8

theorem eight_mul_hInt (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    8 * hInt u v = ∑ i, u i * v i := by
  have := sum_mul_emod_eight hΩ hC4 hu hv
  unfold hInt
  omega

theorem hInt_comm (u v : Fin 24 → ℤ) : hInt u v = hInt v u := by
  simp only [hInt, mul_comm]

theorem hInt_add_left (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    {u u' v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hu' : u' ∈ codeLattice C)
    (hv : v ∈ codeLattice C) : hInt (u + u') v = hInt u v + hInt u' v := by
  have h1 := eight_mul_hInt hΩ hC4 (add_mem_codeLattice hΩ hu hu') hv
  have h2 := eight_mul_hInt hΩ hC4 hu hv
  have h3 := eight_mul_hInt hΩ hC4 hu' hv
  have e : ∑ i, (u + u') i * v i = ∑ i, u i * v i + ∑ i, u' i * v i := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  omega

theorem hInt_smul_left (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0) (c : ℤ)
    {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    hInt (c • u) v = c * hInt u v := by
  have hcu : c • u ∈ codeLattice C := (codeLatticeSubgroup hΩ).zsmul_mem hu c
  have h1 := eight_mul_hInt hΩ hC4 hcu hv
  have h2 := eight_mul_hInt hΩ hC4 hu hv
  have e : ∑ i, (c • u) i * v i = c * ∑ i, u i * v i := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [e, ← h2] at h1
  linarith

theorem two_dvd_hInt_self (hC4 : ∀ d ∈ C, weight d % 4 = 0) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLattice C) : 2 ∣ hInt u u := by
  have := sum_mul_self_emod_sixteen hC4 hu
  unfold hInt
  omega

theorem hInt_add_two_smul (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    {u w : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hw : w ∈ codeLattice C) :
    hInt (u + (2 : ℤ) • w) (u + (2 : ℤ) • w) = hInt u u + 4 * hInt u w + 4 * hInt w w := by
  have h2w : (2 : ℤ) • w ∈ codeLattice C := (codeLatticeSubgroup hΩ).zsmul_mem hw 2
  have huw : u + (2 : ℤ) • w ∈ codeLattice C := add_mem_codeLattice hΩ hu h2w
  rw [hInt_add_left hΩ hC4 hu h2w huw, hInt_smul_left hΩ hC4 2 hw huw, hInt_comm u,
    hInt_comm w, hInt_add_left hΩ hC4 hu h2w hu, hInt_add_left hΩ hC4 hu h2w hw,
    hInt_smul_left hΩ hC4 2 hw hu, hInt_smul_left hΩ hC4 2 hw hw, hInt_comm w u]
  ring

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact .inl rfl
  · exact .inr rfl

variable (C) in
def codeQuad (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0) :
    codeLatticeModTwo C hΩ → ZMod 2 :=
  Quotient.lift
    (s := (LinearMap.range (LinearMap.lsmul ℤ (codeLatticeSubgroup hΩ) ((2 : ℕ) : ℤ))).quotientRel)
    (fun u => ((hInt u u / 2 : ℤ) : ZMod 2)) (by
      intro u u' huu'
      have h := (Submodule.quotientRel_def _).1 huu'
      obtain ⟨w, hw⟩ := (mem_two_range_iff hΩ _).1 h
      have hu : (u : Fin 24 → ℤ) = u' + (2 : ℤ) • (w : Fin 24 → ℤ) := by
        rw [hw]
        simp
      beta_reduce
      rw [hu, hInt_add_two_smul hΩ hC4 u'.2 w.2]
      have he := two_dvd_hInt_self hC4 u'.2
      have : (hInt u' u' + 4 * hInt u' w + 4 * hInt w w) / 2 =
          hInt u' u' / 2 + 2 * (hInt u' w + hInt w w) := by omega
      rw [this]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero])

theorem codeQuad_mk (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (u : codeLatticeSubgroup hΩ) :
    codeQuad C hΩ hC4 (Submodule.Quotient.mk u) = ((hInt u u / 2 : ℤ) : ZMod 2) := rfl

theorem codeQuad_zero (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0) :
    codeQuad C hΩ hC4 0 = 0 := by
  rw [← Submodule.Quotient.mk_zero, codeQuad_mk]
  simp [hInt]

theorem polar_codeQuad_mk (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (u v : codeLatticeSubgroup hΩ) :
    QuadraticMap.polar (codeQuad C hΩ hC4) (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) =
      ((hInt u v : ℤ) : ZMod 2) := by
  rw [QuadraticMap.polar, ← Submodule.Quotient.mk_add, codeQuad_mk, codeQuad_mk, codeQuad_mk]
  have huv : ((u + v : codeLatticeSubgroup hΩ) : Fin 24 → ℤ) = (u : Fin 24 → ℤ) + v := rfl
  rw [huv, hInt_add_left hΩ hC4 u.2 v.2 (add_mem_codeLattice hΩ u.2 v.2), hInt_comm u,
    hInt_comm v, hInt_add_left hΩ hC4 u.2 v.2 u.2, hInt_add_left hΩ hC4 u.2 v.2 v.2,
    hInt_comm v u]
  have hu := two_dvd_hInt_self hC4 u.2
  have hv := two_dvd_hInt_self hC4 v.2
  have : (hInt u u + hInt u v + (hInt u v + hInt v v)) / 2 =
      hInt u u / 2 + hInt v v / 2 + hInt u v := by omega
  rw [this]
  push_cast
  ring

variable (C) in
noncomputable def codeQuadForm (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0) :
    QuadraticForm (ZMod 2) (codeLatticeModTwo C hΩ) :=
  QuadraticMap.ofPolar (codeQuad C hΩ hC4)
    (by
      intro a x
      rcases zmod_two_cases a with rfl | rfl
      · rw [zero_smul, codeQuad_zero, mul_zero, zero_smul]
      · rw [one_smul, mul_one, one_smul])
    (by
      intro x x' y
      induction x using Submodule.Quotient.induction_on with | H u => ?_
      induction x' using Submodule.Quotient.induction_on with | H u' => ?_
      induction y using Submodule.Quotient.induction_on with | H v => ?_
      rw [← Submodule.Quotient.mk_add, polar_codeQuad_mk, polar_codeQuad_mk, polar_codeQuad_mk]
      have : ((u + u' : codeLatticeSubgroup hΩ) : Fin 24 → ℤ) = (u : Fin 24 → ℤ) + u' := rfl
      rw [this, hInt_add_left hΩ hC4 u.2 u'.2 v.2]
      push_cast
      ring)
    (by
      intro a x y
      rcases zmod_two_cases a with rfl | rfl
      · rw [zero_smul, zero_smul, QuadraticMap.polar, zero_add, codeQuad_zero]
        ring
      · rw [one_smul, one_smul])

theorem codeQuadForm_mk (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (u : codeLatticeSubgroup hΩ) :
    codeQuadForm C hΩ hC4 (Submodule.Quotient.mk u) = ((hInt u u / 2 : ℤ) : ZMod 2) :=
  codeQuad_mk hΩ hC4 u

theorem polarBilin_codeQuadForm_mk (hΩ : allOnes ∈ C) (hC4 : ∀ d ∈ C, weight d % 4 = 0)
    (u v : codeLatticeSubgroup hΩ) :
    QuadraticMap.polarBilin (codeQuadForm C hΩ hC4) (Submodule.Quotient.mk u)
      (Submodule.Quotient.mk v) = ((hInt u v : ℤ) : ZMod 2) := by
  rw [QuadraticMap.polarBilin_apply_apply]
  exact polar_codeQuad_mk hΩ hC4 u v

end VOA.Moonshine.MonsterGriess

namespace VOA.Moonshine.MonsterGriess.Code

open VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/Code/LatticeBasic.lean` -/
theorem weight_mod_four {d : Fin 24 → ZMod 2} (hd : d ∈ C) : weight d % 4 = 0 := by
  rw [weight_eq_hammingNorm]
  obtain ⟨k, hk⟩ := four_dvd_wt hd
  rw [hk]
  push_cast
  omega

end VOA.Moonshine.MonsterGriess.Code

namespace VOA.Moonshine.MonsterGriess.SpinLattice

open Module VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code
  VOA.Moonshine.MonsterGriess.Spin

/-! ### From `CFSG/Monster/SpinLattice/Lambda.lean` -/
theorem weight_mod_four' : ∀ d ∈ C, weight d % 4 = 0 := fun _ hd => weight_mod_four hd

/-- The quadratic form `qL(ū) = (u·u/16) mod 2` on `Λ/2Λ`. -/
noncomputable abbrev qL : QuadraticForm (ZMod 2) L2 :=
  codeQuadForm C allOnes_mem_C weight_mod_four'

theorem qL_cls {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    qL (cls u hu) = ((hInt u u / 2 : ℤ) : ZMod 2) :=
  codeQuadForm_mk allOnes_mem_C weight_mod_four' ⟨u, hu⟩

theorem bL_cls {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    QuadraticMap.polarBilin qL (cls u hu) (cls v hv) = ((hInt u v : ℤ) : ZMod 2) :=
  polarBilin_codeQuadForm_mk allOnes_mem_C weight_mod_four' ⟨u, hu⟩ ⟨v, hv⟩

theorem bitLift_mul (x y : ZMod 2) : bitLift (x * y) = bitLift x * bitLift y := by
  fin_cases x <;> fin_cases y <;> rfl

theorem bitLift_sq (x : ZMod 2) : bitLift x * bitLift x = bitLift x := by
  fin_cases x <;> rfl

theorem sum_bitLift_mul (a b : Fin 24 → ZMod 2) :
    ∑ i, bitLift (a i) * bitLift (b i) = hammingNorm (a * b) := by
  rw [← sum_bitLift]
  exact Finset.sum_congr rfl fun i _ => (bitLift_mul _ _).symm

theorem Pint_zero_or_one (a : Fin 24 → ZMod 2) : Pint a = 0 ∨ Pint a = 1 := bitLift_zero_or_one _

private theorem bit01 (x : ZMod 2) : bitLift x = 0 ∨ bitLift x = 1 := bitLift_zero_or_one x

theorem hInt_lamSum (v w : Fin 24 → ZMod 2) :
    hInt (lamSum v) (lamSum w) = 2 * (hammingNorm v : ℤ) * (hammingNorm w : ℤ) +
      2 * (hammingNorm (v * w) : ℤ) := by
  have e : ∑ k, lamSum v k * lamSum w k = 16 * (hammingNorm v : ℤ) * (hammingNorm w : ℤ) +
      16 * (hammingNorm (v * w) : ℤ) := by
    have h := sum_affine (fun k => bitLift (v k)) (fun k => bitLift (w k))
      ((hammingNorm v : ℤ) * (hammingNorm w : ℤ)) (-4 * (hammingNorm w : ℤ))
      (-4 * (hammingNorm v : ℤ)) 16
    rw [sum_bitLift, sum_bitLift, sum_bitLift_mul] at h
    rw [show (∑ k, lamSum v k * lamSum w k) = ∑ k, ((hammingNorm v : ℤ) * (hammingNorm w : ℤ) +
        -4 * (hammingNorm w : ℤ) * bitLift (v k) + -4 * (hammingNorm v : ℤ) * bitLift (w k) +
        16 * (bitLift (v k) * bitLift (w k))) from
      Finset.sum_congr rfl fun k _ => by simp only [lamSum]; ring, h]
    ring
  rw [hInt, e, show 16 * (hammingNorm v : ℤ) * (hammingNorm w : ℤ) + 16 * (hammingNorm (v * w) : ℤ)
    = 8 * (2 * (hammingNorm v : ℤ) * (hammingNorm w : ℤ) + 2 * (hammingNorm (v * w) : ℤ)) by ring,
    Int.mul_ediv_cancel_left _ (by norm_num)]

theorem qL_lamVec (v : Fin 24 → ZMod 2) : qL (lamVec v) = 0 := by
  rw [lamVec, qL_cls, hInt_lamSum]
  have h : 2 * (hammingNorm v : ℤ) * (hammingNorm v : ℤ) + 2 * (hammingNorm (v * v) : ℤ) =
      2 * ((hammingNorm v : ℤ) * (hammingNorm v : ℤ) + (hammingNorm v : ℤ)) := by
    have : v * v = v := by
      funext k
      simp only [Pi.mul_apply]
      generalize v k = x
      fin_cases x <;> rfl
    rw [this]; ring
  rw [h, Int.mul_ediv_cancel_left _ (by norm_num)]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (by
    have := Int.even_mul_succ_self (hammingNorm v : ℤ)
    rw [mul_add, mul_one] at this
    exact even_iff_two_dvd.1 this)

theorem bL_lamVec_lamVec (v w : Fin 24 → ZMod 2) :
    QuadraticMap.polarBilin qL (lamVec v) (lamVec w) = 0 := by
  rw [lamVec, lamVec, bL_cls, hInt_lamSum]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2
    ⟨(hammingNorm v : ℤ) * (hammingNorm w : ℤ) + (hammingNorm (v * w) : ℤ), by ring⟩

theorem cast_Pint (a : Fin 24 → ZMod 2) : ((Pint a : ℤ) : ZMod 2) = P a := bitLift_cast _

theorem P_eq_of_hammingNorm {a : Fin 24 → ZMod 2} {s : ℕ} (hs : hammingNorm a = 4 * s) :
    P a = (s : ZMod 2) := by
  rw [P, hs, Nat.mul_div_cancel_left _ (by norm_num)]

theorem qL_lamCodeCls {a : Fin 24 → ZMod 2} (ha : a ∈ C) : qL (lamCodeCls ha) = P a := by
  obtain ⟨s, hs⟩ := four_dvd_wt ha
  have hP := Pint_zero_or_one a
  have e : ∑ k, lamCode a k * lamCode a k = 8 * (12 * Pint a + 2 * s - 4 * (Pint a * s)) := by
    have h := sum_affine (fun k => bitLift (a k)) (fun k => bitLift (a k)) (4 * Pint a)
      (4 - 8 * Pint a) 0 0
    rw [sum_bitLift, sum_bitLift_mul] at h
    rw [show (∑ k, lamCode a k * lamCode a k) = ∑ k, (4 * Pint a + (4 - 8 * Pint a) *
        bitLift (a k) + 0 * bitLift (a k) + 0 * (bitLift (a k) * bitLift (a k))) from
      Finset.sum_congr rfl fun k _ => by
        simp only [lamCode]
        rcases bit01 (a k) with hb | hb <;> rcases hP with hp | hp <;> rw [hb, hp] <;> ring, h, hs]
    push_cast
    ring
  rw [lamCodeCls, qL_cls, hInt, e, Int.mul_ediv_cancel_left _ (by norm_num)]
  have h2 : (12 * Pint a + 2 * (s : ℤ) - 4 * (Pint a * s)) / 2 =
      6 * Pint a + s - 2 * (Pint a * s) := by omega
  rw [h2]
  push_cast
  rw [cast_Pint, P_eq_of_hammingNorm hs]
  generalize ((s : ℕ) : ZMod 2) = x
  revert x
  decide

theorem bL_lamCodeCls_lamVec {a : Fin 24 → ZMod 2} (ha : a ∈ C) (v : Fin 24 → ZMod 2) :
    QuadraticMap.polarBilin qL (lamCodeCls ha) (lamVec v) = a ⬝ᵥ v := by
  obtain ⟨s, hs⟩ := four_dvd_wt ha
  have e : ∑ k, lamCode a k * lamSum v k =
      8 * (5 * Pint a * (hammingNorm v : ℤ) + ((hammingNorm v : ℤ) - 2 * Pint a *
        (hammingNorm v : ℤ)) * s + (2 * Pint a - 1) * (hammingNorm (a * v) : ℤ)) := by
    have h := sum_affine (fun k => bitLift (a k)) (fun k => bitLift (v k))
      (2 * Pint a * (hammingNorm v : ℤ)) (2 * (hammingNorm v : ℤ) - 4 * Pint a *
        (hammingNorm v : ℤ)) (-8 * Pint a) (16 * Pint a - 8)
    rw [sum_bitLift, sum_bitLift, sum_bitLift_mul] at h
    rw [show (∑ k, lamCode a k * lamSum v k) = ∑ k, (2 * Pint a * (hammingNorm v : ℤ) +
        (2 * (hammingNorm v : ℤ) - 4 * Pint a * (hammingNorm v : ℤ)) * bitLift (a k) +
        -8 * Pint a * bitLift (v k) + (16 * Pint a - 8) * (bitLift (a k) * bitLift (v k))) from
      Finset.sum_congr rfl fun k _ => by simp only [lamCode, lamSum]; ring, h, hs]
    push_cast
    ring
  rw [lamCodeCls, lamVec, bL_cls, hInt, e, Int.mul_ediv_cancel_left _ (by norm_num),
    dotProduct_eq_hammingNorm]
  push_cast
  rw [cast_Pint, P_eq_of_hammingNorm hs]
  generalize ((s : ℕ) : ZMod 2) = x
  generalize ((hammingNorm v : ℕ) : ZMod 2) = y
  generalize ((hammingNorm (a * v) : ℕ) : ZMod 2) = z
  revert x y z
  decide

theorem bL_lamCodeCls_lamCodeCls {a b : Fin 24 → ZMod 2} (ha : a ∈ C) (hb : b ∈ C) :
    QuadraticMap.polarBilin qL (lamCodeCls ha) (lamCodeCls hb) = K a b := by
  obtain ⟨s, hs⟩ := four_dvd_wt ha
  obtain ⟨t, ht⟩ := four_dvd_wt hb
  obtain ⟨m, hm⟩ := two_dvd_hammingNorm_mul ha hb
  have hP := Pint_zero_or_one a
  have hR := Pint_zero_or_one b
  have e : ∑ k, lamCode a k * lamCode b k = 8 * (12 * Pint a * Pint b + 2 * Pint b * s -
      4 * Pint a * Pint b * s + 2 * Pint a * t - 4 * Pint a * Pint b * t + m - 2 * Pint b * m -
      2 * Pint a * m + 4 * Pint a * Pint b * m) := by
    have h := sum_affine (fun k => bitLift (a k)) (fun k => bitLift (b k)) (4 * Pint a * Pint b)
      (4 * Pint b - 8 * Pint a * Pint b) (4 * Pint a - 8 * Pint a * Pint b)
      (4 - 8 * Pint b - 8 * Pint a + 16 * Pint a * Pint b)
    rw [sum_bitLift, sum_bitLift, sum_bitLift_mul] at h
    rw [show (∑ k, lamCode a k * lamCode b k) = ∑ k, (4 * Pint a * Pint b +
        (4 * Pint b - 8 * Pint a * Pint b) * bitLift (a k) +
        (4 * Pint a - 8 * Pint a * Pint b) * bitLift (b k) +
        (4 - 8 * Pint b - 8 * Pint a + 16 * Pint a * Pint b) * (bitLift (a k) * bitLift (b k))) from
      Finset.sum_congr rfl fun k _ => by simp only [lamCode]; ring, h, hs, ht, hm]
    push_cast
    ring
  rw [lamCodeCls, lamCodeCls, bL_cls, hInt, e, Int.mul_ediv_cancel_left _ (by norm_num), K_eq,
    hm, Nat.mul_div_cancel_left _ (by norm_num)]
  push_cast
  rw [cast_Pint, cast_Pint]
  generalize P a = x
  generalize P b = y
  generalize ((s : ℕ) : ZMod 2) = u
  generalize ((t : ℕ) : ZMod 2) = u'
  generalize ((m : ℕ) : ZMod 2) = z
  revert x y u u' z
  decide

theorem lamCodeCls_add {a b : Fin 24 → ZMod 2} (ha : a ∈ C) (hb : b ∈ C) :
    lamCodeCls ha + lamCodeCls hb = lamCodeCls (C.add_mem ha hb) + lamVec (a * b) := by
  obtain ⟨s, hs⟩ := four_dvd_wt ha
  obtain ⟨t, ht⟩ := four_dvd_wt hb
  obtain ⟨m, hm⟩ := two_dvd_hammingNorm_mul ha hb
  set P₁ := Pint a
  set R₁ := Pint b
  set S₁ := Pint (a + b)
  have hpar : (2 : ℤ) ∣ P₁ + R₁ - S₁ - m := by
    have h := P_add ha hb
    rw [K_eq, hm, Nat.mul_div_cancel_left _ (by norm_num)] at h
    have h0 : ((P₁ + R₁ - S₁ - m : ℤ) : ZMod 2) = 0 := by
      push_cast
      rw [cast_Pint, cast_Pint, cast_Pint, h]
      generalize P a = x
      generalize P b = y
      generalize ((m : ℕ) : ZMod 2) = z
      revert x y z
      decide
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (P₁ + R₁ - S₁ - m) 2).1 h0
    exact_mod_cast h1
  obtain ⟨c', hc'⟩ := hpar
  set w : Fin 24 → ℤ := fun k => 2 * c' + (2 * S₁ - 2 * P₁) * bitLift (a k) +
    (2 * S₁ - 2 * R₁) * bitLift (b k) + (4 - 4 * S₁) * (bitLift (a k) * bitLift (b k)) with hwdef
  have hw : w ∈ codeLattice C := by
    refine mem_of_even (y := fun k => c' + (S₁ - P₁) * bitLift (a k) + (S₁ - R₁) * bitLift (b k) +
      (2 - 2 * S₁) * (bitLift (a k) * bitLift (b k))) (fun k => by simp only [hwdef]; ring) ?_ ?_
    · have : (fun k => ((c' + (S₁ - P₁) * bitLift (a k) + (S₁ - R₁) * bitLift (b k) +
          (2 - 2 * S₁) * (bitLift (a k) * bitLift (b k)) : ℤ) : ZMod 2)) =
          (c' : ZMod 2) • Ω + ((S₁ - P₁ : ℤ) : ZMod 2) • a + ((S₁ - R₁ : ℤ) : ZMod 2) • b := by
        funext k
        simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, bitLift_cast, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Ω, mul_one]
        rw [show ((2 : ℤ) : ZMod 2) = 0 from rfl]
        ring
      rw [this]
      exact C.add_mem (C.add_mem (C.smul_mem _ Ω_mem_C) (C.smul_mem _ ha)) (C.smul_mem _ hb)
    · have h := sum_affine (fun k => bitLift (a k)) (fun k => bitLift (b k)) (2 * c')
        (2 * S₁ - 2 * P₁) (2 * S₁ - 2 * R₁) (4 - 4 * S₁)
      rw [sum_bitLift, sum_bitLift, sum_bitLift_mul, hs, ht, hm] at h
      rw [show (∑ k, w k) = _ from h]
      push_cast
      have e : 24 * (2 * c') + (2 * S₁ - 2 * P₁) * (4 * (s : ℤ)) + (2 * S₁ - 2 * R₁) * (4 * t) +
          (4 - 4 * S₁) * (2 * m) = 8 * (6 * c' + (S₁ - P₁) * s + (S₁ - R₁) * t + (1 - S₁) * m) := by
        ring
      rw [e]
      omega
  have hvec : lamCode a + lamCode b = lamCode (a + b) + lamSum (a * b) + (2 : ℤ) • w := by
    funext k
    have h3 := bitLift_add' (a k) (b k)
    have h12 := bitLift_mul (a k) (b k)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lamCode, lamSum, Pi.mul_apply, hwdef]
    rw [h12, hm]
    have hb3 : bitLift (a k + b k) = bitLift (a k) + bitLift (b k) - 2 * (bitLift (a k) *
        bitLift (b k)) := by
      rw [h12] at h3; linarith
    rw [hb3]
    push_cast
    linear_combination (2 : ℤ) * hc'
  have h2w : (2 : ℤ) • w ∈ codeLattice C := (codeLatticeSubgroup allOnes_mem_C).zsmul_mem hw 2
  have hXY : lamCode (a + b) + lamSum (a * b) ∈ codeLattice C :=
    add_mem_codeLattice allOnes_mem_C (lamCode_mem (C.add_mem ha hb)) (lamSum_mem _)
  calc lamCodeCls ha + lamCodeCls hb = cls (lamCode a + lamCode b)
        (add_mem_codeLattice allOnes_mem_C (lamCode_mem ha) (lamCode_mem hb)) := cls_add _ _
    _ = cls (lamCode (a + b) + lamSum (a * b) + (2 : ℤ) • w)
        (add_mem_codeLattice allOnes_mem_C hXY h2w) := cls_congr _ hvec
    _ = cls (lamCode (a + b) + lamSum (a * b)) hXY + cls ((2 : ℤ) • w) h2w := (cls_add hXY h2w).symm
    _ = lamCodeCls (C.add_mem ha hb) + lamVec (a * b) := by
        rw [cls_two_smul hw h2w, add_zero, lamCodeCls, lamVec, cls_add]

/-! ### From `CFSG/Monster/SpinLattice/Cocode.lean` -/
private theorem add_self' (x : L2) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem lamCocode_Acocode (a b : C) :
    lamCocode (Acocode a b) = lamVec ((a : Fin 24 → ZMod 2) * b) := rfl

theorem lamX_add (a b : C) :
    lamX (a + b) = lamX a + lamX b + lamVec ((a : Fin 24 → ZMod 2) * b) := by
  have h := lamCodeCls_add a.2 b.2
  rw [lamX, lamX, lamX, h, add_assoc, add_self', add_zero]

/-- **Additivity of `lamT`** (the source's `lamT_add`): `lamT (a + b) = lamT a + lamT b`. -/
theorem lamT_add (a b : C) : lamT (a + b) = lamT a + lamT b := by
  rw [lamT, lamT, lamT, thetaD_add, map_add, map_add, lamCocode_Acocode, lamX_add]
  have h := add_self' (lamVec ((a : Fin 24 → ZMod 2) * b))
  calc lamX a + lamX b + lamVec (↑a * ↑b) +
        (lamCocode (thetaD a) + lamCocode (thetaD b) + lamVec (↑a * ↑b)) =
      lamX a + lamCocode (thetaD a) + (lamX b + lamCocode (thetaD b)) +
        (lamVec (↑a * ↑b) + lamVec (↑a * ↑b)) := by abel
    _ = _ := by rw [h, add_zero]

theorem qL_lamCocode (δ : Cocode) : qL (lamCocode δ) = 0 := by
  induction δ using Submodule.Quotient.induction_on with | H x => exact qL_lamVec x

theorem bL_lamCocode_lamCocode (δ ε : Cocode) :
    QuadraticMap.polarBilin qL (lamCocode δ) (lamCocode ε) = 0 := by
  induction δ using Submodule.Quotient.induction_on with | H x => ?_
  induction ε using Submodule.Quotient.induction_on with | H y => exact bL_lamVec_lamVec x y

theorem bL_lamX_lamCocode (a : C) (δ : Cocode) :
    QuadraticMap.polarBilin qL (lamX a) (lamCocode δ) = pair a δ := by
  induction δ using Submodule.Quotient.induction_on with | H x =>
    exact bL_lamCodeCls_lamVec a.2 x

theorem qL_lamX (a : C) : qL (lamX a) = P a := qL_lamCodeCls a.2

theorem bL_lamX_lamX (a b : C) : QuadraticMap.polarBilin qL (lamX a) (lamX b) = K a b :=
  bL_lamCodeCls_lamCodeCls a.2 b.2

private theorem polarBilin_symm' (x y : L2) :
    QuadraticMap.polarBilin qL x y = QuadraticMap.polarBilin qL y x := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

private theorem qL_add (x y : L2) : qL (x + y) = qL x + qL y + QuadraticMap.polarBilin qL x y := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  ring

theorem qL_lamT (a : C) : qL (lamT a) = 0 := by
  rw [lamT, qL_add, qL_lamX, qL_lamCocode, bL_lamX_lamCocode, pair_self_thetaD, add_zero]
  generalize P (a : Fin 24 → ZMod 2) = x
  revert x
  decide

theorem bL_lamT_lamT (a b : C) : QuadraticMap.polarBilin qL (lamT a) (lamT b) = 0 := by
  rw [lamT, lamT, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
    bL_lamX_lamX, bL_lamX_lamCocode, polarBilin_symm' (lamCocode _) (lamX b),
    bL_lamX_lamCocode, bL_lamCocode_lamCocode, pair_thetaD, pair_thetaD, add_zero]
  have h := θ_add_θ_swap a b
  rw [← h]
  generalize θ a b = x
  generalize θ b a = y
  revert x y
  decide

theorem bL_lamT_lamCocode (a : C) (δ : Cocode) :
    QuadraticMap.polarBilin qL (lamT a) (lamCocode δ) = pair a δ := by
  rw [lamT, map_add, LinearMap.add_apply, bL_lamX_lamCocode, bL_lamCocode_lamCocode, add_zero]

noncomputable def lamTHom : C →+ L2 where
  toFun := lamT
  map_zero' := by
    have h := lamT_add 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  map_add' := lamT_add

/-- **The bundled coordinate map** (the source's `phi0`, verbatim):
`C × Cocode →ₗ[ZMod 2] Λ/2Λ`, `(a, δ) ↦ lamT a + lamCocode δ`. -/
noncomputable def phi0Lin : C × Cocode →ₗ[ZMod 2] L2 :=
  (AddMonoidHom.toZModLinearMap 2 lamTHom).coprod lamCocode

/-- The bundled map has the values of the ported function `phi0` (by definition). -/
theorem phi0Lin_apply (p : C × Cocode) : phi0Lin p = phi0 p := rfl

/-- **`phi0` is additive.** -/
theorem phi0_add (p q : C × Cocode) : phi0 (p + q) = phi0 p + phi0 q := by
  rw [← phi0Lin_apply, ← phi0Lin_apply, ← phi0Lin_apply, map_add]

theorem qL_phi0 (a : C) (δ : Cocode) : qL (phi0 (a, δ)) = pair a δ := by
  rw [phi0_apply, qL_add, qL_lamT, qL_lamCocode, bL_lamT_lamCocode, zero_add, zero_add]

theorem bL_phi0 (a b : C) (δ ε : Cocode) :
    QuadraticMap.polarBilin qL (phi0 (a, δ)) (phi0 (b, ε)) = pair a ε + pair b δ := by
  rw [phi0_apply, phi0_apply, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
    bL_lamT_lamT, bL_lamT_lamCocode, polarBilin_symm' (lamCocode δ) (lamT b),
    bL_lamT_lamCocode, bL_lamCocode_lamCocode, zero_add, add_zero, add_comm]

theorem phi0Lin_injective : Function.Injective phi0Lin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, δ⟩ h
  rw [phi0Lin_apply] at h
  have h1 : ∀ ε : Cocode, pair a ε = 0 := by
    intro ε
    have := bL_phi0 a 0 δ ε
    rw [h, map_zero, LinearMap.zero_apply, pair_zero_left, add_zero] at this
    exact this.symm
  have h2 : ∀ u : C, pair u δ = 0 := by
    intro u
    have := bL_phi0 a u δ 0
    rw [h, map_zero, LinearMap.zero_apply, pair_zero_right, zero_add] at this
    exact this.symm
  rw [eq_zero_of_forall_pair_left h1, eq_zero_of_forall_pair h2]
  rfl

/-- **`phi0` is injective.** -/
theorem phi0_injective : Function.Injective phi0 := phi0Lin_injective

/-- A `ℤ`-basis of the code lattice with 24 elements: `Submodule.basisOfPid` gives some basis, and
its size is pinned to 24 by the independent vectors `8eᵢ ∈ Λ`. -/
theorem nonempty_basis_codeLatticeSubgroup :
    Nonempty (Module.Basis (Fin 24) ℤ (codeLatticeSubgroup (C := C) allOnes_mem_C)) := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin 24))
    (codeLatticeSubgroup (C := C) allOnes_mem_C).toIntSubmodule
  have hn : n = 24 := by
    have h1 : finrank ℤ (codeLatticeSubgroup (C := C) allOnes_mem_C).toIntSubmodule = n := by
      rw [finrank_eq_card_basis b, Fintype.card_fin]
    have hle := Submodule.finrank_le (codeLatticeSubgroup (C := C) allOnes_mem_C).toIntSubmodule
    rw [finrank_fin_fun] at hle
    haveI : Module.Finite ℤ (codeLatticeSubgroup (C := C) allOnes_mem_C).toIntSubmodule :=
      Module.Finite.of_basis b
    let v : Fin 24 → (codeLatticeSubgroup (C := C) allOnes_mem_C).toIntSubmodule :=
      fun i => ⟨(8 : ℤ) • (Pi.single i 1 : Fin 24 → ℤ), smul_eight_mem_codeLattice _⟩
    have hv : LinearIndependent ℤ v := by
      apply LinearIndependent.of_comp (Submodule.subtype _)
      rw [linearIndependent_iff']
      intro s g hg i hi
      have h := congrFun hg i
      simp only [Function.comp_apply, Submodule.subtype_apply, v, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj])
        (fun h' => absurd hi h')] at h
      simpa using h
    have hge := hv.fintype_card_le_finrank
    rw [Fintype.card_fin] at hge
    omega
  subst hn
  exact ⟨b⟩

/-- `Λ/2Λ` has dimension `24` over `ZMod 2`. -/
theorem finrank_L2 : finrank (ZMod 2) L2 = 24 := by
  obtain ⟨b⟩ := nonempty_basis_codeLatticeSubgroup
  rw [finrank_eq_card_basis (ModN.basis (n := 2) b), Fintype.card_fin]

theorem phi0Lin_bijective : Function.Bijective phi0Lin := by
  obtain ⟨b⟩ := nonempty_basis_codeLatticeSubgroup
  haveI : Module.Finite (ZMod 2) L2 := Module.Finite.of_basis (ModN.basis (n := 2) b)
  refine ⟨phi0Lin_injective, ?_⟩
  have hdim : finrank (ZMod 2) (C × Cocode) = finrank (ZMod 2) L2 := by
    rw [finrank_prod, finrank_cocode, finrank_L2, finrank_C]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 phi0Lin_injective

/-- **`phi0` is bijective.** -/
theorem phi0_bijective : Function.Bijective phi0 := phi0Lin_bijective

/-- **The coordinate isomorphism** `C × Cocode ≃ₗ[ZMod 2] Λ/2Λ` (the source's `phi0Equiv`). -/
noncomputable def phi0Equiv : (C × Cocode) ≃ₗ[ZMod 2] L2 :=
  LinearEquiv.ofBijective phi0Lin phi0Lin_bijective

theorem phi0Equiv_apply (p : C × Cocode) : phi0Equiv p = phi0 p := rfl

end VOA.Moonshine.MonsterGriess.SpinLattice

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
  VOA.Moonshine.MonsterGriess.SpinLattice

/-! ### From `CFSG/Monster/Griess/Short.lean` -/
theorem qL_classOf_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : qL (classOf u) = 0 := by
  have hL := hu.1
  have h4 : ∑ i, u i * u i = 32 := by
    have h := hu.2
    unfold codeForm at h
    have h' : ((∑ i, u i * u i : ℤ) : ℚ) = 32 := by push_cast; linarith
    exact_mod_cast h'
  have hcl : classOf u = cls u hL := by
    rw [classOf, dif_pos hL]
    rfl
  rw [hcl, qL_cls]
  have : hInt u u = 4 := by
    unfold hInt
    rw [h4]
    rfl
  rw [this]
  rfl

/-- **Short coordinates are isotropic**: `pair a δ = 0` whenever `phi0 (a, δ)` is the class of a
minimal vector. -/
theorem pair_eq_zero_of_isShortCoord {p : C × Cocode} (h : IsShortCoord p) : pair p.1 p.2 = 0 := by
  obtain ⟨u, hu, hcl⟩ := h
  rw [← qL_phi0, ← hcl, qL_classOf_minVecs hu]

end VOA.Moonshine.MonsterGriess
