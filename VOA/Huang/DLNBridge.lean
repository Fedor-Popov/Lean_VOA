/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSFinishLevel
import VOA.Huang.DLNAlgWord
import VOA.Huang.HuangModularityZhu

/-!
# The Dong–Lin–Ng bridge: from congruence of Zhu's representation to the classification inputs

For a nice VOA `V` with modular data `D`, the library already constructs (`exists_zhuData`, using
the theorem `VOA.pbw`) Zhu's genuine representation `ρ = D'.rep : SL(2, ℤ) →* Matrix D.ι D.ι ℂ`
with `ZhuModularityAnalytic D'`.  This file proves:

* `characterCovariance_of_zhu` — the characters `D.ch` transform under `ρ` (no independence
  of characters is used);
* `zhu_T_pow_eq_one_of_level` — `ρ(T)^N = 1` for every level `N` of `D`;
* `dlnCongruenceInput_of_zhuCongruence` — **`DLNCongruenceInput` follows from congruence of `ρ`
  at *some* positive level**: the exact level is supplied by the proved Wohlfahrt/DLN Lemma A.1
  (`NSFinish.kernel_gamma_orderOf`);
* `zhuCongruence_of_projective` — that congruence follows from *projective* congruence plus the
  group-theoretic DLN lifting theorem (DLN Theorem 2.3, named `MatrixDLNLifting`);
* `galoisSymmetryNontrivialInput_of_word` — `GaloisSymmetryNontrivialInput` follows from the
  congruence property and the DLN Galois-word theorem (DLN Theorem II(iv), named
  `ZhuGaloisWordInput`): for `a b ≡ 1` the matrix `ρ(T^a S T^b S T^a S⁻¹)` is a signed
  permutation matrix.

The three residual Props are TRUE published theorems (Dong–Lin–Ng, *Congruence property in
conformal field theory*, ANT 9 (2015); arXiv:1201.6644v7 — Theorem 2.3, Theorem 3.10 with
Ng–Schauenburg CMP 300 (2010) Thm 6.8, and Theorem II(iv)); their exact content is recorded on
each definition.  `Nice V` contains `V ≅ V'` (`StronglyFinite.selfDual`), the self-duality DLN
assume.
-/

noncomputable section

namespace VOA.Huang.DLNBridge

open VOA VOA.Classification.COne VOA.Huang.DLN VOA.Huang.DLNAlg VOA.Huang.SPinning
  VOA.Huang.CongruenceGaloisSplit VOA.Huang.HuangModularity CongruenceSubgroup

universe u

/-! ## Group-theoretic contracts on matrix representations -/

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Γ(N)` acts by scalars: the projective representation has `Γ(N)` in its kernel. -/
def MatrixProjectiveCongruence (ρ : SL2Z →* Matrix ι ι ℂ) (N : ℕ) : Prop :=
  ∀ γ ∈ Gamma N, ∃ c : ℂ, ρ γ = c • (1 : Matrix ι ι ℂ)

/-- **DLN Theorem 2.3 (matrix form).** If the projectivization of a linear representation `ρ`
of `SL(2, ℤ)` has `Γ(N)` in its kernel, then `Γ(12 N) ≤ ker ρ`.

Source: Dong–Lin–Ng, arXiv:1201.6644v7, Theorem 2.3 ("the kernel of any lifting of `ρ̄` is a
congruence subgroup of level `m` where `n ∣ m ∣ 12 n`", `n` the level of `ker ρ̄`, here `n ∣ N`),
whose proof uses Beyl's computation of the Schur multiplier of `SL₂(ℤ/m)` (DLN Theorem 2.1) and
`Γ(12) ≤ SL₂(ℤ)'`.  Unproved here. -/
def MatrixDLNLifting : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : SL2Z →* Matrix κ κ ℂ) (N : ℕ), 0 < N →
    MatrixProjectiveCongruence ρ N → KernelContainsGamma ρ (12 * N)

/-- **Congruence at some level gives congruence at the exact order** (DLN Lemma A.1, proved
in `NSFinishLevel`). -/
theorem congruenceAtOrder_of_kernel (ρ : SL2Z →* Matrix ι ι ℂ) {L : ℕ} (hL : 0 < L)
    (h : KernelContainsGamma ρ L) : CongruenceAtOrder ρ :=
  NSFinish.kernel_gamma_orderOf ρ hL h

/-- Projective congruence and the lifting contract give `CongruenceAtOrder`. -/
theorem congruenceAtOrder_of_projective (hlift : MatrixDLNLifting) {κ : Type} [Fintype κ]
    [DecidableEq κ] (ρ : SL2Z →* Matrix κ κ ℂ) {N : ℕ} (hN : 0 < N)
    (hp : MatrixProjectiveCongruence ρ N) : CongruenceAtOrder ρ :=
  congruenceAtOrder_of_kernel ρ (Nat.mul_pos (by norm_num) hN) (hlift κ ρ N hN hp)

end Matrix

/-! ## Zhu's representation on the labels of `D` -/

section Zhu

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-- `D'` is Zhu's modular datum on the labels of `D` (the output of `exists_zhuData`). -/
def IsZhuDatum (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
    (D' : VOA.ModularData V D.ι) : Prop :=
  D'.Mfam = famOf D hD ∧ D'.h = hOf D ∧ ZhuModularityAnalytic D'

theorem mobius_eq_smul' (γ : SL2Z) (τ : UpperHalfPlane) :
    mobius γ τ = ((γ • τ : UpperHalfPlane) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, mobius]
  simp

/-- **Character covariance of Zhu's representation.** -/
theorem characterCovariance_of_zhu (hV : Nice V) (D : VOA.Classification.COne.ModularData V)
    (hD : D.IsModularData) (D' : VOA.ModularData V D.ι) (hZD : IsZhuDatum D hD D') :
    CharacterCovariance D D'.rep := by
  obtain ⟨hM, hh, hZ⟩ := hZD
  have hch : ∀ b (σ : ℂ) (hσ : 0 < σ.im), D.ch b σ = D.trace b V.vacuum ⟨σ, hσ⟩ := by
    intro b σ hσ
    refine (hD.char b σ hσ).unique ?_
    exact VOA.Huang.ZhuModData.hasSum_character (D.module b) (hasConformalWeight_famOf D hD b)
      hV.1.c2Cofinite ⟨σ, hσ⟩
  have htr : ∀ b v τ, traceFun D'.Mfam D'.h b v τ = D.trace b v τ := by
    intro b v τ
    rw [hM, hh]
    rfl
  intro γ a τ hτ
  have hlaw := hZ γ 0 V.vacuum (vacuum_mem_sqWeightSpace_zero V) a ⟨τ, hτ⟩
  rw [pow_zero, one_mul, htr] at hlaw
  have hme : mobius γ τ = ((γ • (⟨τ, hτ⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) :=
    mobius_eq_smul' γ ⟨τ, hτ⟩
  have hτ' : 0 < (mobius γ τ).im := by
    rw [hme]
    exact (γ • (⟨τ, hτ⟩ : UpperHalfPlane)).im_pos
  have hsm : (γ • (⟨τ, hτ⟩ : UpperHalfPlane)) = ⟨mobius γ τ, hτ'⟩ := by
    ext
    exact hme.symm
  rw [hch a _ hτ', ← hsm, hlaw]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [htr, hch b τ hτ]

/-- `ρ(T)` is the diagonal matrix of `e^{2πi(h_a - c/24)}`; hence `ρ(T)^N = 1` at every level. -/
theorem zhu_T_pow_eq_one_of_level (D : VOA.Classification.COne.ModularData V)
    (hD : D.IsModularData) (D' : VOA.ModularData V D.ι) (hZD : IsZhuDatum D hD D') {N : ℕ}
    (hN : D.IsLevel N) : D'.rep ModularGroup.T ^ N = 1 := by
  obtain ⟨-, hh, -⟩ := hZD
  rw [D'.rep_T, hh]
  ext a b
  have hdiag : ∀ k : ℕ, (Matrix.of (modularRepT V (hOf D)) ^ k) a b =
      if a = b then modularTEntry V (hOf D a) ^ k else 0 := by
    intro k
    induction k generalizing b with
    | zero => simp [Matrix.one_apply]
    | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      rw [Finset.sum_eq_single b]
      · rw [ih b]
        simp only [Matrix.of_apply, modularRepT]
        split_ifs with hab
        · subst hab; ring
        · simp
      · intro c _ hcb
        simp [Matrix.of_apply, modularRepT, hcb]
      · simp
  rw [hdiag N, Matrix.one_apply]
  split_ifs with hab
  · obtain ⟨k, hk⟩ := hN.2 a
    rw [modularTEntry, ← Complex.exp_nat_mul]
    have : (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (hOf D a - V.centralCharge / 24)) =
        (k : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hOf]
      linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hk
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I k
  · rfl

/-! ## The residual contracts -/

/-- **Congruence of Zhu's representation at some level** (DLN 2015, Theorem I with Theorem 3.10:
`ker ρ_V` is a congruence subgroup).  The finest VOA-side residual. -/
def ZhuCongruenceInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
      (D' : VOA.ModularData V D.ι), IsZhuDatum D hD D' →
      ∃ L : ℕ, 0 < L ∧ KernelContainsGamma D'.rep L

/-- **Projective congruence of Zhu's representation** (Ng–Schauenburg CMP 300 (2010),
Theorem 6.8, applied to `Rep V` through DLN Theorem 3.10: `ρ_V` is a modular representation of
the modular tensor category of `V`).  `NgSchauenburg.ProjectiveCongruenceTheorem` is the abstract
categorical half; `DLNBridgeCategorical` reduces this Prop to it. -/
def ZhuProjectiveCongruenceInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
      (D' : VOA.ModularData V D.ι), IsZhuDatum D hD D' →
      ∃ N : ℕ, 0 < N ∧ MatrixProjectiveCongruence D'.rep N

/-- A matrix is a signed permutation matrix. -/
def IsSignedPermutation {κ : Type*} [DecidableEq κ] (G : Matrix κ κ ℂ) : Prop :=
  ∃ (π : κ ≃ κ) (ε : κ → ℂ), (∀ a, ε a = 1 ∨ ε a = -1) ∧
    ∀ a b, G a b = if π a = b then ε a else 0

/-- **The DLN Galois word** (DLN 2015, Theorem II(iii)–(iv)): for `a` invertible modulo the level
with inverse `b`, `G_{σ_a} = ρ(t^a s t^b s t^a s⁻¹)` is a signed permutation matrix.  Stated at
every level `N` of `D`; since `ord ρ(T) ∣ N`, `a b ≡ 1 (mod N)` implies the DLN hypothesis. -/
def ZhuGaloisWordInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱), Nice V →
    ∀ (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
      (D' : VOA.ModularData V D.ι), IsZhuDatum D hD D' →
      ∀ N : ℕ, D.IsLevel N → ∀ a b : ℤ, a * b ≡ 1 [ZMOD N] →
        IsSignedPermutation (D'.rep (diagonalWord a b))

/-! ## The assemblies -/

/-- Congruence of Zhu's representation at every level of `D`. -/
theorem kernel_at_level (hC : ZhuCongruenceInput.{u}) (hV : Nice V)
    (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData)
    (D' : VOA.ModularData V D.ι) (hZD : IsZhuDatum D hD D') {N : ℕ} (hN : D.IsLevel N) :
    KernelContainsGamma D'.rep N := by
  obtain ⟨L, hL, hk⟩ := hC _ V hV D hD D' hZD
  exact (congruenceAtOrder_of_kernel D'.rep hL hk).at_level
    (zhu_T_pow_eq_one_of_level D hD D' hZD hN)

/-- **`DLNCongruenceInput` from congruence of Zhu's representation at some level.** -/
theorem dlnCongruenceInput_of_zhuCongruence (hC : ZhuCongruenceInput.{u}) :
    DLNCongruenceInput.{u} := by
  intro 𝒱 _ _ V hV D hD N hN
  obtain ⟨D', hM, hh, hZ⟩ := exists_zhuData hV D hD
  have hZD : IsZhuDatum D hD D' := ⟨hM, hh, hZ⟩
  exact characters_invariant_of_kernel D D'.rep (characterCovariance_of_zhu hV D hD D' hZD) N
    (kernel_at_level hC hV D hD D' hZD hN)

/-- **Congruence from projective congruence and DLN lifting.** -/
theorem zhuCongruence_of_projective (hP : ZhuProjectiveCongruenceInput.{u})
    (hlift : MatrixDLNLifting) : ZhuCongruenceInput.{u} := by
  intro 𝒱 _ _ V hV D hD D' hZD
  obtain ⟨N, hN, hp⟩ := hP 𝒱 V hV D hD D' hZD
  exact ⟨12 * N, Nat.mul_pos (by norm_num) hN, hlift D.ι D'.rep N hN hp⟩

/-- **`GaloisSymmetryNontrivialInput` from congruence and the DLN Galois word.** In fact the
full `D.GaloisSymmetric N` is obtained for every level `N`. -/
theorem galoisSymmetric_of_word (hC : ZhuCongruenceInput.{u}) (hW : ZhuGaloisWordInput.{u})
    {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱} (hV : Nice V)
    (D : VOA.Classification.COne.ModularData V) (hD : D.IsModularData) {N : ℕ}
    (hN : D.IsLevel N) : D.GaloisSymmetric N := by
  intro ℓ ℓ' hℓ γ h00 h11 h01 h10
  obtain ⟨D', hM, hh, hZ⟩ := exists_zhuData hV D hD
  have hZD : IsZhuDatum D hD D' := ⟨hM, hh, hZ⟩
  have hk := kernel_at_level hC hV D hD D' hZD hN
  have hρ : D'.rep γ = D'.rep (diagonalWord ℓ ℓ') :=
    eq_diagonalWord_of_kernel D'.rep hk hℓ (hasDiagonalReduction_of_modEq h00 h11 h01 h10)
  obtain ⟨π, ε, hε, hG⟩ := hW 𝒱 V hV D hD D' hZD N hN ℓ ℓ' hℓ
  refine ⟨π, ε, hε, fun a τ hτ => ?_⟩
  rw [characterCovariance_of_zhu hV D hD D' hZD γ a τ hτ, hρ]
  simp only [hG]
  simp

theorem galoisSymmetryNontrivialInput_of_word (hC : ZhuCongruenceInput.{u})
    (hW : ZhuGaloisWordInput.{u}) : GaloisSymmetryNontrivialInput.{u} := by
  intro 𝒱 _ _ V hV D hD N hN ℓ ℓ' hℓ _ _ γ h00 h11 h01 h10
  exact galoisSymmetric_of_word hC hW hV D hD hN ℓ ℓ' hℓ γ h00 h11 h01 h10

/-- **Both classification inputs from the three DLN/NS contracts.** -/
theorem dln_inputs_of_contracts (hP : ZhuProjectiveCongruenceInput.{u})
    (hlift : MatrixDLNLifting) (hW : ZhuGaloisWordInput.{u}) :
    DLNCongruenceInput.{u} ∧ GaloisSymmetryNontrivialInput.{u} :=
  ⟨dlnCongruenceInput_of_zhuCongruence (zhuCongruence_of_projective hP hlift),
    galoisSymmetryNontrivialInput_of_word (zhuCongruence_of_projective hP hlift) hW⟩

/-- … and the bundled `ICongruenceGalois`. -/
theorem iCongruenceGalois_of_contracts (hP : ZhuProjectiveCongruenceInput.{u})
    (hlift : MatrixDLNLifting) (hW : ZhuGaloisWordInput.{u}) : ICongruenceGalois.{u} :=
  iCongruenceGalois_of_split (dln_inputs_of_contracts hP hlift hW).1
    (dln_inputs_of_contracts hP hlift hW).2

end Zhu

end VOA.Huang.DLNBridge
