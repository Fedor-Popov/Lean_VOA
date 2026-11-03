/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSGaloisSigned
import VOA.Huang.NSGaloisAut
import VOA.Huang.ZhuRepGalois

/-!
# `NSGaloisTwistAll` from the Galois twist core (DLN Lemma 4.2 for `Z(A)`)

`nsGaloisTwistAll_of_core : NSGaloisTwistCore → ZhuRep.NSGaloisTwistAll`.

The signed half (Coste–Gannon) is proved in `NSGaloisSigned` (`galois_signed`), the automorphism
of `ℂ` in `NSGaloisAut` (`exists_ringEquiv_pow`).  What remains is `NSGaloisTwistCore`:

`σ²(θ_i) · θ_{π 0} = θ_{π i}` for every `σ ∈ Aut ℂ`, where `π` is the Galois permutation of the
fusion characters (`σ ∘ χ_k = χ_{π k}`).

This is DLN 2015 Lemma 4.2 (Galois symmetry of the `T`-matrix of a Drinfeld centre, proved in
their §5 with generalized Frobenius–Schur indicators) applied to `Z(A) ≅ A ⊠ A^rev`, whose
simples are `(i, j)` with `T = θ_i/θ_j` and Galois permutation `(π i, π j)` (DLN p. 23), at
`j = 0`.  It is TRUE (literature) and independent of any normalization of `ρ` and of the
congruence property (which, by DLN (4.9)–(4.11), only serves to normalize `β = 1`).

`dln_inputs_of_core : NSProjectiveCongruenceAll → MatrixDLNLifting → NSGaloisTwistCore →
DLNCongruenceInput ∧ GaloisSymmetryNontrivialInput`.
-/

noncomputable section
set_option linter.unusedSectionVars false

namespace VOA.Huang.NSGalois

open CategoryTheory MonoidalCategory Limits BraidedCategory Matrix
open VOA.Huang.NgSchauenburg VOA.Huang.NSFinish VOA.Huang.DLNBridge VOA.Huang.DLN
  VOA.Huang.ZhuRep

universe u v w

attribute [-instance] hasRightDualUnit hasRightDualLeftDual

/-- **DLN Lemma 4.2 for the Drinfeld centre of a modular category, in `A`-terms**: for every
automorphism `σ` of `ℂ` and the Galois permutation `π` of the fusion characters,
`σ²(θ_i) · θ_{π(0)} = θ_{π(i)}`.  VOA-free and normalization-free; TRUE (DLN 2015, Lemma 4.2,
§5, applied to `Z(A)`; see the module docstring). -/
def NSGaloisTwistCore : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F) (σ : ℂ ≃+* ℂ) (π : F.Label → F.Label),
    (∀ k i, σ (fusionChar F k i) = fusionChar F (π k) i) →
    ∀ i, σ (σ (M.twistScalar i)) * M.twistScalar (π F.unitLabel) = M.twistScalar (π i)

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A representation with diagonal `ρ(T)` has diagonal `ρ(T^k)`. -/
theorem rho_T_zpow_diag (ρ : SL2Z →* Matrix ι ι ℂ) (t : ι → ℂ) (ht : ∀ i, t i ≠ 0)
    (hρ : ρ ModularGroup.T = Matrix.diagonal t) (k : ℤ) :
    ρ (ModularGroup.T ^ k) = Matrix.diagonal (fun i => t i ^ k) := by
  have hinv : ρ ModularGroup.T * ρ ModularGroup.T⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [_root_.zpow_add_one, map_mul, ih, hρ, Matrix.diagonal_mul_diagonal]
    congr 1
  | pred k ih =>
    have h1 : ρ (ModularGroup.T ^ (-(k : ℤ) - 1)) =
        ρ (ModularGroup.T ^ (-(k : ℤ))) * ρ ModularGroup.T⁻¹ := by
      rw [← map_mul, ← _root_.zpow_neg_one, ← _root_.zpow_add]; ring_nf
    have h2 : Matrix.diagonal (fun i => t i ^ (-(k : ℤ) - 1)) =
        Matrix.diagonal (fun i => t i ^ (-(k : ℤ))) * ρ ModularGroup.T⁻¹ := by
      calc Matrix.diagonal (fun i => t i ^ (-(k : ℤ) - 1)) =
            Matrix.diagonal (fun i => t i ^ (-(k : ℤ) - 1)) *
              (ρ ModularGroup.T * ρ ModularGroup.T⁻¹) := by rw [hinv, Matrix.mul_one]
        _ = Matrix.diagonal (fun i => t i ^ (-(k : ℤ))) * ρ ModularGroup.T⁻¹ := by
          rw [← Matrix.mul_assoc, hρ, Matrix.diagonal_mul_diagonal]
          congr 2; funext i
          rw [← zpow_add_one₀ (ht i)]; ring_nf
    rw [h1, ih, h2]

end Algebra

section Assembly

variable {C : Type w} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- The normalization `(a² D²)² = 1` forced by `ρ(S)⁴ = 1`. -/
theorem norm_of_rho (F : SphericalFusion C) (M : Modular F)
    (ρ : SL2Z →* Matrix F.Label F.Label ℂ) (a : ℂ)
    (hS : ρ ModularGroup.S = a • categoricalS F) :
    (a ^ 2 * F.globalDimension) ^ 2 = 1 := by
  have h4 : ρ ModularGroup.S ^ 4 = 1 := by
    rw [← map_pow, show ModularGroup.S ^ 4 = 1 by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, VerlindeEigen.modularS_mul_S]
      simp, map_one]
  have hC2 : chargeConjugation F * chargeConjugation F = 1 := by
    ext i j
    simp only [Matrix.mul_apply, chargeConjugation, Matrix.one_apply, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single (F.dualLabel i)]
    · simp only [if_true]
      by_cases h : i = j
      · subst h; simp [F.dualLabel_involutive i]
      · rw [if_neg (fun h' => h (by rw [h', F.dualLabel_involutive])), if_neg h]
    · intro k _ hk; rw [if_neg hk]; split_ifs <;> rfl
    · simp
  have hsq := categoricalS_sq F M
  rw [hS] at h4
  have : (a • categoricalS F) ^ 4 = ((a ^ 2 * F.globalDimension) ^ 2) • (1 : Matrix _ _ ℂ) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, smul_mul_smul_comm, hsq, smul_smul,
      smul_mul_smul_comm, hC2]
    congr 1; ring
  rw [this] at h4
  have hne : Nonempty F.Label := ⟨F.unitLabel⟩
  have := congrFun (congrFun h4 F.unitLabel) F.unitLabel
  simpa using this

open Classical in
/-- **`NSGaloisTwistAll` for one modular category, from the twist core.** -/
theorem galoisTwist_of_core (F : SphericalFusion C) (M : Modular F)
    (hcore : ∀ (σ : ℂ ≃+* ℂ) (π : F.Label → F.Label),
      (∀ k i, σ (fusionChar F k i) = fusionChar F (π k) i) →
      ∀ i, σ (σ (M.twistScalar i)) * M.twistScalar (π F.unitLabel) = M.twistScalar (π i))
    (ρ : SL2Z →* Matrix F.Label F.Label ℂ) (a b : ℂˣ)
    (hS : ∀ i j, ρ ModularGroup.S i j = (a : ℂ) * categoricalS F i j)
    (hT : ∀ i, ρ ModularGroup.T i i = (b : ℂ) * M.twistScalar i)
    (hT' : ∀ i j, i ≠ j → ρ ModularGroup.T i j = 0)
    (N : ℕ) (hN : 0 < N) (hTN : ρ ModularGroup.T ^ N = 1) (x y : ℤ)
    (hxy : x * y ≡ 1 [ZMOD N]) :
    ∃ (σ : ℂ ≃+* ℂ) (G : Matrix F.Label F.Label ℂ), IsSignedPermutation G ∧
      mapσ σ (ρ ModularGroup.S) = G * ρ ModularGroup.S ∧
      mapσ σ (ρ ModularGroup.S) * G = ρ ModularGroup.S ∧
      mapσ σ (ρ ModularGroup.T) = ρ (ModularGroup.T ^ x) ∧
      ∃ β : ℂ, G * ρ ModularGroup.T = β • (ρ (ModularGroup.T ^ (x * x)) * G) := by
  -- `x` is coprime to `N`
  have hx : x.gcd N = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]
    obtain ⟨k, hk⟩ := (Int.ModEq.dvd hxy.symm)
    exact ⟨y, -k, by linear_combination hk⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_pow N hN x hx
  -- the shapes of `ρ(S)` and `ρ(T)`
  have hSm : ρ ModularGroup.S = (a : ℂ) • categoricalS F := by
    ext i j; rw [hS, Matrix.smul_apply, smul_eq_mul]
  set t : F.Label → ℂ := fun i => (b : ℂ) * M.twistScalar i with htdef
  have hTm : ρ ModularGroup.T = Matrix.diagonal t := by
    ext i j
    by_cases h : i = j
    · subst h; rw [hT, Matrix.diagonal_apply_eq]
    · rw [hT' i j h, Matrix.diagonal_apply_ne _ h]
  have htN : ∀ i, t i ^ N = 1 := by
    intro i
    have := congrFun (congrFun hTN i) i
    rw [hTm, Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
    exact this
  have ht0 : ∀ i, t i ≠ 0 := fun i h => by
    have := htN i; rw [h, zero_pow hN.ne'] at this; exact zero_ne_one this
  have hb : (b : ℂ) = t F.unitLabel := by
    simp only [htdef, M.toRibbon.twistScalar_unitLabel, mul_one]
  have hbN : (b : ℂ) ^ N = 1 := by rw [hb]; exact htN _
  have hθN : ∀ i, M.twistScalar i ^ N = 1 := by
    intro i
    have h := htN i
    simp only [htdef, mul_pow, hbN, one_mul] at h
    exact h
  have hσθ : ∀ i, σ (M.twistScalar i) = M.twistScalar i ^ x := fun i => hσ _ (hθN i)
  have hσt : ∀ i, σ (t i) = t i ^ x := fun i => hσ _ (htN i)
  -- normalization and the signed half
  have hnorm := norm_of_rho F M ρ (a : ℂ) hSm
  obtain ⟨hG, h1, h2⟩ := galois_signed F M σ (a : ℂ) hnorm
  refine ⟨σ, galoisSigned F M σ (a : ℂ), hG, by rw [hSm]; exact h1, by rw [hSm]; exact h2, ?_, ?_⟩
  · rw [rho_T_zpow_diag ρ t ht0 hTm, hTm]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.coe_toRingHom]
    by_cases h : i = j
    · subst h; rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hσt]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]
  · set π := galoisPerm F M σ
    have hcore' := hcore σ π (galoisPerm_spec F M σ)
    refine ⟨M.twistScalar (π F.unitLabel) * (b : ℂ) ^ (1 - x * x), ?_⟩
    rw [rho_T_zpow_diag ρ t ht0 hTm, hTm]
    ext i k
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul,
      galoisSigned]
    by_cases h : π i = k
    · subst h
      rw [if_pos rfl]
      have hb0 : (b : ℂ) ≠ 0 := b.ne_zero
      have e1 : t (π i) = (b : ℂ) * (σ (σ (M.twistScalar i)) * M.twistScalar (π F.unitLabel)) := by
        rw [hcore' i]
      rw [e1, hσθ, map_zpow₀, hσθ, ← _root_.zpow_mul]
      simp only [htdef, mul_zpow]
      rw [show (b : ℂ) ^ (1 - x * x) = (b : ℂ) * ((b : ℂ) ^ (x * x))⁻¹ by
        rw [zpow_sub₀ hb0, zpow_one, div_eq_mul_inv]]
      field_simp
    · rw [if_neg h]; ring

/-- **`NSGaloisTwistAll` from `NSGaloisTwistCore`.** -/
theorem nsGaloisTwistAll_of_core (h : NSGaloisTwistCore.{v, w}) :
    NSGaloisTwistAll.{v, w} := by
  intro C _ _ _ _ _ _ _ _ _ _ F M ρ a b hS hT hT' N hN hTN x y hxy
  exact galoisTwist_of_core F M (h C F M) ρ a b hS hT hT' N hN hTN x y hxy

end Assembly

/-- **Both classification inputs from three VOA-free contracts**: Ng–Schauenburg 6.8,
DLN 2.3 and the Galois twist core (DLN Lemma 4.2 for `Z(A)`). -/
theorem dln_inputs_of_core (hNS : NSProjectiveCongruenceAll.{0, 0})
    (hlift : MatrixDLNLifting) (hG : NSGaloisTwistCore.{0, 0}) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_categorical hNS hlift (nsGaloisTwistAll_of_core hG)

end VOA.Huang.NSGalois
