/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSGaloisCoreTrace
import VOA.Huang.NSGaloisAssembly
import VOA.Huang.NSSMoveAssembly
import VOA.Huang.NSCongruenceBridge

/-!
# The Galois twist core from the mixed S move (DLN §5)

This file proves DLN 2015 Lemma 4.2 for `Z(A) ≅ A ⊠ A^rev` in `A`-terms,
`σ²(θ_i) · θ_{π 0} = θ_{π i}`. The proof is conditional on the mixed S move at nonzero rows
(`MixedNonzeroSMove`), for a modular category that has a modular lift. The argument follows DLN
§5 (Lemma 5.3 and §5.3), with one simplification: DLN's Dirichlet prime is replaced by the
coprime pair of rows `(a, 1)` and `(a, 1 + a)`.

The steps, with `ν^p_{m,l}` the mixed generalized indicator of `X_{p.1} ⊠ X_{p.2}`:
* `smove_expand`: `ν^q_{m,l} = Σ_p mixedS_{p,q} ν^p_{l,-m}` (the S move with `z = ρ̃(S) e_q`).
* `galois_mixedS`: `σ(mixedS_{p,(k,l)}) = ε_k ε_l mixedS_{p,(π k, π l)}` (Coste–Gannon).
* `galois_row_neg_one`: `σ(ν^p_{m,-1}) = ν^p_{m,-a}`. This is DLN's τ-trick. It uses
  cyclotomicity of the mixed rows, which is itself a consequence of the S move
  (`mixedRowCyclotomic_of_SMove`, `mixedSCyclotomic_of_SMove`).
* `galois_mixed_row` (a scalar form of DLN Lemma 5.3):
  `ε_k ε_l ν^{(πk,πl)}_{a,m} = ν^{(k,l)}_{1,m a}`.
* `galoisTwistCore_of_SMove_lift`: the twist relation.

Headlines:
* `nsGaloisTwistAll_of_SMove : NSMixedNonzeroSMoveAll → NSGaloisTwistAll`;
* `nsGaloisTwistCore_of_SMove_lifts : NSMixedNonzeroSMoveAll → NSModularLiftExistsAll →
  NSGaloisTwistCore`;
* `dln_inputs_of_SMove_lifting : NSMixedSameSignOffDiagonalSMoveAll → MatrixDLNLifting →
  DLNCongruenceInput ∧ GaloisSymmetryNontrivialInput`.
-/

noncomputable section
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace VOA.Huang.NSGaloisCore

open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence VOA.Huang.NSGalois
open scoped MatrixGroups

universe v u

attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- The S move, expanded at a basis vector. -/
theorem smove_expand (F : SphericalFusion C) (M : Modular F) (hS : MixedNonzeroSMove F M)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ))) (hr : IsModularRepresentation F M ρ)
    (c : F.Label) (m l : ℤ) (hm : m ≠ 0) (hl : l ≠ 0) (hcop : IsCoprime m l)
    (q : F.Label × F.Label) :
    generalizedIndicatorAll F (mixedCenter (F.simple q.1) (F.simple q.2)) (F.simple c) m l =
      ∑ p, mixedS F M p q *
        generalizedIndicatorAll F (mixedCenter (F.simple p.1) (F.simple p.2)) (F.simple c)
          l (-m) := by
  have h := hS ρ hr c m l hm hl hcop (mixedRepresentation ρ ModularGroup.S (Pi.single q 1))
  rw [map_inv, le_inv_apply_apply] at h
  simp only [mixedRow, equivariantIndicator_basis] at h
  rw [← h, mixedRepresentation_S F M ρ hr]
  simp only [equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Mixed S as a product of two normalized S entries. -/
theorem mixedS_eq_mul (F : SphericalFusion C) (M : Modular F) (a₀ : ℂ)
    (ha₀ : a₀ ^ 2 * F.globalDimension = 1) (p q : F.Label × F.Label) :
    mixedS F M p q = (a₀ * categoricalS F p.1 q.1) *
      (a₀ * categoricalS F (F.dualLabel p.2) q.2) := by
  have hD := F.globalDimension_ne_zero
  have hinv : F.globalDimension⁻¹ = a₀ ^ 2 := by
    rw [← mul_one (a₀ ^ 2), ← mul_inv_cancel₀ hD, ← mul_assoc, ha₀, one_mul]
  rw [mixedS_apply, hinv]
  ring

/-- **The Galois action on mixed S** (Coste–Gannon on both factors). -/
theorem galois_mixedS (F : SphericalFusion C) (M : Modular F) (σ : ℂ ≃+* ℂ) (a₀ : ℂ)
    (ha₀ : a₀ ^ 2 * F.globalDimension = 1) (p : F.Label × F.Label) (k l : F.Label) :
    σ (mixedS F M p (k, l)) = galoisSign F M σ a₀ k * galoisSign F M σ a₀ l *
      mixedS F M p (galoisPerm F M σ k, galoisPerm F M σ l) := by
  have ha : (a₀ ^ 2 * F.globalDimension) ^ 2 = 1 := by rw [ha₀, one_pow]
  rw [mixedS_eq_mul F M a₀ ha₀, mixedS_eq_mul F M a₀ ha₀, map_mul,
    galois_entry F M σ a₀ ha, galois_entry F M σ a₀ ha]
  ring

/-- The cyclotomic generator `ζ_N`. -/
abbrev zetaN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- **DLN's τ-trick**: `σ(ν^p_{m,-1}) = ν^p_{m,-a}`. -/
theorem galois_row_neg_one (F : SphericalFusion C) (M : Modular F)
    (hcyc : MixedRowCyclotomic F M) (σ : ℂ ≃+* ℂ) (a : ℕ)
    (hσ : ∀ z : ℂ, z ^ M.toRibbon.twistOrder = 1 → σ z = z ^ (a : ℤ))
    (c : F.Label) (p : F.Label × F.Label) (m : ℤ) (hm : m ≠ 0)
    (hgcd : Nat.Coprime a (m.natAbs * M.toRibbon.twistOrder)) :
    σ (generalizedIndicatorAll F (mixedCenter (F.simple p.1) (F.simple p.2)) (F.simple c)
        m (-1)) =
      generalizedIndicatorAll F (mixedCenter (F.simple p.1) (F.simple p.2)) (F.simple c)
        m (-(a : ℤ)) := by
  have hN := M.toRibbon.finite_twist.1
  have hK : 0 < m.natAbs * M.toRibbon.twistOrder :=
    Nat.mul_pos (Int.natAbs_pos.mpr hm) hN
  obtain ⟨τ, hτ⟩ := exists_ringEquiv_pow (m.natAbs * M.toRibbon.twistOrder) hK (a : ℤ)
    (by rw [Int.gcd_natCast_natCast]; exact hgcd)
  have hζ := Complex.isPrimitiveRoot_exp M.toRibbon.twistOrder hN.ne'
  have hζK : zetaN M.toRibbon.twistOrder ^ (m.natAbs * M.toRibbon.twistOrder) = 1 := by
    rw [mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hστ : σ (zetaN M.toRibbon.twistOrder) = τ (zetaN M.toRibbon.twistOrder) := by
    rw [hσ _ hζ.pow_eq_one, hτ _ hζK]
  have hmem := hcyc c p.1 p.2 m hm
  rw [ringEquiv_eq_of_mem_adjoin σ τ hστ hmem,
    mixed_indicatorAll_galois F M p.1 p.2 (F.simple c) m hm τ (a : ℤ) hτ (-1), neg_one_mul]

/-- The Galois action on the first row `(1, m)`. -/
theorem galois_row_one (F : SphericalFusion C) (M : Modular F) (σ : ℂ ≃+* ℂ) (a : ℕ)
    (hσ : ∀ z : ℂ, z ^ M.toRibbon.twistOrder = 1 → σ z = z ^ (a : ℤ))
    (c : F.Label) (q : F.Label × F.Label) (m : ℤ) :
    σ (generalizedIndicatorAll F (mixedCenter (F.simple q.1) (F.simple q.2)) (F.simple c) 1 m) =
      generalizedIndicatorAll F (mixedCenter (F.simple q.1) (F.simple q.2)) (F.simple c) 1
        (m * a) :=
  mixed_indicatorAll_galois F M q.1 q.2 (F.simple c) 1 one_ne_zero σ (a : ℤ)
    (by simpa using hσ) m

open Classical in
/-- **A scalar form of DLN Lemma 5.3 for `Z(A)`**:
`ε_k ε_l ν^{(πk,πl)}_{a,m} = ν^{(k,l)}_{1,m a}`. -/
theorem galois_mixed_row (F : SphericalFusion C) (M : Modular F) (hS : MixedNonzeroSMove F M)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ))) (hr : IsModularRepresentation F M ρ)
    (hcyc : MixedRowCyclotomic F M) (σ : ℂ ≃+* ℂ) (a : ℕ) (ha : 0 < a)
    (hσ : ∀ z : ℂ, z ^ M.toRibbon.twistOrder = 1 → σ z = z ^ (a : ℤ))
    (a₀ : ℂ) (ha₀ : a₀ ^ 2 * F.globalDimension = 1)
    (c k l : F.Label) (m : ℤ) (hm : m ≠ 0) (hcop : IsCoprime (a : ℤ) m)
    (hgcd : Nat.Coprime a (m.natAbs * M.toRibbon.twistOrder)) :
    galoisSign F M σ a₀ k * galoisSign F M σ a₀ l *
        generalizedIndicatorAll F (mixedCenter (F.simple (galoisPerm F M σ k))
          (F.simple (galoisPerm F M σ l))) (F.simple c) a m =
      generalizedIndicatorAll F (mixedCenter (F.simple k) (F.simple l)) (F.simple c) 1
        (m * a) := by
  have e1 := smove_expand F M hS ρ hr c 1 m one_ne_zero hm isCoprime_one_left (k, l)
  have e2 := smove_expand F M hS ρ hr c a m (by exact_mod_cast ha.ne') hm hcop
    (galoisPerm F M σ k, galoisPerm F M σ l)
  rw [← galois_row_one F M σ a hσ c (k, l) m]
  simp only at e1 e2
  rw [e1, e2, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, galois_mixedS F M σ a₀ ha₀ p k l,
    galois_row_neg_one F M hcyc σ a hσ c p m hm hgcd]
  ring

/-- The first row of a mixed object is a twist multiple of its `(1,0)` value. -/
theorem mixed_row_one_value (F : SphericalFusion C) (M : Modular F) (k l : F.Label) (V : C)
    (m : ℤ) :
    generalizedIndicatorAll F (mixedCenter (F.simple k) (F.simple l)) V 1 m =
      ((M.twistScalar k / M.twistScalar l) ^ m)⁻¹ *
        generalizedIndicatorAll F (mixedCenter (F.simple k) (F.simple l)) V 1 0 := by
  rw [show (1 : ℤ) = ((0 : ℕ) : ℤ) + 1 by norm_num, generalizedIndicatorAll_positive,
    generalizedIndicatorAll_positive]
  have h := mixed_indicatorInt_add_mul_degree F M k l V 0 0 m
  rw [show (0 : ℤ) + m * ((0 + 1 : ℕ) : ℤ) = m by push_cast; ring] at h
  exact h

/-- The T move along the row `(n+1, ·)`, by one degree. -/
theorem mixed_row_T (F : SphericalFusion C) (M : Modular F) (k l : F.Label) (V : C)
    (n : ℕ) (m : ℤ) :
    generalizedIndicatorAll F (mixedCenter (F.simple k) (F.simple l)) V ((n : ℤ) + 1)
        (m + ((n : ℤ) + 1)) =
      (M.twistScalar k / M.twistScalar l)⁻¹ *
        generalizedIndicatorAll F (mixedCenter (F.simple k) (F.simple l)) V ((n : ℤ) + 1) m := by
  rw [generalizedIndicatorAll_positive, generalizedIndicatorAll_positive]
  have h := mixed_indicatorInt_add_mul_degree F M k l V n m 1
  rw [one_mul, zpow_one] at h
  rw [← h]
  push_cast
  ring_nf

/-- Every automorphism of `ℂ` acts as a power `a > 0`, coprime to `N`, on the `N`-th roots of
unity. -/
theorem exists_pow_action (σ : ℂ ≃+* ℂ) {N : ℕ} (hN : 0 < N) :
    ∃ n : ℕ, Nat.Coprime (n + 1) N ∧ ∀ z : ℂ, z ^ N = 1 → σ z = z ^ ((n + 1 : ℕ) : ℤ) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hσζ : IsPrimitiveRoot (σ ζ) N := hζ.map_of_injective σ.injective
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hσζ.pow_eq_one
  have hkc : Nat.Coprime k N := (hζ.pow_iff_coprime hN k).mp (hk ▸ hσζ)
  obtain ⟨n, hn⟩ : ∃ n, k + N = n + 1 := ⟨k + N - 1, by omega⟩
  refine ⟨n, ?_, fun z hz => ?_⟩
  · rw [← hn]; exact Nat.coprime_add_self_left.mpr hkc
  · obtain ⟨e, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    rw [zpow_natCast, map_pow, ← hk, ← pow_mul, ← pow_mul, ← hn,
      show e * (k + N) = k * e + N * e by ring, pow_add, pow_mul ζ N e, hζ.pow_eq_one,
      one_pow, mul_one]

open Classical in
/-- **DLN Lemma 4.2 for `Z(A)`, in `A`-terms, from the mixed S move** (given one modular
lift): `σ²(θ_i) θ_{π 0} = θ_{π i}` for the Galois permutation `π`. -/
theorem galoisTwistCore_of_SMove_lift (F : SphericalFusion C) (M : Modular F)
    (hS : MixedNonzeroSMove F M)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ))) (hr : IsModularRepresentation F M ρ)
    (σ : ℂ ≃+* ℂ) (i : F.Label) :
    σ (σ (M.twistScalar i)) * M.twistScalar (galoisPerm F M σ F.unitLabel) =
      M.twistScalar (galoisPerm F M σ i) := by
  have hN := M.toRibbon.finite_twist.1
  have hSO := SMoveOrbit_of_nonzero F M hS
  have hcyc := mixedRowCyclotomic_of_SMove F M ρ hr hSO (mixedSCyclotomic_of_SMove F M hSO ρ hr)
  obtain ⟨n, hcopN, hσ⟩ := exists_pow_action σ hN
  obtain ⟨a₀, ha₀'⟩ := IsAlgClosed.exists_pow_nat_eq (F.globalDimension)⁻¹ two_pos
  have ha₀ : a₀ ^ 2 * F.globalDimension = 1 := by
    rw [ha₀', inv_mul_cancel₀ (F.globalDimension_ne_zero)]
  set a : ℕ := n + 1 with hadef
  have ha : 0 < a := Nat.succ_pos n
  set π := galoisPerm F M σ
  -- the two rows `(a, 1)` and `(a, 1 + a)`
  have L1 := galois_mixed_row F M hS ρ hr hcyc σ a ha hσ a₀ ha₀ i F.unitLabel i 1 one_ne_zero
    isCoprime_one_right (by simpa using hcopN)
  have hcop2 : IsCoprime (a : ℤ) (1 + a) := ⟨-1, 1, by ring⟩
  have hgcd2 : Nat.Coprime a ((1 + (a : ℤ)).natAbs * M.toRibbon.twistOrder) := by
    have : (1 + (a : ℤ)).natAbs = 1 + a := by omega
    rw [this]
    exact Nat.Coprime.mul_right (by simp [Nat.coprime_add_self_right]) hcopN
  have L2 := galois_mixed_row F M hS ρ hr hcyc σ a ha hσ a₀ ha₀ i F.unitLabel i (1 + a)
    (by omega) hcop2 hgcd2
  -- row values
  set t : ℂ := M.twistScalar F.unitLabel / M.twistScalar i with htdef
  set t' : ℂ := M.twistScalar (π F.unitLabel) / M.twistScalar (π i) with ht'def
  have ht : t ≠ 0 := mixed_twistRatio_ne_zero F M _ _
  have ht' : t' ≠ 0 := mixed_twistRatio_ne_zero F M _ _
  have hd : generalizedIndicatorAll F (mixedCenter (F.simple F.unitLabel) (F.simple i))
      (F.simple i) 1 0 = 1 := by
    rw [mixed_one_zero_value, F.fusion_unit_left, if_pos rfl]; simp
  rw [mixed_row_one_value F M, hd, mul_one] at L1 L2
  have hT := mixed_row_T F M (π F.unitLabel) (π i) (F.simple i) n 1
  rw [show ((n : ℤ) + 1) = (a : ℤ) by simp [hadef]] at hT
  rw [show (1 : ℤ) + a = 1 + (a : ℤ) from rfl] at hT
  rw [hT] at L2
  -- `t'⁻¹ (t^a)⁻¹ = (t^{(1+a)a})⁻¹`
  set ε := galoisSign F M σ a₀ F.unitLabel * galoisSign F M σ a₀ i
  set X := generalizedIndicatorAll F (mixedCenter (F.simple (π F.unitLabel))
    (F.simple (π i))) (F.simple i) (a : ℤ) 1
  have L1' : ε * X = (t ^ (a : ℤ))⁻¹ := by simpa only [one_mul] using L1
  have key : t'⁻¹ * (t ^ (a : ℤ))⁻¹ = (t ^ ((1 + (a : ℤ)) * a))⁻¹ := by
    rw [← L2, ← L1']; ring
  have hsplit : t ^ ((1 + (a : ℤ)) * a) = t ^ (a : ℤ) * t ^ ((a : ℤ) * a) := by
    rw [← zpow_add₀ ht]; ring_nf
  rw [hsplit, mul_inv, mul_comm (t ^ (a : ℤ))⁻¹] at key
  have hta : (t ^ (a : ℤ))⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ ht)
  have key' : t' = t ^ ((a : ℤ) * a) := by
    have := mul_right_cancel₀ hta key
    exact inv_injective this
  -- translate to twists
  have hθN : M.twistScalar i ^ M.toRibbon.twistOrder = 1 := twistScalar_pow_twistOrder M i
  have hσθ : σ (σ (M.twistScalar i)) = M.twistScalar i ^ ((a : ℤ) * a) := by
    rw [hσ _ hθN, map_zpow₀, hσ _ hθN, ← zpow_mul]
  have hθ0 : M.twistScalar F.unitLabel = 1 := M.toRibbon.twistScalar_unitLabel
  have hθi := M.toRibbon.twistScalar_ne_zero i
  have hθπi := M.toRibbon.twistScalar_ne_zero (π i)
  have hπ0 : M.twistScalar (π F.unitLabel) =
      M.twistScalar (π i) * (M.twistScalar i ^ ((a : ℤ) * a))⁻¹ := by
    have e := key'
    rw [htdef, ht'def, hθ0, div_eq_iff hθπi] at e
    rw [e, one_div, inv_zpow]; ring
  rw [hσθ, hπ0]
  have hz : M.twistScalar i ^ ((a : ℤ) * a) ≠ 0 := zpow_ne_zero _ hθi
  field_simp

/-- **The twist core for one category, for any permutation solving the character
equation**, from the mixed S move and one modular lift. -/
theorem galoisTwistCore_of_SMove_lift' (F : SphericalFusion C) (M : Modular F)
    (hS : MixedNonzeroSMove F M)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ))) (hr : IsModularRepresentation F M ρ)
    (σ : ℂ ≃+* ℂ) (π : F.Label → F.Label)
    (hπ : ∀ k i, σ (fusionChar F k i) = fusionChar F (π k) i) (i : F.Label) :
    σ (σ (M.twistScalar i)) * M.twistScalar (π F.unitLabel) = M.twistScalar (π i) := by
  have hπ' : ∀ k, π k = galoisPerm F M σ k := fun k =>
    fusionChar_injective F M (funext fun j => (hπ k j).symm.trans (galoisPerm_spec F M σ k j))
  rw [hπ', hπ']
  exact galoisTwistCore_of_SMove_lift F M hS ρ hr σ i

end VOA.Huang.NSGaloisCore

namespace VOA.Huang.NSGaloisCore

open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence VOA.Huang.NSGalois VOA.Huang.DLNBridge
  VOA.Huang.ZhuRep
open scoped MatrixGroups

universe u v w

attribute [-instance] hasRightDualUnit hasRightDualLeftDual

/-- **Existence of a genuine modular lift** for every modular category. This is TRUE: the
categorical projective `S, T` action lifts to a linear representation of `SL(2, ℤ)`, for example
with `a = D⁻¹` and `b` a cube root of `D / p⁺` (Bakalov–Kirillov 3.1.17, Turaev). It is **not
proved** in the library, because Mathlib has no presentation of `SL(2, ℤ)`. It is needed only to
make `MixedNonzeroSMove` (which quantifies over lifts) non-vacuous in the ρ-free statement
`NSGaloisTwistCore`. -/
def NSModularLiftExistsAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F),
    ∃ ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)), IsModularRepresentation F M ρ

/-- **`NSGaloisTwistCore` from the mixed S move**, given the existence of modular lifts. -/
theorem nsGaloisTwistCore_of_SMove_lifts (hS : NSMixedNonzeroSMoveAll.{v, w})
    (hL : NSModularLiftExistsAll.{v, w}) : NSGaloisTwistCore.{v, w} := by
  intro C _ _ _ _ _ _ _ _ _ _ F M σ π hπ i
  obtain ⟨ρ, hr⟩ := hL C F M
  exact galoisTwistCore_of_SMove_lift' F M (hS C F M) ρ hr σ π hπ i

/-- **`NSGaloisTwistAll` from the mixed S move alone.** `NSGaloisTwistAll` supplies a
modular lift, so no lift-existence hypothesis is needed. -/
theorem nsGaloisTwistAll_of_SMove (h : NSMixedNonzeroSMoveAll.{v, w}) :
    NSGaloisTwistAll.{v, w} := by
  intro C _ _ _ _ _ _ _ _ _ _ F M ρ a b hS hT hT' N hN hTN x y hxy
  classical
  have hmod : IsModularRepresentation F M (matrixRepToLinear ρ) := by
    refine ⟨a, b, fun z i => ?_, fun z i => ?_⟩
    · rw [matrixRepToLinear_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hS, mul_assoc]
    · rw [matrixRepToLinear_apply, Finset.sum_eq_single i]
      · rw [hT]
      · intro j _ hji
        rw [hT' i j (Ne.symm hji), zero_mul]
      · simp
  exact galoisTwist_of_core F M
    (fun σ π hπ i => galoisTwistCore_of_SMove_lift' F M (h C F M) _ hmod σ π hπ i)
    ρ a b hS hT hT' N hN hTN x y hxy

/-- **Both DLN classification inputs from two VOA-free statements**: the mixed S move at
positive-product off-diagonal rows (Ng–Schauenburg Theorem 5.4 for `Z(A)`) and DLN 2.3
(`MatrixDLNLifting`). -/
theorem dln_inputs_of_SMove_lifting (hS : NSMixedSameSignOffDiagonalSMoveAll.{0, 0})
    (hlift : MatrixDLNLifting) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} := by
  have hNZ : NSMixedNonzeroSMoveAll.{0, 0} := by
    intro C _ _ _ _ _ _ _ _ _ _ F M
    exact mixedNonzeroSMove_of_sameSignOffDiagonal F M (hS C F M)
  exact dln_inputs_of_NSKernel_twist (nsProjectiveKernelAll_of_sameSignOffDiagonal hS)
    zhuModularRepresentationInput_holds hlift
    (zhuGaloisTwistInput_of_NS (nsGaloisTwistAll_of_SMove hNZ))

/-- The same assembly from the nonzero-row S move (equivalent to the off-diagonal form by
`mixedNonzeroSMove_iff_sameSignOffDiagonal`). -/
theorem dln_inputs_of_nonzeroSMove_lifting (hS : NSMixedNonzeroSMoveAll.{0, 0})
    (hlift : MatrixDLNLifting) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_NSKernel_twist (nsProjectiveKernelAll_of_nonzeroSMove hS)
    zhuModularRepresentationInput_holds hlift
    (zhuGaloisTwistInput_of_NS (nsGaloisTwistAll_of_SMove hS))

end VOA.Huang.NSGaloisCore
