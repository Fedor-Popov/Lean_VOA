/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeInvolution
import VOA.Core.LocalSystemBare

/-!
# Orthogonal changes of oscillator frame on the Heisenberg Fock space  (M8g-0 bridge, part 1)

The general lattice VOA `V_L = FockN(rank L) ⊗ ℂ{L}` (`LatGen.latticeVOAGen`) writes its Fock
factor in **orthonormal** oscillator variables `aₐ(-n)` (`HeisenbergN.oscN _ 1`), and the
charge-`α` oscillator is `α(m) = ∑ₐ chargeCoord α a · aₐ(m)` (`LatGen.chargeOsc`), where the
coordinates `chargeCoord α = √G · coord α` depend on the chosen basis of `L`
(`latticeBasis`) through the Gram square root `frame`.  The Heisenberg relations depend on the
Gram matrix only through the orthonormality of the unit oscillators (`oscN_comm`), so a
morphism of lattice VOAs must act on the Fock factor by an **orthogonal** linear change of
oscillator variables.  This file provides that change of variables and the analytic-free
ingredients for the lattice-VOA morphism of `LatticeMorph.lean`.

## Contents
* `IntertwH g c A B` — the heterogeneous intertwining relation `g A(z) = c·B(z) g` for a linear
  map `g : V → W` between *different* spaces, closed under normal-ordered products
  (`IntertwH.nprod`), derivatives and scalars (copy of the `Intertw` calculus of
  `LatticeInvolution.lean`).
* `LatGen.fockMap Q : FockN r →ₐ FockN s` — the algebra map `X(k,a) ↦ ∑_b Q b a X(k,b)`, with
  the chain rule `fockMap_pderiv` and the oscillator intertwining `fockMap_oscN`
  (`φ aₐ(n) = ∑_b Q_{ba} a_b(n) φ`, using `Qᵀ Q = 1` for the annihilators), and
  `fockMap_ωN` (`φ ω = ω`, using `Q Qᵀ = 1`), `fockMap_comp` and the inverse `fockMap Qᵀ`.
* `LatGen.exists_fockMatrix` — for an isometric `ℤ`-linear map `ι : K → L` of positive-definite
  lattices of equal rank there is a complex matrix `Q` with `Q · chargeCoord_K α =
  chargeCoord_L (ι α)`, `Qᵀ Q = 1` and `Q Qᵀ = 1` (explicitly `Q = √G_L · M_ι · √G_K⁻¹`).
* `LatGen.signCoboundary` — **the cocycle comparison lemma**: if `D` is a `ℤ`-bilinear form on a
  free `ℤ`-module with `D(α,β) + D(β,α)` always even, then
  `c(α) = i^{∑ᵢ Dᵢᵢ aᵢ(aᵢ-1) + 2∑_{i<j} Dᵢⱼ aᵢ aⱼ}` is a `±1`-valued function with
  `c(α+β) = c(α) c(β) (-1)^{D(α,β)}`.  Applied to `D = cocExp_L ∘ (ι×ι) − cocExp_K`, whose
  symmetrisation is `⟨ια,ιβ⟩ − ⟨α,β⟩ = 0` mod 2, it says that the two FLM cocycles
  `ε_L(ι·,ι·)` and `ε_K` differ by the coboundary of `c`.

## Status
All declarations `sorry`-free; `#print axioms` on the main results gives
`[propext, Classical.choice, Quot.sound]`.  Unconditional.
-/

set_option linter.style.longLine false

namespace VOA

open Module (End)

/-! ## §1  Heterogeneous intertwining of formal distributions -/

section IntertwH

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- `g A(z) = c · B(z) g`, coefficientwise, for `g : V → W`. -/
def IntertwH (g : V →ₗ[ℂ] W) (c : ℂ) (A : FormalDist (End ℂ V)) (B : FormalDist (End ℂ W)) :
    Prop :=
  ∀ (t : ℤ) (x : V), g (A t x) = c • B t (g x)

theorem IntertwH.nprod {g : V →ₗ[ℂ] W} {c d : ℂ} {a b : FormalDist (End ℂ V)}
    {a' b' : FormalDist (End ℂ W)}
    (ha : IsField a) (hb : IsField b) (ha' : IsField a') (hb' : IsField b')
    (hA : IntertwH g c a a') (hB : IntertwH g d b b') :
    IntertwH g (c * d) (VOA.nprod ha hb) (VOA.nprod ha' hb') := by
  intro s x
  rw [nprod_apply, nprod_apply,
    smul_finsum' _ (normalOrdered_diag_support_finite ha' hb' s (g x))]
  refine (g.toAddMonoidHom.map_finsum (normalOrdered_diag_support_finite ha hb s x)).trans ?_
  refine finsum_congr fun m => ?_
  change g (normalOrdered a b m (s - m) x) = (c * d) • normalOrdered a' b' m (s - m) (g x)
  rw [normalOrdered_apply, normalOrdered_apply]
  split_ifs
  · rw [Module.End.mul_apply, Module.End.mul_apply, hA, hB, map_smul, smul_smul]
  · rw [Module.End.mul_apply, Module.End.mul_apply, hB, hA, map_smul, smul_smul, mul_comm d c]

theorem IntertwH.deriv {g : V →ₗ[ℂ] W} {c : ℂ} {A : FormalDist (End ℂ V)}
    {B : FormalDist (End ℂ W)} (h : IntertwH g c A B) :
    IntertwH g c (VOA.deriv A) (VOA.deriv B) := by
  intro t x
  rw [deriv_apply, deriv_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul, h,
    smul_comm]

theorem IntertwH.deriv_iterate {g : V →ₗ[ℂ] W} {c : ℂ} {A : FormalDist (End ℂ V)}
    {B : FormalDist (End ℂ W)} (h : IntertwH g c A B) (i : ℕ) :
    IntertwH g c (VOA.deriv^[i] A) (VOA.deriv^[i] B) := by
  induction i with
  | zero => exact h
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ih.deriv

theorem IntertwH.const_smul {g : V →ₗ[ℂ] W} {c : ℂ} {A : FormalDist (End ℂ V)}
    {B : FormalDist (End ℂ W)} (h : IntertwH g c A B) (e : ℂ) :
    IntertwH g c (e • A) (e • B) := by
  intro t x
  change g ((e • A t) x) = c • (e • B t) (g x)
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, h, smul_comm]

/-- `∂^i` commutes with finite sums of formal distributions. -/
theorem deriv_iterate_sum {ι : Type*} (s : Finset ι) (f : ι → FormalDist (End ℂ W)) (i : ℕ) :
    VOA.deriv^[i] (∑ b ∈ s, f b) = ∑ b ∈ s, VOA.deriv^[i] (f b) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, map_sum]
      simp only [Function.iterate_succ_apply']

/-- Finite sums of fields are fields. -/
theorem isField_finsetSum {ι : Type*} (s : Finset ι) (f : ι → FormalDist (End ℂ W))
    (hf : ∀ b, IsField (f b)) : IsField (∑ b ∈ s, f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Fld.isField_zero
  | insert b s hb ih => rw [Finset.sum_insert hb]; exact Fld.isField_add (hf b) ih

/-- The normal-ordered product is linear in its left argument (finite sums with scalars). -/
theorem nprod_finsetSum_left {ι : Type*} (s : Finset ι) (e : ι → ℂ) (f : ι → FormalDist (End ℂ W))
    (hf : ∀ b, IsField (f b)) {g : FormalDist (End ℂ W)} (hg : IsField g)
    (hs : IsField (∑ b ∈ s, e b • f b)) :
    VOA.nprod hs hg = ∑ b ∈ s, e b • VOA.nprod (hf b) hg := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact Fld.nprod_zero_left hg
  | insert b s hb ih =>
      have h1 : IsField (∑ b ∈ s, e b • f b) :=
        isField_finsetSum s _ fun b => Fld.isField_smul (e b) (hf b)
      rw [Fld.raw_nprod_congr hs (Fld.isField_add (Fld.isField_smul (e b) (hf b)) h1) hg
        (Finset.sum_insert hb), Fld.nprod_add_left (Fld.isField_smul (e b) (hf b)) h1 hg,
        Fld.nprod_smul_left, ih h1, Finset.sum_insert hb]

end IntertwH

end VOA

namespace VOA.LatGen

open scoped BigOperators TensorProduct Matrix
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN MvPolynomial

/-! ## §2  The orthogonal change of oscillator variables -/

section FockMap

variable {r s : ℕ} (Q : Matrix (Fin s) (Fin r) ℂ)

/-- The algebra map of Fock spaces induced by a linear change of oscillator variables:
`X(k,a) ↦ ∑_b Q b a · X(k,b)` (all mode levels `k` transformed by the same matrix). -/
noncomputable def fockMap : FockN r →ₐ[ℂ] FockN s :=
  MvPolynomial.aeval (fun v : ℕ × Fin r => ∑ b : Fin s, Q b v.2 • (X (v.1, b) : FockN s))

@[simp] theorem fockMap_X (k : ℕ) (a : Fin r) :
    fockMap Q (X (k, a)) = ∑ b : Fin s, Q b a • (X (k, b) : FockN s) := by
  rw [fockMap, MvPolynomial.aeval_X]

theorem fockMap_one : fockMap Q 1 = 1 := map_one _

theorem fockMap_mul (p q : FockN r) : fockMap Q (p * q) = fockMap Q p * fockMap Q q :=
  map_mul _ p q

/-- **The chain rule**: `∂_{(k,b)} (φ p) = ∑ₐ Q b a · φ(∂_{(k,a)} p)`. -/
theorem fockMap_pderiv (k : ℕ) (b : Fin s) (p : FockN r) :
    pderiv (k, b) (fockMap Q p) = ∑ a : Fin r, Q b a • fockMap Q (pderiv (k, a) p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq, pderiv_C]
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      rw [MvPolynomial.algebraMap_eq, pderiv_C, map_zero, smul_zero]
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_add, map_add, smul_add]
  | mul_X p w hp =>
      obtain ⟨k', c⟩ := w
      have hX : pderiv (k, b) (∑ b' : Fin s, Q b' c • (X (k', b') : FockN s))
          = if k' = k then Q b c • (1 : FockN s) else 0 := by
        rw [map_sum]
        simp only [Derivation.map_smul, pderiv_X, Pi.single_apply, Prod.mk.injEq]
        by_cases hk : k' = k
        · simp [hk]
        · simp [hk]
      have hR : ∀ a : Fin r, pderiv (k, a) (p * X (k', c))
          = p * (if (k', c) = (k, a) then 1 else 0) + X (k', c) * pderiv (k, a) p := by
        intro a
        rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul, Pi.single_apply]
      rw [fockMap_mul, fockMap_X, Derivation.leibniz, hp, hX, smul_eq_mul, smul_eq_mul]
      simp only [hR, map_add, fockMap_mul, fockMap_X, smul_add, Finset.sum_add_distrib]
      congr 1
      · by_cases hk : k' = k
        · subst hk
          rw [if_pos rfl, Finset.sum_eq_single c (fun a _ ha => by
              rw [if_neg (by simp [Ne.symm ha]), map_zero, mul_zero, smul_zero])
            (fun h => absurd (Finset.mem_univ c) h), if_pos rfl, map_one, mul_one, mul_smul_comm, mul_one]
        · rw [if_neg hk, mul_zero]
          refine (Finset.sum_eq_zero fun a _ => ?_).symm
          rw [if_neg (by simp [hk]), map_zero, mul_zero, smul_zero]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [mul_smul_comm]

/-- **Oscillator intertwining**: `φ aₐ(n) = ∑_b Q_{ba} a_b(n) φ` for all modes `n`, provided
`Qᵀ Q = 1` (used only for the annihilation modes `n > 0`, via the chain rule). -/
theorem fockMap_oscN (hQ : Qᵀ * Q = 1) (k : ℂ) (a : Fin r) (n : ℤ) (p : FockN r) :
    fockMap Q (oscN r k a n p) = ∑ b : Fin s, Q b a • oscN s k b n (fockMap Q p) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · simp only [oscN_apply_neg _ k _ hn, fockMap_mul, fockMap_X, Finset.sum_mul, smul_mul_assoc]
  · subst hn; simp only [oscN_zero, LinearMap.zero_apply, map_zero, smul_zero,
      Finset.sum_const_zero]
  · simp only [oscN_apply_pos _ k _ hn, map_smul, fockMap_pderiv, Finset.smul_sum]
    have hδ : ∀ a' : Fin r, ∑ b : Fin s, Q b a * Q b a' = if a = a' then 1 else 0 := by
      intro a'
      have h := congrFun (congrFun hQ a) a'
      rw [Matrix.mul_apply, Matrix.one_apply] at h
      simpa only [Matrix.transpose_apply] using h
    calc (n : ℂ) • k • fockMap Q (pderiv ((n - 1).toNat, a) p)
        = ∑ a' : Fin r, (if a = a' then (1 : ℂ) else 0) •
            ((n : ℂ) • k • fockMap Q (pderiv ((n - 1).toNat, a') p)) := by
          rw [Finset.sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_smul])
            (fun h => absurd (Finset.mem_univ a) h), if_pos rfl, one_smul]
      _ = ∑ a' : Fin r, ∑ b : Fin s, (Q b a * Q b a') •
            ((n : ℂ) • k • fockMap Q (pderiv ((n - 1).toNat, a') p)) := by
          refine Finset.sum_congr rfl fun a' _ => ?_
          rw [← hδ a', Finset.sum_smul]
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun a' _ => ?_
          rw [mul_smul, smul_comm (Q b a') (n : ℂ), smul_comm (Q b a') k]

/-- Oscillator combinations: if `Q u = v` then `φ ∘ ∑ₐ uₐ aₐ(n) = (∑_b v_b a_b(n)) ∘ φ`. -/
theorem fockMap_oscComb (hQ : Qᵀ * Q = 1) (u : Fin r → ℂ) (v : Fin s → ℂ) (huv : Q *ᵥ u = v)
    (k : ℂ) (n : ℤ) (p : FockN r) :
    fockMap Q ((∑ a : Fin r, u a • oscN r k a n) p)
      = (∑ b : Fin s, v b • oscN s k b n) (fockMap Q p) := by
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    fockMap_oscN Q hQ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul, ← huv, Matrix.mulVec, dotProduct]
  congr 1
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- Creation-variable combinations: if `Q u = v` then `φ(∑ₐ uₐ X(m,a)) = ∑_b v_b X(m,b)`. -/
theorem fockMap_Xcomb (u : Fin r → ℂ) (v : Fin s → ℂ) (huv : Q *ᵥ u = v) (m : ℕ) :
    fockMap Q (∑ a : Fin r, u a • (X (m, a) : FockN r)) = ∑ b : Fin s, v b • (X (m, b) : FockN s) := by
  simp only [map_sum, map_smul, fockMap_X, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul, ← huv, Matrix.mulVec, dotProduct]
  congr 1
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem ωNa_one_eq (a : Fin r) :
    ωNa r 1 a = (1 / 2 : ℂ) • ((X (0, a) : FockN r) * X (0, a)) := by
  rw [ωNa, oscN_apply_neg r 1 a (show (-1 : ℤ) < 0 by norm_num),
    oscN_apply_neg r 1 a (show (-1 : ℤ) < 0 by norm_num), vacuumN, mul_one, mul_one]
  rfl

/-- `φ` fixes the Heisenberg conformal vector when `Q Qᵀ = 1`. -/
theorem fockMap_ωN (hQ' : Q * Qᵀ = 1) : fockMap Q (ωN r 1) = ωN s 1 := by
  simp only [ωN, ωNa_one_eq, map_sum, map_smul, fockMap_mul, fockMap_X]
  simp only [Finset.sum_mul_sum, smul_mul_smul_comm, ← Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single b]
  · rw [← Finset.sum_smul]
    have h := congrFun (congrFun hQ' b) b
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    simp only [Matrix.transpose_apply] at h
    rw [h, one_smul]
  · intro b' _ hb'
    rw [← Finset.sum_smul]
    have h := congrFun (congrFun hQ' b) b'
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Ne.symm hb')] at h
    simp only [Matrix.transpose_apply] at h
    rw [h, zero_smul]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- Composition: `fockMap P ∘ fockMap Q = fockMap (P Q)`. -/
theorem fockMap_comp {t : ℕ} (P : Matrix (Fin t) (Fin s) ℂ) (p : FockN r) :
    fockMap P (fockMap Q p) = fockMap (P * Q) p := by
  have h : (fockMap P).comp (fockMap Q) = fockMap (P * Q) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨k, a⟩ := v
    rw [AlgHom.comp_apply, fockMap_X, fockMap_X, map_sum]
    simp only [map_smul, fockMap_X, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  exact congrArg (fun f : FockN r →ₐ[ℂ] FockN t => f p) h

theorem fockMap_id (p : FockN r) : fockMap (1 : Matrix (Fin r) (Fin r) ℂ) p = p := by
  have h : fockMap (1 : Matrix (Fin r) (Fin r) ℂ) = AlgHom.id ℂ (FockN r) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨k, a⟩ := v
    rw [fockMap_X, AlgHom.id_apply, Finset.sum_eq_single a]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro b _ hb; rw [Matrix.one_apply_ne hb, zero_smul]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [h, AlgHom.id_apply]

/-- For an orthogonal `Q` (`Qᵀ Q = 1`, `Q Qᵀ = 1`) the change of variables is a linear
equivalence, with inverse `fockMap Qᵀ`. -/
noncomputable def fockEquiv (hQ : Qᵀ * Q = 1) (hQ' : Q * Qᵀ = 1) : FockN r ≃ₗ[ℂ] FockN s where
  toLinearMap := (fockMap Q).toLinearMap
  invFun := fockMap Qᵀ
  left_inv p := by
    change fockMap Qᵀ (fockMap Q p) = p
    rw [fockMap_comp, hQ, fockMap_id]
  right_inv p := by
    change fockMap Q (fockMap Qᵀ p) = p
    rw [fockMap_comp, hQ', fockMap_id]

@[simp] theorem fockEquiv_apply (hQ : Qᵀ * Q = 1) (hQ' : Q * Qᵀ = 1) (p : FockN r) :
    fockEquiv Q hQ hQ' p = fockMap Q p := rfl

end FockMap

/-! ## §3  The orthogonal frame matrix of a lattice isometry -/

section Frame

variable (K L : IntegralLattice)

theorem frame_det_isUnit (hPos : L.PosDef) : IsUnit (frame L).det := by
  have h := congrArg Matrix.det (frame_mul_self L hPos)
  rw [Matrix.det_mul] at h
  have hpos : 0 < (gramR L).det := (gramR_posDef L hPos).det_pos
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, zero_mul] at h
  exact hpos.ne' h.symm

/-- The real matrix of a `ℤ`-linear map in the chosen lattice bases: `M j i = coord_L (ι Bᵢ) j`. -/
noncomputable def latMatrix (ι : K.carrier →ₗ[ℤ] L.carrier) :
    Matrix (Fin (latRank L)) (Fin (latRank K)) ℝ :=
  Matrix.of fun j i => coordR L (ι (latticeBasis K i)) j

theorem coordR_map (ι : K.carrier →ₗ[ℤ] L.carrier) (α : K.carrier) :
    coordR L (ι α) = latMatrix K L ι *ᵥ coordR K α := by
  funext j
  conv_lhs => rw [← (latticeBasis K).sum_repr α]
  simp only [coordR, coord, map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, Matrix.mulVec,
    dotProduct, latMatrix, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem latMatrix_gram (ι : K.carrier →ₗ[ℤ] L.carrier)
    (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β) :
    (latMatrix K L ι)ᵀ * gramR L * latMatrix K L ι = gramR K := by
  ext i i'
  have h := coordR_gram_bilin L (ι (latticeBasis K i)) (ι (latticeBasis K i'))
  rw [hι] at h
  have hK : gramR K i i' = ((K.form (latticeBasis K i) (latticeBasis K i') : ℤ) : ℝ) := by
    simp [gramR, gram]
  rw [hK, ← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, latMatrix, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  ring

/-- The orthogonal frame matrix `O = √G_L · M_ι · √G_K⁻¹` of `ι`. -/
noncomputable def frameMatrix (ι : K.carrier →ₗ[ℤ] L.carrier) :
    Matrix (Fin (latRank L)) (Fin (latRank K)) ℝ :=
  frame L * latMatrix K L ι * (frame K)⁻¹

theorem frameMatrix_orthCoord (hK : K.PosDef) (ι : K.carrier →ₗ[ℤ] L.carrier) (α : K.carrier) :
    frameMatrix K L ι *ᵥ orthCoord K α = orthCoord L (ι α) := by
  rw [orthCoord, orthCoord, Matrix.mulVec_mulVec, frameMatrix, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (frame_det_isUnit K hK), Matrix.mul_one,
    ← Matrix.mulVec_mulVec, coordR_map]

theorem frameMatrix_transpose_mul (hK : K.PosDef) (hL : L.PosDef)
    (ι : K.carrier →ₗ[ℤ] L.carrier) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β) :
    (frameMatrix K L ι)ᵀ * frameMatrix K L ι = 1 := by
  have hinvT : ((frame K)⁻¹)ᵀ = (frame K)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, frame_transpose]
  have hG := latMatrix_gram K L ι hι
  rw [← frame_transpose_mul_self L hL] at hG
  rw [frameMatrix, Matrix.transpose_mul, Matrix.transpose_mul, hinvT]
  calc (frame K)⁻¹ * ((latMatrix K L ι)ᵀ * (frame L)ᵀ) * (frame L * latMatrix K L ι * (frame K)⁻¹)
      = (frame K)⁻¹ * ((latMatrix K L ι)ᵀ * ((frame L)ᵀ * frame L) * latMatrix K L ι)
          * (frame K)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (frame K)⁻¹ * (frame K * frame K) * (frame K)⁻¹ := by
          rw [hG, frame_mul_self K hK]
    _ = 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (frame_det_isUnit K hK), Matrix.one_mul,
            Matrix.mul_nonsing_inv _ (frame_det_isUnit K hK)]

/-- The complex oscillator matrix of `ι`, indexed by the Fock directions `Fin (rank ·)`. -/
noncomputable def oscMatrix (ι : K.carrier →ₗ[ℤ] L.carrier) :
    Matrix (Fin (rank L)) (Fin (rank K)) ℂ :=
  ((frameMatrix K L ι).map Complex.ofRealHom).submatrix (rankEquiv L) (rankEquiv K)

theorem oscMatrix_chargeCoord (hK : K.PosDef) (ι : K.carrier →ₗ[ℤ] L.carrier) (α : K.carrier) :
    oscMatrix K L ι *ᵥ chargeCoord K α = chargeCoord L (ι α) := by
  funext b
  have h := congrFun (frameMatrix_orthCoord K L hK ι α) (rankEquiv L b)
  rw [chargeCoord, ← h]
  simp only [Matrix.mulVec, dotProduct, oscMatrix, Matrix.submatrix_apply, Matrix.map_apply,
    Complex.ofRealHom_eq_coe, chargeCoord]
  rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_mul]
  exact Equiv.sum_comp (rankEquiv K) (fun a => (frameMatrix K L ι (rankEquiv L b) a : ℂ) *
    (orthCoord K α a : ℂ))

theorem oscMatrix_transpose_mul (hK : K.PosDef) (hL : L.PosDef)
    (ι : K.carrier →ₗ[ℤ] L.carrier) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β) :
    (oscMatrix K L ι)ᵀ * oscMatrix K L ι = 1 := by
  rw [oscMatrix, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.transpose_map,
    ← Matrix.map_mul, frameMatrix_transpose_mul K L hK hL ι hι, Matrix.map_one _ (by simp)
    (by simp), Matrix.submatrix_one_equiv]

theorem oscMatrix_mul_transpose (hK : K.PosDef) (hL : L.PosDef)
    (ι : K.carrier →ₗ[ℤ] L.carrier) (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β)
    (hr : rank K = rank L) :
    oscMatrix K L ι * (oscMatrix K L ι)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (finCongr hr)).mp (oscMatrix_transpose_mul K L hK hL ι hι)

end Frame

/-! ## §4  Comparing two sign cocycles: the coboundary lemma -/

section Coboundary

variable {M : Type*} [AddCommGroup M] {n : ℕ} (B : Module.Basis (Fin n) ℤ M)
  (D : M →ₗ[ℤ] M →ₗ[ℤ] ℤ)

/-- The symmetrisation of `D` through its upper triangle in the basis `B`. -/
noncomputable def symMatrix : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i ≤ j then D (B i) (B j) else D (B j) (B i)

/-- The symmetric `ℤ`-bilinear form with matrix `symMatrix B D`. -/
noncomputable def symForm : M →ₗ[ℤ] M →ₗ[ℤ] ℤ := Matrix.toLinearMap₂ B B (symMatrix B D)

theorem symForm_basis (i j : Fin n) : symForm B D (B i) (B j) = symMatrix B D i j :=
  Matrix.toLinearMap₂_apply_basis B B _ i j

theorem symForm_comm (x y : M) : symForm B D x y = symForm B D y x := by
  have h : symForm B D = (symForm B D).flip := by
    refine LinearMap.ext_basis B B fun i j => ?_
    rw [LinearMap.flip_apply, symForm_basis, symForm_basis, symMatrix, symMatrix]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_pos hij.le, if_neg (not_le.mpr hij)]
    · rfl
    · rw [if_neg (not_le.mpr hij), if_pos hij.le]
  exact congrArg (fun f : M →ₗ[ℤ] M →ₗ[ℤ] ℤ => f x y) h

theorem two_dvd_sub_symForm (hD : ∀ x y, 2 ∣ D x y + D y x) (x y : M) :
    2 ∣ D x y - symForm B D x y := by
  have hb : ∀ i j, 2 ∣ (D - symForm B D) (B i) (B j) := by
    intro i j
    rw [LinearMap.sub_apply, LinearMap.sub_apply, symForm_basis, symMatrix]
    split_ifs
    · rw [sub_self]; exact dvd_zero 2
    · have h := hD (B i) (B j)
      have h2 : D (B i) (B j) - D (B j) (B i) = (D (B i) (B j) + D (B j) (B i)) - 2 * D (B j) (B i) := by ring
      rw [h2]; exact dvd_sub h (dvd_mul_right 2 _)
  have h := LinearMap.sum_repr_mul_repr_mul B B (B := D - symForm B D) x y
  rw [← LinearMap.sub_apply, ← LinearMap.sub_apply, ← h, Finsupp.sum]
  refine Finset.dvd_sum fun i _ => ?_
  rw [Finsupp.sum]
  refine Finset.dvd_sum fun j _ => ?_
  rw [smul_eq_mul, smul_eq_mul]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (hb i j) _) _

/-- The **coboundary function** `c(α) = i^{S(α,α)}`, `S = symForm B D`. -/
noncomputable def cobSign (α : M) : ℂ := Complex.I ^ (symForm B D α α)

theorem cobSign_ne_zero (α : M) : cobSign B D α ≠ 0 := zpow_ne_zero _ Complex.I_ne_zero

theorem cobSign_zero : cobSign B D 0 = 1 := by simp [cobSign]

theorem cobSign_neg (α : M) : cobSign B D (-α) = cobSign B D α := by
  simp [cobSign]

theorem neg_one_zpow_eq_of_two_dvd {a b : ℤ} (h : 2 ∣ a - b) : (-1 : ℂ) ^ a = (-1 : ℂ) ^ b := by
  obtain ⟨k, hk⟩ := h
  rw [show a = b + 2 * k by omega, zpow_add₀ (by norm_num), zpow_mul]
  norm_num

/-- **The coboundary identity** `c(α+β) = c(α)·c(β)·(−1)^{D(α,β)}`, given that `D(α,β)+D(β,α)` is
always even. -/
theorem cobSign_add (hD : ∀ x y, 2 ∣ D x y + D y x) (α β : M) :
    cobSign B D (α + β) = cobSign B D α * cobSign B D β * (-1 : ℂ) ^ (D α β) := by
  have hS : symForm B D (α + β) (α + β)
      = symForm B D α α + symForm B D β β + 2 * symForm B D α β := by
    simp only [map_add, LinearMap.add_apply]
    rw [symForm_comm B D β α]; ring
  rw [cobSign, hS, zpow_add₀ Complex.I_ne_zero, zpow_add₀ Complex.I_ne_zero, zpow_mul,
    show Complex.I ^ (2 : ℤ) = -1 by rw [zpow_two, Complex.I_mul_I], cobSign, cobSign, neg_one_zpow_eq_of_two_dvd (two_dvd_sub_symForm B D hD α β)]

end Coboundary

/-! ## §5  The cocycle comparison for a lattice isometry -/

section CocycleCompare

variable (K L : IntegralLattice)

/-- The FLM cocycle exponent `cocExp` as a `ℤ`-bilinear map. -/
noncomputable def cocForm : L.carrier →ₗ[ℤ] L.carrier →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (cocExp L (latticeBasis L)) (cocExp_add_left L _)
    (fun c α β => by
      simp only [cocExp, map_zsmul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (cocExp_add_right L _)
    (fun c α β => by
      simp only [cocExp, map_zsmul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem latticeCocycle_eq_zpow (α β : L.carrier) :
    latticeCocycle L α β = (-1 : ℂ) ^ (cocForm L α β) := rfl

/-- The discrepancy `D(α,β) = coc_L(ια,ιβ) − coc_K(α,β)` between the two FLM cocycle exponents. -/
noncomputable def cocDiff (ι : K.carrier →ₗ[ℤ] L.carrier) : K.carrier →ₗ[ℤ] K.carrier →ₗ[ℤ] ℤ :=
  (cocForm L).compl₁₂ ι ι - cocForm K

theorem two_dvd_of_neg_one_zpow_eq_one {a : ℤ} (h : (-1 : ℂ) ^ a = 1) : 2 ∣ a := by
  rcases Int.even_or_odd a with ha | ha
  · exact even_iff_two_dvd.mp ha
  · rw [ha.neg_one_zpow] at h; norm_num at h

theorem neg_one_zpow_cocForm_comm (hEven : L.Even) (α β : L.carrier) :
    (-1 : ℂ) ^ (cocForm L α β + cocForm L β α) = (-1 : ℂ) ^ (L.form α β) := by
  rw [zpow_add₀ (by norm_num), ← latticeCocycle_eq_zpow, ← latticeCocycle_eq_zpow,
    latticeCocycle_comm L hEven]

theorem cocDiff_symm_even (hK : K.Even) (hL : L.Even) (ι : K.carrier →ₗ[ℤ] L.carrier)
    (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β) (x y : K.carrier) :
    2 ∣ cocDiff K L ι x y + cocDiff K L ι y x := by
  apply two_dvd_of_neg_one_zpow_eq_one
  have h1 := neg_one_zpow_cocForm_comm L hL (ι x) (ι y)
  have h2 := neg_one_zpow_cocForm_comm K hK x y
  rw [hι] at h1
  simp only [cocDiff, LinearMap.sub_apply, LinearMap.compl₁₂_apply]
  rw [show cocForm L (ι x) (ι y) - cocForm K x y + (cocForm L (ι y) (ι x) - cocForm K y x)
      = (cocForm L (ι x) (ι y) + cocForm L (ι y) (ι x)) - (cocForm K x y + cocForm K y x) by ring,
    zpow_sub₀ (by norm_num), h1, h2, div_self (zpow_ne_zero _ (by norm_num))]

/-- The momentum rescaling `c(α)` comparing the two cocycles (a fourth root of unity). -/
noncomputable def latCob (ι : K.carrier →ₗ[ℤ] L.carrier) (α : K.carrier) : ℂ :=
  cobSign (latticeBasis K) (cocDiff K L ι) α

/-- **Cocycle comparison**: `ε_L(ια,ιβ)·c(α)·c(β) = ε_K(α,β)·c(α+β)`. -/
theorem latticeCocycle_map_mul_latCob (hK : K.Even) (hL : L.Even) (ι : K.carrier →ₗ[ℤ] L.carrier)
    (hι : ∀ α β, L.form (ι α) (ι β) = K.form α β) (α β : K.carrier) :
    latticeCocycle L (ι α) (ι β) * (latCob K L ι α * latCob K L ι β)
      = latticeCocycle K α β * latCob K L ι (α + β) := by
  rw [latCob, latCob, latCob, cobSign_add _ _ (cocDiff_symm_even K L hK hL ι hι),
    latticeCocycle_eq_zpow, latticeCocycle_eq_zpow]
  simp only [cocDiff, LinearMap.sub_apply, LinearMap.compl₁₂_apply]
  rw [zpow_sub₀ (by norm_num)]
  have h : (-1 : ℂ) ^ (cocForm K α β) * (-1 : ℂ) ^ (cocForm K α β) = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  field_simp

theorem latCob_ne_zero (ι : K.carrier →ₗ[ℤ] L.carrier) (α : K.carrier) : latCob K L ι α ≠ 0 :=
  cobSign_ne_zero _ _ α

theorem latCob_zero (ι : K.carrier →ₗ[ℤ] L.carrier) : latCob K L ι 0 = 1 := cobSign_zero _ _

theorem latCob_neg (ι : K.carrier →ₗ[ℤ] L.carrier) (α : K.carrier) :
    latCob K L ι (-α) = latCob K L ι α := cobSign_neg _ _ α

end CocycleCompare

end VOA.LatGen
