/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3SugawaraField

/-!
# Finite normal-ordering commutators for the sl3 Sugawara translation

The actual inverse trace tensor and structure constants enter each operator
identity. The central terms sum to 2mk; the remaining normal-ordering
residue is controlled by the proved adjoint Casimir six. Every infinite
sum used below has proved finite support on each vacuum-module vector.
-/
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
open VOA VOA.AffineSl3

namespace VOA.AffineSl3.SugawaraCov

open scoped BigOperators
open Module (End)
open VOA.AffineLie

universe u

-- Sanity: the target signature (the gate `hJ`).
example (k : ℂ) (a : Fin 8) : Prop :=
  Reconstruction.DCovariant (AffineSl3.Ltrans k) (AffineSl3.Jfield k a)

/-! ## The affine Sugawara per-term operator -/

/-- The normal-ordered per-term operator `T^{aa,bb}_p = :J^{aa}_{-p-1} J^{bb}_p:`, the `p`-summand
of `(nprod (Jfield aa)(Jfield bb))(-1)`. -/
noncomputable def sugTermJ (k : ℂ) (aa bb : Fin 8) (p : ℤ) : End ℂ (Vacuum k) :=
  if 0 ≤ p then J k aa (-p - 1) * J k bb p else J k bb p * J k aa (-p - 1)

/-- Applying the normal-ordered term uses its specified mode ordering. -/
theorem sugTermJ_apply (k : ℂ) (aa bb : Fin 8) (p : ℤ) (x : Vacuum k) :
    sugTermJ k aa bb p x
      = if 0 ≤ p then J k aa (-p - 1) (J k bb p x) else J k bb p (J k aa (-p - 1) x) := by
  rw [sugTermJ]; split_ifs <;> rw [Module.End.mul_apply]

/-- The `(-1)`-coefficient of `nprod (Jfield aa)(Jfield bb)` acting on `x` is the finite
normal-ordered sum `∑ᶠ p, :J^{aa}_{-p-1} J^{bb}_p: x`. -/
theorem nprod_neg_one_coeff (k : ℂ) (aa bb : Fin 8) (x : Vacuum k) :
    nprod (Jfield_isField k aa) (Jfield_isField k bb) (-1) x
      = ∑ᶠ p : ℤ, sugTermJ k aa bb p x := by
  rw [nprod_apply]
  refine finsum_congr fun p => ?_
  rw [normalOrdered_apply, Jfield_apply, Jfield_apply, sugTermJ_apply,
      show -(-1 - p) - 1 = p from by ring]
  by_cases hp : 0 ≤ p
  · rw [if_pos hp, if_pos hp, Module.End.mul_apply]
  · rw [if_neg hp, if_neg hp, Module.End.mul_apply]

/-- The Sugawara prefactor `c₀ = (2(k+h^∨))⁻¹ = (2(k+3))⁻¹`. -/
noncomputable def c0 (k : ℂ) : ℂ := (2 * (k + dualCoxeter))⁻¹

/-- **The `Ltrans` action formula** `L₋₁ x = c₀ ∑_{aa,bb} κ⁻¹(aa,bb) ∑ᶠ_p :J^{aa}_{-p-1}J^{bb}_p: x`,
the affine analogue of `Lvir_apply'`. -/
theorem Ltrans_apply (k : ℂ) (x : Vacuum k) :
    Ltrans k x
      = c0 k • ∑ aa : Fin 8, ∑ bb : Fin 8,
          kappaInv aa bb • ∑ᶠ p : ℤ, sugTermJ k aa bb p x := by
  rw [Ltrans_eq, sugawaraField]
  show (c0 k • (Reconstruction.evalAt (-1) x
      (∑ aa : Fin 8, ∑ bb : Fin 8,
        kappaInv aa bb • nprod (Jfield_isField k aa) (Jfield_isField k bb)))) = _
  rw [map_sum]
  refine congrArg (c0 k • ·) ?_
  refine Finset.sum_congr rfl fun aa _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun bb _ => ?_
  rw [map_smul]
  refine congrArg (kappaInv aa bb • ·) ?_
  rw [Reconstruction.evalAt_apply, nprod_neg_one_coeff]

/-- The `p`-indexed family `p ↦ sugTermJ aa bb p x` has finite support
(it is `normalOrdered (Jfield aa)(Jfield bb) p (-1-p) x`). -/
theorem sugTermJ_support_finite (k : ℂ) (aa bb : Fin 8) (x : Vacuum k) :
    (Function.support (fun p : ℤ => sugTermJ k aa bb p x)).Finite := by
  have hfin := normalOrdered_diag_support_finite (Jfield_isField k aa) (Jfield_isField k bb)
    (-1) x
  apply Set.Finite.subset hfin
  intro p hp
  rw [Function.mem_support] at hp ⊢
  intro hzero; apply hp
  rw [normalOrdered_apply, Jfield_apply, Jfield_apply,
      show -(-1 - p) - 1 = p from by ring] at hzero
  rw [sugTermJ_apply]
  by_cases hpp : 0 ≤ p
  · rw [if_pos hpp]; rw [if_pos hpp, Module.End.mul_apply] at hzero; exact hzero
  · rw [if_neg hpp]; rw [if_neg hpp, Module.End.mul_apply] at hzero; exact hzero

/-! ## The elementary current bracket as an operator, and the per-term Leibniz expansion -/

/-- Restating `current_comm` as a clean operator bracket `[J^a_m, J^b_n]`. -/
theorem J_bracket (k : ℂ) (a b : Fin 8) (m n : ℤ) :
    J k a m * J k b n - J k b n * J k a m
      = (∑ c, structureConstant a b c • J k c (m + n))
        + (if m + n = 0 then ((m : ℂ) * k * formTable a b) • LinearMap.id else 0) :=
  current_comm k a b m n

/-- A scalar multiple of `id` is central: it commutes with any `J^d_s` (so absorbing
`ID` on either side leaves the single current). -/
theorem J_mul_smul_id (k : ℂ) (d : Fin 8) (s : ℤ) (cc : ℂ) :
    J k d s * (cc • (LinearMap.id : End ℂ (Vacuum k))) = cc • J k d s := by
  rw [mul_smul_comm,
    show (LinearMap.id : End ℂ (Vacuum k)) = 1 from rfl, mul_one]

/-- Multiplication by a scalar identity on the left scales the current operator; it introduces no commutator term. -/
theorem smul_id_mul_J (k : ℂ) (d : Fin 8) (s : ℤ) (cc : ℂ) :
    (cc • (LinearMap.id : End ℂ (Vacuum k))) * J k d s = cc • J k d s := by
  rw [smul_mul_assoc,
    show (LinearMap.id : End ℂ (Vacuum k)) = 1 from rfl, one_mul]

/-- The Leibniz identity for the bracket of an ordered product `XY` against `Z`. -/
theorem leibniz_bracket {k : ℂ} (X Y Z : End ℂ (Vacuum k)) :
    (X * Y) * Z - Z * (X * Y)
      = X * (Y * Z - Z * Y) + (X * Z - Z * X) * Y := by
  rw [mul_sub, sub_mul, mul_assoc, ← mul_assoc Z X Y, mul_assoc X Z Y]; abel

/-- **The per-pair ordered-product Leibniz bracket.**
`[J^{aa}_r J^{bb}_p , J^c_μ]` expanded by Leibniz, with `current_comm` substituted into each
elementary bracket. -/
theorem ordered_bracket (k : ℂ) (aa bb c : Fin 8) (r p μ : ℤ) :
    (J k aa r * J k bb p) * J k c μ - J k c μ * (J k aa r * J k bb p)
      = J k aa r * ((∑ d, structureConstant bb c d • J k d (p + μ))
            + (if p + μ = 0 then ((p : ℂ) * k * formTable bb c) • LinearMap.id else 0))
        + ((∑ d, structureConstant aa c d • J k d (r + μ))
            + (if r + μ = 0 then ((r : ℂ) * k * formTable aa c) • LinearMap.id else 0)) * J k bb p
    := by
  rw [leibniz_bracket, J_bracket k bb c p μ, J_bracket k aa c r μ]

/-! ## Structure-constant `Fin 8` identities (the Casimir / dual-Coxeter algebra) -/

/-- The inverse trace tensor raises the first structure index. -/
noncomputable def graised (a c d : Fin 8) : ℂ := ∑ b, kappaInv a b * structureConstant b c d

/-- `g` is **antisymmetric under `a ↔ d`**: `g(a,c,d) = - g(d,c,a)` (the source of the
dual-Coxeter cancellation), by actual trace invariance. -/
theorem graised_antisymm (a c d : Fin 8) : graised a c d = - graised d c a := by
  exact VOA.AffineSl3.graised_antisymm a c d

/-- The **adjoint Casimir is `2 h^∨ δ`** (`h^∨ = 3`): `∑_{a,b,d} κ⁻¹(a,b) f(a,c,d) f(b,d,e) = 6 δ_{c,e}`. -/
theorem casimir_adjoint (c e : Fin 8) :
    (∑ a, ∑ b, ∑ d, kappaInv a b * structureConstant a c d * structureConstant b d e) = if c = e then 6 else 0 := by
  rw [← VOA.AffineSl3.struct_casimir_contract c e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  rw [kappaInv_symm d b]

/-- The central-collapse identity: `∑_b κ⁻¹(a,b) κ(b,c) = δ_{a,c}` (κ⁻¹ inverts κ on the right). -/
theorem kappaInv_kappa_right (a c : Fin 8) :
    (∑ b, kappaInv a b * formTable b c) = if a = c then 1 else 0 := by
  have h := kappaInv_kappa c a
  rw [show (∑ b, formTable c b * kappaInv b a) = ∑ b, kappaInv a b * formTable b c from by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [kappa_symm c b, kappaInv_symm b a]; ring] at h
  rw [h]; by_cases hac : a = c <;> simp [hac, eq_comm]

/-- `∑_{aa,bb} κ⁻¹(aa,bb) f(aa,bb,d) = 0`: κ⁻¹ symmetric contracted with `f` antisymmetric in
the first two indices, by symmetry and bracket antisymmetry. -/
theorem kappaInv_structureConstant_antisymm_zero (d : Fin 8) :
    (∑ aa, ∑ bb, kappaInv aa bb * structureConstant aa bb d) = 0 := by
  exact VOA.AffineSl3.kappaInv_fabc_antisymm_zero d

/-! ## The swap lemma: normal ordering is irrelevant after the `κ⁻¹` symmetrisation -/

/-- The per-pair operator bracket of the normal-ordered `sugTermJ` against `J^c_μ` equals the
ordered bracket plus a `p<0` correction `-∑_d f(aa,bb,d)[J^d_{-1},J^c_μ]`. -/
theorem sugTermJ_bracket_eq_ordered (k : ℂ) (aa bb c : Fin 8) (p μ : ℤ) :
    sugTermJ k aa bb p * J k c μ - J k c μ * sugTermJ k aa bb p
      = ((J k aa (-p - 1) * J k bb p) * J k c μ - J k c μ * (J k aa (-p - 1) * J k bb p))
        - (if p < 0 then
            ∑ d, structureConstant aa bb d • (J k d (-1) * J k c μ - J k c μ * J k d (-1)) else 0) := by
  rw [sugTermJ]
  by_cases hp : 0 ≤ p
  · rw [if_pos hp, if_neg (by omega : ¬ p < 0), sub_zero]
  · rw [if_neg hp, if_pos (by omega : p < 0)]
    -- swapped product: J^{bb}_p J^{aa}_{-p-1} = J^{aa}_{-p-1}J^{bb}_p - [J^{aa}_{-p-1},J^{bb}_p]
    have hsw : J k bb p * J k aa (-p - 1)
        = J k aa (-p - 1) * J k bb p - (∑ d, structureConstant aa bb d • J k d (-1)) := by
      have hb := J_bracket k aa bb (-p - 1) p
      rw [if_neg (by omega : ¬ -p - 1 + p = 0), add_zero,
        show (-p - 1 + p : ℤ) = -1 from by ring] at hb
      -- hb : J^{aa}_{-p-1}J^{bb}_p - J^{bb}_p J^{aa}_{-p-1} = ∑_d f(aa,bb,d)J^d_{-1}
      rw [eq_sub_iff_add_eq, ← hb]; abel
    rw [hsw]
    -- expand brackets
    rw [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum]
    rw [show (∑ d, structureConstant aa bb d • (J k d (-1) * J k c μ - J k c μ * J k d (-1)))
        = (∑ i, structureConstant aa bb i • J k i (-1) * J k c μ)
          - ∑ i, J k c μ * structureConstant aa bb i • J k i (-1) from by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, smul_sub]]
    abel

/-- **The swap lemma (`κ⁻¹`-weighted): normal ordering is irrelevant.**
`∑_{aa,bb} κ⁻¹(aa,bb) [sugTermJ aa bb p, J^c_μ] = ∑_{aa,bb} κ⁻¹(aa,bb) [J^{aa}_{-p-1}J^{bb}_p, J^c_μ]`
(ordered).  The `p<0` correction `-∑_d (∑_{aa,bb} κ⁻¹ f(aa,bb,d))[J^d_{-1},J^c_μ]` vanishes
since `∑_{aa,bb} κ⁻¹(aa,bb) f(aa,bb,d) = 0`. -/
theorem swap_sum (k : ℂ) (c : Fin 8) (p μ : ℤ) :
    (∑ aa, ∑ bb, kappaInv aa bb •
        (sugTermJ k aa bb p * J k c μ - J k c μ * sugTermJ k aa bb p))
      = ∑ aa, ∑ bb, kappaInv aa bb •
          ((J k aa (-p - 1) * J k bb p) * J k c μ
            - J k c μ * (J k aa (-p - 1) * J k bb p)) := by
  -- substitute the per-pair identity, splitting off the correction
  have hstep : (∑ aa, ∑ bb, kappaInv aa bb •
        (sugTermJ k aa bb p * J k c μ - J k c μ * sugTermJ k aa bb p))
      = (∑ aa, ∑ bb, kappaInv aa bb •
          ((J k aa (-p - 1) * J k bb p) * J k c μ
            - J k c μ * (J k aa (-p - 1) * J k bb p)))
        - (∑ aa, ∑ bb, kappaInv aa bb • (if p < 0 then
              ∑ d, structureConstant aa bb d • (J k d (-1) * J k c μ - J k c μ * J k d (-1)) else 0)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun aa _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun bb _ => ?_
    rw [sugTermJ_bracket_eq_ordered, smul_sub]
  rw [hstep]
  -- the correction double-sum vanishes
  rw [show (∑ aa, ∑ bb, kappaInv aa bb • (if p < 0 then
        ∑ d, structureConstant aa bb d • (J k d (-1) * J k c μ - J k c μ * J k d (-1)) else 0))
      = (0 : End ℂ (Vacuum k)) from ?_, sub_zero]
  by_cases hp : p < 0
  · -- pull the `if`, reorder sums, factor the vanishing structure-constant contraction
    simp only [if_pos hp]
    set W : Fin 8 → End ℂ (Vacuum k) :=
      fun d => J k d (-1) * J k c μ - J k c μ * J k d (-1) with hW
    -- κ⁻¹ aa bb • ∑_d structureConstant • W = ∑_d (κ⁻¹·structureConstant) • W
    have hinner : ∀ aa bb : Fin 8,
        kappaInv aa bb • ∑ d, structureConstant aa bb d • W d
          = ∑ d, (kappaInv aa bb * structureConstant aa bb d) • W d := by
      intro aa bb
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [smul_smul]
    rw [show (∑ aa, ∑ bb, kappaInv aa bb • ∑ d, structureConstant aa bb d • W d)
        = ∑ d, (∑ aa, ∑ bb, kappaInv aa bb * structureConstant aa bb d) • W d from by
      rw [show (∑ d, (∑ aa, ∑ bb, kappaInv aa bb * structureConstant aa bb d) • W d)
          = ∑ d, ∑ aa, ∑ bb, (kappaInv aa bb * structureConstant aa bb d) • W d from by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_smul]; refine Finset.sum_congr rfl fun aa _ => ?_; rw [Finset.sum_smul]]
      -- now both sides are triple sums; reorder ∑aa∑bb∑d ↔ ∑d∑aa∑bb
      rw [Finset.sum_comm (f := fun d aa => ∑ bb, (kappaInv aa bb * structureConstant aa bb d) • W d)]
      refine Finset.sum_congr rfl fun aa _ => ?_
      rw [Finset.sum_comm (f := fun d bb => (kappaInv aa bb * structureConstant aa bb d) • W d)]
      refine Finset.sum_congr rfl fun bb _ => ?_
      exact (hinner aa bb).trans (by refine Finset.sum_congr rfl fun d _ => rfl)]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [kappaInv_structureConstant_antisymm_zero, zero_smul]
  · simp only [if_neg hp, smul_zero, Finset.sum_const_zero]

/-! ## Reducing `[L₋₁, J^c_μ]` to a single finite finsum -/

/-- The κ⁻¹-weighted per-`p` ordered bracket, the summand of `[L₋₁, J^c_μ]`. -/
noncomputable def Hbr (k : ℂ) (c : Fin 8) (μ p : ℤ) : End ℂ (Vacuum k) :=
  ∑ aa, ∑ bb, kappaInv aa bb •
    ((J k aa (-p - 1) * J k bb p) * J k c μ - J k c μ * (J k aa (-p - 1) * J k bb p))

/-- `Hbr` summand acting on `x`, with the scalar/application pushed inside. -/
theorem Hbr_apply (k : ℂ) (c : Fin 8) (μ p : ℤ) (x : Vacuum k) :
    Hbr k c μ p x
      = (∑ aa, ∑ bb, kappaInv aa bb •
          ((J k aa (-p - 1) * J k bb p) * J k c μ
            - J k c μ * (J k aa (-p - 1) * J k bb p))) x := rfl

/-- `∑_{aa,bb} κ⁻¹ • sugTermJ` acting on `x` equals `(c₀⁻¹)·(L₋₁-piece)`: the `p`-summand of
`Ltrans_apply` rewritten per-`p`. -/
theorem Ltrans_apply_finsum (k : ℂ) (x : Vacuum k) :
    Ltrans k x = c0 k • ∑ᶠ p : ℤ,
      (∑ aa, ∑ bb, kappaInv aa bb • sugTermJ k aa bb p x) := by
  rw [Ltrans_apply]
  congr 1
  -- pull each scalar `κ⁻¹` inside the finsum
  have hpull : (∑ aa : Fin 8, ∑ bb : Fin 8, kappaInv aa bb • ∑ᶠ p : ℤ, sugTermJ k aa bb p x)
      = ∑ aa : Fin 8, ∑ bb : Fin 8, ∑ᶠ p : ℤ, kappaInv aa bb • sugTermJ k aa bb p x := by
    refine Finset.sum_congr rfl fun aa _ => Finset.sum_congr rfl fun bb _ => ?_
    rw [smul_finsum' (kappaInv aa bb) (sugTermJ_support_finite k aa bb x)]
  rw [hpull]
  -- each `κ⁻¹•sugTermJ..x` is finitely supported in `p`
  have hfin : ∀ aa bb : Fin 8,
      (Function.support (fun p : ℤ => kappaInv aa bb • sugTermJ k aa bb p x)).Finite := by
    intro aa bb
    apply (sugTermJ_support_finite k aa bb x).subset
    intro p hp; rw [Function.mem_support] at hp ⊢
    exact fun h => hp (by rw [h, smul_zero])
  -- commute ∑bb past ∑ᶠp, then ∑aa past ∑ᶠp
  rw [show (∑ aa : Fin 8, ∑ bb : Fin 8, ∑ᶠ p : ℤ, kappaInv aa bb • sugTermJ k aa bb p x)
      = ∑ aa : Fin 8, ∑ᶠ p : ℤ, ∑ bb : Fin 8, kappaInv aa bb • sugTermJ k aa bb p x from by
    refine Finset.sum_congr rfl fun aa _ => ?_
    rw [sum_finsum_comm Finset.univ
      (fun bb p => kappaInv aa bb • sugTermJ k aa bb p x) (fun bb _ => hfin aa bb)]]
  rw [sum_finsum_comm Finset.univ
    (fun aa p => ∑ bb : Fin 8, kappaInv aa bb • sugTermJ k aa bb p x)
    (fun aa _ => by
      apply Set.Finite.subset ((Finset.univ : Finset (Fin 8)).finite_toSet.biUnion
        (fun bb _ => hfin aa bb))
      intro p hp; rw [Function.mem_support] at hp
      simp only [Set.mem_iUnion]
      by_contra hcon
      push_neg at hcon
      apply hp
      refine Finset.sum_eq_zero fun bb _ => ?_
      have := hcon bb (Finset.mem_coe.mpr (Finset.mem_univ bb))
      rwa [Function.mem_support, not_not] at this)]

/-- The κ⁻¹-summed `sugTermJ` operator (the `L₋₁` summand operator, pre-`x`). -/
noncomputable def Lsum (k : ℂ) (p : ℤ) : End ℂ (Vacuum k) :=
  ∑ aa, ∑ bb, kappaInv aa bb • sugTermJ k aa bb p

/-- The inverse-form contraction of the ordered current products acts by the same finite double sum on a vacuum vector. -/
theorem Lsum_apply (k : ℂ) (p : ℤ) (x : Vacuum k) :
    Lsum k p x = ∑ aa, ∑ bb, kappaInv aa bb • sugTermJ k aa bb p x := by
  rw [Lsum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun aa _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun bb _ => ?_
  rw [LinearMap.smul_apply]

/-- For each vector only finitely many normal-ordering indices contribute to the contracted translation sum. This licenses its algebraic sum. -/
theorem Lsum_support_finite (k : ℂ) (x : Vacuum k) :
    (Function.support (fun p : ℤ => Lsum k p x)).Finite := by
  apply Set.Finite.subset ((Finset.univ : Finset (Fin 8)).finite_toSet.biUnion
    (fun aa _ => (Finset.univ : Finset (Fin 8)).finite_toSet.biUnion
      (fun bb _ => sugTermJ_support_finite k aa bb x)))
  intro p hp; rw [Function.mem_support, Lsum_apply] at hp
  simp only [Set.mem_iUnion]
  by_contra hcon; push_neg at hcon; apply hp
  refine Finset.sum_eq_zero fun aa _ => Finset.sum_eq_zero fun bb _ => ?_
  have := hcon aa (Finset.mem_coe.mpr (Finset.mem_univ aa)) bb
    (Finset.mem_coe.mpr (Finset.mem_univ bb))
  rw [Function.mem_support, not_not] at this
  rw [this, smul_zero]

/-- `Ltrans k x = c₀ • ∑ᶠ_p Lsum k p x`. -/
theorem Ltrans_eq_finsum_Lsum (k : ℂ) (x : Vacuum k) :
    Ltrans k x = c0 k • ∑ᶠ p : ℤ, Lsum k p x := by
  rw [Ltrans_apply_finsum]
  refine congrArg (c0 k • ·) (finsum_congr fun p => (Lsum_apply k p x).symm)

/-- The per-`p` commutator of `Lsum` against `J^c_μ` equals `Hbr` (via `swap_sum`):
`Lsum p · J^c_μ - J^c_μ · Lsum p = Hbr`. -/
theorem Lsum_comm_eq_Hbr (k : ℂ) (c : Fin 8) (μ p : ℤ) :
    Lsum k p * J k c μ - J k c μ * Lsum k p = Hbr k c μ p := by
  rw [Lsum, Hbr]
  -- distribute the multiplication through the double finset-sum
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hdist : ∀ aa : Fin 8,
      (∑ bb, kappaInv aa bb • sugTermJ k aa bb p) * J k c μ
        - J k c μ * ∑ bb, kappaInv aa bb • sugTermJ k aa bb p
      = ∑ bb, kappaInv aa bb •
          (sugTermJ k aa bb p * J k c μ - J k c μ * sugTermJ k aa bb p) := by
    intro aa
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun bb _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [Finset.sum_congr rfl (fun aa _ => hdist aa)]
  exact swap_sum k c p μ

/-- The current commutator of the translation summands has finite support on each vector, by the two corresponding truncation bounds. -/
theorem Hbr_support_finite (k : ℂ) (c : Fin 8) (μ : ℤ) (x : Vacuum k) :
    (Function.support (fun p : ℤ => Hbr k c μ p x)).Finite := by
  -- Hbr p x = Lsum p (J^c x) - J^c (Lsum p x); both have finite support in p.
  apply Set.Finite.subset
    ((Lsum_support_finite k (J k c μ x)).union (Lsum_support_finite k x))
  intro p hp; rw [Function.mem_support] at hp
  simp only [Set.mem_union, Function.mem_support]
  by_contra hcon; push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply hp
  have hval : Hbr k c μ p x = Lsum k p (J k c μ x) - J k c μ (Lsum k p x) := by
    have := Lsum_comm_eq_Hbr k c μ p
    have happ := congrArg (fun (T : End ℂ (Vacuum k)) => T x) this
    simpa only [LinearMap.sub_apply, Module.End.mul_apply] using happ.symm
  rw [hval, h1, h2, map_zero, sub_zero]

/-- **The full commutator as a single finsum of `Hbr`.**
`(L₋₁·J^c_μ - J^c_μ·L₋₁) x = c₀ • ∑ᶠ_p Hbr p x`. -/
theorem Lcomm_eq_finsum_Hbr (k : ℂ) (c : Fin 8) (μ : ℤ) (x : Vacuum k) :
    (Ltrans k * J k c μ - J k c μ * Ltrans k) x
      = c0 k • ∑ᶠ p : ℤ, Hbr k c μ p x := by
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    Ltrans_eq_finsum_Lsum k (J k c μ x), Ltrans_eq_finsum_Lsum k x]
  rw [map_smul, map_finsum (J k c μ) (Lsum_support_finite k x), ← smul_sub]
  congr 1
  rw [← finsum_sub_distrib (Lsum_support_finite k (J k c μ x))
      ((Lsum_support_finite k x).subset (fun p hp => by
        rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, map_zero])))]
  refine finsum_congr fun p => ?_
  have := Lsum_comm_eq_Hbr k c μ p
  have happ := congrArg (fun (T : End ℂ (Vacuum k)) => T x) this
  simpa only [LinearMap.sub_apply, Module.End.mul_apply] using happ

/-! ## The finite collapse of `∑ᶠ_p Hbr` and the main theorem -/

/-- `Hbr` in the gated `sugTermJ` form (the reverse of `swap_sum`). -/
theorem Hbr_eq_sugTermJ_bracket (k : ℂ) (c : Fin 8) (μ p : ℤ) :
    Hbr k c μ p
      = ∑ aa, ∑ bb, kappaInv aa bb •
          (sugTermJ k aa bb p * J k c μ - J k c μ * sugTermJ k aa bb p) := by
  rw [Hbr, swap_sum]

/-- The per-pair bracket `[sugTermJ aa bb p, J^c_μ]` acting on `x`, finitely supported in `p`
(the gate keeps both bilinear pieces lower-truncated). -/
theorem pair_bracket_support_finite (k : ℂ) (aa bb c : Fin 8) (μ : ℤ) (x : Vacuum k) :
    (Function.support (fun p : ℤ =>
      sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x))).Finite := by
  apply Set.Finite.subset
    ((sugTermJ_support_finite k aa bb (J k c μ x)).union (sugTermJ_support_finite k aa bb x))
  intro p hp; rw [Function.mem_support] at hp
  simp only [Set.mem_union, Function.mem_support]
  by_contra hcon; push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact hp (by rw [h1, h2, map_zero, sub_zero])


/-! ## Ported per-pair split machinery (the `sugTermJ`-ordered `structOp`/`centralOp` route)

The `close1` ordered form (`Hbr`) is convenient for the algebra, but for the per-half finiteness
of `∑ᶠ_p` we keep the *normal-ordered* (`if 0 ≤ p`) split, exactly the structure of the sibling
development: each per-pair bracket body `sugTermJ p (J^c x) − J^c (sugTermJ p x)` splits as
`−(structPart + centralPart)`, both finitely supported in `p`. -/

/-- Leibniz for `[J^c_μ, (J^a_r · J^b_s)]` (single current vs ordered product). -/
theorem leibniz_bracket_S (k : ℂ) (c a b : Fin 8) (μ r s : ℤ) :
    J k c μ * (J k a r * J k b s) - (J k a r * J k b s) * J k c μ
      = (J k c μ * J k a r - J k a r * J k c μ) * J k b s
        + J k a r * (J k c μ * J k b s - J k b s * J k c μ) := by
  rw [sub_mul, mul_sub, ← mul_assoc, ← mul_assoc]; abel

/-- The per-pair operator bracket `[J^c_μ, J^a_r J^b_s]` with both `current_comm`'s substituted. -/
theorem pair_bracket_S (k : ℂ) (c a b : Fin 8) (μ r s : ℤ) :
    J k c μ * (J k a r * J k b s) - (J k a r * J k b s) * J k c μ
      = ((∑ d, structureConstant c a d • J k d (μ + r))
            + (if μ + r = 0 then ((μ : ℂ) * k * formTable c a) • LinearMap.id else 0)) * J k b s
        + J k a r * ((∑ d, structureConstant c b d • J k d (μ + s))
            + (if μ + s = 0 then ((μ : ℂ) * k * formTable c b) • LinearMap.id else 0)) := by
  rw [leibniz_bracket_S, current_comm, current_comm]

/-- Bracket of `J^c_μ` with the OTHER ordering `J^b_p · J^a_{-p-1}` (used for `p < 0`). -/
theorem pair_bracket_S' (k : ℂ) (c a b : Fin 8) (μ p : ℤ) :
    J k c μ * (J k b p * J k a (-p - 1)) - (J k b p * J k a (-p - 1)) * J k c μ
      = ((∑ d, structureConstant c b d • J k d (μ + p))
            + (if μ + p = 0 then ((μ : ℂ) * k * formTable c b) • LinearMap.id else 0)) * J k a (-p - 1)
        + J k b p * ((∑ d, structureConstant c a d • J k d (μ + (-p - 1)))
            + (if μ + (-p - 1) = 0 then ((μ : ℂ) * k * formTable c a) • LinearMap.id else 0)) := by
  rw [leibniz_bracket_S, current_comm, current_comm]

/-- Casimir / central contraction: `Σ_a κ(c,a) κ⁻¹(a,b) = δ_{c,b}`. -/
theorem kappa_kappaInv_S (c b : Fin 8) :
    (∑ a, formTable c a * kappaInv a b) = if c = b then 1 else 0 := by
  exact kappaInv_kappa c b

/-- Adjoint Casimir / dual Coxeter: `Σ_{a,b,d} κ⁻¹(a,b) f^{ca}_d f^{db}_e = 6 δ_{c,e}`. -/
theorem adjoint_casimir_S (c e : Fin 8) :
    (∑ a, ∑ b, ∑ d, kappaInv a b * (structureConstant c a d * structureConstant d b e))
      = if c = e then (6 : ℂ) else 0 := by
  rw [← casimir_adjoint c e]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  rw [structureConstant_antisymm c a d,structureConstant_antisymm d b e]
  ring

/-- The inner body equals `-[J^c_μ, sugTermJ aa bb p] x` in the fixed `sugTermJ` ordering. -/
theorem inner_body_eq_S (k : ℂ) (c aa bb : Fin 8) (μ p : ℤ) (x : Vacuum k) :
    sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x)
      = - ((if 0 ≤ p
            then (J k c μ * (J k aa (-p-1) * J k bb p) - (J k aa (-p-1) * J k bb p) * J k c μ)
            else (J k c μ * (J k bb p * J k aa (-p-1)) - (J k bb p * J k aa (-p-1)) * J k c μ)) x) := by
  rw [sugTermJ]
  by_cases hp : 0 ≤ p
  · rw [if_pos hp, if_pos hp]
    have happ := congrArg (fun (R : End ℂ (Vacuum k)) => R x)
      (show (J k aa (-p-1) * J k bb p) * J k c μ - J k c μ * (J k aa (-p-1) * J k bb p)
        = -(J k c μ * (J k aa (-p-1) * J k bb p) - (J k aa (-p-1) * J k bb p) * J k c μ) from by abel)
    simpa only [LinearMap.sub_apply, LinearMap.neg_apply, Module.End.mul_apply] using happ
  · rw [if_neg hp, if_neg hp]
    have happ := congrArg (fun (R : End ℂ (Vacuum k)) => R x)
      (show (J k bb p * J k aa (-p-1)) * J k c μ - J k c μ * (J k bb p * J k aa (-p-1))
        = -(J k c μ * (J k bb p * J k aa (-p-1)) - (J k bb p * J k aa (-p-1)) * J k c μ) from by abel)
    simpa only [LinearMap.sub_apply, LinearMap.neg_apply, Module.End.mul_apply] using happ

/-- The structure-constant operator-part of `[J^c_μ, sugTermJ aa bb p]`. -/
noncomputable def structOp (k : ℂ) (c aa bb : Fin 8) (μ p : ℤ) : End ℂ (Vacuum k) :=
  if 0 ≤ p
    then (∑ d, structureConstant c aa d • J k d (μ + (-p - 1))) * J k bb p
            + J k aa (-p - 1) * (∑ d, structureConstant c bb d • J k d (μ + p))
    else (∑ d, structureConstant c bb d • J k d (μ + p)) * J k aa (-p - 1)
            + J k bb p * (∑ d, structureConstant c aa d • J k d (μ + (-p - 1)))

/-- The central operator-part of `[J^c_μ, sugTermJ aa bb p]`. -/
noncomputable def centralOp (k : ℂ) (c aa bb : Fin 8) (μ p : ℤ) : End ℂ (Vacuum k) :=
  if 0 ≤ p
    then (if μ + (-p-1) = 0 then ((μ : ℂ) * k * formTable c aa) • LinearMap.id else 0) * J k bb p
            + J k aa (-p-1) * (if μ + p = 0 then ((μ : ℂ) * k * formTable c bb) • LinearMap.id else 0)
    else (if μ + p = 0 then ((μ : ℂ) * k * formTable c bb) • LinearMap.id else 0) * J k aa (-p-1)
            + J k bb p * (if μ + (-p-1) = 0 then ((μ : ℂ) * k * formTable c aa) • LinearMap.id else 0)

/-- Structure-constant part applied to `x`. -/
noncomputable def structPart (k : ℂ) (c aa bb : Fin 8) (μ p : ℤ) (x : Vacuum k) : Vacuum k :=
  structOp k c aa bb μ p x

/-- Central part applied to `x`. -/
noncomputable def centralPart (k : ℂ) (c aa bb : Fin 8) (μ p : ℤ) (x : Vacuum k) : Vacuum k :=
  centralOp k c aa bb μ p x

/-- The inner body splits as `-(structPart + centralPart)`. -/
theorem inner_body_split (k : ℂ) (c aa bb : Fin 8) (μ p : ℤ) (x : Vacuum k) :
    sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x)
      = - (structPart k c aa bb μ p x + centralPart k c aa bb μ p x) := by
  rw [inner_body_eq_S, structPart, centralPart, structOp, centralOp]
  congr 1
  by_cases hp : 0 ≤ p
  · rw [if_pos hp, if_pos hp, if_pos hp, pair_bracket_S]
    rw [add_mul, mul_add]
    simp only [LinearMap.add_apply]
    abel
  · rw [if_neg hp, if_neg hp, if_neg hp, pair_bracket_S']
    rw [add_mul, mul_add]
    simp only [LinearMap.add_apply]
    abel

/-- `centralPart` away from `{μ-1, -μ}` vanishes. -/
theorem centralPart_off (k : ℂ) (c aa bb : Fin 8) (μ p : ℤ) (x : Vacuum k)
    (h1 : p ≠ μ - 1) (h2 : p ≠ -μ) : centralPart k c aa bb μ p x = 0 := by
  rw [centralPart, centralOp]
  by_cases hp0 : 0 ≤ p
  · rw [if_pos hp0, if_neg (by omega : ¬ μ + (-p-1) = 0), if_neg (by omega : ¬ μ + p = 0)]
    simp
  · rw [if_neg hp0, if_neg (by omega : ¬ μ + p = 0), if_neg (by omega : ¬ μ + (-p-1) = 0)]
    simp

/-- `centralPart` at `p = μ-1`. -/
theorem centralPart_at_mu1 (k : ℂ) (c aa bb : Fin 8) (μ : ℤ) (x : Vacuum k) :
    centralPart k c aa bb μ (μ - 1) x = ((μ : ℂ) * k * formTable c aa) • (J k bb (μ - 1) x) := by
  rw [centralPart, centralOp]
  by_cases hp0 : 0 ≤ μ - 1
  · rw [if_pos hp0, if_pos (by omega : μ + (-(μ-1)-1) = 0),
        if_neg (by omega : ¬ μ + (μ-1) = 0)]
    simp only [mul_zero, add_zero, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.zero_apply, LinearMap.smul_apply, LinearMap.id_apply, map_zero]
  · rw [if_neg hp0, if_neg (by omega : ¬ μ + (μ-1) = 0),
        if_pos (by omega : μ + (-(μ-1)-1) = 0)]
    rw [show (-(μ-1)-1 : ℤ) = -μ from by ring]
    simp only [zero_mul, zero_add, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.zero_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul]

/-- `centralPart` at `p = -μ`. -/
theorem centralPart_at_negmu (k : ℂ) (c aa bb : Fin 8) (μ : ℤ) (x : Vacuum k) :
    centralPart k c aa bb μ (-μ) x = ((μ : ℂ) * k * formTable c bb) • (J k aa (μ - 1) x) := by
  rw [centralPart, centralOp]
  by_cases hp0 : 0 ≤ -μ
  · rw [if_pos hp0, if_neg (by omega : ¬ μ + (-(-μ)-1) = 0), if_pos (by omega : μ + (-μ) = 0)]
    rw [show (-(-μ)-1 : ℤ) = μ - 1 from by ring]
    simp only [zero_mul, zero_add, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.zero_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  · rw [if_neg hp0, if_pos (by omega : μ + (-μ) = 0), if_neg (by omega : ¬ μ + (-(-μ)-1) = 0)]
    rw [show (-(-μ)-1 : ℤ) = μ - 1 from by ring]
    simp only [mul_zero, add_zero, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.zero_apply, LinearMap.smul_apply, LinearMap.id_apply, map_zero]

/-- The central contribution is supported at the finitely many mode indices where the affine cocycle can be nonzero. -/
theorem centralPart_support_finite (k : ℂ) (c aa bb : Fin 8) (μ : ℤ) (x : Vacuum k) :
    (Function.support (fun p : ℤ => centralPart k c aa bb μ p x)).Finite := by
  apply Set.Finite.subset (Set.toFinite ({μ - 1, -μ} : Finset ℤ))
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hpc
  apply hp
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hpc
  exact centralPart_off k c aa bb μ p x hpc.1 hpc.2

/-- The central finsum collapses (δ-gate) to the two-point central residue body. -/
theorem centralPart_finsum_collapse (k : ℂ) (c aa bb : Fin 8) (μ : ℤ) (x : Vacuum k) :
    (∑ᶠ p : ℤ, centralPart k c aa bb μ p x)
      = ((μ : ℂ) * k * formTable c aa) • (J k bb (μ - 1) x)
        + ((μ : ℂ) * k * formTable c bb) • (J k aa (μ - 1) x) := by
  classical
  rw [finsum_eq_finsetSum_of_support_subset _ (s := ({μ - 1, -μ} : Finset ℤ)) (by
    intro p hp
    rw [Function.mem_support] at hp
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hpc
    rw [not_or] at hpc
    exact hp (centralPart_off k c aa bb μ p x hpc.1 hpc.2))]
  rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
      Finset.sum_singleton, centralPart_at_mu1, centralPart_at_negmu]

/-- Raw central residue (no `c0`): `Σ_{aa,bb} κ⁻¹ Σᶠ_p centralPart = 2μk • J^c_{μ-1} x`. -/
theorem central_residue_raw (k : ℂ) (c : Fin 8) (μ : ℤ) (x : Vacuum k) :
    (∑ aa : Fin 8, ∑ bb : Fin 8, kappaInv aa bb • ∑ᶠ p : ℤ, centralPart k c aa bb μ p x)
      = (2 * μ * k : ℂ) • J k c (μ - 1) x := by
  rw [show (∑ aa : Fin 8, ∑ bb : Fin 8, kappaInv aa bb • ∑ᶠ p : ℤ, centralPart k c aa bb μ p x)
        = ∑ aa : Fin 8, ∑ bb : Fin 8, kappaInv aa bb •
            (((μ : ℂ) * k * formTable c aa) • (J k bb (μ - 1) x)
              + ((μ : ℂ) * k * formTable c bb) • (J k aa (μ - 1) x))
      from Finset.sum_congr rfl fun aa _ => Finset.sum_congr rfl fun bb _ => by
        rw [centralPart_finsum_collapse]]
  have hbody : ∀ aa bb : Fin 8,
      kappaInv aa bb • (((μ : ℂ) * k * formTable c aa) • (J k bb (μ - 1) x)
          + ((μ : ℂ) * k * formTable c bb) • (J k aa (μ - 1) x))
        = (kappaInv aa bb * ((μ : ℂ) * k * formTable c aa)) • (J k bb (μ - 1) x)
          + (kappaInv aa bb * ((μ : ℂ) * k * formTable c bb)) • (J k aa (μ - 1) x) :=
    fun aa bb => by rw [smul_add, smul_smul, smul_smul]
  simp only [hbody]
  rw [show (∑ aa : Fin 8, ∑ bb : Fin 8,
        ((kappaInv aa bb * ((μ : ℂ) * k * formTable c aa)) • (J k bb (μ - 1) x)
          + (kappaInv aa bb * ((μ : ℂ) * k * formTable c bb)) • (J k aa (μ - 1) x)))
      = (∑ aa : Fin 8, ∑ bb : Fin 8, (kappaInv aa bb * ((μ : ℂ) * k * formTable c aa)) • (J k bb (μ - 1) x))
        + (∑ aa : Fin 8, ∑ bb : Fin 8, (kappaInv aa bb * ((μ : ℂ) * k * formTable c bb)) • (J k aa (μ - 1) x))
      from by rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun aa _ => ?_;
              rw [← Finset.sum_add_distrib]]
  have hT1 : (∑ aa : Fin 8, ∑ bb : Fin 8,
        (kappaInv aa bb * ((μ : ℂ) * k * formTable c aa)) • (J k bb (μ - 1) x))
      = ((μ : ℂ) * k) • J k c (μ - 1) x := by
    rw [Finset.sum_comm]
    rw [show (∑ bb : Fin 8, ∑ aa : Fin 8,
          (kappaInv aa bb * ((μ : ℂ) * k * formTable c aa)) • (J k bb (μ - 1) x))
        = ∑ bb : Fin 8, ((∑ aa : Fin 8, formTable c aa * kappaInv aa bb) * ((μ : ℂ) * k))
              • (J k bb (μ - 1) x)
        from Finset.sum_congr rfl fun bb _ => by
          rw [← Finset.sum_smul, Finset.sum_mul]; congr 1;
          refine Finset.sum_congr rfl fun aa _ => ?_; ring]
    rw [show (∑ bb : Fin 8, ((∑ aa : Fin 8, formTable c aa * kappaInv aa bb) * ((μ : ℂ) * k))
              • (J k bb (μ - 1) x))
        = ∑ bb : Fin 8, ((if c = bb then (1:ℂ) else 0) * ((μ : ℂ) * k)) • (J k bb (μ - 1) x)
        from Finset.sum_congr rfl fun bb _ => by rw [kappa_kappaInv_S]]
    rw [Finset.sum_eq_single c (fun bb _ hbb => by rw [if_neg (Ne.symm hbb), zero_mul, zero_smul])
        (fun h => absurd (Finset.mem_univ c) h), if_pos rfl, one_mul]
  have hT2 : (∑ aa : Fin 8, ∑ bb : Fin 8,
        (kappaInv aa bb * ((μ : ℂ) * k * formTable c bb)) • (J k aa (μ - 1) x))
      = ((μ : ℂ) * k) • J k c (μ - 1) x := by
    rw [show (∑ aa : Fin 8, ∑ bb : Fin 8,
          (kappaInv aa bb * ((μ : ℂ) * k * formTable c bb)) • (J k aa (μ - 1) x))
        = ∑ aa : Fin 8, ((∑ bb : Fin 8, formTable c bb * kappaInv bb aa) * ((μ : ℂ) * k))
              • (J k aa (μ - 1) x)
        from Finset.sum_congr rfl fun aa _ => by
          rw [← Finset.sum_smul, Finset.sum_mul]; congr 1;
          refine Finset.sum_congr rfl fun bb _ => ?_; rw [kappaInv_symm aa bb]; ring]
    rw [show (∑ aa : Fin 8, ((∑ bb : Fin 8, formTable c bb * kappaInv bb aa) * ((μ : ℂ) * k))
              • (J k aa (μ - 1) x))
        = ∑ aa : Fin 8, ((if c = aa then (1:ℂ) else 0) * ((μ : ℂ) * k)) • (J k aa (μ - 1) x)
        from Finset.sum_congr rfl fun aa _ => by rw [kappa_kappaInv_S]]
    rw [Finset.sum_eq_single c (fun aa _ haa => by rw [if_neg (Ne.symm haa), zero_mul, zero_smul])
        (fun h => absurd (Finset.mem_univ c) h), if_pos rfl, one_mul]
  rw [hT1, hT2, ← smul_add, ← two_smul ℂ (J k c (μ - 1) x), smul_smul]
  congr 1
  ring

/-- Finite support of `structPart` in `p` (the normal-ordering gate truncates both factors). -/
theorem structPart_support_finite (k : ℂ) (c aa bb : Fin 8) (μ : ℤ) (x : Vacuum k) :
    (Function.support (fun p : ℤ => structPart k c aa bb μ p x)).Finite := by
  have hbody : (Function.support (fun p : ℤ =>
      sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x))).Finite :=
    pair_bracket_support_finite k aa bb c μ x
  have hcen := centralPart_support_finite k c aa bb μ x
  apply Set.Finite.subset (hbody.union hcen)
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hc
  rw [Set.mem_union] at hc
  push_neg at hc
  rw [Function.notMem_support, Function.notMem_support] at hc
  apply hp
  have hs := inner_body_split k c aa bb μ p x
  rw [hc.1, hc.2, add_zero, eq_comm, neg_eq_zero] at hs
  exact hs

/-- The finsum of the inner body splits as `−(Σᶠ struct + Σᶠ central)` (both finite). -/
theorem inner_finsum_split (k : ℂ) (c aa bb : Fin 8) (μ : ℤ) (x : Vacuum k) :
    (∑ᶠ p : ℤ, (sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x)))
      = - ((∑ᶠ p : ℤ, structPart k c aa bb μ p x) + (∑ᶠ p : ℤ, centralPart k c aa bb μ p x)) := by
  have hcen := centralPart_support_finite k c aa bb μ x
  have hstr := structPart_support_finite k c aa bb μ x
  rw [finsum_congr (fun p => inner_body_split k c aa bb μ p x)]
  rw [finsum_congr (fun p => (neg_add _ _) : ∀ p,
        -(structPart k c aa bb μ p x + centralPart k c aa bb μ p x)
          = -(structPart k c aa bb μ p x) + -(centralPart k c aa bb μ p x))]
  rw [finsum_add_distrib (hstr.subset (fun p hp => by
        rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, neg_zero])))
      (hcen.subset (fun p hp => by
        rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, neg_zero])))]
  rw [finsum_neg_distrib, finsum_neg_distrib, ← neg_add]

/-! ## The structure-constant (dual-Coxeter) residue — the single genuine obligation. -/

/-- **The residue kernel** (`sl₃` dual Coxeter `2h^∨ = 6`): the structure-constant double
contraction `∑_{a,d} (∑_b κ⁻¹(a,b) f(b,c,d)) f(a,d,e) = 6 δ_{c,e}` that produces the dual-Coxeter
coefficient when one struct-current is re-normal-ordered past the other (the second commutator).
This is the coordinate form of the actual matrix adjoint Casimir. -/
theorem struct_casimir_contract (c e : Fin 8) :
    (∑ a, ∑ d, (∑ b, kappaInv a b * structureConstant b c d) * structureConstant a d e) = if c = e then (6 : ℂ) else 0 := by
  exact VOA.AffineSl3.struct_casimir_contract c e

end VOA.AffineSl3.SugawaraCov
