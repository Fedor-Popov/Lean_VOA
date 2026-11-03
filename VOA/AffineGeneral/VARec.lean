/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Core.BorcherdsIdentity
import VOA.Core.Reconstruction
import VOA.Core.Skew
import VOA.Core.Goddard
import VOA.Core.OPE

/-!
# VA-level `n`-th product and commutator formula, parametric in a translation operator

A copy of the generic namespace `VOA.AffineVOA.Vir.VARec` from
`VOA/Examples/AffineSl2Virasoro.lean`, placed here so that the general affine construction does not
import the whole sl₂ Sugawara chain.

Given a vertex algebra `V` and an operator `Tr` with `⁅Tr, (V.Y u) s⁆ = (s+1) • (V.Y u)(s+1)` and
`Tr 𝟙 = 0`: `nth_product` (`cCoeff k [Y u, Y v] = Y(u₍ₖ₎v)`), `mode_commutator` and `smul_zero_ge`.
-/

open Module (End)

namespace VOA.AffineGeneral.VARec

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- `commL`-style bracket of a two-variable distribution with `Tr`. -/
noncomputable def commLT (Tr : End ℂ 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) : FormalDist₂ (End ℂ 𝒱) :=
  fun s t => ⁅Tr, G s t⁆

/-- Taking a coefficient of the distribution commutator means taking the
commutator of that coefficient with the supplied translation operator. -/
@[simp] theorem commLT_apply (Tr : End ℂ 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) (s t : ℤ) :
    commLT Tr G s t = ⁅Tr, G s t⁆ := rfl

/-- Multiplication by the formal variable difference commutes with taking
the translation commutator, since translation acts on operator coefficients. -/
theorem commLT_mulBySub (Tr : End ℂ 𝒱) (G : FormalDist₂ (End ℂ 𝒱)) :
    commLT Tr (mulBySub G) = mulBySub (commLT Tr G) := by
  apply FormalDist₂.ext; intro s t
  simp only [commLT_apply, mulBySub_apply, lie_sub]

/-- The same compatibility holds for every power of the variable difference.
This allows extraction of higher OPE coefficients after taking translation. -/
theorem commLT_mulBySubPow (Tr : End ℂ 𝒱) (j : ℕ) (G : FormalDist₂ (End ℂ 𝒱)) :
    commLT Tr (mulBySubPow j G) = mulBySubPow j (commLT Tr G) := by
  induction j generalizing G with
  | zero => rfl
  | succ p ih => rw [mulBySubPow_succ, LinearMap.comp_apply, commLT_mulBySub, ih,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- Translation covariance of the OPE bracket: `[Tr, [Y(u),Y(v)]] = ∂[Y(u),Y(v)]`. -/
theorem commLT_bracketDist (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1)) (u v : 𝒱) :
    commLT Tr (bracketDist (V.Y u) (V.Y v)) = deriv2 (bracketDist (V.Y u) (V.Y v)) := by
  have leib : ∀ (a b c : End ℂ 𝒱), ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := fun a b c => by
    simp only [LieRing.of_associative_ring_bracket]; noncomm_ring
  apply FormalDist₂.ext; intro s t
  simp only [commLT_apply, deriv2_apply, bracketDist_apply, lie_sub, leib, htr,
    smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

/-- The recursion `[Tr, A_m] = (m+1)•A_{m+1}` for `A = cCoeff k (bracketDist (Yu)(Yv))`. -/
theorem Tr_comm_cCoeff (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1))
    (u v : 𝒱) (k : ℕ) (m : ℤ) :
    ⁅Tr, cCoeff k (bracketDist (V.Y u) (V.Y v)) m⁆
      = (m + 1) • cCoeff k (bracketDist (V.Y u) (V.Y v)) (m + 1) := by
  show commLT Tr (mulBySubPow k (bracketDist (V.Y u) (V.Y v))) (-1) m = _
  rw [commLT_mulBySubPow, commLT_bracketDist V Tr htr, resByParts]
  rfl

/-! ### Vacuum action of the field `k`-th product -/

/-- Both products in the field commutator kill the vacuum in this coefficient
quadrant. The statement uses the package's Laurent coefficient convention. -/
theorem applyVec_bracketDist_quadrant (V : PreVertexAlgebra 𝒱) (u v : 𝒱) (s t : ℤ)
    (hs : s ≤ -1) (ht : t ≤ -1) :
    applyVec V.vacuum (bracketDist (V.Y u) (V.Y v)) s t = 0 := by
  rw [applyVec_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, PreVertexAlgebra.Y_apply_vacuum_eq_zero V v (by omega),
    PreVertexAlgebra.Y_apply_vacuum_eq_zero V u (by omega), map_zero, map_zero, sub_zero]

/-- Extracting an OPE coefficient and applying it to the vacuum can be done
in either order. The right side is a vector-valued distribution calculation. -/
theorem cCoeff_apply_vacuum (V : PreVertexAlgebra 𝒱) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDist (V.Y u) (V.Y v)) m V.vacuum
      = mulBySubPow k (applyVec V.vacuum (bracketDist (V.Y u) (V.Y v))) (-1) m := by
  show mulBySubPow k (bracketDist (V.Y u) (V.Y v)) (-1) m V.vacuum = _
  rw [← applyVec_apply, applyVec_mulBySubPow]

/-- The extracted OPE coefficient field has no negative Laurent powers on
the vacuum. This is the regularity part of the creation condition. -/
theorem cCoeff_vacuum_neg (V : PreVertexAlgebra 𝒱) (u v : 𝒱) (k : ℕ) {m : ℤ} (hm : m < 0) :
    cCoeff k (bracketDist (V.Y u) (V.Y v)) m V.vacuum = 0 := by
  rw [cCoeff_apply_vacuum]
  exact mulBySubPow_zero_of_quadrant (applyVec_bracketDist_quadrant V u v) k (-1) m (by omega)
    (by omega)

/-- The constant vacuum coefficient of the kth OPE field is the state u_(k)v.
This identifies which state the reconstructed coefficient field must represent. -/
theorem cCoeff_vacuum_base (V : PreVertexAlgebra 𝒱) (u v : 𝒱) (k : ℕ) :
    cCoeff k (bracketDist (V.Y u) (V.Y v)) 0 V.vacuum = V.smul u k v := by
  rw [cCoeff_apply_vacuum,
    mulBySubPow_diag_of_quadrant (applyVec_bracketDist_quadrant V u v) k (-1) (by omega),
    applyVec_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, PreVertexAlgebra.Y_apply_vacuum_zero,
    PreVertexAlgebra.Y_apply_vacuum_eq_zero V u (by omega), map_zero, sub_zero]
  rw [PreVertexAlgebra.smul_def, mode_apply, show (-1 - (k : ℤ)) = -(k : ℤ) - 1 from by ring]

/-- The vacuum condition for the field `k`-th product. -/
theorem cCoeff_vacuum_eq (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1))
    (htrvac : Tr V.vacuum = 0) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDist (V.Y u) (V.Y v)) m V.vacuum = (V.Y (V.smul u k v)) m V.vacuum := by
  by_cases hm : m < 0
  · rw [cCoeff_vacuum_neg V u v k hm,
      PreVertexAlgebra.Y_apply_vacuum_eq_zero V (V.smul u k v) hm]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
    clear hm
    induction j with
    | zero =>
        rw [Nat.cast_zero, cCoeff_vacuum_base]
        exact (PreVertexAlgebra.Y_apply_vacuum_zero _ _).symm
    | succ i ih =>
        have expand : ∀ (X : End ℂ 𝒱), ⁅Tr, X⁆ V.vacuum = Tr (X V.vacuum) := by
          intro X
          rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
            Module.End.mul_apply, htrvac, map_zero, sub_zero]
        have hA := DFunLike.congr_fun (congrArg (fun (e : End ℂ 𝒱) => e)
          (Tr_comm_cCoeff V Tr htr u v k (i : ℤ))) V.vacuum
        -- Y(u₍ₖ₎v) is also Tr-covariant via htr.
        have hB : ⁅Tr, (V.Y (V.smul u k v)) (i : ℤ)⁆
            = ((i : ℤ) + 1) • (V.Y (V.smul u k v)) ((i : ℤ) + 1) := htr (V.smul u k v) (i : ℤ)
        have hBapp := DFunLike.congr_fun (congrArg (fun (e : End ℂ 𝒱) => e) hB) V.vacuum
        rw [expand, LinearMap.smul_apply] at hA hBapp
        have key : ((i : ℤ) + 1) • cCoeff k (bracketDist (V.Y u) (V.Y v)) ((i : ℤ) + 1) V.vacuum
            = ((i : ℤ) + 1) • (V.Y (V.smul u k v)) ((i : ℤ) + 1) V.vacuum := by
          rw [← hA, ih, hBapp]
        have hc : (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
        rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1),
          ← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1)] at key
        rw [Nat.cast_succ]
        exact smul_right_injective 𝒱 hc key

/-- **The field `n`-th-product theorem** at the VA level (parametric in `Tr`):
`cCoeff k (bracketDist (Yu)(Yv)) = Y(u₍ₖ₎v)`. -/
theorem nth_product (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1))
    (htrvac : Tr V.vacuum = 0) (u v : 𝒱) (k : ℕ) :
    cCoeff k (bracketDist (V.Y u) (V.Y v)) = V.Y (V.smul u k v) := by
  refine V.goddard_uniqueness _ (V.smul u k v) ?_ (cCoeff_vacuum_eq V Tr htr htrvac u v k)
  intro b
  exact dong_nonneg (V.locality u v) (V.locality u b) (V.locality v b) k

/-- **The commutator formula** at the VA level (parametric in `Tr`):
`[u₍ₐ₎, v₍ᵦ₎] = ∑_j C(a,j)·(u₍ⱼ₎v)₍ₐ₊ᵦ₋ⱼ₎`. -/
theorem mode_commutator (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1))
    (htrvac : Tr V.vacuum = 0) (u v : 𝒱) (a b : ℤ) :
    ∃ N : ℕ, ⁅mode (V.Y u) a, mode (V.Y v) b⁆
      = ∑ j : Fin N, gBinom a (j : ℕ) • mode (V.Y (V.smul u (j : ℕ) v)) (a + b - (j : ℕ)) := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSum V u v
  refine ⟨N, ?_⟩
  rw [mode_bracket_ope V u v hdecomp a b]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hcj : c j = (((j : ℕ).factorial : ℂ)⁻¹) • V.Y (V.smul u (j : ℕ) v) := by
    have hrec := cCoeff_deltaSum c j
    rw [← hdecomp, nth_product V Tr htr htrvac] at hrec
    rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
      inv_mul_cancel₀ hne, one_smul]
  rw [hcj, mode_smul,
    ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ))), smul_smul]
  congr 1
  rw [gBinom, div_eq_mul_inv]
  congr 1
  push_cast
  rfl

/-- **The commutator formula together with the locality bound** (parametric in `Tr`): the same
finite sum as `mode_commutator`, *and* the locality vanishing `u₍ⱼ₎v = 0` for `j ≥ N` (the OPE
order).  The vanishing comes from `cCoeff j (bracketDist) = Y(u₍ⱼ₎v) = 0` for `j ≥ N` (a
`δ`-derivative decomposition of order `N`), plus creation `Y w = 0 ⟹ w = 0`. -/
theorem smul_zero_ge (V : PreVertexAlgebra 𝒱) (Tr : End ℂ 𝒱)
    (htr : ∀ (u : 𝒱) (s : ℤ), ⁅Tr, (V.Y u) s⁆ = (s + 1) • (V.Y u) (s + 1))
    (htrvac : Tr V.vacuum = 0) (u v : 𝒱) (a b : ℤ) :
    ∃ N : ℕ, (⁅mode (V.Y u) a, mode (V.Y v) b⁆
      = ∑ j : Fin N, gBinom a (j : ℕ) • mode (V.Y (V.smul u (j : ℕ) v)) (a + b - (j : ℕ)))
      ∧ ∀ j : ℕ, N ≤ j → V.smul u j v = 0 := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSum V u v
  refine ⟨N, ?_, ?_⟩
  · rw [mode_bracket_ope V u v hdecomp a b]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hcj : c j = (((j : ℕ).factorial : ℂ)⁻¹) • V.Y (V.smul u (j : ℕ) v) := by
      have hrec := cCoeff_deltaSum c j
      rw [← hdecomp, nth_product V Tr htr htrvac] at hrec
      rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
    rw [hcj, mode_smul,
      ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ))), smul_smul]
    congr 1
    rw [gBinom, div_eq_mul_inv]
    congr 1
    push_cast
    rfl
  · intro j hj
    have hY : V.Y (V.smul u j v) = cCoeff j (bracketDist (V.Y u) (V.Y v)) :=
      (nth_product V Tr htr htrvac u v j).symm
    rw [hdecomp, cCoeff_sum] at hY
    have hzero : (∑ i : Fin N, cCoeff j (deltaDeriv (i : ℕ) (c i)))
        = (0 : FormalDist (End ℂ 𝒱)) := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [cCoeff_deltaDeriv, if_neg (by have := i.isLt; omega : ¬ (i : ℕ) = j)]
    rw [hzero] at hY
    have hcre := (V.creation (V.smul u j v)).1
    rw [hY, mode_zero, LinearMap.zero_apply] at hcre
    exact hcre.symm


end VOA.AffineGeneral.VARec
