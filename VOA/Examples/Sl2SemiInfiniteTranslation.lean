/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteGhosts
import VOA.Core.SuperNthProduct
import VOA.Core.TensorFieldLift

/-!
# Translation covariance and the mode commutator for the semi-infinite tensor algebra

The bare `SuperVertexAlgebra` interface does not require translation covariance.
`TranslationCovariant` supplies precisely a vacuum-annihilating translation operator
and its coefficient commutator against every field. No differential or nilpotency
property is assumed. The field-product and mode-commutator formulas below follow
from these data, creation, super locality and Goddard uniqueness.
-/

namespace VOA.Sl2SemiInfinite
open Module (End)
open scoped BigOperators TensorProduct
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- Translation data for a super vertex algebra, independently of any conformal vector. -/
structure TranslationCovariant (V : SuperVertexAlgebra 𝒱) where
  T : End ℂ 𝒱
  vacuum_zero : T V.vacuum = 0
  covariant : ∀ u, Reconstruction.DCovariant T (V.Y u)

namespace TranslationCovariant
variable {V : SuperVertexAlgebra 𝒱}

theorem comm_Ycoeff (H : TranslationCovariant V) (u : 𝒱) (m : ℤ) :
    ⁅H.T, V.Y u m⁆ = (m + 1) • V.Y u (m + 1) := by
  rw [LieRing.of_associative_ring_bracket]
  exact H.covariant u m

end TranslationCovariant

namespace TranslationCovariant

variable {V : SuperVertexAlgebra 𝒱}

/-! ## §1  Translation covariance of the twisted OPE bracket -/

/-- **Translation covariance of the twisted OPE bracket**:
`[L₋₁, ⁅Y(u,z₁),Y(v,z₂)⁆_ε] = ∂⁅Y(u,z₁),Y(v,z₂)⁆_ε` with `∂ = ∂₁+∂₂`.  The `ε` rides through
as a scalar; the content is the Leibniz rule plus `comm_Ycoeff`. -/
theorem commT_bracketDistε (H : TranslationCovariant V) (ε : ℂ) (u v : 𝒱) :
    commT (H.T) (bracketDistε ε (V.Y u) (V.Y v))
      = deriv2 (bracketDistε ε (V.Y u) (V.Y v)) := by
  have leib : ∀ (a b c : End ℂ 𝒱), ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := fun a b c => by
    simp only [LieRing.of_associative_ring_bracket]; noncomm_ring
  apply FormalDist₂.ext; intro s t
  simp only [commT_apply, deriv2_apply, bracketDistε_apply, lie_sub, lie_smul, leib,
    comm_Ycoeff, smul_mul_assoc, mul_smul_comm, smul_sub, smul_add, smul_comm ε]
  abel

/-- **The recursion** `[L₋₁, A_m] = (m+1)·A_{m+1}` for the twisted field `k`-th product. -/
theorem L_comm_cCoeffε (H : TranslationCovariant V) (ε : ℂ) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    ⁅H.T, cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m⁆
      = (m + 1) • cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) (m + 1) := by
  show commT (H.T) (mulBySubPow k (bracketDistε ε (V.Y u) (V.Y v))) (-1) m = _
  rw [commT_mulBySubPow, commT_bracketDistε, resByParts]
  rfl

/-! ## §2  The vacuum tower of the twisted field `k`-th product (sign-free) -/

/-- The vacuum-applied twisted OPE bracket vanishes on the quadrant `{s≤-1, t≤-1}`: **both**
terms die by creation, so the `ε` never gets to act. -/
theorem applyVec_bracketDistε_quadrant (H : TranslationCovariant V) (ε : ℂ) (u v : 𝒱) (s t : ℤ)
    (hs : s ≤ -1) (ht : t ≤ -1) :
    applyVec V.vacuum (bracketDistε ε (V.Y u) (V.Y v)) s t = 0 := by
  rw [applyVec_apply, bracketDistε_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.mul_apply,
    V.Y_apply_vacuum_eq_zero v (by omega),
    V.Y_apply_vacuum_eq_zero u (by omega), map_zero, map_zero, smul_zero,
    sub_zero]

/-- Reduce the twisted field `k`-th product on the vacuum to a `(z₁-z₂)ᵏ`-power. -/
theorem cCoeff_apply_vacuumε (H : TranslationCovariant V) (ε : ℂ) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m V.vacuum
      = mulBySubPow k (applyVec V.vacuum (bracketDistε ε (V.Y u) (V.Y v))) (-1) m := by
  show mulBySubPow k (bracketDistε ε (V.Y u) (V.Y v)) (-1) m V.vacuum = _
  rw [← applyVec_apply, applyVec_mulBySubPow]

/-- `A_m 𝟙 = 0` for `m < 0`. -/
theorem cCoeff_vacuum_negε (H : TranslationCovariant V) (ε : ℂ) (u v : 𝒱) (k : ℕ) {m : ℤ} (hm : m < 0) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m V.vacuum = 0 := by
  rw [cCoeff_apply_vacuumε H]
  exact mulBySubPow_zero_of_quadrant (applyVec_bracketDistε_quadrant H ε u v) k (-1) m
    (by omega) (by omega)

/-- `A_0 𝟙 = u₍ₖ₎v` — **no sign**: the `ε`-term of the bracket dies on the vacuum. -/
theorem cCoeff_vacuum_baseε (H : TranslationCovariant V) (ε : ℂ) (u v : 𝒱) (k : ℕ) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) 0 V.vacuum = V.smul u k v := by
  rw [cCoeff_apply_vacuumε H,
    mulBySubPow_diag_of_quadrant (applyVec_bracketDistε_quadrant H ε u v) k (-1) (by omega),
    applyVec_apply, bracketDistε_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.mul_apply,
    V.Y_apply_vacuum_zero,
    V.Y_apply_vacuum_eq_zero u (by omega), map_zero, smul_zero, sub_zero]
  rw [SuperVertexAlgebra.smul_def, mode_apply, show (-1 - (k : ℤ)) = -(k : ℤ) - 1 from by ring]

/-- **The vacuum condition** for the twisted field `k`-th product: `A_m 𝟙 = Y(u₍ₖ₎v)_m 𝟙`. -/
theorem cCoeff_vacuum_eqε (H : TranslationCovariant V) (ε : ℂ) (u v : 𝒱) (k : ℕ) (m : ℤ) :
    cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) m V.vacuum
      = (V.Y (V.smul u k v)) m V.vacuum := by
  by_cases hm : m < 0
  · rw [cCoeff_vacuum_negε H ε u v k hm,
      V.Y_apply_vacuum_eq_zero (V.smul u k v) hm]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
    clear hm
    induction j with
    | zero =>
        rw [Nat.cast_zero, cCoeff_vacuum_baseε H]
        exact (V.Y_apply_vacuum_zero _).symm
    | succ i ih =>
        have expand : ∀ (X : End ℂ 𝒱), ⁅H.T, X⁆ V.vacuum = H.T (X V.vacuum) := by
          intro X
          rw [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
            Module.End.mul_apply, H.vacuum_zero, map_zero, sub_zero]
        have hA := DFunLike.congr_fun (L_comm_cCoeffε H ε u v k (i : ℤ)) V.vacuum
        have hB := DFunLike.congr_fun (comm_Ycoeff H (V.smul u k v) (i : ℤ)) V.vacuum
        rw [expand, LinearMap.smul_apply] at hA hB
        have key : ((i : ℤ) + 1) • cCoeff k (bracketDistε ε (V.Y u) (V.Y v)) ((i : ℤ) + 1)
              V.vacuum
            = ((i : ℤ) + 1) • (V.Y (V.smul u k v)) ((i : ℤ) + 1) V.vacuum := by
          rw [← hA, ih, hB]
        have hc : (((i : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
        rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1),
          ← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) + 1)] at key
        rw [Nat.cast_succ]
        exact smul_right_injective 𝒱 hc key

/-! ## §3  The `n`-th product theorem -/

/-- **The super field `n`-th-product theorem** (`n = k ≥ 0`):
`Y(u₍ₖ₎v, z) = Res_{z₁}((z₁-z)ᵏ ⁅Y(u,z₁),Y(v,z)⁆_ε)` with `ε = (-1)^{|u||v|}`.

Note the **absence of any sign on the right**: the Koszul factor lives in the bracket only.
Goddard uniqueness (`goddard_uniquenessε`) applies because Dong's lemma
(`SuperVertexAlgebra.dong_fields`) delivers exactly the `Localε (koszul (p+q) r)` the parity
`|u₍ₖ₎v| = p + q` demands. -/
theorem nth_productε (H : TranslationCovariant V) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (k : ℕ) :
    cCoeff k (bracketDistε (koszul p q) (V.Y u) (V.Y v)) = V.Y (V.smul u k v) := by
  refine V.goddard_uniquenessε _ (V.smul u k v)
    (V.smul_mem_parity hu hv (k : ℤ)) (fun r b hb => ?_)
    (cCoeff_vacuum_eqε H (koszul p q) u v k)
  exact V.dong_fields hu hv hb k

/-! ## §4  The OPE δ-decomposition and the commutator formula -/

/-- The **twisted mode bracket** `u₍ₘ₎v₍ₙ₎ − ε·v₍ₙ₎u₍ₘ₎`. -/
def modeBracketε (ε : ℂ) (a b : FormalDist (End ℂ 𝒱)) (m n : ℤ) : End ℂ 𝒱 :=
  mode a m * mode b n - ε • (mode b n * mode a m)

@[simp] theorem modeBracketε_apply (ε : ℂ) (a b : FormalDist (End ℂ 𝒱)) (m n : ℤ) :
    modeBracketε ε a b m n = mode a m * mode b n - ε • (mode b n * mode a m) := rfl

/-- The twisted mode bracket is the twisted bracket distribution at the mode indices. -/
theorem modeBracketε_eq (ε : ℂ) (a b : FormalDist (End ℂ 𝒱)) (m n : ℤ) :
    modeBracketε ε a b m n = bracketDistε ε a b (-m - 1) (-n - 1) := rfl

/-- **The operator product expansion, super case.**  Super-locality VA4 plus Proposition
5.1.2 gives a finite `δ`-decomposition of the *twisted* bracket. -/
theorem bracket_deltaSumε (H : TranslationCovariant V) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) :
    ∃ (N : ℕ) (c : Fin N → FormalDist (End ℂ 𝒱)),
      bracketDistε (koszul p q) (V.Y u) (V.Y v) = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j) := by
  obtain ⟨N, hN⟩ := V.locality u hu v hv
  exact ⟨N, (local_iff_deltaSum _ N).mp hN⟩

/-- **The commutator formula, OPE form**, for the twisted bracket. -/
theorem mode_bracket_opeε (H : TranslationCovariant V) (ε : ℂ) (u v : 𝒱) {N : ℕ}
    {c : Fin N → FormalDist (End ℂ 𝒱)}
    (h : bracketDistε ε (V.Y u) (V.Y v) = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j)) (a b : ℤ) :
    modeBracketε ε (V.Y u) (V.Y v) a b = ∑ j : Fin N,
      (∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ))) • mode (c j) (a + b - ((j : ℕ) : ℤ)) := by
  rw [modeBracketε_eq, h, formalDist₂_sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deltaDeriv_apply,
    show (∏ i ∈ Finset.range (j : ℕ), (-(-a - 1) - 1 - (i : ℤ)))
        = ∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ)) from
      Finset.prod_congr rfl (fun i _ => by ring)]
  congr 1
  rw [mode_apply]
  congr 1
  ring

/-- **The super commutator formula with a shared bound.**  One `bracket_deltaSumε` yields
*both* the vanishing `u₍ₖ₎v = 0` for `k ≥ N` and the commutator formula with the same `N` —
the form the Pascal induction consumes.  The right-hand side carries **no** Koszul sign. -/
theorem commBoundε (H : TranslationCovariant V) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (m n : ℤ) :
    ∃ N : ℕ, (∀ k : ℕ, N ≤ k → V.smul u k v = 0)
      ∧ modeBracketε (koszul p q) (V.Y u) (V.Y v) m n
        = ∑ j : Fin N, gBinom m (j : ℕ) • mode (V.Y (V.smul u (j : ℕ) v)) (m + n - (j : ℕ)) := by
  obtain ⟨N, c, hdecomp⟩ := bracket_deltaSumε H hu hv
  refine ⟨N, ?_, ?_⟩
  · intro k hk
    have h1 : V.Y (V.smul u k v) = cCoeff k (bracketDistε (koszul p q) (V.Y u) (V.Y v)) :=
      (nth_productε H hu hv k).symm
    rw [hdecomp, cCoeff_sum, Finset.sum_eq_zero (fun j _ => by
        rw [cCoeff_deltaDeriv, if_neg (by have h := j.2; omega)])] at h1
    have h2 : V.smul u k v = mode (V.Y (V.smul u k v)) (-1) V.vacuum :=
      (V.smul_neg_one_vacuum (V.smul u k v)).symm
    rw [h2, h1, mode_apply]; rfl
  · rw [mode_bracket_opeε H (koszul p q) u v hdecomp m n]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hne : ((j : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hcj : c j = (((j : ℕ).factorial : ℂ)⁻¹) • V.Y (V.smul u (j : ℕ) v) := by
      have hrec := cCoeff_deltaSum c j
      rw [← hdecomp, nth_productε H hu hv] at hrec
      rw [hrec, ← Int.cast_smul_eq_zsmul ℂ ((j : ℕ).factorial : ℤ), Int.cast_natCast, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
    rw [hcj, mode_smul,
      ← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range (j : ℕ), (m - (i : ℤ))), smul_smul]
    congr 1
    rw [gBinom, div_eq_mul_inv]
    congr 1
    push_cast
    rfl

/-- **The super commutator formula 5.1.7c**: `u₍ₐ₎v₍ᵦ₎ − ε·v₍ᵦ₎u₍ₐ₎
= ∑_j C(a,j)·(u₍ⱼ₎v)₍ₐ₊ᵦ₋ⱼ₎`, with `ε = (-1)^{|u||v|}` and no sign on the right. -/
theorem mode_commutatorε (H : TranslationCovariant V) {p q : ZMod 2} {u v : 𝒱} (hu : u ∈ V.parity p)
    (hv : v ∈ V.parity q) (a b : ℤ) :
    ∃ N : ℕ, modeBracketε (koszul p q) (V.Y u) (V.Y v) a b
      = ∑ j : Fin N, gBinom a (j : ℕ) • mode (V.Y (V.smul u (j : ℕ) v)) (a + b - (j : ℕ)) := by
  obtain ⟨N, _, h⟩ := commBoundε H hu hv a b
  exact ⟨N, h⟩


/-- The commutator formula with any prescribed bound on singular state products. -/
theorem mode_commutator_bound (H : TranslationCovariant V) {p q : ZMod 2}
    {u v : 𝒱} (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) (N : ℕ)
    (hN : ∀ j : ℕ, N ≤ j → mode (V.Y u) j v = 0) (m n : ℤ) :
    mode (V.Y u) m * mode (V.Y v) n
      - koszul p q • (mode (V.Y v) n * mode (V.Y u) m)
      = ∑ j ∈ Finset.range N,
          gBinom m j • mode (V.Y (mode (V.Y u) j v)) (m + n - j) := by
  let f : ℕ → End ℂ 𝒱 := fun j =>
    gBinom m j • mode (V.Y (mode (V.Y u) j v)) (m + n - j)
  obtain ⟨M, hM, hc⟩ := commBoundε H hu hv m n
  change modeBracketε (koszul p q) (V.Y u) (V.Y v) m n = ∑ j : Fin M, f j at hc
  rw [Fin.sum_univ_eq_sum_range f] at hc
  change modeBracketε (koszul p q) (V.Y u) (V.Y v) m n = _
  rw [hc]
  change ∑ j ∈ Finset.range M, f j = ∑ j ∈ Finset.range N, f j
  have hbound : ∀ L : ℕ, (∀ j : ℕ, L ≤ j → mode (V.Y u) j v = 0) →
      ∀ K : ℕ, L ≤ K → (∑ j ∈ Finset.range L, f j) = ∑ j ∈ Finset.range K, f j := by
    intro L hL K hLK
    apply Finset.sum_subset (Finset.range_mono hLK)
    intro j _ hj
    have hzero := hL j (by simpa only [Finset.mem_range, not_lt] using hj)
    dsimp only [f]
    rw [hzero, map_zero]
    exact smul_zero _
  exact (hbound M hM (max M N) (le_max_left _ _)).trans
    (hbound N hN (max M N) (le_max_right _ _)).symm

/-- A field pair with only simple and double poles has this complete mode commutator. -/
theorem mode_commutator_two (H : TranslationCovariant V) {p q : ZMod 2}
    {u v : 𝒱} (hu : u ∈ V.parity p) (hv : v ∈ V.parity q)
    (hhigh : ∀ j : ℤ, 2 ≤ j → mode (V.Y u) j v = 0) (m n : ℤ) :
    mode (V.Y u) m * mode (V.Y v) n
      - koszul p q • (mode (V.Y v) n * mode (V.Y u) m)
      = mode (V.Y (mode (V.Y u) 0 v)) (m + n)
        + (m : ℂ) • mode (V.Y (mode (V.Y u) 1 v)) (m + n - 1) := by
  rw [mode_commutator_bound H hu hv 2 (fun j hj => hhigh j (by omega))]
  simp [Finset.sum_range_succ, gBinom]

/-- A zero mode acts on every field by its super commutator. -/
theorem zero_mode_commutator (H : TranslationCovariant V) {p q : ZMod 2}
    {u v : 𝒱} (hu : u ∈ V.parity p) (hv : v ∈ V.parity q) (n : ℤ) :
    mode (V.Y u) 0 * mode (V.Y v) n
      - koszul p q • (mode (V.Y v) n * mode (V.Y u) 0)
      = mode (V.Y (mode (V.Y u) 0 v)) n := by
  exact congrArg (fun f => mode f n) (nth_productε H hu hv 0)

/-- Translation preserves parity, as follows from its vacuum coefficient. -/
theorem T_mem_parity (H : TranslationCovariant V) {p : ZMod 2} {u : 𝒱}
    (hu : u ∈ V.parity p) : H.T u ∈ V.parity p := by
  have h := congrArg (fun f : End ℂ 𝒱 => f V.vacuum) (H.covariant u 0)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, H.vacuum_zero,
    map_zero, sub_zero, V.Y_apply_vacuum_zero, zero_add, one_smul] at h
  rw [h]
  simpa only [add_zero] using V.parity_mode u hu V.vacuum V.vacuum_parity (-2)

/-- Translation commutes with the parity involution. -/
theorem T_parityInvol (H : TranslationCovariant V) (u : 𝒱) :
    H.T ((TensorVA.parGr V).parityInvol u) =
      (TensorVA.parGr V).parityInvol (H.T u) := by
  have hu : u ∈ ⨆ p, V.parity p := by
    rw [((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
      V.parity_isInternal).2]
    trivial
  refine Submodule.iSup_induction' (motive := fun x _ =>
    H.T ((TensorVA.parGr V).parityInvol x) =
      (TensorVA.parGr V).parityInvol (H.T x)) _ ?_ ?_ ?_ hu
  · intro p x hx
    rw [(TensorVA.parGr V).parityInvol_homog hx,
      (TensorVA.parGr V).parityInvol_homog (H.T_mem_parity hx), map_smul]
  · simp only [map_zero]
  · intro x y _ _ hx hy
    simp only [map_add, hx, hy]

end TranslationCovariant

section Tensor
variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
variable {V : SuperVertexAlgebra A} {W : SuperVertexAlgebra B}
open TensorFieldLift Reconstruction

/-- Postcomposition by a constant commuting with translation preserves covariance. -/
theorem dcovariant_postComp {T S : End ℂ A} {f : FormalDist (End ℂ A)}
    (hf : DCovariant T f) (hS : T * S = S * T) :
    DCovariant T (fun m => f m * S) := by
  intro m
  calc
    T * (f m * S) - (f m * S) * T = (T * f m - f m * T) * S := by
      rw [sub_mul, mul_assoc, mul_assoc, ← hS]
      simp only [mul_assoc]
    _ = (m + 1) • (f (m + 1) * S) := by rw [hf m, smul_mul_assoc]

/-- The unsigned tensor convolution has the sum of the two translation operators. -/
theorem rawCoeff_DCovariant (HV : TranslationCovariant V) (HW : TranslationCovariant W)
    (a : A) (b : B) : DCovariant (tensorTranslation HV.T HW.T)
      (fun s => TensorVA.rawCoeff V W a b s) := by
  have heq : (fun s => TensorVA.rawCoeff V W a b s) =
      nprod (isField_firstField (B := B) (TensorVA.isField_superY V a))
        (isField_secondField (A := A) (TensorVA.isField_superY W b)) := by
    funext s
    apply TensorProduct.ext'
    intro x y
    rw [TensorVA.rawCoeff_tmul, nprod_firstField_secondField_apply
      (TensorVA.isField_superY V a) (TensorVA.isField_superY W b)]
    exact finsum_congr fun m => by
      rw [Module.End.mul_apply, secondField_tmul, firstField_tmul]
  rw [heq]
  exact Reconstruction.DCovariant.nprod _ _
    (dcovariant_firstField (HV.covariant a)) (dcovariant_secondField (HW.covariant b))

/-- Tensor translation commutes with the Koszul involution on the first factor. -/
theorem tensorTranslation_kappaTen (HV : TranslationCovariant V)
    (HW : TranslationCovariant W) :
    tensorTranslation HV.T HW.T * TensorVA.kappaTen V W 1 =
      TensorVA.kappaTen V W 1 * tensorTranslation HV.T HW.T := by
  apply TensorProduct.ext'
  intro x y
  simp only [Module.End.mul_apply, tensorTranslation, LinearMap.add_apply,
    LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorVA.kappaTen_tmul,
    TensorVA.koszulOp_one, map_add, HV.T_parityInvol]

/-- Covariance of all fields of the tensor super vertex algebra. -/
theorem tenY_DCovariant (HV : TranslationCovariant V) (HW : TranslationCovariant W)
    (u : A ⊗[ℂ] B) :
    DCovariant (tensorTranslation HV.T HW.T) (TensorVA.tenY V W u) := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Reconstruction.DCovariant.zero
  | add x y hx hy => rw [map_add]; exact hx.add hy
  | tmul a b =>
      rw [TensorVA.tenY_tmul_eq]
      apply Reconstruction.DCovariant.smul
      apply Reconstruction.DCovariant.add
      · apply dcovariant_postComp (rawCoeff_DCovariant HV HW a b)
        rw [mul_add, add_mul, mul_one, one_mul, tensorTranslation_kappaTen HV HW]
      · apply dcovariant_postComp
          (rawCoeff_DCovariant HV HW a ((TensorVA.parGr W).parityInvol b))
        rw [mul_sub, sub_mul, mul_one, one_mul, tensorTranslation_kappaTen HV HW]

/-- Translation data are preserved by tensor products, including the Koszul signs. -/
noncomputable def translationCovariant_tensorSVA
    (HV : TranslationCovariant V) (HW : TranslationCovariant W)
    (hV : TensorVA.ParityCompatible V) (hW : TensorVA.ParityCompatible W)
    (hg : TensorVA.TensorGradingHyp V W) :
    TranslationCovariant (TensorVA.tensorSVA V W hV hW hg) where
  T := tensorTranslation HV.T HW.T
  vacuum_zero := by
    change (tensorTranslation HV.T HW.T) (V.vacuum ⊗ₜ[ℂ] W.vacuum) = 0
    simp only [tensorTranslation, LinearMap.add_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, HV.vacuum_zero, HW.vacuum_zero,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  covariant := tenY_DCovariant HV HW

end Tensor

/-- The translation of the reconstructed one-pair ghost algebra. -/
noncomputable def translationCovariant_bcGhostSVA : TranslationCovariant Ghost.bcGhostSVA where
  T := SympFerm.T
  vacuum_zero := SympFerm.T_one
  covariant := Ghost.YGh_DCovariant

/-- The actual two-pair ghost algebra has translation covariance. -/
noncomputable def translationCovariant_ghostPairSVA : TranslationCovariant ghostPairSVA :=
  translationCovariant_tensorSVA translationCovariant_bcGhostSVA
    translationCovariant_bcGhostSVA _ _ _

/-- The actual three-pair ghost algebra has translation covariance. -/
noncomputable def translationCovariant_sl2GhostSVA : TranslationCovariant sl2GhostSVA :=
  translationCovariant_tensorSVA translationCovariant_ghostPairSVA
    translationCovariant_bcGhostSVA _ _ _

end VOA.Sl2SemiInfinite
