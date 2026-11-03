/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.FLM
import VOA.Core.Identities
import VOA.Core.Reconstruction
import VOA.Foundations.DeltaJump

/-!
# Weak-associativity locality of the reflected field — `weakAssocLoc` (Gannon 5.1.8)

This file discharges the skew-symmetry gate: it proves `weakAssocLoc W u : WeakAssocLoc W u`
(the `b`-uniform operator skew-locality of the candidate skew field `skewDist W u`), which feeds
`Core.Skew`'s proven reduction `WeakAssocLoc → skewDist = Y u` to give skew-symmetry
(Gannon 5.1.8, FLM §8.8–8.10 / Lepowsky–Li Ch. 2–3, the two-sided `ι_z` completion).

The entire kill mechanism (Goddard-vacuum reduction + `vconv`/`negPowJump` engine) is
`sorry`-free / axiom-clean:

* `smul_comm_T`  — the honest `(Comm)` relation `c₍ₚ₎(Tw) = T(c₍ₚ₎w) + p·c₍ₚ₋₁₎w` (from
  `L_neg_one_deriv` + `smul_T_apply`; pure translation covariance, NO skew-field locality).
* **`smul_Tpow_expand`** — the master `e^{zT}`-conjugation of a FIXED mode:
  `c₍ₚ₎(Tᵏu) = ∑_{r≤k} C(k,r)·p^{(r)}·Tᵏ⁻ʳ(c₍ₚ₋ᵣ₎u)`  (falling factorial `p^{(r)} = fallI p r`).
* **`Term2_expand`** — `(Y c)ₙ((Y u)ₘ𝟙)` in closed form via creation + the master lemma.
* **`Term1_expand`** — `skewCoeffFun u m ((Y c)ₙ𝟙)` in closed form via creation + `smul_Tpow`.

The two closed forms are exactly the `w`-dominant (`Term2`) and `z`-dominant (`Term1`)
expansions of the SAME honest field `Y(c, w−z)u` on the fixed `u = ∑ₛ (c₍ₛ₎u)·(w−z)⁻ˢ⁻¹`.

The key step (`Gfield_eq_jumpSum`) is the per-mode cancellation
of the two closed forms onto the jump-sum.  Proved by a `funext m n` + `j`-split of the `Term1`
finsum into three ranges (regular `=Term2`, vanishing middle, singular `=jump-sum`), handling all
four sign sectors of `(m,n)`; the residual scalar identities (`range1_scalar`, `range3_scalar`,
`nneg_scalar`) are pure `ℂ`-factorial algebra.  With this, `skewVacLocal`, `weakAssocLoc`, and
`skew` are all `sorry`-free / axiom-clean (`[propext, Classical.choice, Quot.sound]`), discharging
the entire skew gate.

## Status
Complete & `sorry`-free / axiom-free.  `Gfield_eq_jumpSum` is proved, so
`skewVacLocal`/`weakAssocLoc` — the skew-locality input consumed
by `Core.SkewSymmetry.skew` — are fully proved via the two-sided `ι_z` completion
(FLM §8.8–8.10).  Verified `#print axioms = [propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

open scoped BigOperators
open Module (End)

universe u

/-! ## §A.  Goddard uniqueness from VACUUM-locality only (copied, axiom-clean). -/

namespace PreVertexAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

private def goddardDiffVac (V : PreVertexAlgebra 𝒱) (A : FormalDist (End ℂ 𝒱)) (a b : 𝒱) :
    FormalDist₂ 𝒱 := fun p q => A p ((V.Y b) q V.vacuum) - (V.Y a) p ((V.Y b) q V.vacuum)

theorem goddard_uniqueness_vac (V : PreVertexAlgebra 𝒱) (A : FormalDist (End ℂ 𝒱)) (a : 𝒱)
    (hAloc : ∀ b : 𝒱, ∃ N : ℕ, mulBySubPow N (applyVec V.vacuum (bracketDist A (V.Y b))) = 0)
    (hAvac : ∀ m : ℤ, A m V.vacuum = (V.Y a) m V.vacuum) :
    A = V.Y a := by
  funext m
  refine LinearMap.ext fun b => ?_
  obtain ⟨N₁, hN₁⟩ := hAloc b
  obtain ⟨N₂, hN₂⟩ := V.locality a b
  have hDeq : goddardDiffVac V A a b = applyVec V.vacuum (bracketDist A (V.Y b))
      - applyVec V.vacuum (bracketDist (V.Y a) (V.Y b)) := by
    ext p q
    have hsub : (applyVec V.vacuum (bracketDist A (V.Y b))
        - applyVec V.vacuum (bracketDist (V.Y a) (V.Y b))) p q
        = applyVec V.vacuum (bracketDist A (V.Y b)) p q
          - applyVec V.vacuum (bracketDist (V.Y a) (V.Y b)) p q := rfl
    rw [hsub]
    simp only [goddardDiffVac, applyVec_apply, bracketDist_apply, LinearMap.sub_apply,
      Module.End.mul_apply]
    rw [hAvac p]
    abel
  have hkill : mulBySubPow (N₁ + N₂) (goddardDiffVac V A a b) = 0 := by
    rw [hDeq, map_sub]
    have e1 : mulBySubPow (N₁ + N₂) (applyVec V.vacuum (bracketDist A (V.Y b))) = 0 :=
      mulBySubPow_eq_zero_mono (Nat.le_add_right N₁ N₂) hN₁
    have e2 : mulBySubPow (N₁ + N₂) (applyVec V.vacuum (bracketDist (V.Y a) (V.Y b))) = 0 :=
      mulBySubPow_eq_zero_mono (Nat.le_add_left N₂ N₁)
        (by rw [← applyVec_mulBySubPow, hN₂, applyVec_zero])
    rw [e1, e2, sub_zero]
  have hbb : IsBddBelow₂ (goddardDiffVac V A a b) := by
    refine ⟨0, fun p q hq => ?_⟩
    show A p ((V.Y b) q V.vacuum) - (V.Y a) p ((V.Y b) q V.vacuum) = 0
    rw [V.Y_apply_vacuum_eq_zero b hq, map_zero, map_zero, sub_zero]
  have hD0 : goddardDiffVac V A a b = 0 :=
    eq_zero_of_mulBySubPow_of_bddBelow (N₁ + N₂) _ hkill hbb
  have hfin : goddardDiffVac V A a b m 0 = 0 := congrFun (congrFun hD0 m) 0
  show A m b = (V.Y a) m b
  rw [show goddardDiffVac V A a b m 0
        = A m ((V.Y b) 0 V.vacuum) - (V.Y a) m ((V.Y b) 0 V.vacuum) from rfl,
    V.Y_apply_vacuum_zero b, sub_eq_zero] at hfin
  exact hfin

end PreVertexAlgebra

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

def SkewVacLocal (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) : Prop :=
  ∀ c : 𝒱, ∃ N : ℕ,
    mulBySubPow N (applyVec W.vacuum (bracketDist (skewDist W u) (W.Y c))) = 0

theorem skewDist_eq_Y_of_vacLocal (W : VertexOperatorAlgebra 𝒱) (u : 𝒱)
    (h : SkewVacLocal W u) : skewDist W u = W.Y u := by
  refine PreVertexAlgebra.goddard_uniqueness_vac W.toPreVertexAlgebra (skewDist W u) u ?_ ?_
  · intro b; exact h b
  · intro m; rw [skewDist_apply]; exact skewCoeffFun_vacuum W u m

theorem weakAssocLoc_of_vacLocal (W : VertexOperatorAlgebra 𝒱) (u : 𝒱)
    (h : SkewVacLocal W u) : WeakAssocLoc W u := by
  intro c
  obtain ⟨N, hN⟩ := W.locality u c
  refine ⟨N, fun b => ?_⟩
  rw [skewDist_eq_Y_of_vacLocal W u h, ← applyVec_mulBySubPow, hN, applyVec_zero]

/-! ## §B.  The `vconv` / `negPowJump` kill engine (unconditional; axiom-clean). -/

noncomputable def creS (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (s : ℕ) : ℤ → 𝒱 :=
  fun t => (W.Y (W.smul c (s : ℤ) u)) t W.vacuum

noncomputable def vconv (g : ℤ → 𝒱) (h : FormalDist₂ ℂ) : FormalDist₂ 𝒱 :=
  fun m n => ∑ᶠ p : ℤ, h (m - p) n • g p

@[simp] theorem vconv_apply (g : ℤ → 𝒱) (h : FormalDist₂ ℂ) (m n : ℤ) :
    vconv g h m n = ∑ᶠ p : ℤ, h (m - p) n • g p := rfl

theorem negPowJump_off_antidiag (s : ℕ) {a b : ℤ} (hab : a + b ≠ -(s : ℤ) - 1) :
    negPowJump s a b = 0 := by
  show expandPos (-(s : ℤ) - 1) a b - expandNeg (-(s : ℤ) - 1) a b = 0
  rw [expandPos_apply, expandNeg_apply,
    if_neg (by rintro ⟨_, he⟩; omega), if_neg (by rintro ⟨_, he⟩; omega), sub_zero]

theorem vconv_negPowJump_single (g : ℤ → 𝒱) (s : ℕ) (m n : ℤ) :
    vconv g (negPowJump s) m n
      = negPowJump s (m - (m + n + (s : ℤ) + 1)) n • g (m + n + (s : ℤ) + 1) := by
  rw [vconv_apply]
  refine finsum_eq_single _ (m + n + (s : ℤ) + 1) fun p hp => ?_
  rw [negPowJump_off_antidiag s (by omega), zero_smul]

theorem vconv_mulBySub_negPowJump (g : ℤ → 𝒱) (s : ℕ) :
    mulBySub (vconv g (negPowJump (s + 1))) = vconv g (negPowJump s) := by
  ext m n
  rw [mulBySub_apply, vconv_negPowJump_single, vconv_negPowJump_single,
    vconv_negPowJump_single]
  set d : ℤ := m - (m + n + (s : ℤ) + 1) with hd
  have harg1 : (m - 1) + n + ((s + 1 : ℕ) : ℤ) + 1 = m + n + (s : ℤ) + 1 := by push_cast; ring
  have harg2 : m + (n - 1) + ((s + 1 : ℕ) : ℤ) + 1 = m + n + (s : ℤ) + 1 := by push_cast; ring
  rw [harg1, harg2]
  have hpt1 : (m - 1) - (m + n + (s : ℤ) + 1) = d - 1 := by rw [hd]; ring
  have hpt2 : m - (m + n + (s : ℤ) + 1) = d := by rw [hd]
  rw [hpt1, hpt2, ← sub_smul]
  congr 1
  have e0 := congrFun (congrFun (mulBySub_negPowJump s) d) n
  rw [mulBySub_apply] at e0
  exact e0

theorem vconv_negPowJump_zero_apply (g : ℤ → 𝒱) (m n : ℤ) :
    vconv g (negPowJump 0) m n = g (m + n + 1) := by
  rw [vconv_negPowJump_single, negPowJump_zero, deltaDeriv_apply]
  rw [Finset.range_zero, Finset.prod_empty, one_smul,
    show (m - (m + n + ((0 : ℕ) : ℤ) + 1)) + n + 1 + ((0 : ℕ) : ℤ) = 0 by push_cast; ring,
    deltaCoeff_apply, if_pos rfl, one_smul,
    show m + n + ((0 : ℕ) : ℤ) + 1 = m + n + 1 by push_cast; ring]

theorem mulBySub_vconv_negPowJump_zero (g : ℤ → 𝒱) :
    mulBySub (vconv g (negPowJump 0)) = 0 := by
  ext m n
  rw [mulBySub_apply, vconv_negPowJump_zero_apply, vconv_negPowJump_zero_apply,
    show (m - 1) + n + 1 = m + n by ring, show m + (n - 1) + 1 = m + n by ring, sub_self]
  rfl

theorem mulBySubPow_vconv_negPowJump_descent (g : ℤ → 𝒱) (s : ℕ) :
    mulBySubPow s (vconv g (negPowJump s)) = vconv g (negPowJump 0) := by
  induction s with
  | zero => simp
  | succ k ih =>
      rw [mulBySubPow_succ', vconv_mulBySub_negPowJump, ih]

theorem mulBySubPow_vconv_negPowJump_eq_zero (g : ℤ → 𝒱) {s N : ℕ} (h : s + 1 ≤ N) :
    mulBySubPow N (vconv g (negPowJump s)) = 0 := by
  induction N, h using Nat.le_induction with
  | base =>
      rw [mulBySubPow_succ, LinearMap.comp_apply, mulBySubPow_vconv_negPowJump_descent,
        mulBySub_vconv_negPowJump_zero]
  | succ n _ ih => rw [mulBySubPow_succ, LinearMap.comp_apply, ih, map_zero]

/-! ## §C.  The honest `e^{zT}`-expansion machinery (all axiom-clean). -/

/-- The honest `(Comm)` relation: `c₍ₚ₎(T w) = T(c₍ₚ₎ w) + p • c₍ₚ₋₁₎ w`. -/
theorem smul_comm_T (W : VertexOperatorAlgebra 𝒱) (c w : 𝒱) (p : ℤ) :
    W.smul c p (W.toPreVertexAlgebra.T w)
      = W.toPreVertexAlgebra.T (W.smul c p w) + p • W.smul c (p - 1) w := by
  have hderiv := L_neg_one_deriv W c w p
  rw [← T_eq_Lneg1] at hderiv
  rw [smul_T_apply] at hderiv
  linear_combination (norm := module) -hderiv

/-- Falling factorial `p^{(r)} = ∏_{i<r}(p-i)`. -/
def fallI (p : ℤ) (r : ℕ) : ℤ := ∏ i ∈ Finset.range r, (p - (i : ℤ))

@[simp] theorem fallI_zero (p : ℤ) : fallI p 0 = 1 := by simp [fallI]

theorem mul_fallI_pred (p : ℤ) (r : ℕ) : p * fallI (p - 1) r = fallI p (r + 1) := by
  rw [fallI, fallI, Finset.prod_range_succ' (fun i => p - (i : ℤ)) r]
  rw [show p - ((0 : ℕ) : ℤ) = p by push_cast; ring, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by push_cast; ring

/-- The integer coefficient `C(k,r)·fallI p r` of `Tᵏ⁻ʳ(c₍ₚ₋ᵣ₎u)`. -/
def mcoeff (p : ℤ) (k r : ℕ) : ℤ := (k.choose r : ℤ) * fallI p r

/-- **The master expansion lemma.** -/
theorem smul_Tpow_expand (W : VertexOperatorAlgebra 𝒱) (c u : 𝒱) (p : ℤ) (k : ℕ) :
    W.smul c p ((W.toPreVertexAlgebra.T ^ k) u)
      = ∑ r ∈ Finset.range (k + 1),
          (mcoeff p k r) • ((W.toPreVertexAlgebra.T ^ (k - r)) (W.smul c (p - (r : ℤ)) u)) := by
  induction k generalizing p with
  | zero =>
      rw [Finset.sum_range_one]; simp [mcoeff, fallI]
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, smul_comm_T, ih, ih (p - 1)]
      set Φ : ℕ → 𝒱 := fun r => (W.toPreVertexAlgebra.T ^ ((k + 1) - r)) (W.smul c (p - (r : ℤ)) u)
        with hΦ
      have hA : W.toPreVertexAlgebra.T
            (∑ r ∈ Finset.range (k + 1),
              (mcoeff p k r) • ((W.toPreVertexAlgebra.T ^ (k - r)) (W.smul c (p - (r : ℤ)) u)))
          = ∑ r ∈ Finset.range (k + 2), (mcoeff p k r) • Φ r := by
        rw [map_sum, Finset.sum_range_succ (fun r => (mcoeff p k r) • Φ r) (k + 1),
          show (mcoeff p k (k + 1)) = 0 by
            rw [mcoeff, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul],
          zero_smul, add_zero]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        rw [map_zsmul, hΦ]
        congr 1
        show W.toPreVertexAlgebra.T ((W.toPreVertexAlgebra.T ^ (k - r)) (W.smul c (p - (r : ℤ)) u))
          = (W.toPreVertexAlgebra.T ^ ((k + 1) - r)) (W.smul c (p - (r : ℤ)) u)
        rw [← Module.End.mul_apply, ← pow_succ', show (k + 1) - r = (k - r) + 1 by omega]
      have hB : p • (∑ r ∈ Finset.range (k + 1),
              (mcoeff (p - 1) k r) • ((W.toPreVertexAlgebra.T ^ (k - r)) (W.smul c ((p - 1) - (r : ℤ)) u)))
          = ∑ r ∈ Finset.range (k + 2),
              (if r = 0 then (0 : ℤ) else p * mcoeff (p - 1) k (r - 1)) • Φ r := by
        rw [Finset.smul_sum,
          Finset.sum_range_succ' (fun r => (if r = 0 then (0 : ℤ)
            else p * mcoeff (p - 1) k (r - 1)) • Φ r) (k + 1),
          if_pos rfl, zero_smul, add_zero]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        rw [if_neg (Nat.succ_ne_zero r),
          show (r + 1 - 1) = r from by omega, smul_smul, hΦ]
        show (p * mcoeff (p - 1) k r) •
            (W.toPreVertexAlgebra.T ^ (k - r)) (W.smul c ((p - 1) - (r : ℤ)) u)
          = (p * mcoeff (p - 1) k r) •
            (W.toPreVertexAlgebra.T ^ ((k + 1) - (r + 1))) (W.smul c (p - ((r + 1 : ℕ) : ℤ)) u)
        rw [Nat.succ_sub_succ, show (p - ((r + 1 : ℕ) : ℤ)) = (p - 1) - (r : ℤ) by push_cast; ring]
      rw [hA, hB, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_range] at hr
      rw [← add_smul]
      congr 1
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · subst hr0
        rw [if_pos rfl, add_zero]
        simp only [mcoeff, Nat.choose_zero_right, fallI_zero]
      · obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
        rw [if_neg (Nat.succ_ne_zero q), Nat.add_sub_cancel,
          mcoeff, mcoeff, mcoeff,
          show p * ((k.choose q : ℤ) * fallI (p - 1) q)
              = (k.choose q : ℤ) * (p * fallI (p - 1) q) by ring,
          mul_fallI_pred, Nat.choose_succ_succ, Nat.cast_add, add_mul]
        ring

theorem smul_vac_creation (W : VertexOperatorAlgebra 𝒱) (v : 𝒱) (t : ℕ) :
    W.smul v (-(t : ℤ) - 1) W.vacuum = ((t.factorial : ℂ)⁻¹) • ((W.toPreVertexAlgebra.T ^ t) v) :=
  creation_pow W v t

theorem Yk_smul (W : VertexOperatorAlgebra 𝒱) (v x : 𝒱) (k : ℤ) :
    (W.Y v) k x = W.smul v (-k - 1) x := by
  rw [PreVertexAlgebra.smul_def, mode_apply, show (-(-k - 1) - 1 : ℤ) = k by ring]

theorem skewCoeffFun_smul (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (t : ℤ) (a : ℂ) (b : 𝒱) :
    skewCoeffFun W u t (a • b) = a • skewCoeffFun W u t b := by
  have := (skewOp W u t).map_smul a b
  simpa only [skewOp_apply] using this

/-- **Term2 closed form** (the `w`-dominant expansion of `Y(c,w−z)u` on the fixed `u`). -/
theorem Term2_expand (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (m n : ℤ) :
    (W.Y c) n ((W.Y u) m W.vacuum)
      = if 0 ≤ m then
          ((m.toNat.factorial : ℂ)⁻¹) • (∑ r ∈ Finset.range (m.toNat + 1),
            (mcoeff (-n - 1) m.toNat r) •
              ((W.toPreVertexAlgebra.T ^ (m.toNat - r)) (W.smul c ((-n - 1) - (r : ℤ)) u)))
        else 0 := by
  by_cases hm : 0 ≤ m
  · rw [if_pos hm]
    obtain ⟨M', rfl⟩ : ∃ M' : ℕ, m = (M' : ℤ) := ⟨m.toNat, by omega⟩
    rw [show ((M' : ℤ)).toNat = M' by simp]
    have hinner : (W.Y u) (M' : ℤ) W.vacuum
        = ((M'.factorial : ℂ)⁻¹) • ((W.toPreVertexAlgebra.T ^ M') u) := by
      rw [Yk_smul, show (-(M' : ℤ) - 1) = -((M' : ℕ) : ℤ) - 1 by push_cast; ring, smul_vac_creation]
    rw [hinner, Yk_smul, PreVertexAlgebra.smul_smul_right, smul_Tpow_expand]
  · rw [if_neg hm, PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra u (by omega), map_zero]

/-- **Term1 closed form** (the `z`-dominant expansion of `Y(c,w−z)u` on the fixed `u`). -/
theorem Term1_expand (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (m n : ℤ) :
    skewCoeffFun W u m ((W.Y c) n W.vacuum)
      = if 0 ≤ n then
          ((n.toNat.factorial : ℂ)⁻¹) • (∑ᶠ j : ℕ,
            ((j.factorial : ℂ)⁻¹) • (sgn (m - j)) •
              ((∏ i ∈ Finset.range n.toNat, (-(((-(m - (j : ℤ)) - 1)) - (i : ℤ)))) •
                ((W.toPreVertexAlgebra.T ^ j)
                  (W.smul c ((-(m - (j : ℤ)) - 1) - (n.toNat : ℤ)) u))))
        else 0 := by
  by_cases hn : 0 ≤ n
  · rw [if_pos hn]
    obtain ⟨N', rfl⟩ : ∃ N' : ℕ, n = (N' : ℤ) := ⟨n.toNat, by omega⟩
    rw [show ((N' : ℤ)).toNat = N' by simp]
    have hb : (W.Y c) (N' : ℤ) W.vacuum
        = ((N'.factorial : ℂ)⁻¹) • ((W.toPreVertexAlgebra.T ^ N') c) := by
      rw [Yk_smul, show (-(N' : ℤ) - 1) = -((N' : ℕ) : ℤ) - 1 by push_cast; ring, smul_vac_creation]
    rw [hb, skewCoeffFun_smul]
    congr 1
    rw [skewCoeffFun]
    refine finsum_congr fun j => ?_
    congr 2
    rw [Yk_smul, smul_Tpow, map_zsmul]
  · rw [if_neg hn, PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra c (by omega),
      show skewCoeffFun W u m (0 : 𝒱) = (0 : 𝒱) from by
        have := (skewOp W u m).map_zero; simpa only [skewOp_apply] using this]

/-! ## §D.  The vacuum combined field and the kill. -/

noncomputable def Gfield (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) : FormalDist₂ 𝒱 :=
  fun m n => skewCoeffFun W u m ((W.Y c) n W.vacuum) - (W.Y c) n ((W.Y u) m W.vacuum)

theorem Gfield_eq (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) :
    Gfield W u c = applyVec W.vacuum (bracketDist (skewDist W u) (W.Y c)) := by
  ext m n
  rw [applyVec_bracketDist_skew_coeff, skewCoeffFun_vacuum]; rfl

/-! ### Pointwise-evaluation helpers for `FormalDist₂ 𝒱` and scalar/product casts. -/

theorem fd2_sum_apply (M : ℕ) (g : ℕ → FormalDist₂ 𝒱) (m n : ℤ) :
    (∑ s ∈ Finset.range M, g s) m n = ∑ s ∈ Finset.range M, g s m n := by
  induction M with
  | zero => rfl
  | succ k ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]; rfl

theorem fd2_smul_apply (a : ℂ) (g : FormalDist₂ 𝒱) (m n : ℤ) : (a • g) m n = a • g m n := rfl

/-- The ascending product `∏_{i<n}(a+1+i)` as a ratio of `ℕ`-factorials, cast to `ℂ`. -/
theorem asc_prod_cast (a n : ℕ) :
    (∏ i ∈ Finset.range n, ((a : ℂ) + 1 + (i : ℂ)))
      = ((a + n).factorial : ℂ) / (a.factorial : ℂ) := by
  have hN : a.factorial * (a + 1).ascFactorial n = (a + n).factorial :=
    Nat.factorial_mul_ascFactorial a n
  have hprod : ((a + 1).ascFactorial n : ℂ) = ∏ i ∈ Finset.range n, ((a : ℂ) + 1 + (i : ℂ)) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl; intro i _; push_cast; ring
  have hfac : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos a).ne'
  rw [← hprod]
  field_simp
  rw [mul_comm, ← Nat.cast_mul, hN]

/-- The falling product `fallI(−n−1, r) = ∏_{i<r}(−n−1−i)` as `(−1)^r·(n+r)!/n!`, cast to `ℂ`. -/
theorem fallI_negsucc_cast (n r : ℕ) :
    ((fallI (-(n : ℤ) - 1) r : ℤ) : ℂ)
      = (-1) ^ r * ((n + r).factorial : ℂ) / (n.factorial : ℂ) := by
  have key : (∏ i ∈ Finset.range r, ((-(n : ℤ) - 1) - (i : ℤ)))
      = (∏ i ∈ Finset.range r, ((-1 : ℤ))) * ∏ i ∈ Finset.range r, ((n : ℤ) + 1 + (i : ℤ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro i _; ring
  rw [fallI, key, Finset.prod_const, Finset.card_range]
  push_cast
  rw [asc_prod_cast n r]
  ring

/-- `gBinom(−s−1, n) = (−1)ⁿ (s+n)!/(s! n!)`. -/
theorem gBinom_negsucc (s n : ℕ) :
    gBinom (-(s : ℤ) - 1) n
      = (-1) ^ n * ((s + n).factorial : ℂ) / ((s.factorial : ℂ) * (n.factorial : ℂ)) := by
  rw [gBinom]
  have key : (∏ i ∈ Finset.range n, (((-(s : ℤ) - 1 : ℤ) : ℂ) - (i : ℂ)))
      = (∏ i ∈ Finset.range n, ((-1 : ℂ))) * ∏ i ∈ Finset.range n, ((s : ℂ) + 1 + (i : ℂ)) := by
    rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _; push_cast; ring
  rw [key, Finset.prod_const, Finset.card_range, asc_prod_cast s n]
  have hfs : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hfn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-- The singular descending product `∏_{i<n}(−n−s+i) = (−1)ⁿ (s+n)!/s!`. -/
theorem sing_prod_cast (s n : ℕ) :
    (∏ i ∈ Finset.range n, ((-(n : ℂ) - (s : ℂ)) + (i : ℂ)))
      = (-1) ^ n * ((s + n).factorial : ℂ) / (s.factorial : ℂ) := by
  have key : (∏ i ∈ Finset.range n, ((-(n : ℂ) - (s : ℂ)) + (i : ℂ)))
      = (∏ i ∈ Finset.range n, ((-1 : ℂ))) * ∏ i ∈ Finset.range n, ((n : ℂ) + (s : ℂ) - (i : ℂ)) := by
    rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _; ring
  rw [key, Finset.prod_const, Finset.card_range]
  have hrefl : (∏ i ∈ Finset.range n, ((n : ℂ) + (s : ℂ) - (i : ℂ)))
      = ∏ i ∈ Finset.range n, ((s : ℂ) + 1 + (i : ℂ)) := by
    rw [← Finset.prod_range_reflect (fun i => (s : ℂ) + 1 + (i : ℂ)) n]
    apply Finset.prod_congr rfl; intro i hi; rw [Finset.mem_range] at hi
    have hc : ((n - 1 - i : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℂ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [hc]; ring
  rw [hrefl, asc_prod_cast s n, mul_div_assoc]

/-- **Range (1) scalar identity** (`0 ≤ j ≤ m`): the `Term1` coefficient equals the `Term2`
coefficient on the shared vector `Tʲ(c₍ⱼ₋ₘ₋ₙ₋₁₎u)`. -/
theorem range1_scalar (n j m : ℕ) (hjm : j ≤ m) :
    ((n.factorial : ℂ)⁻¹) * ((j.factorial : ℂ)⁻¹) * (sgn ((m : ℤ) - (j : ℤ)))
        * (∏ i ∈ Finset.range n, ((m : ℂ) - (j : ℂ) + 1 + (i : ℂ)))
      = ((m.factorial : ℂ)⁻¹) * ((mcoeff (-(n : ℤ) - 1) m (m - j) : ℤ) : ℂ) := by
  have hmj : (m : ℤ) - (j : ℤ) = ((m - j : ℕ) : ℤ) := by omega
  have hprodL : (∏ i ∈ Finset.range n, ((m : ℂ) - (j : ℂ) + 1 + (i : ℂ)))
      = ∏ i ∈ Finset.range n, (((m - j : ℕ) : ℂ) + 1 + (i : ℂ)) := by
    apply Finset.prod_congr rfl; intro i _; push_cast [Nat.cast_sub hjm]; ring
  rw [hmj, sgn_natCast, hprodL, asc_prod_cast (m - j) n, mcoeff]
  push_cast [fallI_negsucc_cast n (m - j)]
  have h : ((m.choose (m - j) : ℂ)) * ((m - j).factorial : ℂ) * (j.factorial : ℂ)
      = (m.factorial : ℂ) := by
    have h0 := Nat.choose_mul_factorial_mul_factorial (Nat.sub_le m j)
    rw [Nat.sub_sub_self hjm] at h0
    exact_mod_cast h0
  have hfn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hfj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hfm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hfmj : ((m - j).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hnj : (m - j) + n = (m + n) - j := by omega
  rw [hnj, show n + (m - j) = m + n - j from by omega]
  field_simp
  linear_combination (-((m + n - j).factorial : ℂ)) * h

/-- **Range (3) scalar identity** (`j = m+n+s+1`, any `m`): the `Term1` coefficient equals the
jump-sum coefficient on the shared vector `Tʲ(c₍ₛ₎u)`. -/
theorem range3_scalar (m : ℤ) (n s : ℕ) :
    ((n.factorial : ℂ)⁻¹) * (sgn (m - (m + (n : ℤ) + (s : ℤ) + 1)))
        * (∏ i ∈ Finset.range n, ((m : ℂ) - ((m : ℂ) + (n : ℂ) + (s : ℂ) + 1) + 1 + (i : ℂ)))
      = ((-1 : ℂ) ^ (s + 1)) * (negOnePow (n : ℤ) * gBinom (-(s : ℤ) - 1) n) := by
  have hsgn : sgn (m - (m + (n : ℤ) + (s : ℤ) + 1)) = (-1 : ℂ) ^ (n + s + 1) := by
    rw [show m - (m + (n : ℤ) + (s : ℤ) + 1) = -(((n + s + 1 : ℕ)) : ℤ) by push_cast; ring]
    rw [show sgn (-(((n + s + 1 : ℕ)) : ℤ)) = sgn (((n + s + 1 : ℕ)) : ℤ) from by
      rw [sgn, sgn]; simp only [even_neg]]
    rw [sgn_natCast]
  have hprod : (∏ i ∈ Finset.range n, ((m : ℂ) - ((m : ℂ) + (n : ℂ) + (s : ℂ) + 1) + 1 + (i : ℂ)))
      = ∏ i ∈ Finset.range n, ((-(n : ℂ) - (s : ℂ)) + (i : ℂ)) := by
    apply Finset.prod_congr rfl; intro i _; ring
  rw [hsgn, hprod, sing_prod_cast s n, gBinom_negsucc s n, negOnePow_natCast]
  have hfs : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hfn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [show (-1 : ℂ) ^ (n + s + 1) = (-1) ^ n * (-1) ^ (s + 1) by rw [pow_add]; ring]
  field_simp

/-- `fallI(N, r) = N!/(N-r)!` for `r ≤ N` (rising/descending factorial over a nonneg base). -/
theorem fallI_natCast (N r : ℕ) (hrN : r ≤ N) :
    ((fallI (N : ℤ) r : ℤ) : ℂ) = (N.factorial : ℂ) / ((N - r).factorial : ℂ) := by
  have key : (∏ i ∈ Finset.range r, ((N : ℤ) - (i : ℤ)))
      = ((∏ i ∈ Finset.range r, ((N - i : ℕ) : ℤ))) := by
    apply Finset.prod_congr rfl; intro i hi; rw [Finset.mem_range] at hi; omega
  rw [fallI, key]; push_cast
  have hnat : (∏ i ∈ Finset.range r, (N - i)) * (N - r).factorial = N.factorial := by
    rw [← Nat.descFactorial_eq_prod_range N r, Nat.descFactorial_eq_factorial_mul_choose]
    rw [show r.factorial * N.choose r * (N - r).factorial
        = N.choose r * r.factorial * (N - r).factorial from by ring]
    exact Nat.choose_mul_factorial_mul_factorial hrN
  have hne : ((N - r).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [← Nat.cast_prod]; field_simp; rw [← Nat.cast_mul]; exact_mod_cast hnat

/-- `negOnePow` is additive (local helper, not imported here). -/
theorem negOnePow_add' (a b : ℤ) : negOnePow (a + b) = negOnePow a * negOnePow b := by
  rw [negOnePow, negOnePow, negOnePow]
  by_cases ha : Even a <;> by_cases hb : Even b
  · rw [if_pos ha, if_pos hb, if_pos (ha.add hb)]; ring
  · rw [if_pos ha, if_neg hb, if_neg (by simp [Int.even_add, ha, hb])]; ring
  · rw [if_neg ha, if_pos hb, if_neg (by simp [Int.even_add, ha, hb])]; ring
  · rw [if_neg ha, if_neg hb, if_pos (by simp [Int.even_add, ha, hb])]; ring

theorem negOnePow_neg' (a : ℤ) : negOnePow (-a) = negOnePow a := by
  rw [negOnePow, negOnePow]; simp only [even_neg]

/-- The jump value on the antidiagonal for `n = -(N+1) < 0`, when `s ≤ N` (`expandNeg` branch). -/
theorem negPowJump_antidiag_neg (N s : ℕ) (hsN : s ≤ N) :
    negPowJump s ((N : ℤ) - (s : ℤ)) (-((N : ℤ) + 1))
      = - negOnePow ((-(s : ℤ) - 1) + ((N : ℤ) - (s : ℤ))) * gBinom (-(s : ℤ) - 1) (N - s) := by
  show expandPos (-(s : ℤ) - 1) ((N : ℤ) - (s : ℤ)) (-((N : ℤ) + 1))
      - expandNeg (-(s : ℤ) - 1) ((N : ℤ) - (s : ℤ)) (-((N : ℤ) + 1)) = _
  rw [expandPos_apply, expandNeg_apply,
    if_neg (by rintro ⟨h, _⟩; omega), if_pos ⟨by omega, by ring⟩, zero_sub,
    show ((N : ℤ) - (s : ℤ)).toNat = N - s from by omega]
  ring

/-- For `n = -(N+1) < 0` and `s > N`, the jump value vanishes. -/
theorem negPowJump_antidiag_neg_zero (N s : ℕ) (hsN : N < s) :
    negPowJump s ((N : ℤ) - (s : ℤ)) (-((N : ℤ) + 1)) = 0 := by
  show expandPos (-(s : ℤ) - 1) ((N : ℤ) - (s : ℤ)) (-((N : ℤ) + 1))
      - expandNeg (-(s : ℤ) - 1) ((N : ℤ) - (s : ℤ)) (-((N : ℤ) + 1)) = _
  rw [expandPos_apply, expandNeg_apply,
    if_neg (by rintro ⟨h, _⟩; omega), if_neg (by rintro ⟨h, _⟩; omega), sub_zero]

/-- **The `n < 0` scalar identity**: `−Term2`-coeff = jump-coeff on the shared vector
(`n = -(N+1)`, `m ≥ 0`, `r = N − s`). -/
theorem nneg_scalar (m N r : ℕ) (hrm : r ≤ m) (hrN : r ≤ N) :
    -(((m.factorial : ℂ)⁻¹) * ((mcoeff (N : ℤ) m r : ℤ) : ℂ))
      = ((-1 : ℂ) ^ ((N - r) + 1))
        * (- negOnePow ((-((N : ℤ) - (r : ℤ)) - 1) + (r : ℤ)) * gBinom (-((N : ℤ) - (r : ℤ)) - 1) r)
        * ((m - r).factorial : ℂ)⁻¹ := by
  rw [mcoeff]; push_cast; rw [fallI_natCast N r hrN]
  rw [show -((N : ℤ) - (r : ℤ)) - 1 = -(((N - r : ℕ)) : ℤ) - 1 by push_cast [Nat.cast_sub hrN]; ring]
  rw [gBinom_negsucc (N - r) r, show (N - r) + r = N from by omega]
  have hsign : negOnePow ((-(((N - r : ℕ)) : ℤ) - 1) + (r : ℤ))
      = (-1 : ℂ) ^ (N - r + 1) * (-1 : ℂ) ^ r := by
    rw [show (-(((N - r : ℕ)) : ℤ) - 1) + (r : ℤ) = (-(((N - r + 1 : ℕ)) : ℤ)) + (r : ℤ) by
      push_cast; ring]
    rw [negOnePow_add', negOnePow_neg', negOnePow_natCast, negOnePow_natCast]
  rw [hsign]
  have hch : ((m.choose r : ℂ)) * (r.factorial : ℂ) * ((m - r).factorial : ℂ) = (m.factorial : ℂ) := by
    have h0 := Nat.choose_mul_factorial_mul_factorial hrm; exact_mod_cast h0
  have hfm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hfr : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hfNr : (((N - r : ℕ)).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hfmr : (((m - r : ℕ)).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp
  rw [show (((-1 : ℂ) ^ (N - r + 1)) ^ 2) = 1 from by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      show (((-1 : ℂ) ^ r) ^ 2) = 1 from by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      mul_one, mul_one]
  linear_combination (-((N : ℕ).factorial : ℂ)) * hch

/-- Drop a membership constraint on a `finsum` when the support is contained in the set. -/
theorem finsum_mem_of_support_subset' (F : ℤ → 𝒱) (s : Set ℤ)
    (h : Function.support F ⊆ s) : (∑ᶠ i ∈ s, F i) = ∑ᶠ i, F i := by
  rw [← finsum_mem_inter_support F s, ← finsum_mem_univ (f := F),
    ← finsum_mem_inter_support F Set.univ, Set.univ_inter, Set.inter_eq_right.mpr h]

/-- Reindex a `ℕ`-`finsum` to a `ℤ`-`finsum` via an extension `F` vanishing on negatives. -/
theorem finsum_nat_to_int (g : ℕ → 𝒱) (F : ℤ → 𝒱)
    (hF0 : ∀ p : ℤ, p < 0 → F p = 0) (hFg : ∀ j : ℕ, F (j : ℤ) = g j) :
    (∑ᶠ j : ℕ, g j) = ∑ᶠ p : ℤ, F p := by
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ)) := fun a b h => by simpa using h
  have hsub : Function.support F ⊆ Set.range (fun j : ℕ => (j : ℤ)) := by
    intro p hp
    rw [Function.mem_support] at hp
    rcases lt_or_ge p 0 with hlt | hge
    · exact absurd (hF0 p hlt) hp
    · exact ⟨p.toNat, by simp [Int.toNat_of_nonneg hge]⟩
  rw [← finsum_mem_of_support_subset' F _ hsub, finsum_mem_range hinj]
  exact (finsum_congr fun j => (hFg j).symm)

/-- `creS` vanishes at a negative index (creation has no negative powers). -/
theorem creS_neg (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (s : ℕ) {k : ℤ} (hk : k < 0) :
    creS W u c s k = 0 := by
  rw [creS]; exact PreVertexAlgebra.Y_apply_vacuum_eq_zero W.toPreVertexAlgebra _ hk

/-- The middle/regular term vanishes whenever `m+1 ≤ j ≤ m+n` (general `m : ℤ`). -/
theorem termj_zero_of_mid (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (m : ℤ) (n' j : ℕ)
    (hj1 : m + 1 ≤ (j : ℤ)) (hj2 : (j : ℤ) ≤ m + n') :
    ((n'.factorial : ℂ)⁻¹) • ((j.factorial : ℂ)⁻¹) • (sgn (m - (j : ℤ))) •
        ((∏ i ∈ Finset.range n', (-(((-((m) - (j : ℤ)) - 1)) - (i : ℤ)))) •
          ((W.toPreVertexAlgebra.T ^ j) (W.smul c ((-((m) - (j : ℤ)) - 1) - (n' : ℤ)) u)))
      = 0 := by
  have hzero : (∏ i ∈ Finset.range n', (-(((-((m) - (j : ℤ)) - 1)) - (i : ℤ)))) = 0 := by
    apply Finset.prod_eq_zero (i := (j - (m + 1)).toNat)
    · rw [Finset.mem_range]; omega
    · rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ j - (m + 1))]; ring
  rw [hzero, zero_smul, smul_zero, smul_zero, smul_zero]

/-- The creation form of `creS` at a nonnegative index `k`. -/
theorem creS_creation (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (s k : ℕ) :
    creS W u c s (k : ℤ)
      = ((k.factorial : ℂ)⁻¹) • ((W.toPreVertexAlgebra.T ^ k) (W.smul c (s : ℤ) u)) := by
  rw [creS, Yk_smul, show (-(k : ℤ) - 1) = -((k : ℕ) : ℤ) - 1 by push_cast; ring, smul_vac_creation]

/-- The jump value on the antidiagonal for `n ≥ 0`: `Jₛ(−n−s−1, n) = (−1)ⁿ·C(−s−1, n)`. -/
theorem negPowJump_antidiag_pos (s n : ℕ) :
    negPowJump s (-(n : ℤ) - (s : ℤ) - 1) (n : ℤ) = negOnePow (n : ℤ) * gBinom (-(s : ℤ) - 1) n := by
  show expandPos (-(s : ℤ) - 1) (-(n : ℤ) - (s : ℤ) - 1) (n : ℤ)
      - expandNeg (-(s : ℤ) - 1) (-(n : ℤ) - (s : ℤ) - 1) (n : ℤ) = _
  rw [expandPos_apply, expandNeg_apply, if_pos ⟨by positivity, by ring⟩,
    if_neg (by rintro ⟨h, _⟩; omega), sub_zero, Int.toNat_natCast]

/-- The `Term1` summand has support inside `range (M + m' + n' + 1)` (regularity). -/
theorem term1_supp (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (m' n' M : ℕ)
    (hM : ∀ s : ℤ, (M : ℤ) ≤ s → W.smul c s u = 0) :
    Function.support (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • (sgn ((m' : ℤ) - (j : ℤ))) •
        ((∏ i ∈ Finset.range n', (-(((-(((m' : ℤ)) - (j : ℤ)) - 1)) - (i : ℤ)))) •
          ((W.toPreVertexAlgebra.T ^ j) (W.smul c ((-(((m' : ℤ)) - (j : ℤ)) - 1) - (n' : ℤ)) u))))
      ⊆ Finset.range (M + m' + n' + 1) := by
  intro j hj
  rw [Function.mem_support] at hj
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hjge
  rw [not_lt] at hjge
  apply hj
  have hsmul : W.smul c ((-(((m' : ℤ)) - (j : ℤ)) - 1) - (n' : ℤ)) u = 0 := by
    rw [show (-(((m' : ℤ)) - (j : ℤ)) - 1) - (n' : ℤ) = (j : ℤ) - m' - n' - 1 by ring]
    exact hM _ (by omega)
  rw [hsmul, map_zero, smul_zero, smul_zero, smul_zero]

/-- The `Term1` summand support, with a general `m : ℤ` bound. -/
theorem term1_supp_int (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (m : ℤ) (n' M B : ℕ)
    (hM : ∀ s : ℤ, (M : ℤ) ≤ s → W.smul c s u = 0) (hB : (M : ℤ) + m + n' + 1 ≤ B) :
    Function.support (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • (sgn ((m) - (j : ℤ))) •
        ((∏ i ∈ Finset.range n', (-(((-((m) - (j : ℤ)) - 1)) - (i : ℤ)))) •
          ((W.toPreVertexAlgebra.T ^ j) (W.smul c ((-((m) - (j : ℤ)) - 1) - (n' : ℤ)) u))))
      ⊆ Finset.range B := by
  intro j hj
  rw [Function.mem_support] at hj
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hjge
  rw [not_lt] at hjge
  apply hj
  have hsmul : W.smul c ((-((m) - (j : ℤ)) - 1) - (n' : ℤ)) u = 0 := by
    rw [show (-((m) - (j : ℤ)) - 1) - (n' : ℤ) = (j : ℤ) - m - n' - 1 by ring]
    exact hM _ (by omega)
  rw [hsmul, map_zero, smul_zero, smul_zero, smul_zero]

/-- **Range (2) vanishes**: the middle `m' < j ≤ m'+n'` terms are zero (zero falling factor). -/
theorem range2_term_zero (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (m' n' j : ℕ)
    (hj1 : m' + 1 ≤ j) (hj2 : j ≤ m' + n') :
    ((n'.factorial : ℂ)⁻¹) • ((j.factorial : ℂ)⁻¹) • (sgn ((m' : ℤ) - (j : ℤ))) •
        ((∏ i ∈ Finset.range n', (-(((-(((m' : ℤ)) - (j : ℤ)) - 1)) - (i : ℤ)))) •
          ((W.toPreVertexAlgebra.T ^ j) (W.smul c ((-(((m' : ℤ)) - (j : ℤ)) - 1) - (n' : ℤ)) u)))
      = 0 := by
  have hzero : (∏ i ∈ Finset.range n', (-(((-(((m' : ℤ)) - (j : ℤ)) - 1)) - (i : ℤ)))) = 0 := by
    apply Finset.prod_eq_zero (i := j - m' - 1)
    · rw [Finset.mem_range]; omega
    · have hc : ((j - m' - 1 : ℕ) : ℤ) = (j : ℤ) - (m' : ℤ) - 1 := by omega
      rw [hc]; ring
  rw [hzero, zero_smul, smul_zero, smul_zero, smul_zero]

/-- **Range (1) = Term2**: the regular `0 ≤ j ≤ m'` block equals the `Term2` expansion. -/
theorem range1_eq_term2 (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (m' n' : ℕ) :
    (∑ j ∈ Finset.range (m' + 1),
       ((n'.factorial : ℂ)⁻¹) • ((j.factorial : ℂ)⁻¹) • (sgn ((m' : ℤ) - (j : ℤ))) •
        ((∏ i ∈ Finset.range n', (-(((-(((m' : ℤ)) - (j : ℤ)) - 1)) - (i : ℤ)))) •
          ((W.toPreVertexAlgebra.T ^ j) (W.smul c ((-(((m' : ℤ)) - (j : ℤ)) - 1) - (n' : ℤ)) u))))
      = ((m'.factorial : ℂ)⁻¹) • (∑ r ∈ Finset.range (m' + 1),
            (mcoeff (-(n' : ℤ) - 1) m' r) •
              ((W.toPreVertexAlgebra.T ^ (m' - r)) (W.smul c ((-(n' : ℤ) - 1) - (r : ℤ)) u))) := by
  rw [Finset.smul_sum]
  rw [← Finset.sum_range_reflect (fun r =>
        ((m'.factorial : ℂ)⁻¹) • (mcoeff (-(n' : ℤ) - 1) m' r) •
          ((W.toPreVertexAlgebra.T ^ (m' - r)) (W.smul c ((-(n' : ℤ) - 1) - (r : ℤ)) u))) (m' + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show m' + 1 - 1 - j = m' - j from by omega]
  have hpow : m' - (m' - j) = j := by omega
  have hmode : (-(n' : ℤ) - 1) - ((m' - j : ℕ) : ℤ) = (-(((m' : ℤ)) - (j : ℤ)) - 1) - (n' : ℤ) := by
    have hcast : ((m' - j : ℕ) : ℤ) = (m' : ℤ) - (j : ℤ) := by omega
    rw [hcast]; ring
  rw [hpow, hmode]
  rw [← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range n', (-(((-(((m' : ℤ)) - (j : ℤ)) - 1)) - (i : ℤ)))),
      ← Int.cast_smul_eq_zsmul ℂ (mcoeff (-(n' : ℤ) - 1) m' (m' - j))]
  rw [smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  have hprodC : ((∏ i ∈ Finset.range n', (-(((-(((m' : ℤ)) - (j : ℤ)) - 1)) - (i : ℤ)))) : ℤ)
      = (((∏ i ∈ Finset.range n', ((m' : ℂ) - (j : ℂ) + 1 + (i : ℂ))) : ℂ)) := by
    push_cast; apply Finset.prod_congr rfl; intro i _; push_cast; ring
  rw [hprodC]
  have hsc := range1_scalar n' j m' (by omega)
  rw [mcoeff] at hsc ⊢
  push_cast at hsc ⊢
  linear_combination hsc

/-- **Range (3) = jump-sum** (general `m : ℤ` with `0 ≤ m+n'+1`): the singular tail
`j ∈ [(m+n'+1), (m+n'+1)+M)` equals the jump-sum (`n ≥ 0`). -/
theorem range3_eq_jumpsum (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (m : ℤ) (n' M : ℕ)
    (hLo : 0 ≤ m + n' + 1) :
    (∑ j ∈ Finset.Ico (m + n' + 1).toNat (M + (m + n' + 1).toNat),
       ((n'.factorial : ℂ)⁻¹) • ((j.factorial : ℂ)⁻¹) • (sgn ((m) - (j : ℤ))) •
        ((∏ i ∈ Finset.range n', (-(((-((m) - (j : ℤ)) - 1)) - (i : ℤ)))) •
          ((W.toPreVertexAlgebra.T ^ j) (W.smul c ((-((m) - (j : ℤ)) - 1) - (n' : ℤ)) u))))
      = ∑ s ∈ Finset.range M,
          ((-1 : ℂ) ^ (s + 1)) •
            (negPowJump s (-(n' : ℤ) - (s : ℤ) - 1) (n' : ℤ) • creS W u c s (m + n' + (s : ℤ) + 1)) := by
  rw [Finset.sum_Ico_eq_sum_range,
    show (M + (m + n' + 1).toNat) - (m + n' + 1).toNat = M from by omega]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_range] at hs
  set Lo := (m + n' + 1).toNat with hLodef
  set j := Lo + s with hj
  have hjcast : (j : ℤ) = m + n' + 1 + s := by
    rw [hj]; push_cast [hLodef, Int.toNat_of_nonneg hLo]; ring
  have hmode : (-((m) - (j : ℤ)) - 1) - (n' : ℤ) = (s : ℤ) := by rw [hjcast]; ring
  rw [hmode]
  have hidx : m + n' + (s : ℤ) + 1 = (j : ℤ) := by rw [hjcast]; ring
  rw [hidx, show ((j : ℤ)) = ((j : ℕ) : ℤ) from rfl, creS_creation W u c s j]
  rw [negPowJump_antidiag_pos s n']
  rw [← Int.cast_smul_eq_zsmul ℂ (∏ i ∈ Finset.range n', (-(((-((m) - (j : ℤ)) - 1)) - (i : ℤ))))]
  rw [smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  have hprodC : ((∏ i ∈ Finset.range n', (-(((-((m) - (j : ℤ)) - 1)) - (i : ℤ)))) : ℤ)
      = (((∏ i ∈ Finset.range n', ((m : ℂ) - ((m : ℂ) + (n' : ℂ) + (s : ℂ) + 1) + 1 + (i : ℂ))) : ℂ)) := by
    push_cast [hjcast]; apply Finset.prod_congr rfl; intro i _; push_cast [hjcast]; ring
  rw [hprodC]
  have hsc := range3_scalar m n' s
  have hsgnarg : ((m) - (j : ℤ)) = ((m) - ((m) + (n' : ℤ) + (s : ℤ) + 1)) := by rw [hjcast]; ring
  rw [hsgnarg]
  field_simp
  linear_combination ((j.factorial : ℂ)⁻¹) * hsc

/-- **THE CORE IDENTITY** (honest, non-circular): the vacuum combined field is the explicit
finite jump-sum over the FIXED creation columns of `c₍ₛ₎u`.

Both `Term1` (`= skewCoeffFun u m ((Y c)ₙ𝟙)`, the `z`-dominant expansion, `Term1_expand`) and
`Term2` (`= (Y c)ₙ((Y u)ₘ𝟙)`, the `w`-dominant expansion, `Term2_expand`) are in explicit
closed form as sums of `Tᵃ(c₍ₚ₎u)`.  Reindexing both by the `c`-mode `p` (both contribute
`Tᵖ⁺ᵐ⁺ⁿ⁺¹(c₍ₚ₎u)`), the difference is the jump-sum: the per-`p` scalar identity
  • `p<0`:  Term1-coeff(p) = Term2-coeff(p)  (regular cancellation; RHS = 0);
  • `p≥0`:  Term1-coeff(p) − Term2-coeff(p) = (−1)^{p+1}(p+n)!/(n! p! (p+m+n+1)!),
matching `(−1)^{s+1}·vconv(creS s)(negPowJump s)` via `vconv_negPowJump_single` +
`negPowJump_single_coeff` + `creation_pow`, with `c₍ₚ₎u = 0` for `p ≥ M` (regularity).  Verified
exhaustively in Mathematica (commutative + free-boson VOAs, and abstractly over independent
`Tᵃ(c₍ₚ₎u)`). -/
theorem Gfield_eq_jumpSum (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) {M : ℕ}
    (hM : ∀ s : ℤ, (M : ℤ) ≤ s → W.smul c s u = 0) :
    Gfield W u c
      = ∑ s ∈ Finset.range M, ((-1 : ℂ) ^ (s + 1)) • vconv (creS W u c s) (negPowJump s) := by
  funext m n
  -- Evaluate the RHS pointwise.
  rw [fd2_sum_apply]
  have hRHS : ∀ s ∈ Finset.range M,
      (((-1 : ℂ) ^ (s + 1)) • vconv (creS W u c s) (negPowJump s)) m n
        = ((-1 : ℂ) ^ (s + 1)) •
            (negPowJump s (-n - (s:ℤ) - 1) n • creS W u c s (m + n + (s:ℤ) + 1)) := by
    intro s _
    rw [fd2_smul_apply, vconv_negPowJump_single]
    congr 2
    ring_nf
  rw [Finset.sum_congr rfl hRHS]
  show skewCoeffFun W u m ((W.Y c) n W.vacuum) - (W.Y c) n ((W.Y u) m W.vacuum) = _
  by_cases hn : 0 ≤ n
  · -- ============ n ≥ 0 ============
    obtain ⟨n', rfl⟩ : ∃ n' : ℕ, n = (n' : ℤ) := ⟨n.toNat, by omega⟩
    rw [Term1_expand, if_pos hn, show ((n' : ℤ)).toNat = n' by simp]
    by_cases hm : 0 ≤ m
    · -- n ≥ 0, m ≥ 0 : full three-way j-split.
      obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = (m' : ℤ) := ⟨m.toNat, by omega⟩
      rw [Term2_expand, if_pos hm, show ((m' : ℤ)).toNat = m' by simp]
      rw [finsum_eq_sum_of_support_subset _ (term1_supp W u c m' n' M hM), Finset.smul_sum]
      -- split range into [0,m'] ∪ (m',m'+n'] ∪ (m'+n', B)
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive _ (Nat.zero_le (m' + 1)) (by omega : m' + 1 ≤ M + m' + n' + 1),
        ← Finset.sum_Ico_consecutive _ (by omega : m' + 1 ≤ m' + n' + 1)
          (by omega : m' + n' + 1 ≤ M + m' + n' + 1), ← Finset.range_eq_Ico]
      -- middle block vanishes
      have hmid : (∑ j ∈ Finset.Ico (m' + 1) (m' + n' + 1),
          ((n'.factorial : ℂ)⁻¹) • ((j.factorial : ℂ)⁻¹) • (sgn ((m' : ℤ) - (j : ℤ))) •
            ((∏ i ∈ Finset.range n', (-(((-(((m' : ℤ)) - (j : ℤ)) - 1)) - (i : ℤ)))) •
              ((W.toPreVertexAlgebra.T ^ j)
                (W.smul c ((-(((m' : ℤ)) - (j : ℤ)) - 1) - (n' : ℤ)) u)))) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [Finset.mem_Ico] at hj
        exact range2_term_zero W u c m' n' j hj.1 (by omega)
      rw [hmid, range1_eq_term2 W u c m' n']
      rw [show M + m' + n' + 1 = M + ((m' : ℤ) + n' + 1).toNat from by omega,
          show m' + n' + 1 = ((m' : ℤ) + n' + 1).toNat from by omega]
      rw [range3_eq_jumpsum W u c (m' : ℤ) n' M (by positivity)]
      abel
    · -- n ≥ 0, m < 0 : Term2 = 0, range1 empty.
      rw [Term2_expand, if_neg hm, sub_zero]
      rw [finsum_eq_sum_of_support_subset _
        (term1_supp_int W u c m n' M (M + (m + n' + 1).toNat) hM (by omega)), Finset.smul_sum]
      by_cases hmn : 0 ≤ m + n' + 1
      · -- (a) -n'-1 ≤ m < 0 : leading [0, Lo) vanishes, tail = jumpSum.
        rw [show (M + (m + n' + 1).toNat) = (m + n' + 1).toNat + (M - 0) by omega] at *
        rw [Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive _ (Nat.zero_le (m + n' + 1).toNat)
            (by omega : (m + n' + 1).toNat ≤ (m + n' + 1).toNat + (M - 0))]
        have hlead : (∑ j ∈ Finset.Ico 0 (m + n' + 1).toNat,
            ((n'.factorial : ℂ)⁻¹) • ((j.factorial : ℂ)⁻¹) • (sgn ((m) - (j : ℤ))) •
              ((∏ i ∈ Finset.range n', (-(((-((m) - (j : ℤ)) - 1)) - (i : ℤ)))) •
                ((W.toPreVertexAlgebra.T ^ j)
                  (W.smul c ((-((m) - (j : ℤ)) - 1) - (n' : ℤ)) u)))) = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          rw [Finset.mem_Ico] at hj
          exact termj_zero_of_mid W u c m n' j (by omega) (by omega)
        rw [hlead, zero_add, show (m + n' + 1).toNat + (M - 0) = M + (m + n' + 1).toNat by omega]
        exact range3_eq_jumpsum W u c m n' M hmn
      · -- (b) m ≤ -n'-2 : Lo = 0; whole range = jump-sum tail; leading jump-sum zeros.
        rw [show (m + n' + 1).toNat = 0 from by omega, Nat.add_zero]
        set d : ℕ := (-(m + n' + 1)).toNat with hd
        -- The jump-sum's leading `s < d` terms all vanish (negative creation index).
        have hjlead : ∀ s ∈ Finset.range d,
            ((-1 : ℂ) ^ (s + 1)) •
              (negPowJump s (-(n' : ℤ) - (s : ℤ) - 1) (n' : ℤ) • creS W u c s (m + n' + (s : ℤ) + 1))
              = 0 := by
          intro s hs
          rw [Finset.mem_range] at hs
          have hdval : ((d : ℤ)) = -(m + n' + 1) := by
            rw [hd]; exact Int.toNat_of_nonneg (by omega)
          rw [creS_neg W u c s (by omega : m + n' + (s : ℤ) + 1 < 0), smul_zero, smul_zero]
        by_cases hdM : M ≤ d
        · -- everything is zero: Term1 support empty, jump-sum all leading zeros.
          have hzr : (∑ s ∈ Finset.range M,
              ((-1 : ℂ) ^ (s + 1)) • (negPowJump s (-(n' : ℤ) - (s : ℤ) - 1) (n' : ℤ)
                • creS W u c s (m + n' + (s : ℤ) + 1))) = 0 :=
            Finset.sum_eq_zero (fun s hs => hjlead s (Finset.mem_range.mpr
              (lt_of_lt_of_le (Finset.mem_range.mp hs) hdM)))
          have hzl : (∑ j ∈ Finset.range M, ((n'.factorial : ℂ)⁻¹) • ((j.factorial : ℂ)⁻¹) •
              (sgn ((m) - (j : ℤ))) •
              ((∏ i ∈ Finset.range n', (-(((-((m) - (j : ℤ)) - 1)) - (i : ℤ)))) •
                ((W.toPreVertexAlgebra.T ^ j)
                  (W.smul c ((-((m) - (j : ℤ)) - 1) - (n' : ℤ)) u)))) = 0 := by
            refine Finset.sum_eq_zero fun j hj => ?_
            rw [Finset.mem_range] at hj
            have hdval : ((d : ℤ)) = -(m + n' + 1) := by
              rw [hd]; exact Int.toNat_of_nonneg (by omega)
            have hsmul : W.smul c ((-((m) - (j : ℤ)) - 1) - (n' : ℤ)) u = 0 := by
              rw [show (-((m) - (j : ℤ)) - 1) - (n' : ℤ) = (j : ℤ) - m - n' - 1 by ring]
              exact hM _ (by omega)
            rw [hsmul, map_zero, smul_zero, smul_zero, smul_zero, smul_zero]
          rw [hzr, hzl]
        rw [not_le] at hdM
        -- jump-sum: drop the `d` leading zeros, then reindex to `range (M - d)`.
        have hrhs : (∑ s ∈ Finset.range M,
            ((-1 : ℂ) ^ (s + 1)) • (negPowJump s (-(n' : ℤ) - (s : ℤ) - 1) (n' : ℤ)
              • creS W u c s (m + n' + (s : ℤ) + 1)))
            = ∑ t ∈ Finset.range (M - d),
                ((-1 : ℂ) ^ ((d + t) + 1)) •
                  (negPowJump (d + t) (-(n' : ℤ) - ((d + t : ℕ) : ℤ) - 1) (n' : ℤ)
                    • creS W u c (d + t) (m + n' + ((d + t : ℕ) : ℤ) + 1)) := by
          rw [← Finset.sum_range_add_sum_Ico _ (by omega : d ≤ M),
            Finset.sum_eq_zero hjlead, zero_add, Finset.sum_Ico_eq_sum_range]
        rw [hrhs]
        -- Term1: trailing `j ≥ M - d` terms vanish (regularity), restrict to `range (M - d)`.
        rw [show M = (M - d) + d from by omega, Finset.sum_range_add]
        rw [show (∑ x ∈ Finset.range d, ((n'.factorial : ℂ)⁻¹) • ((((M - d) + x).factorial : ℂ)⁻¹) •
              (sgn ((m) - (((M - d) + x : ℕ) : ℤ))) •
              ((∏ i ∈ Finset.range n', (-(((-((m) - (((M - d) + x : ℕ) : ℤ)) - 1)) - (i : ℤ)))) •
                ((W.toPreVertexAlgebra.T ^ ((M - d) + x))
                  (W.smul c ((-((m) - (((M - d) + x : ℕ) : ℤ)) - 1) - (n' : ℤ)) u)))) = 0 from ?_]
        · rw [add_zero, show M - d + d - d = M - d from by omega]
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mem_range] at ht
          -- match G(t) with RHSterm(d+t).  c-mode j-m-n'-1 with j=t equals d+t (=s).
          have hjcast : ((d + t : ℕ) : ℤ) = (t : ℤ) - (m + n' + 1) := by
            rw [hd]; push_cast [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -(m + n' + 1))]; ring
          have hmode : (-((m) - (t : ℤ)) - 1) - (n' : ℤ) = ((d + t : ℕ) : ℤ) := by
            rw [hjcast]; ring
          rw [hmode]
          have hidx : m + n' + ((d + t : ℕ) : ℤ) + 1 = (t : ℤ) := by rw [hjcast]; ring
          rw [hidx, show ((t : ℤ)) = ((t : ℕ) : ℤ) from rfl, creS_creation W u c (d + t) t]
          rw [negPowJump_antidiag_pos (d + t) n']
          rw [← Int.cast_smul_eq_zsmul ℂ
            (∏ i ∈ Finset.range n', (-(((-((m) - (t : ℤ)) - 1)) - (i : ℤ))))]
          rw [smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
          congr 1
          have hjcastC : ((d : ℂ) + (t : ℂ)) = (t : ℂ) - ((m : ℂ) + (n' : ℂ) + 1) := by
            have h := hjcast; push_cast at h
            have : ((d : ℂ) + (t : ℂ)) = ((t : ℂ) - (m + n' + 1)) := by exact_mod_cast h
            linear_combination this
          have hprodC : ((∏ i ∈ Finset.range n', (-(((-((m) - (t : ℤ)) - 1)) - (i : ℤ)))) : ℤ)
              = (((∏ i ∈ Finset.range n', ((m : ℂ) - ((m : ℂ) + (n' : ℂ) + ((d + t : ℕ) : ℂ) + 1) + 1 + (i : ℂ))) : ℂ)) := by
            push_cast; rw [hjcastC]; apply Finset.prod_congr rfl; intro i _; ring
          rw [hprodC]
          have hsc := range3_scalar m n' (d + t)
          have hsgnarg : ((m) - (t : ℤ)) = ((m) - ((m) + (n' : ℤ) + ((d + t : ℕ) : ℤ) + 1)) := by
            rw [hjcast]; ring
          rw [hsgnarg]
          field_simp
          linear_combination ((t.factorial : ℂ)⁻¹) * hsc
        · refine Finset.sum_eq_zero fun x hx => ?_
          rw [Finset.mem_range] at hx
          have hsmul : W.smul c ((-((m) - (((M - d) + x : ℕ) : ℤ)) - 1) - (n' : ℤ)) u = 0 := by
            rw [show (-((m) - (((M - d) + x : ℕ) : ℤ)) - 1) - (n' : ℤ)
                = (((M - d) + x : ℕ) : ℤ) - m - n' - 1 by ring]
            refine hM _ ?_
            have : ((M - d : ℕ) : ℤ) = (M : ℤ) - d := by omega
            rw [hd] at this ⊢
            push_cast [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -(m + n' + 1))] at this ⊢
            omega
          rw [hsmul, map_zero, smul_zero, smul_zero, smul_zero, smul_zero]
  · -- ============ n < 0 : Term1 = 0, need −Term2 = jumpSum ============
    rw [Term1_expand, if_neg hn, zero_sub]
    obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = -((N : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
    by_cases hm : 0 ≤ m
    · -- n < 0, m ≥ 0 : reindex Term2 (r) ↔ jump-sum (s) via s = N − r.
      obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = (m' : ℤ) := ⟨m.toNat, by omega⟩
      rw [Term2_expand, if_pos hm, show ((m' : ℤ)).toNat = m' by simp,
        show (-(-((N : ℤ) + 1)) - 1) = (N : ℤ) by ring, Finset.smul_sum, ← Finset.sum_neg_distrib]
      -- Both sides reduce to a sum over the common index set `r ∈ [0, min(m',N)]`.
      -- LHS: terms with `r > N` vanish (`fallI N r = 0`).
      have hLrestrict : (∑ r ∈ Finset.range (m' + 1),
            -(((m'.factorial : ℂ)⁻¹) • ((mcoeff (N : ℤ) m' r) •
              ((W.toPreVertexAlgebra.T ^ (m' - r)) (W.smul c ((N : ℤ) - (r : ℤ)) u)))))
          = ∑ r ∈ Finset.range (min m' N + 1),
            -(((m'.factorial : ℂ)⁻¹) • ((mcoeff (N : ℤ) m' r) •
              ((W.toPreVertexAlgebra.T ^ (m' - r)) (W.smul c ((N : ℤ) - (r : ℤ)) u)))) := by
        refine (Finset.sum_subset (by
          intro x hx; rw [Finset.mem_range] at hx ⊢; omega) (fun r hr hrn => ?_)).symm
        rw [Finset.mem_range] at hr hrn
        have hrN : N < r := by omega
        rw [mcoeff, show fallI (N : ℤ) r = 0 from by
          rw [fallI]; exact Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : N < r)) (by simp)]
        simp
      rw [hLrestrict]
      -- Further restrict LHS to `r ≥ N + 1 - M` (regularity: `c₍N₋r₎u = 0` when `N − r ≥ M`).
      have hLrestrict2 : (∑ r ∈ Finset.range (min m' N + 1),
            -(((m'.factorial : ℂ)⁻¹) • ((mcoeff (N : ℤ) m' r) •
              ((W.toPreVertexAlgebra.T ^ (m' - r)) (W.smul c ((N : ℤ) - (r : ℤ)) u)))))
          = ∑ r ∈ Finset.Ico (N + 1 - M) (min m' N + 1),
            -(((m'.factorial : ℂ)⁻¹) • ((mcoeff (N : ℤ) m' r) •
              ((W.toPreVertexAlgebra.T ^ (m' - r)) (W.smul c ((N : ℤ) - (r : ℤ)) u)))) := by
        refine (Finset.sum_subset (by
          intro x hx; rw [Finset.mem_Ico] at hx; rw [Finset.mem_range]; omega)
          (fun r hr hrn => ?_)).symm
        rw [Finset.mem_range] at hr; rw [Finset.mem_Ico] at hrn
        have hreg : W.smul c ((N : ℤ) - (r : ℤ)) u = 0 := hM _ (by omega)
        rw [hreg, map_zero, smul_zero, smul_zero, neg_zero]
      rw [hLrestrict2]
      -- RHS: restrict jump-sum to `s ∈ Ico (N − min m' N) (min (N+1) M)`; everything else is zero.
      have hRrestrict : (∑ s ∈ Finset.range M,
            ((-1 : ℂ) ^ (s + 1)) •
              (negPowJump s (-(-((N : ℤ) + 1)) - (s : ℤ) - 1) (-((N : ℤ) + 1))
                • creS W u c s (m' + (-((N : ℤ) + 1)) + (s : ℤ) + 1)))
          = ∑ s ∈ Finset.Ico (N - min m' N) (min (N + 1) M),
            ((-1 : ℂ) ^ (s + 1)) •
              (negPowJump s (-(-((N : ℤ) + 1)) - (s : ℤ) - 1) (-((N : ℤ) + 1))
                • creS W u c s (m' + (-((N : ℤ) + 1)) + (s : ℤ) + 1)) := by
        refine (Finset.sum_subset (by
          intro x hx; rw [Finset.mem_Ico] at hx; rw [Finset.mem_range]; omega)
          (fun s hs hsn => ?_)).symm
        rw [Finset.mem_range] at hs; rw [Finset.mem_Ico] at hsn
        push_neg at hsn
        by_cases hsN : N < s
        · rw [show (-(-((N : ℤ) + 1)) - (s : ℤ) - 1) = (N : ℤ) - (s : ℤ) by ring,
            negPowJump_antidiag_neg_zero N s hsN, zero_smul, smul_zero]
        · rw [creS_neg W u c s (by
            have : m' < N - s := by omega
            omega : m' + (-((N : ℤ) + 1)) + (s : ℤ) + 1 < 0), smul_zero, smul_zero]
      rw [hRrestrict]
      -- Bridging facts so `omega` can see through the `min`s and the `ℕ`-subtractions.
      have hbN : min m' N ≤ N := min_le_right _ _
      have hbm : min m' N ≤ m' := min_le_left _ _
      have hbridge : N - min m' N + min m' N = N := Nat.sub_add_cancel hbN
      have hbNM1 : min (N + 1) M ≤ N + 1 := min_le_left _ _
      have hbNM2 : min (N + 1) M ≤ M := min_le_right _ _
      have hminm : ∀ a, a ≤ m' → a ≤ N → a ≤ min m' N := fun a h1 h2 => le_min h1 h2
      have hminM : ∀ a, a ≤ N + 1 → a ≤ M → a ≤ min (N + 1) M := fun a h1 h2 => le_min h1 h2
      -- Bijection `r ↦ s = N − r` (`i` maps Term2 indices to jump-sum indices).
      refine Finset.sum_nbij' (fun r => N - r) (fun s => N - s) ?_ ?_ ?_ ?_ ?_
      · intro r hr; rw [Finset.mem_Ico] at hr ⊢; dsimp only
        have hrN : r ≤ N := by omega
        have hub : N - r + 1 ≤ min (N + 1) M := hminM (N - r + 1) (by omega) (by omega)
        omega
      · intro s hs; rw [Finset.mem_Ico] at hs ⊢; dsimp only
        have hsN : s ≤ N := by omega
        have hsM : s < M := by omega
        have hub : N - s ≤ min m' N := hminm (N - s) (by omega) (by omega)
        omega
      · intro r hr; rw [Finset.mem_Ico] at hr; dsimp only
        have hrN : r ≤ N := by omega
        omega
      · intro s hs; rw [Finset.mem_Ico] at hs; dsimp only
        have hsN : s ≤ N := by omega
        omega
      · intro r hr
        rw [Finset.mem_Ico] at hr
        dsimp only
        -- jump-sum index `s = N − r`.
        have hsr : (N - r) ≤ N := by omega
        have hrm : r ≤ m' := by omega
        have hrN : r ≤ N := by omega
        -- vector: `creS (N−r) (m'+n+(N−r)+1) = creS (N−r) (m'−r) = ((m'−r)!)⁻¹•Tᵐ⁻ʳ(c₍N₋r₎u)`.
        have hidx : m' + (-((N : ℤ) + 1)) + ((N - r : ℕ) : ℤ) + 1 = ((m' - r : ℕ) : ℤ) := by
          rw [Nat.cast_sub hrN, Nat.cast_sub hrm]; push_cast; ring
        rw [hidx, creS_creation W u c (N - r) (m' - r)]
        have hcmode : (W.smul c ((N - r : ℕ) : ℤ) u) = W.smul c ((N : ℤ) - (r : ℤ)) u := by
          congr 1; omega
        rw [hcmode]
        rw [show (-(-((N : ℤ) + 1)) - ((N - r : ℕ) : ℤ) - 1) = (N : ℤ) - ((N - r : ℕ) : ℤ) by ring,
          negPowJump_antidiag_neg N (N - r) (by omega), show N - (N - r) = r from by omega]
        rw [← Int.cast_smul_eq_zsmul ℂ (mcoeff (N : ℤ) m' r)]
        rw [smul_smul, ← neg_smul, smul_smul, smul_smul]
        congr 1
        -- align the `↑(N-r)` casts to `↑N - ↑r` and `↑N - ↑(N-r)` to `↑r`.
        rw [show ((N - r : ℕ) : ℤ) = (N : ℤ) - (r : ℤ) from by rw [Nat.cast_sub hrN],
          show ((N : ℤ) - ((N : ℤ) - (r : ℤ))) = (r : ℤ) from by ring]
        exact nneg_scalar m' N r hrm hrN
    · -- n < 0, m < 0 : Term2 = 0, jump-sum = 0.
      rw [Term2_expand, if_neg hm, neg_zero]
      refine (Finset.sum_eq_zero fun s hs => ?_).symm
      rw [Finset.mem_range] at hs
      by_cases hsN : s ≤ N
      · rw [creS_neg W u c s (by omega : m + (-((N : ℤ) + 1)) + (s : ℤ) + 1 < 0),
          smul_zero, smul_zero]
      · rw [show (-(-((N : ℤ) + 1)) - (s : ℤ) - 1) = (N : ℤ) - (s : ℤ) by ring,
          negPowJump_antidiag_neg_zero N s (by omega), zero_smul, smul_zero]

theorem mulBySubPow_jumpSum_eq_zero (W : VertexOperatorAlgebra 𝒱) (u c : 𝒱) (M : ℕ) :
    mulBySubPow M
      (∑ s ∈ Finset.range M, ((-1 : ℂ) ^ (s + 1)) • vconv (creS W u c s) (negPowJump s)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [Finset.mem_range] at hs
  rw [map_smul, mulBySubPow_vconv_negPowJump_eq_zero (creS W u c s) (by omega), smul_zero]

theorem skewVacLocal (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) : SkewVacLocal W u := by
  intro c
  obtain ⟨M₀, hM₀⟩ := W.toPreVertexAlgebra.regularity c u
  refine ⟨M₀.toNat, ?_⟩
  rw [← Gfield_eq,
    Gfield_eq_jumpSum W u c (M := M₀.toNat) (fun s hs => hM₀ s (by omega)),
    mulBySubPow_jumpSum_eq_zero]

/-- **Skew weak-associativity locality (Gannon 5.1.8).**  A `b`-uniform `(z₁−z₂)ᴺ` annihilates
the skew bracket `[skewDist W u, Y(c)]`.  Proved honestly via the two-sided `ι_z` completion
(`skewVacLocal` → Goddard-vacuum uniqueness → full locality); this is the input that `Core.SkewSymmetry`
consumes. -/
theorem weakAssocLoc (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) : WeakAssocLoc W u :=
  weakAssocLoc_of_vacLocal W u (skewVacLocal W u)

end VertexOperatorAlgebra

end VOA
