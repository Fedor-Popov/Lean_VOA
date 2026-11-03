/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2LogBraided
import VOA.Huang.SchurWeylDLMProofFinGen
import VOA.Modules.ModuleRestrictOrd
import VOA.Core.SkewSymmetry

/-! # O3: the ambient VOA as an object of the logarithmic category of its orbifold

For a vertex operator algebra `W` and a subgroup `G ≤ Aut W`, the carrier of `W`, with the
`W`-action restricted to the fixed-point subalgebra `W^G`, is a grading-restricted generalized
`W^G`-module (`ambientLog`, with `W`'s own grading). When it is finitely generated (for instance
when `W` is simple and `G` is finite, `orbifold_finGen`), it is an object `vObj` of
`LogModuleCat (orbifoldVOA G)`.

The vertex operator `Y_W` is a logarithmic intertwining operator of type `(W / W W)` for `W^G`
with no logarithms (`vertexIntertwiner`). Its main property here is **skew-symmetry for HLZ's
`Ω₀`**: `omegaEquiv … 0 vertexIntertwiner = vertexIntertwiner` (`omega_vertexIntertwiner`).
This comes from the VOA skew-symmetry `VertexOperatorAlgebra.skew_mode`: for integral modes the
branch `e^{πi}` contributes only signs.

The object does not depend on `C₂`-cofiniteness; the multiplication (next file) does.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO3
open CategoryTheory VOA.LogTensor VOA.LogTensor.LogModuleCat VOA.C2Rigid.LocalInjective
open VOA.LogTensor.Pz VOA.LogSkew
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (G : Subgroup (Aut W))

/-- The carrier of `W` as a logarithmic (in fact ordinary) `W^G`-module, graded by `W`'s
grading. -/
abbrev ambientLog : LogVModule (orbifoldVOA G) V := (orbifold G).adjointRestrictOrd.toLog

/-- The underlying weak `W^G`-module is the restriction of the adjoint module. -/
theorem ambientLog_toWeakModule :
    (ambientLog G).toWeakModule = (orbifold G).adjointRestrict := rfl

/-- **The ambient VOA as an object of `C = LogModuleCat (W^G)`**, given finite generation
over `W^G`. -/
def vObj (hfg : FinGen (orbifold G).adjointRestrict) : LogModuleCat (orbifoldVOA G) :=
  LogModuleCat.of (ambientLog G) hfg

/-- The object for a simple `W` and a finite group `G` (Dong–Li–Mason finite generation). -/
def vObjOfSimple (hW : W.IsSimple) [Finite G] : LogModuleCat (orbifoldVOA G) :=
  vObj G (VOA.Huang.SchurWeyl.orbifold_finGen G hW)

/-- In particular for `V₂` and every finite `G ≤ Aut V₂`. -/
def V2mObj (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G] :
    LogModuleCat (orbifoldVOA G) :=
  vObj G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G)

/-! ## `Y_W` as a logarithmic intertwining operator over `W^G` -/

/-- `Y_W` satisfies the axioms of a logarithmic intertwining operator of type `(W / W W)` for
`W^G`: every axiom is the `W`-axiom of `isLogIntertwining_module` with `u ∈ W^G`. -/
theorem isLogIntertwining_vertex :
    IsLogIntertwining (orbifold G).adjointRestrict (orbifold G).adjointRestrict
      (orbifold G).adjointRestrict (ofOrd (weakModuleModes (adjointWeakModule W))) := by
  have h := isLogIntertwining_module (adjointWeakModule W)
  exact ⟨h.logFinite, h.truncation, fun w n k => h.L_neg_one w n k,
    fun u => h.jacobi (u : V)⟩

/-- **`Y_W` as a logarithmic intertwining operator of `W^G`-modules.** -/
def vertexIntertwiner : LogIntertwiningOperator (orbifold G).adjointRestrict
    (orbifold G).adjointRestrict (orbifold G).adjointRestrict :=
  ⟨ofOrd (weakModuleModes (adjointWeakModule W)), isLogIntertwining_vertex G⟩

theorem vertexIntertwiner_zero (n : ℂ) (a b : V) :
    (vertexIntertwiner G).1 n 0 a b = weakModuleModes (adjointWeakModule W) n a b := rfl

theorem vertexIntertwiner_succ (n : ℂ) (k : ℕ) (a b : V) :
    (vertexIntertwiner G).1 n (k + 1) a b = 0 := rfl

theorem vertexIntertwiner_int (k : ℤ) (a b : V) :
    (vertexIntertwiner G).1 (k : ℂ) 0 a b = W.smul a k b :=
  weakModuleModes_apply_intCast (adjointWeakModule W) k a b

theorem vertexIntertwiner_of_not_int {n : ℂ} (hn : ∀ k : ℤ, (k : ℂ) ≠ n) (k : ℕ) (a b : V) :
    (vertexIntertwiner G).1 n k a b = 0 := by
  rcases k with _ | k
  · change weakModuleModes (adjointWeakModule W) n a b = 0
    rw [weakModuleModes_of_not_int _ hn]; rfl
  · rfl

/-! ## Skew-symmetry: `Ω₀(Y_W) = Y_W` -/

theorem negOnePow_neg' (a : ℤ) : negOnePow (-a) = negOnePow a := by
  have h1 := negOnePow_add a (-a)
  rw [add_neg_cancel] at h1
  have h0 : negOnePow 0 = 1 := by simp [negOnePow]
  have h2 := negOnePow_mul_self a
  have hne : negOnePow a ≠ 0 := by
    intro h; rw [h, zero_mul] at h2; exact zero_ne_one h2
  apply mul_left_cancel₀ hne
  rw [← h1, h0, h2]

/-- The `Ω₀` phase at an integer: `e^{−πi(k+1)} = (−1)^{k+1}`. -/
theorem omegaPhase_zero_int (k : ℤ) : omegaPhase 0 (k : ℂ) = negOnePow (k + 1) := by
  have h := phase_int (omegaPhase_succ 0) (-1 : ℂ) (k + 1)
  have h1 : omegaPhase 0 (-1 : ℂ) = 1 := by
    simp [omegaPhase]
  rw [h1, mul_one, show (-1 : ℂ) + ((k + 1 : ℤ) : ℂ) = (k : ℂ) by push_cast; ring] at h
  exact h

/-- `L(−1)` of the restricted module is the translation operator of `W`. -/
theorem Lm1_ambient : Lm1 (orbifold G).adjointRestrict = W.toPreVertexAlgebra.T := by
  rw [VertexOperatorAlgebra.T_eq_Lneg1, VertexOperatorAlgebra.L_def]
  rfl

/-- **Mode skew-symmetry in the HLZ form.** For all `n : ℂ`,
`Ω₀`'s per-degree skew of `Y_W` at log degree `0` is `Y_W`. -/
theorem skewK_vertex_zero (n : ℂ) (b a : V) :
    skewK (orbifold G).adjointRestrict (omegaPhase 0) (vertexIntertwiner G).1 n 0 b a =
      (vertexIntertwiner G).1 n 0 b a := by
  classical
  obtain ⟨J, hJ⟩ := ((vertexIntertwiner G).2.trunc_comp 0).bound a b n
  rw [(vertexIntertwiner G).2.skewK_eq_sum (omegaPhase 0) n 0 b a J hJ]
  by_cases hn : ∃ k : ℤ, (k : ℂ) = n
  · obtain ⟨k, rfl⟩ := hn
    rw [vertexIntertwiner_int, VertexOperatorAlgebra.skew_mode W b a k,
      omegaPhase_zero_int, Lm1_ambient]
    have hsupp : Function.support (fun j : ℕ => ((j.factorial : ℂ)⁻¹) • (sgn (-k - 1 - j)) •
        ((W.toPreVertexAlgebra.T ^ j) ((W.Y a) (-k - 1 - j) b))) ⊆ (Finset.range J : Set ℕ) := by
      intro j hj
      rw [Function.mem_support] at hj
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hjJ
      apply hj
      have h0 := hJ j (by omega)
      change (vertexIntertwiner G).1 ((k : ℂ) + (j : ℂ)) 0 a b = 0 at h0
      rw [show (k : ℂ) + (j : ℂ) = ((k + j : ℤ) : ℂ) by push_cast; ring,
        vertexIntertwiner_int] at h0
      change mode (W.Y a) (k + j) b = 0 at h0
      unfold mode at h0
      rw [show -k - 1 - (j : ℤ) = -(k + j) - 1 by ring, h0]
      simp
    rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change negOnePow (k + 1) • (sc j • (W.toPreVertexAlgebra.T ^ j)
      ((vertexIntertwiner G).1 ((k : ℂ) + (j : ℂ)) 0 a b)) = _
    rw [show (k : ℂ) + (j : ℂ) = ((k + j : ℤ) : ℂ) by push_cast; ring, vertexIntertwiner_int]
    have hm : W.smul a (k + j) b = (W.Y a) (-k - 1 - j) b := by
      change mode (W.Y a) (k + j) b = _
      unfold mode
      rw [show -(k + (j : ℤ)) - 1 = -k - 1 - j by ring]
    rw [hm, smul_smul, smul_smul]
    congr 1
    have hs : sgn (-k - 1 - j) = negOnePow (k + 1) * (-1 : ℂ) ^ j := by
      change negOnePow (-k - 1 - j) = _
      rw [show -k - 1 - (j : ℤ) = -((k + 1) + j) by ring, negOnePow_neg', negOnePow_add,
        negOnePow_natCast]
    rw [hs, sc]
    ring
  · have hz : ∀ j : ℕ, (vertexIntertwiner G).1 (n + j) 0 a b = 0 := fun j =>
      vertexIntertwiner_of_not_int G (fun k hk => hn ⟨k - j, by push_cast; rw [hk]; ring⟩) 0 a b
    rw [vertexIntertwiner_of_not_int G (fun k hk => hn ⟨k, hk⟩) 0 b a]
    refine (congrArg _ (Finset.sum_eq_zero fun j _ => ?_)).trans (smul_zero _)
    rw [hz j, map_zero, smul_zero]

/-- The per-degree skew vanishes in positive log degree (`Y_W` has no logarithms). -/
theorem skewK_vertex_succ (n : ℂ) (k : ℕ) (b a : V) :
    skewK (orbifold G).adjointRestrict (omegaPhase 0) (vertexIntertwiner G).1 n (k + 1) b a =
      0 := by
  obtain ⟨J, hJ⟩ := ((vertexIntertwiner G).2.trunc_comp (k + 1)).bound a b n
  rw [(vertexIntertwiner G).2.skewK_eq_sum (omegaPhase 0) n (k + 1) b a J hJ]
  refine (congrArg _ (Finset.sum_eq_zero fun j _ => ?_)).trans (smul_zero _)
  rw [vertexIntertwiner_succ, map_zero, smul_zero]

/-- **Skew-symmetry of `Y_W` for HLZ's `Ω₀`**: `Ω₀(Y_W) = Y_W`. -/
theorem omega_vertexIntertwiner :
    omegaEquiv (orbifold G).adjointRestrict (orbifold G).adjointRestrict
      (orbifold G).adjointRestrict 0 (vertexIntertwiner G) = vertexIntertwiner G := by
  apply Subtype.ext
  change omega _ 0 (vertexIntertwiner G).1 = (vertexIntertwiner G).1
  have hfin := ((vertexIntertwiner G).2.isLogIntertwining_skewK (omegaPhase_succ 0)
    (omegaPhase_ne_zero 0)).logFin
  funext n j
  ext b a
  unfold omega
  rw [logShift_eq_sum hfin 1 (fun k hk => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact skewK_vertex_succ G n k b a)]
  rw [Finset.sum_range_one]
  rcases j with _ | j
  · rw [skewK_vertex_zero]
    simp [shc]
  · rw [vertexIntertwiner_succ]
    simp [shc]

end VOA.Classification.COne.McRaeO3
