/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO5bChannels

/-! # O5b, step 4: the Jacobi identity on a twisted summand, homogeneous inputs

`jacobi_homog`: for a left module `(X, a)` of the O3 algebra, a module endomorphism `p` with
`g`-twisted image, `g`-fixed homogeneous `u, v` and `x = p x'` of generalized weight `c`, the
integral log-free modes `(actY a)_{(j)}` satisfy the module Jacobi identity at `x`, for every
`ℓ, m, n ∈ ℤ`.

Proof: test against an arbitrary functional `f`. With `D = ℓ + m + n` the three channels
`sA, tC, qD` (product, reversed product, iterate) satisfy all hypotheses of
`residue_of_channels`:

* finiteness — truncation of `actY a` and of `Y_W`;
* convergence — Huang's differential equations (`summable_log_product_series`,
  `summable_log_iterate_series`), and the rational Fuchsian equation of the product row
  (`exists_ratFuchsian_log_product_homogeneous`) for the continuation to `ℂ ∖ [0, 1]`;
* `channel_AD`, `channel_CD`.

The residue identity at `a = m` is exactly `f` applied to the Jacobi identity
(`f_lhs`, `f_rhs`).

No `sorry`, no new axioms.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO5b
open CategoryTheory MonoidalCategory BraidedCategory VOA.LogTensor VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion
open VOA.Huang.AssocExpansion VOA.Classification.COne.McRaeO3 VOA.Classification.COne.McRaeO5
open VOA.Classification.COne.McRaeO4c VOA.Huang.LogBraided

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {G : Subgroup (Aut W)} {hfg : FinGen (orbifold G).adjointRestrict}
  {hC2 : C2Cofinite (orbifoldVOA G)}

section Jac
variable {X : LogModuleCat (orbifoldVOA G)} (a : tensorObject hC2 (vObj G hfg) X ⟶ X)

/-- Truncation of the integral modes of `actY a`. -/
theorem actY_trunc (w : V) (y : X) :
    ∃ N : ℤ, ∀ j : ℤ, N ≤ j → (actY hC2 a).1 (j : ℂ) 0 w y = 0 := by
  obtain ⟨N, hN⟩ := (actY hC2 a).2.truncation w y 0
  exact ⟨N, fun j hj => by simpa using hN j hj 0⟩

theorem actY_zero_right (n : ℂ) (k : ℕ) (w : V) : (actY hC2 a).1 n k w (0 : X) = 0 :=
  map_zero _

/-- The left summand family of the Jacobi identity. -/
def famL (u v : V) (y : X) (ℓ m n i : ℤ) : X :=
  (negOnePow i * cbz ℓ i) •
    ((actY hC2 a).1 ((ℓ + m - i : ℤ) : ℂ) 0 u ((actY hC2 a).1 ((n + i : ℤ) : ℂ) 0 v y)
      - negOnePow ℓ • (actY hC2 a).1 ((ℓ + n - i : ℤ) : ℂ) 0 v
          ((actY hC2 a).1 ((m + i : ℤ) : ℂ) 0 u y))

/-- The right summand family of the Jacobi identity. -/
def famR (u v : V) (y : X) (ℓ m n i : ℤ) : X :=
  cbz m i • (actY hC2 a).1 ((m + n - i : ℤ) : ℂ) 0 (W.smul u (ℓ + i) v) y

theorem finite_support_of_bounds {M : Type*} [Zero M] {F : ℤ → M} (I : ℤ)
    (h0 : ∀ i, i < 0 → F i = 0) (hI : ∀ i, I < i → F i = 0) : (Function.support F).Finite := by
  apply Set.Finite.subset (Set.finite_Icc 0 I)
  intro i hi
  rw [Function.mem_support] at hi
  exact ⟨not_lt.mp fun h => hi (h0 i h), not_lt.mp fun h => hi (hI i h)⟩

theorem famL_fin (u v : V) (y : X) (ℓ m n : ℤ) :
    (Function.support (famL a u v y ℓ m n)).Finite := by
  obtain ⟨Nv, hNv⟩ := actY_trunc a v y
  obtain ⟨Nu, hNu⟩ := actY_trunc a u y
  refine finite_support_of_bounds (max (Nv - n) (Nu - m)) (fun i hi => ?_) (fun i hi => ?_)
  · simp only [famL, cbz_apply_neg ℓ hi, mul_zero, zero_smul]
  · simp only [famL]
    rw [hNv (n + i) (by omega), hNu (m + i) (by omega), actY_zero_right, actY_zero_right,
      smul_zero, sub_zero, smul_zero]

theorem famR_fin (u v : V) (y : X) (ℓ m n : ℤ) :
    (Function.support (famR a u v y ℓ m n)).Finite := by
  obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  refine finite_support_of_bounds (Ns - ℓ) (fun i hi => ?_) (fun i hi => ?_)
  · simp only [famR, cbz_apply_neg m hi, zero_smul]
  · simp only [famR]
    rw [show W.smul u (ℓ + i) v = 0 from hNs _ (by omega), actY_zero_left, smul_zero]

end Jac

section Homog
variable {X : LogModuleCat (orbifoldVOA G)} {a : tensorObject hC2 (vObj G hfg) X ⟶ X}
  {p : X ⟶ X} {g : Aut W}

/-- **The Jacobi identity on a twisted summand, homogeneous inputs.** -/
theorem jacobi_homog (hX : letI := logarithmicMonoidalCategory hC2
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a)
    (hT : TwistFacts a p g) {A B : ℤ} {c : ℂ} {u v : V}
    (hu : u ∈ (vObj G hfg).act.weight (A : ℂ)) (hv : v ∈ (vObj G hfg).act.weight (B : ℂ))
    (hgu : g u = u) (hgv : g v = v) (x' : X) (hx : p.1 x' ∈ X.act.weight c) (ℓ m n : ℤ) :
    ∑ᶠ i : ℤ, famL a u v (p.1 x') ℓ m n i = ∑ᶠ i : ℤ, famR a u v (p.1 x') ℓ m n i := by
  classical
  rw [← sub_eq_zero]
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro f
  set y := p.1 x' with hy
  set D : ℤ := ℓ + m + n with hD
  obtain ⟨Nv, hNv⟩ := actY_trunc a v y
  obtain ⟨Nu, hNu⟩ := actY_trunc a u y
  obtain ⟨Ns, hNs⟩ := W.toPreVertexAlgebra.smul_eventually_zero u v
  -- finiteness of the channels
  have hs0 : ∀ k, Nv - D - 2 < k → sA a p f D u v x' k = 0 := by
    intro k hk
    simp only [sA]
    rw [← hy, hNv _ (by omega), actY_zero_right, map_zero]
  have ht0 : ∀ k, k < -Nu → tC a p f D u v x' k = 0 := by
    intro k hk
    simp only [tC]
    rw [← hy, hNu _ (by omega), actY_zero_right, map_zero]
  have hq0 : ∀ k, k < -Ns → qD a p f D u v x' k = 0 := by
    intro k hk
    simp only [qD]
    rw [show W.smul u (-k - 1) v = 0 from hNs _ (by omega), actY_zero_left, map_zero]
  -- the Fuchsian product row
  have hrow : ∃ (K : ℕ) (ν : ℂ) (Q : PowerSeries ℂ), VOA.Huang.Convergence.RatFuchsian 1 ν Q ∧
      ∀ k : ℕ, PowerSeries.coeff (k + K) Q = sA a p f D u v x' ((Nv - D - 2) - k) := by
    obtain ⟨K, ν, Q, hQ, hc⟩ :=
      VOA.Huang.LogHuangODEProduct.exists_ratFuchsian_log_product_homogeneous hC2
        (vObj G hfg).act (vObj G hfg).act X.act X.act X.act (vObj G hfg).finiteGeneration
        (vObj G hfg).finiteGeneration X.finiteGeneration X.finiteGeneration X.finiteGeneration
        (actY hC2 a) (actY hC2 a) hu hv hx f (((-(Nv - D - 2) - 1 : ℤ) : ℂ))
        (((D + (Nv - D - 2) + 1 : ℤ) : ℂ)) 0 0
    refine ⟨K, ν, Q, hQ, fun k => ?_⟩
    rw [hc k, sA]
    have e1 : (((-(Nv - D - 2) - 1 : ℤ) : ℂ)) + (k : ℂ) =
        ((-((Nv - D - 2) - (k : ℤ)) - 1 : ℤ) : ℂ) := by push_cast; ring
    have e2 : (((D + (Nv - D - 2) + 1 : ℤ) : ℂ)) - (k : ℂ) =
        ((D + ((Nv - D - 2) - (k : ℤ)) + 1 : ℤ) : ℂ) := by push_cast; ring
    rw [e1, e2]
  -- convergence of the reversed product and of the iterate
  have hTs : ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ < 1 → Summable fun k : ℤ => tC a p f D u v x' k * ζ ^ k := by
    intro ζ hζ0 hζ1
    have h := VOA.Huang.LogHuangODEProduct.summable_log_product_series hC2
      (vObj G hfg).act (vObj G hfg).act X.act X.act X.act (vObj G hfg).finiteGeneration
      (vObj G hfg).finiteGeneration X.finiteGeneration X.finiteGeneration X.finiteGeneration
      (actY hC2 a) (actY hC2 a) f v u y (((D + (-Nu) + 1 : ℤ) : ℂ)) (((-(-Nu) - 1 : ℤ) : ℂ)) 0 0 hζ1
    refine (hasSum_of_nat_shift ht0 hζ0 (h.congr fun k => ?_).hasSum).summable
    simp only [tC]
    have e1 : (((D + (-Nu) + 1 : ℤ) : ℂ)) + (k : ℂ) = ((D + ((k : ℤ) + -Nu) + 1 : ℤ) : ℂ) := by
      push_cast; ring
    have e2 : (((-(-Nu) - 1 : ℤ) : ℂ)) - (k : ℂ) = ((-((k : ℤ) + -Nu) - 1 : ℤ) : ℂ) := by
      push_cast; ring
    rw [e1, e2]
  have hQs : ∀ r : ℂ, r ≠ 0 → ‖r‖ < 1 → Summable fun k : ℤ => qD a p f D u v x' k * r ^ k := by
    intro r hr0 hr1
    have h := VOA.Huang.LogHuangODEIterate.summable_log_iterate_series hC2
      (vObj G hfg).act (vObj G hfg).act X.act X.act (vObj G hfg).act
      (vObj G hfg).finiteGeneration (vObj G hfg).finiteGeneration X.finiteGeneration
      X.finiteGeneration (vObj G hfg).finiteGeneration (actY hC2 a) (vertexIntertwiner G) f u v y
      (((D + (-Ns) + 1 : ℤ) : ℂ)) (((-(-Ns) - 1 : ℤ) : ℂ)) 0 0 hr1
    refine (hasSum_of_nat_shift hq0 hr0 (h.congr fun k => ?_).hasSum).summable
    simp only [qD]
    have e1 : (((D + (-Ns) + 1 : ℤ) : ℂ)) + (k : ℂ) = ((D + ((k : ℤ) + -Ns) + 1 : ℤ) : ℂ) := by
      push_cast; ring
    have e2 : (((-(-Ns) - 1 : ℤ) : ℂ)) - (k : ℂ) = ((-((k : ℤ) + -Ns) - 1 : ℤ) : ℂ) := by
      push_cast; ring
    rw [e1, e2]
    exact congrArg (fun w : V => f ((actY hC2 a).1 (((D + ((k : ℤ) + -Ns) + 1 : ℤ) : ℂ)) 0 w y) *
      r ^ k) (vertexIntertwiner_int G _ u v)
  -- the residue identity
  have hres := residue_of_channels hs0 ht0 hq0 hrow hTs hQs
    (fun x h1 h2 => channel_AD hX hT hu hv hgu hgv x' hx f x h1 h2)
    (fun x h1 h2 => channel_CD hX hT hu hv hgu hgv x' hx f x h1 h2) m ℓ
  -- identification of the two sides
  rw [map_sub, map_finsum f (famL_fin a u v y ℓ m n), map_finsum f (famR_fin a u v y ℓ m n)]
  have hfL : ∀ i, f (famL a u v y ℓ m n i) = (negOnePow i * cbz ℓ i) * sA a p f D u v x' (i - 1 - m - ℓ)
      - negOnePow ℓ * ((negOnePow i * cbz ℓ i) * tC a p f D u v x' (-1 - m - i)) := by
    intro i
    simp only [famL, sA, tC, map_smul, map_sub, smul_eq_mul]
    rw [show -(i - 1 - m - ℓ) - 1 = ℓ + m - i by ring, show D + (i - 1 - m - ℓ) + 1 = n + i by
      rw [hD]; ring, show D + (-1 - m - i) + 1 = ℓ + n - i by rw [hD]; ring,
      show -(-1 - m - i) - 1 = m + i by ring]
    ring
  have hfR : ∀ i, f (famR a u v y ℓ m n i) = cbz m i * qD a p f D u v x' (-1 - ℓ - i) := by
    intro i
    simp only [famR, qD, map_smul, smul_eq_mul]
    rw [show D + (-1 - ℓ - i) + 1 = m + n - i by rw [hD]; ring,
      show -(-1 - ℓ - i) - 1 = ℓ + i by ring]
  have hfinA : (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) * sA a p f D u v x' (i - 1 - m - ℓ)).Finite := by
    refine finite_support_of_bounds (Nv - n) (fun i hi => ?_) (fun i hi => ?_)
    · rw [cbz_apply_neg ℓ hi, mul_zero, zero_mul]
    · rw [hs0 _ (by omega), mul_zero]
  have hfinB : (Function.support fun i : ℤ => negOnePow ℓ *
      ((negOnePow i * cbz ℓ i) * tC a p f D u v x' (-1 - m - i))).Finite := by
    refine finite_support_of_bounds (Nu - m) (fun i hi => ?_) (fun i hi => ?_)
    · rw [cbz_apply_neg ℓ hi, mul_zero, zero_mul, mul_zero]
    · rw [ht0 _ (by omega), mul_zero, mul_zero]
  rw [finsum_congr hfL, finsum_sub_distrib hfinA hfinB, ← mul_finsum, finsum_congr hfR]
  have e : resInf m ℓ (sA a p f D u v x') - resZero m ℓ (tC a p f D u v x') -
      resOne m ℓ (qD a p f D u v x') = 0 := by rw [hres, sub_self]
  simpa only [resInf, resZero, resOne] using e

end Homog

end VOA.Classification.COne.McRaeO5b
