/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO3Algebra
import VOA.Classification.COne.McRaeO3AssocSeries
import VOA.Classification.COne.McRaeO3Summable
import VOA.Classification.COne.OrbPos9Associativity

/-! # O3: associativity of the ambient algebra in the logarithmic category

The multiplication `μ : V ⊠ V ⟶ V` of `McRaeO3Algebra` is associative for the logarithmic
associator `associatorIso` (`mulHom_assoc`).

Route.
1. Maps out of `(V ⊠ V) ⊠ V` are detected by completed canonical iterates
   (`leftTriple_linearMap_ext_of_completed_iterate`).
2. On a completed iterate, `(μ ⊠ 1) ≫ μ` is the completed iterate of `Y_W` with itself, and
   `α ≫ (1 ⊠ μ) ≫ μ` is the completed product of `Y_W` with itself
   (`tensorAssociatorHom_completed_shift`, functoriality of completions).
3. `vertex_completed_assoc`: for `Y_W` the completed product at `(log(1+e^t), 0)` equals the
   completed iterate at `(t, 0)` on the whole overlap domain. The weight sums are integral
   (`W` is `ℤ`-graded and `Y_W` has no logarithms). They are the series of
   `HKLRational.assoc_series_eq` with the coefficients of the Jacobi identity of `W`
   (`OrbPos9.Assoc.assoc_rel`). The identity is proved at complex points by
   `assoc_series_eq_complex`; the summability inputs are `completedLogIterate_summable` and
   `completedLogProduct_summable` (convergence for `C₂`-cofinite `W^G`).
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO3
open CategoryTheory VOA.LogTensor VOA.LogTensor.LogModuleCat VOA.C2Rigid.LocalInjective
open VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion
open VOA.Classification.COne.McRaeM1 VOA.Huang.LogBraided
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (G : Subgroup (Aut W))

/-! ## The weight-sum terms of `Y_W` -/

/-- Evaluation of `Y_W` at a branch, on homogeneous inputs. -/
theorem evaluatePoint_vertex (ell : ℂ) {a b : ℂ} {x y : V}
    (hx : x ∈ (ambientLog G).weight a) (hy : y ∈ (ambientLog G).weight b) (γ : ℂ) :
    (evaluatePoint (ambientLog G) (ambientLog G) (ambientLog G) (vertexIntertwiner G) ell x y γ :
      V) = Complex.exp (ell * (γ - a - b)) • (vertexIntertwiner G).1 (a + b - γ - 1) 0 x y := by
  rw [evaluatePoint_homogeneous (ambientLog G) (ambientLog G) (ambientLog G)
    (vertexIntertwiner G) ell hx hy γ]
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [vertexIntertwiner_succ, smul_zero]
  · intro h
    exfalso
    apply h
    simp only [Finset.mem_range, pointLogCutoff]
    omega

/-- A block of `Y_W` is its log-degree-zero coefficient times the branch factor. -/
theorem pointEvaluationBlock_vertex (ell a b c : ℂ) (x : (ambientLog G).weight a)
    (y : (ambientLog G).weight b) :
    (pointEvaluationBlock (ambientLog G) (ambientLog G) (ambientLog G) (vertexIntertwiner G)
      ell a b c x y : V) =
      Complex.exp (ell * (c - a - b)) • (vertexIntertwiner G).1 (a + b - c - 1) 0 x y := by
  rw [pointEvaluationBlock_fixed_cutoff (ambientLog G) (ambientLog G) (ambientLog G)
    (vertexIntertwiner G) ell a b c x y 1 (fun k hk => by
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rfl)]
  simp

/-- The iterate summand of `Y_W`. -/
theorem iterTerm_vertex (t : ℂ) {a b c β : ℂ} {x y z : V}
    (hx : x ∈ (ambientLog G).weight a) (hy : y ∈ (ambientLog G).weight b)
    (hz : z ∈ (ambientLog G).weight c) (f : V →ₗ[ℂ] ℂ) (γ : ℂ) :
    f (pointEvaluationBlock (ambientLog G) (ambientLog G) (ambientLog G) (vertexIntertwiner G)
      0 γ c β (evaluatePoint (ambientLog G) (ambientLog G) (ambientLog G) (vertexIntertwiner G)
        t x y γ) ⟨z, hz⟩) =
      Complex.exp (t * (γ - a - b)) *
        f ((vertexIntertwiner G).1 (γ + c - β - 1) 0
          ((vertexIntertwiner G).1 (a + b - γ - 1) 0 x y) z) := by
  rw [pointEvaluationBlock_vertex, evaluatePoint_vertex G t hx hy γ]
  simp only [zero_mul, Complex.exp_zero, one_smul]
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]

/-- The product summand of `Y_W`. -/
theorem prodTerm_vertex (ell : ℂ) {a b c β : ℂ} {x y z : V}
    (hx : x ∈ (ambientLog G).weight a) (hy : y ∈ (ambientLog G).weight b)
    (hz : z ∈ (ambientLog G).weight c) (f : V →ₗ[ℂ] ℂ) (γ : ℂ) :
    f (pointEvaluationBlock (ambientLog G) (ambientLog G) (ambientLog G) (vertexIntertwiner G)
      ell a γ β ⟨x, hx⟩ (evaluatePoint (ambientLog G) (ambientLog G) (ambientLog G)
        (vertexIntertwiner G) 0 y z γ)) =
      Complex.exp (ell * (β - a - γ)) *
        f ((vertexIntertwiner G).1 (a + γ - β - 1) 0 x
          ((vertexIntertwiner G).1 (b + c - γ - 1) 0 y z)) := by
  rw [pointEvaluationBlock_vertex, evaluatePoint_vertex G 0 hy hz γ]
  simp only [zero_mul, Complex.exp_zero, one_smul]
  rw [map_smul, smul_eq_mul]

/-- A nonzero vector of `V` has integral weight. -/
theorem int_of_mem_ne_zero {α : ℂ} {x : V} (hx : x ∈ (ambientLog G).weight α) (h0 : x ≠ 0) :
    ∃ k : ℤ, α = k := by
  by_contra h
  push Not at h
  have hz := adjWeight_eq_bot W (fun k hk => h k hk.symm)
  change x ∈ adjWeight W α at hx
  rw [hz] at hx
  exact h0 hx

/-- A nonzero coefficient of `Y_W` has integral index and nonzero inputs. -/
theorem vertex_ne_zero {n : ℂ} {u v : V} (h : (vertexIntertwiner G).1 n 0 u v ≠ 0) :
    (∃ k : ℤ, (k : ℂ) = n) ∧ u ≠ 0 ∧ v ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra h'
    push Not at h'
    exact h (vertexIntertwiner_of_not_int G h' 0 u v)
  · rintro rfl
    exact h (by rw [map_zero, LinearMap.zero_apply])
  · rintro rfl
    exact h (map_zero _)

theorem vertexIntertwiner_int' (k : ℤ) (u v : V) :
    (vertexIntertwiner G).1 (k : ℂ) 0 u v = mode ((adjointModule W).YM u) k v :=
  vertexIntertwiner_int G k u v

theorem exp_mul_int (t : ℂ) (m : ℤ) : Complex.exp (t * (m : ℂ)) = Complex.exp t ^ m := by
  rw [mul_comm, Complex.exp_int_mul]

/-- **Analytic associativity of `Y_W` in the completed logarithmic form**: on the overlap,
the completed product `Y_W(x, 1+e^t) Y_W(y, 1) z` equals the completed iterate
`Y_W(Y_W(x, e^t) y, 1) z`, weight by weight in the output. -/
theorem vertex_completed_assoc (hC2 : C2Cofinite (orbifoldVOA G))
    (hfg : FinGen (orbifold G).adjointRestrict) {a b c β : ℂ} {x y z : V}
    (hx : x ∈ (ambientLog G).weight a) (hy : y ∈ (ambientLog G).weight b)
    (hz : z ∈ (ambientLog G).weight c) (f : V →ₗ[ℂ] ℂ) {t : ℂ} (ht : t ∈ overlapDomain) :
    completedLogProduct (ambientLog G) (ambientLog G) (ambientLog G) (ambientLog G)
        (ambientLog G) (vertexIntertwiner G) (vertexIntertwiner G)
        (Complex.log (1 + Complex.exp t)) 0 a β f ⟨x, hx⟩ y z =
      completedLogIterate (ambientLog G) (ambientLog G) (ambientLog G) (ambientLog G)
        (ambientLog G) (vertexIntertwiner G) (vertexIntertwiner G) t 0 c β f x y ⟨z, hz⟩ := by
  classical
  set Yv := vertexIntertwiner G with hYv
  have hL : ∀ ell : ℂ, completedLogProduct (ambientLog G) (ambientLog G) (ambientLog G)
      (ambientLog G) (ambientLog G) Yv Yv ell 0 a β f ⟨x, hx⟩ y z =
      ∑' γ : ℂ, Complex.exp (ell * (β - a - γ)) *
        f (Yv.1 (a + γ - β - 1) 0 x (Yv.1 (b + c - γ - 1) 0 y z)) := by
    intro ell
    unfold completedLogProduct completedProductPair
    exact tsum_congr fun γ => prodTerm_vertex G ell hx hy hz f γ
  have hR : ∀ t' : ℂ, completedLogIterate (ambientLog G) (ambientLog G) (ambientLog G)
      (ambientLog G) (ambientLog G) Yv Yv t' 0 c β f x y ⟨z, hz⟩ =
      ∑' γ : ℂ, Complex.exp (t' * (γ - a - b)) *
        f (Yv.1 (γ + c - β - 1) 0 (Yv.1 (a + b - γ - 1) 0 x y) z) := by
    intro t'
    unfold completedLogIterate completedIteratePair
    exact tsum_congr fun γ => iterTerm_vertex G t' hx hy hz f γ
  rw [hL, hR]
  by_cases hall : (∃ a' : ℤ, a = a') ∧ (∃ b' : ℤ, b = b') ∧ (∃ g : ℤ, c - β = g)
  · obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨g, hg⟩⟩ := hall
    set D : ℤ := a' + b' + g - 2 with hD
    let P : ℤ → ℂ := fun k =>
      f (mode ((adjointModule W).YM x) (D - k) (mode ((adjointModule W).YM y) k z))
    let Q : ℤ → ℂ := fun r => f (mode ((adjointModule W).YM (W.smul x r y)) (D - r) z)
    -- the product summands on the integral lattice
    have hPk : ∀ (ell : ℂ) (k : ℤ),
        Complex.exp (ell * (β - a' - (((b' : ℂ) + c - 1) - k))) *
          f (Yv.1 (a' + (((b' : ℂ) + c - 1) - k) - β - 1) 0 x
            (Yv.1 (b' + c - (((b' : ℂ) + c - 1) - k) - 1) 0 y z)) =
        P k * Complex.exp ell ^ (k - D - 1) := by
      intro ell k
      have e1 : (b' : ℂ) + c - (((b' : ℂ) + c - 1) - k) - 1 = ((k : ℤ) : ℂ) := by ring
      have e2 : (a' : ℂ) + (((b' : ℂ) + c - 1) - k) - β - 1 = ((D - k : ℤ) : ℂ) := by
        rw [hD]; push_cast; linear_combination hg
      have e3 : β - a' - (((b' : ℂ) + c - 1) - k) = ((k - D - 1 : ℤ) : ℂ) := by
        rw [hD]; push_cast; linear_combination -hg
      rw [e1, e2, e3, exp_mul_int, hYv, vertexIntertwiner_int', vertexIntertwiner_int']
      ring
    -- the iterate summands on the integral lattice
    have hQr : ∀ (t' : ℂ) (r : ℤ),
        Complex.exp (t' * ((((a' + b' - 1 : ℤ) : ℂ) - r) - a' - b')) *
          f (Yv.1 ((((a' + b' - 1 : ℤ) : ℂ) - r) + c - β - 1) 0
            (Yv.1 (a' + b' - (((a' + b' - 1 : ℤ) : ℂ) - r) - 1) 0 x y) z) =
        Q r * Complex.exp t' ^ (-r - 1) := by
      intro t' r
      have e1 : (a' : ℂ) + b' - (((a' + b' - 1 : ℤ) : ℂ) - r) - 1 = ((r : ℤ) : ℂ) := by
        push_cast; ring
      have e2 : (((a' + b' - 1 : ℤ) : ℂ) - r) + c - β - 1 = ((D - r : ℤ) : ℂ) := by
        rw [hD]; push_cast; linear_combination hg
      have e3 : (((a' + b' - 1 : ℤ) : ℂ) - r) - a' - b' = ((-r - 1 : ℤ) : ℂ) := by
        push_cast; ring
      rw [e1, e2, e3, exp_mul_int, hYv, vertexIntertwiner_int', vertexIntertwiner_int']
      exact mul_comm _ _
    -- reindex both sums over `ℤ`
    rw [VOA.Huang.HKLRational.tsum_eq_tsum_int ((b' : ℂ) + c - 1) ?s1,
      VOA.Huang.HKLRational.tsum_eq_tsum_int (((a' + b' - 1 : ℤ) : ℂ)) ?s2]
    case s1 =>
      intro w hw
      have hin : Yv.1 (b' + c - w - 1) 0 y z ≠ 0 := by
        intro h0
        apply hw
        rw [h0, map_zero, map_zero, mul_zero]
      obtain ⟨⟨k, hk⟩, -, -⟩ := vertex_ne_zero G hin
      exact ⟨k, by rw [hk]; ring⟩
    case s2 =>
      intro w hw
      have hin : Yv.1 (a' + b' - w - 1) 0 x y ≠ 0 := by
        intro h0
        apply hw
        rw [h0, map_zero, LinearMap.zero_apply, map_zero, mul_zero]
      obtain ⟨⟨r, hr⟩, -, -⟩ := vertex_ne_zero G hin
      exact ⟨r, by rw [hr]; push_cast; ring⟩
    simp only [hPk, hQr]
    -- the truncations and the associator relation
    obtain ⟨N0, hN0⟩ := (adjointModule W).truncation x z
    obtain ⟨k1, hk1⟩ := (adjointModule W).truncation y z
    obtain ⟨r0, hr0⟩ := (adjointModule W).truncation x y
    set K : ℕ := N0.toNat
    have hK : ∀ i : ℤ, 0 ≤ i → mode ((adjointModule W).YM x) (K + i) z = 0 := fun i hi =>
      hN0 _ (by simp only [K]; omega)
    have hrel : ∀ ℓ : ℤ, ∑ i ∈ Finset.range (K + 1), (K.choose i : ℂ) * Q (ℓ + i) =
        ∑' i : ℕ, cbz (i - ℓ - 1) i * P (D - K - ℓ + i) := by
      intro ℓ
      have h := OrbPos9.Assoc.assoc_rel G x y z f D K hK k1 hk1 ℓ
      simpa only [OrbPos9.Assoc.ambientIntertwiner_int] using h
    have hP : ∀ k, k1 ≤ k → P k = 0 := by
      intro k hk
      simp only [P]
      rw [hk1 k hk, map_zero, map_zero]
    have hQ : ∀ r, r0 ≤ r → Q r = 0 := by
      intro r hr
      simp only [Q]
      have h0 : W.smul x r y = 0 := hr0 r hr
      rw [h0, map_zero, mode_zero, LinearMap.zero_apply, map_zero]
    -- summability of the product series at real points
    have hProd : ∀ s : ℝ, 0 < s → s < 1 →
        Summable fun k : ℤ => P k * (1 + (s : ℂ)) ^ (k - D - 1) := by
      intro s hs0 hs1
      have ht' : Complex.log (s : ℂ) ∈ overlapDomain := by
        refine ⟨?_, ?_⟩
        · rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
          exact Real.log_neg hs0 hs1
        · rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hs0.le, abs_zero]
          positivity
      have hexp : Complex.exp (Complex.log (s : ℂ)) = s :=
        Complex.exp_log (by exact_mod_cast hs0.ne')
      have hsum := completedLogProduct_summable hC2 (ambientLog G) (ambientLog G)
        (ambientLog G) (ambientLog G) (ambientLog G) hfg hfg hfg hfg hfg Yv Yv hx hy hz f β ht'
      have hinj : Function.Injective fun k : ℤ => (b' : ℂ) + c - 1 - (k : ℂ) :=
        fun m n h => by simpa using h
      refine (hsum.comp_injective hinj).congr fun k => ?_
      simp only [Function.comp]
      rw [prodTerm_vertex G _ hx hy hz f, hPk, hexp, Complex.exp_log (by
        rw [← hexp]; exact one_add_exp_ne_zero ht')]
    -- summability of the iterate series at the given point
    have hIt₀ : Summable fun r : ℤ => Q r * Complex.exp t ^ (-r - 1) := by
      have hsum := completedLogIterate_summable hC2 (ambientLog G) (ambientLog G)
        (ambientLog G) (ambientLog G) (ambientLog G) hfg hfg hfg hfg hfg Yv Yv hx hy hz f β ht
      have hinj : Function.Injective fun r : ℤ => (((a' + b' - 1 : ℤ) : ℂ)) - (r : ℂ) :=
        fun m n h => by simpa using h
      refine (hsum.comp_injective hinj).congr fun r => ?_
      simp only [Function.comp]
      rw [iterTerm_vertex G t hx hy hz f, hQr]
    rw [Complex.exp_log (one_add_exp_ne_zero ht)]
    exact (VOA.Huang.HKLRational.assoc_series_eq_complex P Q D K k1 r0 hP hQ hrel hProd
      (Complex.exp_ne_zero t) (one_lt_norm ht) hIt₀).symm
  · -- non-integral data: every summand vanishes
    have hP0 : ∀ γ : ℂ, Complex.exp (Complex.log (1 + Complex.exp t) * (β - a - γ)) *
        f (Yv.1 (a + γ - β - 1) 0 x (Yv.1 (b + c - γ - 1) 0 y z)) = 0 := by
      intro γ
      by_contra hne
      have hout : Yv.1 (a + γ - β - 1) 0 x (Yv.1 (b + c - γ - 1) 0 y z) ≠ 0 := by
        intro h0; apply hne; rw [h0, map_zero, mul_zero]
      obtain ⟨⟨j, hj⟩, hx0, hin⟩ := vertex_ne_zero G hout
      obtain ⟨⟨k, hk⟩, hy0, -⟩ := vertex_ne_zero G hin
      obtain ⟨a', ha'⟩ := int_of_mem_ne_zero G hx hx0
      obtain ⟨b', hb'⟩ := int_of_mem_ne_zero G hy hy0
      exact hall ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨j + k + 2 - a' - b', by
        push_cast; rw [hj, hk, ha', hb']; ring⟩⟩
    have hI0 : ∀ γ : ℂ, Complex.exp (t * (γ - a - b)) *
        f (Yv.1 (γ + c - β - 1) 0 (Yv.1 (a + b - γ - 1) 0 x y) z) = 0 := by
      intro γ
      by_contra hne
      have hout : Yv.1 (γ + c - β - 1) 0 (Yv.1 (a + b - γ - 1) 0 x y) z ≠ 0 := by
        intro h0; apply hne; rw [h0, map_zero, mul_zero]
      obtain ⟨⟨n, hn⟩, hin, -⟩ := vertex_ne_zero G hout
      obtain ⟨⟨r, hr⟩, hx0, hy0⟩ := vertex_ne_zero G hin
      obtain ⟨a', ha'⟩ := int_of_mem_ne_zero G hx hx0
      obtain ⟨b', hb'⟩ := int_of_mem_ne_zero G hy hy0
      exact hall ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨n + r + 2 - a' - b', by
        push_cast; rw [hn, hr, ha', hb']; ring⟩⟩
    rw [tsum_congr hP0, tsum_congr hI0]

/-! ## Associativity of `μ` -/

section Category
variable (hC2 : C2Cofinite (orbifoldVOA G)) (hfg : FinGen (orbifold G).adjointRestrict)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **Associativity at the level of weak-module maps**:
`(μ ⊠ 1) ≫ μ = α ≫ (1 ⊠ μ) ≫ μ` on the carrier of `(V ⊠ V) ⊠ V`. -/
theorem mulWeakHom_assoc :
    (homComp (mulWeakHom G hfg hC2)
      (tensorMap hC2 (tensorModule hC2 (ambientLog G) (ambientLog G) hfg hfg) (ambientLog G)
        (tensorModule_finGen hC2 (ambientLog G) (ambientLog G) hfg hfg) hfg
        (ambientLog G) (ambientLog G) hfg hfg
        (mulWeakHom G hfg hC2) (weakIdentity (orbifold G).adjointRestrict))).toLinearMap =
    (homComp (mulWeakHom G hfg hC2)
      (homComp
        (tensorMap hC2 (ambientLog G) (tensorModule hC2 (ambientLog G) (ambientLog G) hfg hfg)
          hfg (tensorModule_finGen hC2 (ambientLog G) (ambientLog G) hfg hfg)
          (ambientLog G) (ambientLog G) hfg hfg
          (weakIdentity (orbifold G).adjointRestrict) (mulWeakHom G hfg hC2))
        (tensorAssociatorHom hC2 (ambientLog G) (ambientLog G) (ambientLog G)
          hfg hfg hfg))).toLinearMap := by
  apply leftTriple_linearMap_ext_of_completed_iterate hC2 (ambientLog G) (ambientLog G)
    (ambientLog G) hfg hfg hfg
  intro f a b c β x y z hx hy hz t ht
  -- abbreviations
  let A := ambientLog G
  let T := tensorModule hC2 A A hfg hfg
  let hT : FinGen T.toWeakModule := tensorModule_finGen hC2 A A hfg hfg
  let μ := mulWeakHom G hfg hC2
  let Yv := vertexIntertwiner G
  let θ := tensorIntertwiner hC2 A A hfg hfg
  let η := tensorIntertwiner hC2 T A hT hfg
  let Tm := tensorMap hC2 T A hT hfg A A hfg hfg μ (weakIdentity (orbifold G).adjointRestrict)
  have hY1 : postcompose μ (postcompose Tm η) =
      precompose μ (weakIdentity (orbifold G).adjointRestrict) Yv := by
    have h := tensorMap_intertwiner hC2 T A hT hfg A A hfg hfg μ
      (weakIdentity (orbifold G).adjointRestrict)
    refine (congrArg (postcompose μ) h).trans ?_
    exact (postcompose_precompose' _ _ _ _).trans
      (congrArg (precompose _ _) (mulWeakHom_intertwiner G hfg hC2))
  have hI1 := completedLogIterate_postcompose A A A
    (leftTripleModule hC2 A A hfg hfg A hfg) T (tensorModule hC2 A A hfg hfg) Tm η θ
    t 0 c β (f ∘ₗ μ.toLinearMap) x y ⟨z, hz⟩
  have hI2 := completedLogIterate_postcompose A A A (tensorModule hC2 A A hfg hfg) T A μ
    (postcompose Tm η) θ t 0 c β f x y ⟨z, hz⟩
  have hI3 := completedLogIterate_precompose_left A A A A T A μ Yv θ t 0 c β f x y ⟨z, hz⟩
  have hI4 : completedLogIterate A A A A T (postcompose μ (postcompose Tm η)) θ t 0 c β f x y
      ⟨z, hz⟩ = completedLogIterate A A A A A Yv Yv t 0 c β f x y ⟨z, hz⟩ := by
    refine (congrArg (fun Y => completedLogIterate A A A A T Y θ t 0 c β f x y ⟨z, hz⟩)
      hY1).trans (hI3.trans ?_)
    exact congrArg (fun Y => completedLogIterate A A A A A Yv Y t 0 c β f x y ⟨z, hz⟩)
      (mulWeakHom_intertwiner G hfg hC2)
  have hLeftVal : completedLogIterate A A A (leftTripleModule hC2 A A hfg hfg A hfg) T η θ
      t 0 c β ((f ∘ₗ μ.toLinearMap) ∘ₗ Tm.toLinearMap) x y ⟨z, hz⟩ =
      completedLogIterate A A A A A Yv Yv t 0 c β f x y ⟨z, hz⟩ :=
    hI1.symm.trans (hI2.symm.trans hI4)
  -- the right path: the completed product of `Y_W` with itself
  let Tm' := tensorMap hC2 A T hfg hT A A hfg hfg (weakIdentity (orbifold G).adjointRestrict) μ
  let ζ := tensorIntertwiner hC2 A T hfg hT
  have hA := tensorAssociatorHom_completed_shift (β := β) hC2 A A A hfg hfg hfg hx hy hz
    (f ∘ₗ (homComp μ Tm').toLinearMap) ht 0
  simp only [add_zero] at hA
  have hY2 : postcompose μ (postcompose Tm' ζ) =
      precompose (weakIdentity (orbifold G).adjointRestrict) μ Yv := by
    have h := tensorMap_intertwiner hC2 A T hfg hT A A hfg hfg
      (weakIdentity (orbifold G).adjointRestrict) μ
    refine (congrArg (postcompose μ) h).trans ?_
    exact (postcompose_precompose' _ _ _ _).trans
      (congrArg (precompose _ _) (mulWeakHom_intertwiner G hfg hC2))
  have hP1 := completedLogProduct_postcompose A A A
    (rightTripleModule hC2 A A hfg hfg A hfg) T (tensorModule hC2 A A hfg hfg) Tm' ζ θ
    (Complex.log (1 + Complex.exp t)) 0 a β (f ∘ₗ μ.toLinearMap) ⟨x, hx⟩ y z
  have hP2 := completedLogProduct_postcompose A A A (tensorModule hC2 A A hfg hfg) T A μ
    (postcompose Tm' ζ) θ (Complex.log (1 + Complex.exp t)) 0 a β f ⟨x, hx⟩ y z
  have hP3 := completedLogProduct_precompose_right A A A A T A μ Yv θ
    (Complex.log (1 + Complex.exp t)) 0 a β f ⟨x, hx⟩ y z
  have hP4 : completedLogProduct A A A A T (postcompose μ (postcompose Tm' ζ)) θ
      (Complex.log (1 + Complex.exp t)) 0 a β f ⟨x, hx⟩ y z =
      completedLogProduct A A A A A Yv Yv (Complex.log (1 + Complex.exp t)) 0 a β f
        ⟨x, hx⟩ y z := by
    refine (congrArg (fun Y => completedLogProduct A A A A T Y θ
      (Complex.log (1 + Complex.exp t)) 0 a β f ⟨x, hx⟩ y z) hY2).trans (hP3.trans ?_)
    exact congrArg (fun Y => completedLogProduct A A A A A Yv Y
      (Complex.log (1 + Complex.exp t)) 0 a β f ⟨x, hx⟩ y z) (mulWeakHom_intertwiner G hfg hC2)
  have hRightVal : completedLogIterate A A A (leftTripleModule hC2 A A hfg hfg A hfg) T η θ
      t 0 c β ((f ∘ₗ (homComp μ Tm').toLinearMap) ∘ₗ
        (tensorAssociatorHom hC2 A A A hfg hfg hfg).toLinearMap) x y ⟨z, hz⟩ =
      completedLogProduct A A A A A Yv Yv (Complex.log (1 + Complex.exp t)) 0 a β f
        ⟨x, hx⟩ y z :=
    hA.symm.trans (hP1.symm.trans (hP2.symm.trans hP4))
  exact hLeftVal.trans ((vertex_completed_assoc G hC2 hfg hx hy hz f ht).symm.trans
    hRightVal.symm)

end Category

end VOA.Classification.COne.McRaeO3
