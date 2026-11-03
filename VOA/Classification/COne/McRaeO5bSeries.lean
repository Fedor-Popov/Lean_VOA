/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO5bAssoc

/-! # O5b, step 2: completed iterates and products on a twisted summand are integer series

Setting: `(X, a)` a left module of the O3 algebra `V`, `p : X ⟶ X` a module endomorphism with
`g`-twisted image. `TwistFacts a p g` records what O5(a) proved: on `range p`, for `g`-fixed `v`,
the modes `(actY a)_{n;k} v` vanish for `k ≥ 1` and for `n ∉ ℤ`, and `p` intertwines `actY a`.

For `g`-fixed homogeneous `u ∈ V_A`, `v ∈ V_B` (`A, B ∈ ℤ`), `x ∈ range p` of generalized weight
`c`, and the output weight `β = A + B + c - D - 2` (`D ∈ ℤ`):

* `iterate_series`: the completed iterate `⟨f, 𝒴_a(Y_W(u, e^{ℓ₀}) v, e^{ℓ₂}) x⟩_β` is
  `Σ_r e^{ℓ₀(-r-1)} e^{ℓ₂(r-D-1)} f((u_r v)_{D-r} x)`;
* `product_series`: the completed product `⟨f, 𝒴_a(u, e^{ℓ₁}) 𝒴_a(v, e^{ℓ₂}) x⟩_β` is
  `Σ_j e^{ℓ₁(j-D-1)} e^{ℓ₂(-j-1)} f(u_{D-j} v_j x)`.

Both are equalities of `tsum`s (no summability is claimed or needed here): every non-integral
weight contributes zero, so the sums over `ℂ` are sums over one `ℤ`-coset.

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

/-- The mode-level consequences of the twisted condition (O5(a)), without the Jacobi identity. -/
structure TwistFacts {X : LogModuleCat (orbifoldVOA G)}
    (a : tensorObject hC2 (vObj G hfg) X ⟶ X) (p : X ⟶ X) (g : Aut W) : Prop where
  stab : ∀ (n : ℂ) (k : ℕ) (v : V) (x : X),
    p.1 ((actY hC2 a).1 n k v x) = (actY hC2 a).1 n k v (p.1 x)
  logFree : ∀ v : V, g v = v → ∀ (x : X) (n : ℂ) (k : ℕ), 1 ≤ k →
    (actY hC2 a).1 n k v (p.1 x) = 0
  integral : ∀ v : V, g v = v → ∀ (x : X) (n : ℂ), (∀ j : ℤ, n ≠ j) →
    (actY hC2 a).1 n 0 v (p.1 x) = 0

theorem twistFacts_of (G : Subgroup (Aut W)) (hfg : FinGen (orbifold G).adjointRestrict)
    (hC2 : C2Cofinite (orbifoldVOA G)) {X : LogModuleCat (orbifoldVOA G)}
    (a : tensorObject hC2 (vObj G hfg) X ⟶ X) (g : G) (p : X ⟶ X) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    a ≫ p = vObj G hfg ◁ p ≫ a →
    vObj G hfg ◁ p ≫ monodromy (vObj G hfg) X ≫ autHom G hfg g ▷ X ≫ a = vObj G hfg ◁ p ≫ a →
    TwistFacts a p (g : Aut W) := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  intro hmod htw
  exact
    { stab := modHom_modes hC2 a a p hmod
      logFree := fun v hv x n k hk =>
        (twisted_modes hC2 p (autHom G hfg g) a htw v hv x n).1 k hk
      integral := fun v hv x n hn =>
        (twisted_modes hC2 p (autHom G hfg g) a htw v hv x n).2 hn }

/-! ## Blocks without logarithms -/

section Block
variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {N₁ : LogVModule (orbifoldVOA G) M₁}
  {N₂ : LogVModule (orbifoldVOA G) M₂} {N₃ : LogVModule (orbifoldVOA G) M₃}

theorem block_logFree
    (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)
    (ell a b c : ℂ) (x : N₁.weight a) (y : N₂.weight b)
    (h : ∀ k : ℕ, 1 ≤ k → Y.1 (a + b - c - 1) k x y = 0) :
    (pointEvaluationBlock N₁ N₂ N₃ Y ell a b c x y : M₃) =
      Complex.exp (ell * (c - a - b)) • Y.1 (a + b - c - 1) 0 x y := by
  rw [pointEvaluationBlock_fixed_cutoff N₁ N₂ N₃ Y ell a b c x y 1 h]
  simp

end Block

theorem aut_vertex_fixed (g : Aut W) {u v : V} (hu : g u = u) (hv : g v = v) (n : ℂ) :
    g ((vertexIntertwiner G).1 n 0 u v) = (vertexIntertwiner G).1 n 0 u v := by
  by_cases hn : ∃ k : ℤ, (k : ℂ) = n
  · obtain ⟨k, rfl⟩ := hn
    rw [vertexIntertwiner_int, VOA.Aut.map_smul, hu, hv]
  · push Not at hn
    rw [vertexIntertwiner_of_not_int G hn 0 u v]
    exact g.toLinearEquiv.map_zero

theorem actY_smul_left {X : LogModuleCat (orbifoldVOA G)}
    (a : tensorObject hC2 (vObj G hfg) X ⟶ X) (n : ℂ) (k : ℕ) (r : ℂ) (w : V) (y : X) :
    (actY hC2 a).1 n k (r • w) y = r • (actY hC2 a).1 n k w y :=
  LinearMap.congr_fun (LinearMap.map_smul ((actY hC2 a).1 n k) r w) y

theorem actY_zero_left {X : LogModuleCat (orbifoldVOA G)}
    (a : tensorObject hC2 (vObj G hfg) X ⟶ X) (n : ℂ) (k : ℕ) (y : X) :
    (actY hC2 a).1 n k (0 : V) y = 0 :=
  LinearMap.congr_fun (LinearMap.map_zero ((actY hC2 a).1 n k)) y

/-! ## The iterate -/

section Series
variable {X : LogModuleCat (orbifoldVOA G)} {a : tensorObject hC2 (vObj G hfg) X ⟶ X}
  {p : X ⟶ X} {g : Aut W}

/-- **The completed iterate on a twisted summand as an integer series.** -/
theorem iterate_series (hT : TwistFacts a p g) {A B D : ℤ} {c : ℂ} {u v : V}
    (hu : u ∈ (vObj G hfg).act.weight (A : ℂ)) (hv : v ∈ (vObj G hfg).act.weight (B : ℂ))
    (hgu : g u = u) (hgv : g v = v) (x' : X) (hx : p.1 x' ∈ X.act.weight c)
    (f : X →ₗ[ℂ] ℂ) (ℓ₀ ℓ₂ : ℂ) :
    completedLogIterate (vObj G hfg).act (vObj G hfg).act X.act X.act (vObj G hfg).act
        (actY hC2 a) (vertexIntertwiner G) ℓ₀ ℓ₂ c ((A : ℂ) + B + c - D - 2) f u v
        ⟨p.1 x', hx⟩ =
      ∑' r : ℤ, Complex.exp (ℓ₀ * ((-r - 1 : ℤ) : ℂ)) * Complex.exp (ℓ₂ * ((r - D - 1 : ℤ) : ℂ)) *
        f ((actY hC2 a).1 ((D - r : ℤ) : ℂ) 0 (W.smul u r v) (p.1 x')) := by
  classical
  set β : ℂ := (A : ℂ) + B + c - D - 2 with hβ
  set q := evaluatePoint (vObj G hfg).act (vObj G hfg).act (vObj G hfg).act
    (vertexIntertwiner G) ℓ₀ u v with hq
  have hqv : ∀ γ : ℂ, (q γ).1 = Complex.exp (ℓ₀ * (γ - A - B)) •
      (vertexIntertwiner G).1 (A + B - γ - 1) 0 u v := fun γ =>
    evaluatePoint_vertex G ℓ₀ hu hv γ
  have hterm : ∀ γ : ℂ, f (pointEvaluationBlock (vObj G hfg).act X.act X.act (actY hC2 a) ℓ₂ γ c
      β (q γ) ⟨p.1 x', hx⟩ : X) = Complex.exp (ℓ₂ * (β - γ - c)) * (Complex.exp (ℓ₀ * (γ - A - B)) *
        f ((actY hC2 a).1 (γ + c - β - 1) 0 ((vertexIntertwiner G).1 (A + B - γ - 1) 0 u v)
          (p.1 x'))) := by
    intro γ
    have hfix : g (q γ).1 = (q γ).1 := by
      rw [hqv, map_smul, aut_vertex_fixed g hgu hgv]
    rw [block_logFree (actY hC2 a) ℓ₂ γ c β (q γ) ⟨p.1 x', hx⟩
      (fun k hk => hT.logFree _ hfix x' _ k hk)]
    change f (Complex.exp (ℓ₂ * (β - γ - c)) • (actY hC2 a).1 (γ + c - β - 1) 0 (q γ).1
      (p.1 x')) = _
    rw [map_smul, smul_eq_mul, hqv, actY_smul_left, map_smul, smul_eq_mul]
  unfold completedLogIterate completedIteratePair
  rw [VOA.Huang.HKLRational.tsum_eq_tsum_int ((A : ℂ) + B - 1) ?supp]
  case supp =>
    intro γ hγ
    by_contra hcon
    apply hγ
    rw [hterm]
    by_cases h0 : (vertexIntertwiner G).1 (A + B - γ - 1) 0 u v = 0
    · rw [h0, actY_zero_left, map_zero, mul_zero, mul_zero]
    · obtain ⟨⟨k, hk⟩, -, -⟩ := vertex_ne_zero G h0
      exact absurd ⟨k, by rw [hk]; ring⟩ hcon
  refine tsum_congr fun r => ?_
  rw [hterm]
  have e1 : (A : ℂ) + B - ((A : ℂ) + B - 1 - r) - 1 = (r : ℂ) := by ring
  have e2 : (A : ℂ) + B - 1 - r + c - β - 1 = ((D - r : ℤ) : ℂ) := by rw [hβ]; push_cast; ring
  have e3 : β - ((A : ℂ) + B - 1 - r) - c = ((r - D - 1 : ℤ) : ℂ) := by rw [hβ]; push_cast; ring
  have e4 : (A : ℂ) + B - 1 - r - A - B = ((-r - 1 : ℤ) : ℂ) := by push_cast; ring
  rw [e1, e2, e3, e4, vertexIntertwiner_int]
  ring

/-- **The completed product on a twisted summand as an integer series.** -/
theorem product_series (hT : TwistFacts a p g) {A B D : ℤ} {c : ℂ} {u v : V}
    (hu : u ∈ (vObj G hfg).act.weight (A : ℂ)) (hv : v ∈ (vObj G hfg).act.weight (B : ℂ))
    (hgu : g u = u) (hgv : g v = v) (x' : X) (hx : p.1 x' ∈ X.act.weight c)
    (f : X →ₗ[ℂ] ℂ) (ℓ₁ ℓ₂ : ℂ) :
    completedLogProduct (vObj G hfg).act (vObj G hfg).act X.act X.act X.act
        (actY hC2 a) (actY hC2 a) ℓ₁ ℓ₂ (A : ℂ) ((A : ℂ) + B + c - D - 2) f ⟨u, hu⟩ v (p.1 x') =
      ∑' j : ℤ, Complex.exp (ℓ₁ * ((j - D - 1 : ℤ) : ℂ)) * Complex.exp (ℓ₂ * ((-j - 1 : ℤ) : ℂ)) *
        f ((actY hC2 a).1 ((D - j : ℤ) : ℂ) 0 u ((actY hC2 a).1 (j : ℂ) 0 v (p.1 x'))) := by
  classical
  set β : ℂ := (A : ℂ) + B + c - D - 2 with hβ
  set q := evaluatePoint (vObj G hfg).act X.act X.act (actY hC2 a) ℓ₂ v (p.1 x') with hq
  have hqv : ∀ b : ℂ, (q b).1 = Complex.exp (ℓ₂ * (b - B - c)) •
      (actY hC2 a).1 (B + c - b - 1) 0 v (p.1 x') := by
    intro b
    rw [hq, evaluatePoint_homogeneous (vObj G hfg).act X.act X.act (actY hC2 a) ℓ₂ hv hx b]
    congr 1
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      rw [hT.logFree v hgv x' _ k (Nat.one_le_iff_ne_zero.mpr hk), smul_zero]
    · intro h; exfalso; apply h
      simp only [Finset.mem_range, pointLogCutoff]
      omega
  have hqp : ∀ b : ℂ, (q b).1 = p.1 (Complex.exp (ℓ₂ * (b - B - c)) •
      (actY hC2 a).1 (B + c - b - 1) 0 v x') := by
    intro b
    rw [hqv, map_smul, hT.stab]
  have hterm : ∀ b : ℂ, f (pointEvaluationBlock (vObj G hfg).act X.act X.act (actY hC2 a) ℓ₁
      (A : ℂ) b β ⟨u, hu⟩ (q b) : X) = Complex.exp (ℓ₁ * (β - A - b)) *
        (Complex.exp (ℓ₂ * (b - B - c)) * f ((actY hC2 a).1 (A + b - β - 1) 0 u
          ((actY hC2 a).1 (B + c - b - 1) 0 v (p.1 x')))) := by
    intro b
    rw [block_logFree (actY hC2 a) ℓ₁ (A : ℂ) b β ⟨u, hu⟩ (q b)
      (fun k hk => by
        change (actY hC2 a).1 _ k u (q b).1 = 0
        rw [hqp]; exact hT.logFree u hgu _ _ k hk)]
    change f (Complex.exp (ℓ₁ * (β - A - b)) • (actY hC2 a).1 (A + b - β - 1) 0 u (q b).1) = _
    rw [hqv]
    simp only [map_smul, smul_eq_mul]
  unfold completedLogProduct completedProductPair
  rw [VOA.Huang.HKLRational.tsum_eq_tsum_int ((B : ℂ) + c - 1) ?supp]
  case supp =>
    intro b hb
    by_contra hcon
    apply hb
    rw [hterm]
    have h0 : (actY hC2 a).1 (B + c - b - 1) 0 v (p.1 x') = 0 := by
      refine hT.integral v hgv x' _ fun j hj => hcon ⟨j, ?_⟩
      linear_combination -hj
    simp only [h0, map_zero, mul_zero]
  refine tsum_congr fun j => ?_
  rw [hterm]
  have e1 : (B : ℂ) + c - ((B : ℂ) + c - 1 - j) - 1 = (j : ℂ) := by ring
  have e2 : (A : ℂ) + ((B : ℂ) + c - 1 - j) - β - 1 = ((D - j : ℤ) : ℂ) := by
    rw [hβ]; push_cast; ring
  have e3 : β - A - ((B : ℂ) + c - 1 - j) = ((j - D - 1 : ℤ) : ℂ) := by rw [hβ]; push_cast; ring
  have e4 : (B : ℂ) + c - 1 - j - B - c = ((-j - 1 : ℤ) : ℂ) := by push_cast; ring
  rw [e1, e2, e3, e4]
  ring

end Series

end VOA.Classification.COne.McRaeO5b
