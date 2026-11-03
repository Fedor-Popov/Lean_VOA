/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO5bSeries
import VOA.Classification.COne.McRaeO5bGlue

/-! # O5b, step 3: the three channels of a twisted summand

Fix `g`-fixed homogeneous `u ∈ V_A`, `v ∈ V_B`, `x = p x'` of generalized weight `c`, a functional
`f`, and an index line `D`. The coefficient sequences

* `sA n = f(u_{-n-1} v_{D+n+1} x)` (product, `u` at `ζ`, `v` at `1`),
* `tC n = f(v_{D+n+1} u_{-n-1} x)` (reversed product),
* `qD m = f((u_{-m-1} v)_{D+m+1} x)` (iterate)

satisfy (with `ζ` real):

* `channel_AD`: `Σ sA_n ζ^n = Σ qD_m (ζ-1)^m` on `(1, 3/2)` — the module axiom
  (`actY_completed_assoc`);
* `channel_CD`: `Σ tC_n ζ^n = Σ qD_m (ζ-1)^m` on `(1/2, 1)` — skew-symmetry of `Y_W`
  (`omega_vertexIntertwiner`), the inner translation theorem (`completedLogIterate_omega_inner`)
  and the module axiom at the scale `ζ` (`actY_completed_assoc_shift`). This is where the
  commutativity of the algebra enters.

Together with the finiteness of the sequences, their convergence (Huang's differential
equations: `summable_log_product_series`, `summable_log_iterate_series`) and the rational
Fuchsian equation of the product row (`exists_ratFuchsian_log_product_homogeneous`), this is the
input of `residue_of_channels`.

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

section Channels
variable {X : LogModuleCat (orbifoldVOA G)} (a : tensorObject hC2 (vObj G hfg) X ⟶ X)
  (p : X ⟶ X) (f : X →ₗ[ℂ] ℂ) (D : ℤ) (u v : V) (x' : X)

/-- The product coefficients. -/
def sA (n : ℤ) : ℂ :=
  f ((actY hC2 a).1 ((-n - 1 : ℤ) : ℂ) 0 u ((actY hC2 a).1 ((D + n + 1 : ℤ) : ℂ) 0 v (p.1 x')))

/-- The reversed-product coefficients. -/
def tC (n : ℤ) : ℂ :=
  f ((actY hC2 a).1 ((D + n + 1 : ℤ) : ℂ) 0 v ((actY hC2 a).1 ((-n - 1 : ℤ) : ℂ) 0 u (p.1 x')))

/-- The iterate coefficients. -/
def qD (m : ℤ) : ℂ :=
  f ((actY hC2 a).1 ((D + m + 1 : ℤ) : ℂ) 0 (W.smul u (-m - 1) v) (p.1 x'))

end Channels

/-! ## Elementary facts on exponentials and logarithms -/

theorem exp_mul_intCast (ℓ : ℂ) (k : ℤ) : Complex.exp (ℓ * (k : ℂ)) = Complex.exp ℓ ^ k :=
  exp_mul_int ℓ k

theorem log_real_mem_overlap {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    Complex.log (ρ : ℂ) ∈ overlapDomain := by
  refine ⟨?_, ?_⟩
  · rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
    exact Real.log_neg h0 h1
  · rw [Complex.log_im, Complex.arg_ofReal_of_nonneg h0.le, abs_zero]
    positivity

/-- Reindexing `j = D + n + 1`. -/
theorem tsum_reindex_add (F : ℤ → ℂ) (D : ℤ) :
    ∑' j : ℤ, F j = ∑' n : ℤ, F (D + n + 1) := by
  rw [← (Equiv.addLeft (D + 1)).tsum_eq]
  exact tsum_congr fun n => by simp only [Equiv.coe_addLeft]; ring_nf

/-- Reindexing `r = -m - 1`. -/
theorem tsum_reindex_neg (F : ℤ → ℂ) : ∑' r : ℤ, F r = ∑' m : ℤ, F (-m - 1) := by
  rw [← (Equiv.subLeft (-1 : ℤ)).tsum_eq]
  exact tsum_congr fun m => by simp only [Equiv.subLeft_apply]; ring_nf

section Ident
variable {X : LogModuleCat (orbifoldVOA G)} {a : tensorObject hC2 (vObj G hfg) X ⟶ X}
  {p : X ⟶ X} {g : Aut W}

/-- The completed product in the `A`-channel. -/
theorem product_A (hT : TwistFacts a p g) {A B D : ℤ} {c : ℂ} {u v : V}
    (hu : u ∈ (vObj G hfg).act.weight (A : ℂ)) (hv : v ∈ (vObj G hfg).act.weight (B : ℂ))
    (hgu : g u = u) (hgv : g v = v) (x' : X) (hx : p.1 x' ∈ X.act.weight c)
    (f : X →ₗ[ℂ] ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    completedLogProduct (vObj G hfg).act (vObj G hfg).act X.act X.act X.act
        (actY hC2 a) (actY hC2 a) (Complex.log ζ) 0 (A : ℂ) ((A : ℂ) + B + c - D - 2) f
        ⟨u, hu⟩ v (p.1 x') = ∑' n : ℤ, sA a p f D u v x' n * ζ ^ n := by
  rw [product_series hT hu hv hgu hgv x' hx f, tsum_reindex_add _ D]
  refine tsum_congr fun n => ?_
  rw [exp_mul_intCast, exp_mul_intCast, Complex.exp_log hζ, Complex.exp_zero, one_zpow, mul_one,
    sA, show D + n + 1 - D - 1 = n by ring, show D - (D + n + 1) = -n - 1 by ring]
  ring

/-- The completed iterate in the `D`-channel. -/
theorem iterate_D (hT : TwistFacts a p g) {A B D : ℤ} {c : ℂ} {u v : V}
    (hu : u ∈ (vObj G hfg).act.weight (A : ℂ)) (hv : v ∈ (vObj G hfg).act.weight (B : ℂ))
    (hgu : g u = u) (hgv : g v = v) (x' : X) (hx : p.1 x' ∈ X.act.weight c)
    (f : X →ₗ[ℂ] ℂ) (ℓ₀ : ℂ) :
    completedLogIterate (vObj G hfg).act (vObj G hfg).act X.act X.act (vObj G hfg).act
        (actY hC2 a) (vertexIntertwiner G) ℓ₀ 0 c ((A : ℂ) + B + c - D - 2) f u v
        ⟨p.1 x', hx⟩ = ∑' m : ℤ, qD a p f D u v x' m * Complex.exp ℓ₀ ^ m := by
  rw [iterate_series hT hu hv hgu hgv x' hx f, tsum_reindex_neg]
  refine tsum_congr fun m => ?_
  rw [exp_mul_intCast, exp_mul_intCast, Complex.exp_zero, one_zpow, mul_one, qD,
    show -(-m - 1) - 1 = m by ring, show D - (-m - 1) = D + m + 1 by ring]
  ring

/-- **The `A = D` identity** (associativity). -/
theorem channel_AD (hX : letI := logarithmicMonoidalCategory hC2
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a)
    (hT : TwistFacts a p g) {A B D : ℤ} {c : ℂ} {u v : V}
    (hu : u ∈ (vObj G hfg).act.weight (A : ℂ)) (hv : v ∈ (vObj G hfg).act.weight (B : ℂ))
    (hgu : g u = u) (hgv : g v = v) (x' : X) (hx : p.1 x' ∈ X.act.weight c)
    (f : X →ₗ[ℂ] ℂ) (x : ℝ) (hx1 : 1 < x) (hx2 : x < 3 / 2) :
    ∑' n : ℤ, sA a p f D u v x' n * (x : ℂ) ^ n =
      ∑' m : ℤ, qD a p f D u v x' m * ((x : ℂ) - 1) ^ m := by
  have hρ0 : 0 < x - 1 := by linarith
  have hρ1 : x - 1 < 1 := by linarith
  have ht := log_real_mem_overlap hρ0 hρ1
  have hexp : Complex.exp (Complex.log ((x - 1 : ℝ) : ℂ)) = (x : ℂ) - 1 := by
    rw [Complex.exp_log (by exact_mod_cast hρ0.ne')]; push_cast; ring
  have hassoc := actY_completed_assoc G hfg hC2 a hX (β := (A : ℂ) + B + c - D - 2) hu hv hx f ht
  rw [hexp, show (1 : ℂ) + ((x : ℂ) - 1) = x by ring] at hassoc
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith)
  rw [product_A hT hu hv hgu hgv x' hx f hx0, iterate_D hT hu hv hgu hgv x' hx f, hexp] at hassoc
  exact hassoc

/-- **The `C = D` identity** (commutativity of the algebra, through skew-symmetry). -/
theorem channel_CD (hX : letI := logarithmicMonoidalCategory hC2
      IsLeftModule (mulHom G hfg hC2) (unitHom G hfg) a)
    (hT : TwistFacts a p g) {A B D : ℤ} {c : ℂ} {u v : V}
    (hu : u ∈ (vObj G hfg).act.weight (A : ℂ)) (hv : v ∈ (vObj G hfg).act.weight (B : ℂ))
    (hgu : g u = u) (hgv : g v = v) (x' : X) (hx : p.1 x' ∈ X.act.weight c)
    (f : X →ₗ[ℂ] ℂ) (x : ℝ) (hx1 : 1 / 2 < x) (hx2 : x < 1) :
    ∑' n : ℤ, tC a p f D u v x' n * (x : ℂ) ^ n =
      ∑' m : ℤ, qD a p f D u v x' m * ((x : ℂ) - 1) ^ m := by
  set β : ℂ := (A : ℂ) + B + c - D - 2 with hβ
  set ρ : ℝ := 1 - x with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hρ1 : ρ < 1 / 2 := by rw [hρ]; linarith
  set ℓ₀ : ℂ := Complex.log (ρ : ℂ) - Real.pi * Complex.I with hℓ₀
  have hexpℓ₀ : Complex.exp ℓ₀ = (x : ℂ) - 1 := by
    rw [hℓ₀, Complex.exp_sub, Complex.exp_log (by exact_mod_cast hρ0.ne'),
      Complex.exp_pi_mul_I, hρ]
    push_cast; ring
  -- step 1: the `D` channel as an iterate at `(ℓ₀, 0)`
  have h1 := iterate_D hT hu hv hgu hgv x' hx f (D := D) ℓ₀
  rw [hexpℓ₀] at h1
  -- step 2: skew-symmetry of `Y_W` and the inner translation theorem
  have hsmall : ‖Complex.exp (ℓ₀ - 0)‖ < 1 / 2 := by
    rw [sub_zero, hexpℓ₀, show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hω := completedLogIterate_omega_inner hC2 (vObj G hfg).act (vObj G hfg).act X.act X.act
    (vObj G hfg).act (vObj G hfg).finiteGeneration (vObj G hfg).finiteGeneration
    X.finiteGeneration X.finiteGeneration (vObj G hfg).finiteGeneration (actY hC2 a)
    (vertexIntertwiner G) 0 hu hv hx f β hsmall
  have hΩ : omegaEquiv (vObj G hfg).act.toWeakModule (vObj G hfg).act.toWeakModule
      (vObj G hfg).act.toWeakModule 0 (vertexIntertwiner G) = vertexIntertwiner G :=
    omega_vertexIntertwiner G
  rw [hΩ] at hω
  -- step 3: associativity for `(v, u)` at the scale `x`
  set s : ℂ := Complex.log (x : ℂ) with hs
  have hx0 : 0 < x := by linarith
  have hlog1 : 0 + Complex.log (1 + Complex.exp (ℓ₀ - 0)) = s := by
    rw [sub_zero, hexpℓ₀, zero_add, hs]; ring_nf
  set t : ℂ := Complex.log ((ρ / x : ℝ) : ℂ) with ht
  have htmem : t ∈ overlapDomain :=
    log_real_mem_overlap (div_pos hρ0 hx0) (by rw [div_lt_one hx0]; linarith)
  have hts : t + s = ℓ₀ + kap 0 := by
    rw [ht, hs, hℓ₀, kap, ← Complex.ofReal_log (div_pos hρ0 hx0).le,
      ← Complex.ofReal_log hx0.le, ← Complex.ofReal_log hρ0.le, Real.log_div hρ0.ne' hx0.ne']
    push_cast; ring
  have hassoc := actY_completed_assoc_shift G hfg hC2 a hX (β := β) hv hu hx f htmem s
  rw [hts] at hassoc
  rw [hlog1] at hω
  -- the left end: the product `(v, u)` at `(0, log x)`
  have hone : Complex.log (1 + Complex.exp t) + s = 0 := by
    rw [ht, Complex.exp_log (by exact_mod_cast (div_pos hρ0 hx0).ne'), hs]
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have e : (1 : ℂ) + ((ρ / x : ℝ) : ℂ) = (((x : ℂ))⁻¹) := by
      rw [hρ]; push_cast; field_simp; ring
    rw [e, show ((x : ℂ))⁻¹ = ((x⁻¹ : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (inv_nonneg.mpr hx0.le), ← Complex.ofReal_log hx0.le,
      Real.log_inv]
    push_cast; ring
  rw [hone] at hassoc
  have hP := product_series hT hv hu hgv hgu x' hx f (D := D) 0 s
  have hβ' : (B : ℂ) + A + c - D - 2 = β := by rw [hβ]; ring
  rw [hβ'] at hP
  rw [← h1, hω, ← hassoc, hP]
  conv_rhs => rw [tsum_reindex_neg]
  refine tsum_congr fun n => ?_
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  rw [exp_mul_intCast, exp_mul_intCast, Complex.exp_zero, one_zpow, one_mul, hs,
    Complex.exp_log hxc, tC, show -(-n - 1) - 1 = n by ring, show D - (-n - 1) = D + n + 1 by ring]
  ring

end Ident

end VOA.Classification.COne.McRaeO5b
