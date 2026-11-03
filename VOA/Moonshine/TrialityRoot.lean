/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.TripletScreening
import VOA.Examples.LatticeGenInstance
import VOA.Core.Automorphism
import VOA.Core.ScreeningKernel
import VOA.Modularity.Twisted

/-!
# Root exponentials in a lattice VOA  (Moonshine step M8g ingredients)

For an even positive-definite lattice `L` and a lattice vector `α ≠ 0`, the zero mode
`Q_α := (e^α)₍₀₎` of the charged vacuum is **locally nilpotent** on `V_L`.  The reason is pure
bookkeeping of the bigrading `bigradα (d, β)` (boson degree `d`, charge `β`):

  `Q_α : bigradα (d, β) → bigradα (d − 1 − ⟨α,β⟩, β + α)`            (`Qscr_mem_bigradα`)

so `Q_αᵏ` lands in boson degree `d − k − k⟨α,β⟩ − ⟨α,α⟩·k(k−1)/2`, which is negative for `k`
large because `⟨α,α⟩ > 0`; the negative-degree pieces are `⊥`.

When `⟨α,α⟩ = 2` the state `e^α` has weight `1`, so `exp(c·Q_α)` is an **inner automorphism**
of `V_L` (`VertexOperatorAlgebra.inner`; the condition `(e^α)₍₀₎ ω = 0` holds for every
weight-one state, `screening_conformalVector`).  These are the unipotent generators of the
`SL₂` attached to the root `α`; FLM/DGM's triality on the Niemeier lattice VOA `V_{N(A₁²⁴)}` is a
product of such exponentials and a momentum-sign automorphism (`TrialityGolay.lean`).

We also record the generic **restriction of an involution to an orbifold**: an involution `σ`
with `σ G σ ⊆ G` restricts to an automorphism of `V^G` (`orbifoldInvol`).

## Main results
* `LatGen.Qscr_mem_bigradα`, `LatGen.Qscr_pow_mem_bigradα` — the bigrading shift.
* `LatGen.isLocNilp_Qscr` — `Q_α` is locally nilpotent for every `α ≠ 0` (`L` pos. def.).
* `LatGen.zeroMode_latChargeGen` — `Q_α` is the VOA zero mode `o(e^α)` of `latticeVOAGen`.
* `LatGen.rootExp : Aut (latticeVOAGen L hEven hPos)` — `exp(c·(e^α)₍₀₎)` for `⟨α,α⟩ = 2`.
* `LatGen.rootExp_apply_of_Qscr_eq_zero`, `LatGen.rootExp_comm_of_fix` — fixed vectors and
  commutation with automorphisms fixing `e^α`.
* `VOA.orbifoldInvol` — an involution normalising `G` acts on the orbifold `V^G`.

## Status
All declarations `sorry`-free; no new axioms.  Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN VOA.LatGen.Screen

variable (L : IntegralLattice)

/-! ## §1  The bigrading shift of `Q_α = (e^α)₍₀₎` -/

theorem latStateGen_eq_mkEα (p : FockN (rank L)) (β : L.carrier) :
    latStateGen L p β = mkEα L β p := rfl

/-- `Q_α` shifts the bigrading: `bigradα (d, β) → bigradα (d − 1 − ⟨α,β⟩, β + α)`. -/
theorem Qscr_mem_bigradα (α : L.carrier) {d : ℤ} {β : L.carrier} {x : LatModuleGen L}
    (hx : x ∈ bigradα L (d, β)) :
    Qscr L α x ∈ bigradα L (d - 1 - L.form α β, β + α) := by
  obtain ⟨q, hq, rfl⟩ := hx
  have hq' : q ∈ gradingZN (rank L) d := hq
  show Qscr L α (mkEα L β q) ∈ _
  rw [← latStateGen_eq_mkEα, Qscr_latStateGen]
  refine Submodule.smul_mem _ _ ⟨EEVec L α (-1 - L.form α β) q, ?_, ?_⟩
  · have h := EEVec_mem_gradingZN L α (-1 - L.form α β) hq'
    rwa [show d + (-1 - L.form α β) = d - 1 - L.form α β by ring] at h
  · show mkEα L (β + α) _ = latStateGen L _ (α + β)
    rw [add_comm α β]; rfl

/-- The boson-degree index after `k` applications of `Q_α`. -/
def qIdx (d a b : ℤ) : ℕ → ℤ
  | 0 => d
  | k + 1 => qIdx d a b k - 1 - (b + k * a)

theorem two_mul_qIdx (d a b : ℤ) (k : ℕ) :
    2 * qIdx d a b k = 2 * d - 2 * k - 2 * k * b - a * k * (k - 1) := by
  induction k with
  | zero => simp [qIdx]
  | succ k ih =>
    simp only [qIdx]
    push_cast
    linear_combination ih

theorem exists_qIdx_neg (d a b : ℤ) (ha : 1 ≤ a) : ∃ k : ℕ, qIdx d a b k < 0 := by
  refine ⟨(d.natAbs + 2 * b.natAbs + 1), ?_⟩
  have h := two_mul_qIdx d a b (d.natAbs + 2 * b.natAbs + 1)
  push_cast at h
  have e1 : d ≤ |d| := le_abs_self d
  have e2 : 0 ≤ |b| + b := by have := neg_abs_le b; linarith
  have e3 : 0 ≤ |d| := abs_nonneg d
  have e4 : 0 ≤ |b| := abs_nonneg b
  set K : ℤ := |d| + 2 * |b| + 1 with hK
  have hK1 : 0 ≤ K - 1 := by omega
  have h1 : 0 ≤ (a - 1) * (K * (K - 1)) := mul_nonneg (by omega) (mul_nonneg (by omega) hK1)
  have h2 : 0 ≤ (K - 1) * |d| := mul_nonneg hK1 e3
  have h3 : 0 ≤ K * (|b| + b) := mul_nonneg (by omega) e2
  nlinarith

/-- Iterating the shift: `Q_αᵏ (bigradα (d, β)) ⊆ bigradα (qIdx … k, β + k•α)`. -/
theorem Qscr_pow_mem_bigradα (α : L.carrier) {d : ℤ} {β : L.carrier} {x : LatModuleGen L}
    (hx : x ∈ bigradα L (d, β)) (k : ℕ) :
    (Qscr L α ^ k) x ∈ bigradα L (qIdx d (L.form α α) (L.form α β) k, β + k • α) := by
  induction k with
  | zero => simpa [qIdx] using hx
  | succ k ih =>
    rw [VOA.pow_succ'_apply]
    have h := Qscr_mem_bigradα L α ih
    have hf : L.form α (β + k • α) = L.form α β + k * L.form α α := by
      rw [map_add, map_nsmul, nsmul_eq_mul]
    rw [hf, add_assoc, ← succ_nsmul] at h
    simpa [qIdx] using h

/-- **Local nilpotency of `(e^α)₍₀₎`** for every nonzero `α` of a positive-definite lattice. -/
theorem isLocNilp_Qscr (hPos : L.PosDef) {α : L.carrier} (hα : α ≠ 0) :
    VOA.IsLocNilp (Qscr L α) := by
  intro v
  have hv : v ∈ (⨆ i, bigradα L i) := by rw [bigradα_iSup_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun y => ∃ N : ℕ, (Qscr L α ^ N) y = 0) hv
    ?_ ?_ ?_
  · rintro ⟨d, β⟩ x hx
    have ha : 1 ≤ L.form α α := hPos α hα
    obtain ⟨k, hk⟩ := exists_qIdx_neg d (L.form α α) (L.form α β) ha
    refine ⟨k, ?_⟩
    have h := Qscr_pow_mem_bigradα L α hx k
    rw [bigradα_eq_bot_of_neg L _ hk, Submodule.mem_bot] at h
    exact h
  · exact ⟨0, by simp⟩
  · rintro x y ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, ?_⟩
    rw [map_add, VOA.pow_apply_eq_zero_of_le hN (le_max_left N M),
      VOA.pow_apply_eq_zero_of_le hM (le_max_right N M), add_zero]

/-! ## §2  `Q_α` as the VOA zero mode, and the root exponentials -/

variable (hEven : L.Even) (hPos : L.PosDef)

theorem zeroMode_latChargeGen (α : L.carrier) :
    (latticeVOAGen L hEven hPos).zeroMode (latChargeGen L α) 1 = Qscr L α := by
  rw [Qscr_eq_mode_YfullGen L hEven hPos α]
  rfl

theorem latChargeGen_mem_bigradα (α : L.carrier) : latChargeGen L α ∈ bigradα L (0, α) :=
  ⟨vacuumN (rank L), mem_gradingZN_of_gradingWN (vacuumN_mem_gradingWN _), rfl⟩

theorem latChargeGen_mem_grading_one {α : L.carrier} (hα : L.form α α = 2) :
    latChargeGen L α ∈ (latticeVOAGen L hEven hPos).grading 1 := by
  have h := bigradα_le_gradingLatGen L 0 α (latChargeGen_mem_bigradα L α)
  have hh : halfNorm L α = 1 := by rw [halfNorm, hα]; rfl
  rwa [hh, zero_add] at h

theorem form_self_ne_zero_of_two {α : L.carrier} (hα : L.form α α = 2) : α ≠ 0 := by
  rintro rfl; simp at hα

theorem zeroMode_smul_latChargeGen (α : L.carrier) (c : ℂ) :
    (latticeVOAGen L hEven hPos).zeroMode (c • latChargeGen L α) 1 = c • Qscr L α := by
  refine LinearMap.ext fun w => ?_
  rw [VertexOperatorAlgebra.zeroMode_apply, LinearMap.smul_apply, ← zeroMode_latChargeGen L hEven hPos α,
    VertexOperatorAlgebra.zeroMode_apply]
  exact PreVertexAlgebra.smul_smul_left _ _ _ _ _

theorem isLocNilp_zeroMode_smul {α : L.carrier} (hα : α ≠ 0) (c : ℂ) :
    VOA.IsLocNilp ((latticeVOAGen L hEven hPos).zeroMode (c • latChargeGen L α) 1) := by
  intro v
  obtain ⟨N, hN⟩ := isLocNilp_Qscr L hPos hα v
  refine ⟨N, ?_⟩
  rw [zeroMode_smul_latChargeGen, smul_pow, LinearMap.smul_apply, hN, smul_zero]

theorem smul_latChargeGen_mem_grading_one {α : L.carrier} (hα : L.form α α = 2) (c : ℂ) :
    c • latChargeGen L α ∈ (latticeVOAGen L hEven hPos).grading 1 :=
  Submodule.smul_mem _ _ (latChargeGen_mem_grading_one L hEven hPos hα)

/-- **The root exponential** `exp(c·(e^α)₍₀₎) ∈ Aut(V_L)` for a root `α` (`⟨α,α⟩ = 2`). -/
noncomputable def rootExp {α : L.carrier} (hα : L.form α α = 2) (c : ℂ) :
    Aut (latticeVOAGen L hEven hPos) :=
  VertexOperatorAlgebra.inner ⟨c • latChargeGen L α, smul_latChargeGen_mem_grading_one L hEven hPos hα c⟩
    (isLocNilp_zeroMode_smul L hEven hPos (form_self_ne_zero_of_two L hα) c)
    (by
      rw [← Screening.screening_eq_zeroMode]
      exact Screening.screening_conformalVector _ (smul_latChargeGen_mem_grading_one L hEven hPos hα c))

theorem rootExp_apply {α : L.carrier} (hα : L.form α α = 2) (c : ℂ) (v : LatModuleGen L) :
    rootExp L hEven hPos hα c v
      = VOA.expFun (isLocNilp_zeroMode_smul L hEven hPos (form_self_ne_zero_of_two L hα) c) v := rfl

/-- `exp(c·Q_α)` fixes every vector killed by `Q_α`. -/
theorem rootExp_apply_of_Qscr_eq_zero {α : L.carrier} (hα : L.form α α = 2) (c : ℂ)
    {v : LatModuleGen L} (hv : Qscr L α v = 0) : rootExp L hEven hPos hα c v = v := by
  rw [rootExp_apply]
  refine VOA.expFun_of_apply_eq_zero _ ?_
  rw [zeroMode_smul_latChargeGen, LinearMap.smul_apply, hv, smul_zero]

theorem expFun_congr {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {D D' : End ℂ 𝒱} (h : D = D')
    (hD : VOA.IsLocNilp D) (hD' : VOA.IsLocNilp D') (x : 𝒱) :
    VOA.expFun hD x = VOA.expFun hD' x := by
  subst h; rfl

/-- An automorphism fixing `e^α` commutes with `exp(c·Q_α)`. -/
theorem rootExp_comm_of_fix {α : L.carrier} (hα : L.form α α = 2) (c : ℂ)
    (β : Aut (latticeVOAGen L hEven hPos)) (hfix : β (latChargeGen L α) = latChargeGen L α) :
    β * rootExp L hEven hPos hα c = rootExp L hEven hPos hα c * β := by
  refine Aut.ext (LinearEquiv.ext fun v => ?_)
  show β (rootExp L hEven hPos hα c v) = rootExp L hEven hPos hα c (β v)
  rw [rootExp_apply, rootExp_apply, VertexOperatorAlgebra.aut_conj_expFun]
  refine expFun_congr ?_ _ _ _
  have h : β (c • latChargeGen L α) = c • latChargeGen L α := by
    rw [← Aut.coe_toLinearEquiv, LinearEquiv.map_smul, Aut.coe_toLinearEquiv, hfix]
  exact congrArg (fun x => (latticeVOAGen L hEven hPos).zeroMode x 1) h

end VOA.LatGen

namespace VOA

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

theorem Aut.apply_apply_of_mul_self {σ : Aut W} (hσ : σ * σ = 1) (x : 𝒱) : σ (σ x) = x := by
  have h := congrArg (fun g : Aut W => g x) hσ
  simpa using h

/-- An involution `σ` normalising `G` maps the orbifold `V^G` into itself. -/
theorem mem_orbifold_of_invol (G : Subgroup (Aut W)) {σ : Aut W} (hσ : σ * σ = 1)
    (hG : ∀ g ∈ G, σ * g * σ ∈ G) {v : 𝒱} (hv : v ∈ (orbifold G).carrier) :
    σ v ∈ (orbifold G).carrier := by
  intro g hg
  have h1 : (σ * g * σ) v = v := hv _ (hG g hg)
  show g (σ v) = σ v
  calc g (σ v) = σ (σ (g (σ v))) := (Aut.apply_apply_of_mul_self hσ _).symm
    _ = σ ((σ * g * σ) v) := rfl
    _ = σ v := by rw [h1]

/-- `σ` restricted to `V^G`, as a linear map. -/
noncomputable def orbifoldInvolMap (G : Subgroup (Aut W)) {σ : Aut W} (hσ : σ * σ = 1)
    (hG : ∀ g ∈ G, σ * g * σ ∈ G) : (orbifold G).carrier →ₗ[ℂ] (orbifold G).carrier :=
  (σ.toLinearEquiv.toLinearMap.comp (orbifold G).carrier.subtype).codRestrict _
    (fun v => mem_orbifold_of_invol G hσ hG v.2)

theorem orbifoldInvolMap_invol (G : Subgroup (Aut W)) {σ : Aut W} (hσ : σ * σ = 1)
    (hG : ∀ g ∈ G, σ * g * σ ∈ G) (v : (orbifold G).carrier) :
    orbifoldInvolMap G hσ hG (orbifoldInvolMap G hσ hG v) = v :=
  Subtype.ext (Aut.apply_apply_of_mul_self hσ (v : 𝒱))

/-- **An involution normalising `G` is an automorphism of the orbifold VOA `V^G`.** -/
noncomputable def orbifoldInvol (G : Subgroup (Aut W)) {σ : Aut W} (hσ : σ * σ = 1)
    (hG : ∀ g ∈ G, σ * g * σ ∈ G) : Aut (orbifoldVOA G) where
  toLinearEquiv := LinearEquiv.ofInvolutive (orbifoldInvolMap G hσ hG) (orbifoldInvolMap_invol G hσ hG)
  map_smul' u n v := Subtype.ext (σ.map_smul (u : 𝒱) n v)
  map_vacuum := Subtype.ext σ.map_vacuum
  map_omega := Subtype.ext σ.map_omega

@[simp] theorem orbifoldInvol_coe (G : Subgroup (Aut W)) {σ : Aut W} (hσ : σ * σ = 1)
    (hG : ∀ g ∈ G, σ * g * σ ∈ G) (v : (orbifold G).carrier) :
    ((orbifoldInvol G hσ hG v : (orbifold G).carrier) : 𝒱) = σ v := rfl

theorem orbifoldInvol_sq (G : Subgroup (Aut W)) {σ : Aut W} (hσ : σ * σ = 1)
    (hG : ∀ g ∈ G, σ * g * σ ∈ G) : orbifoldInvol G hσ hG * orbifoldInvol G hσ hG = 1 :=
  Aut.ext (LinearEquiv.ext fun v => orbifoldInvolMap_invol G hσ hG v)

end VOA
