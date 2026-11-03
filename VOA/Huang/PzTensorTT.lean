/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.SkewIntertwiner
import VOA.Modules.ContragredientClose

/-!
# The translated contragredient modes satisfy the commutator formula (commutator)

On a module `N`, the **contragredient (opposite) mode** of a homogeneous `u ∈ V_β` is
`tw(u,m) = (−1)^β Σ_j (1/j!) (L₁ʲu)_{2β−m−2−j}`; its library-proved Borcherds identity
(`ContragredientClose.dualAdjResidualMvec_holds`) gives in particular the (reversed) commutator
formula `tw(v,n) tw(u,m) − tw(u,m) tw(v,n) = Σᵢ C(m,i) tw(u_i v, m+n−i)` (`tw_comm`).

The Huang–Lepowsky `P(1)`-action acts on the first factor `w₁` (at distance `1` from the centre)
by the **translated** contragredient modes `D(u,m) = (−1)^β Σ_j (1/j!) Σ_r C(k_j, r) (L₁ʲu)_r`,
`k_j = 2β−m−2−j`.  These are *not* conjugate to `tw` inside `End N` (translation is not inner).
We prove that they satisfy the same commutator formula (`Dcomm_single`) by transporting the
library identity through the **skew-symmetry intertwiner** `W(t, z)φ = e^{zL₋₁} Y_N(φ, −z) t`
(`Moonshine.SkewIntertwiner`, type `(N; N, V)`): its commutator formula `wMode_comm` turns `tw` on
`N` into `D` on the first slot plus `tw` on `V` on the second, and `W(t, z)𝟙 = e^{zL₋₁} t` is
injective.

The `D`'s change the weight by different amounts on different pieces; we keep track of the
pieces in **weight-indexed families** `ℂ →₀ N` (`Dfam`), and of the matching mode of the skew
intertwiner through the integer offset `offs α₀ δ` of a weight `δ ∈ α₀ + ℤ` (`What`).

## Main results
* `tw`, `tw_comm` (library), `Dpiece`, `Dfam`, `What`.
* `what_tw_single`/`what_tw` — `tw(u,m) Ŵ_c(g)φ − Ŵ_c(g) tw_V(u,m)φ = Ŵ_{c+β−m−1}(D(u,m) g)φ`.
* `eq_zero_of_what_vacuum` — injectivity of `g ↦ (Ŵ_c(g)𝟙)_c`.
* `Dcomm_single` — the commutator formula for the translated contragredient modes.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorTT

open VOA VOA.SkewIntertwiner
open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The contragredient modes and their commutator formula -/

/-- The contragredient (opposite) mode `tw(u, m)` on a module, `u` of weight `β`. -/
noncomputable def tw (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) (x : M) : M :=
  (-1 : ℂ) ^ β • ∑ j ∈ Finset.range (β.toNat + 1), ((j.factorial : ℂ)⁻¹) •
    mode (N.YM ((W.L 1 ^ j) u)) (2 * β - m - 2 - (j : ℤ)) x

theorem tw_add (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) (x y : M) :
    tw N β u m (x + y) = tw N β u m x + tw N β u m y := by
  simp only [tw, map_add, smul_add, Finset.sum_add_distrib]

theorem tw_smul (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) (c : ℂ) (x : M) :
    tw N β u m (c • x) = c • tw N β u m x := by
  simp only [tw, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm (c : ℂ) ((-1 : ℂ) ^ β), smul_comm (c : ℂ) ((j.factorial : ℂ)⁻¹)]

theorem tw_zero_state (N : OrdVModule W M) (β : ℤ) (m : ℤ) (x : M) : tw N β 0 m x = 0 := by
  simp only [tw, map_zero, mode_zero, LinearMap.zero_apply, smul_zero, Finset.sum_const_zero]

theorem tw_eq_dualAdj (N : OrdVModule W M) {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ)
    {α : ℂ} {x : M} (hx : x ∈ N.weight α) : tw N β u m x = dualAdj N β u m α x :=
  (dualAdj_clean N hu m hx).symm

/-- The weight of `tw(u, m) x`. -/
theorem tw_mem (N : OrdVModule W M) {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ)
    {α : ℂ} {x : M} (hx : x ∈ N.weight α) : tw N β u m x ∈ N.weight (matchIdx β m α) := by
  rw [tw_eq_dualAdj N hu m hx]; exact dualAdj_mem N β u m α x

/-- **The commutator formula of the contragredient modes** (from the library's module FHL
Borcherds identity, `ℓ = 0`). -/
theorem tw_comm (N : OrdVModule W M) {β γ : ℤ} {u v : 𝒱} (hu : u ∈ W.grading β)
    (hv : v ∈ W.grading γ) (m n : ℤ) {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    tw N γ v n (tw N β u m x) - tw N β u m (tw N γ v n x)
      = ∑ᶠ i : ℤ, cbz m i • tw N (β + γ - i - 1) (W.smul u i v) (m + n - i) x := by
  have h := dualAdjResidualMvec_holds N β u hu γ v hv 0 m n α x hx
  unfold DualAdjResidualMvecAt at h
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, mul_zero,
    zero_smul])] at h
  simp only [cbz_zero_left, if_pos, mul_one, add_zero, zero_add, sub_zero] at h
  have e0 : negOnePow 0 = 1 := by simp [negOnePow]
  rw [e0, one_smul, one_smul] at h
  rw [tw_eq_dualAdj N hu m hx, tw_eq_dualAdj N hv n hx,
    tw_eq_dualAdj N hv n (dualAdj_mem N β u m α x),
    tw_eq_dualAdj N hu m (dualAdj_mem N γ v n α x), h]
  exact finsum_congr fun i => by
    rw [tw_eq_dualAdj N (W.smul_mem_grading hu hv i) _ hx]

/-! ## Integer offsets of weights -/

/-- The integer offset of `δ` from `α₀` (junk `0` off the coset `α₀ + ℤ`). -/
noncomputable def offs (α₀ δ : ℂ) : ℤ :=
  haveI := Classical.propDecidable
  if h : ∃ k : ℤ, δ = α₀ + k then h.choose else 0

theorem offs_add (α₀ : ℂ) (k : ℤ) : offs α₀ (α₀ + k) = k := by
  have h : ∃ k' : ℤ, α₀ + (k : ℂ) = α₀ + k' := ⟨k, rfl⟩
  unfold offs
  rw [dif_pos h]
  have := h.choose_spec
  exact_mod_cast (add_left_cancel this).symm

/-! ## The translated contragredient modes on weight-indexed families -/

/-- The coefficient of the piece `(L₁ʲu)_r`. -/
noncomputable def coefD (β m : ℤ) (j r : ℕ) : ℂ :=
  (-1 : ℂ) ^ β * (j.factorial : ℂ)⁻¹ * cbz (2 * β - m - 2 - (j : ℤ)) (r : ℤ)

/-- The `r`-th piece of `D(u,m)` applied to `y` (placed at weight `δ + β − j − r − 1`). -/
noncomputable def Dterm (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) (δ : ℂ) (y : M) (j r : ℕ) :
    ℂ →₀ M :=
  Finsupp.single (δ + ((β - (j : ℤ) - (r : ℤ) - 1 : ℤ) : ℂ))
    (coefD β m j r • mode (N.YM ((W.L 1 ^ j) u)) (r : ℤ) y)

theorem Dterm_fin (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) (δ : ℂ) (y : M) (j : ℕ) :
    (Function.support (Dterm N β u m δ y j)).Finite := by
  obtain ⟨R, hR⟩ := N.truncation ((W.L 1 ^ j) u) y
  refine (Set.finite_lt_nat R.toNat).subset fun r hr => ?_
  rw [Function.mem_support] at hr
  by_contra h
  apply hr
  simp only [Set.mem_setOf_eq, not_lt] at h
  rw [Dterm, show mode (N.YM ((W.L 1 ^ j) u)) (r : ℤ) y = 0 from hR _ (by omega), smul_zero,
    Finsupp.single_zero]

/-- The piece `D(u,m)(y at weight δ)`. -/
noncomputable def Dpiece (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) (δ : ℂ) (y : M) :
    ℂ →₀ M :=
  ∑ j ∈ Finset.range (β.toNat + 1), ∑ᶠ r : ℕ, Dterm N β u m δ y j r

theorem Dpiece_add (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) (δ : ℂ) (y y' : M) :
    Dpiece N β u m δ (y + y') = Dpiece N β u m δ y + Dpiece N β u m δ y' := by
  unfold Dpiece
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← finsum_add_distrib (Dterm_fin N β u m δ y j) (Dterm_fin N β u m δ y' j)]
  refine finsum_congr fun r => ?_
  simp only [Dterm, map_add, smul_add, Finsupp.single_add]

theorem Dpiece_zero (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) (δ : ℂ) :
    Dpiece N β u m δ 0 = 0 := by
  simp [Dpiece, Dterm]

/-- **The translated contragredient mode** `D(u, m)` on weight-indexed families. -/
noncomputable def Dfam (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) :
    (ℂ →₀ M) →+ (ℂ →₀ M) :=
  Finsupp.liftAddHom fun δ =>
    { toFun := Dpiece N β u m δ
      map_zero' := Dpiece_zero N β u m δ
      map_add' := Dpiece_add N β u m δ }

theorem Dfam_single (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) (δ : ℂ) (y : M) :
    Dfam N β u m (Finsupp.single δ y) = Dpiece N β u m δ y :=
  Finsupp.liftAddHom_apply_single _ _ _

/-! ## The skew intertwiner on families -/

/-- `Ŵ_c(g)φ = Σ_δ W(g_δ)_{c + offs(δ)} φ`. -/
noncomputable def What (N : OrdVModule W M) (α₀ : ℂ) (c : ℤ) (φ : 𝒱) : (ℂ →₀ M) →+ M :=
  Finsupp.liftAddHom fun δ =>
    { toFun := fun y => wMode N.toWeakModule y (c + offs α₀ δ) φ
      map_zero' := wMode_zero_right _ _ _
      map_add' := fun y y' => wMode_add_right _ y y' _ _ }

theorem What_single (N : OrdVModule W M) (α₀ : ℂ) (c : ℤ) (φ : 𝒱) (δ : ℂ) (y : M) :
    What N α₀ c φ (Finsupp.single δ y) = wMode N.toWeakModule y (c + offs α₀ δ) φ :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem What_add_phi (N : OrdVModule W M) (α₀ : ℂ) (c : ℤ) (φ ψ : 𝒱) (g : ℂ →₀ M) :
    What N α₀ c (φ + ψ) g = What N α₀ c φ g + What N α₀ c ψ g := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' ih ih' => rw [map_add, map_add, map_add, ih, ih']; abel
  | single δ y => rw [What_single, What_single, What_single, wMode_add_left]

theorem What_smul_phi (N : OrdVModule W M) (α₀ : ℂ) (c : ℤ) (a : ℂ) (φ : 𝒱) (g : ℂ →₀ M) :
    What N α₀ c (a • φ) g = a • What N α₀ c φ g := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' ih ih' => rw [map_add, map_add, ih, ih', smul_add]
  | single δ y => rw [What_single, What_single, wMode_smul_left]

theorem What_sum_phi (N : OrdVModule W M) (α₀ : ℂ) (c : ℤ) {ι : Type*} (s : Finset ι)
    (φ : ι → 𝒱) (g : ℂ →₀ M) :
    What N α₀ c (∑ i ∈ s, φ i) g = ∑ i ∈ s, What N α₀ c (φ i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' ih ih' => rw [map_add, ih, ih', add_zero]
    | single δ y =>
      rw [What_single]
      have := wMode_smul_left N.toWeakModule y (c + offs α₀ δ) 0 0
      simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, What_add_phi, ih]

/-! ## Transport of the contragredient modes through the skew intertwiner -/

theorem mode_adjoint (a : 𝒱) (k : ℤ) (φ : 𝒱) :
    mode ((adjointModule W).YM a) k φ = W.smul a k φ := rfl

theorem what_tw_one (N : OrdVModule W M) (a : 𝒱) (p : ℤ) (y : M) (n : ℤ) (φ : 𝒱) :
    ∃ J : ℕ, (∀ r : ℕ, J ≤ r → mode (N.YM a) (r : ℤ) y = 0) ∧
      mode (N.YM a) p (wMode N.toWeakModule y n φ) - wMode N.toWeakModule y n (W.smul a p φ)
        = ∑ r ∈ Finset.range J, gBinom p r •
            wMode N.toWeakModule (mode (N.YM a) (r : ℤ) y) (p + n - r) φ := by
  obtain ⟨R, hR⟩ := N.truncation a y
  refine ⟨R.toNat, fun r hr => hR _ (by omega), ?_⟩
  exact wMode_comm N.toWeakModule a p y n φ R.toNat (fun j hj => hR _ (by omega))

/-- **Transport identity** (one weight piece):
`tw(u,m) Ŵ_c(y)φ − Ŵ_c(y) tw_V(u,m)φ = Ŵ_{c+β−m−1}(D(u,m) y)φ`. -/
theorem what_tw_single (N : OrdVModule W M) {β : ℤ} {u : 𝒱} (_hu : u ∈ W.grading β) (m : ℤ)
    (α₀ : ℂ) (c k : ℤ) (y : M) (φ : 𝒱) :
    tw N β u m (What N α₀ c φ (Finsupp.single (α₀ + k) y))
      - What N α₀ c (tw (adjointModule W) β u m φ) (Finsupp.single (α₀ + k) y)
      = What N α₀ (c + β - m - 1) φ (Dfam N β u m (Finsupp.single (α₀ + k) y)) := by
  rw [What_single, What_single, offs_add, Dfam_single, Dpiece, map_sum]
  -- the left side, as a sum over `j`
  have hL : wMode N.toWeakModule y (c + k) (tw (adjointModule W) β u m φ)
      = (-1 : ℂ) ^ β • ∑ j ∈ Finset.range (β.toNat + 1), ((j.factorial : ℂ)⁻¹) •
          wMode N.toWeakModule y (c + k)
            (W.smul ((W.L 1 ^ j) u) (2 * β - m - 2 - (j : ℤ)) φ) := by
    rw [← wModeLin_apply, tw, map_smul, map_sum]
    simp only [map_smul, wModeLin_apply, mode_adjoint]
  rw [hL, tw, ← smul_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_sub]
  obtain ⟨J, hJ, hcomm⟩ := what_tw_one N ((W.L 1 ^ j) u) (2 * β - m - 2 - (j : ℤ)) y (c + k) φ
  rw [hcomm]
  -- the right side
  rw [map_finsum _ (Dterm_fin N β u m (α₀ + k) y j)]
  have hoffs : ∀ r : ℕ, offs α₀ (α₀ + (k : ℂ) + ((β - (j : ℤ) - (r : ℤ) - 1 : ℤ) : ℂ))
      = k + (β - j - r - 1) := by
    intro r
    rw [show α₀ + (k : ℂ) + ((β - (j : ℤ) - (r : ℤ) - 1 : ℤ) : ℂ)
      = α₀ + ((k + (β - j - r - 1) : ℤ) : ℂ) by push_cast; ring, offs_add]
  have hterm : ∀ r : ℕ, What N α₀ (c + β - m - 1) φ (Dterm N β u m (α₀ + k) y j r)
      = coefD β m j r • wMode N.toWeakModule (mode (N.YM ((W.L 1 ^ j) u)) (r : ℤ) y)
          (2 * β - m - 2 - (j : ℤ) + (c + k) - r) φ := by
    intro r
    rw [Dterm, What_single, hoffs, wMode_smul_right]
    congr 2
    ring
  rw [finsum_congr hterm, finsum_eq_sum_of_support_subset _ (s := Finset.range J) (by
    intro r hr
    rw [Function.mem_support] at hr
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hr
    rw [hJ r (by omega), wMode_zero_right, smul_zero])]
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_smul, smul_smul, coefD, cbz_apply_nonneg _ (Int.natCast_nonneg r), Int.toNat_natCast]

/-! ## Families supported on one coset `α₀ + ℤ` -/

/-- The families supported on the coset `α₀ + ℤ`. -/
noncomputable def coset (α₀ : ℂ) : Submodule ℂ (ℂ →₀ M) :=
  Finsupp.supported M ℂ {δ | ∃ k : ℤ, δ = α₀ + k}

theorem single_mem_coset (α₀ : ℂ) (k : ℤ) (y : M) :
    Finsupp.single (α₀ + k) y ∈ (coset α₀ : Submodule ℂ (ℂ →₀ M)) :=
  Finsupp.single_mem_supported ℂ y ⟨k, rfl⟩

theorem single_mem_coset' (α₀ : ℂ) (y : M) :
    Finsupp.single α₀ y ∈ (coset α₀ : Submodule ℂ (ℂ →₀ M)) := by
  have := single_mem_coset α₀ 0 y
  simpa using this

theorem Dpiece_mem_coset (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) (α₀ : ℂ) (k : ℤ)
    (y : M) : Dpiece N β u m (α₀ + k) y ∈ (coset α₀ : Submodule ℂ (ℂ →₀ M)) := by
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [finsum_eq_sum _ (Dterm_fin N β u m (α₀ + k) y j)]
  refine Submodule.sum_mem _ fun r _ => ?_
  rw [Dterm, show α₀ + (k : ℂ) + ((β - (j : ℤ) - (r : ℤ) - 1 : ℤ) : ℂ)
    = α₀ + ((k + (β - j - r - 1) : ℤ) : ℂ) by push_cast; ring]
  exact single_mem_coset α₀ _ _

theorem Dfam_mem_coset (N : OrdVModule W M) (β : ℤ) (u : 𝒱) (m : ℤ) (α₀ : ℂ)
    {g : ℂ →₀ M} (hg : g ∈ (coset α₀ : Submodule ℂ (ℂ →₀ M))) :
    Dfam N β u m g ∈ (coset α₀ : Submodule ℂ (ℂ →₀ M)) := by
  induction g using Finsupp.induction with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | single_add a b f ha hb ih =>
    have hsupp : (Finsupp.single a b + f).support = insert a f.support := by
      rw [Finsupp.support_add_eq (by
        rw [Finsupp.support_single _ hb]; exact Finset.disjoint_singleton_left.2 ha),
        Finsupp.support_single _ hb]; rfl
    have hsub : ((Finsupp.single a b + f).support : Set ℂ) ⊆ {δ | ∃ k : ℤ, δ = α₀ + k} :=
      (Finsupp.mem_supported ℂ _).1 hg
    rw [hsupp, Finset.coe_insert, Set.insert_subset_iff] at hsub
    obtain ⟨k, rfl⟩ := hsub.1
    rw [map_add, Dfam_single]
    exact Submodule.add_mem _ (Dpiece_mem_coset N β u m α₀ k b)
      (ih ((Finsupp.mem_supported ℂ _).2 hsub.2))

theorem Dfam_zero_state (N : OrdVModule W M) (β : ℤ) (m : ℤ) (g : ℂ →₀ M) :
    Dfam N β 0 m g = 0 := by
  induction g using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add g g' ih ih' => rw [map_add, ih, ih', add_zero]
  | single δ y =>
    rw [Dfam_single, Dpiece]
    refine Finset.sum_eq_zero fun j _ => finsum_eq_zero_of_forall_eq_zero fun r => ?_
    simp only [Dterm, map_zero, mode_zero, LinearMap.zero_apply, smul_zero, Finsupp.single_zero]

theorem What_smul_g (N : OrdVModule W M) (α₀ : ℂ) (c : ℤ) (φ : 𝒱) (a : ℂ) (g : ℂ →₀ M) :
    What N α₀ c φ (a • g) = a • What N α₀ c φ g := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g g' ih ih' => rw [smul_add, map_add, map_add, ih, ih', smul_add]
  | single δ y => rw [Finsupp.smul_single, What_single, What_single, wMode_smul_right]

/-- **Transport identity** for families on one coset. -/
theorem what_tw (N : OrdVModule W M) {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (m : ℤ)
    (α₀ : ℂ) (c : ℤ) (φ : 𝒱) {g : ℂ →₀ M} (hg : g ∈ (coset α₀ : Submodule ℂ (ℂ →₀ M))) :
    tw N β u m (What N α₀ c φ g)
      = What N α₀ (c + β - m - 1) φ (Dfam N β u m g)
        + What N α₀ c (tw (adjointModule W) β u m φ) g := by
  induction g using Finsupp.induction with
  | zero => simp only [map_zero, add_zero]; simpa using tw_smul N β u m 0 0
  | single_add a b f ha hb ih =>
    have hsupp : (Finsupp.single a b + f).support = insert a f.support := by
      rw [Finsupp.support_add_eq (by
        rw [Finsupp.support_single _ hb]; exact Finset.disjoint_singleton_left.2 ha),
        Finsupp.support_single _ hb]; rfl
    have hsub : ((Finsupp.single a b + f).support : Set ℂ) ⊆ {δ | ∃ k : ℤ, δ = α₀ + k} :=
      (Finsupp.mem_supported ℂ _).1 hg
    rw [hsupp, Finset.coe_insert, Set.insert_subset_iff] at hsub
    obtain ⟨k, rfl⟩ := hsub.1
    have h1 := what_tw_single N hu m α₀ c k b φ
    rw [map_add, map_add, map_add, tw_add, ih ((Finsupp.mem_supported ℂ _).2 hsub.2), map_add]
    rw [sub_eq_iff_eq_add] at h1
    rw [h1]
    abel

/-! ## Injectivity of the skew intertwiner on the vacuum -/

theorem offs_spec {α₀ δ : ℂ} (h : ∃ k : ℤ, δ = α₀ + k) : δ = α₀ + offs α₀ δ := by
  obtain ⟨k, rfl⟩ := h
  rw [offs_add]

theorem wMode_vacuum_neg_one (A : WeakModule W M) (t : M) : wMode A t (-1) W.vacuum = t := by
  rw [wMode_vacuum, if_pos le_rfl]
  simp

theorem wMode_vacuum_nonneg (A : WeakModule W M) (t : M) {n : ℤ} (hn : 0 ≤ n) :
    wMode A t n W.vacuum = 0 := by
  rw [wMode_vacuum, if_neg (by omega)]

/-- **Injectivity**: a family on one coset killed by every `Ŵ_c(·)𝟙` is zero. -/
theorem eq_zero_of_what_vacuum (N : OrdVModule W M) (α₀ : ℂ) {e : ℂ →₀ M}
    (he : e ∈ (coset α₀ : Submodule ℂ (ℂ →₀ M)))
    (h : ∀ c : ℤ, What N α₀ c W.vacuum e = 0) : e = 0 := by
  classical
  by_contra hne
  have hsub : (e.support : Set ℂ) ⊆ {δ | ∃ k : ℤ, δ = α₀ + k} := (Finsupp.mem_supported ℂ _).1 he
  have hS : (e.support.image (offs α₀)).Nonempty :=
    Finset.Nonempty.image (Finsupp.support_nonempty_iff.2 hne) _
  set s₀ := (e.support.image (offs α₀)).min' hS with hs₀
  obtain ⟨δ₀, hδ₀, hδ₀s⟩ := Finset.mem_image.1 (Finset.min'_mem _ hS)
  have key := h (-1 - s₀)
  have hsum : What N α₀ (-1 - s₀) W.vacuum e
      = e.sum fun δ y => wMode N.toWeakModule y (-1 - s₀ + offs α₀ δ) W.vacuum := by
    rw [What, Finsupp.liftAddHom_apply]; rfl
  rw [hsum, Finsupp.sum, Finset.sum_eq_single δ₀] at key
  · rw [hδ₀s, show -1 - s₀ + s₀ = -1 by ring, wMode_vacuum_neg_one] at key
    exact (Finsupp.mem_support_iff.1 hδ₀) key
  · intro δ hδ hne'
    have hle : s₀ ≤ offs α₀ δ := Finset.min'_le _ _ (Finset.mem_image_of_mem _ hδ)
    have hneq : offs α₀ δ ≠ s₀ := by
      intro heq
      apply hne'
      rw [offs_spec (hsub hδ), offs_spec (hsub hδ₀), heq, hδ₀s]
    exact wMode_vacuum_nonneg _ _ (by omega)
  · intro h'; exact absurd hδ₀ h'

theorem What_sub_phi (N : OrdVModule W M) (α₀ : ℂ) (c : ℤ) (φ ψ : 𝒱) (g : ℂ →₀ M) :
    What N α₀ c (φ - ψ) g = What N α₀ c φ g - What N α₀ c ψ g := by
  rw [sub_eq_add_neg, What_add_phi, ← neg_one_smul ℂ ψ, What_smul_phi, neg_one_smul,
    ← sub_eq_add_neg]

/-! ## The commutator formula for the translated contragredient modes -/

theorem Lm1_pow_mem (N : OrdVModule W M) {δ : ℂ} {z : M} (hz : z ∈ N.weight δ) (i : ℕ) :
    (SkewIntertwiner.Lm1 N.toWeakModule ^ i) z ∈ N.weight (δ + i) := by
  induction i with
  | zero => simpa using hz
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := VOA.mode_mem_weight N W.conformalVector_mem_grading_two ih 0
    rw [show δ + (i : ℂ) + ((2 : ℤ) : ℂ) - ((0 : ℤ) : ℂ) - 1 = δ + ((i + 1 : ℕ) : ℂ) by
      push_cast; ring] at this
    exact this

/-- The weight of a skew mode. -/
theorem wMode_mem (N : OrdVModule W M) {α : ℂ} {t : M} (ht : t ∈ N.weight α) {γ : ℤ}
    {φ : 𝒱} (hφ : φ ∈ W.grading γ) (n : ℤ) :
    wMode N.toWeakModule t n φ ∈ N.weight (α + γ - n - 1) := by
  obtain ⟨K, hK⟩ := exists_bound N.toWeakModule t n φ
  rw [wMode_eq_sum _ K hK]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h1 := VOA.mode_mem_weight N hφ ht (n + i)
  have h2 := Lm1_pow_mem N h1 i
  convert h2 using 2
  push_cast; ring

/-- The support of the product family `i ↦ cbz m i • F(u_i v)` lies in `[0, N]`. -/
theorem exists_smul_bound (u v : 𝒱) :
    ∃ Ns : ℤ, ∀ i : ℤ, Ns ≤ i → W.smul u i v = 0 :=
  W.toPreVertexAlgebra.smul_eventually_zero u v

theorem finsum_cbz_eq {X : Type u} [AddCommGroup X] [Module ℂ X] {u v : 𝒱} (m : ℤ) {Ns : ℤ}
    (hNs' : ∀ i : ℤ, Ns ≤ i → W.smul u i v = 0) (F : ℤ → 𝒱 → X) (hF : ∀ i, F i 0 = 0) :
    (∑ᶠ i : ℤ, cbz m i • F i (W.smul u i v))
      = ∑ i ∈ Finset.Icc (0 : ℤ) Ns, cbz m i • F i (W.smul u i v) := by
  refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
  rw [Function.mem_support] at hi
  rw [Finset.coe_Icc, Set.mem_Icc]
  by_contra h
  rcases not_and_or.1 h with h | h
  · exact hi (by rw [cbz_apply_neg m (by omega), zero_smul])
  · exact hi (by rw [hNs' i (by omega), hF, smul_zero])

/-- **The commutator formula for the translated contragredient modes** (on a homogeneous
vector, as an identity of weight-indexed families):
`D(v,n) D(u,m) y − D(u,m) D(v,n) y = Σᵢ C(m,i) D(u_i v, m+n−i) y`. -/
theorem Dcomm_single (N : OrdVModule W M) {β γ : ℤ} {u v : 𝒱} (hu : u ∈ W.grading β)
    (hv : v ∈ W.grading γ) (m n : ℤ) {α₀ : ℂ} {y : M} (hy : y ∈ N.weight α₀) :
    Dfam N γ v n (Dfam N β u m (Finsupp.single α₀ y))
      - Dfam N β u m (Dfam N γ v n (Finsupp.single α₀ y))
      = ∑ i ∈ Finset.Icc (0 : ℤ) (max 0 (exists_smul_bound (W := W) u v).choose),
          cbz m i • Dfam N (β + γ - i - 1) (W.smul u i v) (m + n - i)
            (Finsupp.single α₀ y) := by
  set Ns := max 0 (exists_smul_bound (W := W) u v).choose with hNs
  have hNs' : ∀ i : ℤ, Ns ≤ i → W.smul u i v = 0 := fun i hi =>
    (exists_smul_bound (W := W) u v).choose_spec i (le_trans (le_max_right _ _) hi)
  set S := Finset.Icc (0 : ℤ) Ns with hS
  set g₀ : ℂ →₀ M := Finsupp.single α₀ y with hg₀
  have hg₀c : g₀ ∈ (coset α₀ : Submodule ℂ (ℂ →₀ M)) := single_mem_coset' α₀ y
  have hDu := Dfam_mem_coset N β u m α₀ hg₀c
  have hDv := Dfam_mem_coset N γ v n α₀ hg₀c
  have hui : ∀ i : ℤ, W.smul u i v ∈ W.grading (β + γ - i - 1) := fun i =>
    W.smul_mem_grading hu hv i
  set E := Dfam N γ v n (Dfam N β u m g₀) - Dfam N β u m (Dfam N γ v n g₀)
    - ∑ i ∈ S, cbz m i • Dfam N (β + γ - i - 1) (W.smul u i v) (m + n - i) g₀ with hE
  suffices hE0 : E = 0 by rw [hE, sub_eq_zero] at hE0; exact hE0
  have hEc : E ∈ (coset α₀ : Submodule ℂ (ℂ →₀ M)) :=
    Submodule.sub_mem _ (Submodule.sub_mem _ (Dfam_mem_coset N γ v n α₀ hDu)
      (Dfam_mem_coset N β u m α₀ hDv))
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Dfam_mem_coset N _ _ _ α₀ hg₀c))
  refine eq_zero_of_what_vacuum N α₀ hEc fun c' => ?_
  set c := c' - (β + γ - m - n - 2) with hc
  set one := W.vacuum
  -- the homogeneous vector `x = Ŵ_c(y) 𝟙`
  have hx : What N α₀ c one g₀ ∈ N.weight (α₀ + ((0 : ℤ) : ℂ) - c - 1) := by
    rw [hg₀, What_single, show offs α₀ α₀ = 0 by simpa using offs_add α₀ 0, add_zero]
    exact wMode_mem N hy W.vacuum_mem_grading_zero c
  have hcomm := tw_comm N hu hv m n hx
  -- the vacuum identity on `V`
  have h1 : one ∈ (adjointModule W).weight ((0 : ℤ) : ℂ) := by
    change W.vacuum ∈ adjWeight W ((0 : ℤ) : ℂ)
    rw [adjWeight_cast]; exact W.vacuum_mem_grading_zero
  have hcommV := tw_comm (adjointModule W) hu hv m n h1
  -- convert the finsums over `i` to sums over `S`
  have hsuppN := fun {X : Type u} [AddCommGroup X] [Module ℂ X] (F : ℤ → 𝒱 → X)
      (hF : ∀ i, F i 0 = 0) => finsum_cbz_eq (W := W) m hNs' F hF
  rw [hsuppN (fun i w => tw N (β + γ - i - 1) w (m + n - i) (What N α₀ c one g₀))
    (fun i => tw_zero_state N _ _ _)] at hcomm
  rw [hsuppN (fun i w => tw (adjointModule W) (β + γ - i - 1) w (m + n - i) one)
    (fun i => tw_zero_state _ _ _ _)] at hcommV
  -- expand everything through the transport identity
  set X := What N α₀ c one g₀ with hX
  have eu := what_tw N hu m α₀ c one hg₀c
  have ev := what_tw N hv n α₀ c one hg₀c
  have evu1 := what_tw N hv n α₀ (c + β - m - 1) one hDu
  have evu2 := what_tw N hv n α₀ c (tw (adjointModule W) β u m one) hg₀c
  have euv1 := what_tw N hu m α₀ (c + γ - n - 1) one hDv
  have euv2 := what_tw N hu m α₀ c (tw (adjointModule W) γ v n one) hg₀c
  have ei : ∀ i : ℤ, tw N (β + γ - i - 1) (W.smul u i v) (m + n - i) X
      = What N α₀ c' one (Dfam N (β + γ - i - 1) (W.smul u i v) (m + n - i) g₀)
        + What N α₀ c (tw (adjointModule W) (β + γ - i - 1) (W.smul u i v) (m + n - i) one) g₀ := by
    intro i
    rw [what_tw N (hui i) (m + n - i) α₀ c one hg₀c]
    congr 2
    rw [hc]; ring
  have c1 : c + β - m - 1 + γ - n - 1 = c' := by rw [hc]; ring
  have c2 : c + γ - n - 1 + β - m - 1 = c' := by rw [hc]; ring
  rw [c1] at evu1
  rw [c2] at euv1
  rw [eu, tw_add, evu1, evu2] at hcomm
  rw [ev, tw_add, euv1, euv2] at hcomm
  simp only [ei, smul_add, Finset.sum_add_distrib] at hcomm
  -- the vacuum identity transported by `Ŵ_c(g₀)`
  have hV' := congrArg (fun φ => What N α₀ c φ g₀) hcommV
  simp only [What_sub_phi, What_sum_phi, What_smul_phi] at hV'
  -- conclude
  have key : What N α₀ c' one (Dfam N γ v n (Dfam N β u m g₀))
      - What N α₀ c' one (Dfam N β u m (Dfam N γ v n g₀))
      = ∑ i ∈ S, cbz m i • What N α₀ c' one
          (Dfam N (β + γ - i - 1) (W.smul u i v) (m + n - i) g₀) := by
    have h3 := congrArg₂ (· - ·) hcomm hV'
    simp only at h3
    rw [← sub_eq_zero] at h3 ⊢
    rw [← h3]
    abel
  rw [hE, map_sub, map_sub, key, map_sum, sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ => (What_smul_g N α₀ c' one _ _).symm

end VOA.Huang.PzTensorTT
