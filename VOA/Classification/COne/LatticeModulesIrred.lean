/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.LatticeModules

/-!
# Irreducibility and isomorphism classes of the modules `V_{L+λ}`

For `L = √(2m)ℤ` and the modules `latticeModule m hm j` (`= V_{L+jα/(2m)}`, `LatticeModules.lean`):

* `latticeModule_isIrreducible` — `V_{L+λ_j}` is irreducible, for every `j ∈ ℤ`.
  A nonzero submodule `P` contains a nonzero bigraded `q ⊗ e^{nα}` (eigen-separation by the
  commuting operators `α(0)` and `L₀`, `submod_exists_state`); the annihilators `α(k)`, `k > 0`
  (`∝ ∂/∂x_k`) lower it to `𝟙 ⊗ e^{nα}` (`submod_vac_of_state`); the charge vectors then move
  `P` through every charge sector and the leading-term/Schur interpolation of
  `LatticeSimple.lat_mem_of_weight`, rerun for the module action (`gen_eq_top`), gives `P = ⊤`.
* `latticeModuleShiftEquiv : ModuleEquiv (V2m m hm) (latticeModule j) (latticeModule (j+2m))`,
  `p ⊗ e^{nα} ↦ c(n) p ⊗ e^{(n-1)α}`.
* `latticeModuleZeroEquiv : ModuleEquiv (V2m m hm) (latticeModule 0) (adjointModule (V2m m hm))`.
* `latticeModule_not_iso` — `IsEmpty (ModuleEquiv … j … j')` for `0 ≤ j ≠ j' < 2m`, and the
  full criterion `latticeModule_iso_iff : (V_{L+λ_j} ≅ V_{L+λ_{j'}}) ↔ 2m ∣ j - j'`.

## Method for the isomorphisms
`moduleEquivOfCharge`: a linear equivalence intertwining the vertex operators of the charge
vectors `e^β` intertwines everything (the intertwined states form a subspace closed under all
`n`-th products by the module Jacobi identity with `m = 0`, hence all of `V_L` by
`latVOA_generated`).  On `e^β` the module cocycle of `V_{L+λ_j}` is
`ε_L(β,n) σ_j(β) c_j(β+n)/c_j(n)` (`kappa_eq`), with `c_j = latCob` and the character
`σ_j(β) = ε_{N_j}(βα, δ)`; the rescalings `shiftC`, `adjC` absorb the coboundary and the
characters.  No explicit value of any cocycle is needed.

## Method for non-isomorphism
An isomorphism intertwines `α(0)` (the zero mode of `α(-1)𝟙`, `hVec`).  On `V_{L+λ_j}` it acts on
`p ⊗ e^{nα}` by `χ_j(n) = (2mn + j)/√(2m)` (`chi`, `chi_mul`), and its spectrum is exactly
`{χ_j(n)}` (`latticeModule_zeroMode_eigen`, via the charge coordinates `coordEα`).  The image of
`e^{λ_j}` has eigenvalue `j/√(2m)`, so `j ≡ j' (mod 2m)`.  (The lowest weight is not needed.)

## Not done here
Completeness — every irreducible `V_{2m}`-module is some `V_{L+λ_j}` — is rationality (C3).

## Status
No `sorry`, no new axioms.  Unconditional: the only hypothesis is `1 ≤ m`.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne.LatMod

open VOA VOA.IntegralLattice VOA.LatGen HeisenbergN VOA.Moonshine
open Module (End)
open scoped TensorProduct BigOperators

/-! ## §1  Generic linear algebra -/

section Lagrange

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- **Eigen-separation**: if `T` preserves `P` and `∑_{c∈s} u c ∈ P` with `T (u c) = c • u c`
(distinct eigenvalues `c`), then every `u c ∈ P`. -/
theorem mem_of_sum_eigen (T : M →ₗ[ℂ] M) (P : Submodule ℂ M) (hT : ∀ x ∈ P, T x ∈ P) :
    ∀ (s : Finset ℂ) (u : ℂ → M), (∀ c ∈ s, T (u c) = c • u c) → (∑ c ∈ s, u c) ∈ P →
      ∀ c ∈ s, u c ∈ P := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro u _ _ c hc; simp at hc
  | insert k s hk ih =>
    intro u hu hsum
    rw [Finset.sum_insert hk] at hsum
    have hTs : T (u k + ∑ c ∈ s, u c) - k • (u k + ∑ c ∈ s, u c)
        = ∑ c ∈ s, (c - k) • u c := by
      rw [map_add, map_sum, hu k (Finset.mem_insert_self _ _), smul_add, Finset.smul_sum]
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [hu c (Finset.mem_insert_of_mem hc), sub_smul]
    have hmem : ∑ c ∈ s, (c - k) • u c ∈ P := by
      rw [← hTs]; exact Submodule.sub_mem _ (hT _ hsum) (Submodule.smul_mem _ _ hsum)
    have hih := ih (fun c => (c - k) • u c) (fun c hc => by
      simp only [map_smul, hu c (Finset.mem_insert_of_mem hc), smul_comm (c - k) c]) hmem
    have hs : ∀ c ∈ s, u c ∈ P := by
      intro c hc
      have hck : c - k ≠ 0 := sub_ne_zero.mpr (fun h => hk (h ▸ hc))
      have := Submodule.smul_mem _ (c - k)⁻¹ (hih c hc)
      simp only at this
      rwa [smul_smul, inv_mul_cancel₀ hck, one_smul] at this
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · have : u c = (u c + ∑ c ∈ s, u c) - ∑ c ∈ s, u c := by abel
      rw [this]
      exact Submodule.sub_mem _ hsum (Submodule.sum_mem _ hs)
    · exact hs c hc

/-- **Grouped eigen-separation**: the part of a sum in `P` with a given eigenvalue is in `P`. -/
theorem sum_filter_eigen_mem (T : M →ₗ[ℂ] M) (P : Submodule ℂ M) (hT : ∀ x ∈ P, T x ∈ P)
    {ι : Type*} (s : Finset ι) (v : ι → M) (μ : ι → ℂ)
    (hv : ∀ i ∈ s, T (v i) = μ i • v i) (hs : (∑ i ∈ s, v i) ∈ P) (c : ℂ) (t : Finset ι)
    (ht : ∀ i, i ∈ t ↔ i ∈ s ∧ μ i = c) : (∑ i ∈ t, v i) ∈ P := by
  classical
  have htf : t = s.filter (fun i => μ i = c) := by ext i; rw [ht, Finset.mem_filter]
  subst htf
  set u : ℂ → M := fun c => ∑ i ∈ s.filter (fun i => μ i = c), v i
  have hu : ∀ c ∈ s.image μ, T (u c) = c • u c := by
    intro c _
    simp only [u, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [hv i hi.1, hi.2]
  have hsum : (∑ c ∈ s.image μ, u c) = ∑ i ∈ s, v i :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem μ hi) v
  by_cases hc : c ∈ s.image μ
  · exact mem_of_sum_eigen T P hT (s.image μ) u hu (hsum ▸ hs) c hc
  · have : s.filter (fun i => μ i = c) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i hi hic
      exact hc (hic ▸ Finset.mem_image_of_mem μ hi)
    change u c ∈ P
    simp only [u, this, Finset.sum_empty]
    exact Submodule.zero_mem _

end Lagrange

/-! ## §2  Generation of `V_K`-shaped spaces from the charged vacua -/

section Gen

variable (L : IntegralLattice.{0}) (hPos : L.PosDef) (S : Submodule ℂ (LatModuleGen L))
  (hE : ∀ (a c : L.carrier) (q : FockN (rank L)) (d : ℕ),
    latStateGen L q c ∈ S → latStateGen L (EEVec L a (d : ℤ) q) (a + c) ∈ S)
  (hX : ∀ β : L.carrier, latChargeGen L β ∈ S)

include hE in
/-- Leading term (module version of `lat_mem_vSchur_mul`). -/
theorem gen_mem_vSchur_mul (w : ℕ)
    (IH : ∀ w' < w, ∀ (c : L.carrier) (q : FockN (rank L)),
      q ∈ gradingWN (rank L) w' → latStateGen L q c ∈ S) :
    ∀ k : ℕ, ∀ d : ℕ, d + k = w → 1 ≤ d → ∀ γ a : L.carrier,
      ∀ q ∈ gradingWN (rank L) k, latStateGen L (vSchur L a d * q) γ ∈ S := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro d hdk hd γ a q hq
  set c := γ - a with hc
  have h1 := hE a c q d (IH k (by omega) c q hq)
  rw [show a + c = γ by rw [hc]; abel, EEVec_expand L a hq d, latStateGen_finsum,
    Finset.sum_range_succ', aExpVec_zero, LinearMap.id_apply, add_zero] at h1
  have hrest : ∑ r ∈ Finset.range k,
      latStateGen L (vSchur L a (d + (r + 1)) * aExpVec L a (r + 1) q) γ ∈ S := by
    refine Submodule.sum_mem _ fun r hr => ?_
    simp only [Finset.mem_range] at hr
    have hq' : aExpVec L a (r + 1) q ∈ gradingWN (rank L) (k - (r + 1)) := by
      have := aExpVec_mem_gradingZN L a (r + 1) hq
      rwa [gradingZN_of_nonneg (by omega), show ((k : ℤ) - ((r + 1 : ℕ) : ℤ)).toNat = k - (r + 1)
        by omega] at this
    exact ihk (k - (r + 1)) (by omega) (d + (r + 1)) (by omega) (by omega) γ a _ hq'
  have h2 := Submodule.sub_mem _ h1 hrest
  rwa [add_sub_cancel_left] at h2

include hPos hE hX in
/-- Every Fock weight in every charge sector is in `S` (module version of `lat_mem_of_weight`). -/
theorem gen_mem_of_weight :
    ∀ w : ℕ, ∀ (c : L.carrier) (q : FockN (rank L)),
      q ∈ gradingWN (rank L) w → latStateGen L q c ∈ S := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w IH =>
  intro c q hq
  have hB := gen_mem_vSchur_mul L S hE w IH
  have hlin : ∀ p : FockN (rank L), p ∈ Submodule.span ℂ
      {p | ∃ l : List (ℕ × Fin (rank L)), wordWt l = w ∧ p = wordStateN l} →
      latStateGen L p c ∈ S := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      cases l with
      | nil => exact hX c
      | cons ia rest =>
        obtain ⟨m, b⟩ := ia
        rw [wordWt_cons] at hl
        have hrest := wordStateN_mem_gradingWN rest
        rw [wordStateN_cons]
        set φ : FockN (rank L) →ₗ[ℂ] LatModuleGen L :=
          ((TensorProduct.mk ℂ (FockN (rank L)) (L.carrier →₀ ℂ)).flip (eGen L c)).comp
            (LinearMap.mulRight ℂ (wordStateN rest)) with hφ
        have hφapp : ∀ p, φ p = latStateGen L (p * wordStateN rest) c := fun p => rfl
        have hspan := X_mem_span_vVar L hPos m b
        suffices hsub : Submodule.span ℂ (Set.range fun i : Fin (latRank L) =>
            vVar L (latticeBasis L i) m) ≤ S.comap φ by
          have := hsub hspan
          rwa [Submodule.mem_comap, hφapp] at this
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, hφapp]
        set a₀ := latticeBasis L i
        set D := (schurPoly L a₀ (m + 1)).natDegree
        have hpoly := mem_of_forall_sum_pow_smul_mem (S.comap φ)
          (fun j => (schurPoly L a₀ (m + 1)).coeff j) D 0 (fun k _ => by
            rw [Submodule.mem_comap, ← vSchur_nsmul_eq_sum, hφapp]
            exact hB (wordWt rest) (m + 1) (by omega) (by omega) c (k • a₀) _ hrest)
        by_cases h1 : 1 ∈ Finset.range (D + 1)
        · have := hpoly 1 h1
          simp only [schurPoly_coeff_one] at this
          rw [Submodule.mem_comap, map_smul] at this
          have h2 := Submodule.smul_mem _ ((m : ℂ) + 1) this
          rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast Nat.succ_ne_zero m), one_smul,
            hφapp] at h2
          exact h2
        · have hD : D < 1 := by simpa using h1
          have hc1 := Polynomial.coeff_eq_zero_of_natDegree_lt (p := schurPoly L a₀ (m + 1))
            (n := 1) (by omega)
          rw [schurPoly_coeff_one] at hc1
          rcases smul_eq_zero.mp hc1 with h | h
          · exact absurd h (inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero m))
          · dsimp only
            rw [h, zero_mul, latStateGen, TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | zero => rw [latStateGen, TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [latStateGen_add_boson]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [latStateGen_csmul]; exact Submodule.smul_mem _ _ hx
  exact hlin q (gradingWN_le_span_words _ w hq)

include hPos hE hX in
/-- **Generation from the charged vacua**: a subspace containing every `𝟙 ⊗ e^β` and closed
under the charge-raising maps `q ⊗ e^c ↦ EE_d(a) q ⊗ e^{a+c}` is everything. -/
theorem gen_eq_top : S = ⊤ := by
  rw [eq_top_iff, ← wordStateLatGen_span L, Submodule.span_le]
  rintro _ ⟨⟨l, α⟩, rfl⟩
  rw [SetLike.mem_coe, Function.uncurry_apply_pair, wordStateLatGen_eq]
  exact gen_mem_of_weight L hPos S hE hX (wordWt l) α (wordStateN l) (wordStateN_mem_gradingWN l)

end Gen

/-! ## §3  Module maps intertwining the charge vectors intertwine everything -/

section IsoGen

variable {𝒱 : Type} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

theorem jacobi_zero (A : WeakModule W M) (u v : 𝒱) (x : M) (n t : ℤ) :
    mode (A.YM (W.smul u n v)) t x
      = ∑ᶠ i : ℤ, (negOnePow i * cbz n i) •
          (mode (A.YM u) (n + 0 - i) (mode (A.YM v) (t + i) x)
            - negOnePow n • mode (A.YM v) (n + t - i) (mode (A.YM u) (0 + i) x)) := by
  rw [A.jacobi u v x n 0 t, finsum_eq_single _ (0 : ℤ)
    (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul]), cbz_zero_left, if_pos rfl,
    one_smul, add_zero, zero_add, sub_zero]

/-- The subspace of states whose modes are intertwined by `e`. -/
def intertwSub (A : WeakModule W M) (B : WeakModule W N) (e : M →ₗ[ℂ] N) : Submodule ℂ 𝒱 where
  carrier := {u | ∀ (n : ℤ) (x : M), e (mode (A.YM u) n x) = mode (B.YM u) n (e x)}
  add_mem' {u v} hu hv n x := by
    simp only [map_add, mode_add, LinearMap.add_apply]
    rw [hu, hv]
  zero_mem' n x := by simp
  smul_mem' c u hu n x := by
    simp only [map_smul, mode_smul, LinearMap.smul_apply]
    rw [hu]

theorem intertwSub_smul (A : WeakModule W M) (B : WeakModule W N) (e : M →ₗ[ℂ] N)
    (he : Function.Injective e) {u v : 𝒱} (hu : u ∈ intertwSub A B e)
    (hv : v ∈ intertwSub A B e) (n : ℤ) : W.smul u n v ∈ intertwSub A B e := by
  intro t x
  rw [jacobi_zero A u v x n t, jacobi_zero B u v (e x) n t, map_finsum_of_injective e he]
  refine finsum_congr fun i => ?_
  rw [map_smul, map_sub, map_smul, hu, hv, hv, hu]

end IsoGen

section IsoLat

variable (L : IntegralLattice.{0}) (hEven : L.Even) (hPos : L.PosDef)
  {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- A linear equivalence intertwining the vertex operators of every `e^β` is a module
isomorphism (generation of `V_L` by the `e^β`, `latVOA_generated`). -/
noncomputable def moduleEquivOfCharge (A : OrdVModule (latticeVOAGen L hEven hPos) M)
    (B : OrdVModule (latticeVOAGen L hEven hPos) N) (e : M ≃ₗ[ℂ] N)
    (hgen : ∀ (β : L.carrier) (t : ℤ) (x : M),
      e (A.YM (latChargeGen L β) t x) = B.YM (latChargeGen L β) t (e x)) :
    ModuleEquiv (latticeVOAGen L hEven hPos) A B where
  toLinearEquiv := e
  map_act u n x := by
    have htop : intertwSub A.toWeakModule B.toWeakModule e.toLinearMap = ⊤ :=
      latVOA_generated L hEven hPos _
        (fun u hu v hv n => intertwSub_smul _ _ _ e.injective hu hv n)
        (fun β t x => by rw [mode_apply, mode_apply]; exact hgen β _ x)
    have hu : u ∈ intertwSub A.toWeakModule B.toWeakModule e.toLinearMap := by
      rw [htop]; trivial
    exact hu n x

end IsoLat

/-! ## §4  The Heisenberg current on the shifted module -/

section Current

variable (K N : IntegralLattice.{0}) (ι : K.carrier →ₗ[ℤ] N.carrier) (δ : N.carrier)
  (hKe : K.Even) (hK : K.PosDef) (hNe : N.Even) (hN : N.PosDef)
  (hι : ∀ α β, N.form (ι α) (ι β) = K.form α β)

/-- The Heisenberg state `α_a(-1)𝟙 ∈ V_K`. -/
noncomputable def hVec (a : Fin (rank K)) : LatModuleGen K :=
  LinearMap.rTensor (K.carrier →₀ ℂ) (currentN (rank K) 1 a ((0 : ℕ) : ℤ)) (latVacuumGen K)

/-- On the shifted module, `Y_M(α_a(-1)𝟙, z)` is the shifted current `α_a(z) + λ_a z⁻¹`. -/
theorem shiftWeakModule_hVec (a : Fin (rank K)) (t : ℤ) (x : LatModuleGen K) :
    (shiftWeakModule K N ι δ hKe hK hNe hN hι).YM (hVec K a) t x = alphaShift K N ι δ a t x := by
  apply shiftEmb_injective K N ι δ hK hN hι
  rw [shiftWeakModule_intertw]
  have hin := IntertwH.nprod (alphaShift_isField K N ι δ a) idField_isField
    (isField_sum_genField K N ι a 0) (YfullGen_isField N hNe hN _)
    (shiftEmb_alphaShift K N ι δ hK hN hι a) (shiftEmb_vacuumField K N ι δ hKe hK hNe hN hι)
  rw [mul_one, nprod_idField_right] at hin
  have h := hin t x
  rw [one_smul] at h
  rw [h, show (latticeVOAGen N hNe hN).Y = YfullGen N hNe hN from rfl, hVec,
    YN_latMorph_current K N ι hK hNe hN hι a (latVacuumGen K)]

/-- The modes of `α_a(-1)𝟙` on `p ⊗ e^γ`: `α_a(n)` for `n ≠ 0`, and `γ_a + λ_a` for `n = 0`. -/
theorem shiftWeakModule_hVec_mode (a : Fin (rank K)) (n : ℤ) (p : FockN (rank K))
    (γ : K.carrier) :
    mode ((shiftWeakModule K N ι δ hKe hK hNe hN hι).YM (hVec K a)) n (latStateGen K p γ)
      = latStateGen K (oscN (rank K) 1 a n p
          + (if n = 0 then (chargeCoord K γ a + lamShift K N ι δ a) • p else 0)) γ := by
  rw [mode_apply, shiftWeakModule_hVec, alphaShift_latStateGen, show -(-n - 1) - 1 = n by ring]
  by_cases hn : n = 0
  · rw [if_pos (by omega), if_pos hn]
  · rw [if_neg (by omega), if_neg hn]

end Current

/-! ## §5  Fock-space lowering -/

section Lowering

open MvPolynomial

theorem coeff_pderivN {r : ℕ} (s : (ℕ × Fin r) →₀ ℕ) (x : ℕ × Fin r) (p : FockN r) :
    coeff s (pderiv x p) = ((s x : ℂ) + 1) * coeff (s + Finsupp.single x 1) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial t a =>
      rw [pderiv_monomial, coeff_monomial, coeff_monomial]
      by_cases ht : t = s + Finsupp.single x 1
      · subst ht
        rw [if_pos (by ext y; simp), if_pos rfl]
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast; ring
      · rw [if_neg ht, mul_zero]
        split_ifs with h
        · have htx : t x = 0 := by
            by_contra hne
            apply ht
            ext y
            have := congrArg (fun f => f y) h
            simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.add_apply] at this ⊢
            by_cases hy : y = x
            · subst hy; simp only [Finsupp.single_eq_same] at this ⊢; omega
            · rw [Finsupp.single_eq_of_ne' (Ne.symm hy)] at this ⊢; omega
          rw [htx, Nat.cast_zero, mul_zero]
        · rfl
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, coeff_add, mul_add]

/-- A nonzero Fock vector of positive weight has a nonzero partial derivative. -/
theorem exists_pderiv_ne_zero {r w : ℕ} {q : FockN r} (hq : q ∈ gradingWN r w) (hw : w ≠ 0)
    (hq0 : q ≠ 0) : ∃ x : ℕ × Fin r, pderiv x q ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hq0
  have hsw : Finsupp.weight weightFnN s = w := (mem_gradingWN.mp hq) hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsw
    exact hw hsw.symm
  obtain ⟨x, hx⟩ : ∃ x, s x ≠ 0 := by
    by_contra h
    push Not at h
    exact hs0 (Finsupp.ext h)
  refine ⟨x, fun h0 => ?_⟩
  have hle : Finsupp.single x 1 ≤ s := by
    rw [Finsupp.single_le_iff]; omega
  set t : (ℕ × Fin r) →₀ ℕ := s - Finsupp.single x 1 with ht
  have hc := coeff_pderivN t x q
  rw [h0, coeff_zero, ht, tsub_add_cancel_of_le hle] at hc
  have hne : ((t x : ℕ) : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  rcases mul_eq_zero.mp hc.symm with h | h
  · exact hne h
  · exact hs h

end Lowering

/-! ## §6  The rank-one modules `V_{L+λ_j}`: irreducibility -/

section RankOne

open VOA.LatGen.Triplet

variable (m : ℕ) (hm : 1 ≤ m) (j : ℤ)

/-- The `α(0)`-eigenvalue `χ_j(n) = (2mn + j)/√(2m)` on `p ⊗ e^{nα}` in `V_{L+λ_j}`. -/
noncomputable def chi (n : ℤ) : ℂ :=
  chargeCoord (latP m) n (a0 m) + lamShift (latP m) (glueLat m j) (glueIota m j) (glueDelta m j) (a0 m)

include hm in
theorem chi_mul (n : ℤ) :
    chi m j n * chargeCoord (latP m) (1 : ℤ) (a0 m) = 2 * (m : ℂ) * n + j := by
  have hK := latP_posDef m hm
  have hN := glueLat_posDef m hm j
  have hcc := sum_chargeCoord (latP m) hK n (1 : ℤ)
  have hcl := sum_chargeCoord_lamShift (latP m) (glueLat m j) (glueIota m j) (glueDelta m j) hK hN
    (1 : ℤ)
  rw [sum_rankOne] at hcc hcl
  rw [latP_form] at hcc
  rw [glueIota_delta] at hcl
  rw [chi, add_mul, hcc, mul_comm _ (chargeCoord _ _ _), hcl]
  push_cast; ring

include hm in
theorem chargeCoord_one_ne_zero : chargeCoord (latP m) (1 : ℤ) (a0 m) ≠ 0 := by
  intro h
  have := chi_mul m hm 1 0
  rw [h, mul_zero] at this
  norm_num at this

include hm in
theorem chi_injective {n n' : ℤ} (h : chi m j n = chi m j n') : n = n' := by
  have h1 := chi_mul m hm j n
  rw [h, chi_mul m hm j n'] at h1
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : (n' : ℂ) = n := by
    have := h1
    have h2 : (2 * (m : ℂ)) * ((n' : ℂ) - n) = 0 := by linear_combination this
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (mul_ne_zero two_ne_zero hm0)
    · exact (sub_eq_zero.mp h3)
  exact_mod_cast this.symm

/-- The Heisenberg modes on `V_{L+λ_j}`. -/
theorem latticeModule_hVec_mode (n : ℤ) (p : FockN (rank (latP m))) (γ : ℤ) :
    mode ((latticeModule m hm j).YM (hVec (latP m) (a0 m))) n (latStateGen (latP m) p γ)
      = latStateGen (latP m) (oscN (rank (latP m)) 1 (a0 m) n p
          + (if n = 0 then chi m j γ • p else 0)) γ :=
  shiftWeakModule_hVec_mode (latP m) (glueLat m j) (glueIota m j) (glueDelta m j) (latP_even m)
    (latP_posDef m hm) (glueLat_even m j) (glueLat_posDef m hm j) (glueIota_isometry m j) (a0 m)
    n p γ

theorem latticeModule_zeroMode (p : FockN (rank (latP m))) (γ : ℤ) :
    mode ((latticeModule m hm j).YM (hVec (latP m) (a0 m))) 0 (latStateGen (latP m) p γ)
      = chi m j γ • latStateGen (latP m) p γ := by
  rw [latticeModule_hVec_mode, if_pos rfl, oscN_zero, LinearMap.zero_apply, zero_add,
    latStateGen_csmul]

theorem latticeCocycle_ne_zero (L : IntegralLattice) (α β : L.carrier) :
    latticeCocycle L α β ≠ 0 := by
  intro h
  have := latticeCocycle_sq L α β
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- The charge-raising closure of a submodule. -/
theorem submod_charge_step (P : WeakModule.Submodule' (latticeModule m hm j).toWeakModule)
    (a c : ℤ) (q : FockN (rank (latP m))) (d : ℕ)
    (hx : latStateGen (latP m) q c ∈ P.carrier) :
    latStateGen (latP m) (EEVec (latP m) a (d : ℤ) q) (a + c) ∈ P.carrier := by
  set t : ℤ := d + 2 * m * a * c + j * a
  have h := P.act_mem (latChargeGen (latP m) a) (-t - 1) hx
  rw [WeakModule.act_def, mode_apply, show -(-t - 1) - 1 = t by ring,
    latticeModule_latChargeGen, show t - 2 * m * a * c - j * a = (d : ℤ) by ring] at h
  have hκ : latCob (latP m) (glueLat m j) (glueIota m j) a
      * latticeCocycle (glueLat m j) (glueIota m j a) (glueIota m j c + glueDelta m j) ≠ 0 :=
    mul_ne_zero (latCob_ne_zero _ _ _ _) (latticeCocycle_ne_zero _ _ _)
  have h2 := P.carrier.smul_mem (latCob (latP m) (glueLat m j) (glueIota m j) a
      * latticeCocycle (glueLat m j) (glueIota m j a) (glueIota m j c + glueDelta m j))⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul] at h2

include hm in
/-- A submodule containing one charged vacuum `𝟙 ⊗ e^{γ₀}` is everything. -/
theorem submod_eq_top_of_vac (P : WeakModule.Submodule' (latticeModule m hm j).toWeakModule)
    (γ₀ : (latP m).carrier) (h0 : latChargeGen (latP m) γ₀ ∈ P.carrier) : P.carrier = ⊤ := by
  refine gen_eq_top (latP m) (latP_posDef m hm) P.carrier
    (fun a c q d hx => submod_charge_step m hm j P a c q d hx) (fun β => ?_)
  have h := submod_charge_step m hm j P (β - γ₀) γ₀ (vacuumN (rank (latP m))) 0 h0
  rw [Nat.cast_zero, EEVec_vacuum, if_pos le_rfl, Int.toNat_zero, vSchur_zero] at h
  convert h using 2
  exact (Int.sub_add_cancel β γ₀).symm

include hm in
/-- **Lowering**: a submodule containing a nonzero `q ⊗ e^γ` (`q` homogeneous) contains
`𝟙 ⊗ e^γ`. -/
theorem submod_vac_of_state (P : WeakModule.Submodule' (latticeModule m hm j).toWeakModule) :
    ∀ (w : ℕ) (q : FockN (rank (latP m))), q ∈ gradingWN (rank (latP m)) w → q ≠ 0 →
      ∀ γ : ℤ, latStateGen (latP m) q γ ∈ P.carrier → latChargeGen (latP m) γ ∈ P.carrier := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w IH =>
  intro q hq hq0 γ hx
  by_cases hw : w = 0
  · subst hw
    rw [gradingWN_zero_eq_span_one] at hq
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hq
    have hc : c ≠ 0 := by rintro rfl; exact hq0 (zero_smul _ _)
    rw [latStateGen_csmul] at hx
    have h2 := P.carrier.smul_mem c⁻¹ hx
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  · obtain ⟨⟨k, a⟩, hk⟩ := exists_pderiv_ne_zero hq hw hq0
    set n : ℤ := (k : ℤ) + 1
    have hn : 0 < n := by omega
    have ha : a = a0 m := by
      have h1 : a.val < 1 := lt_of_lt_of_eq a.isLt (rank_latP m)
      exact Fin.ext (by simp only [a0]; omega)
    subst ha
    have hact := P.act_mem (hVec (latP m) (a0 m)) n hx
    rw [WeakModule.act_def, latticeModule_hVec_mode, if_neg (by omega), add_zero,
      oscN_apply_pos _ _ _ hn, show (n - 1).toNat = k by omega, one_smul, latStateGen_csmul] at hact
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hx' := P.carrier.smul_mem (n : ℂ)⁻¹ hact
    rw [smul_smul, inv_mul_cancel₀ hn0, one_smul] at hx'
    have hgr := oscN_mem_gradingZN (rank (latP m)) 1 (a0 m) n hq
    rw [oscN_apply_pos _ _ _ hn, show (n - 1).toNat = k by omega, one_smul] at hgr
    have hgr' : MvPolynomial.pderiv (k, a0 m) q ∈ HeisenbergN.gradingZN (rank (latP m)) ((w : ℤ) - n) := by
      have := Submodule.smul_mem _ (n : ℂ)⁻¹ hgr
      rwa [smul_smul, inv_mul_cancel₀ hn0, one_smul] at this
    have hwn : 0 ≤ (w : ℤ) - n := by
      by_contra hneg
      rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hgr'
      exact hk hgr'
    rw [HeisenbergN.gradingZN_of_nonneg hwn] at hgr'
    exact IH _ (by omega) _ hgr' hk γ hx'

theorem mem_bigradα_exists {L : IntegralLattice} {k : ℤ × L.carrier} {v : LatModuleGen L}
    (hv : v ∈ bigradα L k) :
    ∃ q ∈ HeisenbergN.gradingZN (rank L) k.1, v = latStateGen L q k.2 := by
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hv
  exact ⟨q, hq, rfl⟩

/-- The `L₀`-eigenvalue of `Fock_w ⊗ e^{nα}`, as a function of the bigrade. -/
noncomputable def mu2 (k : ℤ × ℤ) : ℂ :=
  (((((k.1.toNat : ℕ) : ℝ) + ((2 * m * k.2 + j : ℤ) : ℝ) ^ 2 / (4 * m) : ℝ)) : ℂ)

include hm in
/-- **Separation**: a nonzero submodule contains a nonzero homogeneous `q ⊗ e^γ`. -/
theorem submod_exists_state (P : WeakModule.Submodule' (latticeModule m hm j).toWeakModule)
    {x : LatModuleGen (latP m)} (hx : x ∈ P.carrier) (hx0 : x ≠ 0) :
    ∃ (w : ℕ) (q : FockN (rank (latP m))) (γ : ℤ), q ∈ gradingWN (rank (latP m)) w ∧ q ≠ 0 ∧
      latStateGen (latP m) q γ ∈ P.carrier := by
  classical
  have hxs : x ∈ iSup (bigradα (latP m)) := by rw [bigradα_iSup_eq_top]; trivial
  obtain ⟨f, hf, hfx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp hxs
  rw [Finsupp.sum] at hfx
  have hsupp : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at hfx
    exact hx0 hfx.symm
  obtain ⟨k₀, hk₀⟩ := hsupp
  -- each component is `q ⊗ e^γ` with `q ≠ 0`, nonnegative weight
  have hcomp : ∀ k ∈ f.support, ∃ q ∈ gradingWN (rank (latP m)) k.1.toNat, q ≠ 0 ∧ 0 ≤ k.1 ∧
      f k = latStateGen (latP m) q k.2 := by
    intro k hk
    obtain ⟨q, hq, hfk⟩ := mem_bigradα_exists (hf k)
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [latStateGen, TensorProduct.zero_tmul] at hfk
      exact (Finsupp.mem_support_iff.mp hk) hfk
    have hk1 : 0 ≤ k.1 := by
      by_contra hneg
      rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hq
      exact hq0 hq
    rw [HeisenbergN.gradingZN_of_nonneg hk1] at hq
    exact ⟨q, hq, hq0, hk1, hfk⟩
  set Z := mode ((latticeModule m hm j).YM (hVec (latP m) (a0 m))) 0
  set L0 := mode ((latticeModule m hm j).YM (V2m m hm).conformalVector) 1
  have hZ : ∀ k ∈ f.support, Z (f k) = chi m j k.2 • f k := by
    intro k hk
    obtain ⟨q, _, _, _, hfk⟩ := hcomp k hk
    rw [hfk]; exact latticeModule_zeroMode m hm j q k.2
  have hL : ∀ k ∈ f.support, L0 (f k) = mu2 m j k • f k := by
    intro k hk
    obtain ⟨q, hq, _, _, hfk⟩ := hcomp k hk
    rw [hfk]; exact latticeModule_L0 m hm j hq k.2
  have key : ∀ k ∈ f.support, chi m j k.2 = chi m j k₀.2 → mu2 m j k = mu2 m j k₀ → k = k₀ := by
    intro k hk hc hμ
    have h2 : k.2 = k₀.2 := chi_injective m hm j hc
    obtain ⟨_, _, _, hk1, _⟩ := hcomp k hk
    obtain ⟨_, _, _, hk01, _⟩ := hcomp k₀ hk₀
    rw [mu2, mu2, h2, Complex.ofReal_inj, add_left_inj, Nat.cast_inj] at hμ
    exact Prod.ext (by omega) h2
  set t1 := f.support.filter (fun k => chi m j k.2 = chi m j k₀.2) with ht1
  have hy := sum_filter_eigen_mem Z P.carrier (fun x hx => P.act_mem _ 0 hx) f.support f
    (fun k => chi m j k.2) hZ (hfx ▸ hx) (chi m j k₀.2) t1 (fun i => Finset.mem_filter)
  have hz := sum_filter_eigen_mem L0 P.carrier (fun x hx => P.act_mem _ 1 hx) t1 f
    (mu2 m j) (fun k hk => hL k (Finset.mem_filter.mp hk).1) hy (mu2 m j k₀) {k₀} (fun i => by
      rw [Finset.mem_singleton]
      constructor
      · rintro rfl; exact ⟨Finset.mem_filter.mpr ⟨hk₀, rfl⟩, rfl⟩
      · rintro ⟨hi, hμ⟩
        exact key i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2 hμ)
  rw [Finset.sum_singleton] at hz
  obtain ⟨q, hq, hq0, _, hfk⟩ := hcomp k₀ hk₀
  exact ⟨_, q, k₀.2, hq, hq0, hfk ▸ hz⟩

theorem latVacuumGen_ne_zero (L : IntegralLattice) : latVacuumGen L ≠ 0 := by
  intro h
  have := congrArg (coordEα L 0) h
  rw [latVacuumGen, latStateGen, coordEα_apply, if_pos rfl, map_zero] at this
  exact one_ne_zero this

include hm in
/-- **C4b (1): `V_{L+λ_j}` is irreducible**, for every `j ∈ ℤ`. -/
theorem latticeModule_isIrreducible : (latticeModule m hm j).IsIrreducible := by
  refine ⟨⟨⟨latVacuumGen (latP m), 0, latVacuumGen_ne_zero _⟩⟩, fun P => ?_⟩
  by_cases hP : P.carrier = ⊥
  · exact Or.inl hP
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    obtain ⟨w, q, γ, hq, hq0, hmem⟩ := submod_exists_state m hm j P hx hx0
    exact submod_eq_top_of_vac m hm j P γ (submod_vac_of_state m hm j P w q hq hq0 γ hmem)

end RankOne

/-! ## §7  Relabelling the momenta -/

section Relabel

variable (L : IntegralLattice.{0}) (c : L.carrier → ℂ) (s : L.carrier)

/-- `e^n ↦ c(n) e^{n+s}` on `ℂ{L}`. -/
noncomputable def momRelabel : (L.carrier →₀ ℂ) →ₗ[ℂ] (L.carrier →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun n => c n • eGen L (n + s))

theorem momRelabel_eGen (n : L.carrier) : momRelabel L c s (eGen L n) = c n • eGen L (n + s) := by
  rw [momRelabel, eGen, Finsupp.linearCombination_single, one_smul]

theorem momRelabel_single (n : L.carrier) (a : ℂ) :
    momRelabel L c s (Finsupp.single n a) = (a * c n) • eGen L (n + s) := by
  rw [momRelabel, Finsupp.linearCombination_single, smul_smul]

variable (hc : ∀ n, c n ≠ 0)

include hc in
theorem momRelabel_comp_inv :
    (momRelabel L c s) ∘ₗ (momRelabel L (fun n => (c (n - s))⁻¹) (-s)) = LinearMap.id := by
  refine Finsupp.lhom_ext fun n a => ?_
  rw [LinearMap.comp_apply, momRelabel_single, map_smul, momRelabel_eGen, smul_smul,
    LinearMap.id_apply, show n + -s = n - s by abel, show n - s + s = n by abel, mul_assoc,
    inv_mul_cancel₀ (hc _), mul_one, eGen, Finsupp.smul_single, smul_eq_mul, mul_one]

include hc in
theorem momRelabel_inv_comp :
    (momRelabel L (fun n => (c (n - s))⁻¹) (-s)) ∘ₗ (momRelabel L c s) = LinearMap.id := by
  refine Finsupp.lhom_ext fun n a => ?_
  rw [LinearMap.comp_apply, momRelabel_single, map_smul, momRelabel_eGen, smul_smul,
    LinearMap.id_apply, show n + s - s = n by abel, show n + s + -s = n by abel, mul_assoc,
    mul_inv_cancel₀ (hc _), mul_one, eGen, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The relabelling equivalence `p ⊗ e^n ↦ c(n) p ⊗ e^{n+s}` of `V_L`-shaped spaces. -/
noncomputable def relabelEquiv : LatModuleGen L ≃ₗ[ℂ] LatModuleGen L :=
  LinearEquiv.lTensor (FockN (rank L))
    (LinearEquiv.ofLinear (momRelabel L c s) (momRelabel L (fun n => (c (n - s))⁻¹) (-s))
      (momRelabel_comp_inv L c s hc) (momRelabel_inv_comp L c s hc))

theorem relabelEquiv_latStateGen (p : FockN (rank L)) (n : L.carrier) :
    relabelEquiv L c s hc (latStateGen L p n) = c n • latStateGen L p (n + s) := by
  rw [relabelEquiv, latStateGen, LinearEquiv.lTensor_tmul]
  change p ⊗ₜ[ℂ] momRelabel L c s (eGen L n) = _
  rw [momRelabel_eGen, TensorProduct.tmul_smul]
  rfl

/-- Two linear maps out of `V_L`-shaped space agreeing on every `p ⊗ e^n` agree. -/
theorem linearMap_ext_latStateGen {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    {f g : LatModuleGen L →ₗ[ℂ] Y}
    (h : ∀ (p : FockN (rank L)) (n : L.carrier), f (latStateGen L p n) = g (latStateGen L p n)) :
    f = g :=
  LinearMap.ext_on_range (latStateGen_span L) fun q => h q.1 q.2

end Relabel

/-! ## §8  The cocycle factors -/

section Cocycles

open VOA.LatGen.Triplet

variable (m : ℕ) (hm : 1 ≤ m) (j : ℤ)

/-- The character `σ_j(k) = ε_{N_j}(kα, δ)` (a sign). -/
noncomputable def sig (k : ℤ) : ℂ :=
  latticeCocycle (glueLat m j) (glueIota m j k) (glueDelta m j)

theorem sig_add (k k' : ℤ) : sig m j (k + k') = sig m j k * sig m j k' := by
  have e : glueIota m j (k + k') = glueIota m j k + glueIota m j k' := (glueIota m j).map_add k k'
  rw [sig, sig, sig, e, latticeCocycle_add_left]

theorem sig_sq (k : ℤ) : sig m j k * sig m j k = 1 := latticeCocycle_sq _ _ _

/-- The module cocycle of `V_{L+λ_j}` in terms of `ε_L`, the character `σ_j`, and a
coboundary. -/
theorem kappa_eq (k n : ℤ) :
    latCob (latP m) (glueLat m j) (glueIota m j) k
        * latticeCocycle (glueLat m j) (glueIota m j k) (glueIota m j n + glueDelta m j)
      = latticeCocycle (latP m) k n * sig m j k
          * latCob (latP m) (glueLat m j) (glueIota m j) (k + n)
          * (latCob (latP m) (glueLat m j) (glueIota m j) n)⁻¹ := by
  have h : latticeCocycle (glueLat m j) (glueIota m j k) (glueIota m j n)
      * (latCob (latP m) (glueLat m j) (glueIota m j) k
        * latCob (latP m) (glueLat m j) (glueIota m j) n)
      = latticeCocycle (latP m) k n * latCob (latP m) (glueLat m j) (glueIota m j) (k + n) :=
    latticeCocycle_map_mul_latCob (latP m) (glueLat m j) (latP_even m) (glueLat_even m j)
      (glueIota m j) (glueIota_isometry m j) k n
  have hn := latCob_ne_zero (latP m) (glueLat m j) (glueIota m j) n
  rw [latticeCocycle_add_right]
  change _ * (_ * sig m j k) = _
  field_simp
  linear_combination sig m j k * h

end Cocycles

/-! ## §9  `V_{L+λ_j} ≅ V_{L+λ_{j+2m}}` and `V_{L+λ_0} ≅ V_L` -/

section Isos

open VOA.LatGen.Triplet

variable (m : ℕ) (hm : 1 ≤ m) (j : ℤ)

/-- Shorthand for the comparison factor `c_j = latCob_j`. -/
noncomputable abbrev cobJ (j : ℤ) (n : ℤ) : ℂ := latCob (latP m) (glueLat m j) (glueIota m j) n

/-- The rescaling of `j ↦ j + 2m`: `c(n) = c_j(n)⁻¹ c_{j+2m}(n-1) σ_j(n) σ_{j+2m}(n) ε(n,-1)`. -/
noncomputable def shiftC (n : ℤ) : ℂ :=
  (cobJ m j n)⁻¹ * cobJ m (j + 2 * m) (n + -1 : ℤ)
    * (sig m j n * sig m (j + 2 * m) n * latticeCocycle (latP m) n (-1 : ℤ))

theorem shiftC_ne_zero (n : ℤ) : shiftC m j n ≠ 0 := by
  have h1 := latCob_ne_zero (latP m) (glueLat m j) (glueIota m j) n
  have h2 := latCob_ne_zero (latP m) (glueLat m (j + 2 * m)) (glueIota m (j + 2 * m)) (n + -1 : ℤ)
  have h3 : sig m j n ≠ 0 := latticeCocycle_ne_zero _ _ _
  have h4 : sig m (j + 2 * m) n ≠ 0 := latticeCocycle_ne_zero _ _ _
  have h5 := latticeCocycle_ne_zero (latP m) n (-1 : ℤ)
  unfold shiftC
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero h1) h2) (mul_ne_zero (mul_ne_zero h3 h4) h5)

theorem shiftC_scalar (β n : ℤ) :
    (latCob (latP m) (glueLat m j) (glueIota m j) β
        * latticeCocycle (glueLat m j) (glueIota m j β) (glueIota m j n + glueDelta m j))
      * shiftC m j (β + n)
      = shiftC m j n * (latCob (latP m) (glueLat m (j + 2 * m)) (glueIota m (j + 2 * m)) β
        * latticeCocycle (glueLat m (j + 2 * m)) (glueIota m (j + 2 * m) β)
            (glueIota m (j + 2 * m) (n + -1 : ℤ) + glueDelta m (j + 2 * m))) := by
  rw [kappa_eq, kappa_eq]
  have hsa := sig_add m j β n
  have hsb := sig_add m (j + 2 * m) β n
  have hs2 := sig_sq m j β
  have hEl : latticeCocycle (latP m) (β + n) (-1 : ℤ)
      = latticeCocycle (latP m) β (-1 : ℤ) * latticeCocycle (latP m) n (-1 : ℤ) :=
    latticeCocycle_add_left _ _ _ _
  have hEr : latticeCocycle (latP m) β (n + -1 : ℤ)
      = latticeCocycle (latP m) β n * latticeCocycle (latP m) β (-1 : ℤ) :=
    latticeCocycle_add_right _ _ _ _
  have hA : (β + (n + -1 : ℤ) : ℤ) = β + n + -1 := by ring
  have hn := latCob_ne_zero (latP m) (glueLat m j) (glueIota m j) n
  have hn' := latCob_ne_zero (latP m) (glueLat m (j + 2 * m)) (glueIota m (j + 2 * m)) (n + -1 : ℤ)
  have hbn := latCob_ne_zero (latP m) (glueLat m j) (glueIota m j) (β + n)
  simp only [shiftC, cobJ]
  rw [hsa, hsb, hEl, hEr, hA]
  field_simp
  linear_combination (latticeCocycle (latP m) β n * sig m (j + 2 * m) β
    * latCob (latP m) (glueLat m (j + 2 * m)) (glueIota m (j + 2 * m)) (β + n + -1 : ℤ)
    * latticeCocycle (latP m) β (-1 : ℤ) * sig m j n * sig m (j + 2 * m) n
    * latticeCocycle (latP m) n (-1 : ℤ)) * hs2

theorem relabel_latP (c : ℤ → ℂ) (s : ℤ) (hc : ∀ n, c n ≠ 0) (p : FockN (rank (latP m))) (n : ℤ) :
    relabelEquiv (latP m) c s hc (latStateGen (latP m) p n) = c n • latStateGen (latP m) p (n + s) :=
  relabelEquiv_latStateGen (latP m) c s hc p n

/-- **C4b (2): `V_{L+λ_j} ≅ V_{L+λ_{j+2m}}`**, via `p ⊗ e^{nα} ↦ c(n) p ⊗ e^{(n-1)α}`. -/
noncomputable def latticeModuleShiftEquiv :
    ModuleEquiv (V2m m hm) (latticeModule m hm j) (latticeModule m hm (j + 2 * m)) :=
  moduleEquivOfCharge (latP m) (latP_even m) (latP_posDef m hm) (latticeModule m hm j)
    (latticeModule m hm (j + 2 * m)) (relabelEquiv (latP m) (shiftC m j) (-1 : ℤ) (shiftC_ne_zero m j))
    (fun (β : ℤ) t x => by
      have hext := linearMap_ext_latStateGen (latP m)
        (f := (relabelEquiv (latP m) (shiftC m j) (-1 : ℤ) (shiftC_ne_zero m j)).toLinearMap ∘ₗ
          (latticeModule m hm j).YM (latChargeGen (latP m) β) t)
        (g := (latticeModule m hm (j + 2 * m)).YM (latChargeGen (latP m) β) t ∘ₗ
          (relabelEquiv (latP m) (shiftC m j) (-1 : ℤ) (shiftC_ne_zero m j)).toLinearMap)
        (fun p (n : ℤ) => by
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
          rw [latticeModule_latChargeGen, map_smul, relabel_latP, relabel_latP, map_smul,
            latticeModule_latChargeGen, smul_smul, smul_smul, shiftC_scalar,
            show (β + (n + -1) : ℤ) = β + n + -1 by ring,
            show (t - 2 * m * β * (n + -1) - (j + 2 * m) * β : ℤ) = t - 2 * m * β * n - j * β by ring])
      exact LinearMap.congr_fun hext x)

/-- The rescaling for `V_{L+λ_0} ≅ V_L`: `c(n) = c_0(n)⁻¹ σ_0(n)`. -/
noncomputable def adjC (n : ℤ) : ℂ := (cobJ m 0 n)⁻¹ * sig m 0 n

theorem adjC_ne_zero (n : ℤ) : adjC m n ≠ 0 :=
  mul_ne_zero (inv_ne_zero (latCob_ne_zero _ _ _ _)) (latticeCocycle_ne_zero _ _ _)

theorem adjC_scalar (β n : ℤ) :
    (latCob (latP m) (glueLat m 0) (glueIota m 0) β
        * latticeCocycle (glueLat m 0) (glueIota m 0 β) (glueIota m 0 n + glueDelta m 0))
      * adjC m (β + n) = adjC m n * latticeCocycle (latP m) β n := by
  rw [kappa_eq]
  have hsa := sig_add m 0 β n
  have hs2 := sig_sq m 0 β
  have hn := latCob_ne_zero (latP m) (glueLat m 0) (glueIota m 0) n
  have hbn := latCob_ne_zero (latP m) (glueLat m 0) (glueIota m 0) (β + n)
  simp only [adjC, cobJ]
  rw [hsa]
  field_simp
  linear_combination (latticeCocycle (latP m) β n * sig m 0 n) * hs2

theorem adjoint_latChargeGen (β n t : ℤ) (p : FockN (rank (latP m))) :
    (adjointModule (V2m m hm)).YM (latChargeGen (latP m) β) t (latStateGen (latP m) p n)
      = latticeCocycle (latP m) β n •
          latStateGen (latP m) (EEVec (latP m) β (t - 2 * m * β * n) p) (β + n) := by
  change (latticeVOAGen (latP m) (latP_even m) (latP_posDef m hm)).Y (latChargeGen (latP m) β) t
    (latStateGen (latP m) p n) = _
  rw [latVOA_Y_latChargeGen, Yeαvec_tmul, latP_form]
  rfl

/-- **C4b (4): `V_{L+λ_0} ≅ V_L`** (the adjoint module), via `p ⊗ e^{nα} ↦ c(n) p ⊗ e^{nα}`. -/
noncomputable def latticeModuleZeroEquiv :
    ModuleEquiv (V2m m hm) (latticeModule m hm 0) (adjointModule (V2m m hm)) :=
  moduleEquivOfCharge (latP m) (latP_even m) (latP_posDef m hm) (latticeModule m hm 0)
    (adjointModule (V2m m hm)) (relabelEquiv (latP m) (adjC m) (0 : ℤ) (adjC_ne_zero m))
    (fun (β : ℤ) t x => by
      have hext := linearMap_ext_latStateGen (latP m)
        (f := (relabelEquiv (latP m) (adjC m) (0 : ℤ) (adjC_ne_zero m)).toLinearMap ∘ₗ
          (latticeModule m hm 0).YM (latChargeGen (latP m) β) t)
        (g := (adjointModule (V2m m hm)).YM (latChargeGen (latP m) β) t ∘ₗ
          (relabelEquiv (latP m) (adjC m) (0 : ℤ) (adjC_ne_zero m)).toLinearMap)
        (fun p (n : ℤ) => by
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
          rw [latticeModule_latChargeGen, map_smul, relabel_latP, relabel_latP, map_smul,
            adjoint_latChargeGen, smul_smul, smul_smul, adjC_scalar]
          simp only [add_zero, zero_mul, sub_zero])
      exact LinearMap.congr_fun hext x)

end Isos

/-! ## §10  Isomorphism classes: `V_{L+λ_j} ≅ V_{L+λ_{j'}}` iff `j ≡ j' (mod 2m)` -/

section Classes

open VOA.LatGen.Triplet

variable (m : ℕ) (hm : 1 ≤ m)

open Classical in
theorem coordEα_eq_finsuppScalarRight (L : IntegralLattice) (n : L.carrier) (y : LatModuleGen L) :
    coordEα L n y = TensorProduct.finsuppScalarRight ℂ ℂ (FockN (rank L)) L.carrier y n := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, ha, hb, map_add, Finsupp.add_apply]
  | tmul p g =>
    rw [TensorProduct.finsuppScalarRight_apply_tmul_apply, coordEα, LinearMap.comp_apply,
      LinearMap.lTensor_tmul, Finsupp.lapply_apply]
    exact TensorProduct.rid_tmul _ _

theorem eq_zero_of_coordEα (L : IntegralLattice) {y : LatModuleGen L}
    (h : ∀ n, coordEα L n y = 0) : y = 0 := by
  classical
  have hf : TensorProduct.finsuppScalarRight ℂ ℂ (FockN (rank L)) L.carrier y = 0 := by
    ext n
    rw [← coordEα_eq_finsuppScalarRight, h n, Finsupp.coe_zero, Pi.zero_apply]
  exact (LinearEquiv.map_eq_zero_iff _).mp hf

/-- The `α(0)`-spectrum of `V_{L+λ_j}` is `{χ_j(n)}`. -/
theorem latticeModule_zeroMode_eigen (j : ℤ) {μ : ℂ} {y : LatModuleGen (latP m)} (hy : y ≠ 0)
    (hZ : mode ((latticeModule m hm j).YM (hVec (latP m) (a0 m))) 0 y = μ • y) :
    ∃ n : ℤ, μ = chi m j n := by
  by_contra hne
  push Not at hne
  apply hy
  refine eq_zero_of_coordEα (latP m) fun n => ?_
  have hc : (coordEα (latP m) n) ∘ₗ mode ((latticeModule m hm j).YM (hVec (latP m) (a0 m))) 0
      = chi m j n • coordEα (latP m) n := by
    refine linearMap_ext_latStateGen (latP m) fun p (γ : ℤ) => ?_
    rw [LinearMap.comp_apply, latticeModule_zeroMode, map_smul, LinearMap.smul_apply,
      latStateGen, coordEα_apply]
    by_cases h : n = γ
    · rw [if_pos h, h]
    · rw [if_neg h, smul_zero, smul_zero]
  have h1 := LinearMap.congr_fun hc y
  rw [LinearMap.comp_apply, hZ, map_smul, LinearMap.smul_apply] at h1
  have h2 : (μ - chi m j n) • coordEα (latP m) n y = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) (hne n)
  · exact h3

include hm in
/-- An isomorphism `V_{L+λ_j} ≅ V_{L+λ_{j'}}` forces `j ≡ j' (mod 2m)`: it intertwines `α(0)`, and
`e^{λ_j}` has `α(0)`-eigenvalue `j/√(2m)`, while the spectrum on `V_{L+λ_{j'}}` is
`(2mn + j')/√(2m)`. -/
theorem latticeModule_iso_imp_modEq {j j' : ℤ}
    (e : ModuleEquiv (V2m m hm) (latticeModule m hm j) (latticeModule m hm j')) :
    ∃ n : ℤ, j = 2 * m * n + j' := by
  set y := e.toLinearEquiv (latChargeGen (latP m) 0)
  have hy : y ≠ 0 := by
    intro h
    exact latVacuumGen_ne_zero (latP m) ((LinearEquiv.map_eq_zero_iff _).mp h)
  have hZ : mode ((latticeModule m hm j').YM (hVec (latP m) (a0 m))) 0 y = chi m j 0 • y := by
    have h := e.map_act (hVec (latP m) (a0 m)) 0 (latChargeGen (latP m) 0)
    simp only [WeakModule.act_def] at h
    rw [← h]
    change e.toLinearEquiv (mode ((latticeModule m hm j).YM (hVec (latP m) (a0 m))) 0
      (latStateGen (latP m) (vacuumN (rank (latP m))) (0 : ℤ))) = _
    rw [latticeModule_zeroMode, map_smul]
    rfl
  obtain ⟨n, hn⟩ := latticeModule_zeroMode_eigen m hm j' hy hZ
  have h1 := chi_mul m hm j 0
  rw [hn, chi_mul m hm j' n] at h1
  refine ⟨n, ?_⟩
  have : ((2 * m * n + j' : ℤ) : ℂ) = ((j : ℤ) : ℂ) := by push_cast; rw [h1]; ring
  exact_mod_cast this.symm

include hm in
/-- **C4b (3): pairwise non-isomorphism** for `0 ≤ j, j' < 2m`, `j ≠ j'`. -/
theorem latticeModule_not_iso {j j' : ℤ} (hj : 0 ≤ j) (hj2 : j < 2 * m) (hj' : 0 ≤ j')
    (hj2' : j' < 2 * m) (hne : j ≠ j') :
    IsEmpty (ModuleEquiv (V2m m hm) (latticeModule m hm j) (latticeModule m hm j')) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨n, hn⟩ := latticeModule_iso_imp_modEq m hm e
  have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
  rcases lt_trichotomy n 0 with h | h | h
  · have : n ≤ -1 := by omega
    nlinarith
  · subst h; apply hne; linarith
  · have : 1 ≤ n := by omega
    nlinarith

theorem latticeModule_iso_of_eq {j j' : ℤ} (h : j = j') :
    Nonempty (ModuleEquiv (V2m m hm) (latticeModule m hm j) (latticeModule m hm j')) := by
  subst h; exact ⟨ModuleEquiv.refl _⟩

theorem latticeModule_iso_add_nat (j : ℤ) (n : ℕ) :
    Nonempty (ModuleEquiv (V2m m hm) (latticeModule m hm j) (latticeModule m hm (j + 2 * m * n))) := by
  induction n with
  | zero => exact latticeModule_iso_of_eq m hm (by simp)
  | succ n ih =>
    exact ⟨ih.some.trans ((latticeModuleShiftEquiv m hm _).trans
      (latticeModule_iso_of_eq m hm (by push_cast; ring)).some)⟩

include hm in
/-- **The isomorphism classes**: `V_{L+λ_j} ≅ V_{L+λ_{j'}}` iff `2m ∣ j - j'`. -/
theorem latticeModule_iso_iff (j j' : ℤ) :
    Nonempty (ModuleEquiv (V2m m hm) (latticeModule m hm j) (latticeModule m hm j'))
      ↔ (2 * (m : ℤ)) ∣ j - j' := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨n, hn⟩ := latticeModule_iso_imp_modEq m hm e
    exact ⟨n, by rw [hn]; ring⟩
  · rintro ⟨k, hk⟩
    rcases le_or_gt 0 k with h | h
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
      have e := (latticeModule_iso_add_nat m hm j' n).some
      exact ⟨(e.trans (latticeModule_iso_of_eq m hm (by linarith)).some).symm⟩
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -k by omega)
      have e := (latticeModule_iso_add_nat m hm j n).some
      exact ⟨e.trans (latticeModule_iso_of_eq m hm (by rw [← hn]; linarith)).some⟩

end Classes

end VOA.Classification.COne.LatMod
