/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusUnitaryCert
import VOA.Classification.COne.PlusUnitaryReduce
import VOA.Classification.COne.PlusUnitaryVacuum

/-!
# H4: a top vector of a `V_{2m}⁺`-module with the vacuum's eigenvalues generates `V⁺`

For `m ≥ 2`, `V⁺ = V_{2m}⁺` is spanned modulo `C₂(V⁺)` by iterated products of `ω, W⁴, E`
(`top_eq_span_iterProd`): this is Q2's sector reduction (`sector_reduction`), the strong
generation of `M(1)⁺` by `ω, W⁴` (`strongGenM1_holds`) and `V⁺(1) ⊆ C₂(V⁺) + E₍₋₁₎M(1)⁺`
(`sectorOneViaE_holds`).  By the propagation theorem `good_of_top_eq`, the zero mode of every
`a ∈ V⁺` on a lowest-weight vector is a fixed polynomial in the eigenvalues of `o(ω), o(W), o(E)`.
Comparing with the vacuum of `V⁺` itself, a top vector with eigenvalues `(0,0,0)` is killed by
every `o(a)`, `a ∈ V⁺_{≥1}`; the generic `nonempty_moduleEquiv_adjoint_of_vacuumTop` finishes.

## Main results
* `top_eq_span_iterProd` — `V⁺ = span{iterated products of ω, W, E} + C₂(V⁺)` (`m ≥ 2`).
* `plusVacuumTop_holds : 2 ≤ m → PlusVacuumTop m hm` (**H4 is a theorem**).
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne.PlusUnitary

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  PlusC2

/-! ## Generic: iterated products along a graded homomorphism -/

section Generic

universe u

variable {𝒰 𝒱 : Type u} [AddCommGroup 𝒰] [Module ℂ 𝒰] [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {U : VertexOperatorAlgebra 𝒰} {V : VertexOperatorAlgebra 𝒱}

theorem isIterProd_map {φ : 𝒰 →ₗ[ℂ] 𝒱} (hφ : GradedHom U V φ) {S : Set 𝒰} {T : Set 𝒱}
    (hST : ∀ s ∈ S, φ s ∈ T) {x : 𝒰} (hx : IsIterProd U S x) : IsIterProd V T (φ x) := by
  induction hx with
  | vacuum => rw [hφ.map_vacuum]; exact IsIterProd.vacuum
  | step s hs n hn x _ ih => rw [hφ.map_smul]; exact IsIterProd.step _ (hST s hs) n hn _ ih

theorem map_iterProdSpan_le {φ : 𝒰 →ₗ[ℂ] 𝒱} (hφ : GradedHom U V φ) {S : Set 𝒰} {T : Set 𝒱}
    (hST : ∀ s ∈ S, φ s ∈ T) {x : 𝒰} (hx : x ∈ iterProdSpan U S) : φ x ∈ iterProdSpan V T := by
  refine Submodule.span_induction (p := fun x _ => φ x ∈ iterProdSpan V T) ?_ ?_ ?_ ?_ hx
  · intro y hy; exact Submodule.subset_span (isIterProd_map hφ hST hy)
  · simp only [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; simp only [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; simp only [map_smul]; exact Submodule.smul_mem _ c ha

theorem idGradedHom (V : VertexOperatorAlgebra 𝒱) : GradedHom V V LinearMap.id where
  map_vacuum := rfl
  map_smul _ _ _ := rfl
  map_grading h := h

/-- The adjoint module has lowest weight `0`. -/
theorem isLowestWeight_adjoint (V : VertexOperatorAlgebra 𝒱) : IsLowestWeight (adjointModule V) 0 := by
  intro α hα
  by_cases hint : ∃ n : ℤ, (n : ℂ) = α
  · obtain ⟨n, rfl⟩ := hint
    change adjWeight V (n : ℂ) ≠ ⊥ at hα
    rw [adjWeight_cast] at hα
    have hn : 0 ≤ n := by
      by_contra h; exact hα (V.positivity n (by omega))
    exact ⟨n.toNat, by rw [zero_add]; exact_mod_cast (Int.toNat_of_nonneg hn).symm⟩
  · push Not at hint
    exact absurd (adjWeight_eq_bot V hint) hα

theorem vacuum_mem_adjoint_weight (V : VertexOperatorAlgebra 𝒱) :
    V.vacuum ∈ (adjointModule V).weight 0 := by
  have h := adjWeight_cast V 0
  rw [Int.cast_zero] at h
  change V.vacuum ∈ adjWeight V 0
  rw [h]; exact V.vacuum_mem

theorem oMod_adjoint_vacuum (V : VertexOperatorAlgebra 𝒱) {k : ℤ} (hk : 1 ≤ k) {a : 𝒱}
    (ha : a ∈ V.grading k) : oMod (adjointModule V) a V.vacuum = 0 := by
  rw [oMod_homogeneous _ ha]
  exact V.smul_vacuum_nonneg a (by omega)

end Generic

/-! ## The generators of `V⁺` -/

variable (m : ℕ) (hm : 1 ≤ m)

/-- `(ω, W⁴, E)`. -/
noncomputable def gP : Fin 3 → VP m hm := ![(V2mPlus m hm).conformalVector, WP m hm, EP m hm]

/-- Their weights. -/
def wtP : Fin 3 → ℕ := ![2, 4, m]

theorem WP_mem_grading : WP m hm ∈ (V2mPlus m hm).grading 4 :=
  (incl_gradedHom m hm).map_grading (WM_mem_grading m hm)

theorem EP_mem_grading : EP m hm ∈ (V2mPlus m hm).grading (m : ℤ) := by
  change ((EP m hm : VP m hm) : LatModuleGen (latP m)) ∈ (V2m m hm).grading (m : ℤ)
  have hn : ∀ c : ℤ, c = 1 ∨ c = -1 → LatGen.halfNorm (latP m) (c : (latP m).carrier) = m := by
    rintro c (rfl | rfl) <;> simp only [LatGen.halfNorm, latP_form] <;> omega
  rw [V2m_grading_eq]
  refine Submodule.add_mem _ ?_ ?_
  · have := latChargeGen_mem_grading (latP m) ((1 : ℤ) : (latP m).carrier)
    rwa [hn 1 (Or.inl rfl)] at this
  · have := latChargeGen_mem_grading (latP m) (-((1 : ℤ) : (latP m).carrier))
    rwa [show -((1 : ℤ) : (latP m).carrier) = ((-1 : ℤ) : (latP m).carrier) from rfl,
      hn (-1) (Or.inr rfl)] at this

theorem gP_mem_grading (i : Fin 3) : gP m hm i ∈ (V2mPlus m hm).grading (wtP m i : ℤ) := by
  fin_cases i
  · exact (V2mPlus m hm).conformal_mem
  · exact WP_mem_grading m hm
  · exact EP_mem_grading m hm

/-- Every `P(q ⊗ e⁰)` is an iterated product of `ω, W⁴`. -/
theorem PP_sec0_mem (q : FockN (rank (latP m))) :
    PP m hm (latStateGen (latP m) q 0) ∈ iterProdSpan (V2mPlus m hm) (Set.range (gP m hm)) := by
  set q' := (1 / 2 : ℂ) • (q + sigmaN (rank (latP m)) q)
  have hq' : sigmaN (rank (latP m)) q' = q' := by
    simp only [q', map_smul, map_add, sigmaN_sigmaN, add_comm]
  have hmem : latStateGen (latP m) q' 0 ∈ m1Carrier m hm := (mem_m1Carrier_iff m hm _).mpr ⟨q', hq', rfl⟩
  have hPP : PP m hm (latStateGen (latP m) q 0) = incl m hm ⟨_, hmem⟩ := by
    apply Subtype.ext
    rw [PP_coe, incl_coe, thetaLat_latStateGen, neg_zero, ← latStateGen_add_boson,
      ← latStateGen_csmul]
  rw [hPP]
  refine map_iterProdSpan_le (incl_gradedHom m hm) ?_ (by rw [strongGenM1_holds m hm]; trivial)
  rintro s (rfl | rfl)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- **`V⁺` is spanned modulo `C₂` by iterated products of `ω, W⁴, E`** (`m ≥ 2`). -/
theorem top_eq_span_iterProd (hm2 : 2 ≤ m) :
    (⊤ : Submodule ℂ (VP m hm)) =
      Submodule.span ℂ {x | IsIterProd (V2mPlus m hm) (Set.range (gP m hm)) x} ⊔ O₂ (V2mPlus m hm) := by
  set T := iterProdSpan (V2mPlus m hm) (Set.range (gP m hm))
  have h0 : sectorP m hm 0 ≤ T := by
    rw [sectorP, Submodule.span_le]; rintro _ ⟨q, rfl⟩; exact PP_sec0_mem m hm q
  have hE : eTimesM1Plus m hm ≤ T := by
    rw [eTimesM1Plus, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    exact smul_mem_iterProdSpan _ _ (show EP m hm ∈ Set.range (gP m hm) from ⟨2, rfl⟩) le_rfl
      (PP_sec0_mem m hm q)
  have h1 : sectorP m hm (1 : ℤ) ≤ O₂ (V2mPlus m hm) ⊔ T := by
    rw [sectorP, Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact (sup_le_sup_left hE _) (sectorOneViaE_holds m hm hm2 f)
  refine le_antisymm ?_ le_top
  intro v _
  have hv := sector_reduction m hm v
  change v ∈ T ⊔ O₂ (V2mPlus m hm)
  have hle : O₂ (V2mPlus m hm) ⊔ (sectorP m hm 0 ⊔ sectorP m hm (1 : ℤ)) ≤ T ⊔ O₂ (V2mPlus m hm) :=
    sup_le le_sup_right (sup_le (h0.trans le_sup_left) (h1.trans (sup_le le_sup_right le_sup_left)))
  exact hle hv

/-- **H4 is a theorem** (`m ≥ 2`). -/
theorem plusVacuumTop_holds (hm2 : 2 ≤ m) : PlusVacuumTop m hm := by
  intro M _ _ N hirr x hlow hx hx0 hW hE
  have hgood := good_of_top_eq (V := V2mPlus m hm) (idGradedHom (V2mPlus m hm)) (wtP m)
    (gP_mem_grading m hm) (fun i => by fin_cases i <;> simp [wtP] <;> omega)
    (top_eq_span_iterProd m hm hm2)
  refine nonempty_moduleEquiv_adjoint_of_vacuumTop (V2mPlus_isSimple m hm) N hirr hlow hx hx0 ?_
  intro k hk a ha
  obtain ⟨Φ, _, hΦ⟩ := hgood k a ha
  have hN := hΦ M N 0 hlow x hx 0 (fun i => by
    fin_cases i
    · change oMod N (V2mPlus m hm).conformalVector x = 0 • x
      rw [oMod_homogeneous N (V2mPlus m hm).conformal_mem, show (2 : ℤ) - 1 = 1 by norm_num,
        N.L0_weight 0 x hx]
    · simpa using hW
    · simpa using hE)
  have hA := hΦ (VP m hm) (adjointModule (V2mPlus m hm)) 0 (isLowestWeight_adjoint _) _
    (vacuum_mem_adjoint_weight _) 0 (fun i => by
      rw [Pi.zero_apply, zero_smul]
      exact oMod_adjoint_vacuum _ (by fin_cases i <;> simp [wtP] <;> omega) (gP_mem_grading m hm i))
  rw [LinearMap.id_apply] at hN hA
  rw [oMod_adjoint_vacuum _ hk ha] at hA
  have hvac : (V2mPlus m hm).vacuum ≠ 0 := (V2mPlus_isSimple m hm).vacuum_ne_zero
  have h0 : MvPolynomial.eval 0 Φ = 0 := (smul_eq_zero.mp hA.symm).resolve_right hvac
  rw [hN, h0, zero_smul]

end VOA.Classification.COne.PlusUnitary
