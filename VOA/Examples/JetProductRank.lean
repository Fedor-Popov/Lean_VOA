/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.JetProductLower

/-!
# The per-degree lower bound for the jet image

* `jetDeg_finiteDimensional` — every graded piece `A_{r,N}` is finite dimensional (it is spanned
  by the finitely many products `P_{w,a}` of the right weight);
* `card_jetIndex_le_finrank` — `#{(k, λ, α) : |λ| + Σ (i+1) α_i + r = N} ≤ dim A_{r,N}`,
  where `k ≤ 2r`, `λ` is a multiset of `k` indices `≤ 2r - k`, and `α : Fin r → ℕ`.

Everything is proved outright.
-/

namespace VOA.JetProduct

open MvPolynomial VOA.SymbolModel
open scoped BigOperators Pointwise

noncomputable section

/-! ### Membership and weights of the products `P_{w,a}` -/

theorem genCoeff_mem_genSpan (g : Fin 4) (a : ℕ) : genCoeff g a ∈ genSpan :=
  Submodule.subset_span ⟨(g, a), rfl⟩

theorem Pga_mem_jetImage : ∀ {r : ℕ} (w : Fin r → Fin 4) (a : Fin r →₀ ℕ),
    Pga w a ∈ jetImage r
  | 0, w, a => by
    rw [Pga, Finset.univ_eq_empty, Finset.prod_empty, jetImage, pow_zero]
    exact Submodule.one_le.mp le_rfl
  | r + 1, w, a => by
    rw [Pga, Fin.prod_univ_succ, jetImage, pow_succ']
    refine Submodule.mul_mem_mul (genCoeff_mem_genSpan _ _) ?_
    have := Pga_mem_jetImage (fun i : Fin r => w i.succ) (toF fun i : Fin r => a i.succ)
    simpa [Pga, jetImage] using this

/-- The `J`-flag of a generator. -/
def jflag (g : Fin 4) : ℕ := if g = 3 then 1 else 0

theorem genSer_serWH (g : Fin 4) : SerWH (genSer g) (jflag g) := by
  fin_cases g
  · simpa [genSer, xSer, jflag] using serWH_mul (serWH_colSer 0) (serWH_colSer 0)
  · simpa [genSer, ySer, jflag] using serWH_mul (serWH_colSer 0) (serWH_colSer 1)
  · simpa [genSer, zSer, jflag] using serWH_mul (serWH_colSer 1) (serWH_colSer 1)
  · have h1 : SerWH (dS (colSer 0) * colSer 1) 1 := by
      simpa using serWH_mul (serWH_dS (serWH_colSer 0)) (serWH_colSer 1)
    have h2 : SerWH (colSer 0 * dS (colSer 1)) 1 := by
      simpa using serWH_mul (serWH_colSer 0) (serWH_dS (serWH_colSer 1))
    simpa [genSer, jSer, jflag] using serWH_sub h1 h2

theorem Pga_isWeightedHomogeneous {r : ℕ} (w : Fin r → Fin 4) (a : Fin r →₀ ℕ) :
    IsWeightedHomogeneous jetWt (Pga w a) (∑ i, ((a i : ℤ) + jflag (w i))) := by
  apply IsWeightedHomogeneous.prod
  intro i _
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp (genSer_serWH (w i) (a i))

theorem weight_toFinsupp (ms : Multiset ℕ) :
    Finsupp.weight (fun j : ℕ => (j : ℤ)) (Multiset.toFinsupp ms) = (ms.sum : ℤ) := by
  induction ms using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, map_add, ih,
      Multiset.toFinsupp_singleton, Finsupp.weight_single, Multiset.sum_add,
      Multiset.sum_singleton]
    push_cast
    simp

theorem weight_mono (ms : Multiset ℕ) (l : ℕ) :
    Finsupp.weight jetWt (mono ms l) = (ms.sum : ℤ) := by
  rw [mono, map_add, Finsupp.weight_single, ← weight_toFinsupp, Finsupp.weight_apply,
    Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • jetWt i)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [jetWt, uIdx]

/-- The `J`-count of a word. -/
def jcount {r : ℕ} (w : Fin r → Fin 4) : ℕ := ∑ i, jflag (w i)

/-- Homogeneity of the generating polynomials. -/
theorem coeff_Apol_ne_zero {r : ℕ} (ms : Multiset ℕ) (l : ℕ) (hms : ∀ j ∈ ms, j ≤ l)
    (w : Fin r → Fin 4) (d : Fin r →₀ ℕ) (hd : coeff d (Apol ms l w) ≠ 0) :
    ∑ i, d i + jcount w = ms.sum := by
  rw [coeff_Apol ms l hms] at hd
  have h := Pga_isWeightedHomogeneous w d hd
  rw [weight_mono] at h
  have : ((∑ i, d i + jcount w : ℕ) : ℤ) = (ms.sum : ℤ) := by
    rw [h, jcount]; push_cast; rw [Finset.sum_add_distrib]
  exact_mod_cast this

theorem esymm_isHomogeneous' (r n : ℕ) : (esymm (Fin r) ℂ n).IsHomogeneous n := by
  rw [esymm]
  apply IsHomogeneous.sum
  intro t ht
  have := IsHomogeneous.prod t (fun i => (X i : MvPolynomial (Fin r) ℂ)) (fun _ => 1)
    (fun i _ => isHomogeneous_X ℂ i)
  simpa [(Finset.mem_powersetCard.mp ht).2] using this

/-- The weight of an exponent vector `α`: `Σ (i+1) α_i`. -/
def awt {r : ℕ} (α : Fin r → ℕ) : ℕ := ∑ i : Fin r, ((i : ℕ) + 1) * α i

theorem esymmPow_isHomogeneous {r : ℕ} (α : Fin r → ℕ) :
    (esymmPow α).IsHomogeneous (awt α) := by
  rw [esymmPow, awt]
  apply IsHomogeneous.prod
  intro i _
  exact (esymm_isHomogeneous' r _).pow _

/-- The functional `Λ_{λ,α} = [u_λ v_0^l] ∘ E_α`. -/
def Lam {r : ℕ} (ms : Multiset ℕ) (l : ℕ) (α : Fin r → ℕ) : JetPoly →ₗ[ℂ] ℂ :=
  lcoeff ℂ (mono ms l) ∘ₗ opE α

/-- The functional `Λ_{λ,α}` on `P_{w,d}` is a coefficient of `e^α · Apol`. -/
theorem coeff_esymmPow_mul_Apol {r : ℕ} (ms : Multiset ℕ) (l : ℕ) (hms : ∀ j ∈ ms, j ≤ l)
    (α : Fin r → ℕ) (w : Fin r → Fin 4) (d : Fin r →₀ ℕ) :
    coeff d (esymmPow α * Apol ms l w) = Lam ms l α (Pga w d) := by
  rw [← MvPolynomial.coeff_coe, MvPolynomial.coe_mul, coe_Apol ms l hms, ← Gam_opE, coeff_Gam]
  rfl

theorem Apol_eq_zero {r : ℕ} (ms : Multiset ℕ) (l : ℕ) (hms : ∀ j ∈ ms, j ≤ l)
    (w : Fin r → Fin 4) (hw : ∑ i, vcount (w i) ≠ l) : Apol ms l w = 0 := by
  ext d
  rw [coeff_Apol ms l hms, coeff_mono_Pga ms l hms, if_neg hw, coeff_zero]

/-- A coefficient of `e^α · Apol` can only be nonzero in the matching total degree. -/
theorem coeff_esymmPow_mul_Apol_eq_zero {r : ℕ} (ms : Multiset ℕ) (l : ℕ)
    (hms : ∀ j ∈ ms, j ≤ l) (α : Fin r → ℕ) (w : Fin r → Fin 4) (d : Fin r →₀ ℕ)
    (hd : ∑ i, d i + jcount w ≠ awt α + ms.sum) :
    coeff d (esymmPow α * Apol ms l w) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  by_contra hne
  have h1 := esymmPow_isHomogeneous α (left_ne_zero_of_mul hne)
  have h2 := coeff_Apol_ne_zero ms l hms w p.2 (right_ne_zero_of_mul hne)
  have h1' : p.1.degree = awt α := by
    rw [Finsupp.degree_eq_weight_one]; exact h1
  apply hd
  have hsum : ∑ i, d i = p.1.degree + ∑ i, p.2 i := by
    rw [← hp, Finsupp.degree]
    simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    congr 1
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
      simpa using hi)).trans rfl |>.symm
  omega

/-! ### Linear independence of the elementary-symmetric monomials -/

theorem esymmPow_eq {r : ℕ} (α : Fin r → ℕ) :
    esymmPow α = (esymmAlgHom (Fin r) ℂ r (monomial (toF α) 1)).val := by
  rw [esymmAlgHom_apply, aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), esymmPow]
  rfl

theorem esymmPow_linearIndependent (r : ℕ) :
    LinearIndependent ℂ (fun α : Fin r → ℕ => esymmPow α) := by
  have hinj : Function.Injective
      ((symmetricSubalgebra (Fin r) ℂ).val.toLinearMap ∘ₗ
        (esymmAlgHom (Fin r) ℂ r).toLinearMap) :=
    Subtype.val_injective.comp (esymmAlgHom_injective ℂ (by simp))
  have hinj' : Function.Injective (toF (r := r)) := Finsupp.equivFunOnFinite.symm.injective
  have h := ((basisMonomials (Fin r) ℂ).linearIndependent.comp toF hinj').map'
    ((symmetricSubalgebra (Fin r) ℂ).val.toLinearMap ∘ₗ (esymmAlgHom (Fin r) ℂ r).toLinearMap)
    (LinearMap.ker_eq_bot.mpr hinj)
  convert h using 1
  funext α
  simp [esymmPow_eq, coe_basisMonomials]

/-! ### Finite dimensionality of the graded pieces -/

theorem Pga_cons {r : ℕ} (g : Fin 4) (w : Fin r → Fin 4) (b : ℕ) (a : Fin r → ℕ) :
    Pga (Fin.cons g w : Fin (r + 1) → Fin 4) (toF (Fin.cons b a : Fin (r + 1) → ℕ)) =
      genCoeff g b * Pga w (toF a) := by
  rw [Pga, Fin.prod_univ_succ]
  simp [Pga]

theorem jetImage_le_span : ∀ r : ℕ, jetImage r ≤
    Submodule.span ℂ (Set.range fun p : (Fin r → Fin 4) × (Fin r → ℕ) => Pga p.1 (toF p.2))
  | 0 => by
    rw [jetImage, pow_zero, Submodule.one_eq_span]
    apply Submodule.span_mono
    rintro _ rfl
    refine ⟨(Fin.elim0, Fin.elim0), ?_⟩
    simp [Pga]
  | r + 1 => by
    rw [jetImage, pow_succ']
    calc genSpan * genSpan ^ r ≤ genSpan * Submodule.span ℂ (Set.range fun p :
          (Fin r → Fin 4) × (Fin r → ℕ) => Pga p.1 (toF p.2)) :=
          mul_le_mul' le_rfl (jetImage_le_span r)
      _ = Submodule.span ℂ ((Set.range fun p : Fin 4 × ℕ => genCoeff p.1 p.2) *
          Set.range fun p : (Fin r → Fin 4) × (Fin r → ℕ) => Pga p.1 (toF p.2)) := by
          rw [genSpan, Submodule.span_mul_span]
      _ ≤ _ := by
          apply Submodule.span_mono
          rintro _ ⟨_, ⟨⟨g, b⟩, rfl⟩, _, ⟨⟨w, a⟩, rfl⟩, rfl⟩
          exact ⟨(Fin.cons g w, Fin.cons b a), Pga_cons g w b a⟩

theorem jetDeg_le_span (r : ℕ) (N : ℤ) :
    (jetDeg r N).map (jetImage r).subtype ≤ Submodule.span ℂ
      (((Finset.univ ×ˢ Fintype.piFinset fun _ : Fin r => Finset.range (N.toNat + 1)).image
        fun p : (Fin r → Fin 4) × (Fin r → ℕ) => Pga p.1 (toF p.2) : Finset JetPoly) :
          Set JetPoly) := by
  classical
  rintro _ ⟨x, hx, rfl⟩
  have hxw : IsWeightedHomogeneous jetWt (x : JetPoly) (N - r) :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp hx
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (jetImage_le_span r x.2)
  have hcomp := congrArg (weightedHomogeneousComponent jetWt (N - r)) hc
  rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hxw),
    if_pos rfl] at hcomp
  simp only [Submodule.subtype_apply]
  rw [← hcomp, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  have hp := Pga_isWeightedHomogeneous p.1 (toF p.2)
  by_cases hwt : (∑ i, (((toF p.2) i : ℤ) + jflag (p.1 i))) = N - r
  · rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hp),
      if_pos hwt.symm]
    apply Submodule.subset_span
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨p, Finset.mem_product.mpr ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr fun i => ?_⟩,
      rfl⟩
    rw [Finset.mem_range]
    have h1 : ((p.2 i : ℕ) : ℤ) ≤ ∑ j, (((toF p.2) j : ℤ) + jflag (p.1 j)) := by
      calc ((p.2 i : ℕ) : ℤ) ≤ ((toF p.2) i : ℤ) + jflag (p.1 i) := by simp
        _ ≤ _ := Finset.single_le_sum (f := fun j => (((toF p.2) j : ℤ) + jflag (p.1 j)))
            (fun j _ => by positivity) (Finset.mem_univ i)
    omega
  · rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hp),
      if_neg (Ne.symm hwt)]
    exact Submodule.zero_mem _

/-- Every graded piece of the jet image is finite dimensional. -/
instance jetDeg_finiteDimensional (r : ℕ) (N : ℤ) : FiniteDimensional ℂ (jetDeg r N) := by
  have hfin : FiniteDimensional ℂ ((jetDeg r N).map (jetImage r).subtype) :=
    Submodule.finiteDimensional_of_le (jetDeg_le_span r N)
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (jetImage r).injective_subtype (jetDeg r N)).symm


/-! ### The independent functionals -/

/-- The index type of the functionals: a charge `k ≤ 2r`, a row `λ`, and an exponent `α`. -/
abbrev JIdx (r : ℕ) : Type := Σ k : Fin (2 * r + 1), Rows r k × (Fin r → ℕ)

/-- The exponents `α` (with `α_i ≤ N`) completing a row to weight `N`. -/
def fib (r N k : ℕ) (s : Rows r k) : Finset (Fin r → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (N + 1)).filter fun α => (msOf s).sum + awt α + r = N

/-- The indices of conformal weight `N`. -/
def jetIndex (r N : ℕ) : Finset (JIdx r) :=
  Finset.univ.sigma fun _ => (Finset.univ ×ˢ Fintype.piFinset fun _ => Finset.range (N + 1)).filter
    fun p => (msOf p.1).sum + awt p.2 + r = N

/-- The functional attached to an index. -/
def LamI (r : ℕ) (i : JIdx r) : JetPoly →ₗ[ℂ] ℂ := Lam (msOf i.2.1) (2 * r - i.1) i.2.2

theorem sum_jetIndex {M : Type*} [AddCommMonoid M] {r N : ℕ} (f : JIdx r → M) :
    ∑ i ∈ jetIndex r N, f i = ∑ k : Fin (2 * r + 1), ∑ s : Rows r k, ∑ α ∈ fib r N k s,
      f ⟨k, (s, α)⟩ := by
  rw [jetIndex, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s _
  rw [fib, Finset.sum_filter]

theorem vcount_ne_of_ne {r : ℕ} (k k' : Fin (2 * r + 1)) (hkk : k' ≠ k) (w : Cols r k) :
    ∑ i, vcount (w.1 i) ≠ 2 * r - k' := by
  rw [sum_vcount, w.2]
  have := k.2; have := k'.2
  intro h
  exact hkk (Fin.ext (by omega))

/-- **Independence of the functionals** on the weight-`N` part of `A_r`. -/
theorem jetIndex_indep (r N : ℕ) (c : JIdx r → ℂ)
    (hc : ∀ Q : JetPoly, Q ∈ jetImage r → IsWeightedHomogeneous jetWt Q ((N : ℤ) - r) →
      ∑ i ∈ jetIndex r N, c i * LamI r i Q = 0) :
    ∀ i ∈ jetIndex r N, c i = 0 := by
  rintro ⟨k0, s0, α0⟩ hi
  have hk0 : (k0 : ℕ) ≤ 2 * r := Nat.lt_succ_iff.mp k0.2
  let y : Rows r k0 → MvPolynomial (Fin r) ℂ := fun s =>
    ∑ α ∈ fib r N k0 s, c ⟨k0, (s, α)⟩ • esymmPow α
  have hy : ∀ w : Cols r k0, ∑ s, y s * Apol (msOf s) (2 * r - k0) w.1 = 0 := by
    intro w
    ext d
    rw [coeff_zero, coeff_sum]
    simp only [y, Finset.sum_mul, coeff_sum, smul_mul_assoc, coeff_smul, smul_eq_mul]
    by_cases hW : ∑ i, d i + jcount w.1 + r = N
    · have htot := hc (Pga w.1 d) (Pga_mem_jetImage w.1 d) (by
        have := Pga_isWeightedHomogeneous w.1 d
        convert this using 1
        rw [Finset.sum_add_distrib]
        have : ((∑ i, d i + jcount w.1 + r : ℕ) : ℤ) = N := by exact_mod_cast hW
        push_cast [jcount] at this
        omega)
      rw [sum_jetIndex, Finset.sum_eq_single k0] at htot
      · rw [← htot]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro α _
        rw [coeff_esymmPow_mul_Apol _ _ (msOf_le s)]
        rfl
      · intro k _ hk
        apply Finset.sum_eq_zero
        intro s _
        apply Finset.sum_eq_zero
        intro α _
        simp only [LamI]
        rw [← coeff_esymmPow_mul_Apol _ _ (msOf_le s), Apol_eq_zero _ _ (msOf_le s) _
          (vcount_ne_of_ne k0 k hk w), mul_zero, coeff_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · apply Finset.sum_eq_zero
      intro s _
      apply Finset.sum_eq_zero
      intro α hα
      rw [coeff_esymmPow_mul_Apol_eq_zero _ _ (msOf_le s), mul_zero]
      intro h
      apply hW
      have := (Finset.mem_filter.mp hα).2
      omega
  have hy0 := block_indep r k0 hk0 y hy
  have hs0 : ∑ α ∈ fib r N k0 s0, c ⟨k0, (s0, α)⟩ • esymmPow α = 0 := congrFun hy0 s0
  have hα0 : α0 ∈ fib r N k0 s0 := by
    rw [jetIndex, Finset.mem_sigma] at hi
    obtain ⟨-, hi⟩ := hi
    rw [Finset.mem_filter, Finset.mem_product] at hi
    exact Finset.mem_filter.mpr ⟨hi.1.2, hi.2⟩
  exact (linearIndependent_iff'.mp (esymmPow_linearIndependent r)) _
    (fun α => c ⟨k0, (s0, α)⟩) hs0 α0 hα0

/-- **The per-degree lower bound**: `#jetIndex r N ≤ dim A_{r,N}`. -/
theorem card_jetIndex_le_finrank (r N : ℕ) :
    (jetIndex r N).card ≤ Module.finrank ℂ (jetDeg r (N : ℤ)) := by
  classical
  set V := jetDeg r (N : ℤ)
  let f : jetIndex r N → Module.Dual ℂ V := fun i =>
    LamI r i.1 ∘ₗ (jetImage r).subtype ∘ₗ V.subtype
  have hli : LinearIndependent ℂ f := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    let c : JIdx r → ℂ := fun j => if h : j ∈ jetIndex r N then
      (if (⟨j, h⟩ : jetIndex r N) ∈ s then g ⟨j, h⟩ else 0) else 0
    have hc : ∀ Q : JetPoly, Q ∈ jetImage r → IsWeightedHomogeneous jetWt Q ((N : ℤ) - r) →
        ∑ j ∈ jetIndex r N, c j * LamI r j Q = 0 := by
      intro Q hQ hQw
      have hv : (⟨Q, hQ⟩ : jetImage r) ∈ V := (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hQw
      have h1 := congrArg (fun φ : Module.Dual ℂ V => φ ⟨⟨Q, hQ⟩, hv⟩) hg
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.zero_apply, f, LinearMap.comp_apply, Submodule.subtype_apply] at h1
      rw [← h1, ← Finset.sum_coe_sort (jetIndex r N)]
      rw [← Finset.sum_subset (Finset.subset_univ s)]
      · apply Finset.sum_congr rfl
        intro j hj
        simp [c, hj]
      · intro j _ hj
        simp [c, hj]
    have := jetIndex_indep r N c hc i.1 i.2
    simpa [c, hi] using this
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_coe, Subspace.dual_finrank_eq] at this


end

end VOA.JetProduct
