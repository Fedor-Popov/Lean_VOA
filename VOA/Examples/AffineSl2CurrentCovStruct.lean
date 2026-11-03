import VOA.Examples.AffineSl2CurrentCov

/-!
# The dual-Coxeter struct residue `struct_residue_value` — the flip-band telescoping

This file discharges the single open obligation of `AffineSl2CurrentCov`, the structure-constant
`:JJ:` residue (the normal-ordering anomaly):
`∑_{aa,bb} κ⁻¹(aa,bb) • ∑ᶠ_p structPart k c aa bb μ p x = (4 μ) • Jᶜ_{μ-1} x`,
and then runs the short cascade `Hbr_collapse → Lcomm_current → Jfield_DCovariant` to the
unconditional affine Sugawara current covariance `[L₋₁, Jᶜ_μ] = -μ Jᶜ_{μ-1}` (the hypothesis `hJ`).

The engine is the **flip-band telescoping** of the bilinear
`bilin d e μ x = ∑ᶠ_p (if 0≤p then J^d_{μ-p-1}(J^e_p x) else J^e_p(J^d_{μ-p-1}x))`:
`bilin d e μ x - bilin e d μ x = μ • ∑_{e'} f(d,e,e') Jᵉ'_{μ-1} x` (a finite band of width `μ`,
each flip a structure-constant commutator that survives, the central part vanishing on the band).
Contracting with `κ⁻¹` through `graised_antisymm` and `struct_casimir_contract = 4 = 2h^∨` gives `4μ`.
-/

open VOA VOA.AffineVOA VOA.AffineVOA.SugawaraCov

namespace VOA.AffineVOA.SugawaraCov

open scoped BigOperators
open Module (End)
open VOA.AffineLie

universe u

/-! ## The bilinear `bilin` and its finiteness -/

/-- The per-`p` summand of `bilin`. -/
noncomputable def bilinSummand (k : ℂ) (d e : Fin 3) (μ p : ℤ) (x : WakModule k) : WakModule k :=
  if 0 ≤ p then J k d (μ - p - 1) (J k e p x) else J k e p (J k d (μ - p - 1) x)

/-- The `μ`-shifted normal-ordered bilinear `:J^d J^e:_{μ-1}` acting on `x`:
`bilin d e μ x = ∑ᶠ_p (if 0≤p then J^d_{μ-p-1} J^e_p else J^e_p J^d_{μ-p-1}) x`. -/
noncomputable def bilin (k : ℂ) (d e : Fin 3) (μ : ℤ) (x : WakModule k) : WakModule k :=
  ∑ᶠ p : ℤ, bilinSummand k d e μ p x

/-- The bilinear summand has finite support in `p` (`J_regularity` truncates both factors). -/
theorem bilinSummand_support_finite (k : ℂ) (d e : Fin 3) (μ : ℤ) (x : WakModule k) :
    (Function.support (fun p : ℤ => bilinSummand k d e μ p x)).Finite := by
  obtain ⟨Be, hBe⟩ := J_regularity k e x
  obtain ⟨Bd, hBd⟩ := J_regularity k d x
  apply Set.Finite.subset (Set.finite_Icc (min 0 (μ - Bd)) (max (Be - 1) (-1)))
  intro p hp
  rw [Function.mem_support, bilinSummand] at hp
  rw [Set.mem_Icc]
  by_cases hpp : 0 ≤ p
  · rw [if_pos hpp] at hp
    have hne : J k e p x ≠ 0 := fun h => hp (by rw [h, map_zero])
    have hpBe : p < Be := by by_contra hc; push_neg at hc; exact hne (hBe p hc)
    exact ⟨le_trans (min_le_left _ _) hpp, le_trans (by omega) (le_max_left _ _)⟩
  · rw [if_neg hpp] at hp
    push_neg at hpp
    have hne : J k d (μ - p - 1) x ≠ 0 := fun h => hp (by rw [h, map_zero])
    have hd : μ - p - 1 < Bd := by by_contra hc; push_neg at hc; exact hne (hBd _ hc)
    exact ⟨le_trans (min_le_right _ _) (by omega), le_trans (by omega : p ≤ -1) (le_max_right _ _)⟩

/-- `bilin` is finitely supported (its summand is). -/
theorem bilin_summand_fin (k : ℂ) (d e : Fin 3) (μ : ℤ) (x : WakModule k) :
    (Function.support (fun p : ℤ => bilinSummand k d e μ p x)).Finite :=
  bilinSummand_support_finite k d e μ x

/-! ## The reindex `bilin2 = bilin` (`p ↦ -p-1`) -/

/-- The second-piece summand `if 0≤p then J^e_{-p-1}(J^d_{μ+p}x) else J^d_{μ+p}(J^e_{-p-1}x)`. -/
noncomputable def bilin2Summand (k : ℂ) (e d : Fin 3) (μ p : ℤ) (x : WakModule k) : WakModule k :=
  if 0 ≤ p then J k e (-p - 1) (J k d (μ + p) x) else J k d (μ + p) (J k e (-p - 1) x)

/-- The involution `p ↦ -p-1` on `ℤ`. -/
def negSuccEquiv : ℤ ≃ ℤ :=
  (Function.Involutive.toPerm (fun p : ℤ => -p - 1) (fun p => by ring))

@[simp] theorem negSuccEquiv_apply (p : ℤ) : negSuccEquiv p = -p - 1 := rfl

/-- **The second piece is the first, reindexed**: `∑ᶠ_p bilin2Summand e d μ p x = bilin d e μ x`. -/
theorem bilin2_eq (k : ℂ) (e d : Fin 3) (μ : ℤ) (x : WakModule k) :
    (∑ᶠ p : ℤ, bilin2Summand k e d μ p x) = bilin k d e μ x := by
  rw [bilin, ← finsum_comp_equiv negSuccEquiv (f := fun p => bilin2Summand k e d μ p x)]
  refine finsum_congr fun p => ?_
  rw [negSuccEquiv_apply, bilin2Summand, bilinSummand]
  rw [show (-(-p - 1) - 1 : ℤ) = p from by ring, show (μ + (-p - 1) : ℤ) = μ - p - 1 from by ring]
  by_cases hp : 0 ≤ p
  · rw [if_pos hp, if_neg (by omega : ¬ (0 : ℤ) ≤ -p - 1)]
  · rw [if_neg hp, if_pos (by omega : (0 : ℤ) ≤ -p - 1)]

/-! ## The flip-band telescoping `bilin d e - bilin e d = μ • ∑ f Jᵉ'_{μ-1}` -/

/-- The structure-constant operator `Vop = ∑_{e'} f(d,e,e') J^{e'}_{μ-1}`, the `p`-independent
struct part of every band commutator. -/
noncomputable def Vop (k : ℂ) (d e : Fin 3) (μ : ℤ) : End ℂ (WakModule k) :=
  ∑ e' : Fin 3, fabc d e e' • J k e' (μ - 1)

/-- The elementary band commutator `[J^d_{μ-p-1}, J^e_p] = Vop + central` (modes sum to `μ-1`). -/
theorem band_bracket (k : ℂ) (d e : Fin 3) (μ p : ℤ) :
    J k d (μ - p - 1) * J k e p - J k e p * J k d (μ - p - 1)
      = Vop k d e μ
        + (if μ - 1 = 0 then (((μ - p - 1 : ℤ) : ℂ) * k * kappa d e) • (LinearMap.id : End ℂ (WakModule k)) else 0) := by
  rw [J_bracket k d e (μ - p - 1) p, show (μ - p - 1 + p : ℤ) = μ - 1 from by ring, Vop]

/-- The involution `p ↦ μ-p-1` on `ℤ`. -/
def flipMuEquiv (μ : ℤ) : ℤ ≃ ℤ :=
  Function.Involutive.toPerm (fun p : ℤ => μ - p - 1) (fun p => by ring)

@[simp] theorem flipMuEquiv_apply (μ p : ℤ) : flipMuEquiv μ p = μ - p - 1 := rfl

/-- `bilin e d` reindexed by `p ↦ μ-p-1`. -/
theorem bilin_eflip (k : ℂ) (e d : Fin 3) (μ : ℤ) (x : WakModule k) :
    bilin k e d μ x = ∑ᶠ p : ℤ, bilinSummand k e d μ (μ - p - 1) x := by
  rw [bilin, ← finsum_comp_equiv (flipMuEquiv μ) (f := fun p => bilinSummand k e d μ p x)]
  exact finsum_congr fun p => by rw [flipMuEquiv_apply]

/-- The per-`p` difference `B(d,e,p) - B'(p)` equals `w(p) • (Vop x)`, where `w(p) = [0≤p] - [μ≤p]`
is the signed band indicator (the central part cancels on the band). -/
theorem bilinSummand_flip_diff (k : ℂ) (d e : Fin 3) (μ p : ℤ) (x : WakModule k) :
    bilinSummand k d e μ p x - bilinSummand k e d μ (μ - p - 1) x
      = ((if 0 ≤ p then (1 : ℤ) else 0) - (if μ ≤ p then (1 : ℤ) else 0)) • (Vop k d e μ x) := by
  -- the elementary band commutator on `x`: `P - Q = Vop x + central x`
  have hPQ : J k d (μ - p - 1) (J k e p x) - J k e p (J k d (μ - p - 1) x)
      = Vop k d e μ x
        + (if μ - 1 = 0 then (((μ - p - 1 : ℤ) : ℂ) * k * kappa d e) • (LinearMap.id : End ℂ (WakModule k)) else 0) x := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← LinearMap.sub_apply, band_bracket,
      LinearMap.add_apply]
  -- the central term vanishes on the band
  have hcen : (0 ≤ p ∧ ¬ μ ≤ p) ∨ (¬ 0 ≤ p ∧ μ ≤ p) →
      (if μ - 1 = 0 then (((μ - p - 1 : ℤ) : ℂ) * k * kappa d e) • (LinearMap.id : End ℂ (WakModule k)) else 0) x
        = (0 : WakModule k) := by
    intro hb
    by_cases hμ : μ - 1 = 0
    · rw [if_pos hμ, show (μ - p - 1 : ℤ) = 0 from by omega]; simp
    · rw [if_neg hμ]; simp
  simp only [bilinSummand]
  rw [show (μ - (μ - p - 1) - 1 : ℤ) = p from by ring]
  by_cases h0 : 0 ≤ p <;> by_cases hμp : μ ≤ p
  · -- both: w = 0
    simp only [if_pos h0, if_pos hμp, if_neg (show ¬ (0 : ℤ) ≤ μ - p - 1 from by omega)]
    simp
  · -- 0≤p, ¬μ≤p : band, w = 1
    simp only [if_pos h0, if_neg hμp, if_pos (show (0 : ℤ) ≤ μ - p - 1 from by omega)]
    rw [hPQ, hcen (Or.inl ⟨h0, hμp⟩), add_zero]; simp
  · -- ¬0≤p, μ≤p : band, w = -1
    simp only [if_neg h0, if_pos hμp, if_neg (show ¬ (0 : ℤ) ≤ μ - p - 1 from by omega)]
    rw [show J k e p (J k d (μ - p - 1) x) - J k d (μ - p - 1) (J k e p x)
        = -(J k d (μ - p - 1) (J k e p x) - J k e p (J k d (μ - p - 1) x)) from by abel,
      hPQ, hcen (Or.inr ⟨h0, hμp⟩), add_zero]
    simp
  · -- neither: w = 0
    simp only [if_neg h0, if_neg hμp, if_pos (show (0 : ℤ) ≤ μ - p - 1 from by omega)]
    simp

/-! ## The signed band count `∑ᶠ_p w_μ(p) • v = μ • v` -/

/-- The signed band indicator `w_μ(p) = [0≤p] - [μ≤p]`. -/
def bandInd (μ p : ℤ) : ℤ := (if 0 ≤ p then 1 else 0) - (if μ ≤ p then 1 else 0)

/-- `w_μ • v` has finite support in `p` (the band `[min 0 μ, max 0 μ)`). -/
theorem bandInd_support_finite (μ : ℤ) {M : Type*} [AddCommGroup M] (v : M) :
    (Function.support (fun p : ℤ => bandInd μ p • v)).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (min 0 μ) (max 0 μ))
  intro p hp
  rw [Function.mem_support] at hp
  rw [Set.mem_Icc]
  by_contra hc
  push_neg at hc
  apply hp
  rw [bandInd]
  by_cases hle : p < min 0 μ
  · rw [if_neg (by omega), if_neg (by omega), sub_zero, zero_smul]
  · have h2 : max 0 μ < p := hc (by omega)
    rw [if_pos (by omega), if_pos (by omega), sub_self, zero_smul]

/-- `w_ν(p) - w_{ν-1}(p)` is the single-point indicator at `ν-1`. -/
theorem bandInd_sub_succ (ν p : ℤ) :
    bandInd ν p - bandInd (ν - 1) p = (if p = ν - 1 then (1 : ℤ) else 0) := by
  rw [bandInd, bandInd]
  by_cases hpe : p = ν - 1
  · subst hpe
    rw [if_neg (by omega : ¬ ν ≤ ν - 1), if_pos (by omega : ν - 1 ≤ ν - 1), if_pos rfl]; ring
  · rw [if_neg hpe]
    by_cases hle : ν ≤ p
    · rw [if_pos hle, if_pos (by omega : ν - 1 ≤ p)]; ring
    · rw [if_neg hle, if_neg (by omega : ¬ ν - 1 ≤ p)]; ring

/-- The band-count recursion `∑ᶠ w_ν • v = ∑ᶠ w_{ν-1} • v + v`. -/
theorem bandSmul_step (k : ℂ) (ν : ℤ) (v : WakModule k) :
    (∑ᶠ p : ℤ, bandInd ν p • v) = (∑ᶠ p : ℤ, bandInd (ν - 1) p • v) + v := by
  have hs : ∀ p : ℤ, bandInd ν p • v - bandInd (ν - 1) p • v
      = (if p = ν - 1 then (1 : ℤ) else 0) • v := by
    intro p; rw [← sub_smul, bandInd_sub_succ]
  have hd : (∑ᶠ p : ℤ, bandInd ν p • v) - (∑ᶠ p : ℤ, bandInd (ν - 1) p • v) = v := by
    rw [← finsum_sub_distrib (bandInd_support_finite ν v) (bandInd_support_finite (ν - 1) v),
      finsum_congr hs]
    rw [finsum_eq_finsetSum_of_support_subset
      (fun p => (if p = ν - 1 then (1 : ℤ) else 0) • v) (s := {ν - 1}) (by
        intro p hp
        rw [Function.mem_support] at hp
        simp only [Finset.coe_singleton, Set.mem_singleton_iff]
        by_contra hne
        exact hp (by rw [if_neg hne, zero_smul]))]
    rw [Finset.sum_singleton, if_pos rfl, one_smul]
  exact sub_eq_iff_eq_add'.mp hd

/-- **The signed band count**: `∑ᶠ_p w_μ(p) • v = μ • v` (finite band of width `μ`). -/
theorem bandSmul (k : ℂ) (μ : ℤ) (v : WakModule k) :
    (∑ᶠ p : ℤ, bandInd μ p • v) = μ • v := by
  induction μ using Int.induction_on with
  | zero =>
      have h0 : ∀ p : ℤ, bandInd 0 p • v = 0 := fun p => by rw [bandInd, sub_self, zero_smul]
      rw [finsum_congr h0, finsum_zero, zero_smul]
  | succ i ih =>
      rw [bandSmul_step k (↑i + 1) v, show ((↑i : ℤ) + 1) - 1 = ↑i from by ring, ih,
        add_smul, one_smul]
  | pred i ih =>
      have hstep := bandSmul_step k (-↑i) v
      rw [ih] at hstep
      rw [eq_sub_of_add_eq hstep.symm, sub_smul, one_smul]

/-! ## The flip-band telescoping theorem -/

/-- **The flip-band telescoping** (the crux): `bilin d e μ x - bilin e d μ x = μ • Vop x`,
i.e. `μ • ∑_{e'} f(d,e,e') J^{e'}_{μ-1} x`. -/
theorem bilin_antisymm (k : ℂ) (d e : Fin 3) (μ : ℤ) (x : WakModule k) :
    bilin k d e μ x - bilin k e d μ x = (μ : ℂ) • (Vop k d e μ x) := by
  rw [bilin, bilin_eflip]
  have hfin2 : (Function.support (fun p : ℤ => bilinSummand k e d μ (μ - p - 1) x)).Finite := by
    have heq : (Function.support (fun p : ℤ => bilinSummand k e d μ (μ - p - 1) x))
        = (flipMuEquiv μ) ⁻¹' (Function.support (fun q : ℤ => bilinSummand k e d μ q x)) := by
      ext p; simp only [Function.mem_support, Set.mem_preimage, flipMuEquiv_apply]
    rw [heq]
    exact (bilinSummand_support_finite k e d μ x).preimage ((flipMuEquiv μ).injective.injOn)
  rw [← finsum_sub_distrib (bilinSummand_support_finite k d e μ x) hfin2,
    finsum_congr (fun p => bilinSummand_flip_diff k d e μ p x)]
  show (∑ᶠ p : ℤ, bandInd μ p • (Vop k d e μ x)) = (μ : ℂ) • (Vop k d e μ x)
  rw [bandSmul, ← Int.cast_smul_eq_zsmul ℂ μ]

/-! ## The structPart decomposition into `bilin` and the contraction -/

/-- The second-piece summand has finite support in `p`. -/
theorem bilin2Summand_support_finite (k : ℂ) (e d : Fin 3) (μ : ℤ) (x : WakModule k) :
    (Function.support (fun p : ℤ => bilin2Summand k e d μ p x)).Finite := by
  obtain ⟨Bd, hBd⟩ := J_regularity k d x
  obtain ⟨Be, hBe⟩ := J_regularity k e x
  apply Set.Finite.subset (Set.finite_Icc (min 0 (-Be)) (max (Bd - μ) (-1)))
  intro p hp
  rw [Function.mem_support, bilin2Summand] at hp
  rw [Set.mem_Icc]
  by_cases hpp : 0 ≤ p
  · rw [if_pos hpp] at hp
    have hne : J k d (μ + p) x ≠ 0 := fun h => hp (by rw [h, map_zero])
    have hb : μ + p < Bd := by by_contra hc; push_neg at hc; exact hne (hBd _ hc)
    exact ⟨le_trans (min_le_left _ _) hpp, le_trans (by omega) (le_max_left _ _)⟩
  · rw [if_neg hpp] at hp
    push_neg at hpp
    have hne : J k e (-p - 1) x ≠ 0 := fun h => hp (by rw [h, map_zero])
    have hb : -p - 1 < Be := by by_contra hc; push_neg at hc; exact hne (hBe _ hc)
    exact ⟨le_trans (min_le_right _ _) (by omega), le_trans (by omega : p ≤ -1) (le_max_right _ _)⟩

/-- **The per-`p` structPart decomposition**: `structPart` regroups by structure constant into
the two `bilin` summands. -/
theorem structPart_eq (k : ℂ) (c aa bb : Fin 3) (μ p : ℤ) (x : WakModule k) :
    structPart k c aa bb μ p x
      = (∑ d, fabc c aa d • bilinSummand k d bb μ p x)
        + (∑ d, fabc c bb d • bilin2Summand k aa d μ p x) := by
  rw [structPart, structOp, show (μ + (-p - 1) : ℤ) = μ - p - 1 from by ring]
  by_cases hp : 0 ≤ p
  · rw [if_pos hp]
    simp only [bilinSummand, bilin2Summand, if_pos hp, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul]
  · rw [if_neg hp]
    simp only [bilinSummand, bilin2Summand, if_neg hp, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul]
    rw [add_comm]

/-- **The summed structPart**: `∑ᶠ_p structPart = ∑_d f(c,aa,d) bilin(d,bb) + ∑_d f(c,bb,d) bilin(d,aa)`. -/
theorem structPart_finsum (k : ℂ) (c aa bb : Fin 3) (μ : ℤ) (x : WakModule k) :
    (∑ᶠ p : ℤ, structPart k c aa bb μ p x)
      = (∑ d, fabc c aa d • bilin k d bb μ x) + (∑ d, fabc c bb d • bilin k d aa μ x) := by
  have hf1 : ∀ d : Fin 3,
      (Function.support (fun p : ℤ => fabc c aa d • bilinSummand k d bb μ p x)).Finite :=
    fun d => (bilinSummand_support_finite k d bb μ x).subset (fun p hp => by
      rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, smul_zero]))
  have hf2 : ∀ d : Fin 3,
      (Function.support (fun p : ℤ => fabc c bb d • bilin2Summand k aa d μ p x)).Finite :=
    fun d => (bilin2Summand_support_finite k aa d μ x).subset (fun p hp => by
      rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, smul_zero]))
  have hAfin : (Function.support
      (fun p : ℤ => ∑ d, fabc c aa d • bilinSummand k d bb μ p x)).Finite := by
    apply Set.Finite.subset ((Finset.univ : Finset (Fin 3)).finite_toSet.biUnion (fun d _ => hf1 d))
    intro p hp; rw [Function.mem_support] at hp
    simp only [Set.mem_iUnion]
    by_contra hcon; push_neg at hcon; apply hp
    refine Finset.sum_eq_zero fun d _ => ?_
    have := hcon d (Finset.mem_coe.mpr (Finset.mem_univ d))
    rwa [Function.mem_support, not_not] at this
  have hBfin : (Function.support
      (fun p : ℤ => ∑ d, fabc c bb d • bilin2Summand k aa d μ p x)).Finite := by
    apply Set.Finite.subset ((Finset.univ : Finset (Fin 3)).finite_toSet.biUnion (fun d _ => hf2 d))
    intro p hp; rw [Function.mem_support] at hp
    simp only [Set.mem_iUnion]
    by_contra hcon; push_neg at hcon; apply hp
    refine Finset.sum_eq_zero fun d _ => ?_
    have := hcon d (Finset.mem_coe.mpr (Finset.mem_univ d))
    rwa [Function.mem_support, not_not] at this
  rw [finsum_congr (fun p => structPart_eq k c aa bb μ p x), finsum_add_distrib hAfin hBfin]
  congr 1
  · rw [← sum_finsum_comm Finset.univ
      (fun d p => fabc c aa d • bilinSummand k d bb μ p x) (fun d _ => hf1 d)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← smul_finsum' (fabc c aa d) (bilinSummand_support_finite k d bb μ x)]
    rfl
  · rw [← sum_finsum_comm Finset.univ
      (fun d p => fabc c bb d • bilin2Summand k aa d μ p x) (fun d _ => hf2 d)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← smul_finsum' (fabc c bb d) (bilin2Summand_support_finite k aa d μ x), bilin2_eq]

/-! ## The structure-constant contraction kernels (Fin 3 bashes) -/

/-- `∑_{aa} κ⁻¹(aa,bb) f(c,aa,d) = -graised(bb,c,d)`. -/
theorem kappaInv_fabc_eq_graised (bb c d : Fin 3) :
    (∑ aa : Fin 3, kappaInv aa bb * fabc c aa d) = - graised bb c d := by
  simp only [graised, Fin.sum_univ_three]
  fin_cases bb <;> fin_cases c <;> fin_cases d <;> norm_num [kappaInv, fabc]

/-- The dual-Coxeter struct double-contraction: `∑_{X,d} graised(X,c,d) f(d,X,e) = -4 δ_{c,e}`. -/
theorem graised_fabc_contract (c e : Fin 3) :
    (∑ X : Fin 3, ∑ d : Fin 3, graised X c d * fabc d X e) = -(if c = e then (4 : ℂ) else 0) := by
  simp only [graised, Fin.sum_univ_three]
  fin_cases c <;> fin_cases e <;> norm_num [kappaInv, fabc]

/-- The `graised`-weighted `Vop` contraction: `∑_{X,d} graised(X,c,d) • (μ • Vop(d,X)) = -4μ • Jᶜ_{μ-1}x`. -/
theorem graisedVop_contract (k : ℂ) (c : Fin 3) (μ : ℤ) (x : WakModule k) :
    (∑ X : Fin 3, ∑ d : Fin 3, graised X c d • ((μ : ℂ) • Vop k d X μ x))
      = (-(4 * μ) : ℂ) • J k c (μ - 1) x := by
  -- each (X,d) term as a scalar combination over e'
  have hterm : ∀ X d : Fin 3, graised X c d • ((μ : ℂ) • Vop k d X μ x)
      = ∑ e' : Fin 3, ((μ : ℂ) * (graised X c d * fabc d X e')) • J k e' (μ - 1) x := by
    intro X d
    rw [Vop, LinearMap.sum_apply, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun e' _ => ?_)
    rw [LinearMap.smul_apply, smul_smul, smul_smul]
    congr 1; ring
  rw [Finset.sum_congr rfl (fun X _ => Finset.sum_congr rfl (fun d _ => hterm X d))]
  -- reorder ∑X∑d∑e' → ∑e'∑X∑d
  rw [Finset.sum_congr rfl (fun X _ => Finset.sum_comm), Finset.sum_comm]
  -- pull the scalar `∑X∑d` out of each e'-term
  rw [show (∑ e' : Fin 3, ∑ X : Fin 3, ∑ d : Fin 3,
        ((μ : ℂ) * (graised X c d * fabc d X e')) • J k e' (μ - 1) x)
      = ∑ e' : Fin 3, ((μ : ℂ) * (∑ X : Fin 3, ∑ d : Fin 3, graised X c d * fabc d X e'))
          • J k e' (μ - 1) x from
    Finset.sum_congr rfl (fun e' _ => by
      rw [Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl (fun X _ => ?_)
      rw [Finset.mul_sum, Finset.sum_smul])]
  -- contract via the dual-Coxeter kernel
  rw [Finset.sum_congr rfl (fun e' _ => by rw [graised_fabc_contract])]
  rw [Finset.sum_eq_single c
    (fun e' _ he' => by rw [if_neg (Ne.symm he'), mul_neg, mul_zero, neg_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ c) h)]
  rw [if_pos rfl]
  congr 1
  push_cast; ring

/-! ## The dual-Coxeter struct residue `struct_residue_value` -/

/-- **The structure-constant residue** (the genuine normal-ordering anomaly):
`∑_{aa,bb} κ⁻¹(aa,bb) • ∑ᶠ_p structPart k c aa bb μ p x = 4μ • Jᶜ_{μ-1} x`. -/
theorem struct_residue_value (k : ℂ) (c : Fin 3) (μ : ℤ) (x : WakModule k) :
    (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb • ∑ᶠ p : ℤ, structPart k c aa bb μ p x)
      = (4 * μ : ℂ) • J k c (μ - 1) x := by
  set Sgr : WakModule k := ∑ X : Fin 3, ∑ d : Fin 3, graised X c d • bilin k d X μ x with hSgr
  -- Step 1: structPart_finsum into each ∑ᶠ, split the `+`
  have hstep1 : (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb • ∑ᶠ p : ℤ, structPart k c aa bb μ p x)
      = (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb •
          ∑ d : Fin 3, fabc c aa d • bilin k d bb μ x)
        + (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb •
          ∑ d : Fin 3, fabc c bb d • bilin k d aa μ x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun aa _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun bb _ => ?_)
    rw [structPart_finsum, smul_add]
  rw [hstep1]
  -- Step 2: T1 = T2 = -Sgr (contract via κ⁻¹ f = -graised)
  have hT1 : (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb •
        ∑ d : Fin 3, fabc c aa d • bilin k d bb μ x) = -Sgr := by
    rw [hSgr, ← Finset.sum_neg_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun bb _ => ?_)
    rw [← Finset.sum_neg_distrib]
    have hdist : ∀ aa : Fin 3, kappaInv aa bb • ∑ d : Fin 3, fabc c aa d • bilin k d bb μ x
        = ∑ d : Fin 3, (kappaInv aa bb * fabc c aa d) • bilin k d bb μ x :=
      fun aa => by rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun d _ => by rw [smul_smul])
    rw [Finset.sum_congr rfl (fun aa _ => hdist aa), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_smul, kappaInv_fabc_eq_graised, neg_smul]
  have hT2 : (∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb •
        ∑ d : Fin 3, fabc c bb d • bilin k d aa μ x) = -Sgr := by
    rw [hSgr, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun aa _ => ?_)
    rw [← Finset.sum_neg_distrib]
    have hdist : ∀ bb : Fin 3, kappaInv aa bb • ∑ d : Fin 3, fabc c bb d • bilin k d aa μ x
        = ∑ d : Fin 3, (kappaInv aa bb * fabc c bb d) • bilin k d aa μ x :=
      fun bb => by rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun d _ => by rw [smul_smul])
    rw [Finset.sum_congr rfl (fun bb _ => hdist bb), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_smul,
      show (∑ bb : Fin 3, kappaInv aa bb * fabc c bb d) = -graised aa c d from by
        rw [← kappaInv_fabc_eq_graised aa c d]
        exact Finset.sum_congr rfl (fun bb _ => by rw [kappaInv_symm aa bb]),
      neg_smul]
  rw [hT1, hT2]
  -- Step 3: -Sgr + -Sgr = 4μ • Jᶜ via the graised/bilin antisymmetrisation
  have hswap : Sgr = -(∑ X : Fin 3, ∑ d : Fin 3, graised X c d • bilin k X d μ x) := by
    rw [hSgr, ← Finset.sum_neg_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun X _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [graised_antisymm d c X, neg_smul]
  have hcontract : Sgr - (∑ X : Fin 3, ∑ d : Fin 3, graised X c d • bilin k X d μ x)
      = (-(4 * μ) : ℂ) • J k c (μ - 1) x := by
    rw [hSgr, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun X _ => (Finset.sum_sub_distrib _ _).symm)]
    rw [Finset.sum_congr rfl (fun X _ => Finset.sum_congr rfl (fun d _ => by
      rw [← smul_sub, bilin_antisymm]))]
    exact graisedVop_contract k c μ x
  have hSgr' : -Sgr = (∑ X : Fin 3, ∑ d : Fin 3, graised X c d • bilin k X d μ x) := by
    rw [hswap, neg_neg]
  rw [show (-Sgr) + (-Sgr) = -(Sgr - (-Sgr)) from by abel, hSgr', hcontract, ← neg_smul, neg_neg]

/-! ## The cascade: `Hbr_collapse → Lcomm_current → Jfield_DCovariant` -/

/-- **The full `Hbr` collapse**: `∑ᶠ_p Hbr = -2μ(k+2) • Jᶜ_{μ-1} x` (struct residue `4μ` +
central residue `2μk`). -/
theorem Hbr_collapse (k : ℂ) (c : Fin 3) (μ : ℤ) (x : WakModule k) :
    (∑ᶠ p : ℤ, Hbr k c μ p x) = (-(2 * (μ : ℂ) * (k + 2))) • J k c (μ - 1) x := by
  have hHbr : ∀ p : ℤ, Hbr k c μ p x = ∑ aa : Fin 3, ∑ bb : Fin 3,
      kappaInv aa bb • (sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x)) := by
    intro p
    rw [Hbr_eq_sugTermJ_bracket]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply]
  rw [finsum_congr hHbr]
  have hfinG : ∀ aa bb : Fin 3, (Function.support (fun p : ℤ =>
      kappaInv aa bb • (sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x)))).Finite :=
    fun aa bb => (pair_bracket_support_finite k aa bb c μ x).subset (fun p hp => by
      rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, smul_zero]))
  have hfinSbb : ∀ aa : Fin 3, (Function.support (fun p : ℤ => ∑ bb : Fin 3,
      kappaInv aa bb • (sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x)))).Finite := by
    intro aa
    apply Set.Finite.subset
      ((Finset.univ : Finset (Fin 3)).finite_toSet.biUnion (fun bb _ => hfinG aa bb))
    intro p hp; rw [Function.mem_support] at hp
    simp only [Set.mem_iUnion]
    by_contra hcon; push_neg at hcon; apply hp
    refine Finset.sum_eq_zero fun bb _ => ?_
    have := hcon bb (Finset.mem_coe.mpr (Finset.mem_univ bb))
    rwa [Function.mem_support, not_not] at this
  have hcomm : (∑ᶠ p : ℤ, ∑ aa : Fin 3, ∑ bb : Fin 3,
        kappaInv aa bb • (sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x)))
      = ∑ aa : Fin 3, ∑ bb : Fin 3, kappaInv aa bb •
          ∑ᶠ p : ℤ, (sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x)) := by
    rw [← sum_finsum_comm Finset.univ
      (fun aa p => ∑ bb : Fin 3,
        kappaInv aa bb • (sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x)))
      (fun aa _ => hfinSbb aa)]
    refine Finset.sum_congr rfl (fun aa _ => ?_)
    rw [← sum_finsum_comm Finset.univ
      (fun bb p => kappaInv aa bb •
        (sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x)))
      (fun bb _ => hfinG aa bb)]
    refine Finset.sum_congr rfl (fun bb _ => ?_)
    rw [← smul_finsum' (kappaInv aa bb) (pair_bracket_support_finite k aa bb c μ x)]
  rw [hcomm]
  -- substitute the per-pair split, collapse each half
  have hval : ∀ aa bb : Fin 3,
      kappaInv aa bb •
          ∑ᶠ p : ℤ, (sugTermJ k aa bb p (J k c μ x) - J k c μ (sugTermJ k aa bb p x))
      = -(kappaInv aa bb • ∑ᶠ p : ℤ, structPart k c aa bb μ p x)
        + -(kappaInv aa bb • ∑ᶠ p : ℤ, centralPart k c aa bb μ p x) :=
    fun aa bb => by rw [inner_finsum_split, smul_neg, smul_add, neg_add]
  rw [Finset.sum_congr rfl (fun aa _ => Finset.sum_congr rfl (fun bb _ => hval aa bb))]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [struct_residue_value, central_residue_raw]
  module

/-- **The Sugawara current covariance**, vector form: `[L₋₁, Jᶜ_μ] x = -μ • Jᶜ_{μ-1} x`
(needs the non-critical level `k + 2 ≠ 0`; `c₀ = (2(k+2))⁻¹` cancels the `2(k+2)` denominator). -/
theorem Lcomm_current (k : ℂ) (hk : k + 2 ≠ 0) (c : Fin 3) (μ : ℤ) (x : WakModule k) :
    (Ltrans k * J k c μ - J k c μ * Ltrans k) x = ((-μ : ℤ) : ℂ) • J k c (μ - 1) x := by
  rw [Lcomm_eq_finsum_Hbr, Hbr_collapse, smul_smul]
  congr 1
  simp only [c0, dualCoxeter]
  have h2 : (2 : ℂ) * (k + 2) ≠ 0 := mul_ne_zero two_ne_zero hk
  field_simp
  push_cast
  ring

/-- **The Sugawara current covariance** (the gate `hJ`): `DCovariant (Ltrans k) (Jfield k a)`
for every colour `a` (at non-critical level `k + 2 ≠ 0`). -/
theorem Jfield_DCovariant (k : ℂ) (hk : k + 2 ≠ 0) (a : Fin 3) :
    Reconstruction.DCovariant (Ltrans k) (Jfield k a) := by
  intro m
  apply LinearMap.ext; intro x
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Jfield_apply, Jfield_apply]
  have h := Lcomm_current k hk a (-m - 1) x
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    show (-m - 1 - 1 : ℤ) = -(m + 1) - 1 from by ring] at h
  rw [h, ← Int.cast_smul_eq_zsmul ℂ (m + 1), LinearMap.smul_apply]
  congr 1
  push_cast; ring

end VOA.AffineVOA.SugawaraCov
