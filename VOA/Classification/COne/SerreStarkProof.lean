/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkHeckeComm
import VOA.Classification.COne.SerreStarkDim

/-!
# Serre–Stark S3-4: the Hecke algebra on `M_{1/2}(N, χ)` and the reduction of Theorem A

For `24 ∣ N` and a Dirichlet character `χ` mod `N`:

* `mSpace N χ`: `M_{1/2}(N, χ)` as a (finite-dimensional) subspace of functions on `ℍ`;
* `heckeEnd χ h24 P`: Shimura's `T(p²)` as an endomorphism of `mSpace N χ`, for every admissible
  prime `P : HPrime N` (`p` odd, `p ∤ N`), with `q`-expansion `heckeCoeff`;
* `heckeEnd_commute`: the `T(p²)` commute.

The residual (`SerreStarkGenEigen24`): every *generalised* simultaneous eigenvector of the `T(p²)`
lies in the span of the `θ_{ψ,t}`. Then

* `iSerreStark24_of_genEigen : SerreStarkGenEigen24 → ISerreStark24` (simultaneous
  triangularisation of the commuting `T(p²)`, the character decomposition, the dimension bound);
* `genEigen_of_semisimple_of_eigenform`: the residual splits into the Petersson input
  `HeckeSemisimple24` (each `T(p²)` is semisimple) and Serre–Stark's eigenform theorem
  `SerreStarkEigenform24` (every simultaneous `T(p²)`-eigenform is a combination of `θ_{ψ,t}`);
* `genEigen_of_theoremA`, `eigenform_of_theoremA`: both residuals follow from the published
  Theorem A, so nothing stronger than Serre–Stark is assumed.
-/

open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## `M_{1/2}(N, χ)` as a space of functions on `ℍ` -/

theorem IsThetaTypeFormChar.congr' {N : ℕ} {χ : DirichletCharacter ℂ N} {f g : ℂ → ℂ}
    (hf : IsThetaTypeFormChar N χ f) (h : ∀ τ : ℂ, 0 < τ.im → f τ = g τ) :
    IsThetaTypeFormChar N χ g where
  thetaType := hf.thetaType.congr h
  character γ hγ τ hτ := by
    rw [← h τ hτ, ← h _ (im_mobius_pos γ hτ)]; exact hf.character γ hγ τ hτ

theorem isThetaTypeFormChar_zero {N : ℕ} (χ : DirichletCharacter ℂ N) :
    IsThetaTypeFormChar N χ (fun _ => 0) where
  thetaType := IsThetaTypeForm.zero
  character _ _ _ _ := by simp

theorem IsThetaTypeFormChar.add' {N : ℕ} {χ : DirichletCharacter ℂ N} {f g : ℂ → ℂ}
    (hf : IsThetaTypeFormChar N χ f) (hg : IsThetaTypeFormChar N χ g) :
    IsThetaTypeFormChar N χ (f + g) where
  thetaType := hf.thetaType.add hg.thetaType
  character γ hγ τ hτ := by
    simp only [Pi.add_apply]
    linear_combination hf.character γ hγ τ hτ + hg.character γ hγ τ hτ

theorem IsThetaTypeFormChar.smul' {N : ℕ} {χ : DirichletCharacter ℂ N} {f : ℂ → ℂ}
    (hf : IsThetaTypeFormChar N χ f) (c : ℂ) : IsThetaTypeFormChar N χ (c • f) where
  thetaType := hf.thetaType.smul c
  character γ hγ τ hτ := by
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination c * hf.character γ hγ τ hτ

/-- `M_{1/2}(N, χ)`, as functions on `ℍ`. -/
def mSpace (N : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (ℍ → ℂ) where
  carrier := {g | ∃ f, IsThetaTypeFormChar N χ f ∧ restrictUpper f = g}
  zero_mem' := ⟨_, isThetaTypeFormChar_zero χ, by funext τ; rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, IsThetaTypeFormChar.add' hf hg, map_add _ _ _⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl⟩
    exact ⟨c • f, IsThetaTypeFormChar.smul' hf c, map_smul _ _ _⟩

theorem mSpace_le_thetaTypeSpace (N : ℕ) (χ : DirichletCharacter ℂ N) :
    mSpace N χ ≤ thetaTypeSpace N := by
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨f, hf.thetaType, rfl⟩

theorem finiteDimensional_mSpace {N : ℕ} (h4 : 4 ∣ N) [NeZero N] (χ : DirichletCharacter ℂ N) :
    FiniteDimensional ℂ (mSpace N χ) := by
  haveI := finiteDimensional_thetaTypeSpace h4 (N := N)
  exact Submodule.finiteDimensional_of_le (mSpace_le_thetaTypeSpace N χ)

/-- Extension by `0` from `ℍ` to `ℂ`. -/
def extH (g : ℍ → ℂ) : ℂ → ℂ := fun τ => if h : 0 < τ.im then g ⟨τ, h⟩ else 0

theorem extH_apply {g : ℍ → ℂ} {τ : ℂ} (hτ : 0 < τ.im) : extH g τ = g ⟨τ, hτ⟩ := by
  simp [extH, hτ]

theorem restrictUpper_extH (g : ℍ → ℂ) : restrictUpper (extH g) = g := by
  funext τ; rw [restrictUpper_apply, extH_apply τ.2]

theorem extH_of_mem {N : ℕ} {χ : DirichletCharacter ℂ N} {g : ℍ → ℂ} (hg : g ∈ mSpace N χ) :
    IsThetaTypeFormChar N χ (extH g) := by
  obtain ⟨f, hf, rfl⟩ := hg
  exact IsThetaTypeFormChar.congr' hf fun τ hτ => by rw [extH_apply hτ, restrictUpper_apply]

theorem extH_add (g h : ℍ → ℂ) : extH (g + h) = extH g + extH h := by
  funext τ; by_cases hτ : 0 < τ.im <;> simp [extH, hτ]

theorem extH_smul (c : ℂ) (g : ℍ → ℂ) : extH (c • g) = c • extH g := by
  funext τ; by_cases hτ : 0 < τ.im <;> simp [extH, hτ]

/-! ## Hecke operators on `M_{1/2}(N, χ)` -/

/-- The admissible primes: odd and prime to `N`. -/
def HPrime (N : ℕ) := {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p.Coprime N}

theorem heckeT_add {N : ℕ} (χ : DirichletCharacter ℂ N) (p : ℕ) [Fact p.Prime] (f g : ℂ → ℂ) :
    heckeT χ p (f + g) = heckeT χ p f + heckeT χ p g := by
  funext τ
  simp only [heckeT, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem heckeT_smul {N : ℕ} (χ : DirichletCharacter ℂ N) (p : ℕ) [Fact p.Prime] (c : ℂ)
    (f : ℂ → ℂ) : heckeT χ p (c • f) = c • heckeT χ p f := by
  funext τ
  simp only [heckeT, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **`T(p²)` as an endomorphism of `M_{1/2}(N, χ)`.** -/
def heckeEnd {N : ℕ} (χ : DirichletCharacter ℂ N) (h24 : 24 ∣ N) (P : HPrime N) :
    Module.End ℂ (mSpace N χ) :=
  haveI : Fact P.1.Prime := ⟨P.2.1⟩
  { toFun := fun g => ⟨restrictUpper (heckeT χ P.1 (extH (g : ℍ → ℂ))),
      ⟨_, isThetaTypeFormChar_heckeT χ P.2.2.1 h24 P.2.2.2 (extH_of_mem g.2), rfl⟩⟩
    map_add' := fun g h => by
      apply Subtype.ext
      simp only [Submodule.coe_add, extH_add, heckeT_add, map_add]
    map_smul' := fun c g => by
      apply Subtype.ext
      simp only [Submodule.coe_smul, extH_smul, heckeT_smul, map_smul, RingHom.id_apply] }

theorem heckeEnd_apply {N : ℕ} (χ : DirichletCharacter ℂ N) (h24 : 24 ∣ N) (P : HPrime N)
    (g : mSpace N χ) :
    ((heckeEnd χ h24 P g : mSpace N χ) : ℍ → ℂ) =
      haveI : Fact P.1.Prime := ⟨P.2.1⟩
      restrictUpper (heckeT χ P.1 (extH (g : ℍ → ℂ))) := rfl

/-- The `q`-expansion coefficients of an element of `M_{1/2}(N, χ)`. -/
def mCoeff {N : ℕ} {χ : DirichletCharacter ℂ N} (g : mSpace N χ) (n : ℕ) : ℂ :=
  thetaTypeCoeff (extH (g : ℍ → ℂ)) n

theorem thetaTypeCoeff_congr {f g : ℂ → ℂ} (h : ∀ τ : ℂ, 0 < τ.im → f τ = g τ) (n : ℕ) :
    thetaTypeCoeff f n = thetaTypeCoeff g n := by
  unfold thetaTypeCoeff
  congr 3
  funext τ
  exact h τ τ.2

theorem mCoeff_heckeEnd {N : ℕ} (χ : DirichletCharacter ℂ N) (h24 : 24 ∣ N) (P : HPrime N)
    (g : mSpace N χ) (n : ℕ) :
    mCoeff (heckeEnd χ h24 P g) n =
      haveI : Fact P.1.Prime := ⟨P.2.1⟩
      heckeCoeff χ P.1 (mCoeff g) n := by
  haveI : Fact P.1.Prime := ⟨P.2.1⟩
  unfold mCoeff
  rw [heckeEnd_apply, thetaTypeCoeff_congr (g := heckeT χ P.1 (extH (g : ℍ → ℂ)))
    (fun τ hτ => by rw [extH_apply hτ, restrictUpper_apply])]
  exact coeff_heckeT χ P.2.2.1 h24 P.2.2.2 (extH_of_mem g.2) n

/-- Elements of `M_{1/2}(N, χ)` are determined by their `q`-expansions. -/
theorem mSpace_ext {N : ℕ} {χ : DirichletCharacter ℂ N} {g h : mSpace N χ}
    (hc : ∀ n, mCoeff g n = mCoeff h n) : g = h := by
  apply Subtype.ext
  funext τ
  have hg : HasSum (fun n : ℕ => mCoeff g n * cexp (2 * Real.pi * I * n * (τ : ℂ)))
      (extH (g : ℍ → ℂ) τ) := (extH_of_mem g.2).thetaType.hasSum_coeff τ.2
  have hh : HasSum (fun n : ℕ => mCoeff h n * cexp (2 * Real.pi * I * n * (τ : ℂ)))
      (extH (h : ℍ → ℂ) τ) := (extH_of_mem h.2).thetaType.hasSum_coeff τ.2
  simp_rw [hc] at hg
  have := hg.unique hh
  rwa [extH_apply τ.2, extH_apply τ.2] at this

/-- **The `T(p²)` commute.** -/
theorem heckeEnd_commute {N : ℕ} (χ : DirichletCharacter ℂ N) (h24 : 24 ∣ N) (P Q : HPrime N) :
    Commute (heckeEnd χ h24 P) (heckeEnd χ h24 Q) := by
  by_cases hPQ : P.1 = Q.1
  · have : P = Q := Subtype.ext hPQ
    subst this; exact Commute.refl _
  haveI : Fact P.1.Prime := ⟨P.2.1⟩
  haveI : Fact Q.1.Prime := ⟨Q.2.1⟩
  refine LinearMap.ext fun g => mSpace_ext fun n => ?_
  simp only [Module.End.mul_apply, mCoeff_heckeEnd]
  have e : (heckeCoeff χ P.1 fun n => heckeCoeff χ Q.1 (mCoeff g) n) =
      heckeCoeff χ P.1 (heckeCoeff χ Q.1 (mCoeff g)) := rfl
  have h1 : mCoeff (heckeEnd χ h24 Q g) = heckeCoeff χ Q.1 (mCoeff g) :=
    funext fun m => mCoeff_heckeEnd χ h24 Q g m
  have h2 : mCoeff (heckeEnd χ h24 P g) = heckeCoeff χ P.1 (mCoeff g) :=
    funext fun m => mCoeff_heckeEnd χ h24 P g m
  rw [h1, h2]
  exact heckeCoeff_comm χ hPQ (mCoeff g) n


/-! ## The residuals -/

/-- **Residual (generalised eigenvectors).** For `24 ∣ N`, every generalised simultaneous
eigenvector of the Hecke operators `T(p²)` (`p` odd, `p ∤ N`) on `M_{1/2}(N, χ)` is a finite
combination of Serre–Stark's `θ_{ψ,t}` (`ψ` even primitive of conductor `r`, `4 r² t ∣ N`).

TRUE: by Serre–Stark Theorem A (LNM 627, 1977) every element of `M_{1/2}(N, χ)` is such a
combination (`genEigen_of_theoremA`). -/
def SerreStarkGenEigen24 : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (μ : HPrime N → ℂ),
    ∀ g ∈ ⨅ P, (heckeEnd χ h24 P).maxGenEigenspace (μ P),
      ((g : mSpace N χ) : ℍ → ℂ) ∈ Submodule.span ℂ (charThetaSet N)

/-- **Residual (Petersson).** Each `T(p²)` is a semisimple endomorphism of `M_{1/2}(N, χ)`.

TRUE: the Petersson inner product converges on `M_{1/2}` (weight `½ < 1`), and `χ(p)⁻¹ T(p²)` is
hermitian for it (Shimura, Ann. of Math. 97 (1973), Thm 1.7 and §5; Serre–Stark §3). -/
def HeckeSemisimple24 : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (P : HPrime N),
    (heckeEnd χ h24 P).IsSemisimple

/-- **Residual (Serre–Stark's eigenform theorem).** Every simultaneous eigenform of the
`T(p²)` (`p` odd, `p ∤ N`) in `M_{1/2}(N, χ)` is a finite combination of the `θ_{ψ,t}`.

TRUE: Serre–Stark (LNM 627) Theorems 1–2 and the proof of Theorem A (the eigenvalue lemma
`c_p = ψ(p)(1 + p⁻¹)` for `a(m) ≠ 0`, support on `t·□`, newform theory and the functional
equation of `Σ a(n²) n^{-s}`); also implied by Theorem A (`eigenform_of_theoremA`). -/
def SerreStarkEigenform24 : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (h24 : 24 ∣ N) (χ : DirichletCharacter ℂ N) (g : mSpace N χ),
    (∀ P : HPrime N, ∃ c : ℂ, heckeEnd χ h24 P g = c • g) →
      ((g : mSpace N χ) : ℍ → ℂ) ∈ Submodule.span ℂ (charThetaSet N)

/-! ## Glue -/

/-- The Petersson input and the eigenform theorem give the generalised-eigenvector residual. -/
theorem genEigen_of_semisimple_of_eigenform (hS : HeckeSemisimple24)
    (hE : SerreStarkEigenform24) : SerreStarkGenEigen24 := by
  intro N hN h24 χ μ g hg
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI := finiteDimensional_mSpace ((show 4 ∣ 24 by norm_num).trans h24) χ
  refine hE N hN h24 χ g fun P => ⟨μ P, ?_⟩
  have hgP : g ∈ (heckeEnd χ h24 P).maxGenEigenspace (μ P) := Submodule.mem_iInf _ |>.1 hg P
  have hfs := Module.End.isFinitelySemisimple_iff_isSemisimple.2 (hS N hN h24 χ P)
  rw [hfs.maxGenEigenspace_eq_eigenspace] at hgP
  exact Module.End.mem_eigenspace_iff.1 hgP

/-- **Simultaneous triangularisation.** Under the residual, all of `M_{1/2}(N, χ)` lies in the
span of the `θ_{ψ,t}`. -/
theorem mem_span_of_genEigen (hG : SerreStarkGenEigen24) {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N)
    (χ : DirichletCharacter ℂ N) (g : mSpace N χ) :
    ((g : mSpace N χ) : ℍ → ℂ) ∈ Submodule.span ℂ (charThetaSet N) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI := finiteDimensional_mSpace ((show 4 ∣ 24 by norm_num).trans h24) χ
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun P => heckeEnd χ h24 P) (fun P Q _ => heckeEnd_commute χ h24 P Q)
    (fun P => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hg : g ∈ ⨆ μ : HPrime N → ℂ, ⨅ P, (heckeEnd χ h24 P).maxGenEigenspace (μ P) := by
    rw [htop]; exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun x : mSpace N χ =>
    ((x : mSpace N χ) : ℍ → ℂ) ∈ Submodule.span ℂ (charThetaSet N)) hg ?_ ?_ ?_
  · intro μ x hx
    exact hG N hN h24 χ μ x hx
  · simp
  · intro x y hx hy
    simpa using Submodule.add_mem _ hx hy

/-- Serre–Stark's `θ_{ψ,t}` (with `4 r² t ∣ N`) lie in the span of the `θ_{n₀,r,t}`. -/
theorem span_charThetaSet_le_thetaSpan {N : ℕ} (hN : 0 < N) :
    Submodule.span ℂ (charThetaSet N) ≤ thetaSpan N := by
  rw [Submodule.span_le]
  rintro _ ⟨r, t, ψ, -, -, ht, hdiv, rfl⟩
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hdiv; simp at hdiv; omega
    · exact h
  have heq : restrictUpper (charTheta r ψ t) = ∑ j ∈ Finset.range r,
      ψ (j : ZMod r) • thetaFn ((j : ℤ), r, t) := by
    funext τ
    rw [restrictUpper_apply, charTheta_eq_sum r hr ψ (by exact_mod_cast ht) τ.2, Finset.sum_apply]
    rfl
  rw [SetLike.mem_coe, heq]
  refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  have hp : ((j : ℤ), r, t) ∈ thetaIndex N := by
    rw [mem_thetaIndex_iff hN]
    exact ⟨by positivity, by simpa using Finset.mem_range.1 hj, hr, ht, hdiv⟩
  exact ⟨⟨_, hp⟩, rfl⟩

/-- Under the residual, `M_{1/2}(Γ₁(N), θ)` is spanned by theta series (`24 ∣ N`). -/
theorem thetaTypeSpace_le_thetaSpan_of_genEigen (hG : SerreStarkGenEigen24) {N : ℕ}
    (hN : 0 < N) (h24 : 24 ∣ N) : thetaTypeSpace N ≤ thetaSpan N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  rintro _ ⟨f, hf, rfl⟩
  refine span_charThetaSet_le_thetaSpan hN ?_
  have hsplit : restrictUpper f = ∑ χ : DirichletCharacter ℂ N, restrictUpper (charProj N χ f) := by
    funext τ
    rw [Finset.sum_apply]
    simp only [restrictUpper_apply]
    exact (hf.sum_charProj τ.2).symm
  rw [hsplit]
  refine Submodule.sum_mem _ fun χ _ => ?_
  have hc := hf.isThetaTypeFormChar_charProj h4 χ
  exact mem_span_of_genEigen hG hN h24 χ ⟨_, _, hc, rfl⟩

/-- The residual gives the dimension bound. -/
theorem dimBound24_of_genEigen (hG : SerreStarkGenEigen24) : SerreStarkDimBound24 := by
  intro N hN h24
  haveI : Module.Finite ℂ (thetaSpan N) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finrank_mono (thetaTypeSpace_le_thetaSpan_of_genEigen hG hN h24)

/-- **Reduction.** The generalised-eigenvector residual gives `ISerreStark` at every level
divisible by `24` — the only levels used by the classification. -/
theorem iSerreStark24_of_genEigen (hG : SerreStarkGenEigen24) : ISerreStark24 :=
  iSerreStark24_of_dimBound (dimBound24_of_genEigen hG)

/-- **Reduction.** Petersson semisimplicity of the `T(p²)` and Serre–Stark's eigenform
theorem give `ISerreStark` at every level divisible by `24`. -/
theorem iSerreStark24_of_semisimple_of_eigenform (hS : HeckeSemisimple24)
    (hE : SerreStarkEigenform24) : ISerreStark24 :=
  iSerreStark24_of_genEigen (genEigen_of_semisimple_of_eigenform hS hE)

/-! ## The residuals are implied by Theorem A -/

theorem mem_span_of_theoremA (hA : SerreStarkTheoremA) {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N)
    (χ : DirichletCharacter ℂ N) (g : mSpace N χ) :
    ((g : mSpace N χ) : ℍ → ℂ) ∈ Submodule.span ℂ (charThetaSet N) := by
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  have := serreStarkTheoremAChar_of_theoremA hA N χ (extH (g : ℍ → ℂ)) hN h4 (extH_of_mem g.2)
  rwa [restrictUpper_extH] at this

/-- The generalised-eigenvector residual is no stronger than Serre–Stark's Theorem A. -/
theorem genEigen_of_theoremA (hA : SerreStarkTheoremA) : SerreStarkGenEigen24 :=
  fun _ hN h24 χ _ g _ => mem_span_of_theoremA hA hN h24 χ g

/-- The eigenform residual is no stronger than Serre–Stark's Theorem A. -/
theorem eigenform_of_theoremA (hA : SerreStarkTheoremA) : SerreStarkEigenform24 :=
  fun _ hN h24 χ g _ => mem_span_of_theoremA hA hN h24 χ g

end SSHecke

end VOA.Classification.COne
