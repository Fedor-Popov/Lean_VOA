/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkDiamond
import VOA.Classification.COne.SerreStarkSturm
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Serre–Stark, stage S2-4b: decomposition by characters, and Theorem A per character

* `IsThetaTypeFormChar N χ f`: Serre–Stark's `M_{1/2}(N, χ)`, cross-multiplied:
  `f(γτ) θ(τ) = χ(d) θ(γτ) f(τ)` for `γ ∈ Γ₀(N)` (their `f(γz) = χ(d) j(γ,z) f(z)`).
* `gammaLift N u ∈ Γ₀(N)` with lower-right entry `≡ u`; `charProj N χ f` the projection
  `φ(N)⁻¹ Σ_u χ(u⁻¹) f ‖ γ_u`; `IsThetaTypeForm.isThetaTypeFormChar_charProj`;
  `IsThetaTypeForm.sum_charProj`: `f = Σ_χ charProj N χ f` on `ℍ`.
* `SerreStarkTheoremAChar`: Theorem A in Serre–Stark's own setting (one character at a time);
  `serreStarkTheoremA_of_char : SerreStarkTheoremAChar → SerreStarkTheoremA`, and the converse
  `serreStarkTheoremAChar_of_theoremA` (so the two residuals are equivalent).
-/

open Complex Filter Topology
open scoped MatrixGroups

noncomputable section

namespace VOA.Classification.COne

/-! ## The space `M_{1/2}(N, χ)` -/

/-- **θ-type form of level `N` with character `χ`** (Serre–Stark's `M_{1/2}(Γ₀(N), χ)`). -/
structure IsThetaTypeFormChar (N : ℕ) (χ : DirichletCharacter ℂ N) (f : ℂ → ℂ) : Prop where
  thetaType : IsThetaTypeForm N f
  character : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℂ, 0 < τ.im →
    f (mobius γ τ) * thetaRef τ = χ ((γ 1 1 : ℤ) : ZMod N) * thetaRef (mobius γ τ) * f τ

/-! ## Lifts of units to `Γ₀(N)` -/

theorem exists_Gamma0_lift (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N ∧ ((γ 1 1 : ℤ) : ZMod N) = u := by
  set d : ℕ := (u : ZMod N).val
  have hcop : IsCoprime (N : ℤ) (d : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u).symm
  obtain ⟨x, y, hxy⟩ := hcop
  refine ⟨⟨!![y, -x; (N : ℤ), (d : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hxy
  · rw [CongruenceSubgroup.Gamma0_mem]; simp
  · simp [d]

/-- A chosen lift `γ_u ∈ Γ₀(N)` of `u ∈ (ℤ/N)ˣ`. -/
def gammaLift (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) : SL(2, ℤ) := (exists_Gamma0_lift N u).choose

theorem gammaLift_mem (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    gammaLift N u ∈ CongruenceSubgroup.Gamma0 N :=
  (exists_Gamma0_lift N u).choose_spec.1

theorem gammaLift_d (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    ((gammaLift N u 1 1 : ℤ) : ZMod N) = u :=
  (exists_Gamma0_lift N u).choose_spec.2

/-- The lower-right entry of a `Γ₀(N)` matrix is a unit mod `N`. -/
theorem isUnit_d_of_mem_Gamma0 {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
  have hdet : ((γ.1.det : ℤ) : ZMod N) = 1 := by simp
  rw [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_mul,
    CongruenceSubgroup.Gamma0_mem.1 hγ, mul_zero, sub_zero] at hdet
  exact IsUnit.of_mul_eq_one_right _ hdet

/-- `Γ₀(N)` matrices with the same `d mod N` differ by `Γ₁(N)`. -/
theorem mul_inv_mem_Gamma1 {N : ℕ} {γ γ' : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (hγ' : γ' ∈ CongruenceSubgroup.Gamma0 N)
    (hd : ((γ 1 1 : ℤ) : ZMod N) = ((γ' 1 1 : ℤ) : ZMod N)) :
    γ' * γ⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  set g : CongruenceSubgroup.Gamma0 N := ⟨γ, hγ⟩
  set g' : CongruenceSubgroup.Gamma0 N := ⟨γ', hγ'⟩
  have hgi : CongruenceSubgroup.Gamma0Map N g * CongruenceSubgroup.Gamma0Map N g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hk : g' * g⁻¹ ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_mem', map_mul]
    have : CongruenceSubgroup.Gamma0Map N g' = CongruenceSubgroup.Gamma0Map N g := hd.symm
    rw [this, hgi]
  rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem] at hk
  rw [CongruenceSubgroup.Gamma1_mem]
  exact hk

namespace IsThetaTypeForm

variable {N : ℕ} {f : ℂ → ℂ}

/-- The diamond action depends only on `d mod N`. -/
theorem thetaSlash_congr (hf : IsThetaTypeForm N f) {γ γ' : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (hγ' : γ' ∈ CongruenceSubgroup.Gamma0 N)
    (hd : ((γ 1 1 : ℤ) : ZMod N) = ((γ' 1 1 : ℤ) : ZMod N)) {τ : ℂ} (hτ : 0 < τ.im) :
    VOA.Classification.COne.thetaSlash γ' f τ = VOA.Classification.COne.thetaSlash γ f τ := by
  have hδ := mul_inv_mem_Gamma1 hγ hγ' hd
  have e : γ' = (γ' * γ⁻¹) * γ := by rw [inv_mul_cancel_right]
  rw [e, ← thetaSlash_mul _ _ _ hτ]
  change (VOA.Classification.COne.thetaSlash (γ' * γ⁻¹) f) (mobius γ τ) * thetaRef τ /
    thetaRef (mobius γ τ) = _
  rw [hf.thetaSlash_of_mem_Gamma1 hδ (im_mobius_pos γ hτ)]
  rfl

end IsThetaTypeForm

/-! ## The character projections -/

theorem thetaSlash_add (γ : SL(2, ℤ)) (f g : ℂ → ℂ) :
    thetaSlash γ (f + g) = thetaSlash γ f + thetaSlash γ g := by
  funext τ; simp only [thetaSlash, Pi.add_apply]; ring

theorem thetaSlash_smul (γ : SL(2, ℤ)) (c : ℂ) (f : ℂ → ℂ) :
    thetaSlash γ (c • f) = c • thetaSlash γ f := by
  funext τ; simp only [thetaSlash, Pi.smul_apply, smul_eq_mul]; ring

theorem thetaSlash_sum {ι : Type*} (s : Finset ι) (γ : SL(2, ℤ)) (f : ι → ℂ → ℂ) :
    thetaSlash γ (∑ i ∈ s, f i) = ∑ i ∈ s, thetaSlash γ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => funext τ; simp [thetaSlash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, thetaSlash_add, ih]

/-- `charProj N χ f = φ(N)⁻¹ Σ_u χ(u⁻¹) f ‖ γ_u`. -/
def charProj (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun τ => (N.totient : ℂ)⁻¹ *
    ∑ u : (ZMod N)ˣ, χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * thetaSlash (gammaLift N u) f τ

theorem charProj_eq (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (f : ℂ → ℂ) :
    charProj N χ f = ((N.totient : ℂ)⁻¹) •
      ∑ u : (ZMod N)ˣ, χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) • thetaSlash (gammaLift N u) f := by
  funext τ
  simp [charProj, Finset.sum_apply]

namespace IsThetaTypeForm

variable {N : ℕ} [NeZero N] {f : ℂ → ℂ}

theorem charProj_isThetaType (h4 : 4 ∣ N) (hf : IsThetaTypeForm N f)
    (χ : DirichletCharacter ℂ N) : IsThetaTypeForm N (charProj N χ f) := by
  rw [charProj_eq]
  exact (Submodule.sum_mem (IsThetaTypeForm.submodule N) fun u _ =>
    (hf.thetaSlash h4 (gammaLift_mem N u)).smul _).smul _

/-- `f ‖ γ_u ‖ γ = f ‖ γ_{u d_γ}`. -/
theorem thetaSlash_gammaLift (hf : IsThetaTypeForm N f) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (u w : (ZMod N)ˣ)
    (hw : ((w : (ZMod N)ˣ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N)) {τ : ℂ} (hτ : 0 < τ.im) :
    VOA.Classification.COne.thetaSlash γ
        (VOA.Classification.COne.thetaSlash (gammaLift N u) f) τ =
      VOA.Classification.COne.thetaSlash (gammaLift N (u * w)) f τ := by
  rw [thetaSlash_mul _ _ _ hτ]
  refine (hf.thetaSlash_congr (mul_mem (gammaLift_mem N u) hγ) (gammaLift_mem N (u * w)) ?_
    hτ).symm
  have h10 := CongruenceSubgroup.Gamma0_mem.1 (gammaLift_mem N u)
  have hmul : (((gammaLift N u * γ) 1 1 : ℤ) : ZMod N) =
      ((gammaLift N u 1 1 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h10, zero_mul, zero_add]
  rw [hmul, gammaLift_d, gammaLift_d, ← hw, Units.val_mul]

/-- **Character law of the projection.** -/
theorem charProj_character (hf : IsThetaTypeForm N f) (χ : DirichletCharacter ℂ N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) {τ : ℂ} (hτ : 0 < τ.im) :
    VOA.Classification.COne.thetaSlash γ (charProj N χ f) τ =
      χ ((γ 1 1 : ℤ) : ZMod N) * charProj N χ f τ := by
  obtain ⟨w, hw⟩ := isUnit_d_of_mem_Gamma0 hγ
  have h1 : VOA.Classification.COne.thetaSlash γ (charProj N χ f) τ =
      (N.totient : ℂ)⁻¹ * ∑ u : (ZMod N)ˣ, χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) *
        VOA.Classification.COne.thetaSlash (gammaLift N (u * w)) f τ := by
    have e : ∀ u : (ZMod N)ˣ, VOA.Classification.COne.thetaSlash (gammaLift N (u * w)) f τ =
        VOA.Classification.COne.thetaSlash (gammaLift N u) f (mobius γ τ) * thetaRef τ /
          thetaRef (mobius γ τ) := fun u => (hf.thetaSlash_gammaLift hγ u w hw hτ).symm
    simp_rw [e]
    change charProj N χ f (mobius γ τ) * thetaRef τ / thetaRef (mobius γ τ) = _
    simp only [charProj]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [h1]
  have hH : ∀ u : (ZMod N)ˣ, χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) *
      VOA.Classification.COne.thetaSlash (gammaLift N (u * w)) f τ =
      (fun v : (ZMod N)ˣ => χ (((w * v⁻¹ : (ZMod N)ˣ)) : ZMod N) *
        VOA.Classification.COne.thetaSlash (gammaLift N v) f τ) (u * w) := by
    intro u
    simp only
    congr 3
    group
  simp_rw [hH]
  have hre := Equiv.sum_comp (Equiv.mulRight w) (fun v : (ZMod N)ˣ =>
    χ (((w * v⁻¹ : (ZMod N)ˣ)) : ZMod N) * VOA.Classification.COne.thetaSlash (gammaLift N v) f τ)
  simp only [Equiv.coe_mulRight] at hre
  rw [hre]
  simp only [charProj, Units.val_mul, map_mul, ← hw]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- `charProj N χ f ∈ M_{1/2}(N, χ)`. -/
theorem isThetaTypeFormChar_charProj (h4 : 4 ∣ N) (hf : IsThetaTypeForm N f)
    (χ : DirichletCharacter ℂ N) : IsThetaTypeFormChar N χ (charProj N χ f) where
  thetaType := hf.charProj_isThetaType h4 χ
  character γ hγ τ hτ := by
    have h := hf.charProj_character χ hγ hτ
    have hθ := thetaRef_ne_zero_of_im_pos (im_mobius_pos γ hτ)
    simp only [VOA.Classification.COne.thetaSlash] at h
    rw [div_eq_iff hθ] at h
    rw [h]
    ring

/-- **Decomposition.** `f = Σ_χ charProj N χ f` on `ℍ`. -/
theorem sum_charProj (hf : IsThetaTypeForm N f) {τ : ℂ} (hτ : 0 < τ.im) :
    ∑ χ : DirichletCharacter ℂ N, charProj N χ f τ = f τ := by
  haveI : NeZero ((Monoid.exponent (ZMod N)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.2 (Monoid.exponent_ne_zero_of_finite)⟩
  have hsum : ∀ u : (ZMod N)ˣ, ∑ χ : DirichletCharacter ℂ N, χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) =
      if u = 1 then (N.totient : ℂ) else 0 := by
    intro u
    rw [DirichletCharacter.sum_characters_eq]
    congr 1
    simp only [Units.val_eq_one, inv_eq_one]
  have e1 : ∑ χ : DirichletCharacter ℂ N, charProj N χ f τ =
      (N.totient : ℂ)⁻¹ * ∑ u : (ZMod N)ˣ,
        (∑ χ : DirichletCharacter ℂ N, χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N)) *
          VOA.Classification.COne.thetaSlash (gammaLift N u) f τ := by
    simp only [charProj]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  rw [e1]
  simp_rw [hsum, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (1 : (ZMod N)ˣ), if_pos (Finset.mem_univ _)]
  have hφ : (N.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.totient_pos.2 (NeZero.pos N)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hφ, one_mul]
  have h1 : gammaLift N 1 ∈ CongruenceSubgroup.Gamma1 N := by
    have := mul_inv_mem_Gamma1 (one_mem _) (gammaLift_mem N 1)
      (by rw [gammaLift_d]; simp)
    simpa using this
  exact hf.thetaSlash_of_mem_Gamma1 h1 hτ

end IsThetaTypeForm

/-! ## Theorem A, one character at a time -/

/-- The set of Serre–Stark's spanning functions `θ_{ψ,t}` of level `N` (restricted to `ℍ`). -/
def charThetaSet (N : ℕ) : Set (UpperHalfPlane → ℂ) :=
  {g | ∃ (r t : ℕ) (ψ : DirichletCharacter ℂ r), ψ.IsPrimitive ∧ ψ.Even ∧ 1 ≤ t ∧
    4 * t * r ^ 2 ∣ N ∧ g = restrictUpper (charTheta r ψ t)}

/-- **Serre–Stark Theorem A, per character.** For `4 ∣ N` and a Dirichlet character `χ` mod `N`,
every `f ∈ M_{1/2}(Γ₀(N), χ)` is a finite combination of the `θ_{ψ,t}` with `ψ` even primitive
of conductor `r` and `4 r² t ∣ N`.

*Source.* Serre–Stark, LNM 627 (1977), Theorem A: the `θ_{ψ,t}` with `(ψ, t) ∈ Ω(N, χ)` form a
basis of `M_{1/2}(N, χ)`. (Only the spanning half is asserted, and the spanning set is allowed to
be the larger family `4 r² t ∣ N`; both are implied by the published statement.) This is
Serre–Stark's own setting; `serreStarkTheoremA_of_char` derives the `Γ₁(N)` form. -/
def SerreStarkTheoremAChar : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : ℂ → ℂ), 0 < N → 4 ∣ N →
    IsThetaTypeFormChar N χ f → restrictUpper f ∈ Submodule.span ℂ (charThetaSet N)

theorem exists_charTheta_of_mem_span {N : ℕ} {f : ℂ → ℂ}
    (h : restrictUpper f ∈ Submodule.span ℂ (charThetaSet N)) :
    ∃ (m : ℕ) (r t : Fin m → ℕ) (ψ : ∀ i, DirichletCharacter ℂ (r i)) (c : Fin m → ℂ),
      (∀ i, (ψ i).IsPrimitive ∧ (ψ i).Even ∧ 1 ≤ t i ∧ 4 * t i * r i ^ 2 ∣ N) ∧
      ∀ τ : ℂ, 0 < τ.im → f τ = ∑ i, c i * charTheta (r i) (ψ i) (t i) τ := by
  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 h
  choose r t ψ hprim heven ht hdiv hgeq using fun i => (g i).2
  refine ⟨m, r, t, ψ, c, fun i => ⟨hprim i, heven i, ht i, hdiv i⟩, fun τ hτ => ?_⟩
  have := congrFun hg ⟨τ, hτ⟩
  rw [restrictUpper_apply] at this
  rw [← this, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, hgeq i, smul_eq_mul, restrictUpper_apply]

/-- **Reduction.** Theorem A per character implies Theorem A on `Γ₁(N)`. -/
theorem serreStarkTheoremA_of_char (hA : SerreStarkTheoremAChar) : SerreStarkTheoremA := by
  intro N f hN h4 hf
  haveI : NeZero N := ⟨hN.ne'⟩
  apply exists_charTheta_of_mem_span
  have hsplit : restrictUpper f =
      ∑ χ : DirichletCharacter ℂ N, restrictUpper (charProj N χ f) := by
    funext τ
    rw [Finset.sum_apply]
    simp only [restrictUpper_apply]
    exact (hf.sum_charProj τ.2).symm
  rw [hsplit]
  exact Submodule.sum_mem _ fun χ _ =>
    hA N χ _ hN h4 (hf.isThetaTypeFormChar_charProj h4 χ)

/-- Conversely, Theorem A on `Γ₁(N)` gives it per character: the residuals are equivalent. -/
theorem serreStarkTheoremAChar_of_theoremA (hA : SerreStarkTheoremA) : SerreStarkTheoremAChar := by
  intro N χ f hN h4 hf
  obtain ⟨m, r, t, ψ, c, hcond, hfe⟩ := hA N f hN h4 hf.thetaType
  have heq : restrictUpper f = ∑ i, c i • restrictUpper (charTheta (r i) (ψ i) (t i)) := by
    funext τ
    rw [restrictUpper_apply, hfe τ τ.2, Finset.sum_apply]
    rfl
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨r i, t i, ψ i, (hcond i).1, (hcond i).2.1, (hcond i).2.2.1, (hcond i).2.2.2, rfl⟩)

end VOA.Classification.COne
