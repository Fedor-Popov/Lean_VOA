/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkUpStable

/-!
# Serre–Stark S5-1b: `U(p²)` on class forms; the coefficient recurrence

For `p ∣ N` (`24 ∣ N`) the operator `U(p²)` (`SerreStarkUpStable.lean`) maps class forms for
`(ψ, t)` (`t` squarefree) to class forms (`isClassForm_upOp`). The class forms of level `N` form a
finite-dimensional space `classSpace N r ψ t` (it sits inside `M_{1/2}(Γ₁(N), θ)`), on which
`U(p²)` is an endomorphism `upEnd`. By Cayley–Hamilton:

`exists_upRecurrence`: there is one monic polynomial `P` of degree `dim (classSpace N r ψ t)`
such that for every class form `f` and every `n`,

`Σ_k P_k a(p^{2k} n) = 0`

(along `p`-powers the coefficients of all class forms satisfy one fixed linear recurrence; in
terms of `A(S) = a(t S²)`, the sequences `k ↦ A(p^k S)` are exponential polynomials whose
exponents are the eigenvalues of `U(p²)` on `classSpace`).
-/

open Complex
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

variable {p : ℕ}

/-! ## Class forms are `U(p²)`-stable -/

theorem dvd_of_sq_dvd_squarefree_mul {t x : ℕ} (hp : p.Prime) (ht : Squarefree t)
    (h : p ^ 2 ∣ t * x ^ 2) : p ∣ x := by
  by_contra hpx
  have hcop : Nat.Coprime (p ^ 2) (x ^ 2) :=
    Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpx)
  have h2 : p ^ 2 ∣ t := hcop.dvd_of_dvd_mul_right h
  have := ht p (by rw [← pow_two]; exact h2)
  exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)

/-- **`U(p²)` maps class forms to class forms** (`p ∣ N`, `24 ∣ N`, `t` squarefree). -/
theorem isClassForm_upOp [hpf : Fact p.Prime] {N r t : ℕ} {ψ : DirichletCharacter ℂ r}
    (hN : 0 < N) (h24 : 24 ∣ N) (hpN : p ∣ N) (ht : Squarefree t) {f : ℂ → ℂ}
    (hf : IsClassForm N r ψ t f) : IsClassForm N r ψ t (upOp p f) := by
  have hp := hpf.out
  have hc := coeff_upOp hN h24 hpN hf.1
  refine ⟨isThetaTypeForm_upOp hN h24 hpN hf.1, fun n hn hne => ?_, fun n v hn hv => ?_⟩
  · rw [hc] at hne
    obtain ⟨x, hx⟩ := hf.2.1 _ (Nat.mul_pos (pow_pos hp.pos 2) hn) hne
    obtain ⟨y, rfl⟩ := dvd_of_sq_dvd_squarefree_mul hp ht ⟨n, hx.symm⟩
    refine ⟨y, ?_⟩
    have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
    have : p ^ 2 * n = p ^ 2 * (t * y ^ 2) := by rw [hx]; ring
    exact Nat.eq_of_mul_eq_mul_left hp2 this
  · rw [hc, hc, show p ^ 2 * (n * v ^ 2) = (p ^ 2 * n) * v ^ 2 by ring]
    exact hf.2.2 _ v (Nat.mul_pos (pow_pos hp.pos 2) hn) hv

/-! ## The space of class forms -/

/-- The class forms for `(ψ, t)` at level `N`, as functions on `ℍ`. -/
def classSpace (N r : ℕ) (ψ : DirichletCharacter ℂ r) (t : ℕ) : Submodule ℂ (ℍ → ℂ) where
  carrier := {g | ∃ f, IsClassForm N r ψ t f ∧ restrictUpper f = g}
  zero_mem' := ⟨_, IsClassForm.zero ψ t, by funext τ; rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + (1 : ℂ) • g, hf.add_smul hg 1, by rw [map_add, map_smul, one_smul]⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl⟩
    refine ⟨(fun _ => 0) + c • f, (IsClassForm.zero ψ t).add_smul hf c, ?_⟩
    rw [map_add, map_smul]
    have : restrictUpper (fun _ : ℂ => (0 : ℂ)) = 0 := by funext τ; rfl
    rw [this, zero_add]

theorem classSpace_le {N r : ℕ} (ψ : DirichletCharacter ℂ r) (t : ℕ) :
    classSpace N r ψ t ≤ thetaTypeSpace N := by
  rintro _ ⟨f, hf, rfl⟩
  exact mem_thetaTypeSpace.2 ⟨f, hf.1, rfl⟩

theorem finiteDimensional_classSpace {N r : ℕ} (h4 : 4 ∣ N) [NeZero N]
    (ψ : DirichletCharacter ℂ r) (t : ℕ) : FiniteDimensional ℂ (classSpace N r ψ t) := by
  haveI := finiteDimensional_thetaTypeSpace h4 (N := N)
  exact Submodule.finiteDimensional_of_le (classSpace_le ψ t)

/-! ## `U(p²)` on functions on `ℍ` -/

/-- `U(p²)` on functions on `ℍ`. -/
def upH (p : ℕ) [hpf : Fact p.Prime] : (ℍ → ℂ) →ₗ[ℂ] (ℍ → ℂ) where
  toFun g τ := 1 / (p : ℂ) ^ 2 * ∑ b : Fin (p ^ 2),
    g ⟨mobZ (cosetMat p (.inl b)) τ, im_mobZ_cosetMat hpf.out.pos _ τ.2⟩
  map_add' g h := by
    funext τ
    simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c g := by
    funext τ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

theorem upH_restrictUpper [Fact p.Prime] (f : ℂ → ℂ) :
    upH p (restrictUpper f) = restrictUpper (upOp p f) := by
  funext τ
  rfl

theorem upH_mem [Fact p.Prime] {N r t : ℕ} {ψ : DirichletCharacter ℂ r} (hN : 0 < N)
    (h24 : 24 ∣ N) (hpN : p ∣ N) (ht : Squarefree t) {g : ℍ → ℂ}
    (hg : g ∈ classSpace N r ψ t) : upH p g ∈ classSpace N r ψ t := by
  obtain ⟨f, hf, rfl⟩ := hg
  exact ⟨upOp p f, isClassForm_upOp hN h24 hpN ht hf, (upH_restrictUpper f).symm⟩

/-- `U(p²)` as an endomorphism of the space of class forms. -/
def upEnd [Fact p.Prime] {N r t : ℕ} (ψ : DirichletCharacter ℂ r) (hN : 0 < N) (h24 : 24 ∣ N)
    (hpN : p ∣ N) (ht : Squarefree t) : Module.End ℂ (classSpace N r ψ t) :=
  (upH p).restrict (fun _ hg => upH_mem hN h24 hpN ht hg)

theorem upEnd_pow_coe [Fact p.Prime] {N r t : ℕ} (ψ : DirichletCharacter ℂ r) (hN : 0 < N)
    (h24 : 24 ∣ N) (hpN : p ∣ N) (ht : Squarefree t) (k : ℕ) (g : classSpace N r ψ t) :
    (((upEnd ψ hN h24 hpN ht ^ k) g : classSpace N r ψ t) : ℍ → ℂ) = (upH p)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply', ← ih]
    rfl

theorem upH_iterate_restrictUpper [Fact p.Prime] (f : ℂ → ℂ) (k : ℕ) :
    (upH p)^[k] (restrictUpper f) = restrictUpper ((upOp p)^[k] f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, upH_restrictUpper, Function.iterate_succ_apply']

/-! ## Coefficients of iterates and of finite combinations -/

theorem isThetaTypeForm_upOp_iterate [Fact p.Prime] {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N)
    (hpN : p ∣ N) {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) (k : ℕ) :
    IsThetaTypeForm N ((upOp p)^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact isThetaTypeForm_upOp hN h24 hpN ih

theorem coeff_upOp_iterate [Fact p.Prime] {N : ℕ} (hN : 0 < N) (h24 : 24 ∣ N) (hpN : p ∣ N)
    {f : ℂ → ℂ} (hf : IsThetaTypeForm N f) (k n : ℕ) :
    thetaTypeCoeff ((upOp p)^[k] f) n = thetaTypeCoeff f (p ^ (2 * k) * n) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', coeff_upOp hN h24 hpN
      (isThetaTypeForm_upOp_iterate hN h24 hpN hf k), ih]
    congr 1
    ring

theorem coeff_finset_sum {N : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℂ) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, IsThetaTypeForm N (f i)) (n : ℕ) :
    thetaTypeCoeff (∑ i ∈ s, c i • f i) n = ∑ i ∈ s, c i * thetaTypeCoeff (f i) n := by
  have hF : IsThetaTypeForm N (∑ i ∈ s, c i • f i) :=
    IsThetaTypeForm.sum s fun i hi => (hf i hi).smul (c i)
  refine hF.coeff_eq_of_hasSum (c := fun n => ∑ i ∈ s, c i * thetaTypeCoeff (f i) n)
    (fun τ hτ => ?_) n
  have H : HasSum (fun m : ℕ => ∑ i ∈ s, c i * thetaTypeCoeff (f i) m *
      cexp (2 * Real.pi * I * m * τ)) (∑ i ∈ s, c i * f i τ) :=
    hasSum_sum fun i hi => (((hf i hi).hasSum_coeff hτ).mul_left (c i)).congr_fun
      fun m => by ring
  have e : (∑ i ∈ s, c i • f i) τ = ∑ i ∈ s, c i * f i τ := by
    simp [Finset.sum_apply]
  rw [e]
  refine H.congr_fun fun m => ?_
  rw [Finset.sum_mul]

theorem coeff_eq_zero_of_eq_zero {f : ℂ → ℂ} (h : ∀ τ : ℂ, 0 < τ.im → f τ = 0) (n : ℕ) :
    thetaTypeCoeff f n = 0 := by
  rw [thetaTypeCoeff_congr (g := fun _ => 0) h]
  exact (IsThetaTypeForm.zero (N := 4)).coeff_eq_of_hasSum (c := fun _ => 0)
    (fun τ _ => by simpa using hasSum_zero) n

/-! ## The recurrence -/

/-- **One recurrence for all class forms.** For `p ∣ N` (`24 ∣ N`, `t` squarefree) there is a
monic polynomial `P` of degree `dim (classSpace N r ψ t)` (the characteristic polynomial of
`U(p²)` on class forms) such that `Σ_k P_k a(p^{2k} n) = 0` for every class form and every `n`. -/
theorem exists_upRecurrence [Fact p.Prime] {N r t : ℕ} (ψ : DirichletCharacter ℂ r)
    (hN : 0 < N) (h24 : 24 ∣ N) (hpN : p ∣ N) (ht : Squarefree t) :
    ∃ P : Polynomial ℂ, P.Monic ∧ P.natDegree = Module.finrank ℂ (classSpace N r ψ t) ∧
      ∀ f, IsClassForm N r ψ t f → ∀ n,
        ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * thetaTypeCoeff f (p ^ (2 * k) * n) =
          0 := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have h4 : 4 ∣ N := (show 4 ∣ 24 by norm_num).trans h24
  haveI := finiteDimensional_classSpace h4 ψ t (N := N)
  set T := upEnd ψ hN h24 hpN ht
  refine ⟨T.charpoly, LinearMap.charpoly_monic T, LinearMap.charpoly_natDegree T,
    fun f hf n => ?_⟩
  have hCH := LinearMap.aeval_self_charpoly T
  set g : classSpace N r ψ t := ⟨restrictUpper f, f, hf, rfl⟩
  have h0 := congrArg (fun F : Module.End ℂ (classSpace N r ψ t) => ((F g : classSpace N r ψ t) :
    ℍ → ℂ)) hCH
  simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul, LinearMap.zero_apply, Submodule.coe_zero] at h0
  have e : ∀ x, (((T ^ x) g : classSpace N r ψ t) : ℍ → ℂ) =
      restrictUpper ((upOp p)^[x] f) := fun x => by
    rw [upEnd_pow_coe ψ hN h24 hpN ht x g]
    exact upH_iterate_restrictUpper f x
  simp_rw [e] at h0
  -- the combination vanishes on `ℍ`
  set F : ℂ → ℂ := ∑ k ∈ Finset.range (T.charpoly.natDegree + 1),
    T.charpoly.coeff k • (upOp p)^[k] f with hF
  have hFz : ∀ τ : ℂ, 0 < τ.im → F τ = 0 := by
    intro τ hτ
    have := congrFun h0 ⟨τ, hτ⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [hF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact this
  have hc := coeff_finset_sum (N := N) (Finset.range (T.charpoly.natDegree + 1))
    (fun k => T.charpoly.coeff k) (f := fun k => (upOp p)^[k] f)
    (fun k _ => isThetaTypeForm_upOp_iterate hN h24 hpN hf.1 k) n
  have hz : thetaTypeCoeff F n = 0 := coeff_eq_zero_of_eq_zero hFz n
  calc ∑ k ∈ Finset.range (T.charpoly.natDegree + 1),
        T.charpoly.coeff k * thetaTypeCoeff f (p ^ (2 * k) * n)
      = ∑ k ∈ Finset.range (T.charpoly.natDegree + 1),
        T.charpoly.coeff k * thetaTypeCoeff ((upOp p)^[k] f) n :=
        Finset.sum_congr rfl fun k _ => by rw [coeff_upOp_iterate hN h24 hpN hf.1]
    _ = thetaTypeCoeff F n := hc.symm
    _ = 0 := hz

end SSHecke

end VOA.Classification.COne
