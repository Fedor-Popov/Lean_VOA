import VOA.Classification.COne.OrbB5Tetra
import VOA.Classification.COne.OrbOddReduce
import VOA.Classification.COne.PlusUnitaryVacuum

/-! # Vacuum uniqueness for the tetrahedral orbifold

The even Zhu classes are polynomials in the conformal class. The square of
the odd generator is even. At weight zero it acts by zero, so the odd
generator has a nonzero kernel. A vector in that kernel has the vacuum's
entire Zhu character, by the proved even/odd spanning theorem.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbB5
open VOA Polynomial OrbZhu OrbPos OrbC2b OrbC2c PlusUnitary

section Linear
universe u v w
variable {A : Type u} {M : Type v} {T : Type w}
  [AddCommGroup A] [Module ℂ A] [AddCommGroup M] [Module ℂ M]
  [AddCommGroup T] [Module ℂ T]

/-- Classes acting with the same scalar on two specified vectors. -/
def pairedScalars (f : A →ₗ[ℂ] M) (g : A →ₗ[ℂ] T) (x : M) (y : T) :
    Submodule ℂ A where
  carrier := {a | ∃ c : ℂ, f a = c • x ∧ g a = c • y}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc, hc'⟩ ⟨d, hd, hd'⟩
    exact ⟨c + d, by rw [map_add, hc, hd, add_smul],
      by rw [map_add, hc', hd', add_smul]⟩
  smul_mem' := by
    rintro r a ⟨c, hc, hc'⟩
    exact ⟨r * c, by rw [map_smul, hc, smul_smul],
      by rw [map_smul, hc', smul_smul]⟩

end Linear

section Bottom
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

theorem actA_Amul (N : OrdVModule W M) {h : ℂ} (hl : IsLowestWeight N h)
    (a b : A W) :
    actA N hl (Amul (zhuRingData_holds W) a b) = actA N hl a * actA N hl b :=
  actA_mul (zhuRingData_holds W) hl a b

theorem actA_omegaL_pow (N : OrdVModule W M) {h : ℂ} (hl : IsLowestWeight N h)
    (n : ℕ) (z : A W) :
    actA N hl ((omegaL W ^ n) z) = h ^ n • actA N hl z := by
  have hw := conformalPolynomial_bottom N hl (X : ℂ[X])
  rw [aeval_X, eval_X] at hw
  change actA N hl (Amul (zhuRingData_holds W) (mk W W.conformalVector)
    (mk W W.vacuum)) = _ at hw
  rw [Amul_one_right] at hw
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, one_smul]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    change actA N hl (Amul (zhuRingData_holds W) (mk W W.conformalVector) _) = _
    rw [actA_Amul, hw, ih, smul_mul_smul, one_mul, ← pow_succ']

end Bottom

private noncomputable local instance : Fintype tetra :=
  @Fintype.ofFinite _ (Finite.of_equiv (alternatingGroup (Fin 4)) tetra_group.some.symm.toEquiv)

private abbrev adj := adjointModule Wt
private theorem adj_low : IsLowestWeight adj 0 := isLowestWeight_adjoint Wt
private def vac : adj.weight 0 := ⟨Wt.vacuum, vacuum_mem_adjoint_weight Wt⟩

private theorem vac_ne_zero : vac ≠ 0 :=
  fun h => OrbOdd.wt_vacuum_ne_zero (congrArg Subtype.val h)

private theorem adj_U : actA adj (h := 0) adj_low (mk Wt tetraU) vac = 0 := by
  apply Subtype.ext
  rw [actA_mk_apply_coe]
  exact oMod_adjoint_vacuum Wt (by norm_num) tetraU_mem

/-- At bottom weight zero every even Zhu class acts by the same scalar as
on the vacuum bottom. -/
theorem tetra_even_zeroBottom {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wt M) (hl : IsLowestWeight N 0) {z : A Wt} (hz : z ∈ evenSpan) :
    ∃ c : ℂ, actA N hl z = c • 1 ∧ actA adj (h := 0) adj_low z = c • 1 := by
  let S := pairedScalars (actA N hl) (actA adj (h := 0) adj_low)
    (1 : Module.End ℂ (N.weight 0)) (1 : Module.End ℂ (adj.weight 0))
  have hp (P : ℂ[X]) : (aeval (omegaL Wt) P) (mk Wt Wt.vacuum) ∈ S :=
    ⟨P.eval 0, conformalPolynomial_bottom N hl P,
      conformalPolynomial_bottom adj adj_low P⟩
  have hv : mk Wt tetraV ∈ S := by
    obtain ⟨P, hP⟩ := OrbOdd.exists_poly_V
    rw [hP]
    exact hp P
  have hpow (n : ℕ) {a : A Wt} (ha : a ∈ S) : (omegaL Wt ^ n) a ∈ S := by
    obtain ⟨c, hc, hc'⟩ := ha
    exact ⟨(0 : ℂ) ^ n * c, by rw [actA_omegaL_pow, hc, smul_smul],
      by rw [actA_omegaL_pow, hc', smul_smul]⟩
  have h1 : mk Wt Wt.vacuum ∈ S :=
    ⟨1, by simpa only [one_smul] using actA_one N hl,
      by simpa only [one_smul] using actA_one adj adj_low⟩
  have hle : evenSpan ≤ S := by
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hpow i h1
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hpow i hv
  change z ∈ S
  exact hle hz

/-- The odd generator acts with square zero on every weight-zero bottom. -/
theorem tetra_odd_zeroBottom_sq {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wt M) (hl : IsLowestWeight N 0) :
    actA N hl (mk Wt tetraU) * actA N hl (mk Wt tetraU) = 0 := by
  let u := mk Wt tetraU
  have he : Amul (zhuRingData_holds Wt) u u ∈ evenSpan := by
    apply mem_evenSpan_of_fixed
    change zhuMap tau_hom tetraInvolution.map_omega (Amul _ u u) = _
    rw [zhuMap_Amul]
    change Amul _ (tauA u) (tauA u) = _
    simp only [u, tauA_U, map_neg, LinearMap.neg_apply, neg_neg]
  obtain ⟨c, hc, hc'⟩ := tetra_even_zeroBottom N hl he
  have hc0 : c = 0 := by
    have hh := congrArg (fun f : Module.End ℂ (adj.weight 0) => f vac) hc'
    rw [actA_Amul] at hh
    change actA adj (h := 0) adj_low u (actA adj (h := 0) adj_low u vac) = c • vac at hh
    rw [adj_U, map_zero] at hh
    have hh' : c • vac = 0 := hh.symm
    exact (smul_eq_zero.mp hh').resolve_right vac_ne_zero
  rw [actA_Amul, hc0, zero_smul] at hc
  exact hc

set_option synthInstance.maxHeartbeats 100000 in
-- Concrete nested orbifold carriers make the scalar-zero instance expensive.
/-- A weight-zero irreducible module is the vacuum module. -/
theorem tetra_vacuum_of_lowest_zero {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wt M) (hi : N.IsIrreducible) (hl : IsLowestWeight N 0)
    (hne : N.weight 0 ≠ ⊥) : Nonempty (ModuleEquiv Wt N (adjointModule Wt)) := by
  let U := actA N hl (mk Wt tetraU)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hy' : (⟨y, hy⟩ : N.weight 0) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  obtain ⟨x, hx0, hxU⟩ : ∃ x : N.weight 0, x ≠ 0 ∧ U x = 0 := by
    by_cases hh : U ⟨y, hy⟩ = 0
    · exact ⟨⟨y, hy⟩, hy', hh⟩
    · refine ⟨U ⟨y, hy⟩, hh, ?_⟩
      exact congrArg (fun f : Module.End ℂ (N.weight 0) => f ⟨y, hy⟩)
        (tetra_odd_zeroBottom_sq N hl)
  let f : A Wt →ₗ[ℂ] N.weight 0 :=
    { toFun := fun z => actA N hl z x
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  let g : A Wt →ₗ[ℂ] adj.weight 0 :=
    { toFun := fun z => actA adj (h := 0) adj_low z vac
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  let S := pairedScalars f g x vac
  have heven : evenSpan ≤ S := by
    intro z hz
    obtain ⟨c, hc, hc'⟩ := tetra_even_zeroBottom N hl hz
    exact ⟨c, by change actA N hl z x = _; rw [hc]; rfl,
      by change actA adj (h := 0) adj_low z vac = _; rw [hc']; rfl⟩
  have hodd : oddSpan ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨0, ?_, ?_⟩
    · change actA N hl ((omegaL Wt ^ (i : ℕ)) (mk Wt tetraU)) x = _
      rw [actA_omegaL_pow, LinearMap.smul_apply, hxU, smul_zero, zero_smul]
    · change actA adj (h := 0) adj_low ((omegaL Wt ^ (i : ℕ)) (mk Wt tetraU)) vac = _
      rw [actA_omegaL_pow, LinearMap.smul_apply, adj_U, smul_zero, zero_smul]
  have hall : ∀ z, z ∈ S := by
    intro z
    apply (sup_le heven hodd)
    rw [even_odd_top]
    trivial
  apply nonempty_moduleEquiv_adjoint_of_vacuumTop (exceptionalOrbifold_isSimple _) N hi
    hl x.property (fun h => hx0 (Subtype.ext h))
  intro k hk a ha
  obtain ⟨c, hc, hc'⟩ := hall (mk Wt a)
  have hc0 : c = 0 := by
    have hh := congrArg Subtype.val hc'
    change ((actA adj (h := 0) adj_low (mk Wt a) vac : adj.weight 0) : _) = c • Wt.vacuum at hh
    rw [actA_mk_apply_coe] at hh
    change oMod (adjointModule Wt) a Wt.vacuum = c • Wt.vacuum at hh
    rw [oMod_adjoint_vacuum Wt hk ha] at hh
    exact (smul_eq_zero.mp hh.symm).resolve_right OrbOdd.wt_vacuum_ne_zero
  have hh := congrArg Subtype.val hc
  change ((actA N hl (mk Wt a) x : N.weight 0) : M) = c • x.val at hh
  rwa [actA_mk_apply_coe, hc0, zero_smul] at hh

/-- The tetrahedral zero-weight obligation is discharged. -/
theorem tetrahedralZeroWeightVacuum_holds : TetrahedralZeroWeightVacuum := by
  intro M _ _ N hi h0
  obtain ⟨h, hl, hne⟩ := N.exists_isLowestWeight_of_irreducible hi
  obtain ⟨n, hn⟩ := hl 0 h0
  rcases tetra_lowestWeight_zero_or_gap N hl hne with rfl | hh
  · exact tetra_vacuum_of_lowest_zero N hi hl h0
  · have he := congrArg Complex.re hn
    simp only [Complex.zero_re, Complex.add_re, Complex.natCast_re] at he
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith

/-- Unconditional tetrahedral B5, obtained directly from its Zhu algebra. -/
theorem tetra_pseudoUnitary : PseudoUnitary Wt :=
  tetra_pseudoUnitary_iff_zeroWeightVacuum.mpr tetrahedralZeroWeightVacuum_holds

end VOA.Classification.COne.OrbB5
