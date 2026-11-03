import VOA.Classification.COne.PlusSplitC2Dimension
import VOA.Classification.COne.PlusUnitaryVac

/-! A sharper neutral C₂ cutoff from the first charged Schur relation. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusC2Sharp
open PlusC2 PlusUnitary VOA.TripletNilp VOA.LatGen VOA.LatGen.Triplet
  VOA.IntegralLattice HeisenbergN VOA.Moonshine MvPolynomial
variable (m : ℕ) (hm : 1 ≤ m)

/-- Inclusion of the neutral Poisson algebra into the plus Poisson algebra. -/
def poissonIncl : A₂ (M1P m hm) →ₐ[ℂ] A₂ (V2mPlus m hm) :=
  let f := (O₂ (M1P m hm)).mapQ (O₂ (V2mPlus m hm)) (incl m hm)
    (fun _ hv => c2M1Plus_le_O₂ m hm (incl_O₂_le m hm ⟨_, hv, rfl⟩))
  { f with
    map_zero' := map_zero f
    map_one' := congrArg (mk₂ (V2mPlus m hm)) (incl_gradedHom m hm).map_vacuum
    map_mul' := by
      intro x y
      obtain ⟨u, rfl⟩ := (O₂ (M1P m hm)).mkQ_surjective x
      obtain ⟨v, rfl⟩ := (O₂ (M1P m hm)).mkQ_surjective y
      change f (mk₂ _ u * mk₂ _ v) = mk₂ _ (incl m hm u) * mk₂ _ (incl m hm v)
      rw [← mk₂_smul_neg_one, ← mk₂_smul_neg_one]
      exact congrArg (mk₂ (V2mPlus m hm)) ((incl_gradedHom m hm).map_smul u (-1) v)
    commutes' := by
      intro c
      change f (c • (1 : A₂ (M1P m hm))) = c • (1 : A₂ (V2mPlus m hm))
      rw [map_smul]
      congr 1 }

@[simp] theorem poissonIncl_mk₂ (v : (m1Sub m hm).carrier) :
    poissonIncl m hm (mk₂ (M1P m hm) v) = mk₂ (V2mPlus m hm) (incl m hm v) := rfl

theorem neutral_class_mem_monSpan {w : ℤ} (v : (m1Sub m hm).carrier)
    (hv : v ∈ (M1P m hm).grading w) : mk₂ (M1P m hm) v ∈ monSpan m hm w := by
  have ht : v ∈ iterProdSpan (M1P m hm) (gensM m hm) := by
    rw [strongGenM1_holds m hm]; trivial
  have h := mem_span_gradedWords (M1P m hm) (gensM_homog m hm) ht hv
  refine Submodule.span_induction (p := fun x _ => mk₂ (M1P m hm) x ∈ monSpan m hm w)
    ?_ ?_ ?_ ?_ h
  · rintro x ⟨hx, hxw⟩; exact mk₂_word_mem_mon m hm hx w hxw
  · simp only [map_zero, Submodule.zero_mem]
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- Above weight ten every neutral C₂ class lies on the omega line. -/
theorem neutral_class_mem_omega_line (k : ℕ) (hk : 6 ≤ k)
    (v : (m1Sub m hm).carrier) (hv : v ∈ (M1P m hm).grading (2 * k)) :
    mk₂ (M1P m hm) v ∈ Submodule.span ℂ {mk₂ (M1P m hm) (ωM m hm) ^ k} := by
  obtain ⟨ρ, σ, h8⟩ := rel8M_holds m hm
  obtain ⟨τ, h10⟩ := rel10M_holds m hm
  refine (show monSpan m hm (2 * k) ≤ _ from ?_) (neutral_class_mem_monSpan m hm v hv)
  rw [monSpan, Submodule.span_le]
  rintro _ ⟨a, b, hab, rfl⟩
  have hab' : a + 2 * b = k := by omega
  simpa only [hab'] using ring_reduction _ _ ρ σ τ h8 h10 b a (by omega)

/-- A neutral Poisson power becomes zero already at exponent m+1, for m≥5.
This uses the charge-one Schur relation at weight 2m+2 < 4m. -/
theorem omega_pow_eq_zero (hm5 : 5 ≤ m) :
    mk₂ (V2mPlus m hm) (V2mPlus m hm).conformalVector ^ (m + 1) = 0 := by
  let k := m + 1
  let S := vSchur (latP m) ((1 : ℤ) : (latP m).carrier) (2 * k)
  let q := (1 / 2 : ℂ) • (S + sigmaN _ S)
  have hσ : sigmaN (rank (latP m)) q = q := by
    dsimp [q]; rw [map_smul, map_add, sigmaN_sigmaN, add_comm]
  let v : (m1Sub m hm).carrier :=
    ⟨latStateGen (latP m) q 0, (mem_m1Carrier_iff m hm _).mpr ⟨q, hσ, rfl⟩⟩
  have hS : S ∈ gradingWN (rank (latP m)) (2 * k) := vSchur_mem_gradingWN _ _ _
  have hv : v ∈ (M1P m hm).grading (2 * k) :=
    latStateGen_mem_grading m hm (Submodule.smul_mem _ _
      (Submodule.add_mem _ hS (sigmaN_mem_gradingWN _ hS)))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (neutral_class_mem_omega_line m hm k (by dsimp [k]; omega) v hv)
  have hphi : phi m (2 * k) (v : LatModuleGen (latP m)) ≠ 0 := by
    change phi m (2 * k) (latStateGen (latP m) q 0) ≠ 0
    rw [phi_latStateGen]
    have he : topCoeff m (2 * k) q = topCoeff m (2 * k) S := by
      dsimp [q]
      simp only [topCoeff, coeff_smul, coeff_add, smul_eq_mul]
      rw [← topCoeff, ← topCoeff, topCoeff_sigmaN, Even.neg_one_pow (even_two_mul k)]
      ring
    rw [he]
    exact topCoeff_vSchur_ne_zero m hm 1 (by omega) (2 * k)
  have hc0 : c ≠ 0 := by
    intro hz
    have hv0 : v ∈ O₂ (M1P m hm) := by
      apply (mk₂_eq_zero_iff _).mp
      rw [← hc, hz, zero_smul]
    exact hphi (phi_O₂ m hm (2 * k) hv0)
  have hi : incl m hm v = PP m hm (latStateGen (latP m) S 0) := by
    apply Subtype.ext
    change latStateGen (latP m) q 0 = _
    rw [PP_coe, thetaLat_latStateGen, neg_zero, ← latStateGen_add_boson,
      ← latStateGen_csmul]
  have hzero : poissonIncl m hm (mk₂ (M1P m hm) v) = 0 := by
    rw [poissonIncl_mk₂, hi, mk₂_eq_zero_iff]
    exact vSchur_mem_G m hm 1 (2 * k) (by dsimp [k]; simp)
      (by dsimp [k]; simp; omega)
  rw [← hc, map_smul, map_pow] at hzero
  exact (smul_eq_zero.mp hzero).resolve_left hc0

end VOA.Classification.COne.PlusC2Sharp
