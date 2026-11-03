import VOA.Classification.COne.PlusRat6TwMono

/-! # The twisted Fock model as a weak `V_{2m}⁺`-module and its joint spectrum

`BW m hm t` is the restriction of the twisted module `Tw m hm t` to `V_{2m}⁺` on the whole carrier
`FockT 1 ⊗ ℂ` (`PlusTwistLattice.restrictedModule`).  Its `L(0)`-eigenspaces are spanned by the
monomials `X^s ⊗ 1` (`weightLT_span`), which are joint eigenvectors of `o(H⁴)`, `o(H⁶)` with
eigenvalues `φT a = -1/128 + a/8`, `ψT b = 1/256 + b/32` (`a = wtT 3 s`, `b = wtT 5 s`):
`specSpan_tw`.
-/
set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.PlusRat6
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2 PlusUnitary PlusRat3 PlusRat5
open VOA.Moonshine.LatticeTwistedGeneral VOA.TwistedHeisenberg VOA.Moonshine.LatticeTwisted
open scoped TensorProduct

variable (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2)

/-- The twisted spectrum maps. -/
def φT (a : ℕ) : ℂ := (-1 / 128 : ℂ) + (a : ℂ) / 8
def ψT (b : ℕ) : ℂ := (1 / 256 : ℂ) + (b : ℂ) / 32

/-- The restricted twisted module as an ordinary `V_{2m}⁺`-module. -/
abbrev NW : OrdVModule (V2mPlus m hm) (FockT (rank (latP m)) ⊗[ℂ] ℂ) :=
  PlusTwistLattice.restrictedModule m hm t

/-- The restricted twisted module as a weak `V_{2m}⁺`-module. -/
abbrev BW : WeakModule (V2mPlus m hm) (FockT (rank (latP m)) ⊗[ℂ] ℂ) := (NW m hm t).toWeakModule

theorem BW_mode (a : VP m hm) (n : ℤ) (x : FockT (rank (latP m)) ⊗[ℂ] ℂ) :
    mode ((BW m hm t).YM a) n x = (Tw m hm t).YM (a : LatModuleGen (latP m)) (2 * n) x := by
  change mode (fixedFields (Tw m hm t) a) n x = _
  rw [mode_fixedFields]

theorem BW_A (x : FockT (rank (latP m)) ⊗[ℂ] ℂ) :
    mode ((BW m hm t).YM (aL m hm).state) (aL m hm).modeIndex x = (Tw m hm t).YM (ls m H4R) 6 x := by
  change mode ((BW m hm t).YM (HP m hm 2)) 3 x = _
  rw [BW_mode, hasN_HP m hm 2 (by norm_num) (by norm_num)]
  rfl

theorem BW_B (x : FockT (rank (latP m)) ⊗[ℂ] ℂ) :
    mode ((BW m hm t).YM (bL m hm).state) (bL m hm).modeIndex x = (Tw m hm t).YM (ls m H6R) 10 x := by
  change mode ((BW m hm t).YM (HP m hm 3)) 5 x = _
  rw [BW_mode, hasN_HP m hm 3 (by norm_num) (by norm_num)]
  rfl

theorem NW_weight (w : ℂ) : (NW m hm t).weight w = weightLT (rank (latP m)) ℂ w := rfl

/-- The doubled level of an exponent vector. -/
abbrev lvl (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) : ℕ := Finsupp.weight wT s

/-- `GT d` is spanned by the monomials of doubled level `d`. -/
theorem GT_span (d : ℕ) {x : FockT (rank (latP m)) ⊗[ℂ] ℂ} (hx : x ∈ GT (rank (latP m)) ℂ d) :
    x ∈ Submodule.span ℂ {u | ∃ s, lvl m s = d ∧ u = monoT m s} := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | tmul y c =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]
    have hy : (y : FockT (rank (latP m))).IsWeightedHomogeneous wT d := y.2
    rw [show ((y : FockT (rank (latP m))) ⊗ₜ[ℂ] c) = c • ((y : FockT (rank (latP m))) ⊗ₜ[ℂ] (1 : ℂ)) by
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, smul_eq_mul, mul_one]]
    apply Submodule.smul_mem
    rw [MvPolynomial.as_sum (y : FockT (rank (latP m))), TensorProduct.sum_tmul]
    refine Submodule.sum_mem _ (fun s hs => ?_)
    rw [show MvPolynomial.monomial s (MvPolynomial.coeff s (y : FockT (rank (latP m)))) =
        MvPolynomial.coeff s (y : FockT (rank (latP m))) • MvPolynomial.monomial s (1 : ℂ) by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], ← TensorProduct.smul_tmul']
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨s, hy (MvPolynomial.mem_support_iff.mp hs), rfl⟩

theorem wtT_le (e : ℕ) (he : 1 ≤ e) (s : (ℕ × Fin (rank (latP m))) →₀ ℕ) :
    wtT m e s ≤ (lvl m s) ^ e := by
  induction s using Finsupp.induction_linear with
  | zero => simp [wtT]
  | add f g hf hg =>
    rw [wtT, map_add, ← wtT, ← wtT, lvl, map_add, ← lvl, ← lvl]
    calc wtT m e f + wtT m e g ≤ (lvl m f) ^ e + (lvl m g) ^ e := Nat.add_le_add hf hg
      _ ≤ _ := pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) (by omega)
  | single a b =>
    rw [wtT, lvl, Finsupp.weight_single, Finsupp.weight_single, smul_eq_mul, smul_eq_mul, pT, wT_apply,
      mul_pow]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · exact Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) b)

/-- **Spectral span of the twisted model.** -/
theorem specSpan_tw (w : ℂ) :
    ∃ C : ℕ, SpecSpanG m hm (BW m hm t) w φT ψT C (fun _ _ => True) := by
  by_cases hex : ∃ d : ℕ, ((levelT (rank (latP m)) d : ℚ) : ℂ) = w
  · obtain ⟨d, hd⟩ := hex
    refine ⟨d ^ 5, fun y hy => ?_⟩
    have hyw : y ∈ (NW m hm t).weight w := VOA.eigenvector_mem_weight _ hy
    rw [NW_weight, ← hd, weightLT_level] at hyw
    refine Submodule.span_mono ?_ (GT_span m d hyw)
    rintro _ ⟨s, hs, rfl⟩
    have h3 := wtT_le m 3 (by norm_num) s
    have h5 := wtT_le m 5 (by norm_num) s
    rw [hs] at h3 h5
    have h35 : d ^ 3 ≤ d ^ 5 := by
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · rw [h0]; simp
      · exact Nat.pow_le_pow_right hpos (by norm_num)
    refine ⟨wtT m 3 s, wtT m 5 s, trivial, by omega, h5, ?_, ?_⟩
    · rw [BW_A, o4_mono]; rfl
    · rw [BW_B, o6_mono]; rfl
  · push Not at hex
    refine ⟨0, fun y hy => ?_⟩
    have hyw : y ∈ (NW m hm t).weight w := VOA.eigenvector_mem_weight _ hy
    rw [NW_weight, weightLT_eq_bot _ _ hex, Submodule.mem_bot] at hyw
    rw [hyw]
    exact Submodule.zero_mem _

end VOA.Classification.COne.PlusRat6
