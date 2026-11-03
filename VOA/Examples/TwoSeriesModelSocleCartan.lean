/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesModelSocleSing

/-!
# Transversality of the model socle

For a coefficient ring `R` with letter constants `t : ℕ → R` and a scaling automorphism `θ`
(`θ (t n) = 2^{n+1} t n`), the model `S_r = modelImage R t r` with its mode action and conformal
grading satisfies the **transversality half of the socle data**: a singular vector of degree
`d` and charge `-2N` meets `Cart N + (other degrees) + range (h₀ + 2N)` only in `0`.

The tool is the `ℂ`-linear functional `lam R q : Q ↦ coeff_q (evV Q)` (the coefficient of the
pure power `v₀^q`, read in `R`):

* it kills `range (h₀ + q)` (`lam_h0_add`);
* it kills the image of the Cartan ideal `I_N` on `S_r` when `q = 2N` (`modelCart_le_ker_lam`):
  `lam` only sees the `u`-free part (`evV_mkillU`), killing `u` commutes with the Cartan modes
  (`mkillU_mder_h`), the `u`-free part of `S_r` lies in the `R`-span of `Z`-products
  (`mkillU_modelImage`), and on a `Z`-product of length `N'` the Cartan calculus of `F ∈ I_N`
  vanishes for `N' = N` (`jetCalc_zprod`) and has charge `-2N' ≠ -2N` otherwise;
* it intertwines the scaling `Θ` with `θ` (`lam_Θ`), so it maps the degree-`d'` piece into the
  `θ`-eigenspace of eigenvalue `2^{d'-r}`, and these eigenspaces are independent;
* on a singular vector `s` of charge `-2N`, `s = lam s · v₀^{2N}` (`msing_eq_C_mul_pow`), so
  `lam s = 0` forces `s = 0`.

`model_transverse` — the transversality, proved outright for every such `(R, t, θ)`.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.SocleDual VOA.CyclicEval VOA.InvariantSymbol
open VOA.AffineVOA.CorrectedR (Generator)

noncomputable section

variable (R : Type) [CommRing R] [Algebra ℂ R]

/-! ### The Cartan calculus on the model ring -/

theorem m_cartanCommute : CartanCommute (mρ R) bHPos := fun i j =>
  LinearMap.ext fun m => mder_comm_ι R _ _ (fun x => jetDer_h_comm (i + 1) (j + 1) (X x)) m

/-- The Cartan calculus on the full model ring. -/
abbrev mCalc : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ (MPoly R) :=
  cartanCalc (mρ R) bHPos (m_cartanCommute R)

theorem mImg_calc_coe (t : ℕ → R) (r : ℕ) (F : MvPolynomial ℕ ℂ) (m : modelImage R t r) :
    ((cartanCalc (mImgRho R t r) bHPos (mImg_cartanCommute R t r) F m : modelImage R t r) :
      MPoly R) = mCalc R F m := by
  have h := algHom_comp_eq_of_X (cartanCalc (mImgRho R t r) bHPos (mImg_cartanCommute R t r))
    (mCalc R) (modelImage R t r).subtype (fun i => by
      rw [cartanCalc_X, cartanCalc_X, LinearMap.comp_neg, LinearMap.neg_comp]
      rfl) F
  exact LinearMap.congr_fun h m

theorem mder_C_mul (k : Fin 3 × ℕ) (a : R) (Q : MPoly R) :
    mder R k (MvPolynomial.C a * Q) = MvPolynomial.C a * mder R k Q := by
  rw [Derivation.leibniz, mder_C, smul_zero, add_zero, smul_eq_mul]

/-! ### Killing `u` -/

/-- `u_j ↦ 0`, `v_j ↦ v_j` on the model ring. -/
def mkillU : MPoly R →ₐ[R] MPoly R := aeval fun x => if x.1 = 0 then 0 else X x

omit [Algebra ℂ R] in
theorem mkillU_C (a : R) : mkillU R (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]

theorem mkillU_ι (P : JetPoly) : mkillU R (ι R P) = ι R (killU P) := by
  have h : ((mkillU R).restrictScalars ℂ).comp (ι R) = (ι R).comp killU := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, ι_X, killU_X, mkillU, aeval_X]
    split_ifs <;> simp
  exact AlgHom.congr_fun h P

omit [Algebra ℂ R] in
theorem evV_mkillU (Q : MPoly R) : evV R (mkillU R Q) = evV R Q := by
  have h : (evV R).comp (mkillU R) = evV R := by
    apply MvPolynomial.algHom_ext
    intro x
    obtain ⟨b, j⟩ := x
    simp only [AlgHom.comp_apply, mkillU, aeval_X]
    fin_cases b <;> simp
  exact AlgHom.congr_fun h Q

theorem mkillU_mder_h (m : ℕ) (Q : MPoly R) :
    mkillU R (mder R (2, m) Q) = mder R (2, m) (mkillU R Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [mder_C, map_zero, mkillU_C, mder_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p x hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp, map_mul,
      Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    congr 2
    rw [mder_X, ← jetDer_X, mkillU_ι, killU_jetDer_h, ← mder_ι, ← mkillU_ι, ι_X]

theorem mkillU_mCalc (F : MvPolynomial ℕ ℂ) (Q : MPoly R) :
    mkillU R (mCalc R F Q) = mCalc R F (mkillU R Q) := by
  have h := algHom_comp_eq_of_X (mCalc R) (mCalc R) ((mkillU R).restrictScalars ℂ).toLinearMap
    (fun i => by
      refine LinearMap.ext fun Q => ?_
      simp only [cartanCalc_X, LinearMap.comp_apply, LinearMap.neg_apply, map_neg,
        AlgHom.toLinearMap_apply, AlgHom.restrictScalars_apply, mρ_apply]
      rw [mkillU_mder_h]) F
  exact LinearMap.congr_fun h Q

/-! ### The `u`-free part of the model lies in the span of `Z`-products -/

/-- The `ℂ`-span of the `R`-multiples of `Z`-products. -/
def KZ : Submodule ℂ (MPoly R) :=
  Submodule.span ℂ {Q | ∃ (a : R) (N : ℕ) (b : Fin N → ℕ),
    Q = MvPolynomial.C a * ι R (zprod (r := N) b)}

theorem zprod_cons {N : ℕ} (k : ℕ) (b : Fin N → ℕ) :
    zprod (r := N + 1) (Fin.cons k b) = genCoeff 2 k * zprod (r := N) b := by
  simp [zprod, Fin.prod_univ_succ]

theorem C_mul_mem_KZ (a' : R) : ∀ x ∈ KZ R, MvPolynomial.C a' * x ∈ KZ R := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, N, b, rfl⟩ := hx
    exact Submodule.subset_span ⟨a' * a, N, b, by rw [map_mul, mul_assoc]⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem zCoeff_mul_mem_KZ (k : ℕ) : ∀ x ∈ KZ R, ι R (genCoeff 2 k) * x ∈ KZ R := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, N, b, rfl⟩ := hx
    refine Submodule.subset_span ⟨a, N + 1, Fin.cons k b, ?_⟩
    rw [zprod_cons, map_mul]
    ring
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem zSpan_mul_mem_KZ : ∀ y ∈ zSpan, ∀ x ∈ KZ R, ι R y * x ∈ KZ R := by
  intro y hy x hx
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact zCoeff_mul_mem_KZ R k x hx
  | zero => rw [map_zero, zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add, add_mul]; exact add_mem hy hz
  | smul c y _ hy => rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ c hy

variable (t : ℕ → R)

theorem mkillU_mletter_mul (l : Generator × ℕ) {x : MPoly R} (hx : x ∈ KZ R) :
    mkillU R (mletter R t l) * x ∈ KZ R := by
  obtain ⟨g, n⟩ := l
  cases g with
  | current a =>
    change mkillU R (ι R (letterSym _)) * x ∈ KZ R
    rw [mkillU_ι]
    exact zSpan_mul_mem_KZ R _ (killU_genSpan _ (letterSym_mem_genSpan _)) x hx
  | sugawara =>
    change mkillU R (ι R (letterSym _) + MvPolynomial.C (t n)) * x ∈ KZ R
    rw [map_add, mkillU_ι, mkillU_C, add_mul]
    exact add_mem (zSpan_mul_mem_KZ R _ (killU_genSpan _ (letterSym_mem_genSpan _)) x hx)
      (C_mul_mem_KZ R _ x hx)

theorem mkillU_mword_mem (w : List (Generator × ℕ)) : mkillU R (mword R t w) ∈ KZ R := by
  induction w with
  | nil =>
    rw [mword_nil, map_one]
    exact Submodule.subset_span ⟨1, 0, Fin.elim0, by simp [zprod]⟩
  | cons l w ih =>
    rw [mword_cons, map_mul]
    exact mkillU_mletter_mul R t l ih

theorem mkillU_modelImage (r : ℕ) : ∀ Q ∈ modelImage R t r, mkillU R Q ∈ KZ R := by
  intro Q hQ
  induction hQ using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨w, -, rfl⟩ := hQ
    exact mkillU_mword_mem R t w
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [show mkillU R (c • x) = c • mkillU R x from (mkillU R).map_smul_of_tower c x]
    exact Submodule.smul_mem _ c hx

/-! ### The `v₀^q`-coefficient functional -/

/-- `Q ↦ coeff_q (evV Q)`: the coefficient of the pure power `v₀^q`, in `R`. -/
def lam (q : ℕ) : MPoly R →ₗ[ℂ] R :=
  ((Polynomial.lcoeff R q).restrictScalars ℂ) ∘ₗ ((evV R).toLinearMap.restrictScalars ℂ)

@[simp] theorem lam_apply (q : ℕ) (Q : MPoly R) : lam R q Q = (evV R Q).coeff q := rfl

theorem lam_h0_add (q : ℕ) (Q : MPoly R) : lam R q (mder R (2, 0) Q + (q : ℂ) • Q) = 0 := by
  rw [map_add, lam_apply, evV_mder_h0, Polynomial.coeff_neg, coeff_X_mul_derivative,
    map_smul, lam_apply, Nat.cast_smul_eq_nsmul ℂ, nsmul_eq_mul]
  ring

theorem mCalc_C_mul_ι (F : MvPolynomial ℕ ℂ) (a : R) (P : JetPoly) :
    mCalc R F (MvPolynomial.C a * ι R P) = MvPolynomial.C a * ι R (jetCalc F P) := by
  let f : JetPoly →ₗ[ℂ] MPoly R := LinearMap.mulLeft ℂ (MvPolynomial.C a) ∘ₗ (ι R).toLinearMap
  have h := algHom_comp_eq_of_X jetCalc (mCalc R) f (fun i => by
    refine LinearMap.ext fun P => ?_
    simp only [f, cartanCalc_X, LinearMap.comp_apply, LinearMap.neg_apply, map_neg,
      AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply, jetRho_apply, mρ_apply, mder_C_mul,
      mder_ι]) F
  exact (LinearMap.congr_fun h P).symm

theorem jetCalc_h0_comm (F : MvPolynomial ℕ ℂ) (P : JetPoly) :
    jetDer (2, 0) (jetCalc F P) = jetCalc F (jetDer (2, 0) P) := by
  have h := algHom_comp_eq_of_X jetCalc jetCalc (jetRho (2, 0)) (fun i => by
    refine LinearMap.ext fun P => ?_
    simp only [cartanCalc_X, LinearMap.comp_apply, LinearMap.neg_apply, map_neg, jetRho_apply]
    rw [jetDer_h_comm]) F
  exact LinearMap.congr_fun h P

theorem lam_mCalc_gen {N : ℕ} {F : MvPolynomial ℕ ℂ} (hF : F ∈ cartanIdeal N) (a : R)
    {N' : ℕ} (b : Fin N' → ℕ) :
    lam R (2 * N) (mCalc R F (MvPolynomial.C a * ι R (zprod (r := N') b))) = 0 := by
  rw [mCalc_C_mul_ι]
  by_cases hN : N' = N
  · subst hN
    rw [jetCalc_zprod N' hF b, map_zero, mul_zero, map_zero]
  · rw [lam_apply]
    refine coeff_evV_eq_zero_of_charge R (c := -(2 * (N' : ℂ))) ?_ ?_
    · rw [mder_C_mul, mder_ι, jetCalc_h0_comm, jetDer_h0_zprod, map_smul, map_smul,
        mul_smul_comm]
    · intro h
      apply hN
      have : ((2 * N' : ℕ) : ℂ) = ((2 * N : ℕ) : ℂ) := by push_cast at h ⊢; linear_combination -h
      have := Nat.cast_injective this
      omega

theorem lam_mCalc_KZ {N : ℕ} {F : MvPolynomial ℕ ℂ} (hF : F ∈ cartanIdeal N) :
    ∀ Q ∈ KZ R, lam R (2 * N) (mCalc R F Q) = 0 := by
  intro Q hQ
  induction hQ using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨a, N', b, rfl⟩ := hQ
    exact lam_mCalc_gen R hF a b
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, map_smul, hx, smul_zero]

/-- **`lam` kills the image of the Cartan ideal `I_N` on the model.** -/
theorem lam_mCalc_modelImage (r N : ℕ) {F : MvPolynomial ℕ ℂ} (hF : F ∈ cartanIdeal N)
    {Q : MPoly R} (hQ : Q ∈ modelImage R t r) : lam R (2 * N) (mCalc R F Q) = 0 := by
  rw [lam_apply, ← evV_mkillU, mkillU_mCalc, ← lam_apply]
  exact lam_mCalc_KZ R hF _ (mkillU_modelImage R t r Q hQ)

/-- `lam` restricted to the model. -/
def lamImg (r q : ℕ) : modelImage R t r →ₗ[ℂ] R := lam R q ∘ₗ (modelImage R t r).subtype

theorem modelCart_le_ker_lam (r N : ℕ) :
    modelCart (mImgRho R t r) (mImg_cartanCommute R t r) N ≤
      LinearMap.ker (lamImg R t r (2 * N)) := by
  refine iSup_le fun F => iSup_le fun hF => ?_
  rintro _ ⟨y, rfl⟩
  rw [LinearMap.mem_ker, lamImg, LinearMap.comp_apply, Submodule.subtype_apply, mImg_calc_coe]
  exact lam_mCalc_modelImage R t r N hF y.2

/-! ### Scaling -/

variable (θ : R →ₐ[ℂ] R)

theorem evV_Θ (Q : MPoly R) : evV R (Θ R θ Q) = Polynomial.map θ.toRingHom (evV R Q) := by
  have h : (evV R).toRingHom.comp (Θ R θ).toRingHom =
      (Polynomial.mapRingHom θ.toRingHom).comp (evV R).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Θ_C]
    · intro x
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Θ,
        AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply, map_X, AlgHom.restrictScalars_apply,
        aeval_X, map_mul, evV_C, evV_X, Polynomial.coe_mapRingHom]
      split_ifs with hx
      · subst hx; simp
      · simp
  exact RingHom.congr_fun h Q

theorem lam_Θ (q : ℕ) (Q : MPoly R) : lam R q (Θ R θ Q) = θ (lam R q Q) := by
  rw [lam_apply, evV_Θ, Polynomial.coeff_map, lam_apply]
  rfl

theorem Θ_modelDeg (ht : ∀ n, θ (t n) = (2 : ℂ) ^ (n + 1) • t n) (r : ℕ) (d : ℤ) :
    modelDeg R t r d ≤ Module.End.eigenspace (Θ R θ).toLinearMap ((2 : ℂ) ^ (d - r)) := by
  rw [modelDeg, Submodule.span_le]
  rintro _ ⟨w, hw, hd, rfl⟩
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, AlgHom.toLinearMap_apply,
    Θ_mword R θ t ht]
  congr 1
  rw [← hd, wordWt_eq_wjw, hw, add_sub_cancel_right, zpow_natCast]

/-! ### Transversality -/

theorem mem_sing_model {r : ℕ} {d : ℤ} {c : ℂ} {s : modelImage R t r}
    (hs : s ∈ sing (mImgRho R t r) (mImgDeg R t r) d c) :
    MSing R c (s : MPoly R) ∧ (s : MPoly R) ∈ modelDeg R t r d := by
  obtain ⟨hsd, hpos, hf, hh⟩ := hs
  refine ⟨⟨fun a j => ?_, ?_, ?_⟩, hsd⟩
  · have := congrArg Subtype.val (hpos a j); simpa using this
  · have := congrArg Subtype.val hf; simpa using this
  · have := congrArg Subtype.val hh; simpa using this

/-- **Transversality of the model socle**, for every coefficient ring with a scaling
automorphism. -/
theorem model_transverse (ht : ∀ n, θ (t n) = (2 : ℂ) ^ (n + 1) • t n) (r : ℕ) (d : ℤ)
    (N : ℕ) :
    Disjoint (sing (mImgRho R t r) (mImgDeg R t r) d (-(2 * (N : ℂ))))
      (avoid (mImgRho R t r) (mImgDeg R t r)
        (modelCart (mImgRho R t r) (mImg_cartanCommute R t r)) d N) := by
  rw [Submodule.disjoint_def]
  intro s hs hav
  obtain ⟨hsing, hsd⟩ := mem_sing_model R t hs
  let E : ℤ → Submodule ℂ R := fun d' =>
    Module.End.eigenspace (θ.toLinearMap) ((2 : ℂ) ^ (d' - r))
  have hind : iSupIndep E :=
    (Module.End.eigenspaces_iSupIndep (θ.toLinearMap)).comp
      (f := fun d' : ℤ => (2 : ℂ) ^ (d' - r))
      (fun a b hab => by simpa using two_zpow_injective hab)
  have hE : ∀ d' : ℤ, ∀ Q ∈ modelDeg R t r d', lam R (2 * N) Q ∈ E d' := by
    intro d' Q hQ
    have h1 := Module.End.mem_eigenspace_iff.mp (Θ_modelDeg R t θ ht r d' hQ)
    rw [AlgHom.toLinearMap_apply] at h1
    rw [Module.End.mem_eigenspace_iff, AlgHom.toLinearMap_apply, ← lam_Θ, h1, map_smul]
  have h1 : lamImg R t r (2 * N) s ∈ E d := hE d _ hsd
  have h2 : lamImg R t r (2 * N) s ∈ ⨆ (d' : ℤ) (_ : d' ≠ d), E d' := by
    have hle : avoid (mImgRho R t r) (mImgDeg R t r)
        (modelCart (mImgRho R t r) (mImg_cartanCommute R t r)) d N ≤
        (⨆ (d' : ℤ) (_ : d' ≠ d), E d').comap (lamImg R t r (2 * N)) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro x hx
        rw [Submodule.mem_comap, LinearMap.mem_ker.mp (modelCart_le_ker_lam R t r N hx)]
        exact zero_mem _
      · refine iSup_le fun d' => iSup_le fun hd' => fun x hx => ?_
        rw [Submodule.mem_comap]
        exact Submodule.mem_iSup_of_mem d' (Submodule.mem_iSup_of_mem hd' (hE d' _ hx))
      · rintro _ ⟨x, rfl⟩
        rw [Submodule.mem_comap]
        have : lamImg R t r (2 * N)
            ((mImgRho R t r (2, 0) + (2 * (N : ℂ)) • (1 : Module.End ℂ (modelImage R t r))) x)
            = 0 := by
          have h := lam_h0_add R (2 * N) (x : MPoly R)
          simp only [lamImg, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.add_apply,
            LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_add, Submodule.coe_smul,
            mImgRho_coe]
          push_cast at h
          exact h
        rw [this]
        exact zero_mem _
    exact hle hav
  have h0 : lamImg R t r (2 * N) s = 0 :=
    Submodule.disjoint_def.mp (hind d) _ h1 h2
  have hc : -(2 * (N : ℂ)) = -((2 * N : ℕ) : ℂ) := by push_cast; ring
  rw [hc] at hsing
  have hs' := msing_eq_C_mul_pow R hsing
  apply Subtype.ext
  rw [hs', show (evV R (s : MPoly R)).coeff (2 * N) = lamImg R t r (2 * N) s from rfl, h0,
    map_zero, zero_mul, ZeroMemClass.coe_zero]

end

end VOA.TwoSeries.StrictModel
