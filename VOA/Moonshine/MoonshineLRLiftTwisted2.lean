import VOA.Moonshine.MoonshineLRLiftTwisted

/-!
# Covariance of the twisted lattice lift

We extend the corrected charge operators to the extraspecial algebra, then use
uniqueness of its simple representation to construct the charge intertwiner.
Conjugation preserves twisted field products, so word-field induction proves
covariance of every `YML` mode. Transport to rank 24 and restriction to theta-fixed
vectors give `liftTwPlusEquiv` and the required `liftTwPlusEquiv_mode` equation.

The remaining normalization is explicit: we have not proved that a scalar multiple
preserves `TPForm`. `liftTwVnatAutOfForm` assembles the lift conditional on precisely
that form equation. Scalar rescaling preserves the already-proved mode covariance.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA IntegralLattice LatGen Extraspecial
open scoped BigOperators TensorProduct Matrix

section ChargeAction

variable (L : IntegralLattice) (ι : L.carrier →ₗ[ℤ] L.carrier)
  (hEven : L.Even) (hU : IsUnit (gramMat L).det)

/-- A representative of each class modulo twice the lattice. -/
def liftTwRedLift (v : Fin L.bRank → ZMod 2) : L.carrier :=
  (red_surjective L v).choose

theorem liftTwRedLift_spec (v : Fin L.bRank → ZMod 2) :
    red L (liftTwRedLift L v) = v := (red_surjective L v).choose_spec

/-- The corrected charge operator depends only on the reduction modulo two. -/
theorem liftTwChargeOp_of_red_eq {α β : L.carrier} (h : red L α = red L β) :
    liftTwChargeOp L ι hEven hU α = liftTwChargeOp L ι hEven hU β := by
  have hz : red L (α - β) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨γ, hγ⟩ := (red_eq_zero_iff L _).mp hz
  have ha : α = β + 2 • γ := by rw [← hγ]; abel
  rw [ha, liftTwChargeOp_add_two]

/-- Linear extension using the coefficients of the regular representation. -/
def liftTwChargeLinear : alg (cocMat L) →ₗ[ℂ] Module.End ℂ (ExtraT L hEven hU) where
  toFun f := ∑ v, f.val (Pi.single 0 1) v •
    liftTwChargeOp L ι hEven hU (liftTwRedLift L v)
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.smul_sum, smul_smul]

theorem liftTwChargeLinear_eA (α : L.carrier) :
    liftTwChargeLinear L ι hEven hU (eA L α) = liftTwChargeOp L ι hEven hU α := by
  classical
  change (∑ v, op (cocMat L) (red L α) (Pi.single 0 1) v • _) = _
  rw [op_single_zero]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  exact liftTwChargeOp_of_red_eq L ι hEven hU (liftTwRedLift_spec L (red L α))

variable (hι : ∀ α β, L.form (ι α) (ι β) = L.form α β)

include hι in
theorem liftTwChargeLinear_mul (a b : alg (cocMat L)) :
    liftTwChargeLinear L ι hEven hU (a * b) =
      liftTwChargeLinear L ι hEven hU a * liftTwChargeLinear L ι hEven hU b := by
  have ha : a ∈ Submodule.span ℂ (Set.range (eA L)) := by rw [span_eA]; trivial
  have hb : b ∈ Submodule.span ℂ (Set.range (eA L)) := by rw [span_eA]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨α, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨β, rfl⟩ := hb
      rw [eA_mul, map_smul, liftTwChargeLinear_eA, liftTwChargeLinear_eA,
        liftTwChargeLinear_eA, liftTwChargeOp_mul L ι hEven hU hι]
    | zero => simp
    | add b c _ _ hb hc => simp only [mul_add, map_add, hb, hc]
    | smul c b _ hb => simp only [mul_smul_comm, map_smul, hb]
  | zero => simp
  | add a c _ _ ha hc => simp only [add_mul, map_add, ha, hc]
  | smul c a _ ha => simp only [smul_mul_assoc, map_smul, ha]

/-- The pulled-back action of the extraspecial algebra on the charge space. -/
def liftTwChargeAction : alg (cocMat L) →ₐ[ℂ] Module.End ℂ (ExtraT L hEven hU) :=
  AlgHom.ofLinearMap (liftTwChargeLinear L ι hEven hU)
    (by rw [← eA_zero L, liftTwChargeLinear_eA, liftTwChargeOp_zero])
    (liftTwChargeLinear_mul L ι hEven hU hι)

theorem liftTwChargeAction_eA (α : L.carrier) :
    liftTwChargeAction L ι hEven hU hι (eA L α) =
      latCob L L ι α • eT L hEven hU (ι α) :=
  liftTwChargeLinear_eA L ι hEven hU α

/-- The corrected action reaches every endomorphism of the charge space. -/
theorem liftTwChargeAction_surjective :
    Function.Surjective (liftTwChargeAction L ι hEven hU hι) := by
  let E := repEquiv (cocMat L) (isUnit_det_cocMat L hEven hU)
  let f := E.symm.toAlgHom.comp (liftTwChargeAction L ι hEven hU hι)
  haveI := isSimpleRing_alg_cocMat L hEven hU
  have hi : Function.Injective f := f.toRingHom.injective
  have hs : Function.Surjective f :=
    LinearMap.surjective_of_injective (f := f.toLinearMap) hi
  intro g
  obtain ⟨a, ha⟩ := hs (E.symm g)
  exact ⟨a, E.symm.injective ha⟩

include hι in
/-- Representation uniqueness supplies the charge intertwiner with the required phase. -/
theorem liftTwChargeIntertwiner_exists :
    ∃ ρ : ExtraT L hEven hU ≃ₗ[ℂ] ExtraT L hEven hU,
      ∀ α t, ρ (eT L hEven hU α t) =
        latCob L L ι α • eT L hEven hU (ι α) (ρ t) := by
  let A := alg (cocMat L)
  let T := ULift.{0} (ExtraT L hEven hU)
  let E : T ≃ₗ[ℂ] ExtraT L hEven hU := ULift.moduleEquiv
  let ψ := (E.symm.conjAlgEquiv ℂ).toAlgHom.comp
    (liftTwChargeAction L ι hEven hU hι)
  letI : SMul A T := ⟨fun a t => ψ a t⟩
  letI : Module A T := Module.compHom T ψ.toRingHom
  have hs (a : A) (t : T) : a • t = ψ a t := rfl
  letI : IsScalarTower ℂ A T := ⟨fun c a t => by
    rw [hs, hs, map_smul, LinearMap.smul_apply]⟩
  letI : IsSimpleModule A T := by
    have hE := (isSimpleModule_iff_toSpanSingleton_surjective
      (R := Module.End ℂ T) (M := T)).mp inferInstance
    refine isSimpleModule_iff_toSpanSingleton_surjective.mpr
      ⟨inferInstance, fun x hx y => ?_⟩
    obtain ⟨f, hf⟩ := hE.2 x hx y
    have hψ : Function.Surjective ψ := (E.symm.conjAlgEquiv ℂ).surjective.comp
      (liftTwChargeAction_surjective L ι hEven hU hι)
    obtain ⟨a, ha⟩ := hψ f
    refine ⟨a, ?_⟩
    change ψ a x = y
    rw [ha]
    exact hf
  obtain ⟨e⟩ := nonempty_linearEquiv_rep (cocMat L)
    (isUnit_det_cocMat L hEven hU) T
  refine ⟨(e.restrictScalars ℂ).symm.trans E, fun α t => ?_⟩
  have he := congrArg E (e.symm.map_smul (eA L α) t)
  change E (e.symm (eT L hEven hU α t)) =
    E (E.symm (liftTwChargeAction L ι hEven hU hι (eA L α) (E (e.symm t)))) at he
  simpa only [LinearEquiv.apply_symm_apply, liftTwChargeAction_eA,
    LinearMap.smul_apply] using he

/-- A chosen charge intertwiner; no surjectivity hypothesis on the isometry is needed. -/
def liftTwChargeEquiv : ExtraT L hEven hU ≃ₗ[ℂ] ExtraT L hEven hU :=
  (liftTwChargeIntertwiner_exists L ι hEven hU hι).choose

theorem liftTwChargeEquiv_eT (α : L.carrier) (t : ExtraT L hEven hU) :
    liftTwChargeEquiv L ι hEven hU hι (eT L hEven hU α t) =
      latCob L L ι α • eT L hEven hU (ι α) (liftTwChargeEquiv L ι hEven hU hι t) :=
  (liftTwChargeIntertwiner_exists L ι hEven hU hι).choose_spec α t

end ChargeAction

section FieldTransport

open LatticeTwisted TwistedReduction

variable {M : Type*} [AddCommGroup M] [Module ℂ M] (E : M ≃ₗ[ℂ] M)

/-- Conjugation of fields by an arbitrary linear equivalence. -/
def liftTwConjField : Fld M →ₗ[ℂ] Fld M where
  toFun A := ⟨fun n => E.toLinearMap ∘ₗ A.1 n ∘ₗ E.symm.toLinearMap, by
    intro x
    obtain ⟨B, hB⟩ := A.2 (E.symm x)
    refine ⟨B, fun n hn => ?_⟩
    change E (A.1 n (E.symm x)) = 0
    rw [hB n hn, map_zero]⟩
  map_add' A B := by
    apply Subtype.ext
    funext n
    exact LinearMap.ext fun x => map_add E _ _
  map_smul' c A := by
    apply Subtype.ext
    funext n
    exact LinearMap.ext fun x => map_smul E c _

theorem liftTwConjField_mode (A : Fld M) (n : ℤ) (x : M) :
    mode (liftTwConjField E A).1 n x = E (mode A.1 n (E.symm x)) := rfl

theorem liftTwConjField_fzmul (c : ℤ) (A : Fld M) :
    liftTwConjField E (fzmul c A) = fzmul c (liftTwConjField E A) := rfl

/-- Conjugation preserves every integer field product. -/
theorem liftTwConjField_prod (p : ℤ) (A B : Fld M) :
    Fld.prod p (liftTwConjField E A) (liftTwConjField E B) =
      liftTwConjField E (Fld.prod p A B) := by
  apply fld_ext_mode
  intro n x
  rw [liftTwConjField_mode, Fld.mode_prod_iterate, Fld.mode_prod_iterate]
  change _ = (E.toAddEquiv.toAddMonoidHom) _
  rw [AddMonoidHom.map_finsum_of_injective _ E.injective]
  refine finsum_congr fun i => ?_
  simp only [liftTwConjField_mode, LinearEquiv.symm_apply_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, LinearEquiv.coe_toAddEquiv]
  change _ = E _
  rw [map_smul, map_sub, map_smul]

/-- Conjugation preserves the twisted products used in the word-field recursion. -/
theorem liftTwConjField_star {A X : Fld M} (h : Local A.1 X.1) (c : ℂ) (p : ℤ) :
    star c (liftTwConjField E A) p (liftTwConjField E X) =
      liftTwConjField E (star c A p X) := by
  obtain ⟨K, hK⟩ := exists_prod_offset_zero h p
  rw [star_eq_sum_range c A p X K hK,
    star_eq_sum_range c (liftTwConjField E A) p (liftTwConjField E X) K
      (fun i hi => by rw [liftTwConjField_prod, hK i hi, map_zero]), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, liftTwConjField_fzmul, liftTwConjField_prod]

end FieldTransport

section LatticeFields

open LatticeTwisted TwistedReduction TwistedHeisenberg HeisenbergN MvPolynomial

variable (L : IntegralLattice) (hEven : L.Even) (hU : IsUnit (gramMat L).det)
  (hPos : L.PosDef) (ι : L.carrier →ₗ[ℤ] L.carrier)
  (hι : ∀ α β, L.form (ι α) (ι β) = L.form α β)

/-- The twisted tensor equivalence with the charge intertwiner now constructed. -/
def liftTwLatticeEquiv : MT L hEven hU ≃ₗ[ℂ] MT L hEven hU :=
  liftTwLatticeTensorEquiv L hEven hU hPos ι hι (liftTwChargeEquiv L ι hEven hU hι)

theorem liftTwLatticeEquiv_YTL (α : L.carrier) (k : ℤ) (x : MT L hEven hU) :
    liftTwLatticeEquiv L hEven hU hPos ι hι (YTL L hEven hU α k x) =
      latCob L L ι α • YTL L hEven hU (ι α) k (liftTwLatticeEquiv L hEven hU hPos ι hι x) :=
  liftTwLatticeTensorEquiv_YTL L hEven hU hPos ι hι _
    (liftTwChargeEquiv_eT L ι hEven hU hι) α k x

theorem liftTwLatticeEquiv_FgT (a : Fin (rank L)) :
    liftTwConjField (liftTwLatticeEquiv L hEven hU hPos ι hι) (FgT a) =
      ∑ b : Fin (rank L), oscMatrix L L ι b a • FgT b := by
  apply fld_ext_mode
  intro n x
  simp only [liftTwConjField_mode, mode_fld_sum, mode_fld_smul, FgT_val, FgenT,
    mode_resc]
  have h := liftTwTensorEquiv_modeTT (oscMatrix L L ι)
    (oscMatrix_transpose_mul L L hPos hPos ι hι)
    (oscMatrix_mul_transpose L L hPos hPos ι hι rfl)
    (liftTwChargeEquiv L ι hEven hU hι) a (2 * n + 1)
    ((liftTwLatticeEquiv L hEven hU hPos ι hι).symm x)
  change liftTwLatticeEquiv L hEven hU hPos ι hι _ =
    ∑ b, oscMatrix L L ι b a • modeTT b _
      (liftTwLatticeEquiv L hEven hU hPos ι hι
        ((liftTwLatticeEquiv L hEven hU hPos ι hι).symm x)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

theorem liftTwLatticeEquiv_YTLFld (α : L.carrier) (e : ℤ) :
    liftTwConjField (liftTwLatticeEquiv L hEven hU hPos ι hι) (YTLFld L hEven hU α e) =
      latCob L L ι α • YTLFld L hEven hU (ι α) e := by
  apply fld_ext_mode
  intro n x
  rw [liftTwConjField_mode, mode_fld_smul]
  change liftTwLatticeEquiv L hEven hU hPos ι hι
    (mode (resc (YTL L hEven hU α) 2 e) n
      ((liftTwLatticeEquiv L hEven hU hPos ι hι).symm x)) =
    latCob L L ι α • mode (resc (YTL L hEven hU (ι α)) 2 e) n x
  rw [mode_resc, mode_resc, liftTwLatticeEquiv_YTL, LinearEquiv.apply_symm_apply]

include hPos in
theorem liftTwStar_sum {J : Type*} (s : Finset J) (A : J → Fld (MT L hEven hU))
    (X : Fld (MT L hEven hU))
    (hA : ∀ j ∈ s, A j ∈ TGenerated (latGenSet L hEven hU))
    (hX : X ∈ TGenerated (latGenSet L hEven hU)) (c : ℂ) (p : ℤ) :
    star c (∑ j ∈ s, A j) p X = ∑ j ∈ s, star c (A j) p X := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty, star_zero_left]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, star_add_left
      (tloc L hEven hU hPos (hA j (Finset.mem_insert_self j s)) hX)
      (tloc L hEven hU hPos (sum_mem_tgenerated s A
        (fun k hk => hA k (Finset.mem_insert_of_mem hk))) hX),
      ih (fun k hk => hA k (Finset.mem_insert_of_mem hk))]

include hPos in
theorem liftTwFL_current (e : ℤ) (a : Fin (rank L)) (i : ℕ) (u : LatModuleGen L) :
    FL L hEven hU e ((currentN (rank L) 1 a i).rTensor _ u) =
      star (1 / 2) (FgT a) (-(i : ℤ) - 1) (FL L hEven hU (e - 1) u) := by
  have hc : currentN (rank L) 1 a i = LinearMap.mulLeft ℂ (X (i, a)) := by
    ext p
    rw [currentN_apply, oscN_neg _ _ _ (by omega)]
    rw [show (-(-(i : ℤ) - 1) - 1).toNat = i by omega]
    rfl
  rw [hc, ← FL_mulLeft L hEven hU hPos (e - 1) (i, a), sub_add_cancel]

include hPos in
theorem liftTwFL_charge (e : ℤ) (α : L.carrier) :
    FL L hEven hU e (latChargeGen L α) = YTLFld L hEven hU α e := by
  rw [← wordStateLatGen_nil L α, wordStateLatGen_eq, FL_wordState L hEven hU hPos,
    Fw_nil]

include hPos hι in
theorem liftTwLatMorph_current (a : Fin (rank L)) (i : ℕ) (u : LatModuleGen L) :
    latMorph L L ι ((currentN (rank L) 1 a i).rTensor _ u) =
      ∑ b : Fin (rank L), oscMatrix L L ι b a •
        (currentN (rank L) 1 b i).rTensor _ (latMorph L L ι u) :=
  latMorphC_rTensor_current L L ι (latCob L L ι) hPos hPos hι a i u

/-- Twisted word-field induction, including the orthogonal mixing of each letter. -/
theorem liftTwLatticeEquiv_word (l : List (ℕ × Fin (rank L))) (α : L.carrier) (e : ℤ) :
    liftTwConjField (liftTwLatticeEquiv L hEven hU hPos ι hι)
      (FL L hEven hU e (wordStateLatGen L l α)) =
    FL L hEven hU e (latMorph L L ι (wordStateLatGen L l α)) := by
  induction l generalizing e with
  | nil =>
    simp only [wordStateLatGen_nil, latMorph, latMorphC_latChargeGen, map_smul,
      liftTwFL_charge L hEven hU hPos]
    exact liftTwLatticeEquiv_YTLFld L hEven hU hPos ι hι α e
  | cons ia l ih =>
    obtain ⟨i, a⟩ := ia
    simp only [wordStateLatGen_cons, liftTwLatMorph_current L hPos ι hι,
      map_sum, map_smul, liftTwFL_current L hEven hU hPos]
    rw [← liftTwConjField_star _ (tloc L hEven hU hPos (FgT_mem L hEven hU a)
      (FL_mem L hEven hU hPos _ _)), liftTwLatticeEquiv_FgT, ih]
    rw [liftTwStar_sum L hEven hU hPos Finset.univ _ _
      (fun b _ => smul_mem_tgenerated _ (FgT_mem L hEven hU b))
      (FL_mem L hEven hU hPos _ _)]
    exact Finset.sum_congr rfl fun b _ => star_smul_left
      (tloc L hEven hU hPos (FgT_mem L hEven hU b) (FL_mem L hEven hU hPos _ _)) _ _ _

/-- Covariance of the rescaled twisted fields on every lattice VOA state. -/
theorem liftTwLatticeEquiv_FL (e : ℤ) (u : LatModuleGen L) :
    liftTwConjField (liftTwLatticeEquiv L hEven hU hPos ι hι) (FL L hEven hU e u) =
      FL L hEven hU e (latMorph L L ι u) := by
  have h : (liftTwConjField (liftTwLatticeEquiv L hEven hU hPos ι hι)).comp
      (FL L hEven hU e) = (FL L hEven hU e).comp (latMorph L L ι) := by
    refine LinearMap.ext_on_range (wordStateLatGen_span L) fun q => ?_
    obtain ⟨l, α⟩ := q
    exact liftTwLatticeEquiv_word L hEven hU hPos ι hι l α e
  exact LinearMap.congr_fun h u

/-- The constructed equivalence intertwines every mode of the full twisted module. -/
theorem liftTwLatticeEquiv_YML (u : LatModuleGen L) (k : ℤ) (x : MT L hEven hU) :
    liftTwLatticeEquiv L hEven hU hPos ι hι (YML L hEven hU u k x) =
      YML L hEven hU (latMorph L L ι u) k (liftTwLatticeEquiv L hEven hU hPos ι hι x) := by
  have h := congrArg (fun A : Fld (MT L hEven hU) =>
    mode A.1 0 (liftTwLatticeEquiv L hEven hU hPos ι hι x))
    (liftTwLatticeEquiv_FL L hEven hU hPos ι hι k u)
  simpa only [liftTwConjField_mode, LinearEquiv.symm_apply_apply, YML_apply] using h

end LatticeFields

section RankTransport

open LatticeTwisted TwistedHeisenberg TwistedSector

variable (L : IntegralLattice.{0}) (hEven : L.Even) (hU : IsUnit (gramMat L).det)
  (hPos : L.PosDef) (ι : L.carrier →ₗ[ℤ] L.carrier)
  (hι : ∀ α β, L.form (ι α) (ι β) = L.form α β)

/-- Transport the constructed equivalence along an equality of oscillator ranks. -/
def liftTwCastEquiv {r : ℕ} (hr : rank L = r) :
    (FockT r ⊗[ℂ] ExtraT L hEven hU) ≃ₗ[ℂ] (FockT r ⊗[ℂ] ExtraT L hEven hU) :=
  hr ▸ liftTwLatticeEquiv L hEven hU hPos ι hι

theorem liftTwCastEquiv_YM {r : ℕ} (hr : rank L = r) (u : LatModuleGen L) (k : ℤ)
    (x : FockT r ⊗[ℂ] ExtraT L hEven hU) :
    liftTwCastEquiv L hEven hU hPos ι hι hr
      ((hr ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2 (FockT r ⊗[ℂ] ExtraT L hEven hU)).YM
          u k x) =
    (hr ▸ latticeTwistedModule L hEven hU hPos :
      TwistedModule (thetaAut L hEven hPos) 2 (FockT r ⊗[ℂ] ExtraT L hEven hU)).YM
        (latMorph L L ι u) k (liftTwCastEquiv L hEven hU hPos ι hι hr x) := by
  subst hr
  exact liftTwLatticeEquiv_YML L hEven hU hPos ι hι u k x

theorem liftTwCastEquiv_theta {r : ℕ} (hr : rank L = r)
    (x : FockT r ⊗[ℂ] ExtraT L hEven hU) :
    liftTwCastEquiv L hEven hU hPos ι hι hr (twTheta r (ExtraT L hEven hU) x) =
      twTheta r (ExtraT L hEven hU) (liftTwCastEquiv L hEven hU hPos ι hι hr x) := by
  subst hr
  exact liftTwTensorEquiv_theta (oscMatrix L L ι)
    (oscMatrix_transpose_mul L L hPos hPos ι hι)
    (oscMatrix_mul_transpose L L hPos hPos ι hι rfl)
    (liftTwChargeEquiv L ι hEven hU hι) x

end RankTransport

section Leech

open LatticeTwisted TwistedSector

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)

/-- The full Leech twisted lift, with the concrete rank 24 used by `Tw`. -/
def liftTwLeechEquiv : Tw ≃ₗ[ℂ] Tw :=
  liftTwCastEquiv leech leech_even leech_isUnit_det_gramMat leech_posDef ι hι leech_rank

theorem liftTwLeechEquiv_YM (u : LatModuleGen leech) (k : ℤ) (x : Tw) :
    liftTwLeechEquiv ι hι (leechTwistedModule.YM u k x) =
      leechTwistedModule.YM (latMorph leech leech ι u) k (liftTwLeechEquiv ι hι x) :=
  liftTwCastEquiv_YM leech leech_even leech_isUnit_det_gramMat leech_posDef
    ι hι leech_rank u k x

theorem liftTwLeechEquiv_theta (x : Tw) :
    liftTwLeechEquiv ι hι (thetaTwLeech x) = thetaTwLeech (liftTwLeechEquiv ι hι x) :=
  liftTwCastEquiv_theta leech leech_even leech_isUnit_det_gramMat leech_posDef
    ι hι leech_rank x

/-- Restriction of the constructed twisted lift to the theta-fixed sector. -/
def liftTwPlusEquiv : TP ≃ₗ[ℂ] TP where
  toFun x := ⟨liftTwLeechEquiv ι hι x, mem_twFixed.mpr (by
    rw [← liftTwLeechEquiv_theta, mem_twFixed.mp x.2])⟩
  invFun x := ⟨(liftTwLeechEquiv ι hι).symm x, mem_twFixed.mpr (by
    apply (liftTwLeechEquiv ι hι).injective
    rw [liftTwLeechEquiv_theta, LinearEquiv.apply_symm_apply, mem_twFixed.mp x.2])⟩
  left_inv x := Subtype.ext ((liftTwLeechEquiv ι hι).symm_apply_apply x)
  right_inv x := Subtype.ext ((liftTwLeechEquiv ι hι).apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add (liftTwLeechEquiv ι hι) x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (liftTwLeechEquiv ι hι) c x.val)

@[simp] theorem liftTwPlusEquiv_coe (x : TP) :
    (liftTwPlusEquiv ι hι x : Tw) = liftTwLeechEquiv ι hι x := rfl

/-- The required covariance with the lifted lattice automorphism on `V_Λ⁺`. -/
theorem liftTwPlusEquiv_mode (hsurj : Function.Surjective ι)
    (u : (orbifold (Subgroup.zpowers leechTheta)).carrier) (n : ℤ) (t : TP) :
    liftTwPlusEquiv ι hι (mode (plusModule.YM u) n t) =
      mode (plusModule.YM (leechPlusLatMorphAut ι hι hsurj u)) n (liftTwPlusEquiv ι hι t) := by
  apply Subtype.ext
  simp only [liftTwPlusEquiv_coe, mode_plusModule]
  exact liftTwLeechEquiv_YM ι hι u.val (2 * n) t.val

/-- Allow the scalar normalization needed for preservation of the twisted form. -/
def liftTwNormalizedPlusEquiv (c : ℂˣ) : TP ≃ₗ[ℂ] TP :=
  (liftTwPlusEquiv ι hι).trans (LinearEquiv.smulOfUnit c)

@[simp] theorem liftTwNormalizedPlusEquiv_apply (c : ℂˣ) (t : TP) :
    liftTwNormalizedPlusEquiv ι hι c t = (c : ℂ) • liftTwPlusEquiv ι hι t := rfl

theorem liftTwNormalizedPlusEquiv_mode (hsurj : Function.Surjective ι) (c : ℂˣ)
    (u : (orbifold (Subgroup.zpowers leechTheta)).carrier) (n : ℤ) (t : TP) :
    liftTwNormalizedPlusEquiv ι hι c (mode (plusModule.YM u) n t) =
      mode (plusModule.YM (leechPlusLatMorphAut ι hι hsurj u)) n
        (liftTwNormalizedPlusEquiv ι hι c t) := by
  simp only [liftTwNormalizedPlusEquiv_apply, liftTwPlusEquiv_mode ι hι hsurj, map_smul]

/-- Conditional assembly: only scalar normalization of `TPForm` remains to be proved. -/
def liftTwVnatAutOfForm (hsurj : Function.Surjective ι) (c : ℂˣ)
    (hT : ∀ t t' : TP,
      InvForm.TPForm (liftTwNormalizedPlusEquiv ι hι c t)
        (liftTwNormalizedPlusEquiv ι hι c t') = InvForm.TPForm t t') : AutMonster.AutVnat :=
  vnatAutOfPair (leechPlusLatMorphAut ι hι hsurj) (liftTwNormalizedPlusEquiv ι hι c)
    (liftTwNormalizedPlusEquiv_mode ι hι hsurj c) hT

end Leech

end VOA.Moonshine.ConwayNorton.M8
