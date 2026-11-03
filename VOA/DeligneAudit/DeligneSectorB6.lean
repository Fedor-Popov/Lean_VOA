/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorGeneric
import VOA.DeligneAudit.A2SectorB6

/-!
# B6 (type-generic): `M_m` is a finite free `B_m`-module

From U5 with its total-dimension field `≤ (dim g)^m` (`FusionModuleBoundG`): the fibre of `M_m`
satisfies the local Weyl and fusion relations, graded Nakayama generates `M_m` by at most
`(dim g)^m` elements, Lagrange interpolation and `Δ^L N_sym ⊂ M_m` give `(dim g)^m` independent
elements, and the rank count over the domain `B_m` concludes.
-/

namespace VOA.DeligneAudit.DeligneSector

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.DeligneAudit.SectorGraded VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorNakayama VOA.QuadraticCurrentFunctionalCarrier
open VOA.DeligneAudit.A2 (Pm psumS esymmS psumS_mem esymmS_mem discS symP z0 z0_injective lagr
  eval_lagr eval_lagr_perm linearIndependent_of_span_card eval_disc_ne_zero)

noncomputable section

variable {S : DeligneSectorData} {m : ℕ} {F : ℕ → PowerSeries ℚ}

set_option synthInstance.maxHeartbeats 400000 in
variable (S) in
/-- **B6 for the type**: `M_m` is a finite free `B_m`-module. -/
structure MFreenessG : Prop where
  free : ∀ m, Module.Free (SymAlg (K := ℂ) m) (MspaceR S m)
  finite : ∀ m, Module.Finite (SymAlg (K := ℂ) m) (MspaceR S m)

/-! ## Degree pieces of `M_m` -/

variable (S) in
/-- Homogeneous tensors of degree `b`. -/
def degT (m b : ℕ) : Submodule ℂ (TPs S m) where
  carrier := {x | IsHomT b x}
  zero_mem' := fun t => isHomogeneous_zero _ _ _
  add_mem' {x y} hx hy t := (hx t).add (hy t)
  smul_mem' c x hx t := by
    change (c • x t).IsHomogeneous b
    rw [← mem_homogeneousSubmodule] at *
    exact Submodule.smul_mem _ c (hx t)

instance (b : ℕ) : FiniteDimensional ℂ (degT S m b) := by
  haveI : FiniteDimensional ℂ (MvPolynomial.homogeneousSubmodule (Fin (m + 0)) ℂ b) :=
    VOA.MvPolynomialFiniteHomogeneous.finiteDimensional_weightedHomogeneousSubmodule
      (fun _ => 1) (by intros; simp) b
  let g : degT S m b →ₗ[ℂ] ((Fin m → Fin S.n) → MvPolynomial.homogeneousSubmodule (Fin (m + 0)) ℂ b) :=
    { toFun := fun x t => ⟨x.1 t, (mem_homogeneousSubmodule _ _).mpr (x.2 t)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective g fun x y h => Subtype.ext (funext fun t => ?_)
  exact congrArg Subtype.val (congrFun h t)

variable (S) in
/-- The degree-`b` part of `M_m`. -/
def Mdeg (m b : ℕ) : Submodule ℂ (TPs S m) := Mspace S.f m S.c₀ ⊓ degT S m b

instance (b : ℕ) : FiniteDimensional ℂ (Mdeg S m b) :=
  Submodule.finiteDimensional_of_le (S₂ := degT S m b) inf_le_right

theorem projT_mem_Mdeg {x : TPs S m} (hx : x ∈ Mspace S.f m S.c₀) (b : ℕ) :
    projT b x ∈ Mdeg S m b :=
  ⟨wordSpan_le_Mspace _ _ _ (projT_mem_wordSpan _ _ _ hx), isHomT_projT b x⟩

theorem gradedActionM : GradedAction (symDeg (K := ℂ) m) (Mdeg S m) where
  one_mem := by
    change (1 : MvPolynomial (Fin (m + 0)) ℂ) ∈ MvPolynomial.homogeneousSubmodule _ ℂ 0
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_one _ _
  mul_mem := by
    intro n k r r' hr hr'
    have h1 : r.1.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hr
    have h2 : r'.1.IsHomogeneous k := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hr'
    change (r.1 * r'.1) ∈ MvPolynomial.homogeneousSubmodule _ ℂ (n + k)
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact h1.mul h2
  smul_mem := by
    intro n a r x hr hx
    have hr' : r.1.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hr
    exact ⟨smul_mem_Mspace S m r hx.1, fun t => hr'.mul (hx.2 t)⟩

/-! ## The fibre of `M_m` as a current-algebra module -/

theorem deltaVec_mem_Mspace (m : ℕ) : deltaVec (K := ℂ) m S.c₀ ∈ Mspace S.f m S.c₀ :=
  Submodule.subset_span ⟨[], rfl⟩

variable (S) in
/-- `B₊ M_m`. -/
def augM (m : ℕ) : Submodule ℂ (TPs S m) :=
  Submodule.span ℂ {z | ∃ n, 1 ≤ n ∧ ∃ s ∈ symDeg (K := ℂ) m n,
    ∃ y ∈ Mspace S.f m S.c₀, z = s • y}

theorem augM_le : augM S m ≤ Mspace S.f m S.c₀ := by
  rw [augM, Submodule.span_le]
  rintro _ ⟨n, _, s, _, y, hy, rfl⟩
  exact smul_mem_Mspace S m s hy

theorem loopOp_mem_augM (x : Fin S.n) (r : ℕ) {z : TPs S m} (hz : z ∈ augM S m) :
    loopOp S.f m x r z ∈ augM S m := by
  induction hz using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨n, hn, s, hs, y, hy, rfl⟩ := hv
      rw [loopOp_smul]
      exact Submodule.subset_span ⟨n, hn, s, hs, _, loopOp_mem_Mspace x r hy, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

variable (S) in
/-- `M_m` as a type. -/
abbrev MsT (m : ℕ) := Mspace S.f m S.c₀

variable (S) in
/-- `B₊ M_m` inside `M_m`. -/
def augMW (m : ℕ) : Submodule ℂ (MsT S m) := (augM S m).comap (MsT S m).subtype

variable (S) in
/-- The fibre `M_m / B₊ M_m`. -/
abbrev FibM (m : ℕ) := MsT S m ⧸ augMW S m

/-- Loop operators on `M_m`. -/
def opMW (x : Fin S.n) (r : ℕ) : MsT S m →ₗ[ℂ] MsT S m :=
  (loopOp S.f m x r).restrict fun _ hp => loopOp_mem_Mspace x r hp

/-- Loop operators on the fibre. -/
def opFM (x : Fin S.n) (r : ℕ) : FibM S m →ₗ[ℂ] FibM S m :=
  (augMW S m).mapQ (augMW S m) (opMW x r) fun _z hz => loopOp_mem_augM x r hz

theorem opFM_mk (x : Fin S.n) (r : ℕ) (y : MsT S m) :
    opFM x r (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨loopOp S.f m x r y.1, loopOp_mem_Mspace x r y.2⟩ := rfl

variable (S) in
/-- **The fibre of `M_m` is an `sl₃[t]`-module.** -/
def fiberRepM (m : ℕ) : CurrentModule S.f (FibM S m) where
  op := opFM
  comm a b r s v := by
    induction v using Submodule.Quotient.induction_on with
    | H y =>
        simp only [opFM_mk]
        rw [← Submodule.Quotient.mk_sub]
        have h := loopOp_comm S.f S.jacobi m a b r s y.1
        have hsum : ∀ (T : Finset (Fin S.n)), (∑ e ∈ T, S.f a b e • (Submodule.Quotient.mk
            ⟨loopOp S.f m e (r + s) y.1, loopOp_mem_Mspace e (r + s) y.2⟩ : FibM S m)) =
            Submodule.Quotient.mk ⟨∑ e ∈ T, S.f a b e • loopOp S.f m e (r + s) y.1,
              Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _
                (loopOp_mem_Mspace e (r + s) y.2)⟩ := by
          intro T
          induction T using Finset.induction_on with
          | empty => simp; rfl
          | insert e T he ih =>
              rw [Finset.sum_insert he, ih, ← Submodule.Quotient.mk_smul,
                ← Submodule.Quotient.mk_add]
              congr 1
              apply Subtype.ext
              simp [Finset.sum_insert he]
        rw [hsum]
        congr 1
        apply Subtype.ext
        simpa using h

variable (S) in
/-- The fibre generator. -/
def wM (m : ℕ) : FibM S m := Submodule.Quotient.mk ⟨deltaVec m S.c₀, deltaVec_mem_Mspace m⟩

theorem applyWord_mem_Mspace (l : List (Fin S.n × ℕ)) :
    applyWord S.f m l (deltaVec (K := ℂ) m S.c₀) ∈ Mspace S.f m S.c₀ :=
  Submodule.subset_span ⟨l, rfl⟩

theorem wordOp_wM (l : List (Fin S.n × ℕ)) :
    wordOp (fiberRepM S m) l (wM S m) =
      Submodule.Quotient.mk ⟨applyWord S.f m l (deltaVec m S.c₀), applyWord_mem_Mspace l⟩ := by
  induction l with
  | nil => rfl
  | cons xs l ih =>
      change opFM xs.1 xs.2 (wordOp (fiberRepM S m) l (wM S m)) = _
      rw [ih, opFM_mk]
      rfl

/-! ## Relations and fibre dimensions -/

theorem mkM_eq_zero {v : TPs S m} (hv : v ∈ Mspace S.f m S.c₀) (ha : v ∈ augM S m) :
    (Submodule.Quotient.mk ⟨v, hv⟩ : FibM S m) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ha

theorem opGenM (x : Fin S.n) (r : ℕ) :
    (fiberRepM S m).op x r (wM S m) = Submodule.Quotient.mk
      ⟨loopOp S.f m x r (deltaVec m S.c₀), loopOp_mem_Mspace x r (deltaVec_mem_Mspace m)⟩ :=
  rfl

theorem iterate_opGenM (k : ℕ) (x : Fin S.n) :
    ((fiberRepM S m).op x 0)^[k] (wM S m) = Submodule.Quotient.mk
      ⟨applyWord S.f m (List.replicate k (x, 0)) (deltaVec m S.c₀),
        applyWord_mem_Mspace _⟩ := by
  rw [← wordOp_wM]
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, List.replicate_succ]
      rfl

/-- **The generator of the fibre of `M_m` satisfies the local Weyl and fusion relations.** -/
theorem localWeylRelM (m : ℕ) : LocalWeylRelG S (fiberRepM S m) (wM S m) m where
  raising e he r := by
    rw [opGenM]
    apply mkM_eq_zero
    rw [loopOp_raising_deltaVec S m e he r]
    exact Submodule.zero_mem _
  cartan_pos h hh r hr := by
    rw [opGenM]
    apply mkM_eq_zero
    rw [loopOp_cartan_deltaVec S m h hh r]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, hr, psumS m r, psumS_mem m r,
      deltaVec m S.c₀, deltaVec_mem_Mspace m, rfl⟩)
  cartan_zero h hh := by
    rw [opGenM, wM, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    change loopOp S.f m h 0 (deltaVec m S.c₀) = ((m * S.thetaH h : ℕ) : ℂ) • deltaVec m S.c₀
    rw [loopOp_cartan_deltaVec S m h hh 0]
    funext t
    rw [Pi.smul_apply, smul_apply_sym, Pi.smul_apply]
    have hp : ((psumS m 0 : SymAlg (K := ℂ) m) : Pm m) = MvPolynomial.C (m : ℂ) := by
      simp [psumS, psum]
    rw [hp, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    congr 2
    push_cast
    ring
  cartanN_pos h hh r hr := by
    rw [opGenM]
    apply mkM_eq_zero
    rw [loopOp_cartanN_deltaVec S m h hh r]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, hr, psumS m r, psumS_mem m r,
      deltaVec m S.c₀, deltaVec_mem_Mspace m, rfl⟩)
  cartanN_zero h hh := by
    rw [opGenM, wM, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    change loopOp S.f m h 0 (deltaVec m S.c₀) = (-((m * S.thetaN h : ℕ) : ℂ)) • deltaVec m S.c₀
    rw [loopOp_cartanN_deltaVec S m h hh 0]
    funext t
    rw [Pi.smul_apply, smul_apply_sym, Pi.smul_apply]
    have hp : ((psumS m 0 : SymAlg (K := ℂ) m) : Pm m) = MvPolynomial.C (m : ℂ) := by
      simp [psumS, psum]
    rw [hp, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    congr 2
    push_cast
    ring
  lowering i hi := by
    rw [iterate_opGenM]
    apply mkM_eq_zero
    rw [applyWord_replicate, lowering_deltaVec S m i hi]
    exact Submodule.zero_mem _
  fusion x _ := by
    rw [opGenM]
    apply mkM_eq_zero
    rw [loopOp_vieta S]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨j, (Finset.mem_Ico.mp hj).1, esymmS m j, esymmS_mem m j, _,
      loopOp_mem_Mspace x (m - j) (deltaVec_mem_Mspace m), rfl⟩

theorem projT_mem_plusM {z : TPs S m} (hz : z ∈ augM S m) (b : ℕ) :
    projT b z ∈ plus (symDeg (K := ℂ) m) (Mdeg S m) b := by
  induction hz using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨n, hn, s, hs, y, hy, rfl⟩ := hv
      rw [projT_smul_sym m hs]
      split_ifs with hnb
      · exact Submodule.subset_span ⟨n, hn, hnb, s, hs, _, projT_mem_Mdeg hy _, rfl⟩
      · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a c _ _ ha hc => rw [map_add]; exact Submodule.add_mem _ ha hc
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem plus_le_augM (b : ℕ) : plus (symDeg (K := ℂ) m) (Mdeg S m) b ≤ augM S m := by
  rw [plus, Submodule.span_le]
  rintro _ ⟨n, hn, _, r, hr, y, hy, rfl⟩
  exact Submodule.subset_span ⟨n, hn, r, hr, y, hy.1, rfl⟩

/-- **Fibre dimension of `M_m` ≤ loop span of the fibre generator.** -/
theorem fiberDimM_le_cycDeg (b : ℕ) :
    fiberDim (symDeg (K := ℂ) m) (Mdeg S m) b ≤
      Module.finrank ℂ (cycDeg (fiberRepM S m) (wM S m) b) := by
  classical
  set Φ : Mdeg S m b →ₗ[ℂ] FibM S m :=
    (augMW S m).mkQ ∘ₗ Submodule.inclusion (inf_le_left : Mdeg S m b ≤ _) with hΦ
  have hker : (plus (symDeg (K := ℂ) m) (Mdeg S m) b).comap (Mdeg S m b).subtype ≤
      LinearMap.ker Φ := by
    intro x hx
    rw [LinearMap.mem_ker, hΦ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact plus_le_augM b hx
  set Φb := (Submodule.comap (Mdeg S m b).subtype
    (plus (symDeg (K := ℂ) m) (Mdeg S m) b)).liftQ Φ hker with hΦb
  have hinj : Function.Injective Φb := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H y =>
        rw [hΦb, Submodule.liftQ_apply, hΦ, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at hx
        rw [Submodule.Quotient.mk_eq_zero]
        change y.1 ∈ plus _ _ b
        have hy := projT_mem_plusM hx b
        change projT b y.1 ∈ _ at hy
        rwa [projT_of_isHomT y.2.2, if_pos rfl] at hy
  have hcyc : ∀ z (hz : z ∈ wordSpan (K := ℂ) S.f (m := m) S.c₀ b),
      (Submodule.Quotient.mk ⟨z, wordSpan_le_Mspace _ _ _ hz⟩ : FibM S m) ∈
        cycDeg (fiberRepM S m) (wM S m) b := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨l, hl, rfl⟩ := hv
        exact Submodule.subset_span ⟨l, hl, (wordOp_wM l).symm⟩
    | zero => exact Submodule.zero_mem _
    | add a c ha hc iha ihc =>
        have := Submodule.add_mem _ iha ihc
        rwa [← Submodule.Quotient.mk_add] at this
    | smul a v hv ihv =>
        have := Submodule.smul_mem _ a ihv
        rwa [← Submodule.Quotient.mk_smul] at this
  have hrange : LinearMap.range Φb ≤ cycDeg (fiberRepM S m) (wM S m) b := by
    rintro _ ⟨x, rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | H y =>
        rw [hΦb, Submodule.liftQ_apply, hΦ, LinearMap.comp_apply, Submodule.mkQ_apply]
        have hw := projT_mem_wordSpan S.f S.c₀ b y.2.1
        rw [projT_of_isHomT y.2.2, if_pos rfl] at hw
        exact hcyc y.1 hw
  have hfin : FiniteDimensional ℂ (cycDeg (fiberRepM S m) (wM S m) b) := by
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range Φb) ?_
    rw [cycDeg, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    rw [wordOp_wM]
    have hmem : applyWord S.f m l (deltaVec (K := ℂ) m S.c₀) ∈ Mdeg S m b :=
      ⟨applyWord_mem_Mspace l, by rw [← hl]; exact isHomT_applyWord S.f S.c₀ l⟩
    refine ⟨Submodule.Quotient.mk ⟨_, hmem⟩, ?_⟩
    rw [hΦb, Submodule.liftQ_apply, hΦ, LinearMap.comp_apply, Submodule.mkQ_apply]
    rfl
  calc fiberDim (symDeg (K := ℂ) m) (Mdeg S m) b
      = Module.finrank ℂ (LinearMap.range Φb) := (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ _ := Submodule.finrank_mono hrange

/-- **Total fibre dimension of `M_m` is at most `8^m`** (U5, total form). -/
theorem sum_fiberDimM_le (hU5 : FusionModuleBoundG S F) (B : ℕ) :
    ∑ b ∈ Finset.range B, fiberDim (symDeg (K := ℂ) m) (Mdeg S m) b ≤ S.n ^ m :=
  (Finset.sum_le_sum fun b _ => fiberDimM_le_cycDeg b).trans
    (hU5.total m (FibM S m) (fiberRepM S m) (wM S m) (localWeylRelM m) B)

/-! ## Generic rank: `8^m` independent elements of `M_m` -/

/-- **Cramer**: tensors whose values at a point form a nonzero multiple of the identity are
independent over `B_m`. -/
theorem linearIndependent_of_eval (w : (Fin m → Fin S.n) → TPs S m) (z0 : Fin (m + 0) → ℂ) (c : ℂ)
    (hc : c ≠ 0) (hw : ∀ t t', MvPolynomial.eval z0 (w t t') = if t' = t then c else 0) :
    LinearIndependent (SymAlg (K := ℂ) m) w := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg t
  let A : Matrix (Fin m → Fin S.n) (Fin m → Fin S.n) (Pm m) := fun t' t => w t t'
  let b : (Fin m → Fin S.n) → Pm m := fun t => (g t : Pm m)
  have hAb : A.mulVec b = 0 := by
    funext t'
    have := congrFun hg t'
    simp only [Finset.sum_apply, smul_apply_sym] at this
    simp only [Matrix.mulVec, dotProduct, A, b, Pi.zero_apply]
    rw [Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  have hdet : A.det ≠ 0 := by
    intro h0
    have h1 := congrArg (MvPolynomial.eval z0) h0
    rw [RingHom.map_det, map_zero] at h1
    have hmat : (MvPolynomial.eval z0).mapMatrix A = Matrix.diagonal fun _ => c := by
      ext t' t
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, A, hw, Matrix.diagonal_apply]
    rw [hmat, Matrix.det_diagonal, Finset.prod_const] at h1
    exact pow_ne_zero _ hc h1
  have hadj := congrArg (fun v => A.adjugate.mulVec v) hAb
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Matrix.smul_mulVec,
    Matrix.one_mulVec] at hadj
  have hbt := congrFun hadj t
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hbt
  have : (g t : Pm m) = 0 := (mul_eq_zero.mp hbt).resolve_left hdet
  exact Subtype.ext this

/-- `act` composes multiplicatively. -/
theorem act_act (g h : Equiv.Perm (Fin m)) (v : TPs S m) : act h (act g v) = act (h * g) v := by
  funext t
  simp only [act, rename_rename, Equiv.Perm.coe_mul]
  rfl

theorem symmetric_of_act {v : TPs S m} (hv : ∀ g, act g v = v) : Symmetric v := by
  intro e g he t
  have hfun : (⇑e : Fin (m + 0) → Fin (m + 0)) = ⇑g := by
    funext i
    have := he i
    exact this
  have h := congrFun (hv g.symm) t
  simp only [act] at h
  rw [hfun, ← h, rename_rename]
  simp

/-- The interpolating symmetric tensors. -/
def vt (t : Fin m → Fin S.n) : TPs S m := ∑ g : Equiv.Perm (Fin m), act g (lagr m • deltaT t)

theorem vt_symmetric (t : Fin m → Fin S.n) : Symmetric (vt t) := by
  apply symmetric_of_act
  intro h
  simp only [vt, act_sum, act_act]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => rfl

theorem eval_vt (t t' : Fin m → Fin S.n) :
    MvPolynomial.eval (z0 m) (vt t t') = if t' = t then 1 else 0 := by
  classical
  simp only [vt, Finset.sum_apply, map_sum, act, psmul_apply, eval_rename, map_mul]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin m))]
  · simp only [Equiv.Perm.coe_one, Function.comp_id, eval_lagr, one_mul, deltaT]
    split_ifs <;> simp
  · intro g _ hg
    rw [eval_lagr_perm g hg, zero_mul]
  · simp

/-- The `8^m` elements `Δ³ v_t` of `M_m`. -/
def wvec (t : Fin m → Fin S.n) : TPs S m := ((discS m : Pm m) ^ S.depth) • vt t

theorem wvec_mem (t : Fin m → Fin S.n) : wvec t ∈ Mspace S.f m S.c₀ :=
  mem_Mspace_of_symmetric (disc_pow_mem_MP _) (disc_symmetric_smul (vt_symmetric t))

theorem wvec_linearIndependent : LinearIndependent (SymAlg (K := ℂ) m) (wvec (S := S) (m := m)) := by
  refine linearIndependent_of_eval _ (z0 m) (MvPolynomial.eval (z0 m) (discS m : Pm m) ^ S.depth)
    (pow_ne_zero _ eval_disc_ne_zero) fun t t' => ?_
  simp only [wvec, psmul_apply, map_mul, map_pow, eval_vt]
  split_ifs <;> simp

/-! ## Finite generation and freeness -/

theorem tensor_eq_sum_projT (x : TPs S m) :
    ∃ D : ℕ, x = ∑ a ∈ Finset.range (D + 1), projT a x := by
  classical
  refine ⟨Finset.univ.sup fun t => (x t).totalDegree, ?_⟩
  funext t
  rw [Finset.sum_apply]
  change x t = ∑ a ∈ Finset.range _, homogeneousComponent a (x t)
  have hle : (x t).totalDegree ≤ Finset.univ.sup fun t => (x t).totalDegree :=
    Finset.le_sup (f := fun t => (x t).totalDegree) (Finset.mem_univ t)
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hle)) ?_]
  · exact (sum_homogeneousComponent (x t)).symm
  · intro a ha hna
    simp only [Finset.mem_range, not_lt] at ha hna
    exact homogeneousComponent_eq_zero _ _ (by omega)

/-- The fibre of `M_m` is nonzero in only finitely many degrees. -/
theorem fiberDimM_eventually_zero (hU5 : FusionModuleBoundG S F) :
    ∃ B0 : ℕ, ∀ b, B0 ≤ b → fiberDim (symDeg (K := ℂ) m) (Mdeg S m) b = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  -- choose `8^m + 1` distinct degrees with nonzero fibre
  have key : ∀ n : ℕ, ∃ B : ℕ, n ≤ ∑ b ∈ Finset.range B, fiberDim (symDeg (K := ℂ) m) (Mdeg S m) b := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
        obtain ⟨B, hB⟩ := ih
        obtain ⟨b, hb, hb0⟩ := hcon B
        refine ⟨b + 1, ?_⟩
        rw [Finset.sum_range_succ]
        have hsub : Finset.range B ⊆ Finset.range b := Finset.range_subset_range.mpr hb
        have := Finset.sum_le_sum_of_subset (f := fun b => fiberDim (symDeg (K := ℂ) m) (Mdeg S m) b)
          hsub
        have h1 : 1 ≤ fiberDim (symDeg (K := ℂ) m) (Mdeg S m) b := Nat.one_le_iff_ne_zero.mpr hb0
        simp only at this
        omega
  obtain ⟨B, hB⟩ := key (S.n ^ m + 1)
  have := sum_fiberDimM_le (m := m) hU5 B
  omega

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in -- a long assembly proof
/-- **B6 for one `m`**: `M_m` is a finite free `B_m`-module. -/
theorem mspace_basis (hU5 : FusionModuleBoundG S F) (m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (Module.Basis ι (SymAlg (K := ℂ) m) (MspaceR S m)) := by
  classical
  obtain ⟨B0, hB0⟩ := fiberDimM_eventually_zero (m := m) hU5
  choose C hC using fun b =>
    Submodule.exists_isCompl ((plus (symDeg (K := ℂ) m) (Mdeg S m) b).comap (Mdeg S m b).subtype)
  have hCdim : ∀ b, Module.finrank ℂ (C b) = fiberDim (symDeg (K := ℂ) m) (Mdeg S m) b := fun b =>
    (Submodule.quotientEquivOfIsCompl _ _ (hC b)).finrank_eq.symm
  let ι := Σ b : Fin B0, Fin (Module.finrank ℂ (C b))
  let gen : ι → TPs S m := fun p => (((Module.finBasis ℂ (C p.1)) p.2 : Mdeg S m p.1) : TPs S m)
  have gen_mem : ∀ p, gen p ∈ Mspace S.f m S.c₀ := fun p =>
    (((Module.finBasis ℂ (C p.1)) p.2 : Mdeg S m p.1)).2.1
  set SB := Submodule.span (SymAlg (K := ℂ) m) (Set.range gen) with hSB
  -- every complement vector lies in the span
  have hCmem : ∀ b (v : Mdeg S m b), v ∈ C b → (v : TPs S m) ∈ SB := by
    intro b v hv
    by_cases hb : b < B0
    · have hrepr := (Module.finBasis ℂ (C b)).sum_repr ⟨v, hv⟩
      have hcoe := congrArg (fun y : C b => ((y : Mdeg S m b) : TPs S m)) hrepr
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hcoe
      rw [← hcoe]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [← algebraMap_smul (SymAlg (K := ℂ) m)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨b, hb⟩, k⟩, rfl⟩)
    · have h0 : Module.finrank ℂ (C b) = 0 := by rw [hCdim]; exact hB0 b (by omega)
      have hbot : C b = ⊥ := Submodule.finrank_eq_zero.mp h0
      rw [hbot, Submodule.mem_bot] at hv
      rw [hv]
      exact Submodule.zero_mem _
  have hspanS : ∀ a, spanS (symDeg (K := ℂ) m) (Mdeg S m) C a ≤ SB.restrictScalars ℂ := by
    intro a
    rw [spanS, Submodule.span_le]
    rintro _ ⟨b, _, r, _, v, hv, rfl⟩
    exact SB.smul_mem r (hCmem b v hv)
  have hM : ∀ x ∈ Mspace S.f m S.c₀, x ∈ SB := by
    intro x hx
    obtain ⟨D, hD⟩ := tensor_eq_sum_projT x
    rw [hD]
    refine Submodule.sum_mem _ fun a _ => ?_
    exact hspanS a (le_spanS gradedActionM C hC a (projT_mem_Mdeg hx a))
  -- generators are independent
  have hcard : Fintype.card ι ≤ Fintype.card (Fin m → Fin S.n) := by
    rw [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    simp only [Fintype.card_fin, hCdim]
    rw [Fin.sum_univ_eq_sum_range (fun b => fiberDim (symDeg (K := ℂ) m) (Mdeg S m) b)]
    exact sum_fiberDimM_le hU5 B0
  have hli : LinearIndependent (SymAlg (K := ℂ) m) gen :=
    linearIndependent_of_span_card gen wvec wvec_linearIndependent
      (fun t => hM _ (wvec_mem t)) hcard
  let gen' : ι → MspaceR S m := fun p => ⟨gen p, gen_mem p⟩
  have hli' : LinearIndependent (SymAlg (K := ℂ) m) gen' :=
    LinearIndependent.of_comp (MspaceR S m).subtype hli
  have hsp : ⊤ ≤ Submodule.span (SymAlg (K := ℂ) m) (Set.range gen') := by
    rintro y -
    have hy := hM y.1 y.2
    have himg : (Set.range gen) = (MspaceR S m).subtype '' Set.range gen' := by
      rw [← Set.range_comp]; rfl
    rw [hSB, himg, Submodule.span_image] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := Subtype.ext hzy
    rwa [← this]
  exact ⟨ι, inferInstance, ⟨Module.Basis.mk hli' hsp⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **B6, proved from U5**: `M_m` is a finite free `B_m`-module for every `m`. -/
theorem mFreeness (hU5 : FusionModuleBoundG S F) : MFreenessG S := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · obtain ⟨ι, _, ⟨b⟩⟩ := mspace_basis hU5 m
    exact Module.Free.of_basis b
  · obtain ⟨ι, _, ⟨b⟩⟩ := mspace_basis hU5 m
    exact Module.Finite.of_basis b

end

end VOA.DeligneAudit.DeligneSector
