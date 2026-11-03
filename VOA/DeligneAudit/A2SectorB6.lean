/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorGeneric

/-!
# Step B6 for A₂: `M_m` is a finite free `B_m`-module

1. The fibre `M_m / B₊ M_m` is an `sl₃[t]`-module whose generator satisfies the local Weyl and
   fusion relations (the same computations as for `W_m`), so U5 in its total-dimension form bounds
   the Nakayama fibre dimensions of `M_m`: `Σ_b dim Fib(M)_b ≤ 8^m`.
2. Graded Nakayama: `M_m` is generated over `B_m` by at most `8^m` elements.
3. Generic rank: `M_m` contains `8^m` elements independent over `B_m` (Lagrange interpolation at
   a point with distinct coordinates, then `Δ³ N_sym ⊂ M_m`; independence by Cramer's rule).
4. Rank count: a generating family of size `≤ 8^m` of a module containing `8^m` independent
   elements is a basis.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial VOA.AffineSl3 VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.DeligneAudit.SectorGraded VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorNakayama VOA.QuadraticCurrentFunctionalCarrier

noncomputable section

variable {m : ℕ} {F : ℕ → PowerSeries ℚ}

/-! ## Degree pieces of `M_m` -/

/-- Homogeneous tensors of degree `b`. -/
def degT (m b : ℕ) : Submodule ℂ (TP m) where
  carrier := {x | IsHomT b x}
  zero_mem' := fun t => isHomogeneous_zero _ _ _
  add_mem' {x y} hx hy t := (hx t).add (hy t)
  smul_mem' c x hx t := by
    change (c • x t).IsHomogeneous b
    rw [← mem_homogeneousSubmodule] at *
    exact Submodule.smul_mem _ c (hx t)

instance (b : ℕ) : FiniteDimensional ℂ (degT m b) := by
  haveI : FiniteDimensional ℂ (MvPolynomial.homogeneousSubmodule (Fin (m + 0)) ℂ b) :=
    VOA.MvPolynomialFiniteHomogeneous.finiteDimensional_weightedHomogeneousSubmodule
      (fun _ => 1) (by intros; simp) b
  let g : degT m b →ₗ[ℂ] ((Fin m → Fin 8) → MvPolynomial.homogeneousSubmodule (Fin (m + 0)) ℂ b) :=
    { toFun := fun x t => ⟨x.1 t, (mem_homogeneousSubmodule _ _).mpr (x.2 t)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective g fun x y h => Subtype.ext (funext fun t => ?_)
  exact congrArg Subtype.val (congrFun h t)

/-- The degree-`b` part of `M_m`. -/
def Mdeg (m b : ℕ) : Submodule ℂ (TP m) := Mspace bracketTable m (5 : Fin 8) ⊓ degT m b

instance (b : ℕ) : FiniteDimensional ℂ (Mdeg m b) :=
  Submodule.finiteDimensional_of_le (S₂ := degT m b) inf_le_right

theorem projT_mem_Mdeg {x : TP m} (hx : x ∈ Mspace bracketTable m (5 : Fin 8)) (b : ℕ) :
    projT b x ∈ Mdeg m b :=
  ⟨wordSpan_le_Mspace _ _ _ (projT_mem_wordSpan _ _ _ hx), isHomT_projT b x⟩

theorem gradedActionM : GradedAction (symDeg (K := ℂ) m) (Mdeg m) where
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
    exact ⟨smul_mem_Mspace m r hx.1, fun t => hr'.mul (hx.2 t)⟩

/-! ## The fibre of `M_m` as a current-algebra module -/

theorem deltaVec_mem_Mspace (m : ℕ) : deltaVec (K := ℂ) m (5 : Fin 8) ∈ Mspace bracketTable m 5 :=
  Submodule.subset_span ⟨[], rfl⟩

/-- `B₊ M_m`. -/
def augM (m : ℕ) : Submodule ℂ (TP m) :=
  Submodule.span ℂ {z | ∃ n, 1 ≤ n ∧ ∃ s ∈ symDeg (K := ℂ) m n,
    ∃ y ∈ Mspace bracketTable m (5 : Fin 8), z = s • y}

theorem augM_le : augM m ≤ Mspace bracketTable m (5 : Fin 8) := by
  rw [augM, Submodule.span_le]
  rintro _ ⟨n, _, s, _, y, hy, rfl⟩
  exact smul_mem_Mspace m s hy

theorem loopOp_mem_augM (x : Fin 8) (r : ℕ) {z : TP m} (hz : z ∈ augM m) :
    loopOp bracketTable m x r z ∈ augM m := by
  induction hz using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨n, hn, s, hs, y, hy, rfl⟩ := hv
      rw [loopOp_smul]
      exact Submodule.subset_span ⟨n, hn, s, hs, _, loopOp_mem_Mspace x r hy, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- `M_m` as a type. -/
abbrev MsT (m : ℕ) := Mspace bracketTable m (5 : Fin 8)

/-- `B₊ M_m` inside `M_m`. -/
def augMW (m : ℕ) : Submodule ℂ (MsT m) := (augM m).comap (MsT m).subtype

/-- The fibre `M_m / B₊ M_m`. -/
abbrev FibM (m : ℕ) := MsT m ⧸ augMW m

/-- Loop operators on `M_m`. -/
def opMW (x : Fin 8) (r : ℕ) : MsT m →ₗ[ℂ] MsT m :=
  (loopOp bracketTable m x r).restrict fun _ hp => loopOp_mem_Mspace x r hp

/-- Loop operators on the fibre. -/
def opFM (x : Fin 8) (r : ℕ) : FibM m →ₗ[ℂ] FibM m :=
  (augMW m).mapQ (augMW m) (opMW x r) fun _z hz => loopOp_mem_augM x r hz

theorem opFM_mk (x : Fin 8) (r : ℕ) (y : MsT m) :
    opFM x r (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨loopOp bracketTable m x r y.1, loopOp_mem_Mspace x r y.2⟩ := rfl

/-- **The fibre of `M_m` is an `sl₃[t]`-module.** -/
def fiberRepM (m : ℕ) : CurrentModule bracketTable (FibM m) where
  op := opFM
  comm a b r s v := by
    induction v using Submodule.Quotient.induction_on with
    | H y =>
        simp only [opFM_mk]
        rw [← Submodule.Quotient.mk_sub]
        have h := loopOp_comm bracketTable jacobiCoord m a b r s y.1
        have hsum : ∀ (S : Finset (Fin 8)), (∑ e ∈ S, bracketTable a b e • (Submodule.Quotient.mk
            ⟨loopOp bracketTable m e (r + s) y.1, loopOp_mem_Mspace e (r + s) y.2⟩ : FibM m)) =
            Submodule.Quotient.mk ⟨∑ e ∈ S, bracketTable a b e • loopOp bracketTable m e (r + s) y.1,
              Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _
                (loopOp_mem_Mspace e (r + s) y.2)⟩ := by
          intro S
          induction S using Finset.induction_on with
          | empty => simp; rfl
          | insert e S he ih =>
              rw [Finset.sum_insert he, ih, ← Submodule.Quotient.mk_smul,
                ← Submodule.Quotient.mk_add]
              congr 1
              apply Subtype.ext
              simp [Finset.sum_insert he]
        rw [hsum]
        congr 1
        apply Subtype.ext
        simpa using h

/-- The fibre generator. -/
def wM (m : ℕ) : FibM m := Submodule.Quotient.mk ⟨deltaVec m 5, deltaVec_mem_Mspace m⟩

theorem applyWord_mem_Mspace (l : List (Fin 8 × ℕ)) :
    applyWord bracketTable m l (deltaVec (K := ℂ) m 5) ∈ Mspace bracketTable m (5 : Fin 8) :=
  Submodule.subset_span ⟨l, rfl⟩

theorem wordOp_wM (l : List (Fin 8 × ℕ)) :
    wordOp (fiberRepM m) l (wM m) =
      Submodule.Quotient.mk ⟨applyWord bracketTable m l (deltaVec m 5), applyWord_mem_Mspace l⟩ := by
  induction l with
  | nil => rfl
  | cons xs l ih =>
      change opFM xs.1 xs.2 (wordOp (fiberRepM m) l (wM m)) = _
      rw [ih, opFM_mk]
      rfl

/-! ## Relations and fibre dimensions -/

theorem mkM_eq_zero {v : TP m} (hv : v ∈ Mspace bracketTable m (5 : Fin 8)) (ha : v ∈ augM m) :
    (Submodule.Quotient.mk ⟨v, hv⟩ : FibM m) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ha

theorem opGenM (x : Fin 8) (r : ℕ) :
    (fiberRepM m).op x r (wM m) = Submodule.Quotient.mk
      ⟨loopOp bracketTable m x r (deltaVec m 5), loopOp_mem_Mspace x r (deltaVec_mem_Mspace m)⟩ :=
  rfl

theorem iterate_opGenM (k : ℕ) (x : Fin 8) :
    ((fiberRepM m).op x 0)^[k] (wM m) = Submodule.Quotient.mk
      ⟨applyWord bracketTable m (List.replicate k (x, 0)) (deltaVec m 5),
        applyWord_mem_Mspace _⟩ := by
  rw [← wordOp_wM]
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, List.replicate_succ]
      rfl

/-- **The generator of the fibre of `M_m` satisfies the local Weyl and fusion relations.** -/
theorem localWeylRelM (m : ℕ) : LocalWeylRel (fiberRepM m) (wM m) m where
  raising e he r := by
    rw [opGenM]
    apply mkM_eq_zero
    rw [loopOp_raising_deltaVec m e he r]
    exact Submodule.zero_mem _
  cartan_pos h hh r hr := by
    rw [opGenM]
    apply mkM_eq_zero
    rw [loopOp_cartan_deltaVec m h hh r]
    exact Submodule.subset_span ⟨r, hr, psumS m r, psumS_mem m r, deltaVec m 5,
      deltaVec_mem_Mspace m, rfl⟩
  cartan_zero h hh := by
    rw [opGenM]
    change _ = (m : ℂ) • Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    change loopOp bracketTable m h 0 (deltaVec m 5) = (m : ℂ) • deltaVec m 5
    rw [loopOp_cartan_deltaVec m h hh 0]
    funext t
    rw [smul_apply_sym, Pi.smul_apply, smul_eq_C_mul]
    congr 1
    simp [psumS, psum]
  lowering_f1 := by
    rw [iterate_opGenM]
    apply mkM_eq_zero
    rw [applyWord_replicate, suppW_eq_zero (iterate_suppW m (m + 1) 3) (no_weight_f1 m)]
    exact Submodule.zero_mem _
  lowering_f2 := by
    rw [iterate_opGenM]
    apply mkM_eq_zero
    rw [applyWord_replicate, suppW_eq_zero (iterate_suppW m (m + 1) 4) (no_weight_f2 m)]
    exact Submodule.zero_mem _
  fusion fα _ _ := by
    rw [opGenM]
    apply mkM_eq_zero
    rw [loopOp_vieta]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨j, (Finset.mem_Ico.mp hj).1, esymmS m j, esymmS_mem m j, _,
      loopOp_mem_Mspace fα (m - j) (deltaVec_mem_Mspace m), rfl⟩

theorem projT_mem_plusM {z : TP m} (hz : z ∈ augM m) (b : ℕ) :
    projT b z ∈ plus (symDeg (K := ℂ) m) (Mdeg m) b := by
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

theorem plus_le_augM (b : ℕ) : plus (symDeg (K := ℂ) m) (Mdeg m) b ≤ augM m := by
  rw [plus, Submodule.span_le]
  rintro _ ⟨n, hn, _, r, hr, y, hy, rfl⟩
  exact Submodule.subset_span ⟨n, hn, r, hr, y, hy.1, rfl⟩

/-- **Fibre dimension of `M_m` ≤ loop span of the fibre generator.** -/
theorem fiberDimM_le_cycDeg (b : ℕ) :
    fiberDim (symDeg (K := ℂ) m) (Mdeg m) b ≤
      Module.finrank ℂ (cycDeg (fiberRepM m) (wM m) b) := by
  classical
  set Φ : Mdeg m b →ₗ[ℂ] FibM m :=
    (augMW m).mkQ ∘ₗ Submodule.inclusion (inf_le_left : Mdeg m b ≤ _) with hΦ
  have hker : (plus (symDeg (K := ℂ) m) (Mdeg m) b).comap (Mdeg m b).subtype ≤
      LinearMap.ker Φ := by
    intro x hx
    rw [LinearMap.mem_ker, hΦ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact plus_le_augM b hx
  set Φb := (Submodule.comap (Mdeg m b).subtype
    (plus (symDeg (K := ℂ) m) (Mdeg m) b)).liftQ Φ hker with hΦb
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
  have hcyc : ∀ z (hz : z ∈ wordSpan (K := ℂ) bracketTable (m := m) 5 b),
      (Submodule.Quotient.mk ⟨z, wordSpan_le_Mspace _ _ _ hz⟩ : FibM m) ∈
        cycDeg (fiberRepM m) (wM m) b := by
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
  have hrange : LinearMap.range Φb ≤ cycDeg (fiberRepM m) (wM m) b := by
    rintro _ ⟨x, rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | H y =>
        rw [hΦb, Submodule.liftQ_apply, hΦ, LinearMap.comp_apply, Submodule.mkQ_apply]
        have hw := projT_mem_wordSpan bracketTable 5 b y.2.1
        rw [projT_of_isHomT y.2.2, if_pos rfl] at hw
        exact hcyc y.1 hw
  have hfin : FiniteDimensional ℂ (cycDeg (fiberRepM m) (wM m) b) := by
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range Φb) ?_
    rw [cycDeg, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    rw [wordOp_wM]
    have hmem : applyWord bracketTable m l (deltaVec (K := ℂ) m 5) ∈ Mdeg m b :=
      ⟨applyWord_mem_Mspace l, by rw [← hl]; exact isHomT_applyWord bracketTable 5 l⟩
    refine ⟨Submodule.Quotient.mk ⟨_, hmem⟩, ?_⟩
    rw [hΦb, Submodule.liftQ_apply, hΦ, LinearMap.comp_apply, Submodule.mkQ_apply]
    rfl
  calc fiberDim (symDeg (K := ℂ) m) (Mdeg m) b
      = Module.finrank ℂ (LinearMap.range Φb) := (LinearMap.finrank_range_of_inj hinj).symm
    _ ≤ _ := Submodule.finrank_mono hrange

/-- **Total fibre dimension of `M_m` is at most `8^m`** (U5, total form). -/
theorem sum_fiberDimM_le (hU5 : FusionModuleBound F) (B : ℕ) :
    ∑ b ∈ Finset.range B, fiberDim (symDeg (K := ℂ) m) (Mdeg m) b ≤ 8 ^ m :=
  (Finset.sum_le_sum fun b _ => fiberDimM_le_cycDeg b).trans
    (hU5.total m (FibM m) (fiberRepM m) (wM m) (localWeylRelM m) B)

/-! ## Rank count over a domain -/

section RankCount

variable {R V : Type*} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V]

/-- **A finite spanning family of a module containing as many independent vectors is
independent** (over a commutative domain). -/
theorem linearIndependent_of_span_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    (gen : ι → V) (v : κ → V) (hv : LinearIndependent R v)
    (hspan : ∀ k, v k ∈ Submodule.span R (Set.range gen))
    (hcard : Fintype.card ι ≤ Fintype.card κ) : LinearIndependent R gen := by
  classical
  by_contra hdep
  obtain ⟨c, hc, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hdep
  -- the reduced generating set
  let w : Finset V := (Finset.univ.erase i0).image gen
  have hcoef : ∀ k, ∃ a : ι → R, ∑ i, a i • gen i = v k := fun k =>
    (Submodule.mem_span_range_iff_exists_fun R).mp (hspan k)
  choose a ha using hcoef
  have hw : ∀ k, c i0 • v k ∈ Submodule.span R (w : Set V) := by
    intro k
    have hrel : c i0 • gen i0 = -∑ i ∈ Finset.univ.erase i0, c i • gen i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)] at hc
      exact eq_neg_of_add_eq_zero_left hc
    have : c i0 • v k = ∑ i ∈ Finset.univ.erase i0, (c i0 * a k i - a k i0 * c i) • gen i := by
      rw [← ha k, Finset.smul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
      rw [smul_smul, mul_comm, ← smul_smul, hrel]
      simp only [smul_neg, Finset.smul_sum, smul_smul, sub_smul, Finset.sum_sub_distrib]
      rw [neg_add_eq_sub]
    rw [this]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem gen hi)
  have hind : LinearIndependent R fun k => c i0 • v k := by
    rw [Fintype.linearIndependent_iff] at hv ⊢
    intro g hg k
    have := hv (fun k => g k * c i0) (by
      rw [← hg]; refine Finset.sum_congr rfl fun k _ => ?_; rw [smul_smul])
    exact (mul_eq_zero.mp (this k)).resolve_right hi0
  have hle := linearIndependent_le_span_aux' (fun k => c i0 • v k) hind (w : Set V)
    (by rintro _ ⟨k, rfl⟩; exact hw k)
  have hwcard : Fintype.card (w : Set V) ≤ Fintype.card ι - 1 := by
    have : Fintype.card (w : Set V) = w.card := by simp
    rw [this]
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i0⟩
  omega

end RankCount

/-! ## Generic rank: `8^m` independent elements of `M_m` -/

/-- **Cramer**: tensors whose values at a point form a nonzero multiple of the identity are
independent over `B_m`. -/
theorem linearIndependent_of_eval (w : (Fin m → Fin 8) → TP m) (z0 : Fin (m + 0) → ℂ) (c : ℂ)
    (hc : c ≠ 0) (hw : ∀ t t', MvPolynomial.eval z0 (w t t') = if t' = t then c else 0) :
    LinearIndependent (SymAlg (K := ℂ) m) w := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg t
  let A : Matrix (Fin m → Fin 8) (Fin m → Fin 8) (Pm m) := fun t' t => w t t'
  let b : (Fin m → Fin 8) → Pm m := fun t => (g t : Pm m)
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
theorem act_act (g h : Equiv.Perm (Fin m)) (v : TP m) : act h (act g v) = act (h * g) v := by
  funext t
  simp only [act, rename_rename, Equiv.Perm.coe_mul]
  rfl

theorem symmetric_of_act {v : TP m} (hv : ∀ g, act g v = v) : Symmetric v := by
  intro e g he t
  have hfun : (⇑e : Fin (m + 0) → Fin (m + 0)) = ⇑g := by
    funext i
    have := he i
    exact this
  have h := congrFun (hv g.symm) t
  simp only [act] at h
  rw [hfun, ← h, rename_rename]
  simp

/-- A point with distinct coordinates. -/
def z0 (m : ℕ) : Fin (m + 0) → ℂ := fun i => ((i : ℕ) : ℂ)

theorem z0_injective : Function.Injective (z0 m) := by
  intro i j h
  simp only [z0, Nat.cast_inj] at h
  exact Fin.ext h

/-- The Lagrange polynomial: `1` at `z0`, `0` at every other permutation of `z0`. -/
def lagr (m : ℕ) : Pm m :=
  ∏ i : Fin (m + 0), ∏ j : Fin (m + 0),
    if j = i then 1 else MvPolynomial.C ((z0 m i - z0 m j)⁻¹) * (X i - MvPolynomial.C (z0 m j))

theorem eval_lagr : MvPolynomial.eval (z0 m) (lagr m) = 1 := by
  simp only [lagr, map_prod]
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs with h
  · simp
  · have : z0 m i - z0 m j ≠ 0 := sub_ne_zero.mpr (z0_injective.ne (Ne.symm h))
    simp [inv_mul_cancel₀ this]

theorem eval_lagr_perm (g : Equiv.Perm (Fin m)) (hg : g ≠ 1) :
    MvPolynomial.eval (z0 m ∘ g) (lagr m) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, g i ≠ i := by
    by_contra h
    exact hg (Equiv.ext fun i => by by_contra hi; exact h ⟨i, hi⟩)
  simp only [lagr, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (i : Fin (m + 0)))
  apply Finset.prod_eq_zero (Finset.mem_univ (g i : Fin (m + 0)))
  rw [if_neg hi]
  simp

/-- The interpolating symmetric tensors. -/
def vt (t : Fin m → Fin 8) : TP m := ∑ g : Equiv.Perm (Fin m), act g (lagr m • deltaT t)

theorem vt_symmetric (t : Fin m → Fin 8) : Symmetric (vt t) := by
  apply symmetric_of_act
  intro h
  simp only [vt, act_sum, act_act]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => rfl

theorem eval_vt (t t' : Fin m → Fin 8) :
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
def wvec (t : Fin m → Fin 8) : TP m := ((discS m : Pm m) ^ 3) • vt t

theorem wvec_mem (t : Fin m → Fin 8) : wvec t ∈ Mspace bracketTable m (5 : Fin 8) :=
  mem_Mspace_of_symmetric (disc_cube_mem_MP _) (disc_symmetric_smul (vt_symmetric t))

theorem eval_disc_ne_zero : MvPolynomial.eval (z0 m) (discS m : Pm m) ≠ 0 := by
  simp only [discS, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  split_ifs with h
  · simp
  · simpa [sub_eq_zero] using z0_injective.ne h

theorem wvec_linearIndependent : LinearIndependent (SymAlg (K := ℂ) m) (wvec (m := m)) := by
  refine linearIndependent_of_eval _ (z0 m) (MvPolynomial.eval (z0 m) (discS m : Pm m) ^ 3)
    (pow_ne_zero _ eval_disc_ne_zero) fun t t' => ?_
  simp only [wvec, psmul_apply, map_mul, map_pow, eval_vt]
  split_ifs <;> simp

/-! ## Finite generation and freeness -/

theorem tensor_eq_sum_projT (x : TP m) :
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
theorem fiberDimM_eventually_zero (hU5 : FusionModuleBound F) :
    ∃ B0 : ℕ, ∀ b, B0 ≤ b → fiberDim (symDeg (K := ℂ) m) (Mdeg m) b = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  -- choose `8^m + 1` distinct degrees with nonzero fibre
  have key : ∀ n : ℕ, ∃ B : ℕ, n ≤ ∑ b ∈ Finset.range B, fiberDim (symDeg (K := ℂ) m) (Mdeg m) b := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
        obtain ⟨B, hB⟩ := ih
        obtain ⟨b, hb, hb0⟩ := hcon B
        refine ⟨b + 1, ?_⟩
        rw [Finset.sum_range_succ]
        have hsub : Finset.range B ⊆ Finset.range b := Finset.range_subset_range.mpr hb
        have := Finset.sum_le_sum_of_subset (f := fun b => fiberDim (symDeg (K := ℂ) m) (Mdeg m) b)
          hsub
        have h1 : 1 ≤ fiberDim (symDeg (K := ℂ) m) (Mdeg m) b := Nat.one_le_iff_ne_zero.mpr hb0
        simp only at this
        omega
  obtain ⟨B, hB⟩ := key (8 ^ m + 1)
  have := sum_fiberDimM_le (m := m) hU5 B
  omega

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in -- a long assembly proof
/-- **B6 for one `m`**: `M_m` is a finite free `B_m`-module. -/
theorem mspace_basis (hU5 : FusionModuleBound F) (m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (Module.Basis ι (SymAlg (K := ℂ) m) (MspaceR m)) := by
  classical
  obtain ⟨B0, hB0⟩ := fiberDimM_eventually_zero (m := m) hU5
  choose C hC using fun b =>
    Submodule.exists_isCompl ((plus (symDeg (K := ℂ) m) (Mdeg m) b).comap (Mdeg m b).subtype)
  have hCdim : ∀ b, Module.finrank ℂ (C b) = fiberDim (symDeg (K := ℂ) m) (Mdeg m) b := fun b =>
    (Submodule.quotientEquivOfIsCompl _ _ (hC b)).finrank_eq.symm
  let ι := Σ b : Fin B0, Fin (Module.finrank ℂ (C b))
  let gen : ι → TP m := fun p => (((Module.finBasis ℂ (C p.1)) p.2 : Mdeg m p.1) : TP m)
  have gen_mem : ∀ p, gen p ∈ Mspace bracketTable m (5 : Fin 8) := fun p =>
    (((Module.finBasis ℂ (C p.1)) p.2 : Mdeg m p.1)).2.1
  set SB := Submodule.span (SymAlg (K := ℂ) m) (Set.range gen) with hSB
  -- every complement vector lies in the span
  have hCmem : ∀ b (v : Mdeg m b), v ∈ C b → (v : TP m) ∈ SB := by
    intro b v hv
    by_cases hb : b < B0
    · have hrepr := (Module.finBasis ℂ (C b)).sum_repr ⟨v, hv⟩
      have hcoe := congrArg (fun y : C b => ((y : Mdeg m b) : TP m)) hrepr
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
  have hspanS : ∀ a, spanS (symDeg (K := ℂ) m) (Mdeg m) C a ≤ SB.restrictScalars ℂ := by
    intro a
    rw [spanS, Submodule.span_le]
    rintro _ ⟨b, _, r, _, v, hv, rfl⟩
    exact SB.smul_mem r (hCmem b v hv)
  have hM : ∀ x ∈ Mspace bracketTable m (5 : Fin 8), x ∈ SB := by
    intro x hx
    obtain ⟨D, hD⟩ := tensor_eq_sum_projT x
    rw [hD]
    refine Submodule.sum_mem _ fun a _ => ?_
    exact hspanS a (le_spanS gradedActionM C hC a (projT_mem_Mdeg hx a))
  -- generators are independent
  have hcard : Fintype.card ι ≤ Fintype.card (Fin m → Fin 8) := by
    rw [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    simp only [Fintype.card_fin, hCdim]
    rw [Fin.sum_univ_eq_sum_range (fun b => fiberDim (symDeg (K := ℂ) m) (Mdeg m) b)]
    exact sum_fiberDimM_le hU5 B0
  have hli : LinearIndependent (SymAlg (K := ℂ) m) gen :=
    linearIndependent_of_span_card gen wvec wvec_linearIndependent
      (fun t => hM _ (wvec_mem t)) hcard
  let gen' : ι → MspaceR m := fun p => ⟨gen p, gen_mem p⟩
  have hli' : LinearIndependent (SymAlg (K := ℂ) m) gen' :=
    LinearIndependent.of_comp (MspaceR m).subtype hli
  have hsp : ⊤ ≤ Submodule.span (SymAlg (K := ℂ) m) (Set.range gen') := by
    rintro y -
    have hy := hM y.1 y.2
    have himg : (Set.range gen) = (MspaceR m).subtype '' Set.range gen' := by
      rw [← Set.range_comp]; rfl
    rw [hSB, himg, Submodule.span_image] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := Subtype.ext hzy
    rwa [← this]
  exact ⟨ι, inferInstance, ⟨Module.Basis.mk hli' hsp⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **B6, proved from U5**: `M_m` is a finite free `B_m`-module for every `m`. -/
theorem mFreeness (hU5 : FusionModuleBound F) : MFreeness := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · obtain ⟨ι, _, ⟨b⟩⟩ := mspace_basis hU5 m
    exact Module.Free.of_basis b
  · obtain ⟨ι, _, ⟨b⟩⟩ := mspace_basis hU5 m
    exact Module.Finite.of_basis b

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.fiberDimM_le_cycDeg
#print axioms VOA.DeligneAudit.A2.linearIndependent_of_span_card
#print axioms VOA.DeligneAudit.A2.wvec_linearIndependent
#print axioms VOA.DeligneAudit.A2.mFreeness
end AxiomAudit
