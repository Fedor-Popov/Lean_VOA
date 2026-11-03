import VOA.Examples.LatticeReconstruct
import VOA.Examples.LatticeGrading
import VOA.Examples.HeisenbergNVOA
import VOA.Core.VertexOperatorAlgebra

open VOA VOA.LatExp VOA.LatticeVOA
open Module (End)
open HeisenbergN (FockN oscN vacuumN gradingWN gradingZN)
open scoped TensorProduct BigOperators
open MvPolynomial

namespace VOA.LatExp

/-! ## STAGE 3 — the lattice A₁ vertex operator algebra (central charge 1), gated on `hYloc`. -/

/-- The lattice conformal vector `ω = ωN 1 2 ⊗ e^0` (the boson Sugawara state in charge sector 0). -/
noncomputable def omegaLat : LatModule := mkE 0 (HeisenbergN.ωN 1 2)

/-! ### The reconstructed all-states map and its six properties (gated on `hYloc`). -/

variable (hYloc : ∀ m m' : ℤ, Local (Yemα m) (Yemα m'))

/-- The reconstructed lattice vertex map `Yfull`. -/
noncomputable def Yfull : LatModule →ₗ[ℂ] FormalDist (End ℂ LatModule) :=
  (latYfull_of_locality hYloc).choose

theorem Yfull_word (l : List ℕ) (m : ℤ) : Yfull hYloc (wordStateLat l m) = YwordLat l m :=
  (latYfull_of_locality hYloc).choose_spec.1 (l, m)

theorem Yfull_isField (u : LatModule) : IsField (Yfull hYloc u) :=
  (latYfull_of_locality hYloc).choose_spec.2.1 u

theorem Yfull_local (u v : LatModule) : Local (Yfull hYloc u) (Yfull hYloc v) :=
  (latYfull_of_locality hYloc).choose_spec.2.2.1 u v

theorem Yfull_cre0 (u : LatModule) : (Yfull hYloc u) 0 latVacuum = u :=
  (latYfull_of_locality hYloc).choose_spec.2.2.2.1 u

theorem Yfull_creneg (u : LatModule) {q : ℤ} (hq : q < 0) : (Yfull hYloc u) q latVacuum = 0 :=
  (latYfull_of_locality hYloc).choose_spec.2.2.2.2.1 u q hq

theorem Yfull_DCov (u : LatModule) : Reconstruction.DCovariant Trec (Yfull hYloc u) :=
  (latYfull_of_locality hYloc).choose_spec.2.2.2.2.2 u

/-! ## VA2 — the vacuum field is the unit: `Yfull latVacuum = 1` via `Yemα 0 = 1`. -/

/-- `cSchurC 0 (N+1) = 0`. -/
theorem cSchurC0_succ (N : ℕ) : cSchurC 0 (N + 1) = 0 := by rw [cSchurC_succ]; simp

/-- `aExpC 0 (N+1) = 0`. -/
theorem aExpC0_succ (N : ℕ) : aExpC 0 (N + 1) = 0 := by rw [aExpC_succ]; simp

/-- `EminusC 0 t = if t = 0 then id else 0`. -/
theorem EminusC0i (t : ℤ) : EminusC 0 t = if t = 0 then (LinearMap.id : End ℂ B) else 0 := by
  rw [EminusC_apply]
  by_cases h : 0 ≤ t
  · rw [if_pos h]
    by_cases h0 : t = 0
    · subst h0; simp only [Int.toNat_zero, EminusOpC, cSchurC_zero]; ext x; simp
    · obtain ⟨K, hK⟩ : ∃ K : ℕ, t.toNat = K + 1 := ⟨t.toNat - 1, by omega⟩
      rw [if_neg h0, hK, EminusOpC, cSchurC0_succ]; ext x; simp
  · rw [if_neg h, if_neg (by omega : ¬ t = 0)]

/-- `aExpC 0 N = if N = 0 then id else 0`. -/
theorem aExpC0 (N : ℕ) : aExpC 0 N = if N = 0 then (LinearMap.id : End ℂ B) else 0 := by
  match N with
  | 0 => rw [aExpC_zero, if_pos rfl]
  | (K + 1) => rw [aExpC0_succ, if_neg (by omega)]

/-- `EplusC 0 t = if t = 0 then id else 0`. -/
theorem EplusC0i (t : ℤ) : EplusC 0 t = if t = 0 then (LinearMap.id : End ℂ B) else 0 := by
  rw [EplusC_apply]
  by_cases h : t ≤ 0
  · rw [if_pos h, aExpC0]
    by_cases h0 : t = 0
    · subst h0; simp
    · rw [if_neg (by omega : ¬ (-t).toNat = 0), if_neg h0]
  · rw [if_neg h, if_neg (by omega : ¬ t = 0)]

/-- `EEC 0 t x = if t = 0 then x else 0`. -/
theorem EEC0i (t : ℤ) (x : B) : EEC 0 t x = if t = 0 then x else 0 := by
  rw [EEC_apply_conv 0 t x]
  have hsupp : ∀ m : ℤ, m ≠ 0 → EminusC 0 m (EplusC 0 (t - m) x) = 0 := by
    intro m hm; rw [EminusC0i, if_neg hm, LinearMap.zero_apply]
  rw [finsum_eq_single _ (0 : ℤ) hsupp, EminusC0i, if_pos rfl, EplusC0i]
  by_cases h0 : t = 0
  · subst h0; simp
  · rw [if_neg (by omega : ¬ t - 0 = 0), if_neg h0, LinearMap.zero_apply, map_zero]

/-- `Yemα 0 = 1` (the charge-0 vertex operator is the identity field). -/
theorem Yemα_zero_apply (t : ℤ) (y : LatModule) :
    Yemα 0 t y = if t = 0 then y else 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; split_ifs <;> rfl
  | add y1 y2 h1 h2 => rw [map_add, h1, h2]; split_ifs <;> simp
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero]; rw [map_zero]; split_ifs <;> rfl
      | add g1 g2 h1 h2 =>
          erw [TensorProduct.tmul_add]; rw [map_add, h1, h2]; split_ifs <;> simp
      | single k a =>
          rw [(Finsupp.smul_single_one k a).symm,
            show (Finsupp.single k 1 : LatGrp) = eVec k from rfl]
          erw [TensorProduct.tmul_smul, map_smul, Yemα_tmul]
          rw [show (t - 2 * 0 * k : ℤ) = t from by ring,
            show ((0 : ℤ) : ℂ) = (0 : ℂ) from by norm_num, EEC0i,
            show k + (0 : ℤ) = k from by ring]
          by_cases ht : t = 0
          · rw [if_pos ht, if_pos ht]
          · rw [if_neg ht, if_neg ht, TensorProduct.zero_tmul, smul_zero]

theorem Yemα_zero_eq_one : (Yemα 0 : FormalDist (End ℂ LatModule)) = (1 : (End ℂ LatModule)⟦z^±⟧) := by
  funext t
  refine LinearMap.ext fun y => ?_
  have h1 : (1 : (End ℂ LatModule)⟦z^±⟧) t y = if t = 0 then y else 0 := by
    rw [FormalDist.one_apply]; split_ifs with ht
    · rw [Module.End.one_apply]
    · rw [LinearMap.zero_apply]
  rw [Yemα_zero_apply]; exact h1.symm

/-- **VA2**: `Yfull latVacuum = 1`. -/
theorem Yfull_vacuum : Yfull hYloc latVacuum = (1 : (End ℂ LatModule)⟦z^±⟧) := by
  rw [show latVacuum = wordStateLat [] 0 from rfl, Yfull_word, YwordLat_nil, Yemα_zero_eq_one]

/-! ## ω — the conformal vector: `Yfull ω = sugField` and `ω ∈ gradingLat 2`. -/

/-- `sugField` is `Trec`-covariant (lift the boson generator covariance through `nprod`/scaling). -/
theorem sugField_DCovariant : Reconstruction.DCovariant Trec sugField := by
  rw [sugField]
  exact Reconstruction.DCovariant.smul _
    (Reconstruction.DCovariant.nprod alphaLat_isField alphaLat_isField
      Trec_alphaLat_DCovariant Trec_alphaLat_DCovariant)

/-- `sugField` annihilates the vacuum below degree `0`. -/
theorem sugField_vacuum_neg {q : ℤ} (hq : q < 0) : (sugField) q latVacuum = 0 := by
  rw [sugField]
  change (1 / 4 : ℂ) • (nprod alphaLat_isField alphaLat_isField q) latVacuum = 0
  rw [nprod_vacuum_neg_gen alphaLat_isField alphaLat_isField latVacuum
    (fun s hs => alphaLat_vacuum_neg hs) (fun s hs => alphaLat_vacuum_neg hs) hq, smul_zero]

/-- `sugField` is local with every word field (Dong over the boson generator `αLat = genFieldLat 0`). -/
theorem sugField_local_YwordLat (l : List ℕ) (m : ℤ) : Local sugField (YwordLat l m) := by
  rw [sugField]
  refine VertexOperatorAlgebra.Local.smul' _ ?_
  refine dong_neg alphaLat_isField alphaLat_isField latticeA1_alpha_local ?_ ?_
  · rw [← genFieldLat_zero]; exact genFieldLat_local_YwordLat l m 0
  · rw [← genFieldLat_zero]; exact genFieldLat_local_YwordLat l m 0

/-- **`Yfull ω = sugField`**: the field of the conformal vector is the lattice Sugawara field
(operator-first uniqueness via the shared vacuum tower). -/
theorem Yfull_omega_eq : Yfull hYloc omegaLat = sugField := by
  have hloc : ∀ l : List ℕ, ∀ m : ℤ,
      Local (Yfull hYloc omegaLat - sugField) (YwordLat l m) := by
    intro l m
    have h1 : Local (Yfull hYloc omegaLat) (YwordLat l m) := by
      rw [← Yfull_word hYloc l m]; exact Yfull_local hYloc omegaLat (wordStateLat l m)
    have h2 : Local sugField (YwordLat l m) := sugField_local_YwordLat l m
    rw [sub_eq_add_neg, ← neg_one_smul ℂ sugField]
    exact Reconstruction.Local.add_left h1 (VertexOperatorAlgebra.Local.smul' (-1) h2)
  have hbase : (Yfull hYloc omegaLat) 0 latVacuum = (sugField) 0 latVacuum := by
    rw [Yfull_cre0]
    have : (sugField) 0 latVacuum = omegaLat := by
      rw [sugField]
      change (1 / 4 : ℂ) • (nprod alphaLat_isField alphaLat_isField 0) latVacuum = omegaLat
      rw [nprod_vacuum_base_gen alphaLat_isField alphaLat_isField latVacuum
        (fun s hs => alphaLat_vacuum_neg hs) (fun s hs => alphaLat_vacuum_neg hs)]
      -- `alphaLat 0 = rTensor (alphaField 0)` (index 0 ≠ -1, no momentum term)
      have ha0 : alphaLat 0 = LinearMap.rTensor LatGrp (alphaField 0) := by
        change LinearMap.rTensor LatGrp (alphaField 0) + (if (0 : ℤ) = -1 then zGradeOp else 0)
          = LinearMap.rTensor LatGrp (alphaField 0)
        rw [if_neg (by norm_num), add_zero]
      rw [ha0]
      -- now `(1/4) • rTensor(αField 0) (rTensor(αField 0) latVacuum) = omegaLat`
      change (1 / 4 : ℂ) • LinearMap.rTensor LatGrp (alphaField 0)
        (LinearMap.rTensor LatGrp (alphaField 0) ((1 : HeisenbergN.FockN 1) ⊗ₜ[ℂ] eVec 0)) = _
      rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, omegaLat, mkE_apply,
        TensorProduct.smul_tmul']
      congr 1
      -- `(1/4) • αField 0 (αField 0 1) = ωN 1 2`
      simp only [alphaField_apply, show (-(0 : ℤ) - 1) = -1 from by ring]
      rw [HeisenbergN.ωN, Fin.sum_univ_one, HeisenbergN.ωNa,
        show (1 / 4 : ℂ) = (1 / (2 * 2) : ℂ) from by norm_num,
        show (α (-1) (α (-1) (1 : HeisenbergN.FockN 1)))
          = HeisenbergN.oscN 1 2 0 (-1) (HeisenbergN.oscN 1 2 0 (-1) (HeisenbergN.vacuumN 1)) from rfl]
    rw [this]
  have hAvac : ∀ p : ℤ, (Yfull hYloc omegaLat - sugField) p latVacuum = 0 := by
    intro p
    show ((Yfull hYloc omegaLat) p - (sugField) p) latVacuum = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact Reconstruction.tower_unique (Yfull_DCov hYloc omegaLat) sugField_DCovariant
      Trec_vacuum hbase
      (fun q hq => Yfull_creneg hYloc omegaLat hq)
      (fun q hq => sugField_vacuum_neg hq) p
  have hz := Reconstruction.field_eq_zero_of_vacuum latVacuum
    (Yfull hYloc omegaLat - sugField) (Function.uncurry wordStateLat)
    (Function.uncurry (fun l m => YwordLat l m))
    (fun lm => hloc lm.1 lm.2)
    (fun lm => YwordLat_vacuum_base lm.1 lm.2)
    (fun lm q hq => YwordLat_vacuum_neg lm.1 lm.2 hq)
    hAvac wordStateLat_span
  rwa [sub_eq_zero] at hz

/-! ## The lift–`nprod` interchange and the Sugawara mode decomposition. -/

/-- `liftF` carries `normalOrdered` of two boson fields to `normalOrdered` of their lifts. -/
theorem normalOrdered_liftF (a b : FormalDist (End ℂ B)) (m n : ℤ) :
    normalOrdered (liftF a) (liftF b) m n = LinearMap.rTensor LatGrp (normalOrdered a b m n) := by
  rw [normalOrdered_apply, normalOrdered_apply]
  by_cases h : 0 ≤ m
  · rw [if_pos h, if_pos h]; change LinearMap.rTensor LatGrp (a m) * LinearMap.rTensor LatGrp (b n)
      = LinearMap.rTensor LatGrp (a m * b n)
    rw [rTensor_mul]
  · rw [if_neg h, if_neg h]; change LinearMap.rTensor LatGrp (b n) * LinearMap.rTensor LatGrp (a m)
      = LinearMap.rTensor LatGrp (b n * a m)
    rw [rTensor_mul]

/-- **The lift–`nprod` interchange**: `nprod (liftF a) (liftF b) = liftF (nprod a b)`. -/
theorem liftF_nprod {a b : FormalDist (End ℂ B)} (ha : IsField a) (hb : IsField b) :
    nprod (IsField_liftF ha) (IsField_liftF hb) = liftF (nprod ha hb) := by
  funext s
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; change liftF (nprod ha hb) s 0 = 0; rw [map_zero]
  | add x y hx hy =>
      rw [map_add, hx, hy]; change _ = liftF (nprod ha hb) s (x + y)
      rw [map_add]
  | tmul p g =>
      rw [nprod_apply]
      change _ = LinearMap.rTensor LatGrp (nprod ha hb s) (p ⊗ₜ[ℂ] g)
      rw [show (nprod ha hb s) = nprodCoeff ha hb s from rfl,
        LinearMap.rTensor_tmul LatGrp (nprodCoeff ha hb s) g p,
        show (nprodCoeff ha hb s p) = ∑ᶠ m : ℤ, normalOrdered a b m (s - m) p from rfl]
      -- LHS finsum: each term lifts to `(NO a b m (s-m) p) ⊗ g`
      have hfin : (Function.support
          (fun m : ℤ => normalOrdered a b m (s - m) p)).Finite :=
        normalOrdered_diag_support_finite ha hb s p
      rw [finsum_congr (fun m => by
        rw [show normalOrdered (liftF a) (liftF b) m (s - m) (p ⊗ₜ[ℂ] g)
            = LinearMap.rTensor LatGrp (normalOrdered a b m (s - m)) (p ⊗ₜ[ℂ] g) from by
              rw [normalOrdered_liftF a b m (s - m)],
          LinearMap.rTensor_tmul,
          show (normalOrdered a b m (s - m) p) ⊗ₜ[ℂ] g
            = ((TensorProduct.mk ℂ B LatGrp).flip g) (normalOrdered a b m (s - m) p) from rfl])]
      -- `∑ᶠ m, (· ⊗ g)(NO p) = (· ⊗ g)(∑ᶠ m, NO p)` via the linear map `· ⊗ g`
      rw [← map_finsum ((TensorProduct.mk ℂ B LatGrp).flip g) hfin]
      rfl

/-! ## `nprod` bilinearity (4-term split) and the lattice Sugawara mode decomposition. -/

/-- `nprod` is additive in its left argument (on every coefficient/vector): the `normalOrdered`
diagonal splits and the finsums add (all three pieces are fields). -/
theorem nprod_add_left {a₁ a₂ b : FormalDist (End ℂ LatModule)}
    (ha₁ : IsField a₁) (ha₂ : IsField a₂) (hb : IsField b)
    (hadd : IsField (a₁ + a₂)) (s : ℤ) (x : LatModule) :
    nprod hadd hb s x = nprod ha₁ hb s x + nprod ha₂ hb s x := by
  rw [nprod_apply, nprod_apply, nprod_apply,
    ← finsum_add_distrib (normalOrdered_diag_support_finite ha₁ hb s x)
      (normalOrdered_diag_support_finite ha₂ hb s x)]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply, normalOrdered_apply, normalOrdered_apply]
  by_cases h : 0 ≤ m
  · rw [if_pos h, if_pos h, if_pos h]
    change ((a₁ m + a₂ m) * b (s - m)) x = (a₁ m * b (s - m)) x + (a₂ m * b (s - m)) x
    rw [add_mul, LinearMap.add_apply]
  · rw [if_neg h, if_neg h, if_neg h]
    change (b (s - m) * (a₁ m + a₂ m)) x = (b (s - m) * a₁ m) x + (b (s - m) * a₂ m) x
    rw [mul_add, LinearMap.add_apply]

/-- `nprod` is additive in its right argument (on every coefficient/vector). -/
theorem nprod_add_right {a b₁ b₂ : FormalDist (End ℂ LatModule)}
    (ha : IsField a) (hb₁ : IsField b₁) (hb₂ : IsField b₂)
    (hadd : IsField (b₁ + b₂)) (s : ℤ) (x : LatModule) :
    nprod ha hadd s x = nprod ha hb₁ s x + nprod ha hb₂ s x := by
  rw [nprod_apply, nprod_apply, nprod_apply,
    ← finsum_add_distrib (normalOrdered_diag_support_finite ha hb₁ s x)
      (normalOrdered_diag_support_finite ha hb₂ s x)]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply, normalOrdered_apply, normalOrdered_apply]
  by_cases h : 0 ≤ m
  · rw [if_pos h, if_pos h, if_pos h]
    change (a m * (b₁ (s - m) + b₂ (s - m))) x = (a m * b₁ (s - m)) x + (a m * b₂ (s - m)) x
    rw [mul_add, LinearMap.add_apply]
  · rw [if_neg h, if_neg h, if_neg h]
    change ((b₁ (s - m) + b₂ (s - m)) * a m) x = (b₁ (s - m) * a m) x + (b₂ (s - m) * a m) x
    rw [add_mul, LinearMap.add_apply]

/-- The momentum-mode field `Zf j = (j = -1 ? zGradeOp : 0)` (the `α₀ = zGradeOp` correction). -/
noncomputable def Zf : FormalDist (End ℂ LatModule) := fun j => if j = -1 then zGradeOp else 0

theorem Zf_isField : IsField Zf := by
  intro x; refine ⟨-1, fun n hn => ?_⟩
  show (if n = -1 then zGradeOp else 0) x = 0
  rw [if_neg (by omega : ¬ n = -1)]; rfl

/-- `alphaLat = liftF alphaField + Zf`. -/
theorem alphaLat_eq : alphaLat = liftF alphaField + Zf := by
  funext j
  show alphaLat j = liftF alphaField j + Zf j
  rw [alphaLat, liftF, Zf]

/-- `liftF alphaField` is a field. -/
theorem liftF_alphaField_isField : IsField (liftF alphaField) :=
  IsField_liftF (HeisenbergN.currentN_isField 1 2 0)

/-- The cross-term `nprod (liftF αF) Zf` on a basis state `q ⊗ eᵏ`: only `m = s+1` survives. -/
theorem nprod_lift_Zf (s : ℤ) (q : B) (k : ℤ) :
    nprod liftF_alphaField_isField Zf_isField s (q ⊗ₜ[ℂ] eVec k)
      = ((2 * k : ℤ) : ℂ) • ((alphaField (s + 1) q) ⊗ₜ[ℂ] eVec k) := by
  rw [nprod_apply]
  have hsupp : ∀ m : ℤ, m ≠ s + 1 →
      normalOrdered (liftF alphaField) Zf m (s - m) (q ⊗ₜ[ℂ] eVec k) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    have hZ : Zf (s - m) = 0 := by
      show (if s - m = -1 then zGradeOp else 0) = 0; rw [if_neg (by omega)]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]; change (LinearMap.rTensor LatGrp (alphaField m) * Zf (s - m)) _ = 0
      rw [hZ, mul_zero, LinearMap.zero_apply]
    · rw [if_neg h0]; change (Zf (s - m) * LinearMap.rTensor LatGrp (alphaField m)) _ = 0
      rw [hZ, zero_mul, LinearMap.zero_apply]
  have hZss : Zf (s - (s + 1)) = zGradeOp := by
    show (if s - (s + 1) = -1 then zGradeOp else 0) = zGradeOp; rw [if_pos (by ring)]
  rw [finsum_eq_single _ (s + 1) hsupp, normalOrdered_apply, hZss]
  by_cases h0 : 0 ≤ s + 1
  · rw [if_pos h0]
    change (LinearMap.rTensor LatGrp (alphaField (s + 1)) * zGradeOp) (q ⊗ₜ[ℂ] eVec k) = _
    rw [Module.End.mul_apply, zGradeOp_tmul, map_smul, LinearMap.rTensor_tmul]
  · rw [if_neg h0]
    change (zGradeOp * LinearMap.rTensor LatGrp (alphaField (s + 1))) (q ⊗ₜ[ℂ] eVec k) = _
    rw [Module.End.mul_apply, LinearMap.rTensor_tmul, zGradeOp_tmul]

/-- The cross-term `nprod Zf (liftF αF)` on a basis state: only `m = -1` survives. -/
theorem nprod_Zf_lift (s : ℤ) (q : B) (k : ℤ) :
    nprod Zf_isField liftF_alphaField_isField s (q ⊗ₜ[ℂ] eVec k)
      = ((2 * k : ℤ) : ℂ) • ((alphaField (s + 1) q) ⊗ₜ[ℂ] eVec k) := by
  rw [nprod_apply]
  have hsupp : ∀ m : ℤ, m ≠ -1 →
      normalOrdered Zf (liftF alphaField) m (s - m) (q ⊗ₜ[ℂ] eVec k) = 0 := by
    intro m hm
    rw [normalOrdered_apply]
    have hZ : Zf m = 0 := by show (if m = -1 then zGradeOp else 0) = 0; rw [if_neg hm]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]; change (Zf m * LinearMap.rTensor LatGrp (alphaField (s - m))) _ = 0
      rw [hZ, zero_mul, LinearMap.zero_apply]
    · rw [if_neg h0]; change (LinearMap.rTensor LatGrp (alphaField (s - m)) * Zf m) _ = 0
      rw [hZ, mul_zero, LinearMap.zero_apply]
  have hZm1 : Zf (-1) = zGradeOp := by
    show (if (-1 : ℤ) = -1 then zGradeOp else 0) = zGradeOp; rw [if_pos rfl]
  rw [finsum_eq_single _ (-1) hsupp, normalOrdered_apply, if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1),
    hZm1]
  change (LinearMap.rTensor LatGrp (alphaField (s - -1)) * zGradeOp) (q ⊗ₜ[ℂ] eVec k) = _
  rw [Module.End.mul_apply, zGradeOp_tmul, map_smul, LinearMap.rTensor_tmul,
    show s - (-1 : ℤ) = s + 1 from by ring]

/-- The `Zf Zf` term on a basis state: `nprod Zf Zf s (q⊗eᵏ) = (s=-2 ? (2k)²•(q⊗eᵏ) : 0)`. -/
theorem nprod_Zf_Zf (s : ℤ) (q : B) (k : ℤ) :
    nprod Zf_isField Zf_isField s (q ⊗ₜ[ℂ] eVec k)
      = if s = -2 then (((2 * k : ℤ) : ℂ) * ((2 * k : ℤ) : ℂ)) • (q ⊗ₜ[ℂ] eVec k) else 0 := by
  rw [nprod_apply]
  by_cases hs : s = -2
  · have hsupp : ∀ m : ℤ, m ≠ -1 →
        normalOrdered Zf Zf m (s - m) (q ⊗ₜ[ℂ] eVec k) = 0 := by
      intro m hm
      rw [normalOrdered_apply]
      have hZ : Zf m = 0 := by show (if m = -1 then zGradeOp else 0) = 0; rw [if_neg hm]
      by_cases h0 : 0 ≤ m
      · rw [if_pos h0]; change (Zf m * Zf (s - m)) _ = 0; rw [hZ, zero_mul, LinearMap.zero_apply]
      · rw [if_neg h0]; change (Zf (s - m) * Zf m) _ = 0; rw [hZ, mul_zero, LinearMap.zero_apply]
    have hZm1 : Zf (-1) = zGradeOp := by
      show (if (-1 : ℤ) = -1 then zGradeOp else 0) = zGradeOp; rw [if_pos rfl]
    have hZsm : Zf (s - -1) = zGradeOp := by
      show (if s - -1 = -1 then zGradeOp else 0) = zGradeOp; rw [if_pos (by omega)]
    rw [finsum_eq_single _ (-1) hsupp, normalOrdered_apply, if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1),
      hZm1, hZsm, if_pos hs]
    change (zGradeOp * zGradeOp) (q ⊗ₜ[ℂ] eVec k) = _
    rw [Module.End.mul_apply, zGradeOp_tmul, map_smul, zGradeOp_tmul, smul_smul]
  · rw [if_neg hs]
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0]
      have hZ : Zf m = 0 := by
        show (if m = -1 then zGradeOp else 0) = 0; rw [if_neg (by omega)]
      change (Zf m * Zf (s - m)) _ = 0; rw [hZ, zero_mul, LinearMap.zero_apply]
    · rw [if_neg h0]
      by_cases hm1 : m = -1
      · subst hm1
        have hZ : Zf (s - -1) = 0 := by
          show (if s - -1 = -1 then zGradeOp else 0) = 0; rw [if_neg (by omega)]
        change (Zf (s - -1) * Zf (-1)) _ = 0; rw [hZ, zero_mul, LinearMap.zero_apply]
      · have hZ : Zf m = 0 := by
          show (if m = -1 then zGradeOp else 0) = 0; rw [if_neg hm1]
        change (Zf (s - m) * Zf m) _ = 0; rw [hZ, mul_zero, LinearMap.zero_apply]

/-- The lift mode of the boson Sugawara on a basis state: `liftF(nprod αF αF) s (q⊗eᵏ)
= (nprod αF αF s q) ⊗ eᵏ`. -/
theorem nprod_lift_lift_tmul (s : ℤ) (q : B) (k : ℤ) :
    nprod liftF_alphaField_isField liftF_alphaField_isField s (q ⊗ₜ[ℂ] eVec k)
      = (nprod (HeisenbergN.currentN_isField 1 2 0) (HeisenbergN.currentN_isField 1 2 0) s q)
        ⊗ₜ[ℂ] eVec k := by
  have heq : nprod liftF_alphaField_isField liftF_alphaField_isField
      = liftF (nprod (HeisenbergN.currentN_isField 1 2 0) (HeisenbergN.currentN_isField 1 2 0)) :=
    liftF_nprod (HeisenbergN.currentN_isField 1 2 0) (HeisenbergN.currentN_isField 1 2 0)
  rw [heq]
  exact LinearMap.rTensor_tmul LatGrp
    (nprod (HeisenbergN.currentN_isField 1 2 0) (HeisenbergN.currentN_isField 1 2 0) s) (eVec k) q

/-- `nprod` depends only on the underlying distributions, not on the field-witness proofs. -/
theorem nprod_congr {a b a' b' : FormalDist (End ℂ LatModule)}
    (ha : IsField a) (hb : IsField b) (ha' : IsField a') (hb' : IsField b')
    (haa : a = a') (hbb : b = b') : nprod ha hb = nprod ha' hb' := by
  subst haa; subst hbb; rfl

/-- **The lattice Sugawara mode decomposition** on a basis state `q ⊗ eᵏ`:
`nprod αLat αLat s (q⊗eᵏ) = (nprod αF αF s q)⊗eᵏ + 4k•(αF(s+1)q)⊗eᵏ + (s=-2 ? (2k)²•(q⊗eᵏ) : 0)`. -/
theorem nprod_alphaLat_tmul (s : ℤ) (q : B) (k : ℤ) :
    nprod alphaLat_isField alphaLat_isField s (q ⊗ₜ[ℂ] eVec k)
      = (nprod (HeisenbergN.currentN_isField 1 2 0) (HeisenbergN.currentN_isField 1 2 0) s q)
          ⊗ₜ[ℂ] eVec k
        + (2 * ((2 * k : ℤ) : ℂ)) • ((alphaField (s + 1) q) ⊗ₜ[ℂ] eVec k)
        + (if s = -2 then (((2 * k : ℤ) : ℂ) * ((2 * k : ℤ) : ℂ)) • (q ⊗ₜ[ℂ] eVec k) else 0) := by
  classical
  have hAZ : IsField (liftF alphaField + Zf) := alphaLat_eq ▸ alphaLat_isField
  -- replace the two `αLat` witnesses by the `liftF αF + Zf` form
  rw [nprod_congr alphaLat_isField alphaLat_isField hAZ hAZ alphaLat_eq alphaLat_eq]
  -- split the left argument, then each of the two right arguments
  rw [nprod_add_left liftF_alphaField_isField Zf_isField hAZ hAZ s (q ⊗ₜ[ℂ] eVec k)]
  rw [nprod_add_right liftF_alphaField_isField liftF_alphaField_isField Zf_isField hAZ s
        (q ⊗ₜ[ℂ] eVec k),
    nprod_add_right Zf_isField liftF_alphaField_isField Zf_isField hAZ s (q ⊗ₜ[ℂ] eVec k)]
  rw [nprod_lift_lift_tmul, nprod_lift_Zf, nprod_Zf_lift, nprod_Zf_Zf]
  -- combine: (lift) + 2k•(..) + (2k•(..) + ZfZf) = lift + 4k•(..) + ZfZf
  rw [show (2 * ((2 * k : ℤ) : ℂ)) • ((alphaField (s + 1) q) ⊗ₜ[ℂ] eVec k)
        = ((2 * k : ℤ) : ℂ) • ((alphaField (s + 1) q) ⊗ₜ[ℂ] eVec k)
          + ((2 * k : ℤ) : ℂ) • ((alphaField (s + 1) q) ⊗ₜ[ℂ] eVec k) from by
      rw [← add_smul]; congr 1; push_cast; ring]
  abel

/-- `(1/4)·(nprod αF αF s) = LvirN 1 2 (-s-2)` (the boson Sugawara mode bridge). -/
theorem quarter_nprod_alphaField (s : ℤ) :
    (1 / 4 : ℂ) • nprod (HeisenbergN.currentN_isField 1 2 0) (HeisenbergN.currentN_isField 1 2 0) s
      = HeisenbergN.LvirN 1 2 (-s - 2) := by
  rw [HeisenbergN.LvirN, Fin.sum_univ_one, HeisenbergN.LvirNa,
    show -(-s - 2) - 2 = s from by ring, show (1 / (2 * 2) : ℂ) = (1 / 4 : ℂ) from by norm_num]

/-- **The lattice Sugawara field on a basis state** `q ⊗ eᵏ`:
`sugField s (q⊗eᵏ) = (LvirN 1 2 (-s-2) q)⊗eᵏ + k•(αF(s+1)q)⊗eᵏ + (s=-2 ? k²•(q⊗eᵏ) : 0)`. -/
theorem sugField_tmul (s : ℤ) (q : B) (k : ℤ) :
    sugField s (q ⊗ₜ[ℂ] eVec k)
      = (HeisenbergN.LvirN 1 2 (-s - 2) q) ⊗ₜ[ℂ] eVec k
        + (k : ℂ) • ((alphaField (s + 1) q) ⊗ₜ[ℂ] eVec k)
        + (if s = -2 then ((k : ℂ) * (k : ℂ)) • (q ⊗ₜ[ℂ] eVec k) else 0) := by
  rw [sugField]
  change (1 / 4 : ℂ) • nprod alphaLat_isField alphaLat_isField s (q ⊗ₜ[ℂ] eVec k) = _
  rw [nprod_alphaLat_tmul, smul_add, smul_add]
  congr 1
  · congr 1
    · -- the lift part: (1/4)•(nprod αF αF s q)⊗eᵏ = (LvirN(-s-2) q)⊗eᵏ
      rw [TensorProduct.smul_tmul']
      congr 1
      have := quarter_nprod_alphaField s
      rw [LinearMap.ext_iff] at this
      rw [← this q]; rfl
    · -- the cross part: (1/4)•(2·2k)•(..) = k•(..)
      rw [smul_smul]; congr 1; push_cast; ring
  · -- the ZfZf part
    by_cases hs : s = -2
    · rw [if_pos hs, if_pos hs, smul_smul]; congr 1; push_cast; ring
    · rw [if_neg hs, if_neg hs, smul_zero]

/-- **The bridge `Ltrans = Trec`**: the abstract Sugawara translation equals the explicit
reconstruction translation operator (both `(LvirN(-1) q)⊗eᵏ + k•(α(-1)q)⊗eᵏ` on `q ⊗ eᵏ`). -/
theorem Ltrans_eq_Trec : Ltrans = Trec := by
  rw [Ltrans_eq]
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y1 y2 h1 h2 => rw [map_add, map_add, h1, h2]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero]; rw [map_zero, map_zero]
      | add g1 g2 h1 h2 =>
          erw [TensorProduct.tmul_add]; rw [map_add, map_add, h1, h2]
      | single c a =>
          rw [(Finsupp.smul_single_one c a).symm,
            show (Finsupp.single c 1 : LatGrp) = eVec c from rfl]
          erw [TensorProduct.tmul_smul, map_smul, map_smul]
          rw [sugField_tmul, Trec_tmul, if_neg (by norm_num : ¬ (-1 : ℤ) = -2),
            add_zero, show (-(-1 : ℤ) - 2) = -1 from by ring, alphaField_apply,
            show (-((-1 : ℤ) + 1) - 1) = -1 from by ring]

/-- **`ω ∈ gradingLat 2`** (conformal_mem): `ω = ωN ⊗ e^0` is boson-weight-2, charge-0. -/
theorem omegaLat_mem : omegaLat ∈ gradingLat 2 := by
  have hb : HeisenbergN.ωN 1 2 ∈ HeisenbergN.gradingZN 1 2 := HeisenbergN.ωN_mem_gradingZN_two 1 2
  have hmem : omegaLat ∈ bigrad (2, 0) := by
    rw [omegaLat, bigrad]; exact Submodule.mem_map_of_mem hb
  have := bigrad_le_gradingLat 2 0 hmem
  rwa [show (2 : ℤ) + (0 : ℤ) ^ 2 = 2 from by ring] at this

/-! ## VOA3 — translation: `Yfull (mode (Yfull ω) 0 v) = deriv (Yfull v)`. -/

/-- `mode (Yfull ω) 0 = Trec` (the conformal `L₋₁` is the reconstruction translation operator). -/
theorem mode_Yfull_omega_zero : mode (Yfull hYloc omegaLat) 0 = Trec := by
  rw [mode_apply, show (-(0 : ℤ) - 1) = -1 from by ring, Yfull_omega_eq, ← Ltrans_eq, Ltrans_eq_Trec]

/-- `(Yfull v) 1 latVacuum = Trec v` (the first creation-tower step, from `Trec`-covariance). -/
theorem Yfull_one_vac (v : LatModule) : (Yfull hYloc v) 1 latVacuum = Trec v := by
  have h := congrArg (fun (R : End ℂ LatModule) => R latVacuum) (Yfull_DCov hYloc v 0)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [Trec_vacuum, map_zero, sub_zero, Yfull_cre0, show ((0 : ℤ) + 1) = 1 from by ring,
    one_zsmul] at h
  exact h.symm

/-- **VOA3 (translation), `L₋₁ = Trec` form**: `Yfull (Trec v) = ∂_z Yfull v`. -/
theorem Yfull_translation (v : LatModule) :
    Yfull hYloc (Trec v) = deriv (Yfull hYloc v) := by
  have hGcov : Reconstruction.DCovariant Trec (deriv (Yfull hYloc v)) :=
    Reconstruction.DCovariant.deriv' (Yfull_DCov hYloc v)
  have hGneg : ∀ q : ℤ, q < 0 → (deriv (Yfull hYloc v)) q latVacuum = 0 := by
    intro q hq
    rw [deriv_apply]
    show ((q + 1 : ℤ) • (Yfull hYloc v) (q + 1)) latVacuum = 0
    rw [← Int.cast_smul_eq_zsmul ℂ (q + 1), LinearMap.smul_apply]
    by_cases hq1 : q + 1 < 0
    · rw [Yfull_creneg hYloc v hq1, smul_zero]
    · rw [show q + 1 = (0 : ℤ) from by omega, Int.cast_zero, zero_smul]
  have hbase : (Yfull hYloc (Trec v)) 0 latVacuum = (deriv (Yfull hYloc v)) 0 latVacuum := by
    rw [Yfull_cre0, deriv_apply]
    show Trec v = ((0 + 1 : ℤ) • (Yfull hYloc v) (0 + 1)) latVacuum
    rw [show (0 + 1 : ℤ) = 1 from by ring, one_zsmul, Yfull_one_vac]
  have hAvac : ∀ p : ℤ, (Yfull hYloc (Trec v) - deriv (Yfull hYloc v)) p latVacuum = 0 := by
    intro p
    show ((Yfull hYloc (Trec v)) p - (deriv (Yfull hYloc v)) p) latVacuum = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact Reconstruction.tower_unique (Yfull_DCov hYloc (Trec v)) hGcov Trec_vacuum hbase
      (fun q hq => Yfull_creneg hYloc (Trec v) hq) hGneg p
  have hloc : ∀ l : List ℕ, ∀ m : ℤ,
      Local (Yfull hYloc (Trec v) - deriv (Yfull hYloc v)) (YwordLat l m) := by
    intro l m
    have h1 : Local (Yfull hYloc (Trec v)) (YwordLat l m) := by
      rw [← Yfull_word hYloc l m]; exact Yfull_local hYloc (Trec v) (wordStateLat l m)
    have h2 : Local (deriv (Yfull hYloc v)) (YwordLat l m) := by
      have hv : Local (Yfull hYloc v) (YwordLat l m) := by
        rw [← Yfull_word hYloc l m]; exact Yfull_local hYloc v (wordStateLat l m)
      exact Local.derivL hv
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (deriv (Yfull hYloc v))]
    exact Reconstruction.Local.add_left h1 (VertexOperatorAlgebra.Local.smul' (-1) h2)
  have hz := Reconstruction.field_eq_zero_of_vacuum latVacuum
    (Yfull hYloc (Trec v) - deriv (Yfull hYloc v)) (Function.uncurry wordStateLat)
    (Function.uncurry (fun l m => YwordLat l m))
    (fun lm => hloc lm.1 lm.2)
    (fun lm => YwordLat_vacuum_base lm.1 lm.2)
    (fun lm q hq => YwordLat_vacuum_neg lm.1 lm.2 hq)
    hAvac wordStateLat_span
  rwa [sub_eq_zero] at hz

/-- **VOA3** (`translation` field): `Yfull (mode (Yfull ω) 0 v) = ∂_z Yfull v`. -/
theorem Yfull_translation_omega (v : LatModule) :
    Yfull hYloc (mode (Yfull hYloc omegaLat) 0 v) = deriv (Yfull hYloc v) := by
  rw [mode_Yfull_omega_zero]; exact Yfull_translation hYloc v

/-! ## VOA2 — `L₀ = mode (Yfull ω) 1 = sugField(-2)` acts as the conformal weight. -/

/-- The lattice `L₀` operator `Lzero := mode (Yfull ω) 1 = sugField(-2)`. -/
theorem mode_Yfull_omega_one : mode (Yfull hYloc omegaLat) 1 = sugField (-2) := by
  rw [mode_apply, show (-(1 : ℤ) - 1) = -2 from by ring, Yfull_omega_eq]

/-- `sugField(-2)` acts as `(w + n²)` on the bigraded basis element `mkE n p`, `p ∈ gradingWN 1 w`:
the boson `L₀` gives `w`, the charge `α₀²` momentum gives `n²` (the `Zf Zf` term, `αF(-1)=0`). -/
theorem sugField_neg_two_bigrad {w : ℕ} {n : ℤ} {p : B} (hp : p ∈ HeisenbergN.gradingWN 1 w) :
    sugField (-2) (mkE n p) = (((w : ℤ) + n ^ 2 : ℤ) : ℂ) • (mkE n p) := by
  rw [mkE_apply, sugField_tmul, if_pos rfl,
    show (-(-2 : ℤ) - 2) = 0 from by ring,
    -- the cross term has `αField (-2+1) = αField (-1) = α 0 = 0`
    show alphaField ((-2 : ℤ) + 1) p = 0 from by
      rw [alphaField_apply, show (-((-2 : ℤ) + 1) - 1) = 0 from by ring,
        show α (0 : ℤ) = HeisenbergN.oscN 1 2 0 0 from rfl, HeisenbergN.oscN_zero,
        LinearMap.zero_apply],
    TensorProduct.zero_tmul, smul_zero, add_zero,
    HeisenbergN.LvirN_zero_gradingWN 1 2 (by norm_num : (2 : ℂ) ≠ 0) hp]
  -- now `(w•p)⊗eⁿ + (n·n)•(p⊗eⁿ) = (w+n²)•(p⊗eⁿ)`
  rw [TensorProduct.smul_tmul',
    show (((w : ℤ) + n ^ 2 : ℤ) : ℂ) = ((w : ℂ)) + ((n : ℂ) * (n : ℂ)) from by push_cast; ring,
    add_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']

/-- `sugField(-2)` acts as the scalar `k` on every `bigrad p'` with `p' ∈ fiberPos k`. -/
theorem sugField_neg_two_bigrad_fiber (k : ℤ) (p' : ℤ × ℤ) (hp' : p' ∈ fiberPos k)
    {x : LatModule} (hx : x ∈ bigrad p') : sugField (-2) x = (k : ℂ) • x := by
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨hfib, hpos⟩ := hp'
  obtain ⟨w, hw⟩ : ∃ w : ℕ, p'.1 = (w : ℤ) := ⟨p'.1.toNat, by omega⟩
  have hqW : q ∈ HeisenbergN.gradingWN 1 w := by
    rw [hw, HeisenbergN.gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at hq; exact hq
  rw [sugField_neg_two_bigrad hqW]
  congr 1
  rw [← hfib, hw]

/-- **VOA2** (`L0_grading`): `mode (Yfull ω) 1 v = n•v` for `v ∈ gradingLat n`.  Each fiber piece
`bigrad p` is a `sugField(-2)`-eigenspace of eigenvalue `n`, so the whole `iSup` lies in the kernel
of `sugField(-2) - n·id` (`iSup_le`/`biSup_le`, no induction needed). -/
theorem Yfull_L0_grading {n : ℤ} (v : LatModule) (hv : v ∈ gradingLat n) :
    mode (Yfull hYloc omegaLat) 1 v = (n : ℂ) • v := by
  rw [mode_Yfull_omega_one]
  have hker : v ∈ LinearMap.ker (sugField (-2) - (n : ℂ) • LinearMap.id) := by
    refine (?_ : gradingLat n ≤ LinearMap.ker (sugField (-2) - (n : ℂ) • LinearMap.id)) hv
    rw [gradingLat_eq_biSup_pos n]
    refine iSup_le (fun p' => iSup_le (fun hp' => ?_))
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sugField_neg_two_bigrad_fiber n p' hp' hx, sub_self]
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at hker
  exact hker

/-! ## VA3/VA5 — the creation tower and regularity from the six `Yfull` props. -/

/-- **VA3 (creation)**: `mode (Yfull u) (-1) |0⟩ = u` and `mode (Yfull u) n |0⟩ = 0` for `n ≥ 0`. -/
theorem Yfull_creation (u : LatModule) :
    mode (Yfull hYloc u) (-1) latVacuum = u
      ∧ ∀ n : ℤ, 0 ≤ n → mode (Yfull hYloc u) n latVacuum = 0 := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [mode_apply, show (-(-1 : ℤ) - 1) = 0 from by ring]; exact Yfull_cre0 hYloc u
  · rw [mode_apply]; exact Yfull_creneg hYloc u (by omega : -n - 1 < 0)

/-- **VA5 (regularity)**: each `Yfull u` is a field, so its modes lower-truncate at `v`. -/
theorem Yfull_regularity (u v : LatModule) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (Yfull hYloc u) n v = 0 := by
  obtain ⟨Bnd, hB⟩ := Yfull_isField hYloc u v
  refine ⟨-Bnd + 1, fun n hn => ?_⟩
  rw [mode_apply]; exact hB (-n - 1) (by omega)

/-! ## VOA1 — the lattice Sugawara Virasoro relation (`c = 1`). -/

/-- The lattice Virasoro mode operator `LL n := sugField(-n-2) = mode (Yfull ω)(n+1)`. -/
noncomputable def LL (n : ℤ) : End ℂ LatModule := sugField (-n - 2)

/-- `sugField(-n-2)` on a basis vector `q ⊗ eᵏ`: the lattice Virasoro mode `Lₙ` is the boson
Virasoro `LvirN n`, plus the charge cross-term `k·αₙ`, plus the `[n=0]·k²` zero-mode. -/
theorem LL_tmul (n : ℤ) (q : B) (k : ℤ) :
    LL (n) (q ⊗ₜ[ℂ] eVec k)
      = (HeisenbergN.LvirN 1 2 n q) ⊗ₜ[ℂ] eVec k
        + (k : ℂ) • ((HeisenbergN.oscN 1 2 0 n q) ⊗ₜ[ℂ] eVec k)
        + (if n = 0 then ((k : ℂ) * (k : ℂ)) • (q ⊗ₜ[ℂ] eVec k) else 0) := by
  rw [LL, sugField_tmul]
  congr 1
  · congr 1
    · congr 1; ring
    · rw [alphaField_apply, show (-((-n - 2) + 1) - 1 : ℤ) = n from by ring]; rfl
  · by_cases hn : n = 0
    · rw [if_pos hn, if_pos (by omega : (-n - 2 : ℤ) = -2)]
    · rw [if_neg hn, if_neg (by omega : ¬ (-n - 2 : ℤ) = -2)]

/-- `mode (Yfull ω)(j) = sugField(-j-1)` (the conformal mode is the Sugawara coefficient). -/
theorem mode_Yfull_omega (j : ℤ) : mode (Yfull hYloc omegaLat) j = sugField (-j - 1) := by
  rw [mode_apply, Yfull_omega_eq]

/-- The lattice Virasoro mode `mode (Yfull ω)(n+1) = LL n`. -/
theorem mode_Yfull_omega_eq_LL (n : ℤ) : mode (Yfull hYloc omegaLat) (n + 1) = LL n := by
  rw [mode_Yfull_omega, LL, show (-(n + 1) - 1 : ℤ) = -n - 2 from by ring]

/-- **The pure boson-operator core** of the lattice Sugawara Virasoro relation.  With
`Op s y = Lₛ y + k·aₛ y + δ_{s,0} k²·y` (the boson Virasoro `L`, the current `a`, and the charge
zero-mode), the lattice Virasoro modes obey `[Op m, Op n] = (m−n)·Op(m+n) + δ_{m+n,0}·(m³−m)/12`:
the boson `c=1` central term, with the charge-sector `2mk²·δ` absorbed into the `(m−n)·Op(m+n)`
zero-mode term (whence central charge exactly `1`). -/
theorem hbos_core (m n : ℤ) (q : B) (kc : ℂ)
    (L : ℤ → End ℂ B) (a : ℤ → End ℂ B)
    (hLL : ∀ (s t : ℤ) (y : B),
      L s (L t y) - L t (L s y)
        = ((s : ℂ) - t) • L (s + t) y
          + (if s + t = 0 then ((s : ℂ) ^ 3 - s) / 12 else 0) • y)
    (hLa : ∀ (s t : ℤ) (y : B),
      L s (a t y) = (-(t : ℂ)) • a (s + t) y + a t (L s y))
    (haa : ∀ (s t : ℤ) (y : B),
      a s (a t y) - a t (a s y) = (if s + t = 0 then (s : ℂ) * 2 else 0) • y)
    (Op : ℤ → B → B)
    (hOp : Op = fun s y => L s y + kc • a s y + (if s = 0 then (kc * kc) • y else 0)) :
    Op m (Op n q) - Op n (Op m q)
      = ((m : ℂ) - (n : ℂ)) • Op (m + n) q
        + (if m + n = 0 then (((m : ℂ) ^ 3 - (m : ℂ)) / 12) • q else 0) := by
  subst hOp
  simp only [map_add, map_smul]
  have eLL : L m (L n q) = L n (L m q) + (((m : ℂ) - n) • L (m + n) q
      + (if m + n = 0 then ((m : ℂ) ^ 3 - m) / 12 else 0) • q) := by
    rw [← hLL m n q]; abel
  have eaa : a m (a n q) = a n (a m q) + (if m + n = 0 then (m : ℂ) * 2 else 0) • q := by
    rw [← haa m n q]; abel
  have eLan : L m (a n q) = (-(n : ℂ)) • a (m + n) q + a n (L m q) := hLa m n q
  have eLam : L n (a m q) = (-(m : ℂ)) • a (m + n) q + a m (L n q) := by
    have := hLa n m q
    rwa [add_comm n m] at this
  rw [eLL, eLan, eLam, eaa]
  by_cases hmn : m + n = 0
  · by_cases hm0 : m = 0
    · have hn0 : n = 0 := by omega
      subst hm0; subst hn0
      simp only [if_pos, map_smul]
      push_cast
      module
    · have hn0 : n ≠ 0 := by omega
      have hnm : (n : ℂ) = -(m : ℂ) := by
        have : n = -m := by omega
        rw [this]; push_cast; ring
      simp only [if_neg hm0, if_neg hn0, if_pos hmn, map_zero, add_zero]
      rw [hnm]
      module
  · by_cases hm0 : m = 0
    · have hn0 : n ≠ 0 := by omega
      simp only [if_neg hmn, if_neg hn0, if_pos hm0, map_zero, add_zero, map_smul]
      subst hm0
      module
    · by_cases hn0 : n = 0
      · simp only [if_neg hmn, if_neg hm0, if_pos hn0, map_zero, add_zero, map_smul]
        subst hn0
        module
      · simp only [if_neg hmn, if_neg hm0, if_neg hn0, map_zero, add_zero]
        module

/-- **The lattice Sugawara Virasoro relation on a basis vector** `q ⊗ eᵏ` (`c = 1`):
the boson `c=1` central term `(m³-m)/12` plus the charge-sector `2k²m·δ` recombine to the
`(m-n)·LL(m+n)` central term, leaving exactly central charge `1`. -/
theorem LL_comm_tmul (m n : ℤ) (q : B) (k : ℤ) :
    (LL m * LL n - LL n * LL m) (q ⊗ₜ[ℂ] eVec k)
      = (((m : ℂ) - n) • LL (m + n)
          + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (1 : ℂ)) • (1 : End ℂ LatModule)
             else 0)) (q ⊗ₜ[ℂ] eVec k) := by
  classical
  -- abbreviations
  set L := HeisenbergN.LvirN 1 2 with hL
  set a := HeisenbergN.oscN 1 2 0 with ha
  have hk2 : (2 : ℂ) ≠ 0 := by norm_num
  -- boson commutator facts (r=1, k=2)
  have hLL : ∀ (s t : ℤ) (y : B),
      L s (L t y) - L t (L s y)
        = ((s : ℂ) - t) • L (s + t) y
          + (if s + t = 0 then ((s : ℂ) ^ 3 - s) / 12 else 0) • y := by
    intro s t y
    have h := congrArg (fun (T : End ℂ B) => T y) (HeisenbergN.L_virasoroN 1 2 hk2 s t)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Nat.cast_one, one_mul] at h
    exact h
  have hLa : ∀ (s t : ℤ) (y : B),
      L s (a t y) = (-(t : ℂ)) • a (s + t) y + a t (L s y) := fun s t y =>
    HeisenbergN.LvirN_oscN 1 2 hk2 0 s t y
  have haa : ∀ (s t : ℤ) (y : B),
      a s (a t y) - a t (a s y) = (if s + t = 0 then (s : ℂ) * 2 else 0) • y := by
    intro s t y
    have h := congrArg (fun (T : End ℂ B) => T y) (HeisenbergN.oscN_comm 1 2 0 0 s t)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.id_apply, true_and] at h
    exact h
  -- the per-mode boson operator `Op s y := L s y + k·a s y + [s=0]k²·y`
  set kc : ℂ := (k : ℂ) with hkc
  set Op : ℤ → B → B := fun s y => L s y + kc • a s y + (if s = 0 then (kc * kc) • y else 0)
    with hOp
  -- `LL s (y ⊗ eᵏ) = (Op s y) ⊗ eᵏ` (the charge `k` is a spectator; `LL` is charge-preserving)
  have hLLOp : ∀ (s : ℤ) (y : B), LL s (y ⊗ₜ[ℂ] eVec k) = (Op s y) ⊗ₜ[ℂ] eVec k := by
    intro s y
    rw [LL_tmul, hOp]
    simp only
    rw [TensorProduct.add_tmul, TensorProduct.add_tmul, TensorProduct.smul_tmul']
    congr 1
    by_cases hs : s = 0
    · rw [if_pos hs, if_pos hs, TensorProduct.smul_tmul']
    · rw [if_neg hs, if_neg hs, TensorProduct.zero_tmul]
  -- reduce the whole identity to the boson-operator identity
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hLLOp, hLLOp, hLLOp, hLLOp,
    LinearMap.add_apply, LinearMap.smul_apply, hLLOp]
  rw [← TensorProduct.sub_tmul, TensorProduct.smul_tmul']
  -- the boson `Op`-identity, tensored with `eᵏ`
  have hbos : Op m (Op n q) - Op n (Op m q)
      = ((m : ℂ) - (n : ℂ)) • Op (m + n) q
        + (if m + n = 0 then (((m : ℂ) ^ 3 - (m : ℂ)) / 12) • q else 0) :=
    hbos_core m n q kc L a hLL hLa haa Op hOp
  rw [hbos]
  by_cases hmn : m + n = 0
  · rw [if_pos hmn, if_pos hmn, LinearMap.smul_apply, Module.End.one_apply,
      TensorProduct.add_tmul, mul_one, TensorProduct.smul_tmul']
  · rw [if_neg hmn, if_neg hmn, add_zero, LinearMap.zero_apply, add_zero]

/-- **VOA1 (conformal symmetry)**, `centralCharge = 1`. -/
theorem Yfull_virasoro (m n : ℤ) :
    ⁅mode (Yfull hYloc omegaLat) (m + 1), mode (Yfull hYloc omegaLat) (n + 1)⁆
      = ((m : ℂ) - n) • mode (Yfull hYloc omegaLat) (m + n + 1)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (1 : ℂ)) • (1 : End ℂ LatModule)
           else 0) := by
  rw [mode_Yfull_omega_eq_LL, mode_Yfull_omega_eq_LL,
    show m + n + 1 = (m + n) + 1 from by ring, mode_Yfull_omega_eq_LL,
    LieRing.of_associative_ring_bracket]
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y1 y2 hy1 hy2 => rw [map_add, map_add, hy1, hy2]
  | tmul q g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero]; rw [map_zero, map_zero]
      | add g1 g2 h1 h2 =>
          erw [TensorProduct.tmul_add]; rw [map_add, map_add, h1, h2]
      | single c b =>
          rw [(Finsupp.smul_single_one c b).symm,
            show (Finsupp.single c 1 : LatGrp) = eVec c from rfl]
          erw [TensorProduct.tmul_smul]
          rw [map_smul, map_smul, LL_comm_tmul]

/-! ## VA1 — the bigrading-tracking mode-grading machinery. -/


-- cSchurC c N is weighted homogeneous of weight N
theorem cSchurC_mem_gradingWN (c : ℂ) (N : ℕ) : cSchurC c N ∈ gradingWN 1 N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [cSchurC_zero]; exact HeisenbergN.vacuumN_mem_gradingWN 1
    | (M+1) =>
      rw [cSchurC_succ]
      refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m hm => ?_))
      simp only [Finset.mem_range] at hm
      have hcv : cVar m ∈ gradingWN 1 (m + 1) := by
        rw [cVar, HeisenbergN.mem_gradingWN]
        have := isWeightedHomogeneous_X ℂ (HeisenbergN.weightFnN (r := 1)) (m, (0 : Fin 1))
        rw [HeisenbergN.weightFnN_apply] at this; exact this
      have hsc : cSchurC c (M - m) ∈ gradingWN 1 (M - m) := ih (M - m) (by omega)
      rw [HeisenbergN.mem_gradingWN] at hcv hsc ⊢
      have hmul := hcv.mul hsc
      rwa [show (m + 1) + (M - m) = M + 1 from by omega] at hmul


-- EminusOpC c N raises gradingWN by N (multiplication by weight-N polynomial cSchurC c N)
theorem EminusOpC_mem_gradingWN (c : ℂ) (N : ℕ) {w : ℕ} {p : B} (hp : p ∈ gradingWN 1 w) :
    EminusOpC c N p ∈ gradingWN 1 (N + w) := by
  rw [EminusOpC, LinearMap.mulLeft_apply]
  have hc : cSchurC c N ∈ gradingWN 1 N := cSchurC_mem_gradingWN c N
  rw [HeisenbergN.mem_gradingWN] at hc hp ⊢
  exact hc.mul hp

-- EminusC c t raises gradingZN by t
theorem EminusC_mem_gradingZN (c : ℂ) (t : ℤ) {w : ℕ} {p : B} (hp : p ∈ gradingWN 1 w) :
    EminusC c t p ∈ gradingZN 1 ((w : ℤ) + t) := by
  rw [EminusC_apply]
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    have h := HeisenbergN.mem_gradingZN_of_gradingWN (EminusOpC_mem_gradingWN c t.toNat hp)
    rwa [show ((t.toNat + w : ℕ) : ℤ) = (w : ℤ) + t from by
      rw [Nat.cast_add, Int.toNat_of_nonneg ht]; ring] at h
  · rw [if_neg ht, LinearMap.zero_apply]; exact Submodule.zero_mem _

-- EplusC c t raises gradingZN by t (lowers by -t = |t|)
theorem EplusC_mem_gradingZN (c : ℂ) (t : ℤ) {w : ℕ} {p : B} (hp : p ∈ gradingWN 1 w) :
    EplusC c t p ∈ gradingZN 1 ((w : ℤ) + t) := by
  rw [EplusC_apply]
  by_cases ht : t ≤ 0
  · rw [if_pos ht]
    have := aExpC_mem_gradingZN c (-t).toNat hp
    rwa [show (w : ℤ) - ((-t).toNat : ℤ) = (w : ℤ) + t from by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -t)]; ring] at this
  · rw [if_neg ht, LinearMap.zero_apply]; exact Submodule.zero_mem _


-- gradingZN versions
theorem EminusC_memZ (c : ℂ) (t : ℤ) {d : ℤ} {p : B} (hp : p ∈ gradingZN 1 d) :
    EminusC c t p ∈ gradingZN 1 (d + t) := by
  by_cases hd : 0 ≤ d
  · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
    have := EminusC_mem_gradingZN c t hp
    rwa [Int.toNat_of_nonneg hd] at this
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, LinearMap.map_zero]; exact Submodule.zero_mem _

theorem EplusC_memZ (c : ℂ) (t : ℤ) {d : ℤ} {p : B} (hp : p ∈ gradingZN 1 d) :
    EplusC c t p ∈ gradingZN 1 (d + t) := by
  by_cases hd : 0 ≤ d
  · rw [HeisenbergN.gradingZN_of_nonneg hd] at hp
    have := EplusC_mem_gradingZN c t hp
    rwa [Int.toNat_of_nonneg hd] at this
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hp
    rw [hp, LinearMap.map_zero]; exact Submodule.zero_mem _

/-- A finite-support finsum of submodule elements lies in the submodule. -/
theorem finsumB_mem_submodule {ι : Type*} (S : Submodule ℂ B)
    (g : ι → B) (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) :
    (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)

-- EEC c s raises gradingZN by s
theorem EEC_memZ (c : ℂ) (s : ℤ) {d : ℤ} {p : B} (hp : p ∈ gradingZN 1 d) :
    EEC c s p ∈ gradingZN 1 (d + s) := by
  rw [EEC, nprod_apply]
  refine finsumB_mem_submodule _ _
    (normalOrdered_diag_support_finite (EminusC_isField c) (EplusC_isField c) s p) (fun m => ?_)
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, Module.End.mul_apply]
    have h1 := EplusC_memZ c (s - m) hp
    have h2 := EminusC_memZ c m h1
    rwa [show d + (s - m) + m = d + s from by ring] at h2
  · rw [if_neg h0, Module.End.mul_apply]
    have h1 := EminusC_memZ c m hp
    have h2 := EplusC_memZ c (s - m) h1
    rwa [show d + m + (s - m) = d + s from by ring] at h2


-- Yemα m t maps bigrad (w,n) into bigrad (w+t-2mn, n+m); conformal weight m²+q+t.
theorem Yemα_bigrad_mem (m t w n : ℤ) {p : B} (hp : p ∈ gradingZN 1 w) :
    Yemα m t (mkE n p) ∈ gradingLat (m ^ 2 + (w + n ^ 2) + t) := by
  rw [mkE_apply, Yemα_tmul]
  have hE : EEC (m : ℂ) (t - 2 * m * n) p ∈ gradingZN 1 (w + (t - 2 * m * n)) :=
    EEC_memZ (m : ℂ) (t - 2 * m * n) hp
  by_cases hwt : 0 ≤ w + (t - 2 * m * n)
  · rw [HeisenbergN.gradingZN_of_nonneg hwt] at hE
    have hmem : (EEC (m : ℂ) (t - 2 * m * n) p) ⊗ₜ[ℂ] eVec (n + m)
        ∈ bigrad ((w + (t - 2 * m * n)).toNat, n + m) := by
      rw [bigrad]
      exact ⟨_, hE, by rw [mkE_apply]⟩
    have hle := bigrad_le_gradingLat (w + (t - 2 * m * n)).toNat (n + m) hmem
    rwa [show ((w + (t - 2 * m * n)).toNat : ℤ) + (n + m) ^ 2 = m ^ 2 + (w + n ^ 2) + t from by
      rw [Int.toNat_of_nonneg hwt]; ring] at hle
  · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hE
    rw [hE, TensorProduct.zero_tmul]; exact Submodule.zero_mem _

/-- A lattice graded field of weight `D`: the `zʲ`-coefficient `a j` shifts conformal grade by
`D + j` (mode `n = a(-n-1)` shifts by `D - n - 1`). -/
def GradedFieldLat (a : FormalDist (End ℂ LatModule)) (D : ℤ) : Prop :=
  ∀ (j q : ℤ) (x : LatModule), x ∈ gradingLat q → a j x ∈ gradingLat (D + q + j)

/-- To check `GradedFieldLat a D`, it suffices to check it on bigraded basis elements `mkE n p`
(`p ∈ gradingZN 1 w`, conformal weight `w + n²`), since `gradingLat q = ⨆ p ∈ fiberPos q, bigrad p`
and `a j` is linear. -/
theorem GradedFieldLat.of_bigrad {a : FormalDist (End ℂ LatModule)} {D : ℤ}
    (h : ∀ (j w n : ℤ) (p : B), p ∈ gradingZN 1 w →
      a j (mkE n p) ∈ gradingLat (D + ((w : ℤ) + n ^ 2) + j)) :
    GradedFieldLat a D := by
  intro j q x hx
  refine (?_ : gradingLat q ≤ (gradingLat (D + q + j)).comap (a j)) hx
  rw [gradingLat_eq_biSup_pos q]
  refine iSup_le (fun p' => iSup_le (fun hp' => ?_))
  rintro y ⟨z, hz, rfl⟩
  rw [Submodule.mem_comap]
  obtain ⟨hfib, hpos⟩ := hp'
  obtain ⟨w, hw⟩ : ∃ w : ℕ, p'.1 = (w : ℤ) := ⟨p'.1.toNat, by omega⟩
  have hzW : z ∈ gradingZN 1 w := by rw [hw] at hz; exact hz
  have hgoal := h j w p'.2 z hzW
  rwa [show D + ((w : ℤ) + p'.2 ^ 2) + j = D + q + j from by rw [← hfib, hw]] at hgoal


/-- The charge field `Yemα m` is a graded field of weight `m²` (the conformal weight of `e^{mα}`). -/
theorem Yemα_gradedField (m : ℤ) : GradedFieldLat (Yemα m) (m ^ 2) := by
  refine GradedFieldLat.of_bigrad (fun j w n p hp => ?_)
  have := Yemα_bigrad_mem m j w n hp
  rwa [show m ^ 2 + ((w : ℤ) + n ^ 2) + j = m ^ 2 + (w + n ^ 2) + j from by ring]

/-- `alphaLat j (mkE n p)` lies in conformal grade `(w + n²) + (1 + j)` for `p ∈ gradingZN 1 w`. -/
theorem alphaLat_bigrad_mem (j w n : ℤ) {p : B} (hp : p ∈ gradingZN 1 w) :
    alphaLat j (mkE n p) ∈ gradingLat (1 + ((w : ℤ) + n ^ 2) + j) := by
  rw [mkE_apply, alphaLat_tmul]
  refine Submodule.add_mem _ ?_ ?_
  · -- (alphaField j p) ⊗ eⁿ ∈ bigrad (w+j+1, n)
    have hα : alphaField j p ∈ gradingZN 1 ((w : ℤ) + j + 1) := by
      rw [alphaField_apply]
      have := alpha_mem_gradingZN (-j - 1) hp
      rwa [show (w : ℤ) - (-j - 1) = (w : ℤ) + j + 1 from by ring] at this
    by_cases hwj : 0 ≤ (w : ℤ) + j + 1
    · rw [HeisenbergN.gradingZN_of_nonneg hwj] at hα
      have hle := bigrad_le_gradingLat ((w : ℤ) + j + 1).toNat n
        (show (alphaField j p) ⊗ₜ[ℂ] eVec n ∈ bigrad (((w : ℤ) + j + 1).toNat, n) from
          ⟨_, hα, by rw [mkE_apply]⟩)
      rwa [show (((w : ℤ) + j + 1).toNat : ℤ) + n ^ 2 = 1 + ((w : ℤ) + n ^ 2) + j from by
        rw [Int.toNat_of_nonneg hwj]; ring] at hle
    · rw [HeisenbergN.gradingZN_of_neg (by omega), Submodule.mem_bot] at hα
      rw [hα, TensorProduct.zero_tmul]; exact Submodule.zero_mem _
  · -- the j=-1 charge term, conformal weight unchanged = w+n² = 1+(w+n²)+(-1)
    by_cases hj : j = -1
    · rw [if_pos hj]
      refine Submodule.smul_mem _ _ ?_
      have hle := bigrad_le_gradingLat w n
        (show p ⊗ₜ[ℂ] eVec n ∈ bigrad (w, n) from ⟨p, hp, by rw [mkE_apply]⟩)
      rwa [show (w : ℤ) + n ^ 2 = 1 + ((w : ℤ) + n ^ 2) + j from by rw [hj]; ring] at hle
    · rw [if_neg hj]; exact Submodule.zero_mem _

/-- `alphaLat` is a graded field of weight `1` (the boson current has conformal weight `1`). -/
theorem alphaLat_gradedField : GradedFieldLat alphaLat 1 := by
  refine GradedFieldLat.of_bigrad (fun j w n p hp => ?_)
  have := alphaLat_bigrad_mem j w n hp
  rwa [show (1 : ℤ) + ((w : ℤ) + n ^ 2) + j = 1 + ((w : ℤ) + n ^ 2) + j from rfl]


/-- A finite-support finsum of submodule elements lies in the submodule (LatModule version). -/
theorem finsumLat_mem_submodule {ι : Type*} (S : Submodule ℂ LatModule)
    (g : ι → LatModule) (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) :
    (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)

theorem GradedFieldLat.add {a b : FormalDist (End ℂ LatModule)} {D : ℤ}
    (ha : GradedFieldLat a D) (hb : GradedFieldLat b D) : GradedFieldLat (a + b) D := by
  intro j q x hx
  show (a j + b j) x ∈ _
  rw [LinearMap.add_apply]
  exact Submodule.add_mem _ (ha j q x hx) (hb j q x hx)

theorem GradedFieldLat.smul' {a : FormalDist (End ℂ LatModule)} {D : ℤ} (c : ℂ)
    (ha : GradedFieldLat a D) : GradedFieldLat (c • a) D := by
  intro j q x hx
  show (c • a j) x ∈ _
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ c (ha j q x hx)

theorem GradedFieldLat.zero {D : ℤ} :
    GradedFieldLat (0 : FormalDist (End ℂ LatModule)) D := by
  intro j q x hx
  show (0 : End ℂ LatModule) x ∈ _
  rw [LinearMap.zero_apply]; exact Submodule.zero_mem _

theorem GradedFieldLat.deriv {a : FormalDist (End ℂ LatModule)} {D : ℤ}
    (ha : GradedFieldLat a D) : GradedFieldLat (VOA.deriv a) (D + 1) := by
  intro j q x hx
  rw [deriv_apply, ← Int.cast_smul_eq_zsmul ℂ (j + 1), LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  have := ha (j + 1) q x hx
  rwa [show D + q + (j + 1) = D + 1 + q + j from by ring] at this

theorem GradedFieldLat.deriv_iterate {a : FormalDist (End ℂ LatModule)} {D : ℤ}
    (ha : GradedFieldLat a D) (i : ℕ) :
    GradedFieldLat (VOA.deriv^[i] a) (D + i) := by
  induction i with
  | zero => rw [Function.iterate_zero, id]; rwa [Nat.cast_zero, add_zero]
  | succ p ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    have := ih.deriv
    rwa [show D + (p : ℤ) + 1 = D + ((p : ℤ) + 1) from by ring, ← Nat.cast_succ] at this

/-- `genFieldLat i = (i!)⁻¹ ∂^i αLat` is a graded field of weight `i + 1`. -/
theorem genFieldLat_gradedField (i : ℕ) : GradedFieldLat (genFieldLat i) ((i : ℤ) + 1) := by
  rw [genFieldLat]
  have := (alphaLat_gradedField.deriv_iterate i).smul' ((i.factorial : ℂ)⁻¹)
  rwa [show (1 : ℤ) + (i : ℤ) = (i : ℤ) + 1 from by ring] at this

theorem GradedFieldLat.nprod {a b : FormalDist (End ℂ LatModule)}
    (haf : IsField a) (hbf : IsField b) {Da Db : ℤ}
    (ha : GradedFieldLat a Da) (hb : GradedFieldLat b Db) :
    GradedFieldLat (VOA.nprod haf hbf) (Da + Db) := by
  intro s q x hx
  rw [nprod_apply]
  refine finsumLat_mem_submodule _ _
    (normalOrdered_diag_support_finite haf hbf s x) (fun m => ?_)
  rw [normalOrdered_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0, Module.End.mul_apply]
    have hb' := hb (s - m) q x hx
    have ha' := ha m (Db + q + (s - m)) _ hb'
    rwa [show Da + (Db + q + (s - m)) + m = Da + Db + q + s from by ring] at ha'
  · rw [if_neg h0, Module.End.mul_apply]
    have ha' := ha m q x hx
    have hb' := hb (s - m) (Da + q + m) _ ha'
    rwa [show Db + (Da + q + m) + (s - m) = Da + Db + q + s from by ring] at hb'


/-- The conformal weight of a lattice word `(l, m)`: boson degree `∑(i+1)` plus charge weight `m²`. -/
def wordDegLat : List ℕ → ℤ → ℤ
  | [], m => m ^ 2
  | (i :: rest), m => ((i : ℤ) + 1) + wordDegLat rest m

@[simp] theorem wordDegLat_nil (m : ℤ) : wordDegLat [] m = m ^ 2 := rfl

theorem wordDegLat_cons (i : ℕ) (rest : List ℕ) (m : ℤ) :
    wordDegLat (i :: rest) m = ((i : ℤ) + 1) + wordDegLat rest m := rfl

/-- Each lattice word field `YwordLat l m` is a graded field of weight `wordDegLat l m`. -/
theorem YwordLat_gradedField :
    ∀ (l : List ℕ) (m : ℤ), GradedFieldLat (YwordLat l m) (wordDegLat l m)
  | [], m => by rw [YwordLat_nil, wordDegLat_nil]; exact Yemα_gradedField m
  | (i :: rest), m => by
      rw [YwordLat_cons, wordDegLat_cons]
      exact GradedFieldLat.nprod (genFieldLat_isField i) (YwordLat_isField rest m)
        (genFieldLat_gradedField i) (YwordLat_gradedField rest m)

/-- The span of the lattice word states of conformal weight `q`. -/
noncomputable def HSpanLat (q : ℤ) : Submodule ℂ LatModule :=
  Submodule.span ℂ {x | ∃ (l : List ℕ) (m : ℤ), wordDegLat l m = q ∧ wordStateLat l m = x}


/-- `wordDegLat l m = ((∑_{i∈l}(i+1)) : ℕ) + m²`, the boson word weight plus the charge weight. -/
theorem wordDegLat_eq_sum (l : List ℕ) (m : ℤ) :
    wordDegLat l m = (((l.map (fun i => i + 1)).sum : ℕ) : ℤ) + m ^ 2 := by
  induction l with
  | nil => rw [wordDegLat_nil]; simp
  | cons i rest ih =>
      rw [wordDegLat_cons, ih, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_add,
        Nat.cast_one]
      ring

/-- `wordDegLat ((monoWordN a).map Prod.fst) m = (weight a : ℤ) + m²`. -/
theorem wordDegLat_monoWordN (a : (ℕ × Fin 1) →₀ ℕ) (m : ℤ) :
    wordDegLat ((HeisenbergN.monoWordN a).map Prod.fst) m
      = ((Finsupp.weight HeisenbergN.weightFnN a : ℕ) : ℤ) + m ^ 2 := by
  rw [wordDegLat_eq_sum]
  congr 2
  rw [← HeisenbergN.wordWeightNN_monoWordN_eq_weight a, HeisenbergN.wordWeightNN, List.map_map]
  rfl

/-- Each weight-`w` monomial tensor `e^{nα}` is a degree-`(w+n²)` word state, hence in `HSpanLat`. -/
theorem monomial_tmul_mem_HSpanLat (a : (ℕ × Fin 1) →₀ ℕ) (w : ℕ) (n : ℤ)
    (ha : Finsupp.weight HeisenbergN.weightFnN a = w) :
    (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eVec n ∈ HSpanLat ((w : ℤ) + n ^ 2) := by
  have hword : wordStateLat ((HeisenbergN.monoWordN a).map Prod.fst) n
      = (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eVec n := by
    rw [wordStateLat_eq, List.map_map,
      show (HeisenbergN.monoWordN a).map ((fun i => ((i, 0) : ℕ × Fin 1)) ∘ Prod.fst)
          = HeisenbergN.monoWordN a from by
        rw [List.map_congr_left (g := id) (fun e _ => by
            simp only [Function.comp_apply, id_eq]
            exact Prod.ext rfl (Subsingleton.elim _ _)), List.map_id],
      HeisenbergN.wordStateN_monoWordN]
  rw [← hword]
  refine Submodule.subset_span ⟨(HeisenbergN.monoWordN a).map Prod.fst, n, ?_, rfl⟩
  rw [wordDegLat_monoWordN, ha]


/-- `mkE n p ∈ HSpanLat (w + n²)` for `p ∈ gradingWN 1 w` (decompose `p` over its weight-`w`
monomials, each a degree-`(w+n²)` word state). -/
theorem mkE_mem_HSpanLat (w : ℕ) (n : ℤ) {p : B} (hp : p ∈ gradingWN 1 w) :
    mkE n p ∈ HSpanLat ((w : ℤ) + n ^ 2) := by
  classical
  rw [mkE_apply, ← MvPolynomial.support_sum_monomial_coeff p, TensorProduct.sum_tmul]
  refine Submodule.sum_mem _ (fun a ha => ?_)
  rw [show (MvPolynomial.monomial a (MvPolynomial.coeff a p))
        = (MvPolynomial.coeff a p) • MvPolynomial.monomial a (1 : ℂ) from by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
    ← TensorProduct.smul_tmul' (MvPolynomial.coeff a p) (MvPolynomial.monomial a (1 : ℂ)) (eVec n)]
  refine Submodule.smul_mem _ _ ?_
  have hwa : Finsupp.weight HeisenbergN.weightFnN a = w := by
    rw [HeisenbergN.mem_gradingWN] at hp
    exact hp (by rw [MvPolynomial.coeff]; exact Finsupp.mem_support_iff.mp ha)
  exact monomial_tmul_mem_HSpanLat a w n hwa

/-- **Homogeneous spanning**: `gradingLat q ≤ HSpanLat q` (each conformal-weight space is spanned by
the degree-`q` lattice word states). -/
theorem gradingLat_le_HSpanLat (q : ℤ) : gradingLat q ≤ HSpanLat q := by
  rw [gradingLat_eq_biSup_pos q]
  refine iSup_le (fun p' => iSup_le (fun hp' => ?_))
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨hfib, hpos⟩ := hp'
  obtain ⟨w, hw⟩ : ∃ w : ℕ, p'.1 = (w : ℤ) := ⟨p'.1.toNat, by omega⟩
  have hzW : z ∈ gradingWN 1 w := by
    rw [hw, HeisenbergN.gradingZN_of_nonneg (by positivity), Int.toNat_natCast] at hz; exact hz
  have := mkE_mem_HSpanLat w p'.2 hzW
  rwa [show (w : ℤ) + p'.2 ^ 2 = q from by rw [← hfib, hw]] at this

/-- A graded field `a` of weight `D` is graded on each `HSpanLat`-spanning word state at the
homogeneous level (combining `YwordLat_gradedField` with the spanning). -/
theorem GradedFieldLat.of_HSpan {a : LatModule → FormalDist (End ℂ LatModule)}
    (hgen : ∀ (l : List ℕ) (m : ℤ), a (wordStateLat l m) = YwordLat l m)
    (hlin : ∀ (x y : LatModule), a (x + y) = a x + a y)
    (hsmul : ∀ (c : ℂ) (x : LatModule), a (c • x) = c • a x)
    (hzero : a 0 = 0)
    (p : ℤ) {u : LatModule} (hu : u ∈ HSpanLat p) :
    GradedFieldLat (a u) p := by
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, m, hl, rfl⟩ := hz
      rw [hgen, ← hl]; exact YwordLat_gradedField l m
  | zero => rw [hzero]; exact GradedFieldLat.zero
  | add x y _ _ ihx ihy => rw [hlin]; exact GradedFieldLat.add ihx ihy
  | smul c x _ ihx => rw [hsmul]; exact GradedFieldLat.smul' c ihx

/-- `Yfull u` is a graded field of conformal weight `p` whenever `u ∈ gradingLat p`
(via homogeneous spanning `gradingLat ≤ HSpanLat` and `GradedFieldLat.of_HSpan`). -/
theorem Yfull_gradedField_of_mem {p : ℤ} {u : LatModule} (hu : u ∈ gradingLat p) :
    GradedFieldLat (Yfull hYloc u) p :=
  GradedFieldLat.of_HSpan (Yfull_word hYloc)
    (fun x y => map_add (Yfull hYloc) x y)
    (fun c x => map_smul (Yfull hYloc) c x)
    (map_zero (Yfull hYloc)) p (gradingLat_le_HSpanLat p hu)

/-- **VA1 (grading_mode)**: `mode (Yfull u) j v ∈ gradingLat (p + q - j - 1)`. -/
theorem Yfull_grading_mode {p q : ℤ} (u : LatModule) (hu : u ∈ gradingLat p)
    (v : LatModule) (hv : v ∈ gradingLat q) (j : ℤ) :
    mode (Yfull hYloc u) j v ∈ gradingLat (p + q - j - 1) := by
  rw [mode_apply]
  have := Yfull_gradedField_of_mem hYloc hu (-j - 1) q v hv
  rwa [show p + q + (-j - 1) = p + q - j - 1 from by ring] at this

/-! ## The assembled VOA. -/

/-- **The lattice A₁ vertex operator algebra** (central charge `1`), gated only on the
charge-pair locality `hYloc`. -/
noncomputable def latticeVOA_A1_of_locality
    (hYloc : ∀ m m' : ℤ, Local (Yemα m) (Yemα m')) :
    VertexOperatorAlgebra LatModule where
  grading := gradingLat
  isInternal := gradingLat_isInternal
  finrank := gradingLat_finrank
  Y := Yfull hYloc
  vacuum := latVacuum
  vacuum_mem := by
    rw [gradingLat_zero_eq_span_vacuum]; exact Submodule.mem_span_singleton_self latVacuum
  grading_mode := fun u hu v hv j => Yfull_grading_mode hYloc u hu v hv j
  vacuum_Y := Yfull_vacuum hYloc
  creation := Yfull_creation hYloc
  locality := Yfull_local hYloc
  regularity := Yfull_regularity hYloc
  conformalVector := omegaLat
  conformal_mem := omegaLat_mem
  centralCharge := 1
  virasoro := Yfull_virasoro hYloc
  L0_grading := fun v hv => Yfull_L0_grading hYloc v hv
  translation := Yfull_translation_omega hYloc
  vacuum_grade := gradingLat_zero_eq_span_vacuum
  positivity := fun n hn => gradingLat_positivity n hn

end VOA.LatExp
