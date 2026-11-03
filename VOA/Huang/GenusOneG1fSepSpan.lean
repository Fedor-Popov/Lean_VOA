import VOA.Huang.GenusOneG1fSubstitution

/-!
# Bracket modes into an arbitrary ordinary module, and their spanning property

`bracketGen Y` is the explicit bracket field `Y(e^{zL(0)} w, e^z − 1)` (same coefficients
`bracketCoeff`), for an intertwiner `Y` whose TARGET is any ordinary module (e.g. a fusion product,
which is not a lowest-weight module). It commutes with module maps into lowest-weight modules
(`map_bracketGen`: `g ∘ Y[·] = (g ∘ Y)[·]`).

`coeff_mem_of_bracket`: the bracket coefficients `Y[C_P w]_n C_Q x` of the coordinate-changed
insertions (`w, x` ordinary-homogeneous) span the same space as all ordinary coefficients
`Y_m(w) x` — a triangularity argument by induction on the (bounded-below) output weight; no
coordinate change on the target is needed.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1f

open VOA
open VOA.Huang.GenusOne.IntCoord (bracketModes bracketCoeff bracketModes_of_weight
  bracketCoeff_zero)
open VOA.Huang.GenusTwoPoint (moduleLevelLE mem_moduleLevelLE moduleLevelLE_mono
  exists_mem_moduleLevelLE)
open VOA.Huang.GenusTwoPoint.Separate (normalizedCoordinateChange
  normalizedCoordinateChange_sub_mem_lower normalizedCoordinateChange_mem)
open VOA.Huang.FusionUnit (homSpace)
open VOA.Huang.FusionProduct (postcompose)
open scoped BigOperators

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P Q : LWModule W} {M : Type u} [AddCommGroup M] [Module ℂ M] {A : OrdVModule W M}

/-! ## §1 The explicit bracket field with an arbitrary target -/

theorem weighted_support_finite (Y : IntertwiningOperator P.isMod Q.isMod A)
    (c : ℕ → ℂ) (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    (Function.support (fun r : ℕ => c r • Y.val (n + r) w x)).Finite := by
  obtain ⟨K, hK⟩ := Y.property.truncation w x n
  refine (Finset.range K.toNat).finite_toSet.subset fun r hr => ?_
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have hrK : K ≤ (r : ℤ) := by omega
  exact hr (by simpa using congrArg (c r • ·) (hK r hrK))

theorem intertwiner_nat_bound' (Y : IntertwiningOperator P.isMod Q.isMod A) (n : ℂ)
    (w : P.carrier) (x : Q.carrier) : ∃ S : ℕ, ∀ s : ℕ, S ≤ s → Y.val (n + s) w x = 0 := by
  obtain ⟨K, hK⟩ := Y.property.truncation w x n
  refine ⟨K.toNat, fun s hs => ?_⟩
  have := hK (s : ℤ) (by omega)
  simpa using this

/-- Homogeneous piece of the explicit bracket field. -/
def bracketAtWeightG (Y : IntertwiningOperator P.isMod Q.isMod A) (α n : ℂ) :
    P.carrier →ₗ[ℂ] Q.carrier →ₗ[ℂ] M where
  toFun w :=
    { toFun := fun x => ∑ᶠ r : ℕ, bracketCoeff α n r • Y.val (n + r) w x
      map_add' x y := by
        simp only [map_add, smul_add]
        exact finsum_add_distrib (weighted_support_finite Y _ n w x)
          (weighted_support_finite Y _ n w y)
      map_smul' c x := by
        simp only [map_smul, RingHom.id_apply, smul_comm (bracketCoeff α n _) c]
        exact (smul_finsum' c (weighted_support_finite Y _ n w x)).symm }
  map_add' w v := by
    ext x
    simp only [map_add, LinearMap.add_apply, smul_add]
    exact finsum_add_distrib (weighted_support_finite Y _ n w x)
      (weighted_support_finite Y _ n v x)
  map_smul' c w := by
    ext x
    simp only [map_smul, RingHom.id_apply, LinearMap.smul_apply,
      smul_comm (bracketCoeff α n _) c]
    exact (smul_finsum' c (weighted_support_finite Y _ n w x)).symm

/-- The explicit bracket field, any ordinary target. -/
def bracketGen (Y : IntertwiningOperator P.isMod Q.isMod A) :
    IntertwiningModes P.carrier Q.carrier M := fun n =>
  letI := DirectSum.IsInternal.chooseDecomposition P.isMod.weight P.isMod.isInternal
  (DFinsupp.lsum ℂ (fun α =>
    (bracketAtWeightG Y α n).comp (P.isMod.weight α).subtype)).comp
    (DirectSum.decomposeLinearEquiv P.isMod.weight).toLinearMap

theorem bracketGen_of_weight (Y : IntertwiningOperator P.isMod Q.isMod A)
    {α : ℂ} {w : P.carrier} (hw : w ∈ P.isMod.weight α) (n : ℂ) (x : Q.carrier) :
    bracketGen Y n w x = ∑ᶠ r : ℕ, bracketCoeff α n r • Y.val (n + r) w x := by
  letI := DirectSum.IsInternal.chooseDecomposition P.isMod.weight P.isMod.isInternal
  change ((DFinsupp.lsum ℂ (fun α =>
    (bracketAtWeightG Y α n).comp (P.isMod.weight α).subtype))
      (DirectSum.decompose P.isMod.weight w)) x = _
  rw [DirectSum.decompose_of_mem P.isMod.weight hw]
  exact congrArg (fun f : Q.carrier →ₗ[ℂ] M => f x)
    (DFinsupp.lsum_single ℂ (fun α =>
      (bracketAtWeightG Y α n).comp (P.isMod.weight α).subtype) α ⟨w, hw⟩)

theorem bracketGen_eq_sum_range (Y : IntertwiningOperator P.isMod Q.isMod A)
    {α : ℂ} {w : P.carrier} (hw : w ∈ P.isMod.weight α) (n : ℂ) (x : Q.carrier)
    (K : ℕ) (hK : ∀ r : ℕ, K ≤ r → Y.val (n + r) w x = 0) :
    bracketGen Y n w x =
      ∑ r ∈ Finset.range K, bracketCoeff α n r • Y.val (n + r) w x := by
  rw [bracketGen_of_weight Y hw]
  apply finsum_eq_sum_of_support_subset
  intro r hr
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hr (by dsimp; rw [hK r (le_of_not_gt h), smul_zero])

/-- **Bracket modes commute with module maps into lowest-weight modules.** -/
theorem map_bracketGen (Y : IntertwiningOperator P.isMod Q.isMod A) (N : LWModule W)
    (g : homSpace A N.isMod) (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    g.val (bracketGen Y n w x) = bracketModes (postcompose Y N.isMod g) n w x := by
  refine FusionTop.induction_weight P.isMod w (by simp) ?_ ?_
  · intro w v hw hv
    simp only [map_add, LinearMap.add_apply, hw, hv]
  · intro α w hw
    obtain ⟨K, hK⟩ := intertwiner_nat_bound' Y n w x
    rw [bracketGen_eq_sum_range Y hw n x K hK,
      VOA.Huang.GenusOne.IntCoord.bracketModes_eq_sum_range (postcompose Y N.isMod g) hw n x K
        (fun r hr => by
          change g.val (Y.val (n + r) w x) = 0
          rw [hK r hr, map_zero]),
      map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul]
    rfl

/-! ## §2 Triangularity: the bracket coefficients of coordinate-changed insertions span -/

theorem coeff_eq_zero_of_low (Y : IntertwiningOperator P.isMod Q.isMod A) {B : ℝ}
    (hB : ∀ μ : ℂ, A.weight μ ≠ ⊥ → B ≤ μ.re) {α β : ℂ} {w : P.carrier} {x : Q.carrier}
    (hw : w ∈ P.isMod.weight α) (hx : x ∈ Q.isMod.weight β) (m : ℂ)
    (hlow : (α + β - m - 1).re < B) : Y.val m w x = 0 := by
  have hm := FusionTop.mem_weight Y.property hw hx m
  by_cases h : A.weight (α + β - m - 1) = ⊥
  · rw [h] at hm; exact (Submodule.mem_bot ℂ).mp hm
  · exact absurd (hB _ h) (not_le.mpr hlow)

theorem bracketGen_sub_mem (Y : IntertwiningOperator P.isMod Q.isMod A) (S' : Submodule ℂ M)
    {a : ℤ} (m : ℂ) (x : Q.carrier)
    (hS' : ∀ (r : ℕ) (w' : P.carrier), w' ∈ moduleLevelLE P a →
      Y.val (m + ((r + 1 : ℕ) : ℂ)) w' x ∈ S')
    {w : P.carrier} (hw : w ∈ moduleLevelLE P a) :
    bracketGen Y m w x - Y.val m w x ∈ S' := by
  induction hw using Submodule.iSup_induction' with
  | mem j w hwj =>
    have hwa : w ∈ moduleLevelLE P a := mem_moduleLevelLE P j.2 hwj
    obtain ⟨R, hR⟩ := intertwiner_nat_bound' Y m w x
    rw [bracketGen_eq_sum_range Y hwj m x (R + 1) (fun r hr => hR r (by omega)),
      Finset.sum_range_succ', bracketCoeff_zero, one_smul, Nat.cast_zero, add_zero,
      add_sub_cancel_right]
    exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (hS' r w hwa)
  | zero => simp
  | add w v _ _ hw hv =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      show bracketGen Y m w x + bracketGen Y m v x - (Y.val m w x + Y.val m v x) =
        (bracketGen Y m w x - Y.val m w x) + (bracketGen Y m v x - Y.val m v x) by abel]
    exact Submodule.add_mem _ hw hv

theorem re_shift (h₁ h₂ m : ℂ) (j l : ℤ) :
    ((h₁ + (j : ℂ)) + (h₂ + (l : ℂ)) - m - 1).re = (h₁ + h₂ - m - 1).re + j + l := by
  simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re, Complex.one_re]
  ring

/-- **Spanning by bracket coefficients.** If a subspace contains every bracket coefficient
`Y[C_P w]_n C_Q x` (`w`, `x` ordinary-homogeneous), it contains every coefficient `Y_m(w) x`. -/
theorem coeff_mem_of_bracket (Y : IntertwiningOperator P.isMod Q.isMod A) (S : Submodule ℂ M)
    (hS : ∀ (n α β : ℂ) (w : P.carrier) (x : Q.carrier), w ∈ P.isMod.weight α →
      x ∈ Q.isMod.weight β →
        bracketGen Y n (normalizedCoordinateChange P w) (normalizedCoordinateChange Q x) ∈ S)
    (n : ℂ) (w : P.carrier) (x : Q.carrier) : Y.val n w x ∈ S := by
  obtain ⟨B, hB⟩ := A.boundedBelow
  have claim : ∀ N : ℕ, ∀ (m : ℂ) (a b : ℤ) (w : P.carrier) (x : Q.carrier),
      w ∈ moduleLevelLE P a → x ∈ moduleLevelLE Q b →
        (P.h + Q.h - m - 1).re + a + b < B + N → Y.val m w x ∈ S := by
    intro N
    induction N with
    | zero =>
      intro m a b w x hw hx hlt
      induction hw using Submodule.iSup_induction' with
      | mem j w hwj =>
        induction hx using Submodule.iSup_induction' with
        | mem l x hxl =>
          rw [coeff_eq_zero_of_low Y hB hwj hxl m (by
            rw [re_shift]; have := j.2; have := l.2; push_cast at hlt ⊢
            have h1 : ((j : ℤ) : ℝ) ≤ a := by exact_mod_cast j.2
            have h2 : ((l : ℤ) : ℝ) ≤ b := by exact_mod_cast l.2
            linarith)]
          exact S.zero_mem
        | zero => rw [map_zero]; exact S.zero_mem
        | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
      | zero => rw [map_zero, LinearMap.zero_apply]; exact S.zero_mem
      | add w v _ _ hw hv => rw [map_add, LinearMap.add_apply]; exact S.add_mem hw hv
    | succ N ih =>
      intro m a b w x hw hx hlt
      induction hw using Submodule.iSup_induction' with
      | mem j w hwj =>
        induction hx using Submodule.iSup_induction' with
        | mem l x hxl =>
          have h1 : ((j : ℤ) : ℝ) ≤ a := by exact_mod_cast j.2
          have h2 : ((l : ℤ) : ℝ) ≤ b := by exact_mod_cast l.2
          have htop : (P.h + Q.h - m - 1).re + (j : ℤ) + (l : ℤ) < B + (N + 1 : ℕ) := by
            push_cast at hlt ⊢; linarith
          by_cases hlow : ((P.h + ((j : ℤ) : ℂ)) + (Q.h + ((l : ℤ) : ℂ)) - m - 1).re < B
          · rw [coeff_eq_zero_of_low Y hB hwj hxl m hlow]; exact S.zero_mem
          have hwj' : w ∈ moduleLevelLE P (j : ℤ) := mem_moduleLevelLE P le_rfl hwj
          have hxl' : x ∈ moduleLevelLE Q (l : ℤ) := mem_moduleLevelLE Q le_rfl hxl
          have hCw := normalizedCoordinateChange_mem P hwj'
          have hCx := normalizedCoordinateChange_mem Q hxl'
          have hw1 : normalizedCoordinateChange P w - w ∈ moduleLevelLE P ((j : ℤ) - 1) :=
            normalizedCoordinateChange_sub_mem_lower P hwj'
          have hx1 : normalizedCoordinateChange Q x - x ∈ moduleLevelLE Q ((l : ℤ) - 1) :=
            normalizedCoordinateChange_sub_mem_lower Q hxl'
          have e : Y.val m w x =
              bracketGen Y m (normalizedCoordinateChange P w) (normalizedCoordinateChange Q x) -
              (bracketGen Y m (normalizedCoordinateChange P w) (normalizedCoordinateChange Q x) -
                Y.val m (normalizedCoordinateChange P w) (normalizedCoordinateChange Q x)) -
              Y.val m (normalizedCoordinateChange P w - w) (normalizedCoordinateChange Q x) -
              Y.val m w (normalizedCoordinateChange Q x - x) := by
            simp only [map_sub, LinearMap.sub_apply]
            abel
          rw [e]
          refine S.sub_mem (S.sub_mem (S.sub_mem (hS m _ _ w x hwj hxl) ?_) ?_) ?_
          · refine bracketGen_sub_mem Y S m _ (fun r w' hw' => ?_) hCw
            refine ih (m + ((r + 1 : ℕ) : ℂ)) (j : ℤ) (l : ℤ) w' _ hw' hCx ?_
            have : (P.h + Q.h - (m + ((r + 1 : ℕ) : ℂ)) - 1).re =
                (P.h + Q.h - m - 1).re - (r + 1 : ℕ) := by
              simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
              ring
            rw [this]
            have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
            push_cast at htop ⊢
            linarith
          · refine ih m ((j : ℤ) - 1) (l : ℤ) _ _ hw1 hCx ?_
            push_cast at htop ⊢
            linarith
          · refine ih m (j : ℤ) ((l : ℤ) - 1) _ _ hwj' hx1 ?_
            push_cast at htop ⊢
            linarith
        | zero => rw [map_zero]; exact S.zero_mem
        | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
      | zero => rw [map_zero, LinearMap.zero_apply]; exact S.zero_mem
      | add w v _ _ hw hv => rw [map_add, LinearMap.add_apply]; exact S.add_mem hw hv
  obtain ⟨a, ha⟩ := exists_mem_moduleLevelLE P w
  obtain ⟨b, hb⟩ := exists_mem_moduleLevelLE Q x
  obtain ⟨N, hN⟩ := exists_nat_gt ((P.h + Q.h - n - 1).re + a + b - B)
  exact claim N n a b w x ha hb (by linarith)

end VOA.Huang.GenusOneG1f
