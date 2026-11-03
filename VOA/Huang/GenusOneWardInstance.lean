import VOA.Huang.GenusOneWardRelations

/-!
# The two-point minus-one Ward identity for actual traces

The abstract assembly `ward_neg_one_abstract` is instantiated with the actual
level traces of a homogeneous state of positive weight. The result is the
collected identity in `ℂ⟦u⟧⟦t⟧`, with Eisenstein series and spatial kernels,
for homogeneous insertions.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.QEquation (TailBound)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

section Inst
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

/-- Left descendants `F_j = Φ(c₍ⱼ₎x, y)`. -/
def famF (c : V) (kc : ℤ) (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (j : ℤ) : R2 :=
  phiH Y₁ Y₂ (mode (P₁.isMod.YM c) j x) y (α₁ + (kc : ℂ) - (j : ℤ) - 1) α₂

/-- Right descendants `G_j = Φ(x, c₍ⱼ₎y)`. -/
def famG (c : V) (kc : ℤ) (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (j : ℤ) : R2 :=
  phiH Y₁ Y₂ x (mode (P₂.isMod.YM c) j y) α₁ (α₂ + (kc : ℂ) - (j : ℤ) - 1)

/-- Boundary-mode traces. -/
def famA (c : V) (kc : ℤ) (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (p : ℤ) : R2 :=
  ofZ (AZ Y₁ Y₂ c kc x y α₁ α₂ p)

/-- Middle-mode traces. -/
def famM (c : V) (kc : ℤ) (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (i : ℕ) : R2 :=
  ofZ (MZ Y₁ Y₂ c kc x y α₁ α₂ i)

variable {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier} {c : V} {kc : ℤ}

theorem vanishes_tauZ (x : P₁.carrier) {y : P₂.carrier} (α₁ : ℂ) (hy : y ∈ P₂.isMod.weight α₂) :
    Vanishes (tauZ Y₁ Y₂ x y α₁ α₂) := by
  intro n k h
  rcases h with h | h
  · exact tauZ_neg_left Y₁ Y₂ x y α₁ α₂ h k
  · exact tauZ_neg_right Y₁ Y₂ hy x α₁ n h

theorem vanishes_AZ (hy : y ∈ P₂.isMod.weight α₂) (p : ℤ) :
    Vanishes (AZ Y₁ Y₂ c kc x y α₁ α₂ p) := by
  intro n k h
  rcases h with h | h
  · exact AZ_neg_left Y₁ Y₂ c kc x y α₁ α₂ p h k
  · exact AZ_neg_right Y₁ Y₂ hy c kc x α₁ p n h

theorem binSum_famF (K : ℕ) (p : ℤ) :
    binSum K (famF Y₁ Y₂ c kc x y α₁ α₂) p = ofZ fun n k =>
      ∑ j ∈ Finset.range K, cbz p j * tauZ Y₁ Y₂ (mode (P₁.isMod.YM c) j x) y
        (α₁ + (kc : ℂ) - (j : ℤ) - 1) α₂ n k := by
  apply ext2
  intro n k
  simp only [binSum, c2_sum, c2_smul, c2_ofZ, famF, phiH, c2_mk2]

theorem binSum_famG (K : ℕ) (p : ℤ) :
    binSum K (famG Y₁ Y₂ c kc x y α₁ α₂) p = ofZ fun n k =>
      ∑ j ∈ Finset.range K, cbz p j * tauZ Y₁ Y₂ x (mode (P₂.isMod.YM c) j y)
        α₁ (α₂ + (kc : ℂ) - (j : ℤ) - 1) n k := by
  apply ext2
  intro n k
  simp only [binSum, c2_sum, c2_smul, c2_ofZ, famG, phiH, c2_mk2]

theorem vanishes_binF (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ) (p : ℤ) :
    Vanishes fun n k => ∑ j ∈ Finset.range K, cbz p j * tauZ Y₁ Y₂ (mode (P₁.isMod.YM c) j x) y
      (α₁ + (kc : ℂ) - (j : ℤ) - 1) α₂ n k := by
  intro n k h
  apply Finset.sum_eq_zero
  intro j _
  rw [vanishes_tauZ Y₁ Y₂ _ _ hy n k h, mul_zero]

theorem vanishes_binG (hc : c ∈ W.grading kc) (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ) (p : ℤ) :
    Vanishes fun n k => ∑ j ∈ Finset.range K, cbz p j * tauZ Y₁ Y₂ x (mode (P₂.isMod.YM c) j y)
      α₁ (α₂ + (kc : ℂ) - (j : ℤ) - 1) n k := by
  intro n k h
  apply Finset.sum_eq_zero
  intro j _
  rw [vanishes_tauZ Y₁ Y₂ _ _ (mode_mem_weight P₂.isMod hc hy j) n k h, mul_zero]

/-- Cyclicity for a positive shift. -/
theorem famA_pos (hc : c ∈ W.grading kc) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) (d : ℕ) :
    (1 - qq ^ d) * famA Y₁ Y₂ c kc x y α₁ α₂ (kc - 1 - d) =
      -(qq ^ d * binSum K (famF Y₁ Y₂ c kc x y α₁ α₂) (kc - 1 - d) +
        uu ^ d * binSum K (famG Y₁ Y₂ c kc x y α₁ α₂) (kc - 1 - d)) := by
  apply ext2
  intro n k
  rw [binSum_famF, binSum_famG, sub_mul, one_mul, c2_sub, c2_neg, c2_add, famA, c2_ofZ,
    c2_qq_pow_ofZ (vanishes_AZ Y₁ Y₂ hy _), c2_qq_pow_ofZ (vanishes_binF Y₁ Y₂ hy K _),
    c2_uu_pow_ofZ (vanishes_binG Y₁ Y₂ hc hy K _)]
  have h := AZ_cyc Y₁ Y₂ hc hx hy K hK (kc - 1 - d) n k
  rw [show kc - 1 - (kc - 1 - (d : ℤ)) = d by ring] at h
  rw [h]
  ring

/-- Cyclicity for a negative shift. -/
theorem famA_neg (hc : c ∈ W.grading kc) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) (e : ℕ) :
    (1 - qq ^ e) * famA Y₁ Y₂ c kc x y α₁ α₂ (kc - 1 + e) =
      binSum K (famF Y₁ Y₂ c kc x y α₁ α₂) (kc - 1 + e) +
        tt ^ e * binSum K (famG Y₁ Y₂ c kc x y α₁ α₂) (kc - 1 + e) := by
  apply ext2
  intro n k
  rw [binSum_famF, binSum_famG, sub_mul, one_mul, c2_sub, c2_add, famA, c2_ofZ,
    c2_qq_pow_ofZ (vanishes_AZ Y₁ Y₂ hy _), c2_ofZ,
    c2_tt_pow_ofZ (vanishes_binG Y₁ Y₂ hc hy K _)]
  have h := AZ_cyc Y₁ Y₂ hc hx hy K hK (kc - 1 + e) ((n : ℤ) - e) ((k : ℤ) - e)
  rw [show kc - 1 - (kc - 1 + (e : ℤ)) = -e by ring,
    show (n : ℤ) - e - -(e : ℤ) = n by ring, show (k : ℤ) - e - -(e : ℤ) = k by ring] at h
  rw [h]
  ring

/-- The zero-mode relation. -/
theorem fam_zero (hc : c ∈ W.grading kc) (hx : x ∈ P₁.isMod.weight α₁)
    (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) :
    binSum K (famF Y₁ Y₂ c kc x y α₁ α₂) (kc - 1) +
      binSum K (famG Y₁ Y₂ c kc x y α₁ α₂) (kc - 1) = 0 := by
  apply ext2
  intro n k
  rw [binSum_famF, binSum_famG, c2_add, c2_ofZ, c2_ofZ, c2_zero]
  have h := AZ_cyc Y₁ Y₂ hc hx hy K hK (kc - 1) n k
  rw [show kc - 1 - (kc - 1) = (0 : ℤ) by ring, sub_zero, sub_zero] at h
  linear_combination h

/-- The middle mode relation. -/
theorem famM_eq (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) (i : ℕ) :
    famM Y₁ Y₂ c kc x y α₁ α₂ i =
      famA Y₁ Y₂ c kc x y α₁ α₂ i - binSum K (famF Y₁ Y₂ c kc x y α₁ α₂) i := by
  apply ext2
  intro n k
  rw [binSum_famF, c2_sub, famM, famA, c2_ofZ, c2_ofZ, c2_ofZ, MZ_eq Y₁ Y₂ K hK]

theorem negOnePow_mul_cbz_neg_one (i : ℕ) : negOnePow (i : ℤ) * cbz (-1) (i : ℤ) = 1 := by
  rw [negOnePow_natCast, cbz_apply_nonneg _ (by omega), Int.toNat_natCast, gBinom_neg_one,
    ← mul_pow]
  norm_num

/-- The Jacobi expansion of the minus-one descendant, through the trace. -/
theorem famF_neg_one_iterate (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) :
    famF Y₁ Y₂ c kc x y α₁ α₂ (-1) =
      lsum fun i : ℕ => famA Y₁ Y₂ c kc x y α₁ α₂ (-1 - i) + famM Y₁ Y₂ c kc x y α₁ α₂ i := by
  apply ext2
  intro n k
  set s₀ := sMode N Q (α₁ + (kc : ℂ) - ((-1 : ℤ) : ℂ) - 1) n k with hs₀
  set r := rMode N Q α₂ n k with hr
  obtain ⟨I, hI⟩ := VOA.Huang.GenusTwoPoint.Separate.product_insertion_cutoff Y₁ Y₂ hx hy c
    s₀ r (N.h + n)
  have hAm : ∀ i : ℕ, AZ Y₁ Y₂ c kc x y α₁ α₂ (-1 - i) n k =
      lvl N (mode (N.isMod.YM c) (-1 - i) *
        ((Y₁.val (s₀ + ((i : ℤ) : ℂ)) x).comp (Y₂.val r y))) n := by
    intro i
    unfold AZ
    congr 3
    rw [hs₀]; unfold sMode; push_cast; ring
  have hMm : ∀ i : ℕ, MZ Y₁ Y₂ c kc x y α₁ α₂ i n k =
      lvl N ((Y₁.val ((-1 : ℤ) + s₀ - ((i : ℤ) : ℂ)) x).comp
        ((mode (Q.isMod.YM c) i).comp (Y₂.val r y))) n := by
    intro i
    unfold MZ
    congr 3
    rw [hs₀]; unfold sMode; push_cast; ring
  rw [c2_lsum_eq_sum (B := I) (fun i hi => by
    rw [c2_add, famA, famM, c2_ofZ, c2_ofZ, hAm, hMm]
    rw [lvl_eq_zero_of_kills N _ _ (fun v hv => by
          rw [Module.End.mul_apply, LinearMap.comp_apply, (hI i (by omega) v hv).1, map_zero]),
      lvl_eq_zero_of_kills N _ _ (fun v hv => by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, (hI i (by omega) v hv).2, map_zero]),
      add_zero])]
  rw [famF, phiH, c2_mk2]
  unfold tauZ
  rw [← hs₀, ← hr]
  have he : lvl N ((Y₁.val s₀ (mode (P₁.isMod.YM c) (-1) x)).comp (Y₂.val r y)) n =
      lvl N (∑ i ∈ Finset.range I, (negOnePow i * cbz (-1) i) •
        (mode (N.isMod.YM c) (-1 - i) * ((Y₁.val (s₀ + i) x).comp (Y₂.val r y)) -
          negOnePow (-1) • (Y₁.val ((-1 : ℤ) + s₀ - i) x).comp
            ((mode (Q.isMod.YM c) i).comp (Y₂.val r y)))) n := by
    unfold lvl
    apply VOA.Huang.GenusTwoPoint.Separate.gradedTraceOp_congr_on_weight
    intro v hv
    have hv' : v ∈ N.isMod.weight (N.h + n) := by convert hv using 2; push_cast; ring
    have h := HuangODEModes.iterate_range Y₁.property c x (Y₂.val r y v) (-1) s₀ I
      (fun i hi => hI i hi v hv')
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.sub_apply, Module.End.mul_apply] using h
  rw [he, lvl_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [c2_add, famA, famM, c2_ofZ, c2_ofZ, hAm, hMm, lvl_smul, lvl_sub, lvl_smul,
    negOnePow_mul_cbz_neg_one, negOnePow_neg_one]
  push_cast
  ring

/-- **The two-point minus-one Ward identity for actual traces**, homogeneous case. -/
theorem ward_neg_one_trace {kc : ℕ} (hk : 1 ≤ kc) (hc : c ∈ W.grading (kc : ℤ))
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂) (K : ℕ)
    (hK : TailBound P₁.isMod.toWeakModule P₂.isMod.toWeakModule c x y K) :
    famF Y₁ Y₂ c kc x y α₁ α₂ (-1) +
        ∑ j ∈ Finset.range K, sqBracketCoeffZ kc (-1) j • famF Y₁ Y₂ c kc x y α₁ α₂ j =
      famA Y₁ Y₂ c kc x y α₁ α₂ ((kc : ℤ) - 1) +
      ∑ m ∈ Finset.range K, eis (m + 1) *
        ∑ j ∈ Finset.range K, sqBracketCoeff kc (2 * m + 1) j • famF Y₁ Y₂ c kc x y α₁ α₂ j +
      ∑ m ∈ Finset.range K, (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
        ∑ j ∈ Finset.range K, sqBracketCoeff kc m j • famG Y₁ Y₂ c kc x y α₁ α₂ j :=
  ward_neg_one_abstract hk K _ _ _ (famM Y₁ Y₂ c kc x y α₁ α₂)
    (fun d _ => famA_pos Y₁ Y₂ hc hx hy K hK d)
    (fun e _ => famA_neg Y₁ Y₂ hc hx hy K hK e)
    (fam_zero Y₁ Y₂ hc hx hy K hK)
    (famM_eq Y₁ Y₂ K hK)
    (famF_neg_one_iterate Y₁ Y₂ hx hy)

end Inst

end VOA.Huang.GenusOneWard
