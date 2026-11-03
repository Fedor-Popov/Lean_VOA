import VOA.DeligneAudit.SL4TAdjointSiteFlatDescent
import VOA.DeligneAudit.SL4TAdjointSiteJointFlagConstruction

/-!
# The flat level relation at one adjoint site, reduced to its top blocks

On a block `(0, d, 0; E, e)` of the module `M(B, h)`, with `f = d + 1 - e`, the flat symbol is
`b₀ = e_f(g₂′)`, and the target `ZeroAdjointFlatRelation B k` says `F(h) π̄(b₀ φ) = 0`.

* **The ring side** (`newtonCoeff_flatShiftSymbol`). At outer labels one the Newton coefficients
  of the symbols `p_s(x₂) - p_s(g₂)` are `(-1)^n e_n(g₂′)`.
* **The realization** (`flatShiftQuotCurrent`). The flat shift current `H_s` descends to the
  first Levi quotient as `2 A₀(s) - h₂(s)`, equal to the difference of the two Cartan operators
  realizing `p_s(x₂)` and `p_s(g₂)`. So the Newton operator `D_f` realizes multiplication by
  `(-1)^f b₀`, and `π̄(b₀) = (-1)^f [D_f (g^E q^e y^d v)]`.
* **The block theorem** (`adjointSite_flatRelation_of_top`). If on the top block `E = B - d`
  the vector `F(h) D_f (g^(B-d) q^e y^d v)` lies in `M_{>(0,d,0)}`, then `F(h) π̄(b₀ φ) = 0` on
  every block `(0, d, 0; E, e)`, by the descent of `SL4TAdjointSiteFlatDescent` and Lemma CI(i).
* **The top blocks with `e ≤ 1`** (`adjointSite_flatTop_of_le_one`) hold unconditionally: for
  `e = 0` by the vanishing of `e_(d+1)` of `d` shifts, for `e = 1` by `flatTopRelation_unit`.

**The residual.** For `e ≥ 2` the top-block statement is recorded as the proposition
`AdjointSiteFlatTopRelation B h`. The paper's argument (Proposition 6.3) needs the marked words
`g^(B-b) q^(e-a) y^b z^a x v` with `a ≥ 2` and the vectors `z · M_{>(0,d',0)}` to lie in
`M_{>(0,d,0)}`; their first Levi keys `(1, b, a)`, `a ≥ 2`, have Levi height `1 - a < 0` and are
*lower* than `(0, d, 0)` in the first Levi order used here (`higherRadicalCounts`, Levi height
first). So that step is not available, and the case `e ≥ 2` is left open.

Consequences: `zeroAdjointFlatRelation_of_topRelation` and
`adjointSiteLawB_of_stratumCount_and_flatTop` (Law B at one adjoint site from the stratum count
and the top-block residual).
-/

namespace VOA.DeligneAudit.SL4T

open MvPolynomial VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.A3Sector

noncomputable section

/-! ### The ring side -/

/-- The symbol `p_s(x₂) - p_s(g₂)` of the flat shift current on a block. -/
def flatShiftSymbol (q : MixedParams) (s : ℕ) : MixedRing q :=
  mixedAlphabetPowerSum (mixedEvaluation q) 1 (mixedLengths q 1) s -
    mixedAlphabetPowerSum (mixedEvaluation q) 4 (mixedLengths q 4) s

set_option synthInstance.maxHeartbeats 100000 in
-- Mixed rings are quotients of a polynomial algebra in five alphabets.
/-- **Newton reconstruction of the flat symbol.** At outer labels one, the Newton coefficients of
`p_s(x₂) - p_s(g₂)` are the signed classes `(-1)^n e_n(g₂′)`. -/
theorem newtonCoeff_flatShiftSymbol (B : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams 1 B d e₁ e₂)) (n : ℕ) :
    newtonCoeff (flatShiftSymbol (mixedLabelBlockParams 1 B d e₁ e₂)) n =
      (-1) ^ n * mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂) (mixedG2prime n) := by
  have hser := newtonCoefficientSeries_relativeAlphabet
    (mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂)) mixedV 4
    (mixedLengths (mixedLabelBlockParams 1 B d e₁ e₂) 4) _
    (newtonCoefficientSeries_mixedAmbient (mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂))
      1 2 (mixedLengths (mixedLabelBlockParams 1 B d e₁ e₂) 1)
      (mixedLengths (mixedLabelBlockParams 1 B d e₁ e₂) 2))
  have hc := congrArg (PowerSeries.coeff n) hser
  simp only [newtonCoefficientSeries, mixedSignedSeries, PowerSeries.coeff_mk] at hc
  rw [newtonCoeff_congr_positive (flatShiftSymbol (mixedLabelBlockParams 1 B d e₁ e₂))
    (fun s => mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂)) 1
        (mixedLengths (mixedLabelBlockParams 1 B d e₁ e₂) 1) s -
      mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂)) 2
        (mixedLengths (mixedLabelBlockParams 1 B d e₁ e₂) 2) s -
      mixedAlphabetPowerSum (mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂)) 4
        (mixedLengths (mixedLabelBlockParams 1 B d e₁ e₂) 4) s)
    (fun s hs => by
      beta_reduce
      rw [mixedAlphabetPowerSum_outer_label_one B d e₁ e₂ hv 2 (Or.inr rfl) s hs, sub_zero]
      rfl) n]
  exact hc

/-! ### The flat shift current on the first Levi quotient -/

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V) (w : V)

/-- Powers of a Levi current on the first Levi quotient. -/
theorem radicalCountQuot_pow_mk (d : Fin 3 → ℕ) (c : Fin 8) (r k : ℕ) (v : V) :
    ((radicalCountQuotCurrent ρ w d).op c r ^ k) ((higherRadicalCountClosure ρ w d).mkQ v) =
      (higherRadicalCountClosure ρ w d).mkQ ((ρ.op (a3LeviColour c) r ^ k) v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    rfl

variable (a b c : ℕ) (h : LocalWeylRel ρ w (weightABC a b c)) (d : Fin 3 → ℕ)

/-- The flat shift current `2 A₀(s) - h₂(s)` on the first Levi quotient. -/
def flatShiftQuotCurrent (s : ℕ) : Module.End ℂ (V ⧸ higherRadicalCountClosure ρ w d) :=
  (2 : ℂ) • radicalAlphabetQuotCurrent ρ w a b c h d 0 s - (radicalCountQuotCurrent ρ w d).op 6 s

/-- The flat shift current descends from the module. -/
theorem flatShiftQuotCurrent_mk (s : ℕ) (v : V) :
    flatShiftQuotCurrent ρ w a b c h d s ((higherRadicalCountClosure ρ w d).mkQ v) =
      (higherRadicalCountClosure ρ w d).mkQ (flatShiftCurrent ρ s v) := by
  simp only [flatShiftQuotCurrent, flatShiftCurrent, LinearMap.sub_apply, LinearMap.smul_apply,
    radicalAlphabetQuotCurrent_mk, map_sub, map_smul]
  rfl

/-- The flat shift current is the difference of the Cartan operators realizing `p_s(x₂)` and
`p_s(g₂)`. -/
theorem flatShiftQuotCurrent_eq (s : ℕ) :
    flatShiftQuotCurrent ρ w a b c h d s =
      middleRadicalOperator ρ w a b c h d s - compoundAlphabetOperator ρ w a b c h d s := by
  apply LinearMap.ext
  intro x
  simp only [flatShiftQuotCurrent, middleRadicalOperator, compoundAlphabetOperator,
    LinearMap.sub_apply, LinearMap.smul_apply]
  module

/-- The flat shift current commutes with `η(0)`. -/
theorem flatShiftQuotCurrent_raising_comm (s : ℕ) (x : V ⧸ higherRadicalCountClosure ρ w d) :
    flatShiftQuotCurrent ρ w a b c h d s ((radicalCountQuotCurrent ρ w d).op 0 0 x) =
      (radicalCountQuotCurrent ρ w d).op 0 0 (flatShiftQuotCurrent ρ w a b c h d s x) := by
  have h6 : (radicalCountQuotCurrent ρ w d).op 6 s ((radicalCountQuotCurrent ρ w d).op 0 0 x) =
      (radicalCountQuotCurrent ρ w d).op 0 0 ((radicalCountQuotCurrent ρ w d).op 6 s x) +
        (2 : ℂ) • (radicalCountQuotCurrent ρ w d).op 0 (s + 0) x := by
    have hc : (radicalCountQuotCurrent ρ w d).op 6 s ((radicalCountQuotCurrent ρ w d).op 0 0 x) -
        (radicalCountQuotCurrent ρ w d).op 0 0 ((radicalCountQuotCurrent ρ w d).op 6 s x) =
          (2 : ℂ) • (radicalCountQuotCurrent ρ w d).op 0 (s + 0) x := by
      simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using
        (radicalCountQuotCurrent ρ w d).comm 6 0 s 0 x
    exact sub_eq_iff_eq_add'.mp hc
  simp only [flatShiftQuotCurrent, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [radicalAlphabetQuotCurrent_outer_levi_comm, h6]
  simp only [outerAlphabetLeviWeight, map_sub, map_smul]
  push_cast
  module

/-- Once currents of mode at least `n + 1` vanish, the flat shift current of positive mode
commutes with `F(n)`. -/
theorem flatShiftQuotCurrent_lastLowering_comm (n : ℕ)
    (ht : ∀ i s v, n + 1 ≤ s → ρ.op i s v = 0) (s : ℕ) (hs : 1 ≤ s)
    (x : V ⧸ higherRadicalCountClosure ρ w d) :
    flatShiftQuotCurrent ρ w a b c h d s ((radicalCountQuotCurrent ρ w d).op 4 n x) =
      (radicalCountQuotCurrent ρ w d).op 4 n (flatShiftQuotCurrent ρ w a b c h d s x) := by
  have h6 : (radicalCountQuotCurrent ρ w d).op 6 s ((radicalCountQuotCurrent ρ w d).op 4 n x) =
      (radicalCountQuotCurrent ρ w d).op 4 n ((radicalCountQuotCurrent ρ w d).op 6 s x) +
        (radicalCountQuotCurrent ρ w d).op 4 (s + n) x := by
    have hc : (radicalCountQuotCurrent ρ w d).op 6 s ((radicalCountQuotCurrent ρ w d).op 4 n x) -
        (radicalCountQuotCurrent ρ w d).op 4 n ((radicalCountQuotCurrent ρ w d).op 6 s x) =
          (radicalCountQuotCurrent ρ w d).op 4 (s + n) x := by
      simpa [Fin.sum_univ_eight, VOA.AffineSl3.bracketTable] using
        (radicalCountQuotCurrent ρ w d).comm 6 4 s n x
    exact sub_eq_iff_eq_add'.mp hc
  have hz : (radicalCountQuotCurrent ρ w d).op 4 (s + n) x = 0 :=
    radicalCountQuot_truncated ρ w (n + 1) ht d 4 (s + n) (by omega) x
  simp only [flatShiftQuotCurrent, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [radicalAlphabetQuotCurrent_outer_levi_comm, h6, hz]
  simp only [outerAlphabetLeviWeight, map_sub, map_smul]
  push_cast
  module

set_option synthInstance.maxHeartbeats 100000 in
-- The second Levi closure is built over nested tensor-product coefficient algebras.
/-- The flat shift current of positive mode preserves every higher second Levi closure. -/
theorem higherSecondLeviCountClosure_flatShift (e₁ e₂ s : ℕ) (hs : 0 < s) :
    higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂ ≤
      (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d) e₁ e₂).comap
          (flatShiftQuotCurrent ρ w a b c h d s) := by
  intro x hx
  rw [Submodule.mem_comap, flatShiftQuotCurrent, LinearMap.sub_apply, LinearMap.smul_apply]
  exact Submodule.sub_mem _
    (Submodule.smul_mem _ _ (higherSecondLeviCountClosure_outerAlphabet ρ w a b c h d e₁ e₂ s
      hs hx))
    (a2LeviClosure_inv _ _ 6 s (by simp [a2Levi]) hx)

/-! ### The realization of the flat symbol -/

set_option synthInstance.maxHeartbeats 100000 in
-- The second Levi multiplicity is built over nested tensor-product coefficient algebras.
/-- **The realization of the flat symbol.** At outer labels one, `π̄(e_f(g₂′))` is represented
by `(-1)^f D_f (g^(e₁) q^(e₂) β(1))`, where `D_f` is the Newton operator of the flat shift
current on the first Levi quotient. -/
theorem flatSymbol_secondLevi_val (B : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) (hv : MixedValid (mixedLabelBlockParams 1 B d e₁ e₂)) (f : ℕ) :
    (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv
        (mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂) (mixedG2prime f))).val =
      ((-1 : ℂ) ^ f) • (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d) e₁ e₂).mkQ
        (newtonEnd (flatShiftQuotCurrent ρ w 1 B 1 hW d) f
          (((radicalCountQuotCurrent ρ w d).op 3 0 ^ e₁)
            (((radicalCountQuotCurrent ρ w d).op 5 0 ^ e₂)
              (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d 1)))) := by
  have hstep : ∀ s, 1 ≤ s → ∀ ψ y,
      (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d) e₁ e₂).mkQ y =
        ((secondLeviMultiplicity (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d) e₁ e₂).subtype.comp
            (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv)) ψ →
      (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d) e₁ e₂).mkQ
          (flatShiftQuotCurrent ρ w 1 B 1 hW d s y) =
        ((secondLeviMultiplicity (radicalCountQuotCurrent ρ w d)
          (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW d) e₁ e₂).subtype.comp
            (mixedSecondLeviEvaluation ρ w 1 B hW d e₁ e₂ hv))
          (flatShiftSymbol (mixedLabelBlockParams 1 B d e₁ e₂) s * ψ) := by
    intro s hs ψ y hy
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hm := middleRadicalOperator_realizes ρ w d B hW e₁ e₂ hv s' ψ y hy
    have hc := compoundAlphabetOperator_realizes ρ w d B hW e₁ e₂ hv s' ψ y hy
    rw [flatShiftQuotCurrent_eq, LinearMap.sub_apply, map_sub, hm, hc, flatShiftSymbol,
      sub_mul, map_sub]
    rfl
  have hreal := newtonEnd_realizes _ _ _ _ hstep f 1 _
    (mixedSecondLeviEvaluation_one_val ρ w 1 B hW d e₁ e₂ hv).symm
  rw [mul_one, newtonCoeff_flatShiftSymbol B d e₁ e₂ hv f] at hreal
  have hsign : ((-1 : MixedRing (mixedLabelBlockParams 1 B d e₁ e₂)) ^ f) *
      mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂) (mixedG2prime f) =
      ((-1 : ℂ) ^ f) • mixedEvaluation (mixedLabelBlockParams 1 B d e₁ e₂) (mixedG2prime f) := by
    rw [Algebra.smul_def, map_pow, map_neg, map_one]
  rw [hsign, map_smul] at hreal
  rw [hreal, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  rfl

/-! ### The hypotheses of the descent on the first Levi quotient -/

/-- The outer raising current `E₁₃` kills every first Levi multiplicity vector. -/
theorem radicalGrassmannianAmbientEvaluation_outerRaising (r : ℕ)
    (φ : RadicalGrassmannianRing a b c d) :
    (radicalCountQuotCurrent ρ w d).op 2 r (radicalGrassmannianAmbientEvaluation ρ w a b c h d φ)
      = 0 := by
  obtain ⟨v, hv, he⟩ := (radicalGrassmannianEvaluation ρ w a b c h d φ).property
  change (radicalCountQuotCurrent ρ w d).op 2 r
    (radicalGrassmannianEvaluation ρ w a b c h d φ).val = 0
  rw [← he]
  exact radicalCountQuot_raising ρ w a b c h d 1 r hv

set_option synthInstance.maxHeartbeats 100000 in
-- The first Levi multiplicity ring is a tensor product of three Grassmannian rings.
/-- Both Levi Cartan currents preserve the image of the first Levi multiplicity evaluation. -/
theorem radicalGrassmannianAmbientEvaluation_cartan_exists (i : Fin 2) (t : ℕ)
    (φ : RadicalGrassmannianRing a b c d) :
    ∃ φ', (radicalCountQuotCurrent ρ w d).op (if i = 0 then 6 else 7) t
        (radicalGrassmannianAmbientEvaluation ρ w a b c h d φ) =
      radicalGrassmannianAmbientEvaluation ρ w a b c h d φ' := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · obtain ⟨v, hv, he⟩ := (radicalGrassmannianEvaluation ρ w a b c h d φ).property
    refine ⟨a3KeyLabel b c i ⟨d 0, d 1, d 2, 0⟩ • φ, ?_⟩
    rw [map_smul]
    change (radicalCountQuotCurrent ρ w d).op _ 0
        (radicalGrassmannianEvaluation ρ w a b c h d φ).val =
      _ • (radicalGrassmannianEvaluation ρ w a b c h d φ).val
    rw [← he]
    exact radicalCountQuot_cartan_zero ρ w a b c h d i hv
  · exact ⟨_, radicalGrassmannianAmbientEvaluation_cartan ρ w a b c h d i t ht φ⟩

set_option synthInstance.maxHeartbeats 100000 in
-- The first Levi multiplicity ring is a tensor product of three Grassmannian rings.
/-- The middle Levi Cartan weight of `β(1)` on the blocks over `(0, d, 0)` is `B - d`. -/
theorem radicalGrassmannianAmbientEvaluation_one_weight (B : ℕ)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (d₂ : ℕ) (hd : d₂ ≤ B) :
    (radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 6 0
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] 1) =
      ((B - d₂ : ℕ) : ℂ) • radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] 1 := by
  rw [radicalGrassmannianAmbientEvaluation_one]
  have hl := radicalCountQuot_cartan_zero ρ w 1 B 1 hW ![0, d₂, 0] 0
    (zeroModeWord_mem_radicalCountLayer ρ w ![0, d₂, 0])
  simp only [↓reduceIte] at hl
  rw [hl]
  congr 1
  simp [a3KeyLabel, Nat.cast_sub hd]

set_option synthInstance.maxHeartbeats 100000 in
-- The first Levi multiplicity ring is a tensor product of three Grassmannian rings.
/-- The zero-mode word `g^E q^e β(1)` on the blocks over `(0, d, 0)` is the image of
`g^E q^e y^d v`. -/
theorem radicalCountQuot_flatTopWord (B : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (d₂ E e : ℕ) :
    ((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 3 0 ^ E)
        (((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 5 0 ^ e)
          (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] 1)) =
      (higherRadicalCountClosure ρ w ![0, d₂, 0]).mkQ (flatNormalWord ρ E e d₂ 0 w) := by
  rw [radicalGrassmannianAmbientEvaluation_one, radicalCountQuot_pow_mk, radicalCountQuot_pow_mk]
  simp only [flatNormalWord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, pow_zero, Module.End.one_apply]
  rfl

/-! ### The descent on the first Levi quotient -/

set_option synthInstance.maxHeartbeats 100000 in
-- The second Levi closure is built over nested tensor-product coefficient algebras.
/-- **The descent for the flat Newton vectors.** If `F(n) D_f (g^(B-d) q^e y^d v)` lies in
`M_{>(0,d,0)}`, then for every `E ≤ B - d` the vector `F(n) D_f (g^E q^e β(1))` of the first Levi
quotient lies in `W_{>((0,d,0),(E,e))}`. -/
theorem flatNewtonLowering_mem_higherSecondLevi (B n : ℕ)
    (hW : LocalWeylRel ρ w (weightABC 1 B 1)) (d₂ e₂ f : ℕ) (hd : d₂ ≤ B)
    (htop : ρ.op 11 n (newtonEnd (flatShiftCurrent ρ) f (flatNormalWord ρ (B - d₂) e₂ d₂ 0 w)) ∈
      higherRadicalCountClosure ρ w ![0, d₂, 0]) (E : ℕ) (hE : E ≤ B - d₂) :
    (radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 4 n
        (newtonEnd (flatShiftQuotCurrent ρ w 1 B 1 hW ![0, d₂, 0]) f
          (((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 3 0 ^ E)
            (((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 5 0 ^ e₂)
              (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] 1)))) ∈
      higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w ![0, d₂, 0])
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0]) E e₂ := by
  have hη : ∀ r φ, (radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 0 r
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] φ) = 0 :=
    fun r φ => radicalGrassmannianAmbientEvaluation_raising ρ w 1 B 1 hW ![0, d₂, 0] 0 r φ
  have he : ∀ r φ, (radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 1 r
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] φ) = 0 :=
    fun r φ => radicalGrassmannianAmbientEvaluation_raising ρ w 1 B 1 hW ![0, d₂, 0] 1 r φ
  have hη₂ : ∀ r φ, (radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 2 r
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] φ) = 0 :=
    fun r φ => radicalGrassmannianAmbientEvaluation_outerRaising ρ w 1 B 1 hW ![0, d₂, 0] r φ
  have h₆ : ∀ t φ, ∃ φ', (radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 6 t
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] φ) =
        radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] φ' :=
    fun t φ => radicalGrassmannianAmbientEvaluation_cartan_exists ρ w 1 B 1 hW ![0, d₂, 0] 0 t φ
  have h₇ : ∀ t φ, ∃ φ', (radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 7 t
      (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] φ) =
        radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] φ' :=
    fun t φ => radicalGrassmannianAmbientEvaluation_cartan_exists ρ w 1 B 1 hW ![0, d₂, 0] 1 t φ
  have hT : ∀ E', higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w ![0, d₂, 0])
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0]) E' e₂ ≤
      (higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w ![0, d₂, 0])
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0]) E' e₂).comap
        ((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 4 n *
          newtonEnd (flatShiftQuotCurrent ρ w 1 B 1 hW ![0, d₂, 0]) f) := by
    intro E' x hx
    have h1 := newtonEnd_le_comap (flatShiftQuotCurrent ρ w 1 B 1 hW ![0, d₂, 0]) _
      (fun s hs => higherSecondLeviCountClosure_flatShift ρ w 1 B 1 hW ![0, d₂, 0] E' e₂ s
        (by omega)) f hx
    exact a2LeviClosure_inv _ _ 4 n (by simp [a2Levi]) h1
  have hTη : Commute ((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 4 n *
      newtonEnd (flatShiftQuotCurrent ρ w 1 B 1 hW ![0, d₂, 0]) f)
      ((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 0 0) := by
    have h1 : Commute ((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 0 0)
        (newtonEnd (flatShiftQuotCurrent ρ w 1 B 1 hW ![0, d₂, 0]) f) :=
      newtonEnd_commute _ _ (fun s _ => LinearMap.ext fun x =>
        (flatShiftQuotCurrent_raising_comm ρ w 1 B 1 hW ![0, d₂, 0] s x).symm) f
    have h2 : Commute ((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 0 0)
        ((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 4 n) :=
      LinearMap.ext fun x =>
        (leviLast_raising_comm (radicalCountQuotCurrent ρ w ![0, d₂, 0]) n 0 x).symm
    exact (h2.mul_right h1).symm
  have htopQ : ((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 4 n *
      newtonEnd (flatShiftQuotCurrent ρ w 1 B 1 hW ![0, d₂, 0]) f)
        (((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 3 0 ^ (B - d₂))
          (((radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 5 0 ^ e₂)
            (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0] 1))) ∈
      higherSecondLeviCountClosure (radicalCountQuotCurrent ρ w ![0, d₂, 0])
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0]) (B - d₂) e₂ := by
    rw [Module.End.mul_apply, radicalCountQuot_flatTopWord, ← newtonEnd_intertwine
      (flatShiftCurrent ρ) _ (higherRadicalCountClosure ρ w ![0, d₂, 0]).mkQ
      (fun s _ v => (flatShiftQuotCurrent_mk ρ w 1 B 1 hW ![0, d₂, 0] s v).symm) f]
    have hF : (radicalCountQuotCurrent ρ w ![0, d₂, 0]).op 4 n
        ((higherRadicalCountClosure ρ w ![0, d₂, 0]).mkQ (newtonEnd (flatShiftCurrent ρ) f
          (flatNormalWord ρ (B - d₂) e₂ d₂ 0 w))) =
        (higherRadicalCountClosure ρ w ![0, d₂, 0]).mkQ (ρ.op 11 n (newtonEnd
          (flatShiftCurrent ρ) f (flatNormalWord ρ (B - d₂) e₂ d₂ 0 w))) := rfl
    have h0 : (higherRadicalCountClosure ρ w ![0, d₂, 0]).mkQ (ρ.op 11 n (newtonEnd
        (flatShiftCurrent ρ) f (flatNormalWord ρ (B - d₂) e₂ d₂ 0 w))) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr htop
    rw [hF, h0]
    exact Submodule.zero_mem _
  exact secondLevi_topWord_descent _ _ hη hη₂ he h₆ h₇ 1 (B - d₂)
    (radicalGrassmannianAmbientEvaluation_one_weight ρ w B hW d₂ hd) e₂ _ hT hTη htopQ E hE

/-! ### The block theorem -/

set_option synthInstance.maxHeartbeats 100000 in
-- The second Levi multiplicity is built over nested tensor-product coefficient algebras.
/-- **The flat relation from its top block.** Let `v` satisfy the local Weyl relations of weight
`(1, B, 1)` and let every current of mode at least `n + 1` vanish. On a valid block
`(0, d₂, 0; e₁, e₂)`, if `F(n) D_f (g^(B-d₂) q^e₂ y^d₂ v) ∈ M_{>(0,d₂,0)}` with
`f = d₂ + 1 - e₂`, then `F(n) π̄(b₀ φ) = 0` for every `φ`. -/
theorem adjointSite_flatRelation_of_top (B n : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (ht : ∀ i s v, n + 1 ≤ s → ρ.op i s v = 0) (d₂ e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂))
    (htop : ρ.op 11 n (newtonEnd (flatShiftCurrent ρ) (d₂ + 1 - e₂)
      (flatNormalWord ρ (B - d₂) e₂ d₂ 0 w)) ∈ higherRadicalCountClosure ρ w ![0, d₂, 0])
    (φ : MixedRing (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂)) :
    secondLeviQuotientLowering (radicalCountQuotCurrent ρ w ![0, d₂, 0])
        (radicalGrassmannianAmbientEvaluation ρ w 1 B 1 hW ![0, d₂, 0]) e₁ e₂ n
      (mixedSecondLeviEvaluation ρ w 1 B hW ![0, d₂, 0] e₁ e₂ hv
        (adjointSiteFlatSymbol (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂) * φ)).val = 0 := by
  have hvv := hv
  simp [MixedValid, mixedLabelBlockParams, mixedP, mixedQ] at hvv
  have hd₂ : d₂ ≤ B := by omega
  have he₁ : e₁ ≤ B - d₂ := by omega
  have hf : (mixedQ (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂) -
      (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂).e2).toNat = d₂ + 1 - e₂ := by
    simp [mixedQ, mixedLabelBlockParams]
  rw [mul_comm]
  apply adjointSite_lowering_mul_eq_zero ρ w B hW ![0, d₂, 0] e₁ e₂ hv n ht
  rw [adjointSiteFlatSymbol, hf, flatSymbol_secondLevi_val, map_smul]
  apply smul_eq_zero_of_right
  rw [Submodule.mkQ_apply, secondLeviQuotientLowering, Submodule.mapQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact flatNewtonLowering_mem_higherSecondLevi ρ w B n hW d₂ e₂ _ hd₂ htop e₁ he₁

/-! ### Top blocks with at most one compound letter -/

set_option synthInstance.maxHeartbeats 100000 in
-- The higher first Levi closure is a Levi closure of merged key layers.
/-- **The top blocks with `e ≤ 1`.** For `e = 0` the Newton operator `D_(d+1)` kills
`g^(B-d) y^d v`; for `e = 1` this is `flatTopRelation_unit`. -/
theorem adjointSite_flatTop_of_le_one (B n : ℕ) (hW : LocalWeylRel ρ w (weightABC 1 B 1))
    (hg : ρ.op 9 n w = 0) (hn : 1 ≤ n) (ht : ∀ i s v, n + 1 ≤ s → ρ.op i s v = 0)
    (d₂ e₂ : ℕ) (hd : d₂ ≤ B) (he : e₂ ≤ 1) :
    ρ.op 11 n (newtonEnd (flatShiftCurrent ρ) (d₂ + 1 - e₂)
      (flatNormalWord ρ (B - d₂) e₂ d₂ 0 w)) ∈ higherRadicalCountClosure ρ w ![0, d₂, 0] := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl | rfl
  · have hcomm := newtonEnd_commute (flatShiftCurrent ρ) (ρ.op 9 0 ^ (B - d₂))
      (fun s _ => LinearMap.ext fun v => (flatShiftCurrent_middlePow ρ s (B - d₂) v).symm)
      (d₂ + 1 - 0)
    simp only [flatNormalWord, pow_zero, Module.End.one_apply]
    have hc' : newtonEnd (flatShiftCurrent ρ) (d₂ + 1 - 0) ((ρ.op 9 0 ^ (B - d₂))
        ((ρ.op 7 0 ^ d₂) w)) = (ρ.op 9 0 ^ (B - d₂)) (newtonEnd (flatShiftCurrent ρ)
          (d₂ + 1 - 0) ((ρ.op 7 0 ^ d₂) w)) := by
      simpa only [Module.End.mul_apply] using
        (LinearMap.congr_fun hcomm.eq ((ρ.op 7 0 ^ d₂) w)).symm
    rw [hc', newtonEnd_flatShift_compoundPow_eq_zero ρ w
      (fun s hs => flatShiftCurrent_source_zero ρ w 1 B 1 hW s hs) d₂ (d₂ + 1 - 0) (by omega),
      map_zero, map_zero]
    exact Submodule.zero_mem _
  · have h1 := flatTopRelation_unit ρ w B n hW hg hn ht d₂ hd
    rwa [Nat.add_sub_cancel]

/-! ### The universal module -/

/-- **The top-block flat relation for `e ≥ 2`** (the open residual of this reduction). On the
module `M(B, h)`, for every `d ≤ B` and `2 ≤ e ≤ d + 1`, with `f = d + 1 - e`, the vector
`F(h) D_f (g^(B-d) q^e y^d v)` lies in the higher first Levi closure `M_{>(0,d,0)}`. -/
def AdjointSiteFlatTopRelation (B h : ℕ) : Prop :=
  ∀ d e : ℕ, d ≤ B → 2 ≤ e → e ≤ d + 1 →
    (adjointSiteRep B h).op 11 h (newtonEnd (flatShiftCurrent (adjointSiteRep B h)) (d + 1 - e)
      (flatNormalWord (adjointSiteRep B h) (B - d) e d 0 (adjointSiteGenerator B h))) ∈
        higherRadicalCountClosure (adjointSiteRep B h) (adjointSiteGenerator B h) ![0, d, 0]

set_option synthInstance.maxHeartbeats 100000 in
-- The second Levi multiplicity is built over nested tensor-product coefficient algebras.
/-- **The flat relation on blocks with at most one compound letter**, unconditionally: on every
block `(0, d₂, 0; e₁, e₂)` with `e₂ ≤ 1` of `M(B, B - k)`, `F(h) π̄(b₀ φ) = 0`. -/
theorem zeroAdjointFlatRelation_unitCompound (B k : ℕ) (hkB : 2 * k ≤ B) (hk : 1 ≤ k)
    (d₂ e₁ e₂ : ℕ) (hv : MixedValid (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂))
    (he₂ : e₂ ≤ 1) (φ : MixedRing (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂)) :
    secondLeviQuotientLowering
        (radicalCountQuotCurrent (adjointSiteRep B (B - k)) (adjointSiteGenerator B (B - k))
          ![0, d₂, 0])
        (radicalGrassmannianAmbientEvaluation (adjointSiteRep B (B - k))
          (adjointSiteGenerator B (B - k)) 1 B 1 (adjointSite_localWeyl B (B - k)) ![0, d₂, 0])
        e₁ e₂ (B - k)
      (mixedSecondLeviEvaluation (adjointSiteRep B (B - k)) (adjointSiteGenerator B (B - k)) 1 B
        (adjointSite_localWeyl B (B - k)) ![0, d₂, 0] e₁ e₂ hv
        (adjointSiteFlatSymbol (mixedLabelBlockParams 1 B ![0, d₂, 0] e₁ e₂) *
          φ)).val = 0 := by
  have hvv := hv
  simp [MixedValid, mixedLabelBlockParams, mixedP, mixedQ] at hvv
  have ht : ∀ i s v, B - k + 1 ≤ s → (adjointSiteRep B (B - k)).op i s v = 0 :=
    fun i s v hs => adjointSiteModule_current_zero B (B - k) i s hs v
  exact adjointSite_flatRelation_of_top _ _ B (B - k) (adjointSite_localWeyl B (B - k)) ht
    d₂ e₁ e₂ hv (adjointSite_flatTop_of_le_one _ _ B (B - k) (adjointSite_localWeyl B (B - k))
      (adjointSite_relations B (B - k)).2.2 (by omega) ht d₂ e₂ (by omega) he₂) φ

set_option synthInstance.maxHeartbeats 100000 in
-- The second Levi multiplicity is built over nested tensor-product coefficient algebras.
/-- **`ZeroAdjointFlatRelation` from the top-block residual.** For `1 ≤ k` and `2k ≤ B`, the
top-block flat relation for `e ≥ 2` implies the flat level relation on every block. -/
theorem zeroAdjointFlatRelation_of_topRelation (B k : ℕ) (hkB : 2 * k ≤ B) (hk : 1 ≤ k)
    (hR : AdjointSiteFlatTopRelation B (B - k)) : ZeroAdjointFlatRelation B k := by
  intro d₂ e₁ e₂ hv φ
  by_cases he₂ : e₂ ≤ 1
  · exact zeroAdjointFlatRelation_unitCompound B k hkB hk d₂ e₁ e₂ hv he₂ φ
  · have hvv := hv
    simp [MixedValid, mixedLabelBlockParams, mixedP, mixedQ] at hvv
    have ht : ∀ i s v, B - k + 1 ≤ s → (adjointSiteRep B (B - k)).op i s v = 0 :=
      fun i s v hs => adjointSiteModule_current_zero B (B - k) i s hs v
    exact adjointSite_flatRelation_of_top _ _ B (B - k) (adjointSite_localWeyl B (B - k)) ht
      d₂ e₁ e₂ hv (hR d₂ e₂ (by omega) (by omega) (by omega)) φ

/-- **Law B at one adjoint site from the stratum count and the top-block residual.** -/
theorem adjointSiteLawB_of_stratumCount_and_flatTop (B k : ℕ) (hk : 1 ≤ k) (hkB : 2 * k ≤ B)
    (hS : OneAdjointStratumCount B k) (hR : AdjointSiteFlatTopRelation B (B - k)) :
    AdjointSiteLawB B k :=
  adjointSiteLawB_of_residuals B k hk hkB hS (zeroAdjointFlatRelation_of_topRelation B k hkB hk hR)

end

end VOA.DeligneAudit.SL4T
