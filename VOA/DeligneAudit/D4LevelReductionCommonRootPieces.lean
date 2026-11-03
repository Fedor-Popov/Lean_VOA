import VOA.DeligneAudit.D4LevelReductionCommonRootBoundary

/-! The four simultaneous union and common-root flag transports. -/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open Polynomial
open VOA.DeligneAudit.SL4T

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra ℂ R] [Algebra ℂ T]

/-- A Thom map transports both polynomial relations from their explicit generators. -/
theorem TwoRelationChain.thom_of_generators (ρ : R →ₐ[ℂ] T)
    (hρ : Function.Surjective ρ) (t : R) (I : Ideal R) (A B : Ideal R[X])
    (q p qbar : R[X]) (m s d : ℕ) (hker : ∀ x, ρ x = 0 → t * x ∈ I)
    (hq : Polynomial.C t * X ^ s * q ∈ I.map Polynomial.C ⊔ A)
    (hm : Polynomial.C t * X ^ (m + s) ∈ I.map Polynomial.C ⊔ A)
    (hp : Polynomial.C t * X ^ d * p ∈ I.map Polynomial.C ⊔ B)
    (hbar : Polynomial.C t * X ^ d * qbar ∈ I.map Polynomial.C ⊔ B)
    {ns : List (ℕ × ℕ)}
    (h : TwoRelationChain (Ideal.span {q.map ρ.toRingHom} ⊔ Ideal.span {X ^ m})
      (commonRootIdeal (p.map ρ.toRingHom) (qbar.map ρ.toRingHom)) ⊥ ⊤ ns) :
    TwoRelationChain A B I (I ⊔ Ideal.span {t})
      (ns.map fun n => (n.1 + s, n.2 + d)) := by
  have ht := h.thom ρ hρ t I A B _ _ s d
    (thomFlag_polynomial ρ hρ t I A q m s hq hm)
    (commonRoot_polynomialTransport ρ hρ t I B p qbar d hp hbar)
  simpa only [thomFlagIdeal_bot ρ t I hker, thomFlagIdeal_top] using ht

theorem commonRootFlag_emptySite (M a b : ℕ) (ha : a < M) (hb : b < M) {ns : List (ℕ × ℕ)}
    (h : TwoRelationChain (S_relationIdeal (M - 1) a b)
      (grassmannianCommonRootIdeal (M - 1) a b) ⊥ ⊤ ns) :
    TwoRelationChain (S_relationIdeal M a b) (grassmannianCommonRootIdeal M a b)
      ⊥ (thomI1 M a b) ns := by
  let ρ := boundaryProjection M a b false false ha.le hb.le ha hb
  let t := leftE M a b a * rightE M a b b
  have hq : (leftP M a b * rightP M a b).map ρ.toRingHom =
      leftP (M - 1) a b * rightP (M - 1) a b := by
    rw [Polynomial.map_mul, boundaryProjection_leftP, boundaryProjection_rightP]
    rfl
  have hker (x : S M a b) (hx : ρ x = 0) : t * x ∈ (⊥ : Ideal (S M a b)) := by
    exact thomNN_kills M a b ha hb x
      ((boundaryProjection_eq_zero M a b false false ha.le hb.le ha hb x).mp hx)
  have hp : Polynomial.C t * X ^ 0 * (leftP M a b * rightP M a b) ∈
      (⊥ : Ideal (S M a b)).map Polynomial.C ⊔ S_relationIdeal M a b := by
    simp only [pow_zero, mul_one, Ideal.map_bot, bot_sup_eq]
    exact (S_relationIdeal M a b).mul_mem_left _
      (relationIdeal_product (leftP M a b) (rightP M a b) M)
  have hm : Polynomial.C t * X ^ ((M - 1) + 0) ∈
      (⊥ : Ideal (S M a b)).map Polynomial.C ⊔ S_relationIdeal M a b := by
    simpa only [Nat.add_zero, Ideal.map_bot, bot_sup_eq] using
      thom_relation_nn M a b (by omega)
  have hpmap : (rightP M a b).map ρ.toRingHom = rightP (M - 1) a b := by
    rw [boundaryProjection_rightP]; rfl
  have hbmap : (leftPbar M a b).divX.map ρ.toRingHom =
      leftPbar (M - 1) a b := complementCharacteristic_boundary_division M a b false ha hb.le hb
  have hcp : Polynomial.C t * X ^ 0 * rightP M a b ∈
      (⊥ : Ideal (S M a b)).map Polynomial.C ⊔ grassmannianCommonRootIdeal M a b := by
    simp only [pow_zero, mul_one, Ideal.map_bot, bot_sup_eq]
    exact (grassmannianCommonRootIdeal M a b).mul_mem_left _
      (commonRootIdeal_left _ _)
  have hcb : Polynomial.C t * X ^ 0 * (leftPbar M a b).divX ∈
      (⊥ : Ideal (S M a b)).map Polynomial.C ⊔ grassmannianCommonRootIdeal M a b := by
    simp only [pow_zero, mul_one, Ideal.map_bot, bot_sup_eq]
    exact commonRoot_emptySite_relation M a b (by omega) ha.le
  have ht := TwoRelationChain.thom_of_generators ρ
    (boundaryProjection_surjective M a b false false ha.le hb.le ha hb)
    t ⊥ (S_relationIdeal M a b) (grassmannianCommonRootIdeal M a b)
    (leftP M a b * rightP M a b) (rightP M a b) (leftPbar M a b).divX
    (M - 1) 0 0 hker hp hm hcp hcb
    (by simpa only [hq, hpmap, hbmap, S_relationIdeal, relationIdeal,
      grassmannianCommonRootIdeal] using h)
  simpa only [Nat.add_zero, List.map_id', bot_sup_eq, thomI1, t, Prod.mk.eta] using ht

theorem commonRootFlag_adjointSite (M a b : ℕ) (ha : a < M) (hb : b ≤ M) (hb0 : 0 < b)
    {ns : List (ℕ × ℕ)} (h : TwoRelationChain (S_relationIdeal (M - 1) a (b - 1))
      (grassmannianCommonRootIdeal (M - 1) a (b - 1)) ⊥ ⊤ ns) :
    TwoRelationChain (S_relationIdeal M a b) (grassmannianCommonRootIdeal M a b)
      (thomI1 M a b) (thomI2 M a b)
      (ns.map (fun n => (n.1 + 1, n.2 + 1))) := by
  let ρ := boundaryProjection M a b false true ha.le hb ha hb0
  let t := leftE M a b a
  have hq : (leftP M a b * (rightP M a b).divX).map ρ.toRingHom =
      leftP (M - 1) a (b - 1) * rightP (M - 1) a (b - 1) := by
    rw [Polynomial.map_mul, boundaryProjection_leftP, boundaryProjection_rightP_divX]
    rfl
  have hker (x : S M a b) (hx : ρ x = 0) : t * x ∈ thomI1 M a b := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact thomNG_kills M a b ha x
      ((boundaryProjection_eq_zero M a b false true ha.le hb ha hb0 x).mp hx)
  have hp : Polynomial.C t * X ^ 1 * (leftP M a b * (rightP M a b).divX) ∈
      (thomI1 M a b).map Polynomial.C ⊔ S_relationIdeal M a b := by
    simpa only [pow_one, mul_assoc, sup_comm] using thom_relation_ng M a b
  have hm : Polynomial.C t * X ^ ((M - 1) + 1) ∈
      (thomI1 M a b).map Polynomial.C ⊔ S_relationIdeal M a b := by
    rw [Nat.sub_add_cancel (show 1 ≤ M by omega)]
    apply (show S_relationIdeal M a b ≤ _ from le_sup_right)
    exact (S_relationIdeal M a b).mul_mem_left _
      (relationIdeal_power (leftP M a b) (rightP M a b) M)
  have hpmap : (rightP M a b).divX.map ρ.toRingHom =
      rightP (M - 1) a (b - 1) := boundaryProjection_rightP_divX M a b false ha.le hb ha hb0
  have hbmap : (leftPbar M a b).divX.map ρ.toRingHom =
      leftPbar (M - 1) a (b - 1) :=
    complementCharacteristic_boundary_division M a b true ha hb hb0
  have hc := commonRoot_adjointSite_relations M a b (by omega) ha.le
  have ht := TwoRelationChain.thom_of_generators ρ
    (boundaryProjection_surjective M a b false true ha.le hb ha hb0)
    t (thomI1 M a b) (S_relationIdeal M a b) (grassmannianCommonRootIdeal M a b)
    (leftP M a b * (rightP M a b).divX) (rightP M a b).divX (leftPbar M a b).divX
    (M - 1) 1 1 hker hp hm (by simpa only [pow_one] using hc.1)
    (by simpa only [pow_one] using hc.2)
    (by simpa only [hq, hpmap, hbmap, S_relationIdeal, relationIdeal,
      grassmannianCommonRootIdeal] using h)
  have heq : thomI1 M a b ⊔ Ideal.span {t} = thomI2 M a b :=
    sup_eq_right.mpr (thomI1_le_I2 M a b)
  simpa only [heq] using ht

theorem commonRootFlag_intersectionSite (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M)
    (ha0 : 0 < a) (hb0 : 0 < b) {ns : List (ℕ × ℕ)}
    (h : TwoRelationChain (S_relationIdeal (M - 1) (a - 1) (b - 1))
      (grassmannianCommonRootIdeal (M - 1) (a - 1) (b - 1)) ⊥ ⊤ ns) :
    TwoRelationChain (S_relationIdeal M a b) (grassmannianCommonRootIdeal M a b)
      (thomI2 M a b) (thomI3 M a b)
      (ns.map (fun n => (n.1 + 1, n.2))) := by
  let ρ := boundaryProjection M a b true true ha hb ha0 hb0
  let t := rightH M a b (M - b)
  have hq : ((leftP M a b).divX * (rightP M a b).divX).map ρ.toRingHom =
      leftP (M - 1) (a - 1) (b - 1) * rightP (M - 1) (a - 1) (b - 1) := by
    rw [Polynomial.map_mul, boundaryProjection_leftP_divX, boundaryProjection_rightP_divX]
    rfl
  have hker (x : S M a b) (hx : ρ x = 0) : t * x ∈ thomI2 M a b := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact thomBoth_kills M a b (by omega) hb x
      ((boundaryProjection_eq_zero M a b true true ha hb ha0 hb0 x).mp hx)
  have hp : Polynomial.C t * X ^ 1 * ((leftP M a b).divX * (rightP M a b).divX) ∈
      (thomI2 M a b).map Polynomial.C ⊔ S_relationIdeal M a b := by
    simpa only [pow_one, mul_assoc, sup_comm] using thom_relation_both M a b (by omega) hb
  have hm : Polynomial.C t * X ^ ((M - 1) + 1) ∈
      (thomI2 M a b).map Polynomial.C ⊔ S_relationIdeal M a b := by
    rw [Nat.sub_add_cancel (show 1 ≤ M by omega)]
    apply (show S_relationIdeal M a b ≤ _ from le_sup_right)
    exact (S_relationIdeal M a b).mul_mem_left _
      (relationIdeal_power (leftP M a b) (rightP M a b) M)
  have hpmap : (rightP M a b).divX.map ρ.toRingHom =
      rightP (M - 1) (a - 1) (b - 1) :=
    boundaryProjection_rightP_divX M a b true ha hb ha0 hb0
  have hbmap : (leftPbar M a b).map ρ.toRingHom =
      leftPbar (M - 1) (a - 1) (b - 1) := by
    rw [complementCharacteristic_boundary]; rfl
  have hcp : Polynomial.C t * X ^ 0 * (rightP M a b).divX ∈
      (thomI2 M a b).map Polynomial.C ⊔ grassmannianCommonRootIdeal M a b := by
    simpa only [pow_zero, mul_one] using
      commonRoot_intersectionSite_relation M a b (by omega) ha hb
  have hcb : Polynomial.C t * X ^ 0 * leftPbar M a b ∈
      (thomI2 M a b).map Polynomial.C ⊔ grassmannianCommonRootIdeal M a b := by
    simp only [pow_zero, mul_one]
    exact (show grassmannianCommonRootIdeal M a b ≤ _ from le_sup_right)
      ((grassmannianCommonRootIdeal M a b).mul_mem_left _ (commonRootIdeal_right _ _))
  have ht := TwoRelationChain.thom_of_generators ρ
    (boundaryProjection_surjective M a b true true ha hb ha0 hb0)
    t (thomI2 M a b) (S_relationIdeal M a b) (grassmannianCommonRootIdeal M a b)
    ((leftP M a b).divX * (rightP M a b).divX) (rightP M a b).divX (leftPbar M a b)
    (M - 1) 1 0 hker hp hm hcp hcb
    (by simpa only [hq, hpmap, hbmap, S_relationIdeal, relationIdeal,
      grassmannianCommonRootIdeal] using h)
  simpa only [Nat.add_zero] using ht

theorem commonRootFlag_complementSite (M a b : ℕ) (ha : a ≤ M) (ha0 : 0 < a) (hb : b < M)
    {ns : List (ℕ × ℕ)} (h : TwoRelationChain (S_relationIdeal (M - 1) (a - 1) b)
      (grassmannianCommonRootIdeal (M - 1) (a - 1) b) ⊥ ⊤ ns) :
    TwoRelationChain (S_relationIdeal M a b) (grassmannianCommonRootIdeal M a b) (thomI3 M a b) ⊤
      (ns.map (fun n => (n.1 + 1, n.2))) := by
  let ρ := boundaryProjection M a b true false ha hb.le ha0 hb
  have hq : ((leftP M a b).divX * rightP M a b).map ρ.toRingHom =
      leftP (M - 1) (a - 1) b * rightP (M - 1) (a - 1) b := by
    rw [Polynomial.map_mul, boundaryProjection_leftP_divX, boundaryProjection_rightP]
    rfl
  have hker (x : S M a b) (hx : ρ x = 0) : (1 : S M a b) * x ∈ thomI3 M a b := by
    rw [one_mul, thomI3_eq_boundary]
    exact (boundaryProjection_eq_zero M a b true false ha hb.le ha0 hb x).mp hx
  have hp : Polynomial.C (1 : S M a b) * X ^ 1 *
      ((leftP M a b).divX * rightP M a b) ∈
      (thomI3 M a b).map Polynomial.C ⊔ S_relationIdeal M a b := by
    simpa only [map_one, one_mul, pow_one, mul_assoc, sup_comm] using thom_relation_gn M a b
  have hm : Polynomial.C (1 : S M a b) * X ^ ((M - 1) + 1) ∈
      (thomI3 M a b).map Polynomial.C ⊔ S_relationIdeal M a b := by
    rw [map_one, one_mul, Nat.sub_add_cancel (show 1 ≤ M by omega)]
    exact (show S_relationIdeal M a b ≤ _ from le_sup_right)
      (relationIdeal_power (leftP M a b) (rightP M a b) M)
  have hpmap : (rightP M a b).map ρ.toRingHom =
      rightP (M - 1) (a - 1) b := by rw [boundaryProjection_rightP]; rfl
  have hbmap : (leftPbar M a b).map ρ.toRingHom =
      leftPbar (M - 1) (a - 1) b := by rw [complementCharacteristic_boundary]; rfl
  have hcp : Polynomial.C (1 : S M a b) * X ^ 0 * rightP M a b ∈
      (thomI3 M a b).map Polynomial.C ⊔ grassmannianCommonRootIdeal M a b := by
    simp only [map_one, pow_zero, one_mul]
    exact (show grassmannianCommonRootIdeal M a b ≤ _ from le_sup_right)
      (commonRootIdeal_left _ _)
  have hcb : Polynomial.C (1 : S M a b) * X ^ 0 * leftPbar M a b ∈
      (thomI3 M a b).map Polynomial.C ⊔ grassmannianCommonRootIdeal M a b := by
    simp only [map_one, pow_zero, one_mul]
    exact (show grassmannianCommonRootIdeal M a b ≤ _ from le_sup_right)
      (commonRootIdeal_right _ _)
  have ht := TwoRelationChain.thom_of_generators ρ
    (boundaryProjection_surjective M a b true false ha hb.le ha0 hb)
    1 (thomI3 M a b) (S_relationIdeal M a b) (grassmannianCommonRootIdeal M a b)
    ((leftP M a b).divX * rightP M a b) (rightP M a b) (leftPbar M a b)
    (M - 1) 1 0 hker hp hm hcp hcb
    (by simpa only [hq, hpmap, hbmap, S_relationIdeal, relationIdeal,
      grassmannianCommonRootIdeal] using h)
  simpa only [Nat.add_zero, Ideal.span_singleton_one, sup_top_eq] using ht

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.TwoRelationChain.thom_of_generators
#print axioms VOA.DeligneAudit.D4LevelReduction.commonRootFlag_emptySite
#print axioms VOA.DeligneAudit.D4LevelReduction.commonRootFlag_adjointSite
#print axioms VOA.DeligneAudit.D4LevelReduction.commonRootFlag_intersectionSite
#print axioms VOA.DeligneAudit.D4LevelReduction.commonRootFlag_complementSite
