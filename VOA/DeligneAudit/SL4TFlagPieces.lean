import VOA.DeligneAudit.SL4TFlagPolynomial

/-! # Transport of the four smaller spanning flags -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra ℂ R] [Algebra ℂ T]

theorem SpanningChain.thom_of_generators (ρ : R →ₐ[ℂ] T)
    (hρ : Function.Surjective ρ) (t : R) (I : Ideal R) (A : Ideal R[X])
    (q : R[X]) (m s : ℕ) (hker : ∀ x, ρ x = 0 → t * x ∈ I)
    (hq : Polynomial.C t * X ^ s * q ∈ I.map Polynomial.C ⊔ A)
    (hm : Polynomial.C t * X ^ (m + s) ∈ I.map Polynomial.C ⊔ A)
    {ns : List ℕ}
    (h : SpanningChain (Ideal.span {q.map ρ.toRingHom} ⊔ Ideal.span {X ^ m}) ⊥ ⊤ ns) :
    SpanningChain A I (I ⊔ Ideal.span {t}) (ns.map (fun n => n + s)) := by
  have ht := h.thom ρ hρ t I A _ s (thomFlag_polynomial ρ hρ t I A q m s hq hm)
  simpa only [thomFlagIdeal_bot ρ t I hker, thomFlagIdeal_top] using ht

theorem boundaryProjection_eq_zero (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) (x : S M a b) :
    boundaryProjection M a b cutL cutR ha hb hL hR x = 0 ↔
      x ∈ boundaryIdeal M a b cutL cutR := by
  change S_boundary_quot M a b cutL cutR ha hb hL hR
      (Ideal.Quotient.mk _ x) = 0 ↔ _
  rw [map_eq_zero_iff _ (S_boundary_quot M a b cutL cutR ha hb hL hR).injective]
  exact Ideal.Quotient.eq_zero_iff_mem

theorem flagPiece_nn (M a b : ℕ) (ha : a < M) (hb : b < M) {ns : List ℕ}
    (h : SpanningChain (S_relationIdeal (M - 1) a b) ⊥ ⊤ ns) :
    SpanningChain (S_relationIdeal M a b) ⊥ (thomI1 M a b) ns := by
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
  have ht := SpanningChain.thom_of_generators ρ
    (boundaryProjection_surjective M a b false false ha.le hb.le ha hb)
    t ⊥ (S_relationIdeal M a b) (leftP M a b * rightP M a b) (M - 1) 0
    hker hp hm (by simpa only [hq] using h)
  have hid : ns.map (fun n => n + 0) = ns :=
    List.map_id'' (fun n : ℕ => Nat.add_zero n) ns
  simpa only [hid, bot_sup_eq, thomI1, t] using ht

theorem flagPiece_ng (M a b : ℕ) (ha : a < M) (hb : b ≤ M) (hb0 : 0 < b)
    {ns : List ℕ} (h : SpanningChain (S_relationIdeal (M - 1) a (b - 1)) ⊥ ⊤ ns) :
    SpanningChain (S_relationIdeal M a b) (thomI1 M a b) (thomI2 M a b)
      (ns.map (fun n => n + 1)) := by
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
  have ht := SpanningChain.thom_of_generators ρ
    (boundaryProjection_surjective M a b false true ha.le hb ha hb0)
    t (thomI1 M a b) (S_relationIdeal M a b)
    (leftP M a b * (rightP M a b).divX) (M - 1) 1 hker hp hm
    (by simpa only [hq] using h)
  have heq : thomI1 M a b ⊔ Ideal.span {t} = thomI2 M a b :=
    sup_eq_right.mpr (thomI1_le_I2 M a b)
  simpa only [heq] using ht

theorem flagPiece_both (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M)
    (ha0 : 0 < a) (hb0 : 0 < b) {ns : List ℕ}
    (h : SpanningChain (S_relationIdeal (M - 1) (a - 1) (b - 1)) ⊥ ⊤ ns) :
    SpanningChain (S_relationIdeal M a b) (thomI2 M a b) (thomI3 M a b)
      (ns.map (fun n => n + 1)) := by
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
  exact SpanningChain.thom_of_generators ρ
    (boundaryProjection_surjective M a b true true ha hb ha0 hb0)
    t (thomI2 M a b) (S_relationIdeal M a b)
    ((leftP M a b).divX * (rightP M a b).divX) (M - 1) 1 hker hp hm
    (by simpa only [hq] using h)

theorem flagPiece_gn (M a b : ℕ) (ha : a ≤ M) (ha0 : 0 < a) (hb : b < M)
    {ns : List ℕ} (h : SpanningChain (S_relationIdeal (M - 1) (a - 1) b) ⊥ ⊤ ns) :
    SpanningChain (S_relationIdeal M a b) (thomI3 M a b) ⊤
      (ns.map (fun n => n + 1)) := by
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
  have ht := SpanningChain.thom_of_generators ρ
    (boundaryProjection_surjective M a b true false ha hb.le ha0 hb)
    1 (thomI3 M a b) (S_relationIdeal M a b)
    ((leftP M a b).divX * rightP M a b) (M - 1) 1 hker hp hm
    (by simpa only [hq] using h)
  simpa only [Ideal.span_singleton_one, sup_top_eq] using ht

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.SpanningChain.thom_of_generators
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_eq_zero
#print axioms VOA.DeligneAudit.SL4T.flagPiece_nn
#print axioms VOA.DeligneAudit.SL4T.flagPiece_ng
#print axioms VOA.DeligneAudit.SL4T.flagPiece_both
#print axioms VOA.DeligneAudit.SL4T.flagPiece_gn
