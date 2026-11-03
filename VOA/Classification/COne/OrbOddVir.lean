import VOA.Core.VertexOperatorAlgebra

/-!
# OrbOdd (1): a kernel-checkable Virasoro normal-ordering engine

Generic, for any VOA `W` with rational central charge `c` and any vector `u` which is a
Virasoro highest-weight vector of weight `h` (`L(m)u = 0` for `m ≥ 1`, `L(0)u = h u`).

A *word* `w = [n₁, …, n_r]` (`nᵢ ≥ 1`) stands for `L(-n₁) ⋯ L(-n_r) u` (`evW`); a *vector* is a
finite `ℚ`-combination of words (`evV`).  The fuel-bounded functions

* `raiseF f m w` — `L(-m)` applied to `w`, straightened into PBW order (`m ≥ 1`),
* `lowerF f m w` — `L(m)` applied to `w`, `m ≥ 0`,

return `none` when out of fuel and are *sound* whenever they return `some`
(`raiseF_sound`, `lowerF_sound`).  `normV` merges equal words (`evV_normV`), so a kernel
computation `isZeroB (normV …) = true` certifies a vector identity in `W` (`evV_eq_zero_of`).

Nothing here is specific to `c = 1`; all numerics are exact over `ℚ`.
-/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbOdd

open VOA VertexOperatorAlgebra

/-- A vector: a `ℚ`-combination of Virasoro words. -/
abbrev VVec := List (ℚ × List ℕ)

/-! ## Pure combinatorics (all structural, kernel-reducible) -/

/-- Scale a vector. -/
def scaleV (a : ℚ) (v : VVec) : VVec := v.map fun p => (a * p.1, p.2)

/-- Bind a word-level operation over a vector. -/
def bindV (g : List ℕ → Option VVec) : VVec → Option VVec
  | [] => some []
  | p :: v => do
      let r ← g p.2
      let s ← bindV g v
      pure (scaleV p.1 r ++ s)

/-- `L(-m)` on a word (`m ≥ 1`), straightened. -/
def raiseF : ℕ → ℕ → List ℕ → Option VVec
  | 0, _, _ => none
  | _ + 1, m, [] => some [(1, [m])]
  | f + 1, m, n :: w =>
      if n ≤ m then some [(1, m :: n :: w)]
      else do
        let a ← raiseF f m w
        let b ← bindV (raiseF f n) a
        let c ← raiseF f (m + n) w
        pure (b ++ scaleV ((n : ℚ) - m) c)

/-- `L(k)` for an integer `k` built from `raiseF` and a given `L(m)`, `m ≥ 0` routine. -/
def applyWith (low : ℕ → List ℕ → Option VVec) (r : ℕ → List ℕ → Option VVec) (k : ℤ)
    (w : List ℕ) : Option VVec :=
  if 0 ≤ k then low k.toNat w else r (-k).toNat w

/-- `L(m)` on a word (`m ≥ 0`), with highest weight `h` and central charge `cc`. -/
def lowerF (h cc : ℚ) : ℕ → ℕ → List ℕ → Option VVec
  | 0, _, _ => none
  | _ + 1, m, [] => if m = 0 then some [(h, [])] else some []
  | f + 1, m, n :: w => do
      let a ← lowerF h cc f m w
      let b ← bindV (raiseF f n) a
      let c ← applyWith (lowerF h cc f) (raiseF f) ((m : ℤ) - n) w
      pure (b ++ scaleV ((m : ℚ) + n) c ++
        (if m = n then [(((m : ℚ) ^ 3 - m) / 12 * cc, w)] else []))

/-- Apply the word `w` (outermost letter first) to a vector. -/
def raiseWordF (f : ℕ) : List ℕ → VVec → Option VVec
  | [], v => some v
  | n :: w, v => do
      let a ← raiseWordF f w v
      bindV (raiseF f n) a

/-- Insert a term, merging equal words (no sorting needed for soundness). -/
def insertT (p : ℚ × List ℕ) : VVec → VVec
  | [] => [p]
  | q :: v => if q.2 = p.2 then (q.1 + p.1, q.2) :: v else q :: insertT p v

/-- Merge equal words. -/
def normV : VVec → VVec
  | [] => []
  | p :: v => insertT p (normV v)

/-- All coefficients vanish. -/
def isZeroB (v : VVec) : Bool := v.all fun p => p.1 = 0

/-! ## Evaluation in a VOA -/

section Eval

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱) (x : 𝒱)

/-- `L(-n₁)⋯L(-n_r) x`. -/
def evW : List ℕ → 𝒱
  | [] => x
  | n :: w => W.L (-(n : ℤ)) (evW w)

/-- Evaluation of a vector. -/
def evV (v : VVec) : 𝒱 := (v.map fun p => ((p.1 : ℂ)) • evW W x p.2).sum

variable {W x}

@[simp] theorem evV_nil : evV W x [] = 0 := rfl

theorem evV_cons (p : ℚ × List ℕ) (v : VVec) :
    evV W x (p :: v) = ((p.1 : ℂ)) • evW W x p.2 + evV W x v := rfl

theorem evV_append (v₁ v₂ : VVec) : evV W x (v₁ ++ v₂) = evV W x v₁ + evV W x v₂ := by
  simp [evV, List.map_append, List.sum_append]

theorem evV_scaleV (a : ℚ) (v : VVec) : evV W x (scaleV a v) = (a : ℂ) • evV W x v := by
  induction v with
  | nil => simp [scaleV]
  | cons p v ih =>
    change ((a * p.1 : ℚ) : ℂ) • evW W x p.2 + evV W x (scaleV a v) = _
    rw [ih, evV_cons, smul_add, smul_smul]
    push_cast; rfl

theorem evV_insertT (p : ℚ × List ℕ) (v : VVec) :
    evV W x (insertT p v) = evV W x (p :: v) := by
  induction v with
  | nil => rfl
  | cons q v ih =>
    unfold insertT
    split_ifs with h
    · rw [evV_cons, evV_cons, evV_cons, h]
      push_cast
      rw [add_smul]; abel
    · rw [evV_cons, ih, evV_cons, evV_cons, evV_cons]; abel

theorem evV_normV (v : VVec) : evV W x (normV v) = evV W x v := by
  induction v with
  | nil => rfl
  | cons p v ih => rw [normV, evV_insertT, evV_cons, ih, evV_cons]

theorem evV_eq_zero_of_isZeroB {v : VVec} (h : isZeroB v = true) : evV W x v = 0 := by
  induction v with
  | nil => rfl
  | cons p v ih =>
    simp only [isZeroB, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [evV_cons, h.1, ih h.2]
    simp

/-- The certificate principle: a normalized vector with all coefficients zero evaluates to 0. -/
theorem evV_eq_zero_of {v : VVec} (h : isZeroB (normV v) = true) : evV W x v = 0 := by
  rw [← evV_normV]; exact evV_eq_zero_of_isZeroB h

end Eval

/-! ## Soundness -/

section Sound

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱} {x : 𝒱}

/-- The Virasoro relation applied to a vector. -/
theorem L_L_apply (a b : ℤ) (y : 𝒱) :
    W.L a (W.L b y) = W.L b (W.L a y) + ((a : ℂ) - b) • W.L (a + b) y +
      (if a + b = 0 then (((a : ℂ) ^ 3 - a) / 12 * W.centralCharge) • y else 0) := by
  have h := congrArg (fun T : Module.End ℂ 𝒱 => T y) (W.L_virasoro a b)
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply] at h
  split_ifs at h ⊢ with hab
  · simp only [LinearMap.smul_apply, Module.End.one_apply] at h
    rw [add_assoc, ← h]; abel
  · simp only [LinearMap.zero_apply, add_zero] at h ⊢
    rw [← h]; abel

theorem bindV_sound {g : List ℕ → Option VVec} {T : 𝒱 →ₗ[ℂ] 𝒱}
    (hg : ∀ w r, g w = some r → evV W x r = T (evW W x w)) :
    ∀ (v r : VVec), bindV g v = some r → evV W x r = T (evV W x v)
  | [], r, h => by
    simp only [bindV, Option.some.injEq] at h
    subst h; simp
  | p :: v, r, h => by
    simp only [bindV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [evV_append, evV_scaleV, hg _ _ ha, bindV_sound hg v b hb, evV_cons, map_add, map_smul]

theorem raiseF_sound : ∀ (f m : ℕ) (w : List ℕ) (r : VVec), raiseF f m w = some r →
    evV W x r = W.L (-(m : ℤ)) (evW W x w)
  | 0, _, _, _, h => by simp [raiseF] at h
  | f + 1, m, [], r, h => by
    simp only [raiseF, Option.some.injEq] at h
    subst h
    simp [evV, evW]
  | f + 1, m, n :: w, r, h => by
    unfold raiseF at h
    split_ifs at h with hnm
    · simp only [Option.some.injEq] at h
      subst h
      simp [evV, evW]
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := h
      have ea := raiseF_sound f m w a ha
      have eb := bindV_sound (W := W) (x := x) (T := W.L (-(n : ℤ)))
        (fun w r h => raiseF_sound f n w r h) a b hb
      have ec := raiseF_sound f (m + n) w c hc
      rw [evV_append, evV_scaleV, eb, ea, ec]
      change _ = W.L (-(m : ℤ)) (W.L (-(n : ℤ)) (evW W x w))
      rw [L_L_apply (-(m : ℤ)) (-(n : ℤ))]
      have hne : ¬ (-(m : ℤ) + -(n : ℤ) = 0) := by omega
      rw [if_neg hne, add_zero]
      push_cast
      congr 1
      congr 1
      · ring_nf
      · congr 1; ring_nf

variable (hcc : ℚ) (h : ℚ)

theorem applyWith_sound {low r : ℕ → List ℕ → Option VVec}
    (hlow : ∀ m w s, low m w = some s → evV W x s = W.L (m : ℤ) (evW W x w))
    (hr : ∀ m w s, r m w = some s → evV W x s = W.L (-(m : ℤ)) (evW W x w))
    (k : ℤ) (w : List ℕ) (s : VVec) (hs : applyWith low r k w = some s) :
    evV W x s = W.L k (evW W x w) := by
  unfold applyWith at hs
  split_ifs at hs with hk
  · rw [hlow _ _ _ hs, show ((k.toNat : ℕ) : ℤ) = k by omega]
  · rw [hr _ _ _ hs, show (-(((-k).toNat : ℕ) : ℤ)) = k by omega]

theorem lowerF_sound {cc h : ℚ} (hc : W.centralCharge = (cc : ℂ))
    (hx : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) x = 0) (hx0 : W.L 0 x = (h : ℂ) • x) :
    ∀ (f m : ℕ) (w : List ℕ) (r : VVec), lowerF h cc f m w = some r →
      evV W x r = W.L (m : ℤ) (evW W x w)
  | 0, _, _, _, hr => by simp [lowerF] at hr
  | f + 1, m, [], r, hr => by
    simp only [lowerF] at hr
    split_ifs at hr with hm
    · simp only [Option.some.injEq] at hr
      subst hr; subst hm
      simp [evV, evW, hx0]
    · simp only [Option.some.injEq] at hr
      subst hr
      simp only [evV_nil, evW]
      rw [hx m (by omega)]
  | f + 1, m, n :: w, r, hr => by
    simp only [lowerF, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hr
    obtain ⟨a, ha, b, hb, c, hc', rfl⟩ := hr
    have ea := lowerF_sound hc hx hx0 f m w a ha
    have eb := bindV_sound (W := W) (x := x) (T := W.L (-(n : ℤ)))
      (fun w r h => raiseF_sound f n w r h) a b hb
    have ec := applyWith_sound (W := W) (x := x)
      (fun m w s h => lowerF_sound hc hx hx0 f m w s h)
      (fun m w s h => raiseF_sound f m w s h) _ w c hc'
    rw [evV_append, evV_append, evV_scaleV, eb, ea, ec]
    change _ = W.L (m : ℤ) (W.L (-(n : ℤ)) (evW W x w))
    rw [L_L_apply (m : ℤ) (-(n : ℤ)), hc]
    split_ifs with h1 h2 h2
    · subst h1
      simp only [evV_cons, evV_nil, add_zero]
      push_cast
      rw [show ((m : ℂ) - -(m : ℂ)) = (m : ℂ) + m by ring,
        show (m : ℤ) + -(m : ℤ) = (m : ℤ) - m by ring]
    · exact absurd (by omega) h2
    · exact absurd (by exact_mod_cast (by omega : m = n)) h1
    · simp only [evV_nil, add_zero]
      push_cast
      rw [show ((m : ℂ) - -(n : ℂ)) = (m : ℂ) + n by ring,
        show (m : ℤ) + -(n : ℤ) = (m : ℤ) - n by ring]

theorem raiseWordF_sound (f : ℕ) : ∀ (w : List ℕ) (v r : VVec), raiseWordF f w v = some r →
    ∀ y : 𝒱, evV W x v = y → evV W x r = evW W y w
  | [], v, r, hr, y, hy => by
    simp only [raiseWordF, Option.some.injEq] at hr
    subst hr; exact hy
  | n :: w, v, r, hr, y, hy => by
    simp only [raiseWordF, Option.bind_eq_bind, Option.bind_eq_some_iff] at hr
    obtain ⟨a, ha, hb⟩ := hr
    have ea := raiseWordF_sound f w v a ha y hy
    have eb := bindV_sound (W := W) (x := x) (T := W.L (-(n : ℤ)))
      (fun w r h => raiseF_sound f n w r h) a r hb
    rw [eb, ea]; rfl

end Sound

end VOA.Classification.COne.OrbOdd
