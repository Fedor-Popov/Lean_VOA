import VOA.Classification.COne.OrbOddVir

/-!
# OrbOdd (3): cached certificates for the Virasoro engine

To keep each kernel computation small, `L(m)` of every PBW word is certified once
(`lowCheck`, `cacheOK`), and vector identities are then checked by pure bookkeeping over the
cached normal forms (`applyCache`, `normK`).  All functions are structural and
kernel-reducible; soundness is proved once for all (`lowCheck_sound`, `applyCache_sound`,
`evV_eq_zero_of_isZeroK`).

Words are ordered by the key `wkey` (letters `< 64`) only to speed up merging; soundness never
uses the key.
-/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbOdd

open VOA VertexOperatorAlgebra

/-- A sort key for words. -/
def wkey : List ℕ → ℕ
  | [] => 0
  | n :: w => n + 64 * wkey w

/-- Keyed terms. -/
abbrev KVec := List (ℕ × ℚ × List ℕ)

/-- Insert a keyed term, merging equal words. -/
def insertK (p : ℕ × ℚ × List ℕ) : KVec → KVec
  | [] => [p]
  | q :: v =>
      if p.1 < q.1 then p :: q :: v
      else if p.1 = q.1 ∧ p.2.2 = q.2.2 then (q.1, q.2.1 + p.2.1, q.2.2) :: v
      else q :: insertK p v

/-- Keyed normalization. -/
def normK : VVec → KVec
  | [] => []
  | p :: v => insertK (wkey p.2, p.1, p.2) (normK v)

/-- All coefficients vanish. -/
def isZeroK (v : KVec) : Bool := v.all fun p => p.2.1 = 0

/-- Back to a vector. -/
def unK (v : KVec) : VVec := v.map fun p => (p.2.1, p.2.2)

/-- `r` is a normal form of `L(m) w` (for highest weight `h`, central charge `cc`). -/
def lowCheck (h cc : ℚ) (fuel m : ℕ) (w : List ℕ) (r : VVec) : Bool :=
  match lowerF h cc fuel m w with
  | some a => isZeroK (normK (a ++ scaleV (-1) r))
  | none => false

/-- A cache of `L(m)`-images: entries `(key, word, image)`. -/
abbrev Cache := List (ℕ × List ℕ × VVec)

def cacheOK (h cc : ℚ) (fuel m : ℕ) (c : Cache) : Bool :=
  c.all fun e => lowCheck h cc fuel m e.2.1 e.2.2

/-- Look a word up (key first, then the word itself). -/
def lookupC (c : Cache) (w : List ℕ) : Option VVec :=
  match c with
  | [] => none
  | e :: c => if e.1 = wkey w ∧ e.2.1 = w then some e.2.2 else lookupC c w

/-- Apply a cache to a vector. -/
def applyCache (c : Cache) (v : VVec) : Option VVec := bindV (lookupC c) v

/-- Apply each witness word to a fixed vector `s` (for multiples of a singular vector). -/
def witApply (fuel : ℕ) (wit : VVec) (s : VVec) : Option VVec :=
  bindV (fun w => raiseWordF fuel w s) wit

/-- Rational coefficients from `(numerator, denominator)` pairs (cheap to elaborate). -/
def ofRaw (l : List (Int × Nat × List ℕ)) : VVec := l.map fun p => (mkRat p.1 p.2.1, p.2.2)

/-- A cache from raw data. -/
def ofRawC (l : List (ℕ × List ℕ × List (Int × Nat × List ℕ))) : Cache :=
  l.map fun e => (e.1, e.2.1, ofRaw e.2.2)

theorem cacheOK_append (h cc : ℚ) (fuel m : ℕ) (a b : Cache) :
    cacheOK h cc fuel m (a ++ b) = (cacheOK h cc fuel m a && cacheOK h cc fuel m b) := by
  simp [cacheOK, List.all_append]

/-- The level-seven singular vector of the `c = 1`, `h = 9` Verma module. -/
def s7v : VVec := ofRaw [(131400, 1, [7]), (-58400, 1, [6, 1]), (-47088, 1, [5, 2]),
  (-43128, 1, [4, 3]), (13760, 1, [5, 1, 1]), (25280, 1, [4, 2, 1]), (10252, 1, [3, 3, 1]),
  (10368, 1, [3, 2, 2]), (-2640, 1, [4, 1, 1, 1]), (-6576, 1, [3, 2, 1, 1]),
  (-2304, 1, [2, 2, 2, 1]), (364, 1, [3, 1, 1, 1, 1]), (784, 1, [2, 2, 1, 1, 1]),
  (-56, 1, [2, 1, 1, 1, 1, 1]), (1, 1, [1, 1, 1, 1, 1, 1, 1])]

/-- The chain check: `L(m) xv = α · prev` modulo multiples (`wit`) of `s₇`. -/
def chkGen (c : Cache) (xv prev wit : VVec) (α : ℚ) : Bool :=
  match applyCache c xv, witApply 64 wit s7v with
  | some a, some b => isZeroK (normK (a ++ scaleV (-α) prev ++ scaleV (-1) b))
  | _, _ => false

/-- The top of the chain: `x₁₅ = u`. -/
def xvTop : VVec := [(1, [])]

/-- `L(1) s₇ = 0` and `L(2) s₇ = 0` in the Verma module. -/
def s7chk (m : ℕ) : Bool := match bindV (lowerF 9 1 64 m) s7v with
  | some r => isZeroK (normK r)
  | none => false

set_option maxRecDepth 100000 in
theorem s7chk_one : s7chk 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem s7chk_two : s7chk 2 = true := by decide +kernel

section Sound

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱} {x : 𝒱}

theorem evV_unK_insertK (p : ℕ × ℚ × List ℕ) (v : KVec) :
    evV W x (unK (insertK p v)) = ((p.2.1 : ℂ)) • evW W x p.2.2 + evV W x (unK v) := by
  induction v with
  | nil => rfl
  | cons q v ih =>
    unfold insertK
    split_ifs with h1 h2
    · rfl
    · simp only [unK, List.map_cons, evV_cons] at *
      rw [h2.2]; push_cast; rw [add_smul]; abel
    · simp only [unK, List.map_cons, evV_cons] at *
      rw [ih]; abel

theorem evV_unK_normK (v : VVec) : evV W x (unK (normK v)) = evV W x v := by
  induction v with
  | nil => rfl
  | cons p v ih => rw [normK, evV_unK_insertK, ih, evV_cons]

theorem evV_eq_zero_of_isZeroK {v : VVec} (h : isZeroK (normK v) = true) : evV W x v = 0 := by
  rw [← evV_unK_normK]
  generalize normK v = k at h
  induction k with
  | nil => rfl
  | cons p k ih =>
    simp only [isZeroK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [unK, List.map_cons, evV_cons] at ih ⊢
    rw [h.1, ih h.2]; simp

theorem lowCheck_sound {h cc : ℚ} (hc : W.centralCharge = (cc : ℂ))
    (hx : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) x = 0) (hx0 : W.L 0 x = (h : ℂ) • x)
    {fuel m : ℕ} {w : List ℕ} {r : VVec} (hk : lowCheck h cc fuel m w r = true) :
    evV W x r = W.L (m : ℤ) (evW W x w) := by
  unfold lowCheck at hk
  split at hk
  · rename_i a ha
    have e := evV_eq_zero_of_isZeroK (W := W) (x := x) hk
    rw [evV_append, evV_scaleV, lowerF_sound hc hx hx0 _ _ _ _ ha] at e
    push_cast at e
    rw [neg_one_smul, add_neg_eq_zero] at e
    exact e.symm
  · exact absurd hk (by simp)

theorem cacheOK_sound {h cc : ℚ} (hc : W.centralCharge = (cc : ℂ))
    (hx : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) x = 0) (hx0 : W.L 0 x = (h : ℂ) • x)
    {fuel m : ℕ} {c : Cache} (hk : cacheOK h cc fuel m c = true) :
    ∀ w r, lookupC c w = some r → evV W x r = W.L (m : ℤ) (evW W x w) := by
  induction c with
  | nil => intro w r hr; simp [lookupC] at hr
  | cons e c ih =>
    simp only [cacheOK, List.all_cons, Bool.and_eq_true] at hk
    intro w r hr
    unfold lookupC at hr
    split_ifs at hr with he
    · simp only [Option.some.injEq] at hr
      subst hr
      rw [← he.2]
      exact lowCheck_sound hc hx hx0 hk.1
    · exact ih hk.2 w r hr

theorem applyCache_sound {h cc : ℚ} (hc : W.centralCharge = (cc : ℂ))
    (hx : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) x = 0) (hx0 : W.L 0 x = (h : ℂ) • x)
    {fuel m : ℕ} {c : Cache} (hk : cacheOK h cc fuel m c = true) {v r : VVec}
    (hr : applyCache c v = some r) : evV W x r = W.L (m : ℤ) (evV W x v) :=
  bindV_sound (cacheOK_sound hc hx hx0 hk) v r hr

/-- Multiples of a vanishing vector vanish. -/
theorem witApply_zero {fuel : ℕ} {wit s r : VVec} (hs : evV W x s = 0)
    (hr : witApply fuel wit s = some r) : evV W x r = 0 := by
  unfold witApply at hr
  have hzero : ∀ w : List ℕ, evW W (0 : 𝒱) w = 0 := by
    intro w; induction w with
    | nil => rfl
    | cons n w ih => simp [evW, ih]
  have := bindV_sound (W := W) (x := x) (g := fun w => raiseWordF fuel w s)
    (T := 0) (fun w r h => by
      rw [raiseWordF_sound fuel w s r h 0 hs, hzero]; rfl) wit r hr
  simpa using this

theorem s7chk_sound (hc : W.centralCharge = ((1 : ℚ) : ℂ))
    (hx : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) x = 0) (hx0 : W.L 0 x = ((9 : ℚ) : ℂ) • x)
    {m : ℕ} (hk : s7chk m = true) : W.L (m : ℤ) (evV W x s7v) = 0 := by
  unfold s7chk at hk
  split at hk
  · rename_i r hr
    rw [← bindV_sound (fun w r h => lowerF_sound hc hx hx0 _ _ w r h) s7v r hr]
    exact evV_eq_zero_of_isZeroK hk
  · exact absurd hk (by simp)

theorem chkGen_sound (hc : W.centralCharge = ((1 : ℚ) : ℂ))
    (hx : ∀ m : ℕ, 1 ≤ m → W.L (m : ℤ) x = 0) (hx0 : W.L 0 x = ((9 : ℚ) : ℂ) • x)
    (hs7 : evV W x s7v = 0) {m : ℕ} {c : Cache} (hcok : cacheOK 9 1 64 m c = true)
    {xv prev wit : VVec} {α : ℚ} (hk : chkGen c xv prev wit α = true) :
    W.L (m : ℤ) (evV W x xv) = (α : ℂ) • evV W x prev := by
  unfold chkGen at hk
  split at hk
  · rename_i a b ha hb
    have e := evV_eq_zero_of_isZeroK (W := W) (x := x) hk
    rw [evV_append, evV_append, evV_scaleV, evV_scaleV, applyCache_sound hc hx hx0 hcok ha,
      witApply_zero hs7 hb] at e
    push_cast at e
    rw [smul_zero, add_zero, neg_smul, add_neg_eq_zero] at e
    exact e
  · exact absurd hk (by simp)

end Sound

end VOA.Classification.COne.OrbOdd
