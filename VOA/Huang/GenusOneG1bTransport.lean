import VOA.Huang.GenusOneG1bKernels

/-!
# Transport of a product Euler system to the iterate channel (abstract form)

Step 3 of the iterate-transport argument. Data:

* product rows `ph j f n ∈ ℂ⟦t⟧` (channel `j`, generator `f`, traced level `n`) satisfying ONE
  Euler system with polynomial numerators common to all channels,
  `(λ+n)(1−t)^E ph_j f n = Σ_g Σ_{p≤n} Pol_{fgp}(t) ph_j g (n−p)` (`H1`);
* iterate rows `Γ f n ∈ ℂ⟦x⟧`, weighted-sup bounded at radius `3/4`;
* on the real segment `0 < s < 1` the associativity identity (`hC`)
  `s^{B₀−a_f−b_f} Γ_f n(s) = Σ_j (1+s)^{A_j−a_f+n} ph_j f n(1/(1+s))`,
  where `a_f, b_f ∈ ℕ` are the levels of the generator.

Conclusion (`transport_system`): the iterate rows satisfy the FORMAL Laurent system
`(λ+n) X^{E+D} Γ_f n = Σ_g Σ_{p≤n} X^{s_{fg}} K_{fgp} Γ_g (n−p)` with the transported
kernels `K_{fgp} = transKer (Pol f g p) …`, independent of `n`.

Proof: evaluate `H1` at `t = 1/(1+s)`, multiply by `(1+s)^{A_j−a_f+n+E+L}` (the integer
level shifts make every kernel a polynomial `transPoly` in `s`), sum over `j`, substitute
`hC`, clear `s^{B_f}`; both sides are then polynomial × convergent series in `s`, equal on
`(0,1/2)`, hence equal as power series (`eq_zero_of_evS_real`); finally cancel `(1+X)^L`.
-/
noncomputable section
namespace VOA.Huang.GenusOneG1b
open scoped BigOperators
open VOA.Huang.GenusOneWard (pc coeff_pc omt)

/-! ## Weighted-sup bounds -/

/-- A weighted-sup bound at radius `r`. -/
def WB (r : ℝ) (F : PowerSeries ℂ) : Prop := ∃ B : ℝ, ∀ i, ‖PowerSeries.coeff i F‖ * r ^ i ≤ B

theorem WB.add {r : ℝ} {F G : PowerSeries ℂ} (hF : WB r F) (hG : WB r G) (hr : 0 ≤ r) :
    WB r (F + G) := by
  obtain ⟨B₁, h₁⟩ := hF
  obtain ⟨B₂, h₂⟩ := hG
  refine ⟨B₁ + B₂, fun i => ?_⟩
  rw [map_add]
  calc ‖PowerSeries.coeff i F + PowerSeries.coeff i G‖ * r ^ i
      ≤ (‖PowerSeries.coeff i F‖ + ‖PowerSeries.coeff i G‖) * r ^ i :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ ≤ B₁ + B₂ := by rw [add_mul]; exact add_le_add (h₁ i) (h₂ i)

theorem WB.smul {r : ℝ} {F : PowerSeries ℂ} (hF : WB r F) (c : ℂ) : WB r (c • F) := by
  obtain ⟨B, h⟩ := hF
  refine ⟨‖c‖ * B, fun i => ?_⟩
  rw [PowerSeries.coeff_smul, smul_eq_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h i) (norm_nonneg c)

theorem WB.pc_mul {r : ℝ} {F : PowerSeries ℂ} (hF : WB r F) (hr : 0 ≤ r) (P : Polynomial ℂ) :
    WB r (pc P * F) := by
  obtain ⟨B, h⟩ := hF
  exact ⟨_, coeff_mul_le hr (normLe_pc P hr) h⟩

theorem WB.zero (r : ℝ) : WB r 0 := ⟨0, fun i => by simp⟩

theorem WB.sum {κ : Type*} (s : Finset κ) {r : ℝ} (hr : 0 ≤ r) {F : κ → PowerSeries ℂ}
    (h : ∀ i ∈ s, WB r (F i)) : WB r (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using WB.zero r
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) hr

theorem evS_sub {F G : PowerSeries ℂ} {x : ℂ} (hF : SumAt F x) (hG : SumAt G x) :
    evS (F - G) x = evS F x - evS G x := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ G, evS_add hF (hG.smul _), evS_smul]
  ring

/-- A weighted-sup bound at radius `r` gives absolute summability at every `ρ < r`. -/
theorem summable_of_wsup {F : PowerSeries ℂ} {r ρ B : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < r)
    (hB : ∀ k, ‖PowerSeries.coeff k F‖ * r ^ k ≤ B) :
    Summable fun k => ‖PowerSeries.coeff k F‖ * ρ ^ k := by
  have hr0 : 0 < r := lt_of_le_of_lt hρ0 hρ
  have hq : ρ / r < 1 := (div_lt_one hr0).2 hρ
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one (by positivity) hq).mul_left B)
  have hrk : 0 < r ^ k := pow_pos hr0 k
  calc ‖PowerSeries.coeff k F‖ * ρ ^ k = (‖PowerSeries.coeff k F‖ * r ^ k) * (ρ / r) ^ k := by
        rw [div_pow]; field_simp
    _ ≤ B * (ρ / r) ^ k := mul_le_mul_of_nonneg_right (hB k) (by positivity)

/-! ## The cpow bookkeeping -/

theorem cpow_mul_pow_eq {z : ℂ} (hz : z ≠ 0) {X Y : ℂ} {k₁ k₂ : ℕ}
    (h : X + k₁ = Y + k₂) : z ^ X * z ^ k₁ = z ^ Y * z ^ k₂ := by
  rw [← Complex.cpow_natCast, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hz,
    ← Complex.cpow_add _ _ hz, h]

/-! ## The transport -/

section Transport
variable {κ J : Type*} [Fintype κ] [Fintype J]

/-- The total level `D = Σ_f (a_f + b_f)`. -/
def dTot (a b : κ → ℕ) : ℕ := ∑ f, (a f + b f)

/-- `A = Σ_f a_f`. -/
def aTot (a : κ → ℕ) : ℕ := ∑ f, a f

theorem le_dTot (a b : κ → ℕ) (f : κ) : a f + b f ≤ dTot a b :=
  Finset.single_le_sum (f := fun f => a f + b f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ f)

theorem le_aTot (a : κ → ℕ) (f : κ) : a f ≤ aTot a :=
  Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ f)

/-- The spatial shift `s_{fg}`. -/
def shiftOf (a b : κ → ℕ) (f g : κ) : ℕ := dTot a b + (a f + b f) - (a g + b g)

/-- The negative-power order `N_p = c p + d + A`. -/
def negOf (c d : ℕ) (a : κ → ℕ) (p : ℕ) : ℕ := c * p + d + aTot a

/-- The numerator degree `m_{fgp} = E + N_p + p + a_g − a_f`. -/
def degOf (E c d : ℕ) (a : κ → ℕ) (f g : κ) (p : ℕ) : ℕ := E + negOf c d a p + p + a g - a f

/-- The transported kernel. -/
def kerOf (Pol : κ → κ → ℕ → Polynomial ℂ) (E c d : ℕ) (a : κ → ℕ) (f g : κ) (p : ℕ) :
    PowerSeries ℂ :=
  transKer (Pol f g p) (degOf E c d a f g p) (negOf c d a p)

/-- Step A: the Euler system evaluated at a point. -/
theorem euler_eval {lam : ℂ} {E : ℕ} {Pol : κ → κ → ℕ → Polynomial ℂ}
    {ph : κ → ℕ → PowerSeries ℂ}
    (H1 : ∀ f (n : ℕ), (lam + n) • (omt ^ E * ph f n) =
      ∑ g, ∑ p ∈ Finset.range (n + 1), pc (Pol f g p) * ph g (n - p))
    {t : ℂ} (hph : ∀ f n, SumAt (ph f n) t) (f : κ) (n : ℕ) :
    (lam + n) * ((1 - t) ^ E * evS (ph f n) t) =
      ∑ g, ∑ p ∈ Finset.range (n + 1), (Pol f g p).eval t * evS (ph g (n - p)) t := by
  have h := congrArg (fun F => evS F t) (H1 f n)
  simp only at h
  have homt : omt ^ E = pc ((1 - Polynomial.X) ^ E) := by
    rw [map_pow, VOA.Huang.GenusOneWard.pc_omt]
  rw [evS_smul, homt, evS_pc_mul (hph f n)] at h
  rw [evS_sum _ fun g _ => SumAt.sum _ fun p _ => (hph g (n - p)).pc_mul _] at h
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X] at h
  rw [h]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [evS_sum _ fun p _ => (hph g (n - p)).pc_mul _]
  exact Finset.sum_congr rfl fun p _ => evS_pc_mul (hph g (n - p)) _

/-- Step B: one channel, multiplied by `(1+s)^{A_j − a_f + n + E + L}`. -/
theorem channel_identity {lam : ℂ} {E c d : ℕ} {Pol : κ → κ → ℕ → Polynomial ℂ}
    (hdeg : ∀ f g p, (Pol f g p).natDegree ≤ c * p + d)
    {ph : κ → ℕ → PowerSeries ℂ}
    (H1 : ∀ f (n : ℕ), (lam + n) • (omt ^ E * ph f n) =
      ∑ g, ∑ p ∈ Finset.range (n + 1), pc (Pol f g p) * ph g (n - p))
    (a : κ → ℕ) (A₀ : ℂ) {s : ℝ} (hs : 0 < s)
    (hph : ∀ f n, SumAt (ph f n) (((1 + s : ℝ) : ℂ)⁻¹)) (f : κ) (n : ℕ) :
    (lam + n) * ((s : ℂ) ^ E * ((1 + s : ℝ) : ℂ) ^ (c * n + d + aTot a) *
        (((1 + s : ℝ) : ℂ) ^ (A₀ - a f + n) * evS (ph f n) (((1 + s : ℝ) : ℂ)⁻¹))) =
      ∑ g, ∑ p ∈ Finset.range (n + 1),
        (transPoly (Pol f g p) (E + (c * n + d + aTot a) + p + a g - a f)).eval (s : ℂ) *
        (((1 + s : ℝ) : ℂ) ^ (A₀ - a g + ↑(n - p)) *
          evS (ph g (n - p)) (((1 + s : ℝ) : ℂ)⁻¹)) := by
  set z : ℂ := ((1 + s : ℝ) : ℂ) with hz
  set L := c * n + d + aTot a with hL
  have hz0 : z ≠ 0 := by rw [hz]; exact_mod_cast (by linarith : (1 + s) ≠ 0)
  have hzs : z = 1 + (s : ℂ) := by rw [hz]; push_cast; ring
  have hA := euler_eval H1 hph f n
  have hst : (1 - z⁻¹) * z = (s : ℂ) := by
    rw [sub_mul, inv_mul_cancel₀ hz0, hzs]; ring
  -- left side
  have hleft : (lam + n) * ((s : ℂ) ^ E * z ^ L * (z ^ (A₀ - a f + n) * evS (ph f n) z⁻¹)) =
      z ^ (A₀ - a f + n) * z ^ E * z ^ L *
        ((lam + n) * ((1 - z⁻¹) ^ E * evS (ph f n) z⁻¹)) := by
    rw [← hst, mul_pow]; ring
  rw [hleft, hA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  have hdegm : (Pol f g p).natDegree ≤ E + L + p + a g - a f := by
    have h1 := hdeg f g p
    have h2 : c * p ≤ c * n := Nat.mul_le_mul_left c (by omega)
    have h3 := le_aTot a f
    omega
  rw [eval_transPoly (Pol f g p) hdegm (by rw [← hzs]; exact hz0), ← hzs]
  have key : z ^ (A₀ - a f + n) * (z ^ E * z ^ L) =
      z ^ (A₀ - a g + ↑(n - p)) * z ^ (E + L + p + a g - a f) := by
    rw [← pow_add]
    apply cpow_mul_pow_eq hz0
    have h3 := le_aTot a f
    have hL' : a f ≤ L := by rw [hL]; omega
    push_cast [Nat.cast_sub (show a f ≤ E + L + p + a g by omega), Nat.cast_sub (Nat.le_of_lt_succ hp)]
    ring
  calc z ^ (A₀ - a f + n) * z ^ E * z ^ L *
        ((Pol f g p).eval z⁻¹ * evS (ph g (n - p)) z⁻¹)
      = (z ^ (A₀ - a f + n) * (z ^ E * z ^ L)) *
          ((Pol f g p).eval z⁻¹ * evS (ph g (n - p)) z⁻¹) := by ring
    _ = (z ^ (A₀ - a g + ↑(n - p)) * z ^ (E + L + p + a g - a f)) *
          ((Pol f g p).eval z⁻¹ * evS (ph g (n - p)) z⁻¹) := by rw [key]
    _ = _ := by ring

/-- Step C1: the channels summed, `hC` substituted, `s^{B_f}` cleared. -/
theorem summed_identity {lam : ℂ} {E c d : ℕ} {Pol : κ → κ → ℕ → Polynomial ℂ}
    (hdeg : ∀ f g p, (Pol f g p).natDegree ≤ c * p + d)
    {ph : J → κ → ℕ → PowerSeries ℂ}
    (H1 : ∀ j f (n : ℕ), (lam + n) • (omt ^ E * ph j f n) =
      ∑ g, ∑ p ∈ Finset.range (n + 1), pc (Pol f g p) * ph j g (n - p))
    (a b : κ → ℕ) (A₀ : J → ℂ) (B₀ : ℂ) (Γ : κ → ℕ → PowerSeries ℂ)
    {s : ℝ} (hs : 0 < s)
    (hph : ∀ j f n, SumAt (ph j f n) (((1 + s : ℝ) : ℂ)⁻¹))
    (hC : ∀ f (n : ℕ), (s : ℂ) ^ (B₀ - a f - b f) * evS (Γ f n) s =
      ∑ j, ((1 + s : ℝ) : ℂ) ^ (A₀ j - a f + n) * evS (ph j f n) (((1 + s : ℝ) : ℂ)⁻¹))
    (f : κ) (n : ℕ) :
    (lam + n) * ((s : ℂ) ^ (E + dTot a b) * (1 + (s : ℂ)) ^ (c * n + d + aTot a) *
        evS (Γ f n) s) =
      ∑ g, ∑ p ∈ Finset.range (n + 1),
        ((s : ℂ) ^ shiftOf a b f g *
          (transPoly (Pol f g p) (E + (c * n + d + aTot a) + p + a g - a f)).eval (s : ℂ)) *
        evS (Γ g (n - p)) s := by
  set z : ℂ := ((1 + s : ℝ) : ℂ) with hz
  set L := c * n + d + aTot a with hL
  set D := dTot a b with hD
  have hzs : z = 1 + (s : ℂ) := by rw [hz]; push_cast; ring
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hch := fun j => channel_identity hdeg (H1 j) a (A₀ j) hs (hph j) f n
  simp only [← hz, ← hL] at hch
  have hsum := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hch j)
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← hC f n] at hsum
  have hre : ∀ (F : J → κ → ℕ → ℂ), ∑ j, ∑ g, ∑ p ∈ Finset.range (n + 1), F j g p =
      ∑ g, ∑ p ∈ Finset.range (n + 1), ∑ j, F j g p := by
    intro F
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_comm]
  rw [hre] at hsum
  simp_rw [← Finset.mul_sum] at hsum
  simp_rw [← hC] at hsum
  -- hsum : (lam+n) * (s^E * z^L * (s^{B_f} evΓ)) = Σ_g Σ_p TP * (s^{B_g} evΓ)
  have hBf : (s : ℂ) ^ (B₀ - a f - b f) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hs0)
  have hshift : ∀ g, (s : ℂ) ^ (B₀ - a g - b g) * (s : ℂ) ^ D =
      (s : ℂ) ^ (B₀ - a f - b f) * (s : ℂ) ^ shiftOf a b f g := by
    intro g
    apply cpow_mul_pow_eq hs0
    have h1 := le_dTot a b g
    rw [shiftOf]
    push_cast [Nat.cast_sub (show a g + b g ≤ dTot a b + (a f + b f) by omega)]
    rw [← hD]
    ring
  apply mul_left_cancel₀ hBf
  have hmul := congrArg (fun w => w * (s : ℂ) ^ D) hsum
  beta_reduce at hmul
  rw [← hzs]
  calc (s : ℂ) ^ (B₀ - a f - b f) * ((lam + n) * ((s : ℂ) ^ (E + D) * z ^ L * evS (Γ f n) s))
      = (lam + n) * ((s : ℂ) ^ E * z ^ L * ((s : ℂ) ^ (B₀ - a f - b f) * evS (Γ f n) s)) *
          (s : ℂ) ^ D := by rw [pow_add]; ring
    _ = (∑ g, ∑ p ∈ Finset.range (n + 1),
          (transPoly (Pol f g p) (E + L + p + a g - a f)).eval (s : ℂ) *
            ((s : ℂ) ^ (B₀ - a g - b g) * evS (Γ g (n - p)) s)) * (s : ℂ) ^ D := hmul
    _ = (s : ℂ) ^ (B₀ - a f - b f) * ∑ g, ∑ p ∈ Finset.range (n + 1),
          ((s : ℂ) ^ shiftOf a b f g *
            (transPoly (Pol f g p) (E + L + p + a g - a f)).eval (s : ℂ)) *
          evS (Γ g (n - p)) s := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        have := hshift g
        calc (transPoly (Pol f g p) (E + L + p + a g - a f)).eval (s : ℂ) *
              ((s : ℂ) ^ (B₀ - a g - b g) * evS (Γ g (n - p)) s) * (s : ℂ) ^ D
            = (transPoly (Pol f g p) (E + L + p + a g - a f)).eval (s : ℂ) *
                ((s : ℂ) ^ (B₀ - a g - b g) * (s : ℂ) ^ D) * evS (Γ g (n - p)) s := by ring
          _ = _ := by rw [this]; ring

/-- **The transported formal Laurent system for the iterate rows.** -/
theorem transport_system {lam : ℂ} {E c d : ℕ} {Pol : κ → κ → ℕ → Polynomial ℂ}
    (hdeg : ∀ f g p, (Pol f g p).natDegree ≤ c * p + d)
    {ph : J → κ → ℕ → PowerSeries ℂ}
    (H1 : ∀ j f (n : ℕ), (lam + n) • (omt ^ E * ph j f n) =
      ∑ g, ∑ p ∈ Finset.range (n + 1), pc (Pol f g p) * ph j g (n - p))
    (a b : κ → ℕ) (A₀ : J → ℂ) (B₀ : ℂ) (Γ : κ → ℕ → PowerSeries ℂ)
    (hph : ∀ j f n (s : ℝ), 0 < s → s < 1 → SumAt (ph j f n) (((1 + s : ℝ) : ℂ)⁻¹))
    (hΓ : ∀ f n, WB (3 / 4) (Γ f n))
    (hC : ∀ f (n : ℕ) (s : ℝ), 0 < s → s < 1 → (s : ℂ) ^ (B₀ - a f - b f) * evS (Γ f n) s =
      ∑ j, ((1 + s : ℝ) : ℂ) ^ (A₀ j - a f + n) * evS (ph j f n) (((1 + s : ℝ) : ℂ)⁻¹))
    (f : κ) (n : ℕ) :
    (lam + n) • (PowerSeries.X ^ (E + dTot a b) * Γ f n) =
      ∑ g, ∑ p ∈ Finset.range (n + 1),
        PowerSeries.X ^ (shiftOf a b f g) * (kerOf Pol E c d a f g p * Γ g (n - p)) := by
  set L := c * n + d + aTot a with hL
  set TP : κ → ℕ → Polynomial ℂ := fun g p =>
    Polynomial.X ^ shiftOf a b f g * transPoly (Pol f g p) (E + L + p + a g - a f) with hTP
  set LHS : PowerSeries ℂ := (lam + n) •
    (pc (Polynomial.X ^ (E + dTot a b) * (Polynomial.X + 1) ^ L) * Γ f n) with hLHS
  set RHS : PowerSeries ℂ := ∑ g, ∑ p ∈ Finset.range (n + 1), pc (TP g p) * Γ g (n - p)
    with hRHS
  -- analytic equality on (0, 1/2)
  have hsum34 : ∀ g m (s : ℝ), 0 < s → s < 1 / 2 → SumAt (Γ g m) (s : ℂ) := by
    intro g m s hs0 hs1
    obtain ⟨B, hB⟩ := hΓ g m
    refine SumAt.of_bound (r := 3 / 4) (B := B) ?_ hB
    rw [Complex.norm_real, Real.norm_of_nonneg hs0.le]; linarith
  have hev : ∀ s : ℝ, 0 < s → s < 1 / 2 → evS (LHS - RHS) s = 0 := by
    intro s hs0 hs1
    have hS : ∀ g m, SumAt (Γ g m) (s : ℂ) := fun g m => hsum34 g m s hs0 hs1
    have hR : SumAt RHS s := SumAt.sum _ fun g _ => SumAt.sum _ fun p _ => (hS g _).pc_mul _
    have hL' : SumAt LHS s := ((hS f n).pc_mul _).smul _
    rw [evS_sub hL' hR, sub_eq_zero, hLHS, evS_smul, evS_pc_mul (hS f n), hRHS,
      evS_sum _ fun g _ => SumAt.sum _ fun p _ => (hS g _).pc_mul _]
    have hsi := summed_identity hdeg H1 a b A₀ B₀ Γ hs0
      (fun j g m => hph j g m s hs0 (by linarith))
      (fun g m => hC g m s hs0 (by linarith)) f n
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_one]
    rw [← hL] at hsi
    rw [show ((s : ℂ) + 1) = 1 + (s : ℂ) by ring, hsi]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [evS_sum _ fun p _ => (hS g _).pc_mul _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [evS_pc_mul (hS g _), hTP]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  -- summability of the difference at radius 1/2
  have hWB : WB (3 / 4) (LHS - RHS) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ RHS]
    refine WB.add (((hΓ f n).pc_mul (by norm_num) _).smul _) (WB.smul ?_ _) (by norm_num)
    exact WB.sum _ (by norm_num) fun g _ => WB.sum _ (by norm_num) fun p _ =>
      (hΓ g _).pc_mul (by norm_num) _
  obtain ⟨Bd, hBd⟩ := hWB
  have hzero := eq_zero_of_evS_real (F := LHS - RHS) (ρ := 1 / 2) (by norm_num)
    (summable_of_wsup (by norm_num) (by norm_num) hBd) hev
  have hLR : LHS = RHS := sub_eq_zero.mp hzero
  -- clear (1+X)^L
  have hLHS' : LHS = (1 + PowerSeries.X) ^ L *
      ((lam + n) • (PowerSeries.X ^ (E + dTot a b) * Γ f n)) := by
    rw [hLHS, map_mul, map_pow, map_pow, pc_X_add_one]
    simp only [pc, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
    rw [mul_smul_comm]; ring_nf
  have hRHS' : RHS = (1 + PowerSeries.X) ^ L * ∑ g, ∑ p ∈ Finset.range (n + 1),
      PowerSeries.X ^ (shiftOf a b f g) * (kerOf Pol E c d a f g p * Γ g (n - p)) := by
    rw [hRHS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_range] at hp
    have hNL : negOf c d a p ≤ L := by
      rw [negOf, hL]
      have : c * p ≤ c * n := Nat.mul_le_mul_left c (by omega)
      omega
    have hdm : (Pol f g p).natDegree ≤ degOf E c d a f g p := by
      have h1 := hdeg f g p
      have h2 := le_aTot a f
      rw [degOf, negOf]
      omega
    have hk := one_add_X_pow_mul_transKer (Pol f g p) hdm hNL
    have harith : degOf E c d a f g p + (L - negOf c d a p) = E + L + p + a g - a f := by
      have h2 := le_aTot a f
      rw [degOf, negOf]
      rw [negOf] at hNL
      omega
    rw [harith] at hk
    rw [hTP, map_mul, map_pow, ← hk, kerOf]
    simp only [pc, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
    ring
  rw [hLHS', hRHS'] at hLR
  have hinv : invOnePlusX ^ L * (1 + PowerSeries.X) ^ L = 1 := by
    rw [← mul_pow, mul_comm, one_add_X_mul_inv, one_pow]
  have := congrArg (fun F => invOnePlusX ^ L * F) hLR
  beta_reduce at this
  rwa [← mul_assoc, ← mul_assoc, hinv, one_mul, one_mul] at this

end Transport

end VOA.Huang.GenusOneG1b
