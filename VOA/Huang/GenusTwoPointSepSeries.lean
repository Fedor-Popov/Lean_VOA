import VOA.Huang.UniformConvSeries
import VOA.Huang.GenusOneQEquationAlgebra
import VOA.Modularity.SubexpClosure

/-!
# The coefficient algebra on the product bidisc

Double power series with jointly subexponential coefficients form a subalgebra.
Consequently finite algebra generation preserves bounds on the entire open unit
bidisc. This is a coefficient-ring result, with no hypothesis about convergence
of the unknown trace series.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA VOA.Huang.HuangODEThree VOA.Huang.UniformConv
open scoped BigOperators

abbrev BiSeries := PowerSeries (PowerSeries ℂ)

def coeff (f : BiSeries) (i j : ℕ) : ℂ :=
  PowerSeries.coeff j (PowerSeries.coeff i f)

def ofArray (c : ℕ → ℕ → ℂ) : BiSeries :=
  PowerSeries.mk (fun i => PowerSeries.mk (c i))

@[simp] theorem coeff_ofArray (c : ℕ → ℕ → ℂ) (i j : ℕ) :
    coeff (ofArray c) i j = c i j := by simp [coeff, ofArray]

theorem coeff_ofArray_fun (c : ℕ → ℕ → ℂ) : coeff (ofArray c) = c :=
  funext fun i => funext fun j => coeff_ofArray c i j

@[simp] theorem coeff_add (f g : BiSeries) (i j : ℕ) :
    coeff (f + g) i j = coeff f i j + coeff g i j := by simp [coeff]

@[simp] theorem coeff_smul (z : ℂ) (f : BiSeries) (i j : ℕ) :
    coeff (z • f) i j = z * coeff f i j := by simp [coeff, smul_eq_mul]

theorem coeff_mul (f g : BiSeries) (m n : ℕ) :
    coeff (f * g) m n = conv (coeff f) (coeff g) m n := by
  simp only [coeff, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, map_sum]
  unfold conv
  rw [← Finset.sum_range_reflect (fun i => ∑ j ∈ Finset.range (n + 1),
    PowerSeries.coeff j (PowerSeries.coeff i f) *
      PowerSeries.coeff (n - j) (PowerSeries.coeff (m - i) g)) (m + 1)]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_range_reflect (fun j =>
    PowerSeries.coeff j (PowerSeries.coeff (m - i) f) *
      PowerSeries.coeff (n - j) (PowerSeries.coeff (m - (m - i)) g)) (n + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hi' : i ≤ m := by simpa using hi
  have hj' : j ≤ n := by simpa using hj
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hi', Nat.sub_sub_self hj', coeff]

/-- A single nonnegative majorant constant can always be chosen. -/
theorem joint_bound {c : ℕ → ℕ → ℂ} (hc : JointSubexponential c)
    {r : ℝ} (hr : 1 < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i j, ‖c i j‖ ≤ K * r ^ (i + j) := by
  obtain ⟨K, hK⟩ := hc r hr
  exact ⟨K, (norm_nonneg (c 0 0)).trans (by simpa using hK 0 0), hK⟩

theorem joint_add {f g : ℕ → ℕ → ℂ}
    (hf : JointSubexponential f) (hg : JointSubexponential g) :
    JointSubexponential (fun i j => f i j + g i j) := by
  intro r hr
  obtain ⟨A, hA⟩ := hf r hr
  obtain ⟨B, hB⟩ := hg r hr
  exact ⟨A + B, fun i j => (norm_add_le _ _).trans
    (by simpa [add_mul] using add_le_add (hA i j) (hB i j))⟩

theorem joint_smul (z : ℂ) {f : ℕ → ℕ → ℂ}
    (hf : JointSubexponential f) : JointSubexponential (fun i j => z * f i j) := by
  intro r hr
  obtain ⟨A, hA⟩ := hf r hr
  refine ⟨‖z‖ * A, fun i j => ?_⟩
  simpa [norm_mul, mul_assoc] using mul_le_mul_of_nonneg_left (hA i j) (norm_nonneg z)

/-- Convolution preserves bounds at every rate greater than one. The polynomial
number of terms is absorbed by using the input bounds at the square-root rate. -/
theorem joint_conv {f g : ℕ → ℕ → ℂ}
    (hf : JointSubexponential f) (hg : JointSubexponential g) :
    JointSubexponential (conv f g) := by
  intro r hr
  let s := Real.sqrt r
  have hs : 1 < s := by
    dsimp [s]
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hr
  have hs0 : 0 ≤ s := by linarith
  obtain ⟨A, hA0, hA⟩ := joint_bound hf hs
  obtain ⟨B, hB0, hB⟩ := joint_bound hg hs
  have hp := (subexponential_pow 2).shift 1
  obtain ⟨C, hC⟩ := hp s hs
  have hC0 : 0 ≤ C := by have := hC 0; norm_num at this; linarith
  refine ⟨A * B * C, fun m n => ?_⟩
  have ht : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (n + 1),
      ‖f (m - i) (n - j) * g i j‖ ≤ A * B * s ^ (m + n) := by
    intro i hi j hj
    have hi' : i ≤ m := by simpa using hi
    have hj' : j ≤ n := by simpa using hj
    calc
      _ ≤ (A * s ^ (m - i + (n - j))) * (B * s ^ (i + j)) := by
        rw [norm_mul]
        exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [mul_mul_mul_comm, ← pow_add]
        congr 2
        omega
  calc
    ‖conv f g m n‖ ≤ ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        ‖f (m - i) (n - j) * g i j‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _i ∈ Finset.range (m + 1), ∑ _j ∈ Finset.range (n + 1),
        A * B * s ^ (m + n) := Finset.sum_le_sum fun i hi => Finset.sum_le_sum (ht i hi)
    _ = ((m + 1 : ℝ) * (n + 1)) * (A * B * s ^ (m + n)) := by simp; ring
    _ ≤ ((m + n + 1 : ℝ) ^ 2) * (A * B * s ^ (m + n)) := by
      gcongr
      nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n]
    _ ≤ (C * s ^ (m + n)) * (A * B * s ^ (m + n)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Nat.cast_add, Nat.cast_one] using hC (m + n)
    _ = (A * B * C) * r ^ (m + n) := by
      have he : s * s = r := Real.mul_self_sqrt (by linarith)
      rw [show (C * s ^ (m + n)) * (A * B * s ^ (m + n)) =
        (A * B * C) * (s * s) ^ (m + n) by rw [mul_pow]; ring, he]

/-- Power series convergent throughout the open unit bidisc, in coefficient form. -/
def bidiscAlgebra : Subalgebra ℂ BiSeries where
  carrier := {f | JointSubexponential (coeff f)}
  zero_mem' := by intro r hr; exact ⟨0, by simp [coeff]⟩
  one_mem' := by
    intro r hr
    refine ⟨1, fun i j => ?_⟩
    have hb : ‖coeff (1 : BiSeries) i j‖ ≤ 1 := by
      by_cases hi : i = 0 <;> by_cases hj : j = 0
      all_goals simp [coeff, PowerSeries.coeff_one, hi, hj]
    exact hb.trans (by simpa only [one_mul] using one_le_pow₀ hr.le (n := i + j))
  add_mem' := by intro f g hf hg; simpa using joint_add hf hg
  mul_mem' := by
    intro f g hf hg
    change JointSubexponential (coeff (f * g))
    have he : coeff (f * g) = conv (coeff f) (coeff g) :=
      funext fun i => funext fun j => coeff_mul f g i j
    rw [he]
    exact joint_conv hf hg
  algebraMap_mem' := by
    intro z r hr
    refine ⟨‖z‖, fun i j => ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    rw [coeff_smul, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
    have hb : ‖coeff (1 : BiSeries) i j‖ ≤ 1 := by
      by_cases hi : i = 0 <;> by_cases hj : j = 0
      all_goals simp [coeff, PowerSeries.coeff_one, hi, hj]
    exact hb.trans (one_le_pow₀ hr.le)

/-- No division is needed to propagate product-chart regularity through the
finite coefficient algebra used by the coinvariant quotient. -/
theorem coefficientAlgebra_le_bidisc (g : Fin 4 → BiSeries)
    (hg : ∀ k, JointSubexponential (coeff (g k))) :
    QEquation.coefficientAlgebra g ≤ bidiscAlgebra := by
  apply Algebra.adjoin_le
  rintro f ⟨k, rfl⟩
  exact hg k

/-- A finite family has one geometric constant, common to both equations. -/
theorem finite_family_bound {ι : Type*} (s : Finset ι) (g : ι → BiSeries)
    (hg : ∀ k ∈ s, g k ∈ bidiscAlgebra) {r : ℝ} (hr : 1 < r) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ k ∈ s, ∀ i j, ‖coeff (g k) i j‖ ≤ G * r ^ i * r ^ j := by
  classical
  have hb : ∀ k ∈ s, ∃ K : ℝ, 0 ≤ K ∧ ∀ i j, ‖coeff (g k) i j‖ ≤ K * r ^ (i + j) :=
    fun k hk => joint_bound (hg k hk) hr
  choose K hK0 hK using hb
  let G := ∑ k ∈ s.attach, K k.val k.property
  refine ⟨G, Finset.sum_nonneg (fun k _ => hK0 k.val k.property), fun k hk i j => ?_⟩
  have hKG : K k hk ≤ G :=
    Finset.single_le_sum (fun a _ => hK0 a.val a.property) (Finset.mem_attach s ⟨k, hk⟩)
  exact (hK k hk i j).trans (by
    simpa [pow_add, mul_assoc] using
      mul_le_mul_of_nonneg_right hKG (pow_nonneg (show 0 ≤ r by linarith) (i + j)))

end VOA.Huang.GenusTwoPoint.Separate
