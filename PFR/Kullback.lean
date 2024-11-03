import PFR.ForMathlib.FiniteRange.Defs
import Mathlib.Probability.IdentDistrib
import PFR.ForMathlib.Entropy.Basic
import PFR.Mathlib.Analysis.SpecialFunctions.NegMulLog

/-!
# Kullback-Leibler divergence

Definition of Kullback-Leibler divergence and basic facts
-/

open MeasureTheory ProbabilityTheory Real

variable {Ω Ω' Ω'' Ω''' G: Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G] -- [MeasurableSingletonClass G]

variable {X : Ω → G} {Y : Ω' → G} -- [FiniteRange X] [FiniteRange Y]

-- one should add somewhere the hypotheses that μ, μ', and μ'' are all probability measures

/-- If `X, Y` are two `G`-valued random variables, the Kullback--Leibler divergence is defined as
  `KL(X ‖ Y) := ∑ₓ 𝐏(X = x) log (𝐏(X = x) / 𝐏(Y = x))`.

Note that due to Lean conventions with junk values, this definition only makes sense when
`X` is absolutely continuous wrt to `Y`, i.e., `∀ x, 𝐏(Y = x) = 0 → 𝐏(X = x) = 0`. Otherwise, the
divergence should be infinite, but since we use real numbers for ease of computations, this is
not a possible choice.
  -/
noncomputable def KL_div (X : Ω → G) (Y: Ω' → G) (μ : Measure Ω := by volume_tac)
    (μ' : Measure Ω' := by volume_tac) : ℝ :=
  ∑' x, (μ.map X {x}).toReal * log ((μ.map X {x}).toReal / (μ'.map Y {x}).toReal)

@[inherit_doc KL_div] notation3:max "KL[" X " ; " μ " # " Y " ; " μ' "]" => KL_div X Y μ μ'

@[inherit_doc KL_div] notation3:max "KL[" X " # " Y "]" => KL_div X Y volume volume

/-- If `X'` is a copy of `X`, and `Y'` is a copy of `Y`, then `KL(X' ‖ Y') = KL(X ‖ Y)`. -/
lemma KL_div_eq_of_equiv (X' : Ω'' → G) (Y' : Ω''' → G)
    (hX : IdentDistrib X X' μ μ'') (hY : IdentDistrib Y Y' μ' μ''') :
    KL[X ; μ # Y ; μ'] = KL[X' ; μ'' # Y' ; μ'''] := by
  simp only [KL_div]
  congr with x
  congr
  · exact hX.map_eq
  · exact hX.map_eq
  · exact hY.map_eq

lemma KL_div_eq_sum [Fintype G] :
    KL[X ; μ # Y ; μ'] = ∑ x,
      (μ.map X {x}).toReal * log ((μ.map X {x}).toReal / (μ'.map Y {x}).toReal) :=
  tsum_eq_sum (by simp)

/-- `KL(X ‖ Y) ≥ 0`.-/
lemma KL_div_nonneg [Fintype G] [MeasurableSingletonClass G] [IsZeroOrProbabilityMeasure μ]
    [IsZeroOrProbabilityMeasure μ'] (hX : Measurable X) (hY : Measurable Y)
    (habs : ∀ x, μ'.map Y {x} = 0 → μ.map X {x} = 0) : 0 ≤ KL[X ; μ # Y ; μ'] := by
  rw [KL_div_eq_sum]
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ' with rfl | hμ'
  · simp
  apply le_trans ?_ (sum_mul_log_div_leq (by simp) (by simp) ?_)
  · have : IsProbabilityMeasure (μ'.map Y) := isProbabilityMeasure_map hY.aemeasurable
    have : IsProbabilityMeasure (μ.map X) := isProbabilityMeasure_map hX.aemeasurable
    simp
  · intro i _ hi
    simp only [ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false] at hi
    simp [habs i hi]

/-- `KL(X ‖ Y) = 0` if and only if `Y` is a copy of `X`. -/
lemma KL_div_eq_zero_iff_identDistrib [Fintype G] [MeasurableSingletonClass G]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (hX : Measurable X) (hY : Measurable Y)
    (habs : ∀ x, μ'.map Y {x} = 0 → μ.map X {x} = 0) :
    KL[X ; μ # Y ; μ'] = 0 ↔ IdentDistrib X Y μ μ' := by
  have L (x : ℝ) : log (x / x) = 0 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · simp [hx]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [KL_div, h.map_eq, L]⟩
  let νY := μ'.map Y
  have : IsProbabilityMeasure νY := isProbabilityMeasure_map hY.aemeasurable
  let νX := μ.map X
  have : IsProbabilityMeasure νX := isProbabilityMeasure_map hX.aemeasurable
  obtain ⟨r, hr⟩ : ∃ (r : ℝ), ∀ x ∈ Finset.univ, (νX {x}).toReal = r * (νY {x}).toReal := by
    apply sum_mul_log_div_eq_iff (by simp) (by simp) (fun i _ hi ↦ ?_)
    · rw [KL_div_eq_sum] at h
      simpa using h
    · simp only [ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false] at hi
      simp [habs i hi]
  have r_eq : r = 1 := by
    have : r * ∑ x, (νY {x}).toReal = ∑ x, (νX {x}).toReal := by
      simp only [Finset.mul_sum, Finset.mem_univ, hr]
    simpa using this
  have : νX = νY := by
    apply Measure.ext_iff_singleton.mpr (fun x ↦ ?_)
    simpa [r_eq, ENNReal.toReal_eq_toReal] using hr x (Finset.mem_univ _)
  exact ⟨hX.aemeasurable, hY.aemeasurable, this⟩

/-- If $S$ is a finite set, $w_s$ is non-negative,
and ${\bf P}(X=x) = \sum_{s\in S} w_s {\bf P}(X_s=x)$, ${\bf P}(Y=x) =
  \sum_{s\in S} w_s {\bf P}(Y_s=x)$ for all $x$, then
$$D_{KL}(X\Vert Y) \le \sum_{s\in S} w_s D_{KL}(X_s\Vert Y_s).$$ -/
lemma KL_div_of_convex [Fintype G] [IsFiniteMeasure μ''']
    {ι : Type*} {S : Finset ι} {w : ι → ℝ} (hw : ∀ s ∈ S, 0 ≤ w s)
    (X' : ι → Ω'' → G) (Y' : ι → Ω''' → G)
    (hconvex : ∀ x, (μ.map X {x}).toReal = ∑ s ∈ S, (w s) * (μ''.map (X' s) {x}).toReal)
    (hconvex' : ∀ x, (μ'.map Y {x}).toReal = ∑ s ∈ S, (w s) * (μ'''.map (Y' s) {x}).toReal)
    (habs : ∀ s ∈ S, ∀ x, μ'''.map (Y' s) {x} = 0 → μ''.map (X' s) {x} = 0) :
    KL[X ; μ # Y ; μ'] ≤ ∑ s ∈ S, w s * KL[X' s ; μ'' # Y' s ; μ'''] := by
  conv_lhs => rw [KL_div_eq_sum]
  have A x : (μ.map X {x}).toReal * log ((μ.map X {x}).toReal / (μ'.map Y {x}).toReal)
    ≤ ∑ s ∈ S, (w s * (μ''.map (X' s) {x}).toReal) *
        log ((w s * (μ''.map (X' s) {x}).toReal) / (w s * (μ'''.map (Y' s) {x}).toReal)) := by
    rw [hconvex, hconvex']
    apply sum_mul_log_div_leq (fun s hs ↦ ?_) (fun s hs ↦ ?_) (fun s hs h's ↦ ?_)
    · exact mul_nonneg (by simp [hw s hs]) (by simp)
    · exact mul_nonneg (by simp [hw s hs]) (by simp)
    · rcases mul_eq_zero.1 h's with h | h
      · simp [h]
      · simp only [ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false] at h
        simp [habs s hs x h]
  have B x : (μ.map X {x}).toReal * log ((μ.map X {x}).toReal / (μ'.map Y {x}).toReal)
    ≤ ∑ s ∈ S, (w s * (μ''.map (X' s) {x}).toReal) *
        log ((μ''.map (X' s) {x}).toReal / (μ'''.map (Y' s) {x}).toReal) := by
    apply (A x).trans_eq
    apply Finset.sum_congr rfl (fun s _ ↦ ?_)
    rcases eq_or_ne (w s) 0 with h's | h's
    · simp [h's]
    · congr 2
      rw [mul_div_mul_left _ _ h's]
  apply (Finset.sum_le_sum (fun x _ ↦ B x)).trans_eq
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, KL_div_eq_sum]

/-- If $f:G \to H$ is an injection, then $D_{KL}(f(X)\Vert f(Y)) = D_{KL}(X\Vert Y)$. -/
lemma KL_div_of_comp_inj {H : Type*} [MeasurableSpace H] [DiscreteMeasurableSpace G]
    [MeasurableSingletonClass H] {f : G → H}
    (hf : Function.Injective f) (hX : Measurable X) (hY : Measurable Y) :
    KL[f ∘ X ; μ # f ∘ Y ; μ'] = KL[X ; μ # Y ; μ'] := by
  simp only [KL_div]
  rw [← hf.tsum_eq]
  · symm
    congr with x
    have : (Measure.map X μ) {x} = (Measure.map (f ∘ X) μ) {f x} := by
      rw [Measure.map_apply, Measure.map_apply]
      · congr
        exact Set.Subset.antisymm (fun ⦃a⦄ ↦ congrArg f) fun ⦃a⦄ a_1 ↦ hf a_1
      · exact Measurable.of_discrete.comp hX
      · exact measurableSet_singleton (f x)
      · exact hX
      · exact measurableSet_singleton x
    have :  (Measure.map Y μ') {x} = (Measure.map (f ∘ Y) μ') {f x} := by
      rw [Measure.map_apply, Measure.map_apply]
      · congr
        exact Set.Subset.antisymm (fun ⦃a⦄ ↦ congrArg f) fun ⦃a⦄ a_1 ↦ hf a_1
      · exact Measurable.of_discrete.comp hY
      · exact measurableSet_singleton (f x)
      · exact hY
      · exact measurableSet_singleton x
    congr
  · intro y hy
    have : Measure.map (f ∘ X) μ {y} ≠ 0 := by
      intro h
      simp [h] at hy
    rw [Measure.map_apply (Measurable.of_discrete.comp hX) (measurableSet_singleton y)] at this
    have : f ∘ X ⁻¹' {y} ≠ ∅ := by
      intro h
      simp [h] at this
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.2 this
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff] at hz
    exact Set.mem_range.2 ⟨X z, hz⟩

open Set

open scoped Pointwise

/-- The distribution of `X + Z` is the convolution of the distributions of `Z` and `X` when these
random variables are independent.
Probably already available somewhere in some form, but I couldn't locate it. -/
lemma ProbabilityTheory.IndepFun.map_add_eq_sum
    [Fintype G] [AddCommGroup G] [DiscreteMeasurableSpace G]
    {X Z : Ω → G} (hindep : IndepFun X Z μ)
    (hX : Measurable X) (hZ : Measurable Z) (S : Set G) :
    μ.map (X + Z) S = ∑ s, μ.map Z {s} * μ.map X ({-s} + S) := by
  rw [Measure.map_apply (by fun_prop) (DiscreteMeasurableSpace.forall_measurableSet S)]
  have : (X + Z) ⁻¹' S = ⋃ s, X ⁻¹' ({-s} + S) ∩ Z ⁻¹' {s} := by
    apply Subset.antisymm
    · intro y hy
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff, exists_and_left,
        exists_prop]
      simp at hy
      exact ⟨Z y, by simpa [add_comm] using hy, rfl⟩
    · simp only [iUnion_subset_iff]
      intro i y hy
      simp only [singleton_add, image_add_left, neg_neg, mem_inter_iff, mem_preimage,
        mem_singleton_iff] at hy
      simp [hy.1, hy.2, add_comm]
  rw [this, measure_iUnion, tsum_fintype]; rotate_left
  · intro i j hij
    simp [Function.onFun]
    apply Disjoint.inter_left'
    apply Disjoint.inter_right'
    apply disjoint_left.2 (fun a ha hb ↦ ?_)
    simp [← neg_eq_iff_eq_neg] at ha hb
    rw [← ha, ← hb] at hij
    exact hij rfl
  · intro i
    exact (hX (DiscreteMeasurableSpace.forall_measurableSet _)).inter (hZ (measurableSet_singleton _))
  congr with i
  rw [hindep.measure_inter_preimage_eq_mul _ _ (DiscreteMeasurableSpace.forall_measurableSet _)
    (measurableSet_singleton _), mul_comm,
    Measure.map_apply hZ (measurableSet_singleton _),
    Measure.map_apply hX (DiscreteMeasurableSpace.forall_measurableSet _)]

/-- The distribution of `X + Z` is the convolution of the distributions of `Z` and `X` when these
random variables are independent.
Probably already available somewhere in some form, but I couldn't locate it. -/
lemma ProbabilityTheory.IndepFun.map_add_singleton_eq_sum
    [Fintype G] [AddCommGroup G] [DiscreteMeasurableSpace G]
    {X Z : Ω → G} (hindep : IndepFun X Z μ)
    (hX : Measurable X) (hZ : Measurable Z) (x : G) :
    μ.map (X + Z) {x} = ∑ s, μ.map Z {s} * μ.map X {x - s} := by
  rw [hindep.map_add_eq_sum hX hZ]
  congr with s
  congr
  simp
  abel

/-- If $X, Y, Z$ are independent $G$-valued random variables, then
  $$D_{KL}(X+Z\Vert Y+Z) \leq D_{KL}(X\Vert Y).$$ -/
lemma KL_div_add_le_KL_div_of_indep [Fintype G] [AddCommGroup G] [DiscreteMeasurableSpace G]
    {X Y Z : Ω → G} [IsZeroOrProbabilityMeasure μ]
    (hindep : IndepFun (⟨X, Y⟩) Z μ)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (habs : ∀ x, μ.map Y {x} = 0 → μ.map X {x} = 0) :
    KL[X + Z ; μ # Y + Z ; μ] ≤ KL[X ; μ # Y ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [KL_div]
  set X' : G → Ω → G := fun s ↦ (· + s) ∘ X with hX'
  set Y' : G → Ω → G := fun s ↦ (· + s) ∘ Y with hY'
  have AX' x i : μ.map (X' i) {x} = μ.map X {x - i} := by
    rw [hX', ← Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
    congr
    ext y
    simp [sub_eq_add_neg]
  have AY' x i : μ.map (Y' i) {x} = μ.map Y {x - i} := by
    rw [hY', ← Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
    congr
    ext y
    simp [sub_eq_add_neg]
  let w : G → ℝ := fun s ↦ (μ.map Z {s}).toReal
  let S : Finset G := Finset.univ
  have sum_w : ∑ s, w s = 1 := by
    have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
    simp [w]
  have A x : (μ.map (X + Z) {x}).toReal = ∑ s ∈ S, w s * (μ.map (X' s) {x}).toReal := by
    have : IndepFun X Z μ := hindep.comp (φ := Prod.fst) (ψ := id) measurable_fst measurable_id
    rw [this.map_add_singleton_eq_sum hX hZ, ENNReal.toReal_sum (by simp [ENNReal.mul_eq_top])]
    simp only [ENNReal.toReal_mul]
    congr with i
    congr 1
    rw [AX']
  have B x : (μ.map (Y + Z) {x}).toReal = ∑ s ∈ S, w s * (μ.map (Y' s) {x}).toReal := by
    have : IndepFun Y Z μ := hindep.comp (φ := Prod.snd) (ψ := id) measurable_snd measurable_id
    rw [this.map_add_singleton_eq_sum hY hZ, ENNReal.toReal_sum (by simp [ENNReal.mul_eq_top])]
    simp only [ENNReal.toReal_mul]
    congr with i
    congr 1
    rw [AY']
  have : KL[X + Z ; μ # Y + Z; μ] ≤ ∑ s ∈ S, w s * KL[X' s ; μ # Y' s ; μ] := by
    apply KL_div_of_convex (fun s _ ↦ by simp [w])
    · exact A
    · exact B
    · intro s _ x
      rw [AX', AY']
      exact habs _
  apply this.trans_eq
  have C s : KL[X' s ; μ # Y' s ; μ] = KL[X ; μ # Y ; μ] :=
    KL_div_of_comp_inj (add_left_injective s) hX hY
  simp_rw [C, ← Finset.sum_mul, sum_w, one_mul]

/-- If $X,Y,Z$ are random variables, with $X,Z$ defined on the same sample space, we define
$$ D_{KL}(X|Z \Vert Y) := \sum_z \mathbf{P}(Z=z) D_{KL}( (X|Z=z) \Vert Y).$$ -/
noncomputable def condKL_div {S: Type*} (X : Ω → G) (Y : Ω' → G) (Z : Ω → S)
    (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) : ℝ :=
  ∑' z, (μ (Z⁻¹' {z})).toReal * KL[X ; (ProbabilityTheory.cond μ (Z⁻¹' {z})) # Y ; μ']

@[inherit_doc condKL_div]
notation3:max "KL[" X " | " Z " ; " μ " # " Y " ; " μ' "]" => condKL_div X Y Z μ μ'

@[inherit_doc condKL_div]
notation3:max "KL[" X " | " Z " # " Y "]" => condKL_div X Y Z volume volume

/-- If $X, Y$ are independent $G$-valued random variables, and $Z$ is another random variable
  defined on the same sample space as $X$, then
  $$D_{KL}((X|Z)\Vert Y) = D_{KL}(X\Vert Y) + \bbH[X] - \bbH[X|Z].$$ -/
lemma condKL_div_eq {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    [Fintype G] [MeasurableSingletonClass G]
    {X : Ω → G} {Y : Ω' → G} {Z : Ω → S}
    [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    KL[ X | Z; μ # Y ; μ'] = KL[X ; μ # Y ; μ'] + H[X ; μ] - H[ X | Z ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [condKL_div, tsum_fintype, KL_div_eq_sum, Finset.mul_sum, entropy_eq_sum]
  simp only [condKL_div, tsum_fintype, KL_div_eq_sum, Finset.mul_sum, entropy_eq_sum]
  rw [Finset.sum_comm, condEntropy_eq_sum_sum hX hZ]
  simp only [negMulLog, neg_mul, Finset.sum_neg_distrib, mul_neg, sub_neg_eq_add]
  sorry

/-- `KL(X|Z ‖ Y) ≥ 0`.-/
lemma condKL_div_nonneg {S : Type*} [MeasurableSingletonClass G] [Fintype G]
    {X : Ω → G} {Y : Ω' → G} {Z : Ω → S}
    [IsZeroOrProbabilityMeasure μ']
    (hX : Measurable X) (hY : Measurable Y)
    (habs : ∀ x, μ'.map Y {x} = 0 → μ.map X {x} = 0) :
    0 ≤ KL[X | Z; μ # Y ; μ'] := by
  rw [condKL_div]
  refine tsum_nonneg (fun i ↦ mul_nonneg (by simp) ?_)
  apply KL_div_nonneg hX hY
  intro s hs
  specialize habs s hs
  rw [Measure.map_apply hX (measurableSet_singleton s)] at habs ⊢
  exact cond_absolutelyContinuous habs
