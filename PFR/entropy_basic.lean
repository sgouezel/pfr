import Mathlib.Data.Prod.TProd
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.IdentDistrib
import PFR.Entropy.KernelMutualInformation
import PFR.ForMathlib.Independence

/-!
# Entropy and conditional entropy

## Main definitions

* `entropy`: entropy of a random variable, defined as `measureEntropy (volume.map X)`
* `condEntropy`: conditional entropy of a random variable `X` w.r.t. another one `Y`
* `mutualInformation`: mutual information of two random variables

## Main statements

* `chain_rule`: $H[⟨ X, Y ⟩] = H[Y] + H[X | Y]$
* `entropy_cond_le_entropy`: $H[X | Y] ≤ H[X]$. (Chain rule another way.)
* `entropy_triple_add_entropy_le`: $H[X, Y, Z] + H[Z] ≤ H[X,Z] + H[Y,Z]$. (Submodularity of entropy.)

## Notations

* `H[X] = entropy X`
* `H[X | Y ← y] = Hm[(ℙ[| Y ⁻¹' {y}]).map X]`
* `H[X | Y] = condEntropy X Y`, such that `H[X | Y] = (volume.map Y)[fun y ↦ H[X | Y ← y]]`
* `I[X : Y] = mutualInformation X Y`

All notations have variants where we can specify the measure (which is otherwise
supposed to be `volume`). For example `H[X ; μ]` and `I[X : Y ; μ]` instead of `H[X]` and
`I[X : Y]` respectively.

-/

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

/-- Give all finite types the discrete sigma-algebra by default. -/
instance Fintype.instMeasurableSpace [Fintype S] : MeasurableSpace S := ⊤

namespace ProbabilityTheory

variable {Ω S T U: Type*} [mΩ : MeasurableSpace Ω]
  [Fintype S] [Fintype T] [Fintype U]
  [Nonempty S] [Nonempty T] [Nonempty U]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  {μ : Measure Ω}

section entropy

/-- Entropy of a random variable with values in a finite measurable space. -/
noncomputable
def entropy (X : Ω → S) (μ : Measure Ω := by volume_tac) := Hm[μ.map X]

notation3:max "H[" X "; " μ "]" => entropy X μ
notation3:max "H[" X "]" => entropy X volume
notation3:max "H[" X "|" Y "←" y "; " μ "]" => entropy X (μ[|Y ⁻¹' {y}])
notation3:max "H[" X "|" Y "←" y "]" => entropy X (ℙ[|Y ⁻¹' {y}])

/-- Entropy of a random variable agrees with entropy of its distribution. -/
lemma entropy_def (X : Ω → S) (μ : Measure Ω) : entropy X μ = Hm[μ.map X] := rfl

/-- Entropy of a random variable is also the kernel entropy of the distribution over a Dirac mass. -/
lemma entropy_eq_kernel_entropy (X : Ω → S) (μ : Measure Ω) :
    H[X ; μ] = Hk[kernel.const Unit (μ.map X), Measure.dirac ()] := by
  simp only [kernel.entropy, kernel.const_apply, integral_const, MeasurableSpace.measurableSet_top,
    Measure.dirac_apply', Set.mem_univ, Set.indicator_of_mem, Pi.one_apply, ENNReal.one_toReal,
    smul_eq_mul, one_mul]
  rfl

/-- Any variable on a zero measure space has zero entropy. -/
@[simp]
lemma entropy_zero_measure (X : Ω → S) : H[X ; (0 : Measure Ω)] = 0 := by simp [entropy]

/-- Two variables that agree almost everywhere, have the same entropy. -/
lemma entropy_congr {X X' : Ω → S} (h : X =ᵐ[μ] X') : H[X ; μ] = H[X' ; μ] := by
  rw [entropy_def, Measure.map_congr h, entropy_def]

/-- Entropy is always non-negative. -/
lemma entropy_nonneg (X : Ω → S) (μ : Measure Ω) : 0 ≤ entropy X μ := measureEntropy_nonneg _

/-- Two variables that have the same distribution, have the same entropy. -/
lemma IdentDistrib.entropy_eq {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} {X' : Ω' → S}
    (h : IdentDistrib X X' μ μ') : entropy X μ = entropy X' μ' := by
  simp [entropy_def, h.map_eq]

/-- Entropy is at most the logarithm of the cardinality of the range. -/
lemma entropy_le_log_card
    (X : Ω → S) (μ : Measure Ω) : entropy X μ ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card _

/-- $H[X] = \sum_s P[X=s] \log \frac{1}{P[X=s]}$. -/
lemma entropy_eq_sum (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    entropy X μ = ∑ x, negIdMulLog (μ.map X {x}).toReal := by
  have : IsProbabilityMeasure (Measure.map X μ) := isProbabilityMeasure_map hX.aemeasurable
  rw [entropy_def, measureEntropy_of_isProbabilityMeasure]

/-- $H[X|Y=y] = \sum_s P[X=s|Y=y] \log \frac{1}{P[X=s|Y=y]}$. -/
lemma entropy_cond_eq_sum (hX : Measurable X) (μ : Measure Ω) [IsProbabilityMeasure μ] (y : T) :
    H[X | Y ← y ; μ] = ∑ x, negIdMulLog ((μ[|Y ⁻¹' {y}]).map X {x}).toReal := by
  by_cases hy : μ (Y ⁻¹' {y}) = 0
  · rw [entropy_def, cond_eq_zero_of_measure_zero hy]
    simp
  · have : IsProbabilityMeasure (μ[|Y ⁻¹' {y}]) := cond_isProbabilityMeasure _ hy
    rw [entropy_eq_sum hX]

/-- If $X$, $Y$ are $S$-valued and $T$-valued random variables, and $Y = f(X)$ for
some injection $f: S \to T$, then $H[Y] = H[X]$. One can also use `entropy_of_comp_eq_of_comp` as an alternative if verifying injectivity is fiddly.  For the upper bound only, see `entropy_comp_le`. -/
lemma entropy_comp_of_injective
    (μ : Measure Ω) (hX : Measurable X) (f : S → T) (hf : Function.Injective f) :
    H[f ∘ X ; μ] = H[X ; μ] := by
  have hf_m : Measurable f := measurable_of_finite f
  rw [entropy_def, ← Measure.map_map hf_m hX, measureEntropy_map_of_injective _ _ hf,
    entropy_def]

/-- The assertion that the law of $X$ is the uniform probability measure on a finite set $H$.  While in applications $H$ will be non-empty finite set, $X$ measurable, and and $μ$ a probability measure, it could be technically convenient to have a definition that works even without these hypotheses.  (For instance, isUniform would be well-defined, but false, for infinite H)   -/
def isUniform (H: Set S) (X : Ω → S) (μ : Measure Ω := by volume_tac) : Prop := sorry

/-- Uniform distributions exist.   -/
lemma exists_uniform (H : Finset S) [h: Nonempty H] : ∃ Ω : Type*, ∃ mΩ : MeasurableSpace Ω, ∃ X : Ω → S, ∃ μ: Measure Ω, IsProbabilityMeasure μ ∧ Measurable X ∧ isUniform H X μ ∧ ∀ ω : Ω, X ω ∈ H := by sorry

/-- A "unit test" for the definition of uniform distribution. -/
lemma prob_of_uniform_of_in (H: Finset S) (X : Ω → S) (μ : Measure Ω) (hX : isUniform H X μ) (s : S) (hs: s ∈ H): μ.map X {s} = (μ Set.univ) / (Fintype.card H) := sorry

/-- Another "unit test" for the definition of uniform distribution. -/
lemma prob_of_uniform_of_not_in (H: Finset S) (X : Ω → S) (μ : Measure Ω) (hX : isUniform H X μ) (s : S) (hs: ¬ s ∈ H): μ.map X {s} = 0 := sorry




/-- If $X$ is uniformly distributed on $H$, then $H[X] = \log |H|$.  May need some non-degeneracy and measurability conditions. -/
lemma entropy_of_uniform (H: Finset S) (X : Ω → S) (μ : Measure Ω) (hX : isUniform H X μ) :
    H[X ; μ] = log (Fintype.card H) := sorry

/-- If $X$ is $S$-valued random variable, then $H[X] = \log |S|$ if and only if $X$ is uniformly
distributed. -/
lemma entropy_eq_log_card {X : Ω → S} (hX : Measurable X) (μ : Measure Ω) (hμ: NeZero μ) (hμ' : IsFiniteMeasure μ): (entropy X μ = log (Fintype.card S)) ↔ (∀ s : S, μ.map X {s} = (μ Set.univ) / (Fintype.card S)) := by
  rcases eq_zero_or_neZero (μ.map X) with h | h
  . have := Measure.le_map_apply  (@Measurable.aemeasurable Ω S _ _ X μ hX) Set.univ
    simp [h] at this; simp [this] at hμ
  have : IsFiniteMeasure (μ.map X) := by
    apply Measure.isFiniteMeasure_map
  rw [entropy_def, measureEntropy_eq_card_iff_measure_eq, Measure.map_apply hX MeasurableSet.univ]
  simp

/-- If $X$ is an $S$-valued random variable, then there exists $s \in S$ such that
$P[X=s] \geq \exp(-H[X])$. -/
lemma prob_ge_exp_neg_entropy (X : Ω → S) (μ : Measure Ω) : ∃ s : S, μ.map X {s} ≥ (μ Set.univ) * (rexp (- entropy X μ )).toNNReal := by sorry

abbrev prod {Ω S T : Type*} ( X : Ω → S ) ( Y : Ω → T ) (ω : Ω) : S × T := (X ω, Y ω)

notation3:100 "⟨" X ", " Y "⟩" => prod X Y

/-- $H[X,Y] = H[Y,X]$. -/
lemma entropy_comm
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨ X, Y ⟩; μ] = H[⟨ Y, X ⟩ ; μ] := by
  change H[⟨ X, Y ⟩ ; μ] = H[Prod.swap ∘ ⟨ X, Y ⟩ ; μ]
  exact (entropy_comp_of_injective μ (hX.prod_mk hY) Prod.swap Prod.swap_injective).symm

/-- $H[(X,Y),Z] = H[X,(Y,Z)]$. -/
lemma entropy_assoc [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) :
    H[⟨ X, ⟨ Y, Z ⟩ ⟩; μ] = H[⟨ ⟨X, Y⟩ , Z ⟩ ; μ] := by
  change H[⟨ X, ⟨ Y, Z ⟩ ⟩ ; μ] = H[(Equiv.prodAssoc _ _ _).symm ∘ ⟨ X, ⟨ Y, Z ⟩ ⟩ ; μ]
  exact entropy_comp_of_injective μ (hX.prod_mk (hY.prod_mk hZ)) _
    (Equiv.prodAssoc S T U).symm.injective |>.symm

variable [AddGroup S] in
/-- $H[X,X+Y] = H[X,Y]$. -/
lemma entropy_add_right {Y : Ω → S}
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨ X, X + Y ⟩; μ] = H[⟨ X, Y ⟩ ; μ] := by
  change H[(Equiv.refl _).prodShear Equiv.addLeft ∘ ⟨ X, Y ⟩ ; μ] = H[⟨ X, Y ⟩ ; μ]
  exact entropy_comp_of_injective μ (hX.prod_mk hY) _ (Equiv.injective _)

end entropy

section condEntropy

variable {X : Ω → S} {Y : Ω → T}

/-- Conditional entropy of a random variable w.r.t. another.
This is the expectation under the law of `Y` of the entropy of the law of `X` conditioned on the
event `Y = y`. -/
noncomputable
def condEntropy (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  (μ.map Y)[fun y ↦ H[X | Y ← y ; μ]]

lemma condEntropy_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    condEntropy X Y μ = (μ.map Y)[fun y ↦ H[X | Y ← y ; μ]] := rfl

notation3:max "H[" X "|" Y "; " μ "]" => condEntropy X Y μ
notation3:max "H[" X "|" Y "]" => condEntropy X Y volume

/-- Conditional entropy of a random variable is equal to the entropy of its conditional kernel. -/
lemma condEntropy_eq_kernel_entropy
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] :
    H[X | Y ; μ] = Hk[condEntropyKernel X Y μ, μ.map Y] := by
  rw [condEntropy_def, kernel.entropy]
  simp_rw [integral_eq_sum]
  congr with t
  by_cases ht : (μ.map Y {t}).toReal = 0
  · simp [ht]
  simp only [ENNReal.toReal_eq_zero_iff, measure_ne_top (μ.map Y), or_false] at ht
  rw [Measure.map_apply hY (measurableSet_singleton _)] at ht
  simp only [entropy_def]
  congr
  ext S hS
  rw [condEntropyKernel_apply' hX hY _ _ ht hS, Measure.map_apply hX hS,
      cond_apply _ (hY (measurableSet_singleton _))]

lemma map_prod_comap_swap (hX : Measurable X) (hZ : Measurable Z) (μ : Measure Ω) :
    (μ.map (fun ω ↦ (X ω, Z ω))).comap Prod.swap = μ.map (fun ω ↦ (Z ω, X ω)) := by
  ext s hs
  rw [Measure.map_apply (hZ.prod_mk hX) hs, Measure.comap_apply _ Prod.swap_injective _ _ hs]
  · rw [Measure.map_apply (hX.prod_mk hZ)]
    · congr with ω
      simp only [Set.image_swap_eq_preimage_swap, Set.mem_preimage, Prod.swap_prod_mk]
    · exact MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' hs
  · exact fun t ht ↦ MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' ht

lemma condEntropy_two_eq_kernel_entropy
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    H[X | ⟨ Y, Z ⟩ ; μ] =
      Hk[kernel.condKernel (condEntropyKernel (fun a ↦ (Y a, X a)) Z μ) ,
        Measure.map Z μ ⊗ₘ kernel.fst (condEntropyKernel (fun a ↦ (Y a, X a)) Z μ)] := by
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  have := isMarkovKernel_condEntropyKernel (hY.prod_mk hX) hZ μ
  have := isMarkovKernel_condEntropyKernel hY hZ μ
  rw [Measure.compProd_congr (condEntropyKernel_fst_ae_eq hY hX hZ μ),
      map_compProd_condEntropyKernel hY hZ,
      kernel.entropy_congr (condKernel_condEntropyKernel_ae_eq hY hX hZ μ),
      ← kernel.entropy_congr (swap_condEntropyKernel_ae_eq hY hX hZ μ)]
  have : μ.map (fun ω ↦ (Z ω, Y ω)) = (μ.map (fun ω ↦ (Y ω, Z ω))).comap Prod.swap := by
    rw [map_prod_comap_swap hY hZ]
  rw [this, condEntropy_eq_kernel_entropy hX (hY.prod_mk hZ), kernel.entropy_comap_swap]

/-- Any random variable on a zero measure space has zero conditional entropy. -/
@[simp]
lemma condEntropy_zero_measure (X : Ω → S) (Y : Ω → T) : H[X | Y ; (0 : Measure Ω)] = 0 :=
  by simp [condEntropy]

/-- Conditional entropy is non-negative. -/
lemma condEntropy_nonneg (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : 0 ≤ H[X | Y ; μ] :=
  integral_nonneg (fun _ ↦ measureEntropy_nonneg _)

/-- Conditional entropy is at most the logarithm of the cardinality of the range. -/
lemma condEntropy_le_log_card [MeasurableSingletonClass S]
    (X : Ω → S) (Y : Ω → T) (hY : Measurable Y) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    H[X | Y ; μ] ≤ log (Fintype.card S) := by
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ entropy_nonneg _ _)
  · exact ae_of_all _ (fun _ ↦ entropy_le_log_card _ _)
  · have : IsProbabilityMeasure (μ.map Y) := isProbabilityMeasure_map hY.aemeasurable
    simp

/-- $H[X|Y] = \sum_y P[Y=y] H[X|Y=y]$.-/
lemma condEntropy_eq_sum [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    H[X | Y ; μ] = ∑ y, (μ.map Y {y}).toReal * H[X | Y ← y ; μ] := by
  rw [condEntropy_def, integral_eq_sum]
  simp_rw [smul_eq_mul]

/-- $H[X|Y] = \sum_y \sum_x P[Y=y] P[X=x|Y=y] log ¼{1}{P[X=x|Y=y]$}.-/
lemma condEntropy_eq_sum_sum [MeasurableSingletonClass T] (hX : Measurable X) (Y : Ω → T)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    H[X | Y ; μ]
      = ∑ y, ∑ x, (μ.map Y {y}).toReal * negIdMulLog ((μ[|Y ⁻¹' {y}]).map X {x}).toReal := by
  rw [condEntropy_eq_sum]
  congr with y
  rw [entropy_cond_eq_sum hX, Finset.mul_sum]

/-- Same as previous lemma, but with a sum over a product space rather than a double sum. -/
lemma condEntropy_eq_sum_prod [MeasurableSingletonClass T] (hX : Measurable X) (Y : Ω → T)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    H[X | Y ; μ] = ∑ p : S × T,
      (μ.map Y {p.2}).toReal * negIdMulLog ((μ[|Y ⁻¹' {p.2}]).map X {p.1}).toReal := by
  have h_prod : (Finset.univ : Finset (S × T)) = (Finset.univ : Finset S) ×ˢ Finset.univ := rfl
  rw [condEntropy_eq_sum_sum hX Y, h_prod, Finset.sum_product_right]

/-- If $X: \Omega \to S$, $Y: \Omega \to T$ are random variables, and $f: T \times S → U$ is injective for each fixed $t \in T$, then $H[f(Y,X)|Y] = H[X|Y]$.  Thus for instance $H[X-Y|Y]=H[X|Y]$.-/
lemma condEntropy_of_inj_map [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (f : T → S → U) (hf : ∀ t : T, Function.Injective (f t)) :
    H[(fun ω ↦ f (Y ω) (X ω)) | Y ; μ] = H[X | Y ; μ] := by
  rw [condEntropy_eq_sum, condEntropy_eq_sum]
  have : ∀ y, H[fun ω ↦ f (Y ω) (X ω)|Y←y; μ] = H[(f y ∘ X) | Y ← y ; μ] := by
    intro y
    refine entropy_congr ?_
    have : ∀ᵐ ω ∂μ[|Y ⁻¹' {y}], Y ω = y := by
      rw [ae_iff, cond_apply _ (hY (measurableSet_singleton _))]
      have : {a | ¬Y a = y} = (Y ⁻¹' {y})ᶜ := by ext; simp
      rw [this, Set.inter_compl_self, measure_empty, mul_zero]
    filter_upwards [this] with ω hω
    rw [hω]
    simp
  simp_rw [this]
  congr with y
  rw [entropy_comp_of_injective _ hX (f y) (hf y)]

/-- A weaker version of the above lemma in which f is independent of Y. -/
lemma condEntropy_comp_of_injective [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (μ : Measure Ω) (hX : Measurable X) (f : S → U) (hf : Function.Injective f) :
    H[f ∘ X | Y ; μ] = H[X | Y ; μ] :=
  integral_congr_ae (ae_of_all _ (fun _ ↦ entropy_comp_of_injective _ hX f hf))

lemma condEntropy_comm {Z : Ω → U} [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨ X, Y ⟩ | Z ; μ] = H[⟨ Y, X ⟩ | Z; μ] := by
  change H[⟨ X, Y ⟩ | Z ; μ] = H[Prod.swap ∘ ⟨ X, Y ⟩ | Z; μ]
  exact (condEntropy_comp_of_injective μ (hX.prod_mk hY) Prod.swap Prod.swap_injective).symm

end condEntropy

section pair

/-- One form of the chain rule: $H[X,Y] = H[X] + H[Y|X]. -/
lemma chain_rule'
  (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) :
    H[⟨ X, Y ⟩; μ] = H[X ; μ] + H[Y | X ; μ] := by
  have : IsProbabilityMeasure (μ.map X) := isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (μ.map (⟨ X, Y ⟩)) :=
    isProbabilityMeasure_map (hX.prod_mk hY).aemeasurable
  rw [entropy_eq_kernel_entropy, kernel.chain_rule,
    ← kernel.map_const _ (hX.prod_mk hY), kernel.fst_map_prod _ hX hY, kernel.map_const _ hX,
    kernel.map_const _ (hX.prod_mk hY)]
  congr 1
  · rw [kernel.entropy, integral_dirac]
    rfl
  · simp_rw [condEntropy_eq_kernel_entropy hY hX]
    have : Measure.dirac () ⊗ₘ kernel.const Unit (μ.map X) = μ.map (fun ω ↦ ((), X ω)) := by
      ext s _
      rw [Measure.dirac_unit_compProd_const, Measure.map_map measurable_prod_mk_left hX]
      congr
    rw [this, kernel.entropy_congr (condEntropyKernel_const_unit hX hY μ)]
    have : μ.map (fun ω ↦ ((), X ω)) = (μ.map X).map (Prod.mk ()) := by
      ext s _
      rw [Measure.map_map measurable_prod_mk_left hX]
      rfl
    rw [this, kernel.entropy_prodMkLeft_unit]

/-- Another form of the chain rule: $H[X,Y] = H[Y] + H[X|Y]. -/
lemma chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) :
    H[⟨ X, Y ⟩; μ] = H[Y ; μ] + H[X  | Y ; μ] := by
  rw [entropy_comm hX hY, chain_rule' μ hY hX]

/-- Another form of the chain rule: $H[X|Y] = H[X,Y] - H[Y]. -/
lemma chain_rule'' (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) : H[X|Y;μ] = H[⟨ X, Y ⟩; μ] - H[Y ; μ] := by
  rw [chain_rule μ hX hY, add_sub_cancel']

/-- If $X: \Omega \to S$ and $Y: \Omega \to T$ are random variables, and $f: T \to U$ is an injection then $H[X|f(Y)] = H[X|Y]$.
 -/
lemma condEntropy_of_inj_map' [MeasurableSingletonClass S] (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (f : T → U) (hf : Function.Injective f) (hfY : Measurable (f ∘ Y)):
    H[X | f ∘ Y ; μ] = H[X | Y ; μ] := by
    rw [chain_rule'' μ hX hY, chain_rule'' μ hX hfY, chain_rule' μ hX hY, chain_rule' μ hX hfY]
    congr 1
    . congr 1
      exact condEntropy_comp_of_injective μ hY f hf
    exact entropy_comp_of_injective μ hY f hf

/--   If $X: \Omega \to S$, $Y: \Omega \to T$,$Z: \Omega \to U$ are random variables, then
$$ H[  X,Y | Z ] = H[X | Z] + H[Y|X, Z].$$ -/
lemma cond_chain_rule' (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[⟨ X, Y ⟩ | Z ; μ] = H[X | Z ; μ] + H[Y | ⟨ X, Z ⟩ ; μ] := by
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  have := isMarkovKernel_condEntropyKernel (hX.prod_mk hY) hZ μ
  rw [condEntropy_eq_kernel_entropy (hX.prod_mk hY) hZ, kernel.chain_rule]
  congr 1
  . rw [condEntropy_eq_kernel_entropy hX hZ]
    refine kernel.entropy_congr ?_
    exact condEntropyKernel_fst_ae_eq hX hY hZ μ
  · rw [condEntropy_two_eq_kernel_entropy hY hX hZ]

/-- $$ H[  X,Y | Z ] = H[Y | Z] + H[X|Y, Z].$$ -/
lemma cond_chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[⟨ X, Y ⟩ | Z ; μ] = H[Y | Z ; μ] + H[X | ⟨ Y, Z ⟩ ; μ] := by
    rw [condEntropy_comm hX hY, cond_chain_rule' _ hY hX hZ]

/-- Data-processing inequality for the entropy:
$$ H[f(X)] \leq H[X].$$
To upgrade this to equality, see `entropy_of_comp_eq_of_comp` or `entropy_comp_of_injective`. -/
lemma entropy_comp_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (f : S → U) :
    H[f ∘ X ; μ] ≤ H[X ; μ] := by
  have hfX : Measurable (f ∘ X) := (measurable_of_finite _).comp hX
  have : H[X ; μ] = H[⟨ X, f ∘ X ⟩ ; μ] := by
    refine (entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) ?_).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule _ hX hfX]
  simp only [le_add_iff_nonneg_right]
  exact condEntropy_nonneg X (f ∘ X) μ

/-- A Schroder-Bernstein type theorem for entropy: if two random variables are functions of each other, then they have the same entropy.  Can be used as a substitute for `entropy_comp_of_injective` if one doesn't want to establish the injectivity. -/
lemma entropy_of_comp_eq_of_comp
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (f : S → T) (g : T → S) (h1 : Y = f ∘ X) (h2 : X = g ∘ Y) :
    H[X ; μ] = H[Y ; μ] := by
  have h3 : H[X ; μ] ≤ H[Y ; μ]  := by
    rw [h2]; exact entropy_comp_le μ hY _
  have h4 : H[Y ; μ] ≤ H[X ; μ]  := by
    rw [h1]; exact entropy_comp_le μ hX _
  linarith



end pair

section mutualInformation

/-- The mutual information $I[X:Y]$ of two random variables is defined to be $H[X] + H[Y] - H[X;Y]$. -/
noncomputable
def mutualInformation (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[⟨ X, Y ⟩ ; μ]

lemma mutualInformation_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
  mutualInformation X Y μ = H[X ; μ] + H[Y ; μ] - H[⟨ X, Y ⟩ ; μ] := rfl

notation3:max "I[" X ":" Y ";" μ "]" => mutualInformation X Y μ
notation3:max "I[" X ":" Y "]" => mutualInformation X Y volume

/-- $I[X:Y] = H[X] - H[X|Y]$. -/
lemma mutualInformation_eq_entropy_sub_condEntropy [MeasurableSingletonClass S]
    [MeasurableSingletonClass T] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  rw [mutualInformation_def, chain_rule μ hX hY]
  abel

/-- $I[X:Y] = I[Y:X]$. -/
lemma mutualInformation_comm [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    I[X : Y ; μ] = I[Y : X ; μ] := by simp_rw [mutualInformation, add_comm, entropy_comm hX hY]

/-- Mutual information is non-negative. -/
lemma mutualInformation_nonneg [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    0 ≤ I[X : Y ; μ] := by
  have : IsProbabilityMeasure (μ.map (⟨ X, Y ⟩)) :=
    isProbabilityMeasure_map (hX.prod_mk hY).aemeasurable
  simp_rw [mutualInformation_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨ X, Y ⟩)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prod_mk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨ X, Y ⟩)).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prod_mk hY)]
    congr
  rw [h_fst, h_snd]
  exact measureMutualInfo_nonneg _

/-- Substituting variables for ones with the same distributions doesn't change the entropy. -/
lemma IdentDistrib.mutualInformation_eq {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X' : Ω' → S} {Y' : Ω' → T} (hX : IdentDistrib X X' μ μ') (hY : IdentDistrib Y Y' μ μ')
      (hXY : IdentDistrib (⟨X,Y⟩) (⟨X',Y'⟩) μ μ') : I[X : Y ; μ] = I[X' : Y' ; μ'] := by
  simp_rw [mutualInformation_def,hX.entropy_eq,hY.entropy_eq,hXY.entropy_eq]

/-- Subadditivity of entropy. -/
lemma entropy_pair_le_add [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    H[⟨ X, Y ⟩ ; μ] ≤ H[X ; μ] + H[Y ; μ] :=
  sub_nonneg.1 $ mutualInformation_nonneg hX hY _

/-- $I[X:Y]=0$ iff $X,Y$ are independent. -/
lemma mutualInformation_eq_zero (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    I[X : Y ; μ] = 0 ↔ IndepFun X Y μ := by
  have : IsProbabilityMeasure (μ.map (⟨ X, Y ⟩)) :=
    isProbabilityMeasure_map (hX.prod_mk hY).aemeasurable
  simp_rw [mutualInformation_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨ X, Y ⟩)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prod_mk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨ X, Y ⟩)).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prod_mk hY)]
    congr
  rw [h_fst, h_snd]
  convert measureMutualInfo_eq_zero_iff (μ.map (⟨ X, Y ⟩))
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ext_iff_measureReal_singleton]
  congr! with p
  convert measureReal_prod_prod (μ:=  μ.map X) (ν := μ.map Y) {p.1} {p.2}
  · simp
  · exact Measure.map_map measurable_fst (hX.prod_mk hY)
  · exact Measure.map_map measurable_snd (hX.prod_mk hY)

/-- $H[X,Y] = H[X] + H[Y]$ if and only if $X,Y$ are independent. -/
lemma entropy_pair_eq_add (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    H[⟨ X, Y ⟩ ; μ] = H[X ; μ] + H[Y ; μ] ↔ IndepFun X Y μ := by
  rw [eq_comm, ←sub_eq_zero]
  exact mutualInformation_eq_zero hX hY

/-- If $X,Y$ are independent, then $H[X,Y] = H[X] + H[Y]$. -/
lemma entropy_pair_eq_add' (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h: IndepFun X Y μ) :
    H[⟨ X, Y ⟩ ; μ] = H[X ; μ] + H[Y ; μ] :=
  (entropy_pair_eq_add hX hY).2 h

variable [AddGroup S] in
/-- $I[X : X + Y] = H[X + Y] - H[Y]$ iff $X, Y$ are independent. -/
lemma mutualInformation_add_right {Y : Ω → S} (hX : Measurable X) (hY : Measurable Y) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h: IndepFun X Y μ) :
    I[X : X + Y ; μ] = H[X + Y; μ] - H[Y; μ] := by
  rw [mutualInformation_def, entropy_add_right hX hY, entropy_pair_eq_add' hX hY h]
  abel


/-- The conditional mutual information $I[X:Y|Z]$ is the mutual information of $X|Z=z$ and $Y|Z=z$, integrated over $z$. -/
noncomputable
def condMutualInformation (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω := by volume_tac) :
    ℝ := (μ.map Z)[fun z ↦ H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨ X, Y ⟩ | Z ← z ; μ]]

lemma condMutualInformation_def (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) :
    condMutualInformation X Y Z μ = (μ.map Z)[fun z ↦
      H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨ X, Y ⟩ | Z ← z ; μ]] := rfl

notation3:max "I[" X ":" Y "|" Z ";" μ "]" => condMutualInformation X Y Z μ
notation3:max "I[" X ":" Y "|" Z "]" => condMutualInformation X Y Z MeasureTheory.MeasureSpace.volume

/-- The conditional mutual information agrees with the information of the conditional kernel.
-/
lemma condMutualInformation_eq_kernel_mutualInfo
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : Y | Z ; μ] = Ik[condEntropyKernel (⟨ X, Y ⟩) Z μ, μ.map Z] := by
  simp_rw [condMutualInformation_def, entropy_def, kernel.mutualInfo, kernel.entropy,
    integral_eq_sum, smul_eq_mul, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr with x
  · have h := condEntropyKernel_fst_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_fintype] at h
    specialize h x
    by_cases hx : (μ.map Z) {x} = 0
    · simp [hx]
    rw [h hx, condEntropyKernel_apply hX hZ]
    rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx
  · have h := condEntropyKernel_snd_ae_eq hX hY hZ μ
    rw [Filter.EventuallyEq, ae_iff_of_fintype] at h
    specialize h x
    by_cases hx : (μ.map Z) {x} = 0
    · simp [hx]
    rw [h hx, condEntropyKernel_apply hY hZ]
    rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx
  · by_cases hx : (μ.map Z) {x} = 0
    · simp [hx]
    rw [condEntropyKernel_apply (hX.prod_mk hY) hZ]
    rwa [Measure.map_apply hZ (measurableSet_singleton _)] at hx

lemma condMutualInformation_eq_integral_mutualInformation :
    I[X : Y | Z ; μ] = (μ.map Z)[fun z ↦ I[X : Y ; μ[|Z ⁻¹' {z}]]] := rfl

/-- $I[X:Y|Z] = I[Y:X|Z]$. -/
lemma condMutualInformation_comm [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (μ : Measure Ω) :
    I[X : Y | Z ; μ] = I[Y : X | Z ; μ] := by
  simp_rw [condMutualInformation_def, add_comm, entropy_comm hX hY]

/-- Conditional information is non-nnegative. -/
lemma condMutualInformation_nonneg [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) (Z : Ω → U) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    0 ≤ I[X : Y | Z ; μ] := by
  refine integral_nonneg (fun z ↦ ?_)
  by_cases hz : μ (Z ⁻¹' {z}) = 0
  · have : μ[|Z ⁻¹' {z}] = 0 := cond_eq_zero_of_measure_zero hz
    simp [this]
  have : IsProbabilityMeasure (μ[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure μ hz
  exact mutualInformation_nonneg hX hY _

/-- $$ I[X:Y|Z] = H[X|Z] + H[Y|Z] - H[X,Y|Z].$$ -/
lemma condMutualInformation_eq (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z; μ] - H[⟨X, Y⟩ | Z ; μ] := by
  rw [condMutualInformation_eq_kernel_mutualInfo hX hY hZ, kernel.mutualInfo,
    kernel.entropy_congr (condEntropyKernel_fst_ae_eq hX hY hZ _),
    kernel.entropy_congr (condEntropyKernel_snd_ae_eq hX hY hZ _),
    condEntropy_eq_kernel_entropy hX hZ, condEntropy_eq_kernel_entropy hY hZ,
    condEntropy_eq_kernel_entropy (hX.prod_mk hY) hZ]

/-- $$ I[X:Y|Z] = H[X|Z] - H[X|Y,Z].$$ -/
lemma condMutualInformation_eq' (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    I[X : Y | Z ; μ] = H[X | Z ; μ] - H[X | ⟨Y, Z⟩  ; μ] := by
  rw [condMutualInformation_eq hX hY hZ, cond_chain_rule _ hX hY hZ]
  ring

section IsProbabilityMeasure
variable (μ : Measure Ω) [IsProbabilityMeasure μ] [MeasurableSingletonClass S]
  [MeasurableSingletonClass T]

/-- $$ H[X] - H[X|Y] = I[X:Y] $$ -/
lemma entropy_sub_condEntropy (hX : Measurable X) (hY : Measurable Y) :
    H[X ; μ] - H[X | Y ; μ] = I[X : Y ; μ] := by
  rw [mutualInformation_def, chain_rule _ hX hY, add_comm, add_sub_add_left_eq_sub]

/-- $$ H[X|Y] ≤ H[X] $$ -/
lemma condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y) [IsProbabilityMeasure μ] :
    H[X | Y ; μ] ≤ H[X ; μ] :=
  sub_nonneg.1 $ by rw [entropy_sub_condEntropy _ hX hY]; exact mutualInformation_nonneg hX hY _

/-- $H[X|Y,Z] \leq H[X|Z]$ -/
lemma entropy_submodular (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[X | ⟨ Y, Z ⟩ ; μ] ≤ H[X | Z ; μ] := by
  rw [condEntropy_eq_kernel_entropy hX hZ, condEntropy_two_eq_kernel_entropy hX hY hZ]
  have : IsMarkovKernel (condEntropyKernel (fun a ↦ (Y a, X a)) Z μ) :=
    isMarkovKernel_condEntropyKernel (hY.prod_mk hX) hZ μ
  have : IsProbabilityMeasure (μ.map Z) := isProbabilityMeasure_map hZ.aemeasurable
  refine (kernel.entropy_condKernel_le_entropy_snd _ _).trans_eq ?_
  exact kernel.entropy_congr (condEntropyKernel_snd_ae_eq hY hX hZ _)

/-- The submodularity inequality:
$$ H[X,Y,Z] + H[Z] \leq H[X,Z] + H[Y,Z].$$ -/
lemma entropy_triple_add_entropy_le
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    H[⟨ X, ⟨ Y, Z ⟩ ⟩; μ] + H[Z ; μ] ≤
      H[⟨ X, Z ⟩ ; μ] + H[⟨ Y, Z ⟩ ; μ] := by
  rw [chain_rule _ hX (hY.prod_mk hZ), chain_rule _ hX hZ, chain_rule _ hY hZ]
  ring_nf
  exact add_le_add le_rfl (entropy_submodular _ hX hY hZ)

variable {μ : Measure Ω}

/-- The assertion that X and Y are conditionally independent relative to Z.  -/
def condIndepFun (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω) : Prop := sorry

/-- $I[X:Y|Z]=0$ iff $X,Y$ are conditionally independent over $Z$. -/
lemma condMutualInformation_eq_zero (X : Ω → S) (Y : Ω → T) (Z : Ω → U) : I[X : Y | Z ; μ] = 0 ↔ condIndepFun X Y Z μ := sorry

/-- If $X, Y$ are conditionally independent over $Z$, then $H[X,Y,Z] = H[X,Z] + H[Y,Z] - H[Z]$. -/
lemma ent_of_cond_indep (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (h : condIndepFun X Y Z μ): H[ ⟨ X, ⟨ Y, Z ⟩ ⟩ ; μ ] = H[ ⟨ X, Z ⟩; μ ] + H[ ⟨ X, Z ⟩; μ ] - H[Z; μ] := by sorry


end IsProbabilityMeasure
end mutualInformation

section copy

variable {mΩ' : MeasurableSpace Ω'}

/-- The following three lemmas should probably be in Mathlib. -/
lemma _root_.MeasurableSet_comap_fst {s : Set (S × T)}
  (h : MeasurableSet[MeasurableSpace.comap Prod.fst inferInstance] s) : ∃ s' : Set S, s' ×ˢ Set.univ = s := by
  simp_rw [Set.prod_univ]
  obtain ⟨s', _, hs'⟩ := h
  exact ⟨s', hs'⟩

lemma _root_.MeasurableSet_comap_snd {t : Set (S × T)}
    (h : MeasurableSet[MeasurableSpace.comap Prod.snd inferInstance] t) : ∃ t' : Set T, Set.univ ×ˢ t' = t := by
  simp_rw [Set.univ_prod]
  obtain ⟨t', _, ht'⟩ := h
  exact ⟨t', ht'⟩

lemma _root_.IndepFun.fst_snd [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] : IndepFun (Prod.fst : Ω × Ω' → Ω) (Prod.snd : Ω × Ω' → Ω') (μ.prod μ') := by
  rw [@IndepFun_iff]
  intro t1 t2 ht1 ht2
  obtain ⟨t1', ht1'⟩ := MeasurableSet_comap_fst ht1
  obtain ⟨t2', ht2'⟩ := MeasurableSet_comap_snd ht2
  simp [← ht1',← ht2', Set.top_eq_univ, Set.prod_inter_prod, Set.inter_univ, Set.univ_inter, Measure.prod_prod, measure_univ, mul_one, one_mul]

/-- For $X,Y$ random variables, one can find independent copies $X',Y'$ of $X,Y$. -/
lemma independent_copies {X : Ω → S} {Y : Ω' → T} (hX: Measurable X) (hY: Measurable Y) (μ: Measure Ω) (μ': Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] : ∃ ν : Measure (S × T), ∃ X' : S × T → S, ∃ Y' : S × T → T, IsProbabilityMeasure ν ∧ Measurable X' ∧ Measurable Y' ∧ (IndepFun X' Y' ν) ∧ IdentDistrib X' X ν μ ∧ IdentDistrib Y' Y ν μ' := by
  use (μ.map X).prod (μ'.map Y)
  have := MeasureTheory.isProbabilityMeasure_map hX.aemeasurable (μ:=μ)
  have := MeasureTheory.isProbabilityMeasure_map hY.aemeasurable (μ:=μ')
  use Prod.fst
  use Prod.snd
  refine ⟨inferInstance, measurable_fst, measurable_snd, IndepFun.fst_snd, ?_, ?_⟩
  · refine ⟨measurable_fst.aemeasurable, hX.aemeasurable, ?_⟩
    simp? says simp only [Measure.map_fst_prod, measure_univ, one_smul]
  · refine ⟨measurable_snd.aemeasurable, hY.aemeasurable, ?_⟩
    simp? says simp only [Measure.map_snd_prod, measure_univ, one_smul]

universe u v

/-- Let $X_i : \Omega_i \to S_i$ be random variables for $i=1,\dots,k$.  Then there exist jointly independent random variables $X'_i: \Omega' \to S_i$ for $i=1,\dots,k$ such that each $X'_i$ is a copy of $X_i$.  May need some hypotheses of measurability and non-degeneracy -/
lemma independent_copies' {I: Type*} [Fintype I] {S : I → Type u}
    [mS : ∀ i : I, MeasurableSpace (S i)] {Ω : I → Type v}
    [mΩ : ∀ i : I, MeasurableSpace (Ω i)] (X : ∀ i : I, Ω i → S i) (hX : ∀ i : I, Measurable (X i))
    (μ : ∀ i : I, Measure (Ω i)) :
    ∃ (A : Type (max u v)) (mA : MeasurableSpace A) (μA : Measure A) (X' : ∀ i, A → S i),
    IsProbabilityMeasure μA ∧
    (iIndepFun mS X' μA) ∧
    ∀ i : I, Measurable (X' i) ∧ IdentDistrib (X' i) (X i) μA (μ i) := by sorry

inductive Triple := | first | second | third deriving DecidableEq
instance Triple.fintype : Fintype Triple where
  elems := {first, second, third}
  complete := by intro i; induction i <;> decide

def Triple_equiv_fin3 : Triple ≃ Fin 3 where
  toFun x := match x with | .first => 0 | .second => 1 | .third => 2
  invFun := ![.first, .second, .third]
  left_inv x := by cases x <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- A version with exactly 3 random variables that have the same codomain.
It's unfortunately incredibly painful to prove this from the general case. -/
lemma independent_copies3_nondep {S : Type u}
    [mS : MeasurableSpace S]
    {Ω₁ Ω₂ Ω₃ : Type v}
    [mΩ₁ : MeasurableSpace Ω₁] [mΩ₂ : MeasurableSpace Ω₂] [mΩ₃ : MeasurableSpace Ω₃]
    {X₁ : Ω₁ → S} {X₂ : Ω₂ → S} {X₃ : Ω₃ → S}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hX₃ : Measurable X₃)
    (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂) (μ₃ : Measure Ω₃) :
    ∃ (A : Type (max u v)) (mA : MeasurableSpace A) (μA : Measure A)
      (X₁' X₂' X₃' : A → S),
    IsProbabilityMeasure μA ∧
    (iIndepFun (fun _ ↦ mS) ![X₁', X₂', X₃'] μA) ∧
      Measurable X₁' ∧ Measurable X₂' ∧ Measurable X₃' ∧
      IdentDistrib X₁' X₁ μA μ₁ ∧ IdentDistrib X₂' X₂ μA μ₂ ∧ IdentDistrib X₃' X₃ μA μ₃ := by
  let Ω : Triple → Type v := Triple.rec Ω₁ Ω₂ Ω₃
  let mΩ : (i : Triple) → MeasurableSpace (Ω i) := by intro i; induction i <;> (dsimp; assumption)
  let X : (i : Triple) → Ω i → S := Triple.rec X₁ X₂ X₃
  let hX : ∀ (i : Triple), @Measurable _ _ (mΩ i) mS (X i) := by
    intro i; induction i <;> (dsimp; assumption)
  let μ : (i : Triple) → @Measure (Ω i) (mΩ i) := by intro i; induction i <;> (dsimp; assumption)
  obtain ⟨A, mA, μA, X', hμ, hi, hX'⟩ := independent_copies' (mS := fun _ ↦ mS) (mΩ := mΩ) X hX μ
  refine ⟨A, mA, μA, X' .first, X' .second, X' .third, hμ, ?_,
    (hX' .first).1, (hX' .second).1, (hX' .third).1,
    (hX' .first).2, (hX' .second).2, (hX' .third).2⟩
  apply iIndepFun.reindex Triple_equiv_fin3 _
  convert hi using 1; ext i; cases i <;> rfl

/-- For $X,Y$ random variables, there is a canonical choice of conditionally independent trials $X_1,X_2,Y'$.-/
lemma condIndependent_copies (X : Ω → S) (Y : Ω → T) (μ: Measure Ω): ∃ ν : Measure (S × S × T), ∃ X_1 X_2 : S × S × T → S, ∃ Y' : S × S × T → T, IsProbabilityMeasure ν ∧ Measurable X_1 ∧ Measurable X_2 ∧ Measurable Y' ∧ (condIndepFun X_1 X_2 Y' ν) ∧ IdentDistrib (⟨ X_1, Y' ⟩) (⟨ X, Y ⟩) ν μ ∧ IdentDistrib (⟨ X_2, Y' ⟩) (⟨ X, Y ⟩) ν μ := by sorry


end copy


end ProbabilityTheory



section MeasureSpace_example

open ProbabilityTheory

variable {Ω S T : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T}

/-- An example to illustrate how `MeasureSpace` can be used to suppress the ambient measure. -/
example (hX : Measurable X) (hY : Measurable Y) :
  H[⟨ X, Y ⟩] = H[Y] + H[X | Y] := chain_rule _ hX hY

end MeasureSpace_example
