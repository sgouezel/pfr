import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Products of finite measures and probability measures
-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory
section FiniteMeasure_product
namespace FiniteMeasure
variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]

/-- The binary product of finite measures. -/
noncomputable def prod (μ : FiniteMeasure α) (ν : FiniteMeasure β) : FiniteMeasure (α × β) :=
  ⟨μ.toMeasure.prod ν.toMeasure, Measure.prod.instIsFiniteMeasure μ.toMeasure ν.toMeasure⟩

variable (μ : FiniteMeasure α) (ν : FiniteMeasure β)

@[simp] lemma toMeasure_prod : (μ.prod ν).toMeasure = μ.toMeasure.prod ν.toMeasure := rfl

lemma prod_apply (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ) := by
  simp [prod, @Measure.prod_apply α β _ _ μ ν _ s s_mble]

lemma prod_apply_symm (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ y, μ.toMeasure ((fun x ↦ ⟨x, y⟩) ⁻¹' s) ∂ν) := by
  simp [prod, @Measure.prod_apply_symm α β _ _ μ ν _ _ s s_mble]

lemma prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  simp only [prod, mk_apply, Measure.prod_prod, toNNReal_mul]
  rfl

lemma mass_prod : (μ.prod ν).mass = μ.mass * ν.mass := by
  simp only [mass, MeasurableSet.univ, prod_apply, preimage_univ, lintegral_const, toNNReal_mul,
    mul_comm]
  rfl

lemma zero_prod : (0 : FiniteMeasure α).prod ν = 0 := by
  rw [← mass_zero_iff, mass_prod, zero_mass, zero_mul]

lemma prod_zero : μ.prod (0 : FiniteMeasure β) = 0 := by
  rw [← mass_zero_iff, mass_prod, zero_mass, mul_zero]

@[simp] lemma map_fst_prod : (μ.prod ν).map Prod.fst = (ν univ) • μ := by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_map, toMeasure_prod, Measure.map_fst_prod]
  ext s _
  simp

@[simp] lemma map_snd_prod : (μ.prod ν).map Prod.snd = (μ univ) • ν := by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_map, toMeasure_prod, Measure.map_fst_prod]
  ext s _
  simp

lemma map_prod_map {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpace β']
    {f : α → α'} {g : β → β'} (f_mble : Measurable f) (g_mble : Measurable g):
    (μ.map f).prod (ν.map g) = (μ.prod ν).map (Prod.map f g) := by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]

lemma prod_apply_null {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = 0 ↔ (fun x ↦ ν (Prod.mk x ⁻¹' s)) =ᵐ[μ.toMeasure] 0 := by
  convert Measure.measure_prod_null (μ := μ.toMeasure) (ν := ν.toMeasure) hs
  · simp
  · constructor <;> intro h <;> filter_upwards [h] with p hp
    · simp only [Pi.zero_apply] at *
      rcases (ENNReal.toNNReal_eq_zero_iff _).mp hp with (h'|con)
      · exact h'
      · by_contra
        exact measure_ne_top _ _ con
    · simp only [Pi.zero_apply] at *
      exact (ENNReal.toNNReal_eq_zero_iff _).mpr (Or.inl hp)

lemma measure_ae_null_of_prod_null {s : Set (α × β)} (h : μ.prod ν s = 0) :
    (fun x ↦ ν (Prod.mk x ⁻¹' s)) =ᵐ[μ.toMeasure] 0 := by
  convert Measure.measure_ae_null_of_prod_null (μ := μ.toMeasure) (ν := ν.toMeasure) (s := s) ?_
  · constructor <;> intro h <;> filter_upwards [h] with p hp
    · simp only [Pi.zero_apply] at *
      rcases (ENNReal.toNNReal_eq_zero_iff _).mp hp with (h'|con)
      · exact h'
      · by_contra
        exact measure_ne_top _ _ con
    · simp only [Pi.zero_apply] at *
      exact (ENNReal.toNNReal_eq_zero_iff _).mpr (Or.inl hp)
  · simpa [toNNReal_eq_zero_iff] using h

lemma prod_swap : (μ.prod ν).map Prod.swap = ν.prod μ := by
  apply Subtype.ext
  simp [Measure.prod_swap]

end FiniteMeasure -- namespace

end FiniteMeasure_product -- section

section ProbabilityMeasure_product

namespace ProbabilityMeasure

variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]

/-- The binary product of probability measures. -/
noncomputable def prod (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    ProbabilityMeasure (α × β) :=
  ⟨μ.toMeasure.prod ν.toMeasure, Measure.prod.instIsProbabilityMeasure μ.toMeasure ν.toMeasure⟩

variable (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β)

@[simp] lemma toMeasure_prod : (μ.prod ν).toMeasure = μ.toMeasure.prod ν.toMeasure := rfl

lemma prod_apply (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ) := by
  simp [prod, @Measure.prod_apply α β _ _ μ ν _ s s_mble]

lemma prod_apply_symm (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ y, μ.toMeasure ((fun x ↦ ⟨x, y⟩) ⁻¹' s) ∂ν) := by
  simp [prod, @Measure.prod_apply_symm α β _ _ μ ν _ _ s s_mble]

lemma prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  simp only [prod, mk_apply, Measure.prod_prod, toNNReal_mul]
  rfl

example : Measurable (Prod.fst : α × β → α) := by
  exact measurable_fst

@[simp] lemma map_fst_prod : (μ.prod ν).map measurable_fst.aemeasurable = μ := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_fst_prod,
             measure_univ, one_smul]

@[simp] lemma map_snd_prod : (μ.prod ν).map measurable_snd.aemeasurable = ν := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_snd_prod,
             measure_univ, one_smul]

lemma map_prodMap {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpace β']
    {f : α → α'} {g : β → β'} (f_mble : Measurable f) (g_mble : Measurable g) :
    (μ.map f_mble.aemeasurable).prod (ν.map g_mble.aemeasurable)
      = (μ.prod ν).map (f_mble.prodMap g_mble).aemeasurable := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]

lemma prod_apply_null {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = 0 ↔ (fun x ↦ ν (Prod.mk x ⁻¹' s)) =ᵐ[μ.toMeasure] 0 := by
  convert Measure.measure_prod_null (μ := μ.toMeasure) (ν := ν.toMeasure) hs
  · simp
  · constructor <;> intro h <;> filter_upwards [h] with p hp
    · simp only [Pi.zero_apply] at *
      rcases (ENNReal.toNNReal_eq_zero_iff _).mp hp with (h'|con)
      · exact h'
      · by_contra
        exact measure_ne_top _ _ con
    · simp only [Pi.zero_apply] at *
      exact (ENNReal.toNNReal_eq_zero_iff _).mpr (Or.inl hp)

lemma measure_ae_null_of_prod_null {s : Set (α × β)} (h : μ.prod ν s = 0) :
    (fun x ↦ ν (Prod.mk x ⁻¹' s)) =ᵐ[μ.toMeasure] 0 := by
  convert Measure.measure_ae_null_of_prod_null (μ := μ.toMeasure) (ν := ν.toMeasure) (s := s) ?_
  · constructor <;> intro h <;> filter_upwards [h] with p hp
    · simp only [Pi.zero_apply] at *
      rcases (ENNReal.toNNReal_eq_zero_iff _).mp hp with (h'|con)
      · exact h'
      · by_contra
        exact measure_ne_top _ _ con
    · simp only [Pi.zero_apply] at *
      exact (ENNReal.toNNReal_eq_zero_iff _).mpr (Or.inl hp)
  · simpa [toNNReal_eq_zero_iff] using h

lemma prod_swap : (μ.prod ν).map measurable_swap.aemeasurable = ν.prod μ := by
  apply Subtype.ext
  simp [Measure.prod_swap]

end ProbabilityMeasure -- namespace

end ProbabilityMeasure_product -- section

end MeasureTheory -- namespace
