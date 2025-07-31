import Mathlib.Data.Fin.Basic

theorem Fin.cast_surjective {k l:ℕ} (h: k = l) : Function.Surjective (Fin.cast h) :=
  (rightInverse_cast h).surjective -- or `(finCongr h).surjective`

/-- For Mathlib -/
theorem Fin.cast_bijective {k l:ℕ} (h: k = l) : Function.Bijective (Fin.cast h) :=
  ⟨ cast_injective h, cast_surjective h ⟩ -- or `(finCongr h).bijective`


theorem Fin.forall_fin_three {p : Fin 3 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 ∧ p 2 :=
  Fin.forall_fin_succ.trans <| and_congr_right fun _ => Fin.forall_fin_two

