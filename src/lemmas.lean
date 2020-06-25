universe u

theorem cond_tt {A : Type u} {a b : A} : cond tt a b = a := by simp
theorem cond_ff {A : Type u} {a b : A} : cond ff a b = b := by simp
