universe u

reserve infix ` /= `:50
notation [parsing_only] a /= b := ne a b

/- irreflexive functions -/

def irreflexive_fun {A : Sort u} (f : A -> A)
  := forall a, f a /= a

class is_irrefl_fun {A : Sort u} (f : A -> A) :=
  (fun_irrefl : forall a, f a /= a)

export is_irrefl_fun (fun_irrefl)

/- types with irreflexive functions -/

class has_anot (A : Sort u) :=
  (anot : A -> A)
  (anot_ne_self : forall a, anot a /= a)

export has_anot (anot anot_ne_self)

instance anot_is_irrefl {A : Sort u} [i : has_anot A] : is_irrefl_fun anot := 
  (| i.anot_ne_self |)

/- prop not -/

theorem not_ne_self: 
forall (a : Prop), not a /= a 
:= begin
  intro a,
  apply ne.elim,
  assume he : not a = a,
  have hf : (not a <-> a) <-> false := not_iff_self a,
  exact hf.mp he.to_iff
end

instance not_is_irrefl : is_irrefl_fun not := (| not_ne_self |)

instance prop_has_anot : has_anot Prop := {
  anot := not,
  anot_ne_self := not_ne_self
}

/- bool not -/

theorem bnot_ne_self: 
forall (a : bool), bnot a /= a 
:= begin
  intro a,
  cases a,
  case bool.tt begin
    rewrite bnot,
    exact ff_eq_tt_eq_false
  end,
  case bool.ff begin
    rewrite bnot,
    exact tt_eq_ff_eq_false
  end
end

instance bnot_is_irrefl : is_irrefl_fun bnot := (| bnot_ne_self |)

instance bool_has_anot : has_anot bool := {
  anot := bnot,
  anot_ne_self := bnot_ne_self
}

/- nat not -/

namespace nat

instance succ_is_irrefl : is_irrefl_fun succ := (| succ_ne_self |)

instance has_anot_succ : has_anot nat := {
  anot := succ,
  anot_ne_self := succ_ne_self
}

end nat