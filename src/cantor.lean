import irrefl
import diagonal

universes u v

namespace cantor

open diagonal

/- Cantor's diagonal argument generalized to types with irreflexive maps -/

-- Diagonal Argument for Types
theorem type_cantor {A : Sort u} {B : Sort v} [has_anot B] :
not exists M : A -> (A -> B), forall f : A -> B, exists a : A, f = M a :=
begin
  by_contradiction h,
  exact exists.elim h begin
    intro M,
    assume hm,
    have hfd := hm (dnot M),
    exact exists.elim hfd begin 
      intro a,
      assume hd : dnot M = M a,
      have hnd : not (dnot M = M a) := dnot_ne_part M a,
      exact hnd hd
    end
  end
end

-- Diagonal Argument for Closed Binary Functions
theorem closed_cantor {A : Sort u} [has_anot A] :
not exists M : A -> (A -> A), forall f : A -> A, exists a : A, f = M a := type_cantor

-- Diagonal Argument for Relations
theorem relational_cantor {A : Sort u} :
not exists R : A -> A -> Prop, forall S : A -> Prop, exists a : A, S = R a := type_cantor

end cantor
