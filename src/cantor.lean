import irrefl
import diagonal
import data.stream

universes u v

namespace cantor

open diagonal

-- Cantor's diagonal argument generalized to types with irreflexive maps
theorem type_cantor {A : Sort u} {B : Sort v} [has_anot B]:
not exists M : A -> (A -> B), forall f : A -> B, exists a : A, f = M a 
:= begin
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

/- Specializations of the generalized diagonal argument -/

-- Diagonal Argument for Closed Binary Functions
theorem closed_cantor {A : Sort u} [has_anot A]:
not exists M : A -> (A -> A), forall f : A -> A, exists a, f = M a 
:= type_cantor

-- Diagonal Argument for Relations
theorem relational_cantor {A : Sort u}:
not exists R : A -> A -> Prop, forall S : A -> Prop, exists a, S = R a 
:= type_cantor

-- Diagonal Argument for Sets
theorem set_cantor {A : Type u}:
not exists R : A -> set A, forall S : set A, exists a, S = R a 
:= relational_cantor

-- Diagonal Argument for Streams
theorem stream_cantor {a : Type u} [has_anot a]:
not exists M : stream (stream a), forall S : stream a, exists n, S = M n 
:= type_cantor

-- Diagonal Argument for Boolean (Bit) Streams
theorem bool_stream_cantor:
not exists M : stream (stream bool), forall S : stream bool, exists n, S = M n 
:= stream_cantor

end cantor
