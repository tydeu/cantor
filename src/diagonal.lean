import .irrefl

universes u v

namespace diagonal

-- diagonal of a binary function
def diag {a : Sort u} {b : Sort v} (M : a -> a -> b) : (a -> b) 
:= fun n, (M n n)

-- map of the diagonal of a binary function
def dmap {a : Sort u} {b : Sort v} (f : b -> b) (M : a -> a -> b) : (a -> b) 
:= fun n, f (M n n)

/- 
  an irreflexive map of the diagonal of a binary function is 
  not equal to any of its partial applications (rows) 
-/
theorem irrefl_dmap_ne_part {A : Sort u} {X : Sort v}:
forall f : X -> X, irreflexive_fun f -> 
forall M : A -> (A -> X), forall a : A, dmap f M /= M a := 
begin 
  intro f,
  assume irrefl,
  intros M n,
  let d := dmap f,
  assume h  : d M = M n,
  have hn   : d M n = M n n        := congr h (eq.refl n),
  have dn   : d M n = f (M n n)    := rfl,
  have heq  : f (M n n) = M n n    := hn.subst dn,
  have hne  : f (M n n) /= M n n   := irrefl (M n n),
  exact hne heq
end

-- irrefl_dmap_ne_part using the is_irrefl type class
theorem dmap_ne_part_of_irrefl 
{A : Sort u} {B : Sort v} (f : B -> B) [is_irrefl_fun f]: 
forall M : A -> (A -> B), forall a : A, dmap f M /= M a  
:= irrefl_dmap_ne_part f fun_irrefl

-- anti-diagonal of a binary function
def dnot {a : Sort u} {b : Sort v} [bi : has_anot b] : (a -> a -> b) -> (a -> b) 
:= dmap bi.anot

-- irrefl_dmap_ne_part for dnot
theorem dnot_ne_part {A : Sort u} {B : Sort v} [has_anot B]:
forall M : A -> (A -> B), forall (n : A), dnot M /= M n 
:= dmap_ne_part_of_irrefl anot

end diagonal
