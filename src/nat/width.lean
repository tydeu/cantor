import .lemmas

namespace nat

-- Bit Width of Naturals

def width : nat -> nat
| n := 
  if h : n > 1 then 
    have n.div2 < n,
      from div2_lt_self (lt.trans zero_lt_one h),
    succ (width n.div2)
  else
    1

-- Basic Width Theorems

theorem width_zero : width 0 = 1 := rfl
theorem width_one : width 1 = 1 := rfl
theorem width_le1 {n : nat} (n_le1 : n <= 1) : width n = 1 
:= begin
  cases n, refl,
  cases n, refl,
  exact absurd n_le1 (not_succ_succ_le_one n)
end

theorem width_gt1 {n : nat} (n_gt1 : n > 1) : n.width = n.div2.width.succ 
:= by rw [width, if_pos n_gt1]

lemma width_succ_succ (n : nat) : 
n.succ.succ.width = n.succ.succ.div2.width.succ 
:= width_gt1 (one_lt_succ_succ n)

lemma width_two : width 2 = 2 := 
by rw [width_gt1 one_lt_two, div2_two, width_one]

lemma width_three : width 3 = 2 :=
by rw [width_gt1 (one_lt_succ_succ 1), div2_succ_succ, div2_one, width_one]


theorem width_pos {n : nat} : n.width > 0
:= begin
  cases n,
  rw [width_zero], 
  exact nat.zero_lt_one,
  cases n,
  rw [width_one], 
  exact nat.zero_lt_one,
  rw [width_succ_succ n],
  exact (nat.zero_lt_succ _)
end

lemma zero_lt_width (n : nat) : n.width > 0 := width_pos

--- Complex Width Theorems

theorem width_div2 {n : nat} (n_gt1 : n > 1): 
n.div2.width = n.width.pred  
:= by rw [width_gt1 n_gt1, pred_succ]

lemma width_div2_succ_succ (n : nat) : 
n.succ.succ.div2.width = n.succ.succ.width.pred  
:= width_div2 (one_lt_succ_succ n)

theorem width_mul2 {n : nat} (n_pos : n > 0): 
width (2 * n) = n.width.succ
:= begin
  cases n,
  exact absurd n_pos (not_lt_zero 0),
  rw [mul_succ 2 n, add_two],
  rw [width_succ_succ (2 * n)],
  rw [div2_succ_succ, div2_mul2],
end

lemma width_mul2_succ (n : nat): 
width (2 * n.succ) = n.succ.width.succ
:= width_mul2 (zero_lt_succ n)

theorem width_mul2_add_one (n : nat) (n_pos : n > 0): 
width (2 * n + 1) = n.width.succ
:= begin
  cases n, exact absurd n_pos (not_lt_zero 0),
  rw [width_gt1 (one_lt_succ_of_pos (mul_pos two_pos n_pos))],
  rw [div2_succ_mul2],
end

theorem width_pow2 (n : nat): 
width (2 ^ n) = n.succ
:= begin
  induction n, refl,
  rw [pow_succ, nat.mul_comm],
  rw [width_mul2 pow2_pos, n_ih],
end

theorem width_pow2_add {n : nat}: 
forall {m : nat}, m < 2 ^ n -> width (2 ^ n + m) = n.succ
:= begin
  induction n,
  rw [pow_zero],
  intro m, assume h,
  cases m, refl,
  exact absurd h (not_succ_lt_one _),
  intro m, assume h,
  rw [width_gt1 (one_lt_pow2_succ_add_right _ m)],
  rw [div2_val, pow_succ_add_div _ _ two_pos],
  have h' := div_lt_of_lt_pow_succ two_pos h,
  rw [n_ih h'],
end

theorem width_pow2_sub_one (n : nat) (n_pos : n > 0): 
width (2 ^ n - 1) = n
:= begin
  cases n, exact absurd n_pos (not_lt_zero 0),
  induction n, transitivity width 1, refl, exact width_one,
  rw [width_gt1 (one_lt_pow2_sub_one (one_lt_succ_succ n_n))],
  rw [div2_pow2_succ_sub_one (succ n_n)],
  rw [n_ih (zero_lt_succ n_n)],
end

theorem lt_pow2_of_width (n : nat): n < 2 ^ (width n)
:= begin
  apply nat.strong_induction_on n,
  intro n_n, assume n_ih,
  cases n_n, 
  rw [width_zero, pow_one],
  exact zero_lt_two,
  cases n_n,
  rw [width_one, pow_one],
  exact one_lt_two,
  rw [width_succ_succ],
  rw [pow_succ, div2_val],
  apply (div_lt_iff_lt_mul n_n.succ.succ _ two_pos).mp,
  apply n_ih (n_n.succ.succ / 2),
  exact (div_lt_self (zero_lt_succ n_n.succ) one_lt_two),
end

theorem lt_pow2_max_width_right (n x : nat): n < 2 ^ max x (width n) 
:= begin
  apply nat.lt_of_lt_of_le,
  exact lt_pow2_of_width n,
  apply pow_le_pow_of_le_right two_pos,
  exact le_max_right _ _,
end

end nat