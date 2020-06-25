import lemmas

namespace nat 

-- Additional constant `add` Theorems

theorem add_two (n : nat) : n + 2 = n.succ.succ 
:= rfl

theorem two_add (n : nat) : 2 + n = n.succ.succ 
:= eq.trans (add_comm _ _) rfl

-- Additional not `le` / `lt` Theorems

theorem not_lt_self (n : nat) : not (n < n)
:= not_succ_le_self n

theorem not_succ_lt_one (n : nat) : not (n.succ < 1)
:= fun h, absurd (lt_of_succ_lt_succ h) (not_lt_zero n)

theorem not_succ_succ_le_one (n : nat) : not (n.succ.succ <= 1)
:= fun h, absurd (le_of_succ_le_succ h) (not_succ_le_zero n)

-- Additional Constant `le` / `lt` Theorems

lemma one_le_two : 1 <= 2 := le_succ 1

lemma one_lt_two : 1 < 2 := lt_succ_self 1

lemma one_lt_succ_of_pos {n : nat} (n_pos : n > 0) : 1 < n.succ 
:= succ_lt_succ n_pos

lemma one_lt_succ_succ (n : nat) : 1 < n.succ.succ 
:= succ_lt_succ (zero_lt_succ n)

lemma zero_lt_two : 0 < 2 := zero_lt_succ 1

lemma zero_lt_of_lt {n m : nat} (h : n < m) : 0 < m
:= begin cases n, exact h, exact lt.trans (zero_lt_succ n) h end

lemma zero_lt_add_of_pos_right {k : nat} (n : nat) (k_pos : k > 0) : 0 < n + k
:= zero_lt_of_lt (nat.lt_add_of_pos_right k_pos)

lemma zero_lt_add_of_pos_left {k : nat} (n : nat) (k_pos : k > 0) : 0 < k + n
:= zero_lt_of_lt (nat.lt_add_of_pos_left k_pos)

-- Additional `le_pow` / `lt_pow` Theorems

theorem base_lt_pow {b x : nat} (b_gt1 : b > 1) (x_gt1 : x > 1) : b < b ^ x
:= by have h := pow_lt_pow_of_lt_right b_gt1 x_gt1;  rw [pow_one] at h; exact h

theorem one_le_pow {b : nat} (x : nat) (b_pos : b > 0): 1 <= b ^ x
:= pow_le_pow_of_le_right b_pos (zero_le _)

theorem one_lt_pow {b x : nat} (b_gt1 : b > 1) (x_pos : x > 0) : 1 < b ^ x
:= pow_lt_pow_of_lt_right b_gt1 x_pos

theorem zero_lt_pow {b : nat} (x : nat) (b_pos : b > 0) : 0 < b ^ x
:= pos_pow_of_pos x b_pos

-- Additional `pow2` Theorems

lemma pow2_pos {n : nat} : 2 ^ n > 0 
:= pos_pow_of_pos n two_pos 

lemma zero_lt_pow2 (n : nat) : 0 < 2 ^ n := pow2_pos

lemma zero_lt_pow2_sub_one {n : nat} (n_pos : n > 0) : 0 < 2 ^ n - 1
:= pred_lt_pred one_ne_zero (one_lt_pow one_lt_two n_pos)

lemma one_lt_pow2 {x : nat} (x_pos : x > 0) : 1 < 2 ^ x
:= one_lt_pow one_lt_two x_pos

lemma one_lt_pow2_succ (x : nat) : 1 < 2 ^ x.succ
:= one_lt_pow2 (zero_lt_succ x)

lemma one_lt_pow2_succ_add_right (x m : nat) : 1 < 2 ^ x.succ + m
:= lt_add_right _ _ m (one_lt_pow2_succ x)

lemma one_lt_pow2_sub_one {n : nat} (n_gt1 : n > 1) : 1 < 2 ^ n - 1
:= pred_lt_pred two_ne_zero (base_lt_pow one_lt_two n_gt1)

-- Additional `div` Theorems

theorem add_pow_succ_div 
{b : nat} (n m : nat) (b_pos : b > 0):
(m + b ^ n.succ) / b = (m / b) + (b ^ n)
:= begin
  cases n,
  rw [pow_one, pow_zero],
  rw [add_div_right m b_pos],
  rw [pow_succ, add_mul_div_right m _ b_pos],
end

lemma pow_succ_add_div 
{b : nat} (n m : nat) (b_pos : b > 0):
(b ^ n.succ + m) / b = (b ^ n) + (m / b) 
:= begin  
  rw [nat.add_comm _ m],
  rw [nat.add_comm _ (m / b)],
  exact add_pow_succ_div n m b_pos
end

theorem div_of_pow_succ_sub_one 
{b : nat} (n : nat) (b_pos : b > 0): 
(b ^ n.succ - 1) / b = (b ^ n) - 1
:= begin
  rw [pow_succ, mul_comm],
  have h : b * b ^ n > 0,
  rw [mul_comm, <-pow_succ],
  exact pos_pow_of_pos n.succ b_pos,
  rw [mul_sub_div 0 b (b ^ n) h],
  rw [nat.zero_div b],
end

theorem div_lt_of_lt_mul {m n k : nat} 
(k_pos : k > 0): m < k * n -> m / k < n
:= by rw [mul_comm]; exact (div_lt_iff_lt_mul m n k_pos).mpr

theorem div_lt_of_lt_pow_succ 
{n x b : nat} (b_pos : b > 0): 
n < b ^ x.succ -> n / b < b ^ x
:= begin
  rw [pow_succ, mul_comm], 
  assume h, 
  exact div_lt_of_lt_mul b_pos h,
end

-- Additional `bodd` Theorems

theorem bodd_mul2 (n : nat) : bodd (2 * n) = ff
:= by rw [bodd_mul, bodd_two, ff_band]

theorem bodd_pow2_of_pos {n : nat} (n_pos : n > 0) :  bodd (2 ^ n) = ff
:= begin
  induction n,
  exact absurd n_pos (not_lt_zero 0),
  rw [pow_succ, bodd_mul, bodd_two, band_ff],
end

-- Additional `div2` Theorems

theorem div2_lt_self {n : nat} (n_pos : n > 0): n.div2 < n
:= by rw [div2_val]; exact div_lt_self n_pos one_lt_two

theorem div2_succ_lt_self {n : nat}: n.succ.div2 < n.succ
:= div2_lt_self (zero_lt_succ n)

theorem div2_mul2 (n : nat): div2 (2 * n) = n
:= by rw [div2_val, nat.mul_div_cancel_left n two_pos]

theorem div2_add_two (n : nat): 
div2 (n + 2) = n.div2 + 1 
:= begin
  rw [<-(mul_one 2), div2_val, div2_val],
  rw [add_mul_div_left n 1 two_pos],
end

theorem div2_succ_succ (n : nat): n.succ.succ.div2 = n.div2.succ 
:= by rw [<-add_two, <-add_one]; exact div2_add_two n

theorem div2_succ_mul2 (n : nat): div2 (succ (2 * n)) = n 
:= by rw [div2_succ, bodd_mul2, cond_ff, div2_mul2]

theorem div2_succ_pow2 {n : nat} (n_pos : n > 0): div2 (succ (2 ^ n)) = div2 (2 ^ n) 
:= by rw [div2_succ, bodd_pow2_of_pos n_pos, cond_ff]

theorem div2_pow2_succ (n : nat): div2 (2 ^ n.succ) = 2 ^ n 
:= by rw [pow_succ, mul_comm, div2_mul2]

theorem div2_pow2_succ_sub_one (n : nat): div2 (2 ^ n.succ - 1) = (2 ^ n) - 1
:= by rw [div2_val]; exact div_of_pow_succ_sub_one n two_pos


end nat