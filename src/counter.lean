import nat.width
import nat.lemmas

namespace counter

open nat

def idx (m n : nat) := (2 ^ m - 1) + n

theorem idx_pos {m n : nat} (m_pos : m > 0): 0 < idx m n
:= by rw [idx]; exact zero_lt_add_of_pos_left _ (zero_lt_pow2_sub_one m_pos)

theorem idx_succ {m n : nat}: succ (idx m n) = (2 ^ m) + n
:= begin
  rw [idx, <-add_one],
  rw [nat.add_assoc, nat.add_comm n 1, <-nat.add_assoc],
  rw [nat.sub_add_cancel (one_le_pow m two_pos)],
end

def idx_width (n : nat) : nat := width n.succ - 1 

theorem idx_width_zero : idx_width 0 = 0 := rfl

theorem idx_width_of_idx {m n : nat} (h : n < 2 ^ m): idx_width (idx m n) = m
:= by rw [idx_width, idx_succ, width_pow2_add h, succ_sub_one]

def counter (n : nat): 
Pi (i : nat), i < idx_width n -> bool
:= fun i _, test_bit (n.succ - 2 ^ (idx_width n)) i

theorem counter_val (n i : nat) (h : i < idx_width n):
counter n i h = test_bit (n.succ - 2 ^ (idx_width n)) i
:= rfl

def bit (n i : nat)
:= counter (idx (max i.succ (width n)) n) i begin
  rw [idx_width_of_idx],
  exact le_max_left (succ i) _,
  exact lt_pow2_max_width_right _ _,
end

theorem bit_eq_test_bit {n i : nat}: 
bit n i = test_bit n i
:= begin
  rw [bit, counter_val],
  rw [idx_succ, idx_width_of_idx (lt_pow2_max_width_right _ _)],
  rw [add_comm, nat.add_sub_cancel],
end

def sub_bit (n i : nat) (h : i < width n)
:= counter (idx (width n) n) i begin  
  rw [idx_width_of_idx (lt_pow2_of_width n)], exact h
end

theorem sub_bit_eq_test_bit {n i : nat} (h : i < width n): 
sub_bit n i h = test_bit n i
:= begin
  rw [sub_bit, counter_val],
  rw [idx_succ, idx_width_of_idx (lt_pow2_of_width n)],
  rw [add_comm, nat.add_sub_cancel],
end

end counter