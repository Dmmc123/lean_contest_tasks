import data.real.basic
import algebra.field.basic
import data.nat.parity
import algebra.big_operators.ring

open_locale big_operators

open division_ring
open finset
open nat

-- supporting proofs

theorem alg_sup_proof_1 (n : ℕ) (h₀ : n > 1) :
  (n-1)/2 < n :=
begin
  rw nat.div_lt_iff_lt_mul,
  {
    induction n with n hn,
    {linarith},
    {rw succ_eq_add_one, simp, linarith}
  },
  {exact zero_lt_two}
end

theorem alg_sup_proof_2 (n : ℕ) (h₀ : n > 1) :
  n/2 < n :=
begin
  rw nat.div_lt_iff_lt_mul,
  {linarith},
  {exact zero_lt_two}
end

theorem alg_sup_proof_3 (n k : ℕ) :
  2 * 2 ^ k * (n + 1) > 1 :=
begin
  have hx : ∃ x : ℕ, x = 2 ^ k, by use 2 ^ k,
  cases hx with x hx,
  have hx₂ : x > 0, by simp *,
  have hy : ∃ y : ℕ, y = n + 1, by use (n+1),
  cases hy with y hy,
  have hy₂ : y > 0, by simp *,
  have hxy : ∃ xy : ℕ, xy = x * y, by use x * y,
  cases hxy with xy hxy,
  have hxy₂ : xy > 0, by {rw hxy, exact mul_pos hx₂ hy₂},
  rw [←hx, ←hy, mul_assoc, ←hxy],
  linarith
end


def c : ℕ → ℤ
| n :=
  if h₀ : n > 1 then
    if h₁ : odd n then
      have (n-1)/2 < n, by exact alg_sup_proof_1 n h₀,
      (-1) ^ ((n-1)/2) * c ((n-1)/2)
    else
      have n/2 < n, by exact alg_sup_proof_2 n h₀,
      c (n/2)
  else
    1

-- lhs of core

theorem c_2n_eq_c_n (n : ℕ) :
  c(2*n) = c(n) :=
begin
  rw c,
  cases n,
  {simp, rw c, simp},
  {
    rw succ_eq_add_one,
    have n_greater : 2 * (n + 1) > 1, by {
      exact (cmp_eq_lt_iff 1 (2 * (n + 1))).mp rfl
    },
    have n_even : even (2 * (n + 1)), by {rw even, use n + 1},
    simp *,
  }
end

theorem c_2n_add_2_eq_c_n_add_1 (n : ℕ) :
  c(2*n+2) = c(n+1) :=
begin
  have eq_ex : 2 * n + 2 = 2 * (n + 1), by linarith,
  rw eq_ex,
  exact c_2n_eq_c_n (n + 1)
end

-- rhs of core

theorem c_2n_add_1_eq_sign_c_n (n : ℕ) :
  c(2*n+1) = (-1) ^ n * c(n) :=
begin
  rw c,
  cases n,
  {simp, rw c, simp},
  {
    rw succ_eq_add_one,
    have ex_greater : 2 * (n + 1) + 1 > 1, by linarith,
    have ex_odd : odd (2*(n+1)+1), by {rw odd, use (n+1)},
    simp *
  }
end

theorem c_2n_add_3_eq_sign_c_n_add_1 (n : ℕ) : 
  c(2*n+3) = (-1) ^ (n+1) * c(n+1) :=
begin
  have eq_ex : 2 * n + 3 = 2 * (n + 1) + 1, by linarith,
  rw eq_ex,
  exact c_2n_add_1_eq_sign_c_n (n + 1)
end

-- main equality 
theorem core_eq_putnam (n : ℕ) :
  c(2*n) * c(2*n+2) = (-1) * c(2*n+1) * c(2*n+3) :=
begin
  -- exploiting mini-proofs to simplify
  rw c_2n_eq_c_n,
  rw c_2n_add_2_eq_c_n_add_1,
  rw c_2n_add_1_eq_sign_c_n,
  rw c_2n_add_3_eq_sign_c_n_add_1,
  -- deal with signs
  -- get rid of (-1)^(2)
  rw [←mul_assoc, ←mul_assoc, ←pow_succ],
  rw mul_assoc ((-1 : ℤ) ^ (n + 1)),
  rw mul_comm (c(n)) ((-1)^(n+1)),
  rw [←mul_assoc, pow_succ, ←mul_assoc],
  rw [mul_assoc (-1 : ℤ), mul_comm ((-1 : ℤ)^n)],
  rw ←mul_assoc (-1 : ℤ) (-1) ((-1)^n),
  rw [←sq (-1 : ℤ), neg_one_sq, one_mul],
  -- get rid of (-1)^n
  rw [←pow_add, ←two_mul, mul_comm 2 n],
  rw [pow_mul', neg_one_sq, one_pow, one_mul]
end


theorem putnam_2013_b1 : 
  ∑ i in range 2014, c(i) * c(i+2) = 0 :=
begin
  have eq : 2014 = 2 * 1007, by norm_num,
  rw eq,
  induction 1007,
  {simp},
  {
    rw [succ_eq_add_one, mul_add, mul_one],
    rw [sum_range_succ, sum_range_succ],
    rw [ih, zero_add, core_eq_putnam],
    linarith 
  }
end