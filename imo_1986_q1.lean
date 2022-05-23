import algebra.ring.basic
import data.real.basic
import data.nat.parity

open nat

--helper theorems
theorem num_odd_square_odd (a : ℕ): odd a ↔ odd (a^2) :=
begin
  split,
  {
    intro h,
    rw pow_two,
    have h₁ : odd (a * a) ↔ odd a ∧ odd a, from nat.odd_mul,
    rw h₁,
    split,
    {exact h},
    {exact h}
  },
  {
    rw pow_two,
    intro h,
    have h₁ : odd (a * a) ↔ (odd a ∧ odd a), from nat.odd_mul,
    have h₂ : odd a ∧ odd a, by {
      have h₃ : odd (a * a) → (odd a ∧ odd a), from iff.mp h₁,
      show odd a ∧ odd a, from h₃ (h)
    },
    have h₄ : odd a, from and.left h₂,
    exact h₄
  }
end

-- the same but for even numbers
-- such wow trick
theorem num_even_square_even (a : ℕ) : even a ↔ even (a^2) :=
begin
  repeat {rw nat.even_iff_not_odd},
  rw not_iff_not_of_iff,
  rw num_odd_square_odd,
end

-- another helper theorem for casing the even difference 
theorem even_diff_same_parity (a b : ℕ) (h₀ : a ≥ b) :
  even (a - b) ↔ odd a ∧ odd b ∨ even a ∧ even b :=
begin
  split,
  {
    intro h,
    cases even_or_odd a with even_a odd_a,
    {
      have h₁ : even a ↔ even b, by {
        rw ←nat.even_sub,
        exact h,
        exact h₀,
      },
      have even_b : even b, by {rw ←h₁, exact even_a},
      have even_a_b : even a ∧ even b, by {
        exact ⟨even_a, even_b⟩,
      },
      exact or.inr even_a_b,
    },
    {
      have h₁ : odd a ↔ odd b, by {
        rw ←nat.even_sub',
        exact h,
        exact h₀,
      },
      have odd_b : odd b, by {rw ←h₁, exact odd_a},
      have odd_a_b : odd a ∧ odd b, by {
        exact ⟨odd_a, odd_b⟩,
      },
      exact or.inl odd_a_b,
    },
  },
  {
    intro h,
    cases h with odd_a_b even_a_b,
    {
      rw nat.even_sub',
      {
        cases odd_a_b with odd_a odd_b,
        exact iff_of_true odd_a odd_b,
      },
      {exact h₀},
    },
    {
      rw nat.even_sub,
      {
        cases even_a_b with even_a even_b,
        exact iff_of_true even_a even_b,
      },
      {exact h₀},
    }
  }
end

-- definitions of a square number 
def is_square (n : ℕ) :=
  ∃ k : ℕ, k^2 = n

-- useful theorem to rewrite the definition
theorem is_square_def {n : ℕ} : 
  is_square n ↔ ∃ k : ℕ, k^2 = n :=
begin
  refl
end

-- couple of cases to test how squaring of numbers works
-- case 1: 9 is a square, just using a substitution by definition
theorem nine_is_square : is_square 9 :=
begin
  rw is_square_def,
  use 3,
  ring
end

-- case 2: 10 is not a square, here we have to use parity contradictions
theorem ten_is_not_square : ¬ is_square 10 :=
begin
  rw is_square_def,
  by_contradiction,
  cases h with k h,
  have h₁ : even 10, by {rw even, use 5, ring},
  have h₂ : even k, by {rw num_even_square_even, rw h, exact h₁},
  unfold even at h₂,
  cases h₂ with m h₃,
  have h₄ : (2 * m) ^ 2 = 10, by {rw ←h₃, exact h},
  have h₅ : 4 * m ^ 2 = 10, by {rw ←h₄, ring},
  have h₆ : 2 * m ^ 2 = 5, by linarith,
  have h₇ : even (2 * m ^ 2), by {rw even, use (m ^ 2)},
  have h₈ : even 5, by {rw ←h₆, exact h₇},
  have h₉ : ¬ even 5, by {
    rw nat.even_iff_not_odd, rw decidable.not_not_iff,
    rw odd, use 2, ring
  },
  exact h₉ h₈,
end

-- trivial proof by substitution that 4 is not an odd number
theorem four_is_not_odd (n : ℕ) : ¬ odd 4 :=
begin
  rw nat.odd_iff_not_even,
  rw decidable.not_not_iff,
  rw even,
  use 2,
  ring,
end

-- solving the original task
theorem IMO1986P1
  (d : ℕ)
  (h₀ : d > 1)
  (h₁ : is_square (2 * d - 1))
  (h₂ : is_square (5 * d - 1))
  (h₃ : is_square (13 * d - 1)):
  false :=
begin
  -- step 1, proving that a is odd
  unfold is_square at h₁,
  cases h₁ with a ha,
  have a_odd : odd a, by {
    rw [num_odd_square_odd, ha, nat.odd_sub'],
    {
      have one_odd : odd 1, by {rw odd, use 0, ring},
      have even_2d : even (2 * d), by {rw even, use d},
      exact iff_of_true one_odd even_2d
    },
    {
      linarith
    },
  },
  -- step 2, proving that d is odd
  unfold odd at a_odd,
  cases a_odd with x hx,
  have d_odd : odd d, by {
    have h₄ : (2*x + 1)^2 = 2*d - 1, by {rw ←hx, exact ha},
    have h₅ : 4*x*x + 4*x + 1 = 2*d - 1, by linarith,
    have h₆ : 2*d - 1 = 4*x*x + 4*x + 1, by exact eq.symm h₅,
    have h₇ : 2*d - 1 + 1 = 4*x*x + 4*x + 1 + 1, by linarith,
    have h₈ : 2*d = 4*x*x + 4*x + 1 + 1, by {
      rw ←h₇, induction d, linarith, ring_nf,
    },
    have h₉ : 2*d = 4*x*x + 4*x + 2, by linarith,
    have hh₁ : 2*d = 2*(2*x*x + 2*x + 1), by linarith,
    have hh₂ : d = 2*x*x + 2*x + 1, by linarith,
    rw odd,
    use (x*x + x),
    rw [mul_add, ←mul_assoc],
    exact hh₂,
  },
  -- step 3, proving that b is even
  unfold odd at d_odd,
  cases d_odd with d' hd',
  unfold is_square at h₂,
  cases h₂ with b hb,
  have b_even : even b, by {
    rw [num_even_square_even, hb, hd', even],
    use (5*d' + 2),
    repeat {rw mul_add, rw ←mul_assoc},
    simp,
    refl,
  },
  -- step 4, proving that c is even
  unfold is_square at h₃,
  cases h₃ with c hc,
  have c_even : even c, by {
    rw [num_even_square_even, hc, hd', even],
    use (13*d' + 6),
    repeat {rw mul_add, rw ←mul_assoc},
    simp,
    refl,
  },
  -- step 5, introducing new parity facts about d
  unfold even at b_even,
  cases b_even with y hy,
  unfold even at c_even,
  cases c_even with z hz,
  have hdp : (z + y) * (z - y) = 2*d, by {
    have h₁ : c^2 - b^2 = (13*d-1) - (5*d-1), by rw [hc, hb],
    have h₂ : c^2 - b^2 = 8*d, by {
      rw h₁,
      have h₃ : 13 = 8 + 5, by refl,
      rw h₃,
      rw add_mul,
      have h₄ : (∃ t₁ : ℕ, t₁ = 8*d), by use (8*d),
      cases h₄ with t₁ ht₁,
      have h₅ : (∃ t₂ : ℕ, t₂ = 5*d), by use (5*d),
      cases h₅ with t₂ ht₂,
      repeat {rw [←ht₁, ←ht₂]},
      have h₆ : 1 ≤ t₂, by {rw ht₂, linarith},
      have h₇ : t₁ + t₂ - 1 = t₁ + (t₂ - 1), by {
        rw nat.add_sub_assoc,
        exact h₆,
      },
      rw h₇,
      have h₈ : (∃ t₃ : ℕ, t₃ = t₂ - 1), by use (t₂-1),
      cases h₈ with t₃ ht₃,
      repeat {rw ←ht₃},
      simp,
    },
    have h₃ : (2*z)^2 - (2*y)^2 = 8*d, by {rw [←hz, ←hy], exact h₂},
    have h₄ : 4*z*z - 4*y*y = 8*d, by {
      rw ←h₃,
      repeat {rw [pow_two, ←mul_assoc]},
      ring_nf,
    },
    have h₅ : 4*(z*z - y*y) = 4*(2*d), by {
      have eight_eq : 4 * 2 = 8, by refl,
      rw [←mul_assoc, eight_eq, ←h₄, mul_assoc, mul_assoc],
      have h₆ : (∃ t₁ : ℕ, t₁ = z * z), by use (z*z),
      cases h₆ with t₁ ht₁,
      have h₇ : (∃ t₂ : ℕ, t₂ = y * y), by use (y*y),
      cases h₇ with t₂ ht₂,
      rw [←ht₁, ←ht₂],
      rw nat.mul_sub_left_distrib,
    },
    have h₆ : z*z - y*y = 2*d, by linarith,
    rw [←h₆, nat.mul_self_sub_mul_self_eq],
  },
  -- step 6, proving the possible cases of new parity facts
  have h : odd (z + y) ∧ odd (z - y) ∨ even (z + y) ∧ even (z - y), by {
    rw ←even_diff_same_parity,
    {
      rw even,
      use y,
      have z_ge_y : z ≥ y, by {
        have y_2_le_z_2 : 2 * y ≤ 2 * z, by {
          rw [←hy, ←hz],
          have b2_le_c2 : b ^ 2 ≤ c ^ 2, by {
            rw [hb, hc],
            have d5_le_d13 : 5 * d ≤ 13 * d, by linarith,
            exact tsub_le_tsub_right d5_le_d13 1,
          },
          repeat {rw pow_two at b2_le_c2},
          exact nat.mul_self_le_mul_self_iff.mpr b2_le_c2,
        },
        linarith,
      },
      have h₁ : (∃ t₁ : ℕ, t₁ = z + y), by use (z + y),
      cases h₁ with t₁ ht₁,
      have h₂ : (∃ t₂ : ℕ, t₂ = z - y), by use (z - y),
      cases h₂ with t₂ ht₂,
      have h₃ : (∃ t₃ : ℕ, t₃ = 2 * y), by use (2 * y),
      cases h₃ with t₃ ht₃,
      rw [←ht₁, ←ht₂, ←ht₃],
      have h₁ : t₁ ≥ t₂, by {
        rw [ht₁, ht₂],
        norm_num,
        induction y,
        {ring_nf},
        {
          ring_nf,
          exact le_self_add,
        },
      },
      rw nat.sub_eq_iff_eq_add,
      {
        rw [ht₂, ←nat.add_sub_assoc],
        {
          rw nat.sub_add_comm,
          {
            rw [ht₃, ←nat.one_mul y, ←mul_assoc, ←nat.mul_sub_right_distrib],
            norm_num,
            rw ht₁,
            exact add_comm z y,
          },
          {rw ht₃, linarith},
        },
        {exact z_ge_y},
      },
      {exact h₁},
    },
    {
      have ht : z - y + y ≤ z + y + y, by {simp, linarith},
      exact (add_le_add_iff_right y).mp ht,
    },
  },
  cases h with mul_odd mul_even,
  {
    cases mul_odd with h₁ h₂,
    have even_2d : even (2 * d), by {rw even, use d},
    have odd_2d : odd (2 * d), by {rw ←hdp, exact odd.mul h₁ h₂},
    have not_odd_2d : ¬odd (2 * d), by {rw ←even_iff_not_odd, exact even_2d},
    exact not_odd_2d odd_2d,
  },
  {
    cases mul_even with h₁ h₂,
    unfold even at h₁ h₂,
    cases h₁ with t₁ ht₁,
    cases h₂ with t₂ ht₂,
    have d_odd : odd d, by {rw odd, use d', exact hd'},
    have d_even : even d, by {
      have h₁ : (2 * t₁) * (2 * t₂) = 2 * d, by {rw [←ht₁, ←ht₂], exact hdp},
      have h₂ : 2 * t₁ * t₂ = d, by linarith,
      rw even,
      use (t₁ * t₂),
      rw ←h₂,
      exact mul_assoc 2 t₁ t₂,
    },
    have d_not_odd : ¬odd d, by {rw ←even_iff_not_odd, exact d_even},
    exact d_not_odd d_odd,
  },
end