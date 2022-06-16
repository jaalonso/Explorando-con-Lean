/-
Copyright (c) 2022 Clara Löh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Clara Löh.
-/

/-
# A simple introductory example
-/

import tactic -- standard proof tactics

lemma binomial_solution 
      (x : ℤ)
    : x^2 - 2 * x + 1 = 0 ↔ x = 1
:=
begin
  -- We show both implications individually

  have one_is_solution : x = 1 → x^2 - 2 * x + 1 = 0, from
  begin
    assume x_is_1 : x = 1,
    show x^2 - 2 * x + 1 = 0, 
         by {rw [x_is_1], ring},
  end,

  have solution_is_one : x^2 - 2 * x + 1 = 0 → x = 1, from
  begin 
    assume x_is_solution : x^2 - 2 * x + 1 = 0,
    -- nlinarith solves this right away, 
    -- but we give a human-readable proof

    have xminus1_squared_is_0 : (x-1)^2 = 0, by 
    calc (x-1)^2 = x^2 - 2 * x + 1 : by ring_nf
             ... = 0               : by exact x_is_solution,

    have xminus1_is_0 : x - 1 = 0, 
         by exact pow_eq_zero xminus1_squared_is_0,

    calc x = x - 1 + 1 : by ring
       ... = 1         : by {rw[xminus1_is_0], ring},
  end,

  show _, by exact {mp  := solution_is_one, 
                    mpr := one_is_solution},
end