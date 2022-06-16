-- primer_ejemplo.lean
-- Primer ejemplo de demostración.
-- ---------------------------------------------------------------------

import tactic 

-- 1ª demostración
-- ===============

example
  (x : ℤ)           
  : x^2 - 2 * x + 1 = 0 ↔ x = 1 :=
begin
  have uno_es_solucion : x = 1 → x^2 - 2 * x + 1 = 0, from
  begin
    assume x_es_1 : x = 1,
    calc x^2 - 2 * x + 1 = 1^2 - 2 * 1 + 1 : by rw x_es_1
                     ... = 0               : by ring
  end,

  have solucion_es_uno : x^2 - 2 * x + 1 = 0 → x = 1, from
  begin 
    assume x_es_solucion : x^2 - 2 * x + 1 = 0,

    have x_menos_1_al_cuadrado_es_0 : (x-1)^2 = 0, by 
      calc (x-1)^2 = x^2 - 2 * x + 1 : by ring_nf
               ... = 0               : x_es_solucion,

    have x_menos_1_es_0 : x - 1 = 0 :=
      pow_eq_zero x_menos_1_al_cuadrado_es_0,

    calc x = (x - 1) + 1 : by ring
       ... = 0 + 1       : by rw x_menos_1_es_0
       ... = 1           : by ring
  end,

  show _, by exact { mp  := solucion_es_uno, 
                     mpr := uno_es_solucion },
end

-- 2ª demostración
-- ===============

example
  (x : ℤ)           
  : x^2 - 2 * x + 1 = 0 ↔ x = 1 :=
begin
  split,
  { intro x_es_solucion,
    have x_menos_1_al_cuadrado_es_0 : (x-1)^2 = 0,
      { calc (x-1)^2 = x^2 - 2 * x + 1 : by ring_nf
                 ... = 0                 : x_es_solucion, },
    have x_menos_1_es_0 : x - 1 = 0,
      { exact pow_eq_zero x_menos_1_al_cuadrado_es_0, },
    exact sub_eq_zero.mp x_menos_1_es_0, },
  { intro x_es_1,
    rw x_es_1,
    ring, },
end

-- 3ª demostración
-- ===============

example
  (x : ℤ)           
  : x^2 - 2 * x + 1 = 0 ↔ x = 1 :=
begin
  split,
  { intro x_es_solucion,
    rw ← sub_eq_zero,
    have x_menos_1_al_cuadrado_es_0 : (x-1)^2 = 0,
      { by linarith },
    exact pow_eq_zero x_menos_1_al_cuadrado_es_0, },
  { intro x_es_1,
    rw x_es_1,
    ring, },
end

-- Referencia
-- ==========

-- Basado en "A simple introductory example" de Clara Löh que se
-- encuentra en https://bit.ly/3Om9Clp
