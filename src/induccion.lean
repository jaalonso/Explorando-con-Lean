-- induccion.lean
-- Inducción.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 5-julio-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Importar la librerías de tácticas y la teoría de grupos.
-- ---------------------------------------------------------------------

import tactic
import algebra.group.basic

-- ---------------------------------------------------------------------
-- Ejercicio. Habilitar la lógica clásica.
-- ---------------------------------------------------------------------

open classical

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    suma_potencias_de_dos : nat → nat
-- tal que (suma_potencias_de_dos n) = 2^0 + 2^1 +···+ 2^n
-- ---------------------------------------------------------------------

def suma_potencias_de_dos : nat → nat
| 0            := 1 
| (nat.succ n) := suma_potencias_de_dos n + 2^(n+1)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que 
--    suma_potencias_de_dos n = 2^(n+1) - 1
-- ---------------------------------------------------------------------

lemma valor_suma_potencias_de_dos 
  (n : nat)
  : suma_potencias_de_dos n = 2^(n+1) - 1 := 
begin
  induction n with m HI,
  { simp [suma_potencias_de_dos], },
  { calc suma_potencias_de_dos (m+1) 
         = suma_potencias_de_dos m + 2^(m+1) 
           : by simp [suma_potencias_de_dos]
    ...  = 2^(m+1) - 1 + 2^(m+1)     
           : by simp [HI]
    ...  = 2^(m+1) + 2^(m+1) - 1     
           : by omega
    ...  = 2 * 2^(m+1) - 1           
           : by ring_nf
    ...  = 2^(m+2) - 1               
           : by ring, },
end      

-- ---------------------------------------------------------------------
-- Ejercicio. Calcular la suma de las 5 primeras potencias de dos.
-- ---------------------------------------------------------------------

-- Se descomenta la siguiente línea y al situar el cursor en #eval se
-- obtiene el valor (que es 63).
-- 
-- #eval suma_potencias_de_dos 5 

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir la teoría de conjuntos finitos.
-- ---------------------------------------------------------------------

open finset

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir localmente la teoría de los grandes operadores (para
-- usar ∑).
-- ---------------------------------------------------------------------

open_locale big_operators 

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    suma_de_unos : nat → nat 
-- tal que (suma_de_unos n) es la suma de n veces el número 1.
-- ---------------------------------------------------------------------

def suma_de_unos : nat → nat := 
λ n : nat, ∑ (i : nat) in range n, 1

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    suma_de_unos n = n
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (n : nat)
  : suma_de_unos n = n :=
begin
  induction n with m HI,
  { simp [suma_de_unos] },
  { calc suma_de_unos (m+1) 
         = ∑ (i : nat) in range (m+1), 1  : by simp [suma_de_unos]
    ... = (∑ (i : nat) in range m, 1) + 1 : by simp
    ... = m + 1                           : by simp [HI] }, 
end

-- 2ª demostración
example
  (n : nat)
  : suma_de_unos n = n :=
begin
  unfold suma_de_unos,
  -- by library_search,
  exact sum_range_induction (λ (k : ℕ), 1) (λ (n : ℕ), n) rfl (congr_fun rfl) n,
end

-- 2ª demostración
example
  (n : nat)
  : suma_de_unos n = n :=
begin
  unfold suma_de_unos,
  apply sum_range_induction,
  { refl, },
  { intro n,
    refl, },
end

-- ---------------------------------------------------------------------
-- Ejercicio. Definir, usando sumatorios, la función
--    suma_potencias_de_dos' : nat → nat
-- tal que (suma_potencias_de_dos' n) = 2^0 + 2^1 +···+ 2^n
-- ---------------------------------------------------------------------

def suma_potencias_de_dos' : nat → nat 
:= λ n, ∑ (i : nat) in range n, 2^i  

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que 
--    suma_potencias_de_dos' n = 2^(n+1) - 1
-- ---------------------------------------------------------------------

example
  (n : nat)
  : suma_potencias_de_dos' n =  2^n - 1 :=
begin   
  induction n with m HI,
  { unfold suma_potencias_de_dos', 
    ring},
  { calc suma_potencias_de_dos' (m+1) 
        = ∑ i in range (m+1), 2^i 
        : by unfold suma_potencias_de_dos'
    ... = ∑ i in range m, 2^i + 2^m 
        : by exact sum_range_succ (λ x, 2^x) m
    ... = suma_potencias_de_dos' m + 2^m 
        : by simp [suma_potencias_de_dos']
    ... = 2^m - 1 + 2^m 
        : by simp [HI]
    ... = 2^m + 2^m - 1
        : by omega    
    ... = 2^(m+1) - 1 
        : by ring_nf, },
end 

-- =====================================================================
-- § Ejercicios complementarios                                       --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    suma_primeros_pares : nat → nat
-- tal que (suma_primeros_pares n) es la suma 
--    0 + 2 + 4 + 6 +···+ 2*n
-- ---------------------------------------------------------------------

def suma_primeros_pares : nat → nat
| 0            := 0
| (nat.succ n) := suma_primeros_pares n + 2 * (n + 1)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    suma_primeros_pares n = n * (n+1)
-- ---------------------------------------------------------------------

example
  (n : nat)
  : suma_primeros_pares n = n * (n+1) :=
begin
  induction n with m HI,
  { simp [suma_primeros_pares], },
  { calc suma_primeros_pares (m+1) 
         = suma_primeros_pares m + 2 * (m+1) 
        : by simp [suma_primeros_pares]
    ... = m * (m+1) + 2 * (m+1)
        : by simp [HI]
    ... = (m+2) * (m+1)
        : by ring        
    ... = (m+1) * (m+2) 
        : by ring, },
end     

-- ---------------------------------------------------------------------
-- Ejercicio. Definir, usando sumatorio, la función
--    suma_primeros_pares' : nat → nat
-- tal que (suma_primeros_pares' n) es la suma 
--    0 + 2 + 4 + 6 +···+ 2*n
-- ---------------------------------------------------------------------

def suma_primeros_pares' : nat → nat
:= λ n, 2 * ∑ (i : nat) in range (n+1), i   

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    suma_primeros_pares' n = n * (n+1)
-- ---------------------------------------------------------------------

example
  (n : nat)
  : suma_primeros_pares' n = n * (n+1) :=
begin
  induction n with m HI,
  { simp [suma_primeros_pares'], },
  { calc suma_primeros_pares' (m+1) 
        = 2 * ∑ (i : nat) in range (m+2), i
        : by unfold suma_primeros_pares'
    ... = 2 * ((∑ (i : nat) in range (m+1), i) + m + 1)
        : by {congr, simp only [sum_range_succ], ring} 
    ... = 2 * ∑ (i : nat) in  range (m+1), i + 2 * (m+1)
        : by ring       
    ... = m * (m+1) + 2 * (m+1)
        : by {unfold suma_primeros_pares' at HI, simp [HI]}
    ... = (m+2) * (m+1)
        : by ring        
    ... = (m+1) * (m+2)
        : by ring, },
end      

-- ---------------------------------------------------------------------
-- Ejercicio. Sea G un grupo, n ∈ ℕ y a, b ∈ G. Demostrar que
--    (a * b * a⁻¹)^n = a * b^n * a⁻¹
-- ---------------------------------------------------------------------

example
  {G : Type*} [group G]
  (a : G)
  (b : G)
  (n : ℕ)
  : (a * b * a⁻¹)^n = a * b^n * a⁻¹ :=
begin
  induction n with m HI,
  { group },
  { calc (a * b * a⁻¹)^(m+1) 
        = (a * b * a⁻¹)^m * (a * b * a⁻¹) : by simp [pow_succ' _ m]
    ... = (a * b^m * a⁻¹) * (a * b * a⁻¹) : by simp [HI]
    ... = a * b^m * b * a⁻¹               : by group 
    ... = a * b^(m+1) * a⁻¹               : by group },
end      

-- ---------------------------------------------------------------------
-- Ejercicio. Sea G un grupo, n ∈ ℕ y a, b ∈ G. Demostrar que si
--    a * b = b * a
-- entonces
--    b^n * a = a * b^n 
-- ---------------------------------------------------------------------

example
  {G : Type*} [group G]
  (a : G)
  (b : G)
  (hab : a * b = b * a)
  (n : nat)
  : b^n * a = a * b^n :=
begin
  induction n with m HI,
  { group },
  { calc b^(m+1) * a 
        = b^m * b * a : by group 
    ... = b^m * (b*a) : by group
    ... = b^m * (a*b) : by simp [hab]
    ... = b^m * a * b : by group
    ... = a * b^m * b : by simp [HI]
    ... = a * b^(m+1) : by group },
end

-- Referencia
-- ==========

-- Basado en induction.lean de Clara Löh que se encuentra en
-- https://bit.ly/3upWGTV
