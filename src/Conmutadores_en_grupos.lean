-- Conmutadores_en_grupos.lean
-- Conmutadores en grupos.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 9-julio-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Importar la libería de táctica.
-- ---------------------------------------------------------------------

import tactic

-- ---------------------------------------------------------------------
-- Ejercicio. Import la libería básica de grupos.
-- ---------------------------------------------------------------------

import algebra.group.basic 

-- ---------------------------------------------------------------------
-- Ejercicio. Habilitar la lógica clásica.
-- ---------------------------------------------------------------------

open classical

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar G y H como variables sobre grupos.
-- ---------------------------------------------------------------------

variables {G : Type*} [group G]
variables {H : Type*} [group H]

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar g y h como variables sobre elementos de G.
-- ---------------------------------------------------------------------

variables (g h : G)

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    conmutador : G → G → G
-- tal que (gonmutador g h) es es conmutador de g y h; es decir, 
--    g * h * g⁻¹ * h⁻¹
-- ---------------------------------------------------------------------

def conmutador 
  (g : G)
  (h : G) 
:= g * h * g⁻¹ * h⁻¹

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que las imágenes por homorfismo de conmutadores
-- son conmutadores.
-- ---------------------------------------------------------------------

lemma conmutador_hom
  (f : monoid_hom G H)
  : f (conmutador g h) = conmutador (f g) (f h) := 
begin
  calc f (conmutador g h) 
       = f (g * h * g⁻¹ * h⁻¹) 
       : by simp [conmutador]
  ... = f g * f h * f (g⁻¹) * f (h⁻¹) 
      : by simp [mul_hom.map_mul]
  ... = f g * f h * (f g)⁻¹ * (f h)⁻¹ 
      : by {congr; simp only [monoid_hom.map_inv]}
  ... = conmutador (f g) (f h) 
      : by simp [conmutador],
end      

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    g^3 = g * g * g
-- ---------------------------------------------------------------------

lemma cubo : 
  g^3 = g * g * g := 
by group

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el cubo de un conmutador se puede escribir
-- como el producto de dos conmutadores.
-- ---------------------------------------------------------------------

lemma cubo_de_conmutador
  (a : G) {A : G} {A_def : A = a⁻¹}
  (b : G) {B : G} {B_def : B = b⁻¹}
  : (conmutador a b)^3 = 
    conmutador (a*b*A) (B*a*b*A^2) * conmutador (B*a*b) (b^2) :=
begin
  unfold conmutador,
  simp [cubo, A_def, B_def], 
  group,
end

-- Referencia
-- ==========

-- Basado en commutator.lean de Clara Löh que se encuentra en
-- https://bit.ly/3uApeua
