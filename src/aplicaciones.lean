-- aplicaciones.lean
-- Aplicaciones inyectivas. suprayectivas y biyectivas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-junio-2022
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio. Importar la librería de tácticas-
-- ---------------------------------------------------------------------

import tactic

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir la lógica clásica.
-- ---------------------------------------------------------------------

open classical  

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar X, Y y Z variables de tipo-
-- ---------------------------------------------------------------------

variables {X Y Z : Type*}

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función es_inyectiva tal (es_inyectiva f)
-- expresa que f es inyectiva.
-- ---------------------------------------------------------------------

def es_inyectiva 
  (f : X → Y) := 
  ∀ x x', f x = f x' → x = x'

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función es_suprayectiva tal (es_suprayectiva f)
-- expresa que f es suprayectiva.
-- ---------------------------------------------------------------------

def es_suprayectiva 
  (f : X → Y) := 
  ∀ y, ∃ x, f x = y  

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función es_biyectiva tal (es_biyectiva f)
-- expresa que f es biyectiva.
-- ---------------------------------------------------------------------

def es_biyectiva
  (f : X → Y) := 
  es_inyectiva f ∧ es_suprayectiva f    

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que las funciones biyectivas son inyectivas.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  {f : X → Y}
  (f_biyectiva : es_biyectiva f)
  : es_inyectiva f := 
and.elim_left f_biyectiva

-- 2ª demostración
-- ===============

lemma biy_iny
  {f : X → Y}
  (f_biyectiva: es_biyectiva f)
  : es_inyectiva f := 
f_biyectiva.1

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que las funciones biyectivas son suprayectivas.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  {f : X → Y}
  (f_biyectiva : es_biyectiva f)
  : es_suprayectiva f := 
and.elim_right f_biyectiva

-- 2ª demostración
-- ===============

lemma biy_supr
  {f : X → Y}
  (f_biyectiva : es_biyectiva f)
  : es_suprayectiva f := 
f_biyectiva.2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es suprayectiva e inyectiva, entonces
-- es biyectiva.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  {f : X → Y}
  (f_suprayectiva : es_suprayectiva f)
  (f_inyectiva : es_inyectiva f)
  : es_biyectiva f :=
and.intro f_inyectiva f_suprayectiva

-- 2ª demostración
-- ===============

lemma supr_iny_biy
  {f : X → Y}
  (f_suprayectiva : es_suprayectiva f)
  (f_inyectiva : es_inyectiva f)
  : es_biyectiva f :=
⟨f_inyectiva, f_suprayectiva⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si (g ∘ f) es inyectiva, entonces f es
-- inyectiva. 
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  {f : X → Y}
  {g : Y → Z}
  (gf_inyectiva : es_inyectiva (g ∘ f))
  : es_inyectiva f :=  
begin
  intros x x' f_xx',
  apply gf_inyectiva,
  simp [f_xx'],
end

-- 2ª demostración
-- ===============

lemma iny_comp_iny_primera 
  {f : X → Y}
  {g : Y → Z}
  (gf_inyectiva : es_inyectiva (g ∘ f))
  : es_inyectiva f :=  
begin
  assume x  : X, 
  assume x' : X, 
  assume f_xx' : f x = f x',
  have gf_xx' : (g ∘ f) x = (g ∘ f) x', from 
    calc (g ∘ f) x = g (f x)    : by simp
               ... = g (f x')   : by simp [f_xx']
               ... = (g ∘ f) x' : by simp,
  show x = x', 
    { apply gf_inyectiva, 
      apply gf_xx'},
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si (g ∘ f) es suprayectiva, entonces f es
-- suprayectiva. 
-- ---------------------------------------------------------------------

lemma supr_comp_supr_segunda
  {f : X → Y}
  {g : Y → Z}
  (gf_suprayectiva : es_suprayectiva (g ∘ f))
  : es_suprayectiva g  := 
begin
  assume z : Z,
  rcases gf_suprayectiva z with ⟨ x : X, gf_x_z : (g ∘ f) x = z⟩,
  let y : Y := f x,
  use y,
  show g y = z, from
    calc g y = g (f x)   : by simp
         ... = (g ∘ f) x : by simp
         ... = z         : by exact gf_x_z,
end  

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si (f ∘ f) es biyectiva, entonces f es
-- biyectiva. 
-- ---------------------------------------------------------------------

-- 2ª demostración
-- ===============

example
  (f : X → X)
  (ff_biyectiva : es_biyectiva (f ∘ f))
  : es_biyectiva f :=
begin
  apply supr_iny_biy,
  { apply supr_comp_supr_segunda,
    apply biy_supr,
    exact ff_biyectiva, },
  { apply iny_comp_iny_primera,
    apply biy_iny,
    exact ff_biyectiva, },
end

-- 2ª demostración
-- ===============

lemma cuadrado_biy_biy
  (f : X → X)
  (ff_biyectiva : es_biyectiva (f ∘ f))
  : es_biyectiva f :=
begin
  have f_inyectiva : es_inyectiva f, from
    begin
      have ff_inyectiva : es_inyectiva (f ∘ f), 
        by exact biy_iny ff_biyectiva,
      show _,
        by exact iny_comp_iny_primera ff_inyectiva,
    end,
  have f_suprayectiva: es_suprayectiva f, from
    begin
      have ff_suprayectiva : es_suprayectiva (f ∘ f),
        by exact biy_supr ff_biyectiva,
      show _,
        by exact supr_comp_supr_segunda ff_suprayectiva,     
    end,
  show es_biyectiva f, 
    by exact supr_iny_biy f_suprayectiva f_inyectiva,
end      

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el tipo A con los constructores A1, A2 y A3.
-- ---------------------------------------------------------------------

inductive A : Type
  | A1
  | A2
  | A3

open A

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--   f ; A -> A
-- tal que 
--   f A1 = A1, 
--   f A2 = A1 y
--   f A3 = A2.
-- ---------------------------------------------------------------------

def f : A → A
  | A1 := A1
  | A2 := A1
  | A3 := A2

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que f no es inyectiva.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  : ¬ es_inyectiva f :=
begin
  unfold es_inyectiva,
  simp,
  use [A1, A2],
  split,
  { dsimp [f],
    refl, },
  { simp, },
end

-- 2ª demostración
-- ===============

lemma f_no_iny 
  : ¬ es_inyectiva f :=
begin
  let x  := A1,
  let x' := A2,
  have f_xx'_x_diferente_x' : f x = f x' ∧ x ≠ x', from
    begin
      have f_xx' : f x  = f x', by simp [f],
      have x_diferente_x' :  x ≠ x', by finish,
      show _, by exact and.intro f_xx' x_diferente_x',
    end,
  show ¬ es_inyectiva f, from
    begin
      simp only [es_inyectiva, not_forall], 
      use x,
      use x',
      exact f_xx'_x_diferente_x',
    end
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que f no es suprayectiva.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  : ¬ es_suprayectiva f:=
begin
  unfold es_suprayectiva,
  rw not_forall,
  use A3,
  rw not_exists,
  intro x,
  cases x,
  { simp [f], },
  { simp [f], },
  { simp [f], },
end

-- 2ª demostración
-- ===============

example
  : ¬ es_suprayectiva f:=
begin
  unfold es_suprayectiva,
  push_neg,
  use A3,
  intro x,
  cases x; finish,
end

-- 3ª demostración
-- ===============

lemma f_no_es_supr
  : ¬ es_suprayectiva f:=
begin
  simp only [es_suprayectiva, not_forall],
  show ∃ y : A, ¬(∃ x : A, f x = y), by
    begin
      use A3,
      have A3_no_es_imagen : ∀ x : A, ¬ f x = A3, from
        begin
          assume x : A,
          cases x,
            case A1 : {simp [f] }, 
            case A2 : {simp [f] },
            case A3 : {simp [f] },
        end,
      show _, 
        by {simp only [not_exists], exact A3_no_es_imagen}
    end 
end

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el tipo B con los constructores B1 y B2.
-- ---------------------------------------------------------------------

inductive B 
  | B1
  | B2

open B

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función 
--    g : B → B
-- tal que 
--    g B1 = B2 
--    g B2 = B1
-- ---------------------------------------------------------------------

def g : B → B
  | B1 := B2
  | B2 := B1

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que g es biyectiva.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  : es_biyectiva g := 
begin
  apply supr_iny_biy,
  { unfold es_suprayectiva,
    intro y,
    cases y,
    { use B2,
      simp [g], },
    { use B1,
      simp [g], }},
  { unfold es_inyectiva,
    intros x x' gxx',
    cases x,
    { cases x',
      { refl, },
      { dsimp [g] at gxx',
        rw gxx', }},
    { cases x',
      { dsimp [g] at gxx',
        rw gxx', },
      { refl, }}},
end

-- 2ª demostración
-- ===============

lemma g_es_biyectiva 
  : es_biyectiva g := 
begin
  have g_es_inyectiva : es_inyectiva g, from 
    begin
      assume x  : B,
      assume x' : B,
      assume g_xx' : g x = g x',
      cases x,
        case B1 : begin cases x', finish, finish end,
        case B2 : begin cases x', finish, finish end,
    end,
  have g_es_suprayectiva : es_suprayectiva g, from
    begin
      assume y : B,
      cases y,
        case B1 : begin use B2, finish end,
        case B2 : begin use B1, finish end,
    end,
  show _,
    by exact supr_iny_biy g_es_suprayectiva g_es_inyectiva
end

-- ---------------------------------------------------------------------
-- Ejercicio. Definir el conjunto conj_123 cuyos elementos son los
-- números naturales 1, 2 y 3.
-- ---------------------------------------------------------------------

def conj_123 : set ℕ := 
  {1,2,3}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    1 ∈ conj_123
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : 1 ∈ conj_123  :=
begin
  fconstructor,
  refl,
end

-- 2ª demostración
-- ===============

lemma uno_en_123 : 1 ∈ conj_123 := 
by {fconstructor, refl}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    2 ∈ conj_123
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : 2 ∈ conj_123  :=
begin
  apply or.inr,
  fconstructor,
  refl,
end

-- 2ª demostración
-- ===============

lemma dos_en_123 : 2 ∈ conj_123 := 
by {apply or.inr, simp}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    3 ∈ conj_123
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example : 3 ∈ conj_123  :=
begin
  apply or.inr,
  apply or.inr,
  fconstructor,
end

-- 2ª demostración
-- ===============

lemma tres_en_123 : 3 ∈ conj_123 := 
by {apply or.inr, simp}

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    const1 : conj_123 → conj_123 
-- que aplica todos los elementos en el 1.
-- ---------------------------------------------------------------------

def const1 : conj_123 → conj_123 := 
λ ⟨x, _⟩, ⟨1, uno_en_123⟩ 

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función 
--    h : conj_123 → conj_123
-- que aplica el 3 en el 2 y los demás en el 1.
-- ---------------------------------------------------------------------

def h : conj_123 → conj_123 := 
λ ⟨x, x_in_123⟩, 
  if x = 3 then ⟨ 2, dos_en_123 ⟩
           else ⟨ 1, uno_en_123 ⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que h no es inyectiva.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  : ¬ es_inyectiva h :=
begin
  unfold es_inyectiva,
  push_neg,
  let x1 : ↥conj_123 := ⟨ 1, uno_en_123 ⟩,
  let x2 : ↥conj_123 := ⟨ 2, dos_en_123 ⟩,
  use [x1, x2],
  split,
  { simp [h], },
  { simp, },
end

-- 2ª demostración
-- ===============

lemma h_no_es_inyectiva 
  : ¬ es_inyectiva h :=
begin
  let x1 : ↥conj_123 := ⟨ 1, uno_en_123 ⟩,
  let x2 : ↥conj_123 := ⟨ 2, dos_en_123 ⟩,
  refine not_forall.mpr _,
  use x1,
  refine not_forall.mpr _,
  use x2,
  finish,
end

-- =====================================================================
-- § Ejercicios                                                       --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio 2.E.1.a. Definir la aplicación identidad
-- ---------------------------------------------------------------------

def apl_id 
  (X : Type*)
  : X → X := 
λ x, x

-- ---------------------------------------------------------------------
-- Ejercicio 2.E.1.b. Demostrar que la aplicación identidad es
-- biyectiva.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (X : Type*)
  : es_biyectiva (apl_id X) :=
begin
  apply supr_iny_biy,
  { unfold es_suprayectiva,
    intro y,
    use y,
    simp [apl_id], },
  { unfold es_inyectiva,
    intros x x' f_xx',
    simp [apl_id] at f_xx',
    exact f_xx', },
end

-- 2ª demostración
-- ===============

lemma id_biyectiva 
  (X : Type*)
  : es_biyectiva (apl_id X) :=
begin
  let f : X → X := apl_id X,
  have id_iny : es_inyectiva f, from
    begin
      assume x x' : X,
      assume f_xx' : f x = f x',
      show x = x', by 
        calc x = f x  : by refl
           ... = f x' : by simp [f_xx']
           ... = x'   : by refl,
    end,
  have id_supr : es_suprayectiva f, from
    begin
      assume y : X,
      use y,
      show f y = y, by refl,
    end,
  show _, 
    by exact supr_iny_biy id_supr id_iny,
end  

-- ---------------------------------------------------------------------
-- Ejercicio 2:E.2. Demostrar que la composición de funciones inyectivas
-- es inyectiva.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (f : X → Y)
  (g : Y → Z)
  (f_inyectiva : es_inyectiva f)
  (g_inyectiva : es_inyectiva g)
  : es_inyectiva (g ∘ f) :=
begin
  unfold es_inyectiva,
  intros x x' gf_xx',
  apply f_inyectiva,
  apply g_inyectiva,
  calc g (f x) = (g ∘ f) x  : rfl
           ... = (g ∘ f) x' : gf_xx'
           ... = g (f x')   : rfl
end

-- 2ª demostración
-- ===============

lemma comp_iny_es_iny 
  (f : X → Y)
  (g : Y → Z)
  (f_inyectiva : es_inyectiva f)
  (g_inyectiva : es_inyectiva g)
  : es_inyectiva (g ∘ f) :=
begin
  assume x x' : X,
  assume gf_xx' : (g ∘ f) x = (g ∘ f) x',
  show x = x', by
    begin
      have f_xx' : f x = f x', from
        begin
          have g_fxfx' : g (f x) = g (f x'), from
            calc g (f x) = (g ∘ f) x  : by simp
                     ... = (g ∘ f) x' : by simp[gf_xx']
                     ... = g (f x')   : by simp,
          show _, 
            by {apply g_inyectiva, apply g_fxfx'},
        end, 
      show _, 
        by {apply f_inyectiva, apply f_xx'},
    end
end      

-- ---------------------------------------------------------------------
-- Ejercicio 2.E.3.a. Sea f : X → Y tal que existen x, x' ∈ X tales que 
-- x ≠ x' y f x = f x'. Demostrar que f no es inyectiva.
-- ---------------------------------------------------------------------

lemma CS_inyectiva 
  (f : X → Y)
  (x : X)
  (x' : X)
  (x_neq_x' : x ≠ x')
  (f_xx' : f x = f x')
  : ¬ es_inyectiva f := 
begin
  simp only [es_inyectiva, not_forall],
  use [x, x'], 
  finish,
end

-- ---------------------------------------------------------------------
-- Ejercicio 2.E.3.a.  Usar el lema anterior para demostrar que f no es
-- inyectiva.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  : ¬ es_inyectiva f :=
begin
  apply CS_inyectiva f A1 A2,
  { trivial, },
  { simp [f] },
end


-- 2ª demostración
-- ===============

example
  : ¬ es_inyectiva f :=
begin
  let x  : A := A1,
  let x' : A := A2,
  have x_diferente_x' : x ≠ x', by finish,
  have f_xx' : f x = f x', by refl,
  show _, 
    by exact (CS_inyectiva f x x' x_diferente_x' f_xx'),
end

-- ---------------------------------------------------------------------
-- Ejercicio 2.E.4.a. Demostrar que (g ∘ g = id).
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  : g ∘ g = apl_id B :=
begin
  ext1,
  simp [apl_id],
  cases x,
  { calc g (g B1) = g B2 : by simp [g]
              ... = B1   : by simp [g] },
  { calc g (g B2) = g B1 : by simp [g]
              ... = B2   : by simp [g] },
end

-- 2ª demostración
-- ===============

lemma gg_id 
  : g ∘ g = apl_id B :=
begin
  have g_id : ∀ x : B, (g ∘ g) x = apl_id B x, from
    begin
       assume x : B,
       cases x,
         {finish},
         {finish},
    end,
  show _, by {ext1, tauto},
end    

-- ---------------------------------------------------------------------
-- Ejercicio 2.E.4.a. Demostrar que g es biyectiva.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  : es_biyectiva g :=
begin
  apply cuadrado_biy_biy g,
  convert id_biyectiva B,
  exact gg_id,
end

-- 2ª demostración
-- ===============

example
  : es_biyectiva g :=
begin
  have gg_biy : es_biyectiva (g ∘ g), from
    begin
      have gg_id : g ∘ g = apl_id B, by exact gg_id,
      show _, by {simp only [gg_id], apply id_biyectiva B},
    end, 
  show _, by exact (cuadrado_biy_biy g gg_biy),
end    

-- Referencia
-- ==========

-- Basado en "Injective, surjective, bijective maps" de Clara Löh que se
-- encuentra en https://bit.ly/3xzYqun
