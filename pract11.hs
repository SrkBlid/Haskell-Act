--Se utilizan las ternas de Hoare.
--Para demostrar/derivar un programa imperativo se usa el wp.
--
--p es màs debil que p0 cuando p0 -> p
--ej: 
--    y = 1 o y = 3     p0
--    y <= 3            p
--    wp nos devuelve el màs debil, el p0
-- P -> wp.S.Q == {P}S{Q}
-- wp.skip.Q == Q
-- {P}skip{Q} == [P -> Q]

-- NO LLEGAMOS A DERIVAR CON IMPERATIVO
-- LIBRO DE JAVIER BLANCO: TEMA 17
-- SABER COMO HACER UN WP DEL DO, DEMOSTRAR COTA

--EJERCICIO 1: Encontrar la precondiciòn màs dèbil.
{wp}x := (x-y)*(x+y) {(x+y^2 = 0)}
    [SUSTITUCIÒN]
(((x-y)*(x+y))+y^2 = 0)
    [ARITMETICA]
(x^2+xy-xy-y^2+y^2 = 0)
    [ARITMETICA]
(x^2-y^2+y^2 = 0)
    [ARITMETICA]
x^2 = 0
    [ARITMETICA (RAIZ)]
x = 0
PRECONDICIÒN MÀS DÈBIL: x = 0

{wp} q,r := q+1, r-y {q*y+r = x)}
    [SUSTITUCIÒN]
(q+1)*y+(r-y) = x
    [ARITMETICA]
q*y+y+r-y = x
    [ARITMETICA]
q*y+r = x
PRECONDICIÒN MÀS DÈBIL: q*y+r = x

--Esta se resuelve por concatenaciòn, de atras para adelante.
{wp}
a := a == b; (s1)
b := a == b; (s2)
a := a == b; (s3)
{(a == B)∧(b == A)}
    [WP s3, s2, s1]
wp.(a := a == b).(wp.(b := a == b).(wp.(a := a == b).((a == B)∧(b == A))))
    [SUSTITUCIÒN WP]
wp.(a := a == b).(wp.(b := a == b).(((a == b) == B)∧(b == A)))
    [SUSTITUCIÒN WP]
wp.(a := a == b).((a == (a == b)) == B)∧((a == b) == A))
    [ASOCIATIVA ==]
wp.(a := a == b).(((a == a) == b) == B)∧((a == b) == A))
    [LÒGICA]
wp.(a := a == b).((True == b) == B)∧((a == b) == A))
    [LÒGICA]
wp.(a := a == b).(b == B)∧((a == b) == A))
    [SUSTITUCIÒN WP]
(b == B)∧(((a == b) == b) == A)
    [ASOCIATIVA ==]
(b == B)∧((a == (b == b)) == A)
    [LÒGICA]
(b == B)∧((a == True) == A)
    [LÒGICA
(b == B)∧(a == A)
PRECONDICIÒN MÀS DÈBIL: (b == B)∧(a == A)

--EJERCICIO 2: Càlcular expresiones de E
--1ro
{A = q*B+r} q := E; r := r-B {A = q*B+r}
    [ESPECIFICACIÒN WP]
A = q*B+r -> wp.(q := E; r := r-B)(A = q*B+r)
    [SUSTITUCIÒN WP]
A = q*B+r -> A = E*B+(r-B)
    [REEMPLAZO PRECONDICIÒN/LEIBNITZ]
A = q*B+r -> q*B+r = E*B+r-B
    [ARITMETICA]
A = q*B+r -> q*B = E*B-B
    [ARTIMETICA]
A = q*B+r -> q*B = E*B-B
    [ARITMETICA]
A = q*B+r -> (q*B+B)/B = E
    [ARITMETICA]
A = q*B+r -> B(q+1)/B = E
    [ARTIMETICA]
A = q*B+r -> q+1 = E
E = q+1

CORROBORAMOS
A = q*B+r -> A = E*B+(r-B)
    [REEMPLAZO E]
A = q*B+r -> A = (q+1)*B+(r-B)
    [ARITMETICA]
A = q*B+r -> A = B*q+B+(r-B)
    [ARITMETICA]
A = q*B+r -> A = q*B+r
    [LÒGICA]
True

--2do
{x*y+p*q = N} x := x-p; q := E {x*y+p*q = N}
    [ESPECIFICACIÒN WP]
x*y+p*q = N -> wp.(x := x-p; q := E).(x*y+p*q = N)
    [SUSTITUCIÒN WP]
x*y+p*q = N -> (x-p)*y+p*E = N
    [ARITMETICA]
x*y+p*q = N -> x*y-p*y+p*E = N
    [LEIBNITZ]
x*y+p*q = N -> x*y-p*y+p*E = x*y+p*q
    [ARITMETICA]
x*y+p*q = N -> -p*y+p*E = p*q
    [ARITMETICA]
x*y+p*q = N -> E = (p*q+p*y)/p
    [ARITMETICA (FACTOR COMUN P)]
x*y+p*q = N -> E = p(q+y)/p
    [ARTIMETICA]
x*y+p*q = N -> E = q+y
E = q+y

CORROBORAMOS
x*y+p*q = N -> x*y-p*y+p*E = N
    [REEMPLAZAMOS E]
x*y+p*q = N -> x*y-p*y+p*(q+y) = N
    [ARITMETICA]
x*y+p*q = N -> x*y-p*y+p*q+p*y = N
    [ARITMETICA]
x*y+p*q = N -> x*y+p*q = N

--EJERCICIO 3: Demostrar la correcciòn del programa
--P -> wp.S.Q, vamos a llegar a un P0 que es la precondiciòn màs dèbil, si llegamos a un P -> P, entonces es True y se demuestra la correcciòn del programa.

{x = A ∧ y = B}
x := x-y;
y := x+y;
x := y-x;
{x = B ∧ y = A}

x = A ∧ y = B -> wp.(x := x-y).(wp.(y := x+y).(wp.(x := x-y).(x = B ∧ y = A)))
    [SUSTITUCIÒN WP]
x = A ∧ y = B -> wp.(x := x-y).(wp.(y := x+y).(x-y = B ∧ y = A))
    [SUSTITUCIÒN WP]
x = A ∧ y = B -> wp.(x := x-y).(x-x+y = B ∧ x+y = A)
    [ALGORITMICA]
x = A ∧ y = B -> wp.(x := x-y).(y = B ∧ x+y = A)
    [SUSTITUCIÒN WP]
x = A ∧ y = B -> y = B ∧ x-y+y = A
    [ARITMETICA]
x = A ∧ y = B -> y = B ∧ x = A
    [LÒGICA]
True

--EJERCICIO 4: Demostrar la correcciòn de los sig. programas
--1ro
{True}
if x >= y -> skip
[] x <= y -> x,y := x,y
{x >= y}

-- [P -> (B0 v B1 v...v Bn)] ∧ {P ∧ B0}S0{Q} ∧ {P ∧ B1}S1{Q}
-- ∧ ... ∧ {P ∧ Bn}Sn{Q}
-- VISTO COMO WP:
-- wp.if.Q == [(B0 v B1 v..v Bn) ∧ (B0 -> wp.S0.Q) ∧
--  ... ∧ (Bn -> wp.Sn.Q)]
True -> (x >= y v x <= y)
∧ (True ∧ x >= y) -> wp.skip.(x >= y)
∧ (True ∧ x <= y) -> wp.(x,y := x,y)(x >= y)
--SE DEBEN SATISFACER TODAS

True -> (x >= y v x <= y)
    [LÒGICA]
True -> True
    [LÒGICA]
True

(True ∧ x >= y) -> wp.skip.(x >= y)
    [DEF WP SKIP]
True ∧ x >= y -> x >= y
    [LÒGICA]
x >= y -> x >= y
    [LÒGICA]
True

(True ∧ x <= y) -> wp.(x,y := y,x)(x >= y)
    [SUSTITUCIÒN WP]
(True ∧ x <= y) -> x >= y
    [LÒGICA]
x <= y -> y >= x
    [LÒGICA]
True

--COMO SE CUMPLEN TODOS LOS CASOS, LA CORRECCIÒN DEL PROGRAMA ES VÀLIDA.

--2d0
{True}
x, y := y*y, x*x;
if x >= y -> x := x+1
[] x <= y -> y := y-x
fi
{x >= 0 ∧ y >= 0}

--P -> wp.S1(wp.S2.Q)
--S1 = x,y := y*y, x*x;
--S2 = if

--S2
wp.if.Q
(x >= y v x <= y)
∧ (x >= y -> wp.(x := x+1).(x >= 0 ∧ y >= 0))
∧ (x <= y -> wp.(y := y-x).(x >= 0 ∧ y >= 0))

(x >= y v x <= y)
    [LÓGICA]
True

x >= y -> wp.(x := x+1).(x >= 0 ∧ y >= 0)
    [SUSTITUCIÓN WP]
x >= y -> x+1 >= 0 ∧ y >= 0
    [LEIBNITZ, TRANSITIVIDAD]
x >= y -> x+1 >= y
    [LÓGICA]
True

x <= y -> wp.(y := y-x).(x >= 0 ∧ y >= 0)
    [SUSTITUCIÓN WP]
x <= y -> x >= 0 ∧ y-x >= 0
    [LEIBNITZ, TRANSITIVIDAD]
x <= y -> x <= y-x
    [LÓGICA]
True

S2 = True
--P -> wp.S1.True

True -> wp.(x,y := y*y, x*x).True
    [SUSTITUCIÓN WP]
True -> True
    [LÓGICA]
True

--3ro
{True}
if not a or b -> a := not a
[] a or not b -> b := not b
fi
{a v b}

wp.if.Q
(not a or b) v (a or not b)
∧ (not a or b -> wp.(a := not a).(a v b))
∧ (a or not b -> wp.(b := not b).(a v b))

(not a or b) v (a or not b)
    [ASOCIATIVA v]
(not a or a) v (b or not b)
    [LÓGICA]
True v True
    [LÓGICA]
True

not a or b -> wp.(a := not a).(a v b)
    [SUSTITUCIÓN WP]
not a or b -> not a v b
    [LÓGICA]
True

a or not b -> wp.(b := not b).(a v b)
    [SUSTITUCIÓN WP]
a or not b -> a v not b
    [LÓGICA]
True

--4ta
--USAMOS EL TEOREMA DEL DO
-- Inicialización: {P} S {I}
-- Postcondición: I ∧ -B0 ∧ ... ∧ -Bn -> Q
-- Invariante: {Bi ∧ I} Si {I}
-- Variante(a): I ∧ Bi -> v >= 0
-- Variante(b): {I ∧ Bi ∧ v = A} Si {v < A}

{N >= 0}
x := 0
do x <> N -> x := x+1
od
{x = N}

INICIALIZACIÓN
x = 0
N = 5
0 <> 5 -> 0 <- 1
1 <> 5 -> 1 <- 2 
...
I = x <= N
--I: Invariante, condición que se cumple antes y despues de cada ciclado.

--{P} S {I}
{N >= 0} x := 0 {x <= N}
    [IMPLEMENTACIÓN WP]
N >= 0 -> wp.(x := 0).(x <= N)
    [SUSTITUCIÓN WP]
N >= 0 -> 0 <= N
    [LÓGICA]
True

POSTCONDICIÓN
--I ∧ -B0 ∧ ... ∧ -Bn -> Q
x <= N ∧ x = N -> x = N
    [LEIBNITZ]
True

INVARIANTE
--{Bi ∧ I} Si {I}
{x <> N ∧ x <= N} x := x+1 {x <= N}
    [IMPLEMENTACIÓN WP]
x <> N ∧ x <= N -> wp.(x := x+1).(x <= N)
    [SUSTITUCIÓN WP]
x <> N ∧ x <= N -> x+1 <= N
    [LEIBNITZ (True)]
    --Cómo x <> N, por lo que x < N ... entonces x+1 es menor o igual a N.
True

VARIANTE(A)
--I ∧ Bi -> v >= 0
--v = expresión númerica que disminuye su tamaño en cada ciclo, en este caso:
v = N-x
x <= N ∧ x <> N -> N-x >= 0
    [ARITMETICA]
x <= N ∧ x <> N -> N >= x
    [ARITMETICA]
x <= N ∧ x <> N -> x <= N
    [LEIBNITZ]
True

VARIANTE(B)
--{I ∧ Bi ∧ v = A} Si {v < A}
v = N-x
{x <= N ∧ x <> N ∧ N-x = A} x := x+1 {N-x < A}
    [IMPLEMENTACIÓN WP]
x <= N ∧ x <> N ∧ N-x = A -> wp.(x := x+1).(N-x < A)
    [SUSTITUCIÓN WP]
x <= N ∧ x <> N ∧ N-x = A -> N-(x+1) < A
    [ARITMETICA]
x <= N ∧ x <> N ∧ N-x = A -> N-x-1 < A
    [ARITMETICA]
x <= N ∧ x <> N ∧ N-x = A -> N-x < A+1
    [LEIBNITZ]
x <= N ∧ x <> N ∧ N-x = A -> A < A+1
    [LÓGICA, obviamente A va a ser menor que A+1]
True