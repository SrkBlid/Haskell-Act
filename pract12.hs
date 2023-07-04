--ESTA PRACTICA ES PARA EL FINAL, CON ESTO Y EL LIBRO DE JAVIER BLANCO, TOMAN ALGO ASI EN EL FINAL (Màximo comùn multiplo y asi, tipo ejercicio 3)

------------------------------------------------------------
--EJERCICIO 12: Derivar dos programas que calculen r = X^Y a partir de:
--Precondiciòn P: {x = X ∧ y = Y ∧ x >= 0 ∧ y >= 0}
--Postcondiciòn Q: {r = X^Y}
--Invariante I: {y >= 0 ∧ r*x^y = X^Y}

--HAY QUE RESOLVER CON EL TEOREMA DEL DO
--(a)
--exp (x,y) = (y = 0 -> 1
--						[]y /= 0 -> x*exp(x, y-1)
--						)

--INICIALIZACIÒN: Sirve para ver el valor de S
--REGLA: Inicializamos todo lo que esta en el invariante y no en la precondiciòn
{P}S{I}
	[DEF WP]
P -> wp.S.I
	[DEF P, DEF I]
x = X ∧ y = Y ∧ x >= 0 ∧ y >= 0 -> wp.(r := E).(y >= 0 ∧ r*x^y = X^Y)
	[DEF ASIGNACIÒN WP, SUPONGO ANTECEDENTE]
y >= 0 ∧ E*x^y = X^Y
	[LEIBNITZ, NEUTRO ∧]
E*X^Y = X^Y
	[ARITMETICA]
E = X^Y/X^Y
	[ARITMETICA]
E = 1

P..
	r := 1
do

--POSTCONDICIÒN: Sirve para sacar las guardas
(I ∧ -B0 ∧..∧ -Bn) -> Q
	[DEF I, DEF Q]
(y >= 0 ∧ r*x^y = X^Y ∧ E0) -> r = X^Y
--PARA QUE SE CUMPLA r*x^y = r entonces y = 0, esa es nuestra B0
	[RANGO Y]
(y >= 0 ∧ r*x^0 = X^Y ∧ y /= 0) -> r = X^Y
	[ARITMETICA]
(y >= 0 ∧ r = X^Y ∧ y /= 0) -> r = X^Y
	[DEF R]
(y >= 0 ∧ r = X^Y ∧ y /= 0) -> r = r
	[LÒGICA]
(y >= 0 ∧ r = X^Y ∧ y /= 0) -> True

P..
	r := 1
do y /= 0

--INVARIANTE: Sirve para sacar Sn
{Bn ∧ I}Sn{I}
	[DEF WP]
Bn ∧ I -> wp.Sn.I.
	[DEF Bn, DEF I]
y /= 0 ∧ y >= 0 ∧ r*x^y = X^Y -> wp.(r, y := E, y-1).(y >= 0 ∧ r*x^y = X^Y)
	[DEF ASIGNACIÒN WP, ASUMO PREDICADO]
y-1 >= 0 ∧ E*x^y-1 = X^Y
	[ARITMETICA]
y >= 1 ∧ E*x^y-1 = X^Y
	[LEIBNITZ, NEUTRO ∧]
E*(x^y)/x = r*x^y
	[ARITMETICA]
E*x^y = r*x^y*x
	[ARITMETICA]
E = (r*x^y*x)/x^y
	[ARITMETICA]
E = r*x

P..
	r := 1
do y /= 0 -> r, y := r*x, y-1

--v = y, YA QUE y SE VA ACHICANDO SOLO EN CADA CICLO
--VARIANTE(A)
Bn ∧ I -> v >= 0
	[DEF Bn, DEF I, DEF v]
y /= 0 ∧ y >= 0 ∧ r*x^y = X^Y -> y >= 0
	[LEIBNITZ]
y /= 0 ∧ y >= 0 ∧ r*x^y = X^Y -> True
	[LÒGICA]
True

--VARIANTE(B)
{Bn ∧ I ∧ v = A} Sn {v < A}
	[DEF WP]
Bn ∧ I ∧ v = A -> wp.Sn.(v < A)
	[DEF Bn, DEF I, DEF v, DEF Sn]
y /= 0 ∧ y >= 0 ∧ r*x^y = X^Y ∧ y = A -> wp.(r, y := r*x, y-1).(y < A)
	[DEF ASIGNACIÒN WP, ASUMO PREDICADO]
y-1 < A
	[DEF A]
y-1 < y
	[LÒGICA]
True

--Precondiciòn P: {x = X ∧ y = Y ∧ x >= 0 ∧ y >= 0}
--Postcondiciòn Q: {r = X^Y}
--Invariante I: {y >= 0 ∧ r*x^y = X^Y}

--(b)
--exp (x,y) = (y = 0 -> 1
--						[]y /= 0 -> (y mod 2 = 0 -> exp(x*x, y div 2)
--												[]y mod 2 = 1 -> x*exp(x, y-1)
--												)
--						)
y = y/2

--INICIALIZACIÒN
{P}S{I}
	[DEF WP]
P -> wp.S.I
	[DEF P, DEF I]
x = X ∧ y = Y ∧ x >= 0 ∧ y >= 0 -> wp.(r := E).(y >= 0 ∧ r*x^y = X^Y)
	[ASUMO PREDICADO, DEF ASIGNACIÒN WP]
y >= 0 ∧ E*x^y = X^Y
	[LÒGICA, NEUTRO ∧, LEIBNITZ]
E*X^Y = X^Y
	[ARITMETICA]
E = 1

P..
	r := 1
do

--POSTCONDICIÒN
(P ∧ -B0 ∧..∧ -Bn) -> Q
	[DEF P, DEF Q]
(x = X ∧ y = Y ∧ x >= 0 ∧ y >= 0 ∧ -B0 ∧ -B1) -> r = X^Y

FALTA TERMINARLO PERO ES CASI TODO LO MISMO

------------------------------------------------------------
--EJERCICIO 3:
-- (A) Derivar un programa que deermine si todos los elementos de A son positivos.
-- Empezamos pensando P, Q

{P : N >= 0}
{Q : r = <∀j : 0 <= j < N : A.j >= 0>}

-- Usamos la teoria para sacar invariantes para obtenerlo, el màs clasico es cambio de constante por variable

{I : r = <∀j : 0 <= j < i : A.j >= 0> ∧ 0 <= i <= N}

-- A partir de aca largamos resolviendo como hicimos en los ejercicios anteriores

--INICIALIZACIÒN
{P}S{I}
	[DEF WP]
P -> wp.S.I
	[DEF P, DEF I]
N >= 0 -> wp.(r, i := True, 0).(r = <∀j : 0 <= j < i : A.j >= 0> ∧ 0 <= i <= N)
	[ASUMO PREDICADO, DEF ASIGNACIÒN WP]
True = <∀j : 0 <= j < 0 : A.j >= 0> ∧ 0 <= 0 <= N
	[RANGO VACIO, LEIBNITZ]
True = True ∧ True
	[LÒGICA]
True

P
	r, i := True, 0
	do
	od

--POSTCONDICIÒN
(P ∧ -B0 ∧..∧ -Bn) -> Q
	[DEF P, DEF Q]
(N >= 0 ∧ -B0) -> r = <∀j : 0 <= j < N : A.j >= 0>
	PARA QUE SE CUMPLA: B0 -> i /= N o -B0 -> i = N
	
P
	r, i := True, 0
	do i /= N
	od
	
--INVARIANTE
{I ∧ Bn}Sn{I}
	[DEF WP]
I ∧ Bn -> wp.Sn.I








