--------------------------------------------------------------------------------------
-----------------------------------------2015-----------------------------------------
--------------------------------------------------------------------------------------
-- ¿Qué es el wp? ¿Cuáles son sus propiedades más importantes? Explicar el wp para la asignación y el if.
El wp es la "weakest precondition", es decir, la precondición mas debil que hace valido a la postcondición. Dentro de sus propiedades más importantes nos encontramos con el skip, el := (asignación), el abort.
- := (ASIGNACIÓN): wp.(:=).Q
    Lo que hacemos en la asignación es reemplazar cada elemento que se asigne en la postcondición, es decir: Q(:=)
    EJ: wp.(x = x+1).(2x) = 2(x+1)

- if: wp.if.q
    VERLO, NO ME ACUERDO

--------------------------------------------------------------------------------------
-- Especificar y derivar una función f : [Num] -> Bool, tal que devuelve true cuando siempre que aparece un 0 aparece un 1 en alguna posición posterior, además la cantidad de 0’s y 1’s es la misma. Puede suponer que solo aparecen 0’s o 1’s.
f : [Num] -> Bool
f.xs = <∀i : 0 <= i < #xs ∧ xs.i = 0 : <∃j : 0 <= j < i : xs.j = 1>> && (cantCeros.xs == cantUnos.xs)

cantCeros : [Num] -> Int
cantCeros.xs = <Σi : 0 <= i < #xs ∧ xs.i = 0 : 1>

cantUnos : [Num] -> Int
cantUnos.xs = <Σi : 0 <= i < #xs ∧ xs.i = 1 : 1>

-- DERIVACIONES
-- cantCeros CB = []
cantCeros.[]
    [ESPECIFICACIÓN]
<Σi : 0 <= i < #[] ∧ [].i = 0 : 1>
    [DEF CARDINAL]
<Σi : 0 <= i < 0 ∧ [].i = 0 : 1>
    [RANGO VACIO]
0

-- cantCeros CI = x:xs
-- HI cantCeros.xs = <Σi : 0 <= i < #xs ∧ xs.i = 0 : 1>
cantCeros.(x:xs)
    [ESPECIFICACIÓN]
<Σi : 0 <= i < #(x:xs) ∧ (x:xs).i = 0 : 1>
    [DEF CARDINAL]
<Σi : 0 <= i < 1+#xs ∧ (x:xs).i = 0 : 1>
    [LÓGICA, PARTICIÓN DE RANGO]
<Σi : 0 <= i < 1 ∧ (x:xs).i = 0 : 1> + <Σi : 1 <= i < 1+#xs ∧ (x:xs).i = 0 : 1>
    [RANGO UNITARIO]
1 + <Σi : 1 <= i < 1+#xs ∧ (x:xs).i = 0 : 1>
    [i <- i+1, ARITMETICA, DEF POSICIÓN]
1 + <Σi : 0 <= i < #xs ∧ xs.i = 0 : 1>
    [HI]
1 + cantCeros.xs

-- cantUnos CB = []
cantUnos.[]
    [ESPECIFICACIÓN]
<Σi : 0 <= i < #[] ∧ [].i = 1 : 1>
    [DEF CARDINAL]
<Σi : 0 <= i < 0 ∧ [].i = 1 : 1>
    [RANGO VACIO]
0

-- cantUnos CI = x:xs
-- HI cantUnos.xs = <Σi : 0 <= i < #xs ∧ xs.i = 1 : 1>
cantCeros.(x:xs)
    [ESPECIFICACIÓN]
<Σi : 0 <= i < #(x:xs) ∧ (x:xs).i = 1 : 1>
    [DEF CARDINAL]
<Σi : 0 <= i < 1+#xs ∧ (x:xs).i = 1 : 1>
    [LÓGICA, PARTICIÓN DE RANGO]
<Σi : 0 <= i < 1 ∧ (x:xs).i = 1 : 1> + <Σi : 1 <= i < 1+#xs ∧ (x:xs).i = 1 : 1>
    [RANGO UNITARIO]
1 + <Σi : 1 <= i < 1+#xs ∧ (x:xs).i = 1 : 1>
    [i <- i+1, ARITMETICA, DEF POSICIÓN]
1 + <Σi : 0 <= i < #xs ∧ xs.i = 1 : 1>
    [HI]
1 + cantUnos.xs

-- f CB = []
f.[]
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[] ∧ [].i = 0 : <∃j : 0 <= j < i : [].j = 1>>
    [DEF CARDINAL]
<∀i : 0 <= i < 0 ∧ [].i = 0 : <∃j : 0 <= j < i : [].j = 1>>
    [RANGO VACIO]
True

-- f CI = x:xs
-- HI f.xs = <∀i : 0 <= i < #xs ∧ xs.i = 0 : <∃j : 0 <= j < i : xs.j = 1>>
f.(x:xs)
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #(x:xs) ∧ (x:xs).i = 0 : <∃j : 0 <= j < i : (x:xs).j = 1>>
    [DEF CARDINAL]
<∀i : 0 <= i < 1+#xs ∧ (x:xs).i = 0 : <∃j : 0 <= j < i : (x:xs).j = 1>>
    [LÓGICA, PARTICIÓN DE RANGO]
<∀i : 0 <= i < 1 ∧ (x:xs).i = 0 : <∃j : 0 <= j < i : (x:xs).j = 1>> ∧ <∀i : 1 <= i < 1+#xs ∧ (x:xs).i = 0 : <∃j : 0 <= j < i : (x:xs).j = 1>>
    [RANGO UNITARIO]
<∃j : 0 <= j < 0 : (x:xs).j = 1> ∧ <∀i : 1 <= i < 1+#xs ∧ (x:xs).i = 0 : <∃j : 0 <= j < i : (x:xs).j = 1>>
    [RANGO VACIO]
False ∧ <∀i : 1 <= i < 1+#xs ∧ (x:xs).i = 0 : <∃j : 0 <= j < i : (x:xs).j = 1>>
    [i <- i+1, ARITMETICA, DEF POSICIÓN]
False ∧ <∀i : 0 <= i < #xs ∧ xs.i = 0 : <∃j : 0 <= j < i+1 : (x:xs).j = 1>>
    [LÓGICA, PARTICIÓN DE RANGO]
False ∧ <∀i : 0 <= i < #xs ∧ xs.i = 0 : <∃j : 0 <= j < 1 : (x:xs).j = 1> v <∃j : 1 <= j < i+1 : (x:xs).j = 1>>
    [RANGO UNITARIO, DEF POSICIÓN]
False ∧ <∀i : 0 <= i < #xs ∧ xs.i = 0 : x = 1 v <∃j : 1 <= j < i+1 : (x:xs).j = 1>>
    [j <- j+1, ARITMETICA, DEF POSICIÓN]
False ∧ <∀i : 0 <= i < #xs ∧ xs.i = 0 : x = 1 v <∃j : 0 <= j < i : xs.j = 1>>
    [HAY QUE MODULARIZAR POR EL x = 1]
    ...

--------------------------------------------------------------------------------------
-- Derivar un programa imperativo que dado un número positivo calcule la suma de sus divisores, puede usar las funciones div y mod.
f : Int -> Int
f.i = <Σi : 1 <= j <= i ∧ (mod i j = 0) : j> 

{P: i > 0}
j, res := 1, 0;
do (j <= i)
    if (mod i j = 0) -> j, res := j+1, res+j 
    [] (mod i j != 0) -> j := j+1
    fi
od
{Q: res >= 2}
{I: i > 0 ∧ j <= i ∧ res >= 0}

-- Inicialización: {P}S{I}
{i > 0} j, res := 1, 0 {i > 0 ∧ j <= i}
    [DEF WP]
i > 0 -> wp.(j, res := 1, 0).(i > 0 ∧ j <= i)
    [DEF ASIGNACIÓN WP]
i > 0 -> i > 0 ∧ 1 <= i ∧ 0 >= 0
    [LEIBNITZ, NEUTRO ∧, ARITMETICA]
i > 0 ->  i >= 1
    [LÓGICA, ya que i > 0 entonces i >= 1]
True

-- Postcondición: I ∧ -B0 ∧...∧ -Bn -> Q
(i > 0 ∧ j <= i ∧ res >= 0) ∧ (j > i) -> res >= 2
    [ASOCIATIVA Y CONMUTATIVA ∧, LÓGICA]
res >= 0 -> res >= 2
    [LEIBNITZ]
True

-- Invariante: {I ∧ Bn} Sn {I}
-- B0
{(i > 0 ∧ j <= i ∧ res >= 0) ∧ j <= i} j, res := j+1, res+j {(i > 0 ∧ j <= i ∧ res >= 0) ∧ j <= i}
    [DEF WP]
(i > 0 ∧ j <= i ∧ res >= 0) ∧ j <= i -> wp.(j, res := j+1, res+j)((i > 0 ∧ j <= i ∧ res >= 0) ∧ j <= i)
    [DEF WP ASIGNACIÓN]
(i > 0 ∧ j <= i ∧ res >= 0) ∧ j <= i -> (i > 0 ∧ j+1 <= i ∧ res+j >= 0) ∧ j+1 <= i
    [ASUMIMOS ANTECEDENTE PARA MEJOR LECTURA]
(i > 0 ∧ j+1 <= i ∧ res+j >= 0) ∧ j+1 <= i
    [LEIBNITZ, LÓGICA (YA QUE j <= i entonces j+1 <= i Y res >= 0 entonces res+j >= 0 porque j >= 0)]
True

-- B1
{(i > 0 ∧ j <= i ∧ res >= 0) ∧ j <= i} j := j+1 {(i > 0 ∧ j <= i ∧ res >= 0) ∧ j <= i}
    [DEF WP]
(i > 0 ∧ j <= i ∧ res >= 0) ∧ j <= i -> wp.(j := j+1 )((i > 0 ∧ j <= i ∧ res >= 0) ∧ j <= i)
    [DEF WP ASIGNACIÓN, ASUMIMOS ANTECEDENTE]
(i > 0 ∧ j+1 <= i ∧ res >= 0) ∧ j+1 <= i
    [LEIBNITZ, LÓGICA]
True

--------------------------------------------------------------------------------------
-- ¿Cómo se define el conjunto de expresiones canónicas de los tipos utilizados en el formalismo dado en la materia? Dar ejemplos. Dar de cada tipo un elemento que no tenga forma normal.

    [RELEER POR QUE NO ENTENDI]

--------------------------------------------------------------------------------------
----------------------------------------2016A-----------------------------------------
--------------------------------------------------------------------------------------
-- Demostrar que la regla dorada es una tautología.
A ∧ B ≡ A ≡ B ≡ B ∨ A ≡ True
    [NEUTRO v]
A ∧ B ≡ A ≡ B v False ≡ B ∨ A ≡ True
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
A ∧ B ≡ A ≡ B v (False ≡ A) ≡ True
    [CONTRAPOSITIVA]
A ∧ B ≡ A ≡ B v -A ≡ True
    [REGLA DORADA]
B ≡ B v A ≡ B v -A ≡ True
    [NEUTRO v]
B v False ≡ B v A ≡ B v -A ≡ True
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
B v (False ≡ A) ≡ B v -A ≡ True
    [CONTRAPOSITIVA]
B v -A ≡ B v -A ≡ True
    [NEUTRO ≡]
B v -A ≡ B v -A
    [LÓGICA]
True

--------------------------------------------------------------------------------------
-- Especificar y derivar una función f : [Nat] -> Nat -> Bool, tal que f.xs.k devuelve true cuando todos los elementos en posiciones mayores que k son mayores a xs.k
f : [Nat] -> Nat -> Bool
f.xs.k = <∀i : 0 <= i < #xs ∧ i >= k : xs.i > xs.k>

--CB xs = []
f.[].k
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[] ∧ i >= k : xs.i > xs.k>
    [DEF CARDINAL]
<∀i : 0 <= i < 0 ∧ i >= k : xs.i > xs.k>
    [RANGO VACIO]
True

--CI xs = x:xs
--HI f.xs.k = <∀i : 0 <= i < #xs ∧ i >= k : xs.i > xs.k>
f.(x:xs).k
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #(x:xs) ∧ i >= k : (x:xs).i > (x:xs).k>
    [DEF CARDINAL]
<∀i : 0 <= i < 1+#xs ∧ i >= k : (x:xs).i > (x:xs).k>
    [LÓGICA, PARTICIÓN DE RANGO]
<∀i : 0 <= i < 1 ∧ i >= k : (x:xs).i > (x:xs).k> ∧ <∀i : 1 <= i < 1+#xs ∧ i >= k : (x:xs).i > (x:xs).k>
    [RANGO UNITARIO, DEF POSICIÓN]
x > (x:xs).k ∧ <∀i : 1 <= i < 1+#xs ∧ i >= k : (x:xs).i > (x:xs).k>
    [i <- i+1]
x > (x:xs).k ∧ <∀i : 1 <= i+1 < 1+#xs ∧ i+1 >= k : (x:xs).i+1 > (x:xs).k>
    [ARITMETICA, DEF POSICIÓN]
x > (x:xs).k ∧ <∀i : 0 <= i < #xs ∧ i+1 >= k : xs.i > (x:xs).k>

    [MODULARIZACIÓN <∀i : 0 <= i < #xs ∧ i+1 >= k : xs.i > (x:xs).k>]

--CB xs = []
g.[].k.n
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[] ∧ i+n >= k : [].i > (x:[]).k>
    [DEF CARDINAL]
<∀i : 0 <= i < 0 ∧ i+n >= k : [].i > (x:[]).k>
    [RANGO VACIO]
True

--CI xs = y:ys
--HI g.xs.k = <∀i : 0 <= i < #xs ∧ i+n >= k : xs.i > (x:xs).k>
g.(y:ys).k.n
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #(y:ys) ∧ i+n >= k : (y:ys).i > (x:(y:ys)).k>
    [DEF CARDINAL]
<∀i : 0 <= i < 1+#ys ∧ i+n >= k : (y:ys).i > (x:(y:ys)).k>
    [LÓGICA, PARTICIÓN DE RANGO]
<∀i : 0 <= i < 1 ∧ i+n >= k : (y:ys).i > (x:(y:ys)).k> ∧ <∀i : 1 <= i < 1+#ys ∧ i+n >= k : (y:ys).i > (x:(y:ys)).k>
    [RANGO UNITARIO, DEF POSICIÓN]
y > (x:(y:ys)).k ∧ <∀i : 1 <= i < 1+#ys ∧ i+n+1 >= k : (y:ys).i > (x:(y:ys)).k>
    [i <- i+1, ARITMETICA]
y > (x:(y:ys)).k ∧ <∀i : 0 <= i < #ys ∧ i+(n+1) >= k : (y:ys).i > (x:(y:ys)).k>
    [HI]
y > (x:(y:ys)).k ∧ g.(y:ys).k.n

f.xs.k = True
f.(x:xs).k = y > (x:(y:ys)).k ∧ g.(y:ys).k.n


--------------------------------------------------------------------------------------
-- Dadas las siguientes definiciones funcionales:
--	    f^0 = id
--	    f^(n+1) = f • f^n
-- Donde • es la composición funcional, demostrar:
--	    f^n • f^m • f^h = f^(n+m+h)

--CB n = 0
f^0 • f^m • f^h = f^(0+m+h)
    [DEF F]
f^m • f^h = f^(m+h)
    [HI]
True

--CI n = n+1
f^(n+1) • f^m • f^h = f^((n+1)+m+h)
    [DEF F]
(f • f^n) • f^m • f^h = f^((n+1)+m+h)
    [ASOCIATIVA •]
f • (f^n • f^m • f^h) = f^((n+1)+m+h)
    [HI, ARITMETICA]
f • f^(n+m+h) = f^(1+n+m+h)
    [PROPIEDAD]
f^(1+n+m+h) = f^(1+n+m+h)
    [LÓGICA]
True

--------------------------------------------------------------------------------------
-- Especificar y derivar la siguiente función: Dada una lista de números naturales, la función P dice si la suma de elementos pares es igual a la suma de los elementos impares de la lista.
pares : [Nat] -> Int
pares.xs = <Σi : 0 <= i < #xs ∧ mod xs.i 2 == 0 : 1>

impares : [Nat] -> Int
impares.xs = <Σi : 0 <= i < #xs ∧ mod xs.i 2 /= 0 : 1>

p : [Nat] -> Bool
p.xs = pares.xs == impares.xs

--DEMOSTRACIONES
--CB pares = 0
pares.[]
    [ESPECIFICACIÓN]
<Σi : 0 <= i < #[] ∧ mod [].i 2 == 0 : 1>
    [DEF CARDINAL]
<Σi : 0 <= i < 0 ∧ mod [].i 2 == 0 : 1>
    [RANGO VACIO]
0

--CI pares = x:xs
--HI pares.xs = <Σi : 0 <= i < #xs ∧ mod xs.i 2 == 0 : 1>
pares.(x:xs)
    [ESPECIFICACIÓN]
<Σi : 0 <= i < #(x:xs) ∧ mod (x:xs).i 2 == 0 : 1>
    [DEF CARDINAL]
<Σi : 0 <= i < 1+#xs ∧ mod (x:xs).i 2 == 0 : 1>
    [LÓGICA, PARTICIÓN DE RANGO]
<Σi : 0 <= i < 1 ∧ mod (x:xs).i 2 == 0 : 1> + <Σi : 1 <= i < 1+#xs ∧ mod (x:xs).i 2 == 0 : 1> 
    [RANGO UNITARIO]
1 + <Σi : 1 <= i < 1+#xs ∧ mod (x:xs).i 2 == 0 : 1> 
    [i <- i+1, ARITMETICA, DEF POSICIÓN]
1 + <Σi : 0 <= i < #xs ∧ mod xs.i 2 == 0 : 1> 
    [HI]
1 + pares.xs

--CB impares = 0
impares.[]
    [ESPECIFICACIÓN]
<Σi : 0 <= i < #[] ∧ mod [].i 2 /= 0 : 1>
    [DEF CARDINAL]
<Σi : 0 <= i < 0 ∧ mod [].i 2 /= 0 : 1>
    [RANGO VACIO]
0

--CI impares = x:xs
--HI impares.xs = <Σi : 0 <= i < #xs ∧ mod xs.i 2 /= 0 : 1>
impares.(x:xs)
    [ESPECIFICACIÓN]
<Σi : 0 <= i < #(x:xs) ∧ mod (x:xs).i 2 /= 0 : 1>
    [DEF CARDINAL]
<Σi : 0 <= i < 1+#xs ∧ mod (x:xs).i 2 /= 0 : 1>
    [LÓGICA, PARTICIÓN DE RANGO]
<Σi : 0 <= i < 1 ∧ mod (x:xs).i 2 /= 0 : 1> + <Σi : 1 <= i < 1+#xs ∧ mod (x:xs).i 2 /= 0 : 1> 
    [RANGO UNITARIO]
1 + <Σi : 1 <= i < 1+#xs ∧ mod (x:xs).i 2 /= 0 : 1> 
    [i <- i+1, ARITMETICA, DEF POSICIÓN]
1 + <Σi : 0 <= i < #xs ∧ mod xs.i 2 /= 0 : 1> 
    [HI]
1 + impares.xs

--CB p = []
p.[] 
    [ESPECIFICACIÓN]
pares.[] == impares.[]
    [DEF PARES, DEF IMPARES]
0 == 0
    [LÓGICA]
True

--CI p = x:xs
--HI p.xs = pares.xs == impares.xs
p.(x:xs) 
    [ESPECIFICACIÓN]
pares.(x:xs) == impares.(x:xs)
    [DEF PARES, DEF IMPARES]
1 + pares.xs == 1 + impares.xs

--------------------------------------------------------------------------------------
-- Especificar y derivar un algoritmo imperativo que calcule el máximo común divisor de dos números positivos, recordar que el máximo común divisor posee las siguientes propiedades:
--	    mcd.x.x = x
--	    mcd.x.y = mcd.y.x
--	    Si x > y, entonces mcd.x.y = mcd.(x-y).y
--	    Si x < y, entonces mcd.x.y = mcd.x.(y-x)

--SACAMOS WP IF: 
(x == y -> wp.(y := x).(mcd.x.y)) 
∧ (x < y -> wp.(x := x-y).(mcd.x.y)) 
∧ (x > y -> wp.(y := y-x).(mcd.x.y))

x == y -> wp.(y := x).(mcd.x.y)
    [DEF ASIGNACIÓN WP]
x == y -> mcd.x.x
    [DEF MCD]
x == y -> x
    [LEIBNITZ]
x

x < y -> wp.(x := x-y).(mcd.x.y)
    [DEF ASIGNACIÓN WP]
x < y -> mcd.(x-y).y
    [LEIBNITZ]
mcd.(x-y).y

x > y -> wp.(y := y-x).(mcd.x.y)
    [DEF ASIGNACIÓN WP]
x > y -> mcd.x.(y-x)
    [LEIBNITZ]
mcd.x.(y-x)

WP: x ∧ mcd.(x-y).y ∧ mcd.x.(y-x)

--Armamos el programa teniendo el wp como P

{x ∧ mcd.(x-y).y ∧ mcd.x.(y-x)}
if x == y -> y := x
[] x > y -> x := x-y
[] x < y -> y := y-x
fi
{mcd.x.y}

--DEMOSTRACIONES
[x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) -> (x == y v x > y v x < y)]
∧ {x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x == y} y := x {mcd.x.y}
∧ {x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x < y} x := x-y {mcd.x.y}
∧ {x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x > y} y := y-x {mcd.x.y}

x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) -> (x == y v x > y v x < y)
    [LÓGICA]
x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) -> True
    [LÓGICA]
True

{x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x == y} y := x {mcd.x.y}
    [DEF WP]
x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x == y -> wp.(y := x).(mcd.x.y)
    [DEF ASIGNACIÓN WP]
x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x == y -> mcd.x.x
    [DEF MCD]
x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x == y -> x
    [LEIBNITZ]
True

{x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x < y} x := x-y {mcd.x.y}
    [DEF WP]
x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x < y -> wp.(x := x-y).(mcd.x.y)
    [DEF ASIGNACIÓN WP]
x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x < y -> mcd.(x-y).y
    [LEIBNITZ]
True

{x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x > y} y := y-x {mcd.x.y}
    [DEF WP]
x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x > y -> wp.(y := y-x).(mcd.x.y)
    [DEF ASIGNACIÓN WP]
x ∧ mcd.(x-y).y ∧ mcd.x.(y-x) ∧ x > y -> mcd.x.(y-x)
    [LEIBNITZ]
True

-- Como son todas True entonces se demuestra la función imperativa.

--------------------------------------------------------------------------------------
----------------------------------------2016B-----------------------------------------
--------------------------------------------------------------------------------------
-- En la isla de mentirosos y caballeros se encuentran en el siguiente escenario:
--	    •A dice: B y yo somos del mismo tipo
--	    •B dice: A y yo somos de diferente tipo
--  ¿Qué puede deducir utilizando el cálculo proposicional dado en la materia?

A ≡ (B ∧ A) v (-B ∧ -A)
    [REGLA DORADA]
A ≡ (A ≡ B ≡ B v A) v (-B ∧ -A)
    [NEUTRO v]
A ≡ (A ≡ B v False ≡ B v A) v (-B ∧ -A)
    [A v (B ≡ C) ≡ A v B ≡ A v C]
A ≡ (A ≡ B v (False ≡ A)) v (-B ∧ -A)
    [CONTRAPOSITIVA]
A ≡ (A ≡ B v -A) v (-B ∧ -A)
    [ASOCIATIVA v, CONMUTATIVA v]
A ≡ A ≡ -A v B v (-B ∧ -A)
    [CONTRAPOSITIVA]
A ≡ False v B v (-B ∧ -A)
    [NEUTRO v]
A ≡ B v (-B ∧ -A)
    [DISTRIBUTIVA v]
A ≡ (B v -B) ∧ (B v -A)
    [TERCERO EXCLUIDO, NEUTRO ∧]
A ≡ B v -A
    [REGLA DORADA]
A ≡ B ≡ -A ≡ -A ∧ B
    [ASOCIATIVA ≡]
A ≡ -A ≡ B ≡ -A ∧ B
    [DEF ≡]
False ≡ B ≡ -A ∧ B
    [REGLA DORADA]
False ≡ -A ≡ B v -A
    [NEUTRO v]
False ≡ False v -A ≡ B v -A
    [A v (B ≡ C) ≡ A v B ≡ A v C]
False ≡ -A v (False ≡ B)
    [CONTRAPOSITIVO]
False ≡ -A v -B
    [DE MORGAN]
False ≡ -(A ∧ B)
    [CONTRAPOSITIVA]
A ∧ B

--Esto quiere decir que A y B son caballeros.

--------------------------------------------------------------------------------------
-- Demostrar la siguiente propiedad:
--	    <Min i : R.i : -E.i> ≡ -<Max i : R.i : F.i>

--------------------------------------------------------------------------------------
-- Dada la siguiente especificación de la función f : [Nat] -> [Nat] -> Bool:
--	    f.xs.ys = <∀i, j : 0 <= i < #xs ∧ 0 <= j < #ys : xs.i - ys.j = 0>
-- derive la función f.

--CB xs = []
f.[].ys
    [ESPECIFICACIÓN]
<∀i, j : 0 <= i < #[] ∧ 0 <= j < #ys : xs.i - ys.j = 0>
    [DEF CARDINAL]
<∀i, j : 0 <= i < 0 ∧ 0 <= j < #ys : xs.i - ys.j = 0>
    [RANGO VACIO]
True

--CB xs = (x:xs), ys = []
f.(x:xs).[]
    [ESPECIFICACIÓN]
<∀i, j : 0 <= i < #(x:xs) ∧ 0 <= j < #[] : xs.i - ys.j = 0>
    [DEF CARDINAL]
<∀i, j : 0 <= i < 1+#xs ∧ 0 <= j < 0 : xs.i - ys.j = 0>
    [RANGO VACIO]
True

--CI xs = (x:xs), y = (y:ys)
--HI f.xs.ys = <∀i, j : 0 <= i < #xs ∧ 0 <= j < #ys : xs.i - ys.j = 0>
f.(x:xs).(y:ys) 
    [ESPECIFICACIÓN]
<∀i, j : 0 <= i < #(x:xs) ∧ 0 <= j < #(y:ys) : (x:xs).i - (y:ys).j = 0>
    [DEF CARDINAL]
<∀i, j : 0 <= i < 1+#xs ∧ 0 <= j < 1+#ys : (x:xs).i - (y:ys).j = 0>
    [LÓGICA, PARTICIÓN DE RANGO]
<∀i, j : 0 <= i < 1 ∧ 0 <= j < 1 : (x:xs).i - (y:ys).j = 0> ∧ <∀i, j : 1 <= i < 1+#xs ∧ 1 <= j < 1+#xs : (x:xs).i - (y:ys).j = 0>
    [RANGO UNITARIO]
(x:xs).0 - (y:ys).0 = 0 ∧ <∀i, j : 1 <= i < 1+#xs ∧ 1 <= j < 1+#xs : (x:xs).i - (y:ys).j = 0>
    [i <- i+1, j <- j+1, ARITMETICA, DEF POSICIÓN]
x - y = 0 ∧ <∀i, j : 0 <= i < #xs ∧ 0 <= j < #xs : xs.i - ys.j = 0>
    [HI]
x - y = 0 ∧ f.xs.ys

f.[].ys = True
f.(x:xs).[] = True
f.(x:xs).(y:ys) = x - y = 0 ∧ f.xs.ys

--------------------------------------------------------------------------------------
-- Especificar y derivar un programa imperativo que dado dos números x e y, calcule su mínimo común múltiplo.
mcm : Int -> Int -> Int
mcm.x.y
    | x == y = x
    | otherwise = x*y

{True}
if x = y -> res := x
[] x <> y -> res := x*y
fi
{res = mcm.x.y}

--Demostración
[P -> (B0 v...v Bn)]
∧ {P ∧ B0} S0 {Q}
∧...∧ {P ∧ Bn} Sn {Q}

True -> x = y v x <> y
    [LÓGICA]
True -> True
    [LÓGICA]
True

{True ∧ x = y} res := x {res = mcm.x.y}
    [DEF WP]
True ∧ x = y -> wp.(res := x).(res = mcm.x.y)
    [NEUTRO ∧, DEF ASIGNACIÓN WP]
x = y -> x = mcm.x.y
    [LEIBNITZ]
x = y -> x = mcm.x.x
    [DEF MCM]
x = y -> x = x
    [ARITMETICA]
True

{True ∧ x <> y} res := x*y {res = mcm.x.y}
    [DEF WP]
True ∧ x <> y -> wp.(res := x*y).(res = mcm.x.y)
    [NEUTRO ∧, DEF ASIGNACIÓN WP]
x <> y -> x*y = mcm.x.y
    [DEF MCM]
x <> y -> x*y = x*y
    [ARITMETICA]
True

--Como se cumplen todas las conjunciones, podemos decir que se ha demostrado el if.

--------------------------------------------------------------------------------------
-- Demostrar que durante cualquier ciclo lo siguiente se cumple: 
--	    I ∧ t ≤ 0 ⇒ ¬B ≡ I ∧ B ⇒ t > 0
--  Teniendo en cuenta que P es el invariante del ciclo, B es la guarda y t es el variante.

I ∧ t ≤ 0 -> ¬B ≡ I ∧ B -> t > 0
    [DEF VARIANTE(A)]
I ∧ t ≤ 0 -> ¬B ≡ True
    [NEUTRO ≡]
I ∧ t ≤ 0 -> ¬B

--------------------------------------------------------------------------------------
----------------------------------------2016C-----------------------------------------
--------------------------------------------------------------------------------------
-- En la isla de mentirosos y caballeros se encuentran en el siguiente escenario:
--	    •A dice: B y yo somos del mismo tipo
--	    •B dice: A y yo somos de diferente tipo
--  ¿Qué puede deducir utilizando el cálculo proposicional dado en la materia?

--------------------------------------------------------------------------------------
-- Especificar y derivar una función imperativa que calcule el mínimo común múltiplo entre dos números positivos dados.

--------------------------------------------------------------------------------------
-- Especificar y derivar una función recursiva f : [Nat] -> Bool, que diga si hay elementos repetidos en la lista o no.

--------------------------------------------------------------------------------------
-- Definir el tipo de árboles binarios en Haskell, definir una función que cuente la cantidad de hojas que tiene un árbol.

--------------------------------------------------------------------------------------
-- Responder las siguientes preguntas:
--	    •Algún programa cumple: {false}S{true}, justifique su respuesta.
--	    •Algún programa cumple: {true}S{false}, justifique su respuesta.
--	    •¿Cuál es la diferencia entre corrección total y parcial? De un ejemplo.

--------------------------------------------------------------------------------------
----------------------------------------2016D-----------------------------------------
--------------------------------------------------------------------------------------
-- Especificar y derivar una función f : [Char] -> Bool, tal que devuelve true cuando los paréntesis que aparecen en la secuencia están balanceados (se puede considerar que la secuencia solo consta de paréntesis)

--------------------------------------------------------------------------------------
-- Demostrar por inducción que:
--	    #α(S) = 2^(#S)
-- Donde S es un conjunto finito y #S es la cantidad de elementos de S.

--------------------------------------------------------------------------------------
-- Especificar y derivar un algoritmo imperativo que, dado un arreglo de enteros, calcule la longitud de la mayor subsecuencia cuyos elementos son todos 0.

--------------------------------------------------------------------------------------
-- ¿Qué son las expresiones canónicas? Explicar cuáles son las expresiones canónicas de los tipos básicos y estructurados de Haskell. ¿Qué son las formas normales? 

--------------------------------------------------------------------------------------
--  Dar ejemplos de expresiones que no tienen forma normal.

--------------------------------------------------------------------------------------
----------------------------------------2016E-----------------------------------------
--------------------------------------------------------------------------------------
-- Explicar las diferencias entre evaluación lazy y evaluación normal, ilustrar con ejemplos. ¿Cuál es la forma de evaluación de Haskell?¿Se puede cambiar la forma de evaluación en Haskell? Dar ejemplos.

--------------------------------------------------------------------------------------
-- Dar definiciones de los siguientes conceptos: expresión, tipo básico, forma normal, valores, expresión canónica. Utilizar ejemplos para ilustrar sus definiciones.

--------------------------------------------------------------------------------------
-- Especifique y derive una función que dada una lista de naturales retorne true si y solo si la lista es capicúa.

--------------------------------------------------------------------------------------
-- Especificar y derivar la siguiente función: Dada una lista de números naturales, la función P dice si hay algún elemento de la lista que es igual a la suma de los anteriores.

--------------------------------------------------------------------------------------
-- Dado un arreglo de enteros, especifique y derive un programa imperativo que devuelva en una variable x el mayor elemento del arreglo.

--------------------------------------------------------------------------------------
-- Demostrar que durante cualquier ciclo lo siguiente se cumple:
--	    P ∧ t ≤ 0 ⇒ ¬B ≡ P ∧ B ⇒ t > 0
--  Teniendo en cuenta que P es el invariante del ciclo, B es la guarda y t es el variante.

--------------------------------------------------------------------------------------
----------------------------------------2016F-----------------------------------------
--------------------------------------------------------------------------------------
-- Especificar y derivar una función f : [Num] -> Num que devuelve la longitud de la subsecuencia más larga cuyos elementos son todos iguales.

--------------------------------------------------------------------------------------
-- Demostrar:
--	    map (f • g) xs = map f (map g xs)

--------------------------------------------------------------------------------------
-- Especificar y derivar un algoritmo imperativo que calcule el máximo común divisor de dos números dados.

--------------------------------------------------------------------------------------
-- Implemente en Haskell la función g : [Int] -> [Int] -> [Int], que dadas dos listas de enteros xs e ys, devuelve una lista la cual en cada posición i contiene la suma del i-ésimo numero par de xs con el i-ésimo numero par de ys, en caso de que alguna de las dos listas no contenga i números pares se debe considerar un 0. 
--  Por ejemplo:	g  [1,2,4,6] [2,2] = [4,6,6]

--------------------------------------------------------------------------------------
----------------------------------------2018A-----------------------------------------
--------------------------------------------------------------------------------------
-- ¿Cuáles son las principales propiedades de las funciones? De un ejemplo de como se pueden utilizar estas propiedades.

--------------------------------------------------------------------------------------
-- Especificar y derivar una función imperativa que calcule Fibonacci.

--------------------------------------------------------------------------------------
-- Dada la siguiente especificación:
--	    f.n = <Σ i : 0 <= i < n : 1/n>
--  Derive una función. Utilice alguna técnica para mejorar la eficiencia de su programa.

--------------------------------------------------------------------------------------
-- ¿Cómo definiría el tipo lista en Haskell con definiciones inductivas? Defina la función longitud y la concatenación de listas sobre su tipo lista.

--------------------------------------------------------------------------------------
-- Explique los siguientes conceptos:
--	    •Precondición
--	    •Postcondición
--	    •Invariante
--	    •Variante
--  De ejemplos.

--------------------------------------------------------------------------------------
----------------------------------------2018B-----------------------------------------
--------------------------------------------------------------------------------------
-- Explique las reglas de intercambio de iguales por iguales, explicar como se utiliza esta regla en la práctica.

--------------------------------------------------------------------------------------
-- Especificar y derivar una función f : [Num] -> Num, tal que devuelve la suma del subsegmento de suma mínima de una secuencia de números enteros.

--------------------------------------------------------------------------------------
-- Especificar y derivar un programa imperativo que calcule la función Fibonacci.

--------------------------------------------------------------------------------------
-- Sea ⊕ donde ⊕ es una operación asociativa y conmutativa, probar la siguiente regla de cuantificadores:
--	    <⊕i, j : i = Z ∧ R.i.j : T.i.j> ≡ <⊕j : R.Z.j : T.Z.j>

--------------------------------------------------------------------------------------
-- Demostrar:
--	    foldr (+) 0 xs = <Σ i : 0 <= i < #xs : xs.i>

--------------------------------------------------------------------------------------
-----------------------------------------2019-----------------------------------------
--------------------------------------------------------------------------------------
-- En la isla de mentirosos y caballeros se encuentran en el siguiente escenario:
--	    •A dice: B y yo somos del mismo tipo
--	    •B dice: A y yo somos de diferente tipo
--  ¿Qué puede deducir utilizando el cálculo proposicional dado en la materia?

--------------------------------------------------------------------------------------
-- Demostrar la siguiente propiedad:
--	    <Min i : R.i : -E.i> = - <Max i : R.i : F.i>

--------------------------------------------------------------------------------------
-- Especifique y derive una función recursiva que diga si, dada una secuencia de xs, existe una subsecuencia no vacía con suma 0.

--------------------------------------------------------------------------------------
-- Demostrar o refutar la siguiente propiedad:
--	    wp.S.P v Q ≡ wp.S.P v wp.S.Q

--------------------------------------------------------------------------------------
-- Demostrar que durante cualquier ciclo lo siguiente se cumple: 
--	    P ∧ t ≤ 0 ⇒ ¬B ≡ P ∧ B ⇒ t > 0
--  Teniendo en cuenta que P es el invariante del ciclo, B es la guarda y t es el variante.
