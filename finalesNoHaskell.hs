--------------------------------------------------------------------------------------
-----------------------------------------2015-----------------------------------------
--------------------------------------------------------------------------------------
-- ¿Qué es el wp? ¿Cuáles son sus propiedades más importantes? Explicar el wp para la asignación y el if.
El wp es la "weakest precondition", es decir, la precondición mas debil que hace valido a la postcondición.
Dentro de ella hay 5 propiedades importantes (Son las propiedades de las ternas de Hoare) las cuales son:
•Exclusión de milagros: {P}S{False} ≡ [P ≡ False]
•Fortalecimiento de la precondición: {P}S{Q} ∧ [P0 -> P] -> {P0}S{Q}
    EJ: {x=2 ∧ x=5}S{Q} -> {x=2}S{Q}
•Debilitamiento de la postcondición: {P}S{Q} ∧ [Q -> Q0] -> {P}S{Q0}
    EJ: {P}S{x=2} -> {P}S{x=2 v x=5}
•Conjunción de postcondición: {P}S{Q} ∧ {P}S{Q'} ≡ {P}S{Q y Q'}
•Disyunción de precondición: {P}S{Q} ∧ {P'}S{Q} ≡ {P v P'}S{Q}

- := (ASIGNACIÓN): wp.(:=).Q
    Lo que hacemos en la asignación es reemplazar cada elemento que se asigne en la postcondición, es decir: Q(:=)
    EJ: wp.(x = x+1).(2x) = 2(x+1)

- if: wp.if.q
    Lo que comprobamos es [(B0 v...v Bn) ∧ (B0 -> wp.S0.Q) ∧...∧ (Bn -> wp.Sn.Q)
    El wp del if requiere minimamente que alguna de las guardas sea verdadera y que cada una de ellas sea mas fuerte que la precondición más debil respecto a S.

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
{Q: res >= <Σi : 0 <= i < #xs ∧ mod x i == 0 ∧ i <> 0 : 1>}
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
(i > 0 ∧ j <= i ∧ res >= 0) ∧ (j > i) -> res >= <Σi : 0 <= i < #xs ∧ mod x i == 0 ∧ i <> 0 : 1>
    [ASOCIATIVA Y CONMUTATIVA ∧, LÓGICA]
res >= 0 -> res >= <Σi : 0 <= i < #xs ∧ mod x i == 0 ∧ i <> 0 : 1>
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
    [A -> B ≡ -A v B]
-(I ∧ t ≤ 0) v -B
    [DE MORGAN]
-I v -t ≤ 0 v -B
    [DEF -]
-I v t > 0 v -B
    [ASOCIATIVA Y CONMUTATIVA v]
(-I v -B) v t > 0
    [DE MORGAN]
-(I ∧ B) v t > 0
    [A -> B ≡ -A v B]
I ∧ B -> t > 0

--------------------------------------------------------------------------------------
----------------------------------------2016C-----------------------------------------
--------------------------------------------------------------------------------------
-- En la isla de mentirosos y caballeros se encuentran en el siguiente escenario:
--	    •A dice: B y yo somos del mismo tipo
--	    •B dice: A y yo somos de diferente tipo
--  ¿Qué puede deducir utilizando el cálculo proposicional dado en la materia?

B ≡ (-A ∧ B) v (A ∧ -B)
    [REGLA DORADA]
B ≡ (-A ≡ B ≡ -A v B) v (A ∧ -B)
    [NEUTRO v]
B ≡ (-A ≡ B v False ≡ -A v B) v (A ∧ -B)
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
B ≡ (-A ≡ B v (False ≡ -A)) v (A ∧ -B)
    [CONTRAPOSITIVA]
B ≡ (-A ≡ B v A) v (A ∧ -B)
    [REGLA DORADA]
B ≡ (-A ≡ B v A) v (A ≡ B ≡ A v -B)
    [NEUTRO v, CONMUTATIVA ≡]
B ≡ (-A ≡ B v A) v (B ≡ A v False ≡ A v -B)
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
B ≡ (-A ≡ B v A) v (B ≡ A v (False ≡ -B))
    [CONTRAPOSITIVA]
B ≡ (-A ≡ B v A) v (B ≡ A v B)
    [NEUTRO v]
B ≡ (-A ≡ B v A) v (False v B ≡ A v B)
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
B ≡ (-A ≡ B v A) v (B v (False ≡ A))
    [CONTRAPOSITIVA]
B ≡ (-A ≡ B v A) v B v -A
    [REGLA DORADA]
B ≡ (-A ≡ A ≡ B ≡ A ∧ B) v B v -A
    [NEUTRO ≡]
B ≡ (B ≡ A ∧ B) v B v -A
    [REGLA DORADA]
B ≡ (A ≡ A v B) v B v -A
    [NEUTRO v]
B ≡ (A v False ≡ A v B) v B v -A

B ≡ (A v (False ≡ B)) v B v -A
    [CONTRAPOSITIVA]
B ≡ A v -B v B v -A
    [CONMUTATIVA, ASOCIATIVA v]
B ≡ (A v -A) v (B v -B)
    [TERCERO EXCLUIDO]
B ≡ True v True
    [LÓGICA]
B ≡ True
    [NEUTRO ≡]
B

--Esto quiere decir que B es caballero, como son distintos entonces A es mentiroso.

--------------------------------------------------------------------------------------
-- Especificar y derivar una función recursiva f : [Nat] -> Bool, que diga si hay elementos repetidos en la lista o no.
--Lo tomo como: True si hay elementos repetidos, False si no hay repetidos.

f : [Nat] -> Bool
f.xs = <∃i : 0 <= i < #xs : <∃j : 0 <= j < #xs : xs.i == xs.j>>

--CB []
f.[]
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #[] : <∃j : 0 <= j < #[] : [].i == [].j>>
    [DEF CARDINAL]
<∃i : 0 <= i < 0 : <∃j : 0 <= j < 0: [].i == [].j>>
    [RANGO VACIO]
False

--CI x:xs
--HI f.xs = <∃i : 0 <= i < #xs : <∃j : 0 <= j < #xs : xs.i == xs.j>>
f.(x:xs)
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #(x:xs) : <∃j : 0 <= j < #(x:xs) : (x:xs).i == (x:xs).j>>
    [DEF CARDINAL]
<∃i : 0 <= i < 1+#xs : <∃j : 0 <= j < 1+#xs : (x:xs).i == (x:xs).j>>
    [LÓGICA, PARTICIÓN DE RANGO]
<∃i : 0 <= i < 1+#xs : <∃j : 0 <= j < 1 : (x:xs).i == (x:xs).j> v <∃j : 1 <= j < 1+#xs : (x:xs).i == (x:xs).j>>
    [RANGO UNITARIO, j <- j+1, ARITMETICA, DEF POSICIÓN]
<∃i : 0 <= i < 1+#xs : (x:xs).i == x v <∃j : 0 <= j < #xs : (x:xs).i == xs.j>>
    [LÓGICA, PARTICIÓN DE RANGO]
<∃i : 0 <= i < 1 : (x:xs).i == x v <∃j : 0 <= j < #xs : (x:xs).i == xs.j>> v <∃i : 1 <= i < 1+#xs : (x:xs).i == x v <∃j : 0 <= j < #xs : (x:xs).i == xs.j>>
    [RANGO UNITARIO, i <- i+1, ARITMETICA, DEF POSICIÓN]
x == x v <∃j : 0 <= j < #xs : x == xs.j> v <∃i : 0 <= i < #xs : xs.i == x v <∃j : 0 <= j < #xs : xs.i == xs.j>>
    [LÓGICA]
True v <∃j : 0 <= j < #xs : x == xs.j> v <∃i : 0 <= i < #xs : xs.i == x v <∃j : 0 <= j < #xs : xs.i == xs.j>>
    [LÓGICA]
<∃j : 0 <= j < #xs : x == xs.j> v <∃i : 0 <= i < #xs : xs.i == x v <∃j : 0 <= j < #xs : xs.i == xs.j>>

    [DEMOSTRAMOS]
    h.xs.y = <∃j : 0 <= j < #xs : y == xs.j>

--CB []
h.[].y
    [ESPECIFICACIÓN]
<∃j : 0 <= j < #[] : y == [].j>
    [DEF CARDINAL]
<∃j : 0 <= j < 0 : y == [].j>
    [RANGO VACIO]
False

--CI x:xs
--HI h.xs.y = <∃j : 0 <= j < #xs : y == xs.j>
h.(x:xs).y
    [ESPECIFICACIÓN]
<∃j : 0 <= j < #(x:xs) : y == (x:xs).j>
    [DEF CARDINAL]
<∃j : 0 <= j < 1+#xs : y == (x:xs).j>
    [LÓGICA, PARTICIÓN DE RANGO]
<∃j : 0 <= j < 1 : y == (x:xs).j> v <∃j : 1 <= j < 1+#xs : y == (x:xs).j>
    [RANGO UNITARIO, j <- j+1, ARITMETICA, DEF POSICIÓN]
y == x v <∃j : 0 <= j < #xs : y == xs.j>
    [LÓGICA, HI]
y == x v h.xs.y

h.[] = False
h.(x:xs).y = y == x v h.xs.y

    [VOLVEMOS]

x == x v h.xs.x v <∃i : 0 <= i < #xs : xs.i == x v <∃j : 0 <= j < #xs : xs.i == xs.j>>

    [MODULARIZAMOS]
    g.hs.n = <∃i : 0 <= i < #xs : n v <∃j : 0 <= j < #xs : xs.i == xs.j>>

--CB []
g.[].n 
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #[] : n v <∃j : 0 <= j < #[] : xs.i == xs.j>>
    [DEF CARDINAL]
<∃i : 0 <= i < 0 : n v <∃j : 0 <= j < 0 : xs.i == xs.j>>
    [RANGO VACIO]
False

--CI x:xs
--HI g.xs.n = <∃i : 0 <= i < #xs : n v <∃j : 0 <= j < #xs : xs.i == xs.j>>
g.(x:xs).n
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #(x:xs) : n v <∃j : 0 <= j < #(x:xs) : (x:xs).i == (x:xs).j>>
    [DEF CARDINAL]
<∃i : 0 <= i < 1+#xs : n v <∃j : 0 <= j < 1+#xs : (x:xs).i == (x:xs).j>>
    [LÓGICA, PARTICIÓN DE RANGO]
<∃i : 0 <= i < 1+#xs : n v <∃j : 0 <= j < 1 : (x:xs).i == (x:xs).j> v <∃j : 1 <= j < 1+#xs : (x:xs).i == (x:xs).j>>
    [RANGO UNITARIO, j <- j+1, ARITMETICA, DEF POSICIÓN]
<∃i : 0 <= i < 1+#xs : n v (x:xs).i == x v <∃j : 0 <= j < #xs : (x:xs).i == xs.j>>
    [LÓGICA, PARTICIÓN DE RANGO]
<∃i : 0 <= i < 1 : n v (x:xs).i == x v <∃j : 0 <= j < #xs : (x:xs).i == xs.j>> v <∃i : 1 <= i < 1+#xs : n v (x:xs).i == x v <∃j : 0 <= j < #xs : (x:xs).i == xs.j>>
    [RANGO UNITARIO, i <- i+1, ARITMETICA, DEF POSICIÓN]
n v x == x v <∃j : 0 <= j < #xs : x == xs.j> v <∃i : 0 <= i < #xs : n v xs.i == x v <∃j : 0 <= j < #xs : xs.i == xs.j>>
    [DEF H, HI]
n v x == x v h.xs.x v g.xs.(n v xs.i == x)
    [LÓGICA]
n v h.xs.x v g.xs.(n v xs.i == x)

g.[].n = False
g.(x:xs).n = n v h.xs.x v g.xs.(n v xs.i == x)

    [VOLVEMOS]

(x == x v h.xs.x) v (xs.i == x) v (h.xs.x) v (g.xs.(xs.i == x v xs.i == x))
    [IDEMPOTENCIA, LÓGICA]
(xs.i == x) v (h.xs.x) v (g.xs.(xs.i == x))

f.[] = False
f.(x:xs) = (xs.i == x) v (h.xs.x) v (g.xs.(xs.i == x))

--------------------------------------------------------------------------------------
-- Responder las siguientes preguntas:
--	    •Algún programa cumple: {false}S{true}, justifique su respuesta.
--	    •Algún programa cumple: {true}S{false}, justifique su respuesta.
--	    •¿Cuál es la diferencia entre corrección total y parcial? De un ejemplo.

{false}S{true}
    [DEF WP]
False -> wp.S.True
    [wp.S.True == True, LÓGICA]
False -> True
    [LÓGICA]
True
-- Todo programa existente cumple con ello ya que False -> True siempre es True

{true}S{false}
    [DEF WP]
True -> wp.S.False
    [wp.S.False == False, LÓGICA]
True -> False
    [LÓGICA]
False
--Nunca se cumple esto sin importar que valor pongamos en la precondición.

¿Cuál es la diferencia entre corrección total y parcial?
En una corrección parcial demostramos que el programa es correcto viendo la inicialización, la postcondición y el invariante mientras que en la corrección total, ademas de ver estos 3 mencionados anteriormente, tambien comprobamos que se salga/se termine el ciclado viendo el variante(a) y variante(b)

--------------------------------------------------------------------------------------
----------------------------------------2016D-----------------------------------------
--------------------------------------------------------------------------------------
-- Especificar y derivar una función f : [Char] -> Bool, tal que devuelve true cuando los paréntesis que aparecen en la secuencia están balanceados (se puede considerar que la secuencia solo consta de paréntesis)

f : [Char] -> Bool
f.xs = <∀i : 0 <= i < #xs : xs.i = '(' v xs.i = ')'>

--CB []
f.[]
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[] : [].i = '(' v [].i = ')'>
    [DEF CARDINAL]
<∀i : 0 <= i < 0 : [].i = '(' v [].i = ')'>
    [RANGO VACIO]
True

--CI x:xs
--HI f.xs = <∀i : 0 <= i < #xs : xs.i = '(' v xs.i = ')'>
f.(x:xs)
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #(x:xs) : (x:xs).i = '(' v (x:xs).i = ')'>
    [DEF CARDINAL]
<∀i : 0 <= i < 1+#xs : (x:xs).i = '(' v (x:xs).i = ')'>
    [LÓGICA, PARTICIÓN DE RANGO]
<∀i : 0 <= i < 1 : (x:xs).i = '(' v (x:xs).i = ')'> ∧ <∀i : 1 <= i < 1+#xs : (x:xs).i = '(' v (x:xs).i = ')'>
    [RANGO UNITARIO]
(x:xs).0 = '(' v (x:xs).0 = ')' ∧ <∀i : 1 <= i < 1+#xs : (x:xs).i = '(' v (x:xs).i = ')'>
    [DEF POSICIÓN, i <- i+1, ARITMETICA]
x = '(' v x = ')' ∧ <∀i : 0 <= i < #xs : xs.i = '(' v xs.i = ')'>
    [HI]
x = '(' v x = ')' ∧ f.xs

--------------------------------------------------------------------------------------
-- Demostrar por inducción que:
--	    #α(S) = 2^(#S)
-- Donde S es un conjunto finito y #S es la cantidad de elementos de S.


--------------------------------------------------------------------------------------
-- Especificar y derivar un algoritmo imperativo que, dado un arreglo de enteros, calcule la longitud de la mayor subsecuencia cuyos elementos son todos 0.

a : array [0, N) of Int
i, r, m := 0, 0, 0;
{N > 0}
do i < N
    if a.i = 0 -> r, i := r+1, i+1;
    [] a.i /= 0 -> r, i, m := 0, i+1, r;
    fi
od
{m = <Max as,bs,cs : a.i = as++bs++cs ∧ bs.i = 0 : #bs>}
{I = N-i > 0}


--DEMOSTRACIONES
--Inicialización: {P}S{I}
{N > 0} i, r, m := 0, 0, 0 {N-i > 0}
    [DEF WP]
N > 0 -> wp.(i, r, m := 0, 0, 0).(N-i > 0)
    [DEF ASIGNACIÓN WP]
N > 0 -> N-0 > 0
    [ARITMETICA]
N > 0 -> N > 0
    [LEIBNITZ]
True

--Postcondición: (I ∧ -Bn) -> Q
N-i > 0 ∧ a.i = 0 ∧ a.i /= 0 -> m = <Max as,bs,cs : a.i = as++bs++cs ∧ bs.i = 0 : #bs>
    [ARITMETICA, LÓGICA]
N > i ∧ False -> m = <Max as,bs,cs : a.i = as++bs++cs ∧ bs.i = 0 : #bs>
    [LÓGICA]
False -> m = <Max as,bs,cs : a.i = as++bs++cs ∧ bs.i = 0 : #bs>
    [LÓGICA ->]
True

--Invariante: {I ∧ Bn} Sn {I}
{N-i > 0 ∧ a.i = 0} r, i := r+1, i+1 {N-i > 0}
    [DEF WP]
N-i > 0 ∧ a.i = 0 -> wp.(r, i := r+1, i+1).(N-i > 0)
    [DEF ASIGNACIÓN WP]
N-i > 0 ∧ a.i = 0 -> N-i+1 > 0
    [LEIBNITZ, LÓGICA (Si a > 0 entonces a+1 > 0)]
True

{N-i > 0 ∧ a.i /= 0} r, i, m := 0, i+1, r {N-i > 0}
    [DEF WP]
N-i > 0 ∧ a.i /= 0 -> wp.(r, i, m := 0, i+1, r).(N-i > 0)
    [DEF ASIGNACIÓN WP]
N-i > 0 ∧ a.i /= 0 -> N-i+1 > 0
    [LEIBNITZ, LÓGICA (Si a > 0 entonces a+1 > 0)]
True

--Variante(a): I ∧ Bn -> v >= 0

--Variante(b): {I ∧ Bn ∧ v = A} Sn {v < A}

--------------------------------------------------------------------------------------
-- ¿Qué son las expresiones canónicas? Explicar cuáles son las expresiones canónicas de los tipos básicos y estructurados de Haskell. ¿Qué son las formas normales? Dar ejemplos de expresiones que no tienen forma normal.

Las expresiones canonicas son aquellas que son la maxima reducción de una expresión/fórmula.
EJ: 5+5, Canonica: 10

Expresiones canonicas para los tipos de Haskell:
-Booleanos: true, false
-Números: 0,1,2,3...
-Pares: (E0, E1) donde E0 y E1 son expresiones canonicas
-Listas: [E0, E1, ..., En] donde En son expresiones canonicas

Las formas normales de una expresión es la expresión canonica la cual representa el mismo valor.
Hay expresiones que no tienen forma normal, como: inf = inf+1

--------------------------------------------------------------------------------------
----------------------------------------2016E-----------------------------------------
--------------------------------------------------------------------------------------
-- Explicar las diferencias entre evaluación lazy y evaluación normal, ilustrar con ejemplos. ¿Cuál es la forma de evaluación de Haskell?¿Se puede cambiar la forma de evaluación en Haskell? Dar ejemplos.
-Normal: Los argumentos se pasan sin evaluar a una función hasta que sea necesario. Esto significa que los argumentos solo son evaluados cuando son requeridos por la función durante la ejecución.
-Lazy: Al igual que la normal, los argumentos no se evaluan hasta que sean requeridos. Los valores se evaluan y se almacenan en memoria para su uso posterior, mejorando asi la eficiencia.

La forma de evaluación de Haskell es la Lazy, no se puede cambiar la forma de evaluación de Haskell pero se puede hacer que alguna funciones tomen prioridad en unas variables sobre otras con el operador ($), se puede utilizar para ahorrar parentesis o para composición de funciones.
EJ: sqrt 3 + 4 + 9 -> sqrt $ 3 + 4 + 9 = sqrt(3 + 4 + 9)

--------------------------------------------------------------------------------------
-- Dar definiciones de los siguientes conceptos: expresión, tipo básico, forma normal, valores, expresión canónica. Utilizar ejemplos para ilustrar sus definiciones.
-Expresión: Una expresión es un valor el cual tiene un significado lógica o matematico, que generalmente se usa en funciones.
EJ: f.x = E
-Tipo básico: Un tipo básico es aquel que viene ya definido y no requiere de información adicional para comprenderlos o darle uso.
EJ: Booleanos, Integrales, etc.
-Forma normal: La forma normal de una expresión es la expresión canónica la cual representa el mismo valor.
EJ: la forma normal de (5+5) es 10, ya que es la expresión canonica que representa a la expresión.
-Valores: ¿¿¿??? Los valores son datos los cuales se utilizan en las funciones para inicializar tanto a las mismas cómo a las variables.
-Expresión canónica: Es la máxima reducción posible aritmeticamente de una expresión.
EJ: 10*2 = 20, donde 20 es la expresión canonica.

--------------------------------------------------------------------------------------
-- Especifique y derive una función que dada una lista de naturales retorne true si y solo si la lista es capicúa.

f : [Nat] -> True
f.xs = <∀i : 0 <= i < #xs : xs.i = xs.(#xs-i-1)>

--CB = []
f.[]
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[] : [].i = [].(#xs-i-1)>
    [DEF CARDINAL]
<∀i : 0 <= i < 0 : [].i = [].(#xs-i-1)>
    [RANGO VACIO]
True

--CI = x:xs
--HI f.xs = <∀i : 0 <= i < #xs : xs.i = xs.(#xs-i-1)>
f.(x:xs)
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #(x:xs) : (x:xs).i = (x:xs).(#(x:xs)-i-1)> 
    [DEF CARDINAL]
<∀i : 0 <= i < 1+#xs : (x:xs).i = (x:xs).(#(x:xs)-i-1)>
    [LÓGICA, PARTICIÓN DE RANGO]
<∀i : 0 <= i < 1 : (x:xs).i = (x:xs).(#(x:xs)-i-1)> ∧ <∀i : 1 <= i < 1+#xs : (x:xs).i = (x:xs).(#(x:xs)-i-1)>
    [RANGO UNITARIO]
(x:xs).0 = (x:xs).(#(x:xs)-0-1) ∧ <∀i : 1 <= i < 1+#xs :(x:xs).i = (x:xs).(#(x:xs)-i-1)>
    [i <- i+1, DEF POSICIÓN, ARITMETICA]
x = (x:xs).#xs ∧ <∀i : 0 <= i < #xs : xs.i = (x:xs).(1+#xs-i)>

    [MODULARIZAMOS]
g.xs.ys.j = <∀i : 0 <= i < #xs : xs.i = ys.(j+#xs-i)>

--CB []
g.[].ys.j 
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[] : [].i = (x:[]).(1+#[]-i)>
    [DEF CARDINAL]
<∀i : 0 <= i < 0 : [].i = (x:[]).(1+0-i)>
    [RANGO VACIO]
True

--CI x:xs
--HI g.xs.ys.j = <∀i : 0 <= i < #xs : xs.i = ys.j>
g.(x:xs).ys.j
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #(x:xs) : (x:xs).i = (x:(x:xs)).(1+#(x:xs)-i)>
    [DEF CARDINAL, ARITMETICA]
<∀i : 0 <= i < 1+#xs : (x:xs).i = (x:(x:xs)).(2+#xs-i)>
    [LÓGICA, PARTICIÓN DE RANGO]
<∀i : 0 <= i < 1 : (x:xs).i = (x:(x:xs)).(2+#xs-i)> ∧ <∀i : 1 <= i < 1+#xs : (x:xs).i = (x:(x:xs)).(2+#xs-i)>
    [RANGO UNITARIO]
(x:xs).0 = (x:(x:xs)).(2+#xs-0) ∧ <∀i: 1 <= i < 1+#xs : (x:xs).i = (x:(x:xs)).(2+#xs-i)>
    [DEF POSICIÓN, i <- i+1, ARITMETICA]
x = (x:(x:xs)).(2+#xs) ∧ <∀i : 0 <= i < #xs : xs.i = (x:(x:xs)).(1+#xs-i)>
    [HI]
x = (x:(x:xs)).(2+#xs) ∧ g.xs.(x:(x:xs)).1

--PARA COMPLETAR TENEMOS
f.[] = True
f.(x:xs) = x == (x:(x:xs)).(2+#xs) ∧ g.xs.(x:(x:xs)).1

--------------------------------------------------------------------------------------
-- Especificar y derivar la siguiente función: Dada una lista de números naturales, la función P dice si hay algún elemento de la lista que es igual a la suma de los anteriores.

p : [Nat] -> Bool
p.xs = <∃i : 0 <= i < #xs : xs.i = <Σj : 0 <= j < i : xs.j>> 

--CB p = []
p.[]
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #[] : [].i = <Σj : 0 <= j < i : [].j>> 
    [DEF CARDINAL]
<∃i : 0 <= i < 0 : [].i = <Σj : 0 <= j < i : [].j>> 
    [RANGO VACIO]
False

--CI p = x:xs
--HI p.xs = <∃i : 0 <= i < #xs : xs.i = <Σj : 0 <= j < i : xs.j>> 
p.(x:xs) 
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #(x:xs) : (x:xs).i = <Σj : 0 <= j < i : (x:xs).j>> 
    [DEF CARDINAL]
<∃i : 0 <= i < 1+#xs : (x:xs).i = <Σj : 0 <= j < i : (x:xs).j>> 
    [LÓGICA, PARTICIÓN DE RANGO]
<∃i : 0 <= i < 1 : (x:xs).i = <Σj : 0 <= j < i : (x:xs).j>> v <∃i : 1 <= i < 1+#xs : (x:xs).i = <Σj : 0 <= j < i : (x:xs).j>>
    [RANGO UNITARIO, DEF POSICIÓN, RANGO VACIO]
x = 0 v <∃i : 1 <= i < 1+#xs : (x:xs).i = <Σj : 0 <= j < i : (x:xs).j>>
    [i <- i+1, ARITMETICA, DEF POSICIÓN]
x = 0 v <∃i : 0 <= i < #xs : xs.i = <Σj : 0 <= j < i+1 : (x:xs).j>>

    [GENERALIZAMOS]

g.xs.ys.k = <∃i : 0 <= i < #xs : xs.i = <Σj : 0 <= j < i+k : ys.j>>

--CB []
g.[].ys.k
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #[] : [].i = <Σj : 0 <= j < i+1 : (x:[]).j>>
    [DEF CARDINAL]
<∃i : 0 <= i < 0 : [].i = <Σj : 0 <= j < i+1 : (x:[]).j>>
    [RANGO VACIO]
True

--CI x:xs
--HI g.xs.ys.k = <∃i : 0 <= i < #xs : xs.i = <Σj : 0 <= j < i+k : ys.j>>
g.(x:xs).ys.k
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #(x:xs) : (x:xs).i = <Σj : 0 <= j < i+1 : (x:(x:xs)).j>>
    [DEF CARDINAL]
<∃i : 0 <= i < 1+#xs : (x:xs).i = <Σj : 0 <= j < i+1 : (x:(x:xs)).j>>
    [LÓGICA, PARTICIÓN DE RANGO]
<∃i : 0 <= i < 1 : (x:xs).i = <Σj : 0 <= j < i+1 : (x:(x:xs)).j>> v <∃i : 1 <= i < 1+#xs : (x:xs).i = <Σj : 0 <= j < i+1 : (x:(x:xs)).j>>
    [RANGO UNITARIO]
x = <Σj : 0 <= j < 1 : (x:(x:xs)).j> v <∃i : 1 <= i < 1+#xs : (x:xs).i = <Σj : 0 <= j < i+1 : (x:(x:xs)).j>>
    [RANGO UNITARIO]
x = x v <∃i : 1 <= i < 1+#xs : (x:xs).i = <Σj : 0 <= j < i+1 : (x:(x:xs)).j>>
    [LÓGICA, i <- i+1, ARITMETICA, DEF POSICIÓN]
True v <∃i : 0 <= i < #xs : xs.i = <Σj : 0 <= j < i+2 : (x:(x:xs)).j>>
    [HI]
True v g.xs.(x:(x:xs)).2

--PARA COMPLETAR
f.[] = True
f.(x:xs) = True v g.xs.(x:(x:xs)).2

--------------------------------------------------------------------------------------
-- Dado un arreglo de enteros, especifique y derive un programa imperativo que devuelva en una variable x el mayor elemento del arreglo.

a : array [0, N) of Int
i, x := 0, 0;
{N > 0}
do i < N
    if a.i > x -> x, i := a.i, i+1
    [] a.i <= x -> i := i+1
    fi
od
{x = <Max i : 0 <= i < #a : a.i> ∧ i = N>}
{I: x = <Max i : 0 <= i < #a : a.i> ∧ i = k> ∧ 0 <= k < N ∧ N-i > 0}
{v: N-i}

--Inicialización: {P}S{I}
{N > 0} i, x := 0, 0 {x = <Max i : 0 <= i < #a : a.i> ∧ i = k> ∧ 0 <= k < N ∧ N-i > 0}
    [DEF WP]
N > 0 -> wp.(i, x := 0, 0).(x = <Max i : 0 <= i < #a : a.i> ∧ i = k> ∧ 0 <= k < N ∧ N-i > 0)
    [DEF ASIGNACIÓN WP]
N > 0 -> 0 = <Max i : 0 <= 0 < #a : a.0> ∧ 0 = k> ∧ 0 <= k < N ∧ N-0 > 0
    [RANGO VACIO, ARITMETICA]
N > 0 -> 0 = 0 ∧ 0 <= k < N ∧ N > 0
    [LEIBNITZ, LÓGICA]
N > 0 -> True ∧ True ∧ True
    [NEUTRO ∧, LEIBNITZ]
True

--Postcondición: I ∧ -B0 ∧...∧ -Bn -> Q
x = <Max i : 0 <= i < #a : a.i> ∧ i = k> ∧ 0 <= k < N ∧ N-i > 0 ∧ a.i < ∧ x a.i => x -> x = <Max i : 0 <= i < #a : a.i> ∧ i = N>
    [LÓGICA, k = N por reemplazo de constante por variables]
x = <Max i : 0 <= i < #a : a.i> ∧ i = N> ∧ N-i > 0 ∧ True -> x = <Max i : 0 <= i < #a : a.i> ∧ i = N>
    [NEUTRO ∧]
x = <Max i : 0 <= i < #a : a.i> ∧ i = N> ∧ N-i > 0 -> x = <Max i : 0 <= i < #a : a.i> ∧ i = N>
    [LEIBNITZ]
True

--Invariante: {I ∧ Bn} Sn {I}
{x = <Max i : 0 <= i < #a : a.i> ∧ i = k> ∧ 0 <= k < N ∧ N-i > 0 ∧ a.i > x} x -> x, i := a.i, i+1 {x = <Max i : 0 <= i < #a : a.i> ∧ i = k> ∧ 0 <= k < N ∧ N-i > 0}
    [DEF WP]
x = <Max i : 0 <= i < #a : a.i> ∧ i = k> ∧ 0 <= k < N ∧ N-i > 0 ∧ a.i > x -> wp.(x -> x, i := a.i, i+1).(x = <Max i : 0 <= i < #a : a.i> ∧ i = k> ∧ 0 <= k < N ∧ N-i > 0)
    [ASUMIMOS ANTECEDENTE PARA AHORRAR ESPACIO, DEF ASIGNACIÓN WP]
a.i = <Max i : 0 <= i+1 < #a : a.(i+1)> ∧ i+1 = k> ∧ 0 <= k < N ∧ N-i+1 > 0
    [LÓGICA (Si a > 0 entonces a+1 > 0)]
a.i = <Max i : 0 <= i+1 < #a : a.(i+1)> ∧ i+1 = k> ∧ 0 <= k < N ∧ True
    [NEUTRO ∧]
a.i = <Max i : 0 <= i+1 < #a : a.(i+1)> ∧ i+1 = k> ∧ 0 <= k < N

--Variante(a): I ∧ Bn -> v >= 0

--Variante(b): {I ∧ Bn ∧ v = A} Sn {v < A}

--------------------------------------------------------------------------------------
----------------------------------------2016F-----------------------------------------
--------------------------------------------------------------------------------------
-- Especificar y derivar una función f : [Num] -> Num que devuelve la longitud de la subsecuencia más larga cuyos elementos son todos iguales.

f : [Num] -> Num
f.xs = <Max as,bs,cs : xs = as++bs++cs ∧ elemI.bs : #bs>

elemI : [Num] -> Bool
elemI.xs = <∀i : 0 <= i < #xs-1 : xs.i = xs.(i+1)>

--DEMOSTRACION elemI
--CB elemI []
elemI.[]
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[]-1 : [].i = [].(i+1)>
    [DEF CARDINAL]
<∀i : 0 <= i < 0-1 : [].i = [].(i+1)>
    [RANGO VACIO]
True

--CI elemI x:xs
--HI elemI.xs = <∀i : 0 <= i < #xs-1 : xs.i = xs.(i+1)>
elemI.(x:xs)
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #(x:xs)-1 : (x:xs).i = (x:xs).(i+1)>
    [DEF CARDINAL, DEF POSICIÓN]
<∀i : 0 <= i < #xs : (x:xs).i = xs.i>
    
    [MODULARIZACIÓN]

g.xs = <∀i : 0 <= i < #xs : (x:xs).i = xs.i>
--CB []
g.[]
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[] : (x:[]).i = [].i>
    [DEF CARDINAL]
<∀i : 0 <= i < 0 : (x:[]).i = [].i>
    [RANGO VACIO]
True

--CI x:xs
--HI g.xs = <∀i : 0 <= i < #xs : (x:xs).i = xs.i>
g.(x:xs)
    [ESPECIFICAR]
<∀i : 0 <= i < #(x:xs) : (x:(x:xs)).i = (x:xs).i>
    [DEF CARDINAL]
<∀i : 0 <= i < 1+#xs : (x:(x:xs)).i = (x:xs).i>
    [LÓGICA, PARTICIÓN DE RANGO]
<∀i : 0 <= i < 1 : (x:(x:xs)).i = (x:xs).i> ∧ <∀i : 1 <= i < 1+#xs : (x:(x:xs)).i = (x:xs).i>
    [RANGO UNITARIO]
(x:(x:xs)).0 = (x:xs).0 ∧ <∀i : 1 <= i < 1+#xs : (x:(x:xs)).i = (x:xs).i>
    [i <- i+1, ARITMETICA, DEF POSICIÓN]
x = x ∧ <∀i : 0 <= i < #xs : (x:xs).i = xs.i>
    [HI, LÓGICA]
True ∧ g.xs

--PARA FINALIZAR
f.[] = True
f.(x:xs) = True ∧ g.xs

--DEMOSTRACION f
--CB f []
f.[]
    [ESPECIFICACIÓN]
<Max as,bs,cs : [] = as++bs++cs ∧ elemI.bs : #bs>
    [PROP ++]
<Max as,bs,cs : [] = as++bs++cs ∧ as = [] ∧ bs = [] ∧ cs = [] ∧ elemI.bs : #bs>
    [TERMINO CONSTANTE]
#[]
    [DEF CARDINAL]
0

--CI f x:xs
--HI f.xs = <Max as,bs,cs : xs = as++bs++cs ∧ elemI.bs : #bs>
f.(x:xs)
    [ESPECIFICACIÓN]
<Max as,bs,cs : (x:xs) = as++bs++cs ∧ elemI.bs : #bs>
    [PARTICIÓN DE RANGO (as = [] o as /= [])]
<Max as,bs,cs : (x:xs) = as++bs++cs ∧ as = [] ∧ elemI.bs : #bs> 
'Max' 
<Max as,bs,cs : (x:xs) = as++bs++cs ∧ as /= [] ∧ elemI.bs : #bs>
    [ANIDANDO EL PRIMER TERMINO: REEMPLAZO as <- a:as EN EL SEGUNDO TERMINO (VÁLIDO POR as /= [])]
<Max as : as = [] : <Max bs,cs : (x:xs) = as++bs++cs ∧ elemI.bs : #bs>> 
'Max' 
<Max a,as,bs,cs : (x:xs) = (a:as)++bs++cs ∧ (a:as) /= [] ∧ elemI.bs : #bs>
    [RANGO UNITARIO, DEFINICIÓN ++]
<Max bs,cs : (x:xs) = bs++cs ∧ elemI.bs : #bs>
'Max' 
<Max a,as,bs,cs : (x:xs) = (a:as)++bs++cs ∧ (a:as) /= [] ∧ elemI.bs : #bs>
    [DEF ++, IGUALDAD DE LISTAS]
<Max bs,cs : (x:xs) = bs++cs ∧ elemI.bs : #bs>
'Max' 
<Max a,as,bs,cs : x = a ∧ xs = as++bs++cs ∧ elemI.bs : #bs>
    [ANIDADO, RANGO UNITARIO]
<Max bs,cs : (x:xs) = bs++cs ∧ elemI.bs : #bs>
'Max' 
<Max as,bs,cs : xs = as++bs++cs ∧ elemI.bs : #bs>
    [HI]
<Max bs,cs : (x:xs) = bs++cs ∧ elemI.bs : #bs> 'Max' f.xs
    
    [INTRODUCCIÓN DE g.xs = <Max bs,cs : xs = bs++cs ∧ elemI.bs : bs>]

--CB g []
g.[]
    [ESPECIFICAR]
<Max bs,cs : [] = bs++cs ∧ elemI.bs : #bs>
    [PROP ++]
<Max bs,cs : [] = bs++cs ∧ bs = [] ∧ cs = [] ∧ elemI.bs : #bs>
    [CONSTANTE]
#[]
    [DEF CARDINAL]
0

--CI g x:xs
--HI g.xs = <Max bs,cs : xs = bs++cs ∧ elemI.bs : #bs>
g.(x:xs)
    [ESPECIFICACIÓN]
<Max bs,cs : (x:xs) = bs++cs ∧ elemI.bs : #bs>
    [PARTICIÓN DE RANGO (bs = [] o bs /= [])]
<Max bs,cs : (x:xs) = bs++cs ∧ bs = [] ∧ elemI.bs : #bs>
'Max'
<Max bs,cs : (x:xs) = bs++cs ∧ bs /= [] ∧ elemI.bs : #bs>
    [ANIDANDO EL PRIMER TERMINO: REEMPLAZO bs <- b:as EN EL SEGUNDO TERMINO (VÁLIDO POR bs /= [])]
<Max bs : bs = [] : <Max cs : (x:xs) = bs++cs ∧ elemI.bs : #bs>
'Max'
<Max b,bs,cs : (x:xs) = (b:bs)++cs ∧ (b:bs) /= [] ∧ elemI.bs : #(b:bs)>
    [RANGO UNITARIO]
<Max cs : (x:xs) = []++cs ∧ elemI.[] : #[]>
'Max'
<Max b,bs,cs : (x:xs) = (b:bs)++cs ∧ (b:bs) /= [] ∧ elemI.bs : #(b:bs)>
    [TERMINO CONSTANTE, DEF CARDINAL]
0 'Max' <Max b,bs,cs : (x:xs) = (b:bs)++cs ∧ (b:bs) /= [] ∧ elemI.bs : #(b:bs)>
    [DEF ++, IGUALDAD DE LISTAS]
0 'Max' <Max b,bs,cs : x = b ∧ xs = bs++cs ∧ elemI.bs : #(b:bs)>
    [ANIDADO, RANGO UNITARIO, DEF CARDINAL]
0 'Max' <Max bs,cs : xs = bs++cs ∧ elemI.bs : 1+#bs>
    [DISTRIBUTIVA DEL + CON RESPECTO AL MAX]
0 'Max' (1 + <Max bs,cs : xs = bs++cs ∧ elemI.bs : #bs>)
    [HI]
0 'Max' (1 + g.xs)

--PARA CONCLUIR
g.[] = 0
g.(x:xs) = 0 'Max' (1 + g.xs)

f.[] = 0
f.(x:xs) = g.(x:xs) 'Max' f.xs

--------------------------------------------------------------------------------------
-- Demostrar:
--	    map (f • g) xs = map f (map g xs)

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f xs = f (head xs) : map f (tail xs)

map (f • g) xs = map f (map g xs)
map f (map g xs)
    [DEF MAP]
map f (g (head xs) : map g (tail xs))

--------------------------------------------------------------------------------------
-- Especificar y derivar un algoritmo imperativo que calcule el máximo común divisor de dos números dados.
mcd x y
    | x == y = x
    | otherwise = x*y

{P: x >= 0 ∧ y >= 0}
if x == y -> r,y := x, x
[] x <> y -> r := x*y
fi
{Q: r = mcd.x.y}

--DEMOSTRACIÓN
-- [P -> -B0 v...v -Bn] ∧ {P ∧ B0}S0{Q} ∧...∧ {P ∧ Bn}Sn{Q}
--[P -> -B0 v...v -Bn]
x >= 0 ∧ y >= 0 -> x <> y ∧ x == y
    [ARITMETICA, ya que toma cuando x e y son iguales y cuando son distintos]
x >= 0 ∧ y >= 0 -> True
    [LÓGICA]
True

--{P ∧ B0}S0{Q}
{x >= 0 ∧ y >= 0 ∧ x == y} r, y := x, x {r = mcd.x.y}
    [DEF WP]
x >= 0 ∧ y >= 0 ∧ x == y -> wp.(r, y := x, x).(r = mcd.x.y)
    [DEF ASIGNACIÓN WP]
x >= 0 ∧ y >= 0 ∧ x == y -> x = mcd.x.x
    [DEF MCD]
x >= 0 ∧ y >= 0 ∧ x == y -> x = x
    [LÓGICA, LEIBNITZ]
True

--{P ∧ Bn}Sn{Q}
{x >= 0 ∧ y >= 0 ∧ x <> y} r := x*y {r = mcd.x.y}
    [DEF WP]
x >= 0 ∧ y >= 0 ∧ x <> y -> wp.(r := x*y).(r = mcd.x.y)
    [DEF ASIGNACIÓN WP]
x >= 0 ∧ y >= 0 ∧ x <> y -> x*y = mcd.x.y
    [DEF MCD]
x >= 0 ∧ y >= 0 ∧ x <> y -> x*y = x*y
    [LÓGICA]
True

--------------------------------------------------------------------------------------
----------------------------------------2018A-----------------------------------------
--------------------------------------------------------------------------------------
-- Especificar y derivar una función imperativa que calcule Fibonacci.
fib 0 = 0
fib 1 = 1
fib n = fib(n-1)+fib(n-2)

{P: N >= 0}
r, i := 0, N
do i >= 0
    if i == 0 -> r := r
    [] i == 1 -> r, i := r+1, i-1
    [] i >= 2 -> r, i := r+fib(i-1)+fib(i-2), i-1
    fi
od
{Q: r = fib i ∧ i = 0}
{I: r = fib i}
{v: N-i >= 0}

--Inicialización: {P}S{I}
{N >= 0} r, i := 0, N {r = fib i}
    [DEF WP]
N >= 0 -> wp.(r, i := 0, N).(r = fib i)
    [DEF ASIGNACIÓN WP]
N >= 0 -> 0 = fib N
    [LEIBNITZ]
N >= 0 -> 0 = fib 0
    [DEF FIB]
N >= 0 -> 0 = 0
    [LÓGICA]
True

--Precondición: I ∧ (-B0 ∧...∧ -Bn) -> Q

--Invariante: {I ∧ Bn} Sn {I}

--Variante(a): I ∧ Bn -> v >= 0

--Variante(b): {I ∧ Bn ∧ v = A} Sn {v < A}



--------------------------------------------------------------------------------------
-- Dada la siguiente especificación:
--	    f.n = <Σ i : 0 <= i < n : 1/n>
-- Derive una función. Utilice alguna técnica para mejorar la eficiencia de su programa.

--CB 0
f.0
    [ESPECIFICACIÓN]
<Σ i : 0 <= i < 0 : 1/0>
    [RANGO VACIO]
0

--CI n+1
--HI f.n = <Σ i : 0 <= i < n : 1/n>
f.n+1
    [ESPECIFICACIÓN]
<Σ i : 0 <= i < n+1 : 1/n+1>
    [LÓGICA, PARTICIÓN DE RANGO]
<Σ i : 0 <= i < n : 1/n+1> + <Σ i : n <= i < n+1 : 1/n+1>
    [RANGO UNITARIO]
<Σ i : 0 <= i < n : 1/n+1> + 1/n+1

    [INTRODUCIMOS g.n.m]
    g.n.m = <Σ i : 0 <= i < n : 1/n+m>

--CB 0
g.0.m 
    [ESPECIFICACIÓN]
<Σ i : 0 <= i < 0 : 1/0+m>
    [RANGO VACIO]
0

--CI n+1
--HI g.n.m = <Σ i : 0 <= i < n : 1/n+m>
g.(n+1).m 
    [ESPECIFICACIÓN]
<Σ i : 0 <= i < (n+1) : 1/(n+1)+m>
    [LÓGICA, PARTICIÓN DE RANGO]
<Σ i : 0 <= i < n : 1/(n+1)+m> + <Σ i : n <= i < (n+1) : 1/(n+1)+m>
    [RANGO UNITARIO, ASOCIATIVA +]
<Σ i : 0 <= i < n : 1/n+(1+m)> + 1/(n+(1+m))
    [HI, con m = 1+m]
g.n.(1+m) + 1/(n+(1+m))

    [VOLVIENDO]

g.0.m = 0
g.(n+1).m = g.n.(1+m) + 1/(n+(1+m))

f.0 = 0
f.(n+1) = g.n.m + 1/n+1

[FALTA USAR UNA TECNICA PARA MEJORAR LA EFICIENCIA, SEGURAMENTE TUPLING]

--------------------------------------------------------------------------------------
-- Explique los siguientes conceptos:
•Precondición: La precondición es lo que tiene que cumplir las variables del programa para entrar en la ejecución del mismo. La precondición tiene que ser más fuerte que la postcondición, por lo que tiene que precederla, asi mismo para llegar a ella.
{x >= 0}S{Q}

•Postcondición: La postcondición es el valor esperado de las variables al finalizar la ejecución del programa, al ser valida la postcondición, es valido el programa.
{P}S{r = mod 2 i}

•Invariante: El invariante son aquellas variables o fórmulas que al pasar durante los ciclos nunca cambian, nunca varian.
{I: x-N >= 0}

•Variante: El variante es justamente lo contrario al invariante, es lo que varia todos los ciclos para lograr llegar al cambio de condicionalidad. Es una expresión aritmetica.
{v: i-N}

--------------------------------------------------------------------------------------
----------------------------------------2018B-----------------------------------------
--------------------------------------------------------------------------------------
-- Explique las reglas de intercambio de iguales por iguales, explicar como se utiliza esta regla en la práctica.

--------------------------------------------------------------------------------------
-- Especificar y derivar una función f : [Num] -> Num, tal que devuelve la suma del subsegmento de suma mínima de una secuencia de números enteros.

f.xs = <Min as,bs,cs : xs = as++bs++cs : sum.bs>
sum.bs = <Σi : 0 <= i < #bs : bs.i>


--CB []
f.[]
    [ESPECIFICACIÓN]
<Min as,bs,cs : [] = as++bs++cs : sum.bs>
    [PROP ++]
<Min as,bs,cs : [] = as++bs++cs ∧ as = [] ∧ bs = [] ∧ cs = [] : sum.bs>
    [TERMINO CONSTANTE]
sum.[]
    [DEF SUM]
0

--CI x:xs
--HI f.xs = <Min as,bs,cs : xs = as++bs++cs : sum.bs>
f.(x:xs)
    [ESPECIFICACIÓN]
<Min as,bs,cs : (x:xs) = as++bs++cs : sum.bs>
    [PARTICIÓN DE RANGO, a = [] o a <> []]
<Min as,bs,cs : (x:xs) = as++bs++cs ∧ as = [] : sum.bs> 'Min' <Min as,bs,cs : (x:xs) = as++bs++cs ∧ as <> [] : sum.bs>
    [ANIDAMIENTO, EXISTENCIA DE A:AS]
<Min as : as = [] : <Min bs,cs : (x:xs) = as++bs++cs : sum.bs>> 'Min' <Min as,bs,cs : (x:xs) = (a:as)++bs++cs ∧ as <> [] : sum.bs>
    [RANGO UNITARIO, DEFINICIÓN ++]
<Min bs,cs : (x:xs) = bs++cs : sum.bs> 'Min' <Min as,bs,cs : (x:xs) = (a:as)++bs++cs ∧ as <> [] : sum.bs>
    [DEF ++, IGUALDAD DE LISTAS]
<Min bs,cs : (x:xs) = bs++cs : sum.bs> 'Min' <Min as,bs,cs : x = a ∧ xs = as++bs++cs : sum.bs>
    [ANIDADO, RANGO UNITARIO]
<Min bs,cs : (x:xs) = bs++cs : sum.bs> 'Min' <Min as,bs,cs : xs = as++bs++cs : sum.bs>
    [HI]
<Min bs,cs : (x:xs) = bs++cs : sum.bs> 'Min' f.xs

    [INTRODUCCIÓN DE g.xs = <Min bs,cs : xs = bs++cs : sum.bs>]

--CB []
g.[] 
    [ESPECIFICACIÓN]
<Min bs,cs : [] = bs++cs : sum.bs>
    [PROP ++]
<Min bs,cs : [] = bs++cs ∧ bs = [] ∧ cs = [] : sum.bs>
    [RANGO UNITARIO]
sum.[]
    [DEF SUM]
0

--CI x:xs
--HI g.xs = <Min bs,cs : xs = bs++cs : sum.bs>
g.(x:xs)
    [ESPECIFICACIÓN]
<Min bs,cs : (x:xs) = bs++cs : sum.bs>
    [PARTICIÓN DE RANGO, bs = [] o bs <> [] ]
<Min bs,cs : (x:xs) = bs++cs ∧ bs = [] : sum.bs> 'Min' <Min bs,cs : (x:xs) = bs++cs ∧ bs <> [] : sum.bs>
    [ANIDAMIENTO, EXISTENCIA DE B:BS YA QUE BS <> [] ]
<Min bs : bs = [] : <Min cs : (x:xs) = bs++cs : sum.bs>> 'Min' <Min bs,cs : (x:xs) = (b:bs)++cs : sum.(b:bs)>
    [RANGO UNITARIO, DEF ++]
<Min cs : (x:xs) = cs : sum.[]> 'Min' <Min bs,cs : (x:xs) = (b:bs)++cs : sum.(b:bs)>
    [TERMINO CONSTANTE, DEF SUM, IGUALDAD DE LISTAS]
0 'Min' <Min bs,cs : x = b ∧ xs = bs++cs : sum.(b:bs)>
    [ANIDADO, RANGO UNITARIO, DEF SUM]
0 'Min' <Min bs,cs : xs = bs++cs : b+sum.bs>
    [HI]
0 'Min' (x+g.xs)

--PARA CONCLUIR
g.[] = 0
g.(x:xs) = 0 'Min' (x+g.xs)

f.[] = 0
f.(x:xs) = g.(x:xs) 'Min' f.xs

--------------------------------------------------------------------------------------
-- Sea ⊕ donde ⊕ es una operación asociativa y conmutativa, probar la siguiente regla de cuantificadores:
--	    <⊕i, j : i = Z ∧ R.i.j : T.i.j> ≡ <⊕j : R.Z.j : T.Z.j>

<⊕i, j : i = Z ∧ R.i.j : T.i.j> ≡ <⊕j : R.Z.j : T.Z.j>
    [i CONSTANTE]
<⊕i : R.Z.j : T.Z.j> ≡ <⊕j : R.Z.j : T.Z.j>

    [¿ES ASI? NO CREO]

--------------------------------------------------------------------------------------
-- Demostrar:
--	    foldr (+) 0 xs = <Σ i : 0 <= i < #xs : xs.i>

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

foldr (+) 0 xs = <Σ i : 0 <= i < #xs : xs.i>
    [DEF Σ]
foldr (+) 0 xs = sum.xs
    [DEF FOLDR]
sum.xs = sum.xs
    [LÓGICA]
True

--------------------------------------------------------------------------------------
-----------------------------------------2019-----------------------------------------
--------------------------------------------------------------------------------------
-- Especifique y derive una función recursiva que diga si, dada una secuencia de xs, existe una subsecuencia no vacía con suma 0.

f.xs = <∃ as,bs,cs : xs = as++bs++cs : sum.bs = 0>

--CB []
f.[]
    [ESPECIFICACIÓN]
<∃ as,bs,cs : [] = as++bs++cs : sum.bs = 0>

--CI x:xs
--HI f.xs = <∃ as,bs,cs : xs = as++bs++cs : sum.bs = 0>
f.(x:xs)
    [ESPECIFICACIÓN]
<∃ as,bs,cs : (x:xs) = as++bs++cs : sum.bs = 0>

--------------------------------------------------------------------------------------
-- Demostrar o refutar la siguiente propiedad:
--	    wp.S.P v Q ≡ wp.S.P v wp.S.Q

wp.S.P v Q ≡ wp.S.P v wp.S.Q
    [DEF WP]
wp.S.P v Q ≡ wp.S.P v {True}S{Q}