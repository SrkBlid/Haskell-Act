------------------------------------------------------------------------------
--LÓGICA DE PRIMER ORDEN, EJERCICIOS DEL LIBRO
--PÁGINA 99
------------------------------------------------------------------------------
--EJERCICIO 1: Probar
-- <∃x : r.x : p.x> -> <∃x :: r.x>
<∃x : r.x : p.x> -> <∃x :: r.x>
    [DEF IMPLICACIÓN]
<∃x : r.x : p.x> v <∃x :: r.x> ≡ <∃x :: r.x>
    [NEUTRO V, CONMUTATIVA V]
<∃x :: r.x> v <∃x : r.x : p.x> ≡ <∃x :: r.x> v False
    [A v (B ≡ C) ≡ (A v B) ≡ (A v C)]
<∃x :: r.x> v (<∃x : r.x : p.x> ≡ False)
    [CONTRAPOSITIVA]
<∃x :: r.x> v -(<∃x : r.x : p.x>)
    [ARITMETICA]
<∃x :: r.x> v <∃x : r.x : -(p.x)>

------------------------------------------------------------------------------
--CUANTIFICADORES, EJERCICIOS DEL LIBRO
--PÁGINA 107
------------------------------------------------------------------------------
--EJERCICIO 1: Probar la siguiente regla:
-- <⊕i,j : i = Z ∧ R.i.j : T.i.j> ≡ <⊕j : R.Z.j : T.Z.j>
<⊕i,j : i = Z ∧ R.i.j : T.i.j> ≡ <⊕j : R.Z.j : T.Z.j>
    [ANIDAMIENTO]
<⊕i : i = Z : <⊕j : R.i.j : T.i.j>> ≡ <⊕j : R.Z.j : T.Z.j>
    [RANGO UNITARIO]
<⊕j : R.Z.j : T.Z.j>> ≡ <⊕j : R.Z.j : T.Z.j>
    [LÓGICA]
True

------------------------------------------------------------------------------
--EJERCICIO 2: Demostrar
-- <∃x,y : x = y : P.x.y> ≡ <∃x :: P.x.x>
<∃x,y : x = y : P.x.y> ≡ <∃x :: P.x.x>
    [¿RANGO UNITARIO? x = y]
<∃x :: P.x.x> ≡ <∃x :: P.x.x>
    [LÓGICA]
True

------------------------------------------------------------------------------
--EJERCICIO 3: Probar que la implicación es distributiva respecto al cuantificador
-- universal:
-- <∀i : R.i : Z -> T.i> ≡ Z -> <∀i : R.i : T.i>
<∀i : R.i : Z -> T.i> ≡ Z -> <∀i : R.i : T.i>
    [DEF IMPLICACIÓN]
<∀i : R.i : Z v T.i ≡ T.i> ≡ Z -> <∀i : R.i : T.i>
    [DISTRIBUTIVA DE V CON PARA TODO]
Z v <∀i : R.i : T.i ≡ T.i> ≡ Z -> <∀i : R.i : T.i>
    [LÓGICA]
Z v <∀i : R.i : True> ≡ Z -> <∀i : R.i : T.i>
    [DEF IMPLICACIÓN]
Z -> <∀i : R.i : True> ≡ True ≡ Z -> <∀i : R.i : T.i>
    [NEUTRO]
Z -> <∀i : R.i : True> ≡ Z -> <∀i : R.i : T.i>

------------------------------------------------------------------------------
--EJERCICIO 4: Dado el cuantificador N:
-- <Ni : R.i : T.i> = <∑i : R.i ∧ T.i : 1>

--Enunciar y demostrar la regla de partición de rango para N:
-- <Ni : R.i v S.i : T.i> = <Ni : R.i : T.i> + <Ni : S.i : T.i>
<Ni : R.i v S.i : T.i>
    [DEF N]
<∑i : (R.i v S.i) ∧ T.i : 1>
    [DISTRIBUTIVA ∧]
<∑i : (R.i ∧ T.i) v (S.i ∧ T.i) : 1>
    [PARTICIÓN DE RANGO]
<∑i : R.i ∧ T.i : 1> + <∑i : S.i ∧ T.i : 1>

--Idem con la regla vacio
-- <Ni : false : T.i> = 0
<Ni : false : T.i>
    [DEF N]
<∑i : false ∧ T.i : 1>
    [LÓGICA]
<∑i : false : 1>
    [RANGO VACIO]
0

--Probar:
-- <∑i : R.i ∧ T.i : k> = k*<Ni : R.i : T.i>
<∑i : R.i ∧ T.i : k>
    [DEF N]
<Ni : R.i : k*T.i>
    [DISTRIBUTIVA DE K RESPECTO A N]
k*<Ni : R.i : T.i>

------------------------------------------------------------------------------
--PRÁCTICO 9
------------------------------------------------------------------------------
--EJERCICIO 1: Expresar en lenguaje de primer orden.
--f es una función que determina si los elementos de una lista xs son iguales
iguales.xs = <∀i : 0 <= i < #xs : xs.0 = xs.i>

--f es una función que determina si los elementos de una lista xs son todos distintos
distintos.xs = <∀i,j : 0 <= i < j < #xs : xs.i /= xs.j>

--f es una función que determina si los elementos de una lista xs están ordenados
f.xs = <∀i,j : 0 <= i < j < #xs : xs.i <= xs.j>

--P es un predicado que es true sii cuando aparece 1 en xs entonces aparece 0 en xs
P = <∃i : 0 <= i < #xs : xs.i = 1> -> <∃j : 0 <= j < #xs : xs.j = 0>

--p es el producto de todos los elementos primos de xs
p = <∏i : 0 <= i < #xs ∧ esPrimo(xs.i) : xs.i>

esPrimo.i
    | cant.i.1 == 2 = True
    | otherwise = False
    where
        cant.i.n
            | i == m = 0
            | mod i n == 0 = 1+cant.i.(n+1)
            | otherwise = cant.i.(n+1)

------------------------------------------------------------------------------
--EJERCICIO 2: Dada una lista xs con al menos un true, dar:
--n es el menor entero tal que xs.n = True
xs.n = <Min n : 0 <= n < #xs ∧ xs.n : n>

--n es el último elemento de la lista tal que xs.n = True
xs.n = <Max n : 0 <= n < #xs ∧ xs.n : n>

--f es una función que devuelve True sii todos los ementos de xs son equivalentes
f.xs = <∀i : 0 <= i < #xs : xs.0 = xs.i>

------------------------------------------------------------------------------
--EJERCICIO 3: Especificar
--f.xs determina si xs tiene la misma cantidad de pares que impares
f.xs = <∑i : 0 <= i < #xs ∧ mod xs.i 2 = 0: 1> == <∑j : 0 <= j < #xs ∧ mod xs.j 2 /= 0: 1>
f'.xs = <Ni : 0 <= i < #xs : mod xs.i 2 = 0> == <Nj : 0 <= j < #xs : mod xs.j 2 /= 0>

--f.n determina si n es primo
f.n = <Ni : 1 <= i <= n : mod n i = 0> == 2

--f.xs.ys determina si ys es una subsecuencia de xs
f.xs.ys = <∃as,bs : xs = as++ys++bs>

--f.xs.ys determina si ys es una subsecuencia final de xs
f.xs.ys = <∃as : xs = as++ys>

--f.xs.ys determina si ys es una subsecuencia inicial de xs
f.xs.ys = <∃as,bs : xs = ys++bs>

------------------------------------------------------------------------------
--EJERCICIO 4: Especificar
--Dada una lista de enteros, especifique la suma del subsegmento de suma minima de
-- la lista
f.xs = <Min bs : xs = as++bs++cs : sum.bs>

--Una función maxIgual que determine la longitud del máximo subsegmento en donde todos
-- los elementos son iguales
maxIgual.xs = <Max bs : xs = as++bs++cs ∧ iguales.bs : #bs>

--maxDistinto que determina la longitud del máximo segmentos donde todos los elementos
-- son distintos
maxDistinto.xs = <Max bs : xs = as++bs++cs ∧ distintos.bs : #bs>

------------------------------------------------------------------------------
--EJERCICIO 5: Dados las funciones split3 y split2, especificar:
-- split2.xs = [(take n xs, drop n xs) | n <- [0..length xs]]
-- split3.xs = [(as, bs, cs) | (as, ys) <- split2 xs, (bs, cs) <- split2 ys]

--p.xs = <∏i : 0 <= i < #xs ∧ esPrimo(xs.i) : xs.i>
p.xs = product [n | n <- xs, esPrimo(n)]

--f.xs.ys = <∃as,bs : xs = as++ys++bs>
f.xs.ys = any (\(as, cs) -> xs == as++ys++cs) (split2 xs)

--f.xs.ys determina si ys es una subsecuencia final de xs
f.xs.ys = any (\as -> xs == as++ys) (split2 xs)

--Dada una lista de números, calcular el valor del subsegmento de suma máxima
f.xs = <Max bs : xs = as++bs++cs : sum.bs>

------------------------------------------------------------------------------
--ESPECIFICACIÓN, EJERCICIOS DEL LIBRO
--PÁGINA 157
------------------------------------------------------------------------------
--EJERCICIO 1: Expresar en lenguaje formal
--Dado un entero N > 0: "x es el mayor entero que vale a lo sumo N y es una
-- potencia de 2"
f.x = <Max i : 0 < i <= N ∧ mod i 2 == 0: i>

--Dado un conjunto B: "si B no es vacio, x es el mayor elemento de B, en caso
-- contrario, x es igual a 0"
f.[] = 0
f.bs = <Max i : 0 <= i < #bs : bs.i>

------------------------------------------------------------------------------
--EJERCICIO 2: Sea xs una lista no vacia, expresar:
--Suponiendo que #xs > 1 y que existen al menos 2 valores distintos en xs:
-- "x es el segundo valor más grande de xs"
f.xs = <Max j : 0 <= j < #xs ∧ distMax.xs.max(xs) : xs.i> <Max i : 0 <= i < #xs : xs.i>

max.xs = <Max i : 0 <= i < #xs : xs.i>

distMax.(x:xs).n
    | x == n = distMax xs
    | x /= n = n:distMax xs

--"s es la suma de los elementos de xs"
s.xs = <∑i : 0 <= i < #xs : xs.i>

--Dado un entero X: "n es la cantidad de veces que X aparece en xs"
s.xs.n = <Ni : 0 <= i < #xs ∧ n = xs.i : 1>

--p es el producto de todos los valores positivos de xs
p.xs = <∏i : 0 <= i < #xs ∧ xs.i > 0 : xs.i>

--Dado un entero x: "p es un booleano cuyo valor de verdad coincide con el de
-- la afirmación x E xs"
f.xs.x = <∃i : 0 <= i < #xs : xs.i = x>
p = f.xs.x

------------------------------------------------------------------------------
--EJERCICIO 3: Sea xs una lista no vacía, expresar en lenguaje común las
-- especificaciones
-- <∀i : 0 <= i < N ∧ N <= #xs : xs.i >= 0>
Esta especificación comprueba que todos los elementos de xs son positivos.

-- <∃i : 0 < i < N ∧ N <= #xs : xs.(i-1) < xs.i>
Esta especificación comprueba si hay algun elemento que menor que el siguiente,
o que cambie el método de ordenamiento

-- <∃i : 0 <= i < N ∧ N <= #xs : xs.i = 0>
Esta especificación comprueba si hay algun elemento igual a 0 en la lista de xs.

-- <∀p,q : 0 <= p ∧ 0 <= q ∧ p+q = N-1 ∧ N <= #xs : xs.p = xs.q>
-- <∀p,q : p > 0 ∧ q > 0 ∧ p+q = N-1 ∧ N <= #xs : xs.p = xs.q>
Esta especificación, dado un p y q positivos los cuales su suma tiene que ser igual
a N-1, comprueba que todos los p y q sean el mismo elemento/mismo valor.

------------------------------------------------------------------------------
--EJERCICIO 4: Dada una lista no vacia especificar:
--"xs es creciente"
<∀i,j : 0 <= i < j < #xs : xs.i <= xs.j>

--"si xs es creciente, entonces el primer elemento es el menor"
<∀i,j : 0 <= i < j < #xs : xs.i <= xs.j> -> <∀i : 0 <= i < #xs : xs.0 > xs.i>

------------------------------------------------------------------------------
--EJERCICIO 4: Especificar las siguientes funciones
-- f : [Num] -> Bool
-- f.xs determina si xs contiene igual cantidad de impares que pares
f.xs = <Ni : 0 <= i < #xs ∧ mod xs.i 2 == 0 : 1> 
       == <Ni : 0 <= i < #xs ∧ mod xs.i 2 /= 0 : 1>

-- cp : [Num] -> Num
-- cp.xs determina la cantidad de números pares que contiene xs
cp.xs = <Ni : 0 <= i < #xs ∧ mod xs.i 2 == 0 : 1>

-- g : Num -> [Num] -> Bool
-- g.k.xs determina si el k-ésimo elemento de xs aloja el máximo valor de xs
g.k.xs = xs.k == <Max i : 0 <= i < #xs : xs.i>

-- nonulo : [Num] -> Bool
-- nonulo.xs es True sii xs no contiene elementos nulos
nonulo.xs = <∀i : 0 <= i < #xs : xs.i /= 0>

-- prod : Num -> [Num] -> Bool
-- prod.x.xs es True sii x contiene el producto de los elementos de xs
prod.x.xs = x == <∏i : 0 <= i < #xs : xs.i>

-- meseta : [Num] -> Num -> Num -> Bool
-- meseta.xs.i.j determina si todos los valores de l a lista xs que están entre
--  los indices i, j son iguales
meseta.xs.i.j = <∀n : i <= n <= j : xs.i = xs.n> 

-- ordenada : [Num] -> Num -> Num -> Bool
-- ordenada.xs.i.j determina si la lista xs está ordenada entre los índices i, j.
--  Notar que ordenado puede ser creciente o decreciente
ordenada.xs.i.j = <∀n : i <= n < m <= j : xs.n <= xs.m> 
                    || <∀n : i <= n < m <= j : xs.n => xs.m>

------------------------------------------------------------------------------
--PRÁCTICO 10
------------------------------------------------------------------------------
--EJERCICIO 6: Especificar y derivar una función m que devuelve el mínimo de xs
m : [Num] -> Num
m.xs = <Min i : 0 <= i < #xs : xs.i>

--CB xs = []
m.[]
    [ESPECIFICACIÓN]
<Min i : 0 <= i < [] : [].i>
    [DEF CARDINAL]
<Min i : 0 <= i < 0 : [].i>
    [RANGO VACIO]
-inf

--CI xs = x:xs
--HI m.xs = <Min i : 0 <= i < #xs : xs.i>
m.(x:xs)
    [ESPECIFICACIÓN]
<Min i : 0 <= i < #(x:xs) : (x:xs).i>
    [DEF CARDINAL]
<Min i : 0 <= i < 1+#xs : (x:xs).i>
    [LÓGICA, PARTICIÓN DE RANGO]
<Min i : 0 <= i < 1 : (x:xs).i> 'Min' <Min i : 1 <= i < 1+#xs : (x:xs).i>
    [RANGO UNITARIO]
(x:xs).0 'Min' <Min i : 1 <= i < 1+#xs : (x:xs).i>
    [DEF POSICIÓN]
x 'Min' <Min i : 1 <= i < 1+#xs : (x:xs).i>
    [i <- i+1]
x 'Min' <Min i : 1 <= i+1 < 1+#xs : (x:xs).(i+1)>
    [ARITMETICA, DEF POSICIÓN]
x 'Min' <Min i : 0 <= i < #xs : xs.i>
    [HI]
x 'Min' m.xs

m.[] = -inf
m.(x:xs) = x 'Min' m.xs

------------------------------------------------------------------------------
--EJERCICIO 7: Especificar y derivar una función que dada una lista determine si
-- existe un elemento en ella que sea igual a la suma del resto de los elementos
f.xs = <∃i : 0 <= i < #xs : xs.i = sum.xs-xs.i>

--CB xs = []
f.[]
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #[] : [].i = sum.[]-[].i>
    [DEF CARDINAL]
<∃i : 0 <= i < 0 : [].i = sum.[]-[].i>
    [RANGO VACIO]
False

--CB xs = [x]
f.[x]
    [ESPECIFICACIÓN]
<∃i : 0 <= i < [x] : [x].i = sum.[x]-[x].i>
    [DEF CARDINAL, DEF SUM]
<∃i : 0 <= i < 1 : [x].i = x-[x].i>
    [RANGO UNITARIO]
[x].0 = x-[x].0
    [ARITMETICA]
x = x-x
    [ARITMETICA]
x = 0
    [LÓGICA]
False

--CI xs = x:xs
--HI f.xs = <∃i : 0 <= i < #xs : xs.i = sum.xs-xs.i>
f.(x:xs)
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #(x:xs) : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [DEF CARDINAL]
<∃i : 0 <= i < 1+#xs : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [LÓGICA, PARTICIÓN DE RANGO]
<∃i : 0 <= i < 1 : (x:xs).i = sum.(x:xs)-(x:xs).i> 
 v <∃i : 1 <= i < 1+#xs : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [RANGO UNITARIO]
(x:xs).0 = sum.(x:xs)-(x:xs).0 v <∃i : 1 <= i < 1+#xs : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [DEF POSICIÓN, DEF SUM]
x = x+sum.xs-x v <∃i : 1 <= i < 1+#xs : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [ARITMETICA]
x = sum.xs v <∃i : 1 <= i < 1+#xs : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [i <- i+1]
x = sum.xs v <∃i : 1 <= i+1 < 1+#xs : (x:xs).(i+1) = sum.(x:xs)-(x:xs).(i+1)>
    [ARITMETICA, DEF POSICIÓN, DEF SUM]
x = sum.xs v <∃i : 0 <= i < #xs : xs.i = x+sum.xs-xs.i>

    NO PODEMOS SEGUIR RESOLVIENDO Y NO TENEMOS CON QUE REEMPLAZAR LA HI, POR LO QUE
    PASAMOS A GENERALIZAR

g.z.xs = <∃i : 0 <= i < #xs : xs.i = z+sum.xs-xs.i>

--CB xs = []
g.z.[]
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #[] : [].i = z+sum.[]-[].i>
    [DEF CARDINAL]
<∃i : 0 <= i < 0 : [].i = z+sum.[]-[].i>
    [RANGO VACIO]
False

--CB xs = [x]
g.z.[x]
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #[x] : [x].i = z+sum.[x]-[x].i>
    [DEF CARDINAL, DEF SUM]
<∃i : 0 <= i < 1 : [x].i = z+x-[x].i>
    [RANGO UNITARIO]
[x].0 = z+x-[x].0
    [ARITMETICA]
x = z+x-x
    [ARITMETICA]
x = z
    [LÓGICA]
False

--CI xs = x:xs
--HI g.z.xs = <∃i : 0 <= i < #xs : xs.i = z+sum.xs-xs.i>
g.z.(x:xs)
    [ESPECIFICACIÓN]
<∃i : 0 <= i < #(x:xs) : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
    [DEF CARDINAL]
<∃i : 0 <= i < 1+#xs : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
    [LÓGICA, PARTICIÓN DE RANGO]
<∃i : 0 <= i < 1 : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
 v <∃i : 1 <= i < 1+#xs : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
    [RANGO UNITARIO]
(x:xs).0 = z+sum.(x:xs)-(x:xs).0
v <∃i : 1 <= i < 1+#xs : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
    [DEF POSICIÓN, DEF SUM]
x = z+x+sum.xs-x v <∃i : 1 <= i < 1+#xs : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
    [ARITMETICA]
x = z+sum.xs v <∃i : 1 <= i < 1+#xs : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
    [i <- i+1]
x = z+sum.xs v <∃i : 1 <= i+1 < 1+#xs : (x:xs).(i+1) = z+sum.(x:xs)-(x:xs).(i+1)>
    [DEF POSICIÓN, DEF SUM, ARITMETICA]
x = z+sum.xs v <∃i : 0 <= i < #xs : xs.i = (z+x)+sum.xs-xs.i>
    [HI]
x = z+sum.xs v g.(z+x).xs

    COMO LLEGAMOS A UNA SOLUCIÓN GENERALIZANDO, AHORA LA APLICAMOS A LA FUNCIÓN
    QUE TENIAMOS ORIGINALMENTE

f.[] = False
f.[x] = False
f.(x:xs) = 0+sum.xs v g.(0.x).xs

------------------------------------------------------------------------------
--EJERCICIO 9: Especificar y derivar una función con subsegmentos que dadas dos
-- listas determina si la primera es subsegmento de la segunda
-- P.xs.ys = <∃as, bs :: ys = as++xs++bs>

--CB xs = []
P.[].ys
    [ESPECIFICACIÓN]
<∃as, bs :: ys = as++[]++bs>
    [DEF ++]
<∃as, bs :: ys = as++bs>
    [PARTICIÓN DE RANGO (as == [] o as /= [])]
<∃as, bs : as == [] : ys = as++bs> v <∃as, bs : as /= [] : ys = as++bs>
    [RANGO UNITARIO (ANIDADO)]
<∃bs :: ys = []++bs> v <∃as, bs : as /= [] : ys = as++bs>
    [DEF ++]
<∃bs :: ys = bs> v <∃as, bs : as /= [] : ys = as++bs>
    [INTERCAMBIO (CONJUNCIÓN CON TRUE)]
<∃bs : ys = bs : True> v <∃as, bs : as /= [] : ys = as++bs>
    [RANGO UNITARIO]
True v <∃as, bs : as /= [] : ys = as++bs>
    [ABSORCIÓN]
True

--CI x = x:xs, CB ys = []
P.(x:xs).[]
    [ESPECIFICACIÓN]
<∃as, bs :: [] = as++(x:xs)++bs>
    [IGUALDAD DE LISTAS]
<∃as, bs :: [] = as ∧ [] = (x:xs) ∧ [] = bs>
    [IGUALDAD DE LISTAS]
<∃as, bs :: [] = as ∧ False ∧ [] = bs>
    [RANGO VACIO]
False

--CI x = x:xs, y = y:ys
--HI P.xs.ys = <∃as, bs :: ys = as++xs++bs>
P.(x:xs).(y:ys)
    [ESPECIFICACIÓN]
<∃as, bs :: (y:ys) = as++(x:xs)++bs>
    [PARTICIÓN DE RANGO (as == [] o as /= [])]
<∃as, bs : as == [] : (y:ys) = as++(x:xs)++bs> 
 v <∃as, bs : as /= [] : (y:ys) = as++(x:xs)++bs>
    [RANGO UNITARIO (ANIDADO)]
<∃bs :: (y:ys) = []++(x:xs)++bs> v <∃as, bs : as /= [] : (y:ys) = as++(x:xs)++bs>
    [as = (a:as), VALIDO POR AS /= []]
<∃bs :: (y:ys) = []++(x:xs)++bs> 
 v <∃as, bs : (a:as) /= [] : (y:ys) = (a:as)++(x:xs)++bs>
    [DEF ++, IGUALDAD DE LISTAS ((a:as) /= [] = True)]
<∃bs :: (y:ys) = (x:xs)++bs> v <∃as, bs :: (y:ys) = (a:as)++(x:xs)++bs>
    [IGUALDAD DE LISTAS]
<∃bs :: y = x ∧ ys = xs++bs> v <∃as, bs :: y = a ∧ ys = as++(x:xs)++bs>
    [DISTRIBUTIVA]
x = y ∧ <∃bs :: ys = xs++bs> v <∃as, bs :: y = a ∧ ys = as++(x:xs)++bs>
    [INTERCAMBIO]
x = y ∧ <∃bs :: ys = xs++bs> v <∃as, bs : y = a : ys = as++(x:xs)++bs>
    [RANGO UNITARIO (ANIDADO)]
x = y ∧ <∃bs :: ys = xs++bs> v <∃as, bs :: ys = as++(x:xs)++bs>

    NO PODEMOS RESOLVER MAS ASI QUE HAY QUE MODULARIZAR LO CUAL ES MUY LARGO PERO
    QUEDA ASI:

Q.[].ys = True
Q.(x:xs).ys = False
Q.(x:xs).(y:ys) = (x = y) v Q.xs.ys

------------------------------------------------------------------------------
--EJERCICIO 10: Especificar y derivar una función que dada una lista de números
-- calcula el promedio de la misma, recorriendo la lista una sola vez (tupling)
suma.xs = <∑i : 0 <= i < #xs : xs.i>
cant.xs = <Ni : 0 <= i < #xs : 1>
f.xs = (suma.xs, cant.xs)

--DERIVACIÓN SUMA
--CB xs = []
suma.[]
    [ESPECIFICACIÓN]
<∑i : 0 <= i < #[] : [].i>
    [DEF CARDINAL]
<∑i : 0 <= i < 0 : [].i>
    [RANGO VACIO]
0

--CI xs = x:xs
--HI suma.xs = <∑i : 0 <(a, b) = f.xs= i < #xs : xs.i>
suma.(x:xs)
    [ESPECIFICACIÓN]
<∑i : 0 <= i < #x:xs : (x:xs).i>
    [DEF CARDINAL]
<∑i : 0 <= i < 1+#xs : (x:xs).i>
    [LÓGICA, PARTICIÓN DE RANGO]
<∑i : 0 <= i < 1 : (x:xs).i> + <∑i : 1 <= i < 1+#xs : (x:xs).i>
    [RANGO UNITARIO]
(x.xs).0 + <∑i : 1 <= i < 1+#xs : (x:xs).i>
    [ARITMETICA]
x + <∑i : 1 <= i < 1+#xs : (x:xs).i>
    [i <- i+1, ARITMETICA, DEF POSICIÓN]
x + <∑i : 0 <= i < #xs : xs.i>
    [HI]
x + suma.xs

--DERIVACIÓN CANT
--CB xs = []
cant.[]
    [ESPECIFICACIÓN]
<Ni : 0 <= i < #[] : 1>
    [DEF CARDINAL]
<Ni : 0 <= i < 0 : 1>
    [RANGO VACIO]
0

--CI xs = x:xs
--HI cant.xs = <Ni : 0 <= i < #xs : 1>
cant.(x:xs)
    [ESPECIFICACIÓN]
<Ni : 0 <= i < #x:xs : 1>
    [DEF CARDINAL]
<Ni : 0 <= i < 1+#xs : 1>
    [LÓGICA, PARTICIÓN DE RANGO]
<Ni : 0 <= i < 1 : 1> + <Ni : 1 <= i < 1+#xs : 1>
    [RANGO UNITARIO]
1 + <Ni : 1 <= i < 1+#xs : 1>
    [i <- i+1, ARITMETICA]
1 + <Ni : 0 <= i < #xs : 1>
    [HI]
1 + cant.xs

suma.[] = 0
suma.(x:xs) = x + suma.xs

cant.[] = 0
cant.(x:xs) = 1 + cant.xs

--DERIVAMOS AHORA F
f.xs = (suma.xs, cant.xs)

--CB xs = []
f.[]
    [ESPECIFICACIÓN]
(suma.[], cant.[])
    [ESPECIFICACIONES SUMA Y CANT]
(0, 0)

--CI xs = x:xs
--HI f.xs = (suma.xs, cant.xs)
f.(x:xs)
    [ESPECIFICACIÓN]
(suma.(x:xs), cant.(x:xs))
    [ESPECIFICACIONES SUMA Y CANT]
(x+suma.xs, 1+cant.xs)
    [INTRODUCCIÓN -> a = suma.xs, b = cant.xs]
(x+a, 1+b)
    [IGUALDAD DE PARES -> (a, b) = (suma.xs, cant.xs)]
(x+a, 1+b)
    [HI]
(a, b) = f.xs

--CONCLUSIÓN
f.[] = (0, 0)
f.(x:xs) = (x+a, 1+b)
            [(a,b) = f.xs]

promedio = f.xs.0/f.xs.1
        f.xs.0 = suma.xs, f.xs.1 = cant.xs

------------------------------------------------------------------------------
--INDUCCIÓN Y RECURSIÓN, EJERCICIOS DEL LIBRO
--PÁGINA 169
------------------------------------------------------------------------------
--EJERCICIO 1: Dada la sucesión de fibonacci:
--  fib.0 = 0
--  fib.1 = 1
--  fib(n+2) = fib.n + fib.(n+1)
--
-- Demostrar la siguiente especificación:
-- <∀n : 0 <= n : fib.n < 2^n>

--CB n = 0
fib.0
    [ESPECIFICACIÓN]
<∀n : 0 <= 0 : fib.0 < 2^0>
    [RANGO VACIO]
True

--CB n = 1
fib.1
    [ESPECIFICACIÓN]
<∀n : 0 <= 1 : fib.1 < 2^1>
    [RANGO UNITARIO]
fib.1 < 2^1
    [DEF FIB, ARITMETICA]
1 < 2
    [LÓGICA]
True

--CI n = n+1
--HI fib.n = <∀n : 0 <= n : fib.n < 2^n>
fib.(n+1)
    [ESPECIFICACIÓN]
<∀n : 0 <= n+1 : fib.(n+1) < 2^(n+1)>
    [n <- n+1]
<∀n : 0 <= (n+1)+1 : fib.((n+1)+1) < 2^((n+1)+1)>
    [ARITMETICA]
<∀n : 0 <= n+2 : fib.(n+2) < 2^(n+2)>
    [DEF FIB, DEF POTENCIA]
<∀n : 0 <= n+2 : fib.n + fib.(1+1) < 2^n*2^2)>
    [DEF FIB, ARITMETICA]
<∀n : 0 <= n+2 : fib.n + fib.1 + fib.1 < 2^n*2^2)>
    [DEF FIB]
<∀n : 0 <= n+2 : fib.n + 1 + 1 < 2^n*2^2)>
    [ARITMETICA]
<∀n : 0 <= n+2 : 2 + fib.n < 2^n*2^2)>

GENERALIZAMOS
g.n = <∀n : 0 <= n+i : i + fib.n < 2^i*2^n)>

------------------------------------------------------------------------------
--DERIVACIÓN DE LISTAS, EJERCICIOS DEL LIBRO
--PÁGINA 201
------------------------------------------------------------------------------
--EJERCICIO 1: Derivar una función recursiva para la función
-- f : Int -> [Num] -> Bool
-- la cual determinar si el k-esimo elemento de una lista de números aloja el
-- mínimo valor de la misma

f : Int -> [Num] -> Bool
f.k.xs = <∀i : 0 <= i < #xs : xs.k <= xs.i>

--CB xs = []
f.k.[] 
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[] : [].k <= [].i>
    [DEF CARDINAL]
<∀i : 0 <= i < 0 : [].k <= [].i>
    [RANGO VACIO]
True

--CI xs = x:xs
--HI f.k.xs = <∀i : 0 <= i < #xs : xs.k <= xs.i>
f.k.(x:xs)
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #(x:xs) : (x:xs).k <= (x:xs).i>
    [DEF CARDINAL]
<∀i : 0 <= i < 1+#xs : (x:xs).k <= (x:xs).i>
    [LÓGICA, PARTICIÓN DE RANGO]
<∀i : 0 <= i < 1 : (x:xs).k <= (x:xs).i> ∧ <∀i : 1 <= i < 1+#xs : (x:xs).k <= (x:xs).i>
    [RANGO UNITARIO]
(x:xs).k <= (x:xs).0 ∧ <∀i : 1 <= i < 1+#xs : (x:xs).k <= (x:xs).i>
    [DEF POSICIÓN]
(x:xs).k <= x ∧ <∀i : 1 <= i < 1+#xs : (x:xs).k <= (x:xs).i>
    [i <- i+1, ARITMETICA, DEF POSICIÓN]
(x:xs).k <= x ∧ <∀i : 0 <= i < #xs : (x:xs).k <= xs.i>

MODULARIZACIÓN
g.k.z.xs = <∀i : 0 <= i < #xs : z.k <= xs.i>

--CB xs = []
g.k.z.[]
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[] : z.k <= [].i>
    [DEF CARDINAL]
<∀i : 0 <= i < 0 : z.k <= [].i>
    [RANGO VACIO]
True

--CI xs = x:xs
--HI g.k.z.xs = <∀i : 0 <= i < #xs : z.k <= xs.i>
g.k.z.(x:xs)
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #(x:xs) : z.k <= (x:xs).i>
    [DEF CARDINAL]
<∀i : 0 <= i < 1+#xs : z.k <= (x:xs).i>
    [LÓGICA, PARTICIÓN DE RANGO]
<∀i : 0 <= i < 1 : z.k <= (x:xs).i> ∧ <∀i : 1 <= i < 1+#xs : z.k <= (x:xs).i>
    [RANGO UNITARIO, DEF POSICIÓN, i <- i+1, ARITMETICA]
z.k <= x ∧ <∀i : 0 <= i < #xs : z.k <= xs.i>
    [HI]
z.k <= x ∧ g.k.z.xs

--PARA CONCLUIR
f.k.[] = True
f.k.(x:xs) = z.k <= x ∧ g.k.z.xs

------------------------------------------------------------------------------
--EJERCICIO 2: Derivar una función recursiva para
-- f.xs.ys = <Min i, j : 0 <= i < #xs ∧ 0 <= j < #ys : |xs.i - ys.j|>

--CB xs = []
f.[].ys
    [ESPECIFICACIÓN]
<Min i, j : 0 <= i < #[] ∧ 0 <= j < #ys : |[].i - ys.j|>
    [DEF CARDINAL, LÓGICA]
<Min i, j : False ∧ 0 <= j < #ys : |[].i - ys.j|>
    [LÓGICA]
<Min i, j : False : |[].i - ys.j|>
    [RANGO VACIO]
-inf

--CB ys = []
f.[].ys
    [ESPECIFICACIÓN]
<Min i, j : 0 <= i < #xs ∧ 0 <= j < #[] : |xs.i - [].j|>
    [DEF CARDINAL, LÓGICA]
<Min i, j : 0 <= i < #xs ∧ False : |xs.i - [].j|>
    [LÓGICA]
<Min i, j : False : |xs.i - [].j|>
    [RANGO VACIO]
-inf

--CI xs = (x:xs), ys = (y:ys)
--HI f.xs.ys = <Min i, j : 0 <= i < #xs ∧ 0 <= j < #ys : |xs.i - ys.j|>
<Min i, j : 0 <= i < #(x:xs) ∧ 0 <= j < #(y:ys) : |(x:xs).i - (y:ys).j|>
    [DEF CARDINAL]
<Min i, j : 0 <= i < 1+#xs ∧ 0 <= j < 1+#ys : |(x:xs).i - (y:ys).j|>
    [LÓGICA]
<Min i, j : ((0 <= i < 1) v (1 <= i < 1+#xs))
 ∧ ((0 <= j < 1) v (1 <= j < 1+#ys)) : |(x:xs).i - (y:ys).j|>
    [PARTICIÓN DE RANGO]
<Min i, j : (0 <= i < 1) ∧ (0 <= j < 1) : |(x:xs).i - (y:ys).j|>
 'Min' <Min i, j : (1 <= i < 1+#xs) ∧ (1 <= j < 1+#ys) : |(x:xs).i - (y:ys).j|>
    [RANGO UNITARIO, ARITMETICA]
|x - y| 'Min' <Min i, j : (1 <= i < 1+#xs) ∧ (1 <= j < 1+#ys) : |(x:xs).i - (y:ys).j|>
    [i <- i+1, j <- j+1, ARITMETICA]
|x - y| 'Min' <Min i, j : 0 <= i < #xs ∧ 0 <= j < #ys : |(x:xs).(i+1) - (y:ys).(j+1)|>
    [DEF POSICIÓN]
|x - y| 'Min' <Min i, j : 0 <= i < #xs ∧ 0 <= j < #ys : |xs.i - ys.j|>
    [HI]
|x - y| 'Min' f.xs.ys

--PARA CERRAR
f.[].ys = False
f.xs.[] = False
f.(x:xs).(y:ys) = |x - y| 'Min' f.xs.ys

------------------------------------------------------------------------------
--PRÁCTICO 10
------------------------------------------------------------------------------
--EJERCICIO 1: Encontrar la wp
-- {wp} x := (x-y)*(x+y) {x+y^2 = 0}
{wp} x := (x-y)*(x+y) {x+y^2 = 0}
    [DEF WP]
wp.(x := (x-y)*(x+y)).(x+y^2 = 0)
    [DEF ASIGNACIÓN WP]
((x-y)*(x+y))+y^2 = 0
    [ARITMETICA]
(x^2+xy-xy-y^2)+y^2 = 0
    [ARITMETICA]
x^2-y^2+y^2 = 0
    [ARITMETICA]
x^2 = 0
    [ARITMETICA]
x = 0
WEAKEST PRECONDITION -> x = 0

-- {wp}q,r := q+1 , r-y{q*y+r = x}
{wp}q,r := q+1 , r-y{q*y+r = x}
    [DEF WP]
wp.(q,r := q+1, r-y).({q*y+r = x})
    [DEF ASIGNACIÓN WP]
(q+1)*y+(r-y) = x
    [ARITMETICA]
q*y+y+r-y = x
    [ARITMETICA]
q*y+r = x
WEAKEST PRECONDITION -> q*y-r = x

-- {wp}
-- a := a = b; (S1)
-- b := a = b; (S2)
-- a := a = b; (S3)(b = B) ∧ (a = A)
    [DEF Q, DEF S3]
wp.(S1).(wp.(S2).(wp.(a := a = b).((a = B) ∧ (b = A))))
    [DEF ASIGNACIÓN WP]
wp.(S1).(wp.(S2).(((a = b = B) ∧ (b = A))))
    [DEF S2]
wp.(S1).(wp.(b := a = b).(((a = b = B) ∧ (b = A))))
    [DEF ASIGNACIÓN WP]
wp.(S1).((((a = a = b = B) ∧ (a = b = A))))
    [SIMETRIA]
wp.(S1).((((b = B) ∧ (a = b = A))))
    [DEF S1]
wp.(a := a = b).((((b = B) ∧ (a = b = A))))
    [DEF ASIGNACIÓN WP]
((b = B) ∧ (a = b = b = A))
    [SIMETRIA]
(b = B) ∧ (a = A)
WEAKEST PRECONDITION -> (b = B) ∧ (a = A)

------------------------------------------------------------------------------
--EJERCICIO 2: Calcular expresiones E tal que
-- {A = q*B+r} q := E; r := r-B {A = q*B+r}
{A = q*B+r} q := E; r := r-B {A = q*B+r}
    [DEF WP]
A = q*B+r -> wp.(q := E; r := r-B).(A = q*B+r)
    [DEF ASIGNACIÓN WP]
A = q*B+r -> A = E*B+r-B
    [LEIBNITZ]
q*B+r = E*B+r-B
    [ARITMETICA]
(q*B+r-r+B)/B = E
    [ARITMETICA]
(q*B+B)/B = E
    [ARITMETICA (FACTOR COMUN B)]
B*(q+1)/B = E
    [ARITMETICA]
E = q+1

--CORROBORAMOS
A = q*B+r -> A = E*B+r-B
    [REEMPLAZAMOS E]
A = q*B+r -> A = (q+1)*B+r-B
    [ARITMETICA]
A = q*B+r -> A = q*B+B+r-B
    [ARITMETICA]
A = q*B+r -> A = q*B+r
    [LEIBNITZ]
A = A
    [LÓGICA]
True

-- {x*y+p*q = N} x:= x-p; q := E {x*y+p*q = N}
{x*y+p*q = N} x:= x-p; q := E {x*y+p*q = N}
    [DEF WP]
x*y+p*q = N -> wp.(x:= x-p; q := E).(x*y+p*q = N)
    [DEF ASIGNACIÓN WP]
x*y+p*q = N -> (x-p)*y+p*E = N
    [ARITMETICA]
x*y+p*q = N -> x*y-p*y+p*E = N
    [LEIBNITZ]
x*y-p*y+p*E = x*y+p*q
    [ARITMETICA]
E = (x*y+p*q-x*y+p*y)/p
    [ARITMETICA]
E = (p*q+p*y)/p
    [ARITMETICA (FACTOR COMUN P)]
E = p(q+y)/p
    [ARITMETICA]
E = q+y

--CORROBORAMOS
x*y+p*q = N -> x*y-p*y+p*E = N
    [REEMPLAZAMOS E]
x*y+p*q = N -> x*y-p*y+p*(q+y) = N
    [ARITMETICA]
x*y+p*q = N -> x*y+p*q = N
    [LEIBNITZ]
N = N
    [LÓGICA]
True

------------------------------------------------------------------------------
--EJERCICIO 3: Demostrar la corrección
-- {x = A ∧ y = B}
-- x := x-y; (S1)
-- y := x+y; (S2)
-- x := y-x; (S3)
-- {x = B ∧ y = A}
P -> wp.S1.(wp.S2.(wp.S3.Q))
    [DEF P, DEF WP S3, DEF Q]
x = A ∧ y = B -> wp.S1.(wp.S2.(wp.(x := y-x).(x = B ∧ y = A)))
    [DEF ASIGNACIÓN WP]
x = A ∧ y = B -> wp.S1.(wp.S2.(y-x = B ∧ y = A))
    [DEF WP S2]
x = A ∧ y = B -> wp.S1.(wp.(y := x+y).(y-x = B ∧ y = A))
    [DEF ASIGNACIÓN WP]
x = A ∧ y = B -> wp.S1.(x+y-x = B ∧ x+y = A)
    [DEF WP S1]
x = A ∧ y = B -> wp.(x := x-y).(x+y-x = B ∧ x+y = A)
    [ARITMETICA]
x = A ∧ y = B -> wp.(x := x-y).(y = B ∧ x+y = A)
    [DEF ASIGNACIÓN WP]
x = A ∧ y = B -> y = B ∧ x-y+y = A
    [ARITMETICA]
x = A ∧ y = B -> y = B ∧ x = A
    [LEIBNITZ]
x = A ∧ y = B -> B = B ∧ A = A
    [LÓGICA (True ∧ True)]
x = A ∧ y = B -> True
    [LÓGICA]
True
-- Por lo tanto se demuestra la corrección

------------------------------------------------------------------------------
--EJERCICIO 4: Demostrar la corrección
-- En todos los casos tenemos (x, y : Int) y (a, b : Bool)
-- {True}
-- if x >= y -> skip            (S1)
-- [] x <= y -> x, y := y, x    (S2)
-- fi
-- {x >= y}

-- I. [True -> x >= y v x <= y]
-- II. {True ∧ x >= y} skip {x >= y}
-- III. {True ∧ x <= y} x,y := y,x {x >= y}

True -> x >= y v x <= y
    [LÓGICA]
True -> True
    [LÓGICA]
True

{True ∧ x >= y} skip {x >= y}
    [DEF WP]
True ∧ x >= y -> wp.skip.(x >= y)
    [NEUTRO ∧]
x >= y -> wp.skip.(x >= y)
    [DEF WP SKIP]
x >= y -> x >= y
    [LÓGICA]
True

{True ∧ x <= y} x,y := y,x {x >= y}
    [DEF WP]
True ∧ x <= y -> wp.(x,y := y,x).(x >= y)
    [NEUTRO ∧]
x <= y -> wp.(x,y := y,x).(x >= y)
    [DEF ASIGNACIÓN WP]
x <= y -> y >= x
    [LÓGICA]
x <= y -> x <= y
    [LÓGICA]
True