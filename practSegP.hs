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
--PRÁCTICO 11
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

-- {True}
-- x, y := y*y, x*x;
-- if x >= y -> x := x+1
-- [] x <= y -> y := y-x
-- fi
-- {x >= 0 ∧ y >= 0}

--Dado S1: x,y := y*y, x*x
--     S2: if
--Hay que demostrar: P -> wp.S1.(wp.S2.Q)

--Para wp.if.Q hay que demostrar:
-- I. [B0 v B1 v...v Bn]
-- II. ∧ Bn -> wp.Sn.Q

-- I. [x >= y v x <= y]
x >= y v x <= y
    [LÓGICA, ya que x >= y/x <= y cubre todo el dominio en, post, pre a la y]
True

-- II. x >= y -> wp.(x := x+1).(x >= 0 ∧ y >= 0)
x >= y -> wp.(x := x+1).(x >= 0 ∧ y >= 0)
    [DEF ASIGNACIÓN WP]
x >= y -> x+1 >= 0 ∧ y >= 0
    [LÓGICA, ya que x+1 >= 0 e y >= 0]
x >= y -> x+1 >= y
    [LEIBNITZ, si x >= y entonces x+1 >= y]
True

-- II. x <= y -> wp.(y := y-x).(x >= 0 ∧ y >= 0)
x <= y -> wp.(y := y-x).(x >= 0 ∧ y >= 0)
    [DEF ASIGNACIÓN WP]
x <= y -> x >= 0 ∧ y-x >= 0
    [ARITMETICA]
x <= y -> x >= 0 ∧ -x >= -y
    [ARITMETICA]
x <= y -> x >= 0 ∧ x <= y
    [LEIBNITZ]
True

--Demostramos el wp.S2.Q, ahora demostramos lo que nos falta
P -> wp.S1.True
    [DEF S1, DEF P]
True -> wp.(x, y := y*y, x*x).True
    [DEF ASIGNACIÓN WP]
True -> True
    [LÓGICA]
True

-- {True}
-- if not a or b -> a := not a
-- [] a or not b -> b := not b
-- fi
-- {a v b}

-- I. [P -> (B0 v B1 v..v Bn)]
-- II. ∧ {P ∧ Bn} Sn {Q}

-- I. [True -> (not a or b) v (a or not b)]
True -> (not a or b) v (a or not b)
    [CONMUTATIVA v]
True -> (not a or a) v (b or not b)
    [TERCERO EXCLUIDO]
True -> True v True
    [LÓGICA]
True

-- II. {True ∧ not a or b} a := not a {a v b}
{True ∧ not a or b} a := not a {a v b}
    [DEF WP]
True ∧ not a or b -> wp.(a := not a).(a v b)
    [NEUTRO ∧, DEF ASIGNACIÓN WP]
not a or b -> not a v b
    [LÓGICA]
True

-- II. {True ∧ a or not b} b := not b {a v b}
{True ∧ a or not b} b := not b {a v b}
    [DEF WP]
True ∧ a or not b -> wp.(b := not b).(a v b)
    [NEUTRO ∧, DEF ASIGNACIÓN WP]
a or not b -> a v not b
    [LÓGICA]
True

-- {N >= 0}
-- x := 0
-- do x <> N -> x := x+1
-- od
-- {x = N}

-- TEOREMA DEL DO, 5 PUNTOS
-- Inicialización: {P} S {I}
-- Postcondición: [I ∧ -B0 ∧..∧ -Bn -> Q]
-- Invariante: {Bn ∧ I} Sn {I}
-- Variante(a): I ∧ Bn -> v => 0
-- Variante(b): {I ∧ Bn ∧ v = A} Sn {v < A}

-- NECESITAMOS AVERIGUAR I
-- Vamos a hacerlo comprobando el ciclo y ver que no varia
x = 0 ----> x = N (Q)
N = 3 ----> x <> 3 = x+1
    0 <> 3 -> True, 0 < 3, 3-0 = 3
    1 <> 3 -> True, 1 < 3, 3-1 = 2
    2 <> 3 -> True, 2 < 3, 3-2 = 1
    3 <> 3 -> False, 3 = 3, 3-3 = 0

-- ANALIZANDO LA RECURSIÓN TENEMOS QUE
I = x <= N
v = N-x

--Inicialización
--{P}S{I}
{N >= 0} x := 0 {x <= N}
    [DEF WP]
N >= 0 -> wp.(x := 0).(x <= N)
    [DEF ASIGNACIÓN WP]
N >= 0 -> 0 <= N
    [ARITMETICA]
N >= 0 -> N >= 0
    [LEIBNITZ]
True

--Postcondición
--(I ∧ -Bn) -> Q
(x <= N ∧ x = N) -> x = N
    [LEIBNITZ]
True

--Invariante
--{I ∧ Bn}Sn{I}
{x <= N ∧ x <> N} x := x+1 {x <= N}
    [DEF WP]
x <= N ∧ x <> N -> wp.(x := x+1).(x <= N)
    [DEF ASIGNACIÓN WP]
x <= N ∧ x <> N -> x+1 <= N
    [LEIBNITZ Y LÓGICA (Si x <= N entonces tambien se cumple que x+1 <= N)]
True

--Variante(a)
--I ∧ Bn -> v >= 0
x <= N ∧ x <> N -> N-x >= 0
    [ARITMETICA]
x <= N ∧ x <> N -> N >= x
    [LEIBNITZ]
True

--Variante(b)
--{I ∧ Bn ∧ v = A} Sn {v < A}
{x <= N ∧ x <> N ∧ N-x = A} x := x+1 {N-x < A}
    [DEF WP]
x <= N ∧ x <> N ∧ N-x = A -> wp.(x := x+1).(N-x < A)
    [DEF ASIGNACIÓN WP]
x <= N ∧ x <> N ∧ N-x = A -> N-(x+1) < A
    [ARITMETICA, LEIBNITZ]
x <= N ∧ x <> N ∧ N-x = A -> N-x-1 < N-x
    [LÓGICA]
True

------------------------------------------------------------------------------
--Ejercicio 5
con N : Nat
var n : Nat; r : Bool
var A : array [0..N) of Nat

{N > 0}
n, r := 0, True

I = {r= <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N}

do n <> N
	n, r := n+1, r and A.n = A.(N-n-1)
od

{r= <∀i : 0 <= i < N : A.i = A.(N-i-1)>}

--Inicializaciòn
--{P}S{I}
{N > 0} n, r := 0, True {r= <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N}
	[DEF WP]
N > 0 -> wp.(n, r := 0, True).(r= <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N)
	[DEF ASIGNACIÒN WP]
N > 0 -> True = <∀i : 0 <= i < 0 : A.i = A.(N-i-1)> ∧ 0 <= 0 <= N
	[RANGO VACIO]
N > 0 -> True = 0 <= N
	[LÒGICA, ARITMETICA]
N > 0 -> N >=0
	[LÒGICA]
True

--Postcondiciòn
--(I ∧ -Bn) -> Q
(r= <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N) ∧ n = N -> r= <∀i : 0 <= i < N : A.i = A.(N-i-1)>
	[LEIBNITZ]
(r= <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N) ∧ n = N -> r= <∀i : 0 <= i < n : A.i = A.(N-i-1)>
	[LEIBNITZ]
(r= <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N) ∧ n = N -> r= r>
	[LÒGICA]
True

--Invariante
--{I ∧ Bn} Sn {I}
{(r= <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N) ∧ n <> N} n, r := n+1, r and A.n = A.(N-n-1) {r= <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N>}
	[DEF WP]
(r= <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N) ∧ n <> N -> wp.(n, r := n+1, r and A.n = A.(N-n-1)).(r = <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N>)
	[DEF ASIGNACIÒN WP]
(r= <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N) ∧ n <> N -> r and A.n = A.(N-n-1) = <∀i : 0 <= i < n+1 : A.i = A.(N-i-1)> ∧ 0 <= n+1 <= N>
	[PARTICIÒN DE RANGO]
(r= <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N) ∧ n <> N -> r and A.n = A.(N-n-1) = <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ <∀i : n <= i < n+1 : A.i = A.(N-i-1)> ∧ 0 <= n+1 <= N>
	[LEIBNITZ (SACO PARTE IZQUIERDA, MAS LEGIBLE)]
r and A.n = A.(N-n-1) = r and <∀i : n <= i < n+1 : A.i = A.(N-i-1)> ∧ 0 <= n+1 <= N>
	[RANGO UNITARIO]
r and A.n = A.(N-n-1) = r and A.n = A.(N-n-1) ∧ 0 <= n+1 <= N
	[LÒGICA (SI SE CUMPLE (0 <= n <= N y n <> N entonces 0 <= n < N) entonces se cumple 0 <= n+1 <= N)]
r and A.n = A.(N-n-1) = r and A.n = A.(N-n-1) ∧ True
	[LÒGICA]
r and A.n = A.(N-n-1) = r and A.n = A.(N-n-1)
	[LÒGICA]
True

--Variante(a)
--v = N-n
--(I ∧ Bn) -> v >= 0
r = <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N ∧ n <> N -> N-n >= 0
    [ARITMETICA]
r = <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N ∧ n <> N -> N >= n
    [ARITMETICA (LEIBNITZ)]
r = <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N ∧ n <> N -> N > n
    [LEIBNITZ]
r = <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ 0 <= n <= N ∧ n <> N -> True
    [LÓGICA]
True

--Variante(b)
--{I ∧ Bn ∧ v = A} Sn {v < A}
{r = <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ (0 <= n <= N) ∧ (n <> N) ∧ (N-n = A)}
n, r := n+1, r and A.n = A.(N-n-1)
{N-n < A}
    [DEF WP]
r = <∀i : 0 <= i < n : A.i = A.(N-i-1)> ∧ (0 <= n <= N) ∧ (n <> N) ∧ (N-n = A) ->
wp.(n, r := n+1, r and A.n = A.(N-n-1)).(N-n < A)
    [DEF SUSTITUCIÓN WP, SACO PARTE IZQUIERDA PARA MEJOR LECTURA]
N-n+1 < A
    [LEIBNITZ]
A+1 < A
    [LÓGICA]
False

------------------------------------------------------------------------------
--PRÁCTICO PARCIAL #1
------------------------------------------------------------------------------
--EJERCICIO 1: Especificar y derivar un programa funcional que, dada una secuencia
-- de números, devuelva la longitud de la secuencia inicial ordenada más larga

f.xs = <Max as, bs : xs = as++bs ∧ ordenada(as): #as>

--CB xs = []
f.[]
    [ESPECIFICACIÓN]
<Max as, bs : [] = as++bs : #as>
    [PROPIEDAD DE ++]
<Max as, bs : [] = as++bs ∧ as = [] ∧ bs = [] : #as>
    [RANGO UNITARIO, TERMINO CONSTANTE]
#[]
    [DEF CARDINAL]
0

--CI xs = x:xs
--HI f.xs = <Max as, bs : xs = as++bs : #as>
f.(x:xs)
    [ESPECIFICACIÓN]
<Max as, bs : (x:xs) = as++bs : #as>
    [PARTICIÓN DE RANGO]
<Max as, bs : (x:xs) = as++bs ∧ bs = [] : #as> 
'Max' 
<Max as, bs : (x:xs) = as++bs ∧ bs /= []: #as>
    [as <- (a:as) EN EL SEGUNDO TERMINO, YA QUE NO ES VACIO]
<Max bs : bs = [] : <Max as : (x:xs) = as++bs ∧ bs = [] : #as>> 
'Max' 
<Max as, bs : (x:xs) = as++(b:bs) ∧ (b:bs) /= []: #as>
    [RANGO UNITARIO, DEF ++]
<Max as : (x:xs) = as : #as> 
'Max' 
<Max as, bs : (x:xs) = as++(b:bs) ∧ (b:bs) /= []: #as>
    [DEF ++, IGUALDAD DE LISTAS]
<Max as : (x:xs) = as : #as> 
'Max' 
<Max as, b, bs : x = b ∧ xs = as++bs : #as>
    [RANGO UNITARIO]
<Max as : (x:xs) = as : #as> 
'Max' 
<Max as, bs : xs = as++bs : #as>
    [HI]
<Max as : (x:xs) = as : #as> 'Max' f.xs
    [Introducción de g.xs = <Max as : (x:xs) = as : #as>]
g.(x:xs) 'Max' f.xs

--PARA CERRAR
f.[] = 0
f.(x:xs) = g.(x:xs) 'Max' f.xs

------------------------------------------------------------------------------
--EJERCICIO 2: Calcular wp del siguiente programa
-- {wp}
-- if a >= b -> a := a-b;
-- [] b >= a -> b := b-a;
-- fi
-- {a > 0 ∧ b > 0}

--wp.if.Q = (B0 v B1 v...v Bn) ∧ (B0 -> wp.S0.Q) ∧...∧ (Bn -> wp.Sn.Q) 
(a >= b v b >= a) ∧ (a >= b -> wp.(a := a-b).(a > 0 ∧ b > 0))
    ∧ (b >= a -> wp.(b := b-a).(a > 0 ∧ b > 0))

a >= b v b >= a
    [ARITMETICA]
a >= b v a <= b
    [LÓGICA]
True

a >= b -> wp.(a := a-b).(a > 0 ∧ b > 0)
    [DEF SUSTITUCIÓN WP]
a >= b -> a-b > 0 ∧ b > 0
    [ARITMETICA]
a >= b -> a > b ∧ b > 0
    [LEIBNITZ]
a >= b -> True ∧ b > 0
    [NEUTRO ∧]
a >= b -> b > 0
    [LEIBNITZ]
b > 0

b >= a -> wp.(b := b-a).(a > 0 ∧ b > 0)
    [DEF SUSTITUCIÓN WP]
b >= a -> a > 0 ∧ b-a > 0
    [ARITMETICA]
b >= a -> a > 0 ∧ b > a
    [LEIBNITZ]
b >= a -> a > 0 ∧ True
    [NEUTRO ∧]
b >= a -> a > 0
    [LEIBNITZ]
a > 0

True ∧ b > 0 ∧ a > 0
    [NEUTRO ∧]
b > 0 ∧ a > 0

WEAKEST PRECONDITION: b > 0 ∧ a > 0

------------------------------------------------------------------------------
--EJERCICIO 3: Demostrar la siguiente corrección parcial
-- var i, k: Int;
-- cons N: Int;
-- array b[0, N] of Int;
-- {N > 0}
-- i, k := 1,0;
-- do i < N ∧ b[i] <= b[k] -> i := i+1
-- [] i < N ∧ b[i] >= b[k] -> k, i := i, i+1
-- od
-- {<∀j : 0 <= j < N : b[k] >= b[j]>}

--AL SER CORRECCIÓN PARCIAL DEBEMOS DEMOSTRAR:
-- Inicialización: {P}S{I}
-- Postcondición: (I ∧ -B0 ∧ -B1 ∧...∧ -Bn) -> Q
-- Invariante: {Bn ∧ I} Sn {I}

--DEBEMOS AVERIGUAR I
{I: i <= N ∧ i >= k}

--Inicialización
--{P}S{I}
{N > 0} i, k := 1, 0 {i <= N ∧ i >= k}
    [DEF WP]
N > 0 -> wp.(i, k := 1, 0).(i <= N ∧ i >= k)
    [DEF ASIGNACIÓN WP]
N > 0 -> 1 <= N ∧ 1 >= 0
    [ARITMETICA]
N > 0 -> N >= 1 ∧ 1 >= 0
    [LÓGICA]
N > 0 -> N >= 1 ∧ True
    [NEUTRO ∧]
N > 0 -> N >= 1
    [LÓGICA, LEIBNITZ]
    [(como n > 0 entonces va a ser que n es mayor o igual al sig, es decir n >= 1)]
True

--Postcondición
--(I ∧ -B0 ∧ -B1 ∧...∧ -Bn) -> Q
(i <= N ∧ i >= k) ∧ -(i < N ∧ b[i] <= b[k]) ∧ -(i < N ∧ b[i] >= b[k]) 
-> <∀i : 0 <= i < N : b[k] >= b[i]>
    [DE MORGAN]
(i <= N ∧ i >= k) ∧ (-(i < N) v -(b[i] <= b[k])) ∧ (-(i < N) v -(b[i] >= b[k])) 
-> <∀i : 0 <= i < N : b[k] >= b[i]>
    [ARITMETICA]
(i <= N ∧ i >= k) ∧ (i >= N v b[i] > b[k]) ∧ (i >= N v b[i] < b[k]) 
-> <∀i : 0 <= i < N : b[k] >= b[i]>
    [LÓGICA]
(i <= N ∧ i >= k) ∧ (i < N v b[i] = b[k]) -> <∀i : 0 <= i < N : b[k] >= b[i]>
    [LEIBNITZ]
(i <= N ∧ i >= k) ∧ (i < N v b[i] = b[k]) -> <∀i : 0 <= i < N : True>
    [TERMINO CONSTANTE]
(i <= N ∧ i >= k) ∧ (i < N v b[i] = b[k]) -> True
    [LEIBNITZ]
True

--Invariante
--{Bn ∧ I} Sn {I}
{i < N ∧ b[i] <= b[k] ∧ i <= N ∧ i >= k} i := i+1 {i <= N ∧ i >= k}
    [DEF WP]
i < N ∧ b[i] <= b[k] ∧ i <= N ∧ i >= k -> wp.(i := i+1).(i <= N ∧ i >= k)
    [DEF ASIGNACIÓN WP]
i < N ∧ b[i] <= b[k] ∧ i <= N ∧ i >= k -> i+1 <= N ∧ i+1 >= k
    [ARITMETICA]
    [si i <= N, i >= k entonces tambien se cumple que i+1 <= N, i+1 >= k]
i < N ∧ b[i] <= b[k] ∧ i <= N ∧ i >= k -> True
    [LÓGICA]
True

{i < N ∧ b[i] >= b[k] ∧ i <= N ∧ i >= k} k, i := i, i+1 {i <= N ∧ i >= k}
    [DEF WP]
i < N ∧ b[i] >= b[k] ∧ i <= N ∧ i >= k -> wp.(k, i := i, i+1).(i <= N ∧ i >= k)
    [DEF ASIGNACIÓN WP]
i < N ∧ b[i] >= b[k] ∧ i <= N ∧ i >= k -> i+1 <= N ∧ i+1 >= i
    [ARITMETICA]
    [si i <= N entonces tambien se cumple que i+1 <= N]
    [i+1 > i siempre]
i < N ∧ b[i] >= b[k] ∧ i <= N ∧ i >= k -> True
    [LÓGICA]
True

------------------------------------------------------------------------------
--EJERCICIO 4: Encontrar predicados P que se cumplan:
{x= A ∧ y= B}
x := x-y;
y := x+y;
x := y-x;
{x= B ∧ y= A}

------------------------------------------------------------------------------
--EJERCICIO 5: Encontrar predicados P que se cumplan:
-- {P} x,y := y*x, x*y {x+y > 0}
{P} x,y := y*x, x*y {x+y > 0}
    [DEF WP]
wp.(x,y := y*x, x*y).(x+y > 0)
    [DEF ASIGNACIÓN WP]
y*x+x*y > 0
P: (x > 0 ∧ y > 0) v (x < 0 ∧ y < 0)

-- {P} a := a ≡ b {a}
{P} a := a ≡ b {a}
    [DEF WP]
wp.(a := a ≡ b).a
    [DEF ASIGNACIÓN WP]
a ≡ b
P: b = a

------------------------------------------------------------------------------
--EJERCICIO 5: Demostrar que skip;skip es equivalente a skip
-- {P} skip {Q} = {P} skip {Q}; {P} skip {Q}
{P} skip {Q} = {P} skip {Q}; {P} skip {Q}
    [DEF WP]
wp.skip.Q = wp.skip.(wp.skip.Q)
    [DEF SKIP WP, lado derecho]
wp.skip.Q = wp.skip.Q
    [LÓGICA]
True

--EJERCICIO 6: Determinar wp de
-- x := x+1;
-- if x > 0 -> x := x-1;
-- [] x < 0 -> x := x+2;
-- [] x = 1 -> skip;
-- fi
-- {x >= 1}

--CONCATENACIÓN DE WP: wp.S1.(wp.S2.Q)
-- S1: x := x+1, S2: if
-- Demostrar S2
wp.S2.Q
    [DEF WP IF]
(x > 0 v x < 0 v x = 1) 
∧ (x > 0 -> wp.(x := x-1).(x >= 1))
∧ (x < 0 -> wp.(x := x+2).(x >= 1))
∧ (x = 1 -> wp.skip.(x >= 1))

(x > 0 v x < 0 v x = 1)
    [ARITMETICA]
x <> 0 v x = 1

x > 0 -> wp.(x := x-1).(x >= 1)
    [DEF ASIGNACIÓN WP]
x > 0 -> x-1 >= 1
    [ARITMETICA]
x > 0 -> x >= 2
    [LEIBNITZ]
True

x < 0 -> wp.(x := x+2).(x >= 1)
    [DEF ASIGNACIÓN WP]
x < 0 -> x+2 >= 1
    [ARITMETICA]
x < 0 -> x >= -1
    [LEIBNITZ]
x >= -1

x = 1 -> wp.skip.(x >= 1)
    [DEF WP SKIP]
x = 1 -> x >= 1
    [LEIBNITZ]
True

--JUNTANDO TODAS LAS CONJUNCIONES
x <> 0 v x = 1 ∧ True ∧ x >= -1 ∧ True
    [NEUTRO ∧]
x <> 0 v x = 1 ∧ x >= -1

wp.S1.(x <> 0 v x = 1 ∧ x >= -1)
    [DEF S1]
wp.(x := x+1).(x <> 0 v x = 1 ∧ x >= -1)
    [DEF SUSTITUCIÓN WP]
x+1 <> 0 v x+1 = 1 ∧ x+1 >= -1
    [ARITMETICA]
x <> -1 v x = 0 ∧ x >= -2
    [ARITMETICA]
x = -2 v x = 0

WEAKEST PRECONDITION: x = -2 v x = 0

------------------------------------------------------------------------------
--PRÁCTICO PARCIAL #2
------------------------------------------------------------------------------
--EJERCICIO 1: Especificar y derivar un programa funciona que, dada una secuencia
-- de números, devuelva la longitud de la secuencia final de ceros más larga
f.xs = <Max as, bs : xs = as++bs ∧ ceros.bs : #bs>
    where ceros.xs = <∀n : 0 <= n < #xs : xs.n = 0>

--CB xs = []
f.[]
    [ESPECIFICACIÓN]
<Max as, bs : [] = as++bs ∧ ceros.bs : #bs>
    [PROPIEDAD DE ++]
<Max as, bs : [] = as++bs ∧ as = [] ∧ bs = [] ∧ #ceros.bs : #bs>
    [RANGO UNITARIO, TERMINO CONSTANTE]
#[]
    [DEF CARDINAL]
0

--CI xs = x:xs
f.(x:xs)
    [ESPECIFICACIÓN]
<Max as, bs : (x:xs) = as++bs : #ceros.bs>

FALTA DERIVAR

------------------------------------------------------------------------------
--EJERCICIO 2: Decir si los siguientes programas son parcial o totalmente correctos.
-- Demostrarlos.
-- {True}
-- do True -> skip
-- od
-- {True}
-- {I = True}

-- Corrección parcial
-- Inicialización: {P}S{I}
-- Postcondición: (I ∧ -B0 ∧...∧ -Bn) -> Q
-- Invariante: {I ∧ Bn} Sn {I}

--Inicialización
{True} True {True} que es True

--Postcondición
True ∧ False -> True
    [LÓGICA]
False -> True
    [LÓGICA]
True

--Invariante
{True ∧ True} skip {True}
    [DEF WP]
True -> wp.skip.True
    [DEF SKIP WP]
True

-- Corrección total
-- Variante(a): (I ∧ Bn) -> v >= 0
-- Variante(b): {I ∧ Bn ∧ v = A} Sn {v < A}

-- Variante(a)
{True ∧ True ∧ v = A} -> skip {v < A}
    [DEF WP]
True ∧ True ∧ v = A -> wp.skip.(v < A)
    [NEUTRO ∧]
v = A -> v < A
    [LÓGICA]
Falso

COMO ES FALSO NO TENEMOS CORRECCION TOTAL PERO SI PARCIAL

------------------------------------------------------------------------------
--EJERCICIO 3: Probar que es correcto
-- {True}
-- if x >= y -> skip
-- [] y >= x -> x, y := y, x
-- fi
-- {x >= y}

--Dem if:
-- I. [True -> x >= y v y >= x]
-- II. {True ∧ x >= y} skip {x >= y}
-- III. {True ∧ y >= x} x,y := y,x {x >= y}

True -> x >= y v y >= x
    [LÓGICA]
True -> True
    [LÓGICA]
True

{True ∧ x >= y} skip {x >= y}
    [DEF WP]
True ∧ x >= y -> wp.skip.(x >= y)
    [DEF SKIP WP, NEUTRO ∧]
x >= y -> x >= y
    [LEIBITZ]
True

{True ∧ y >= x} x,y := y,x {x >= y}
    [DEF WP]
True ∧ y >= x -> wp.(x,y := y,x).(x >= y)
    [NEUTRO ∧, DEF ASIGNACIÓN WP]
y >= x -> y >= x
    [LEIBNITZ]
True

ES CORRECTO

------------------------------------------------------------------------------
--EJERCICIO 5: Demostrar la corrección
-- {N >= 0}
-- x, y := 0,1
-- do x /= N -> x, y := x+1, y+y
-- od
-- {y = 2*N}

--Sacar I
--x = 0, y = 1, N = 3
0 /= 3 -> 0+1,1+1 -> 1,2
1 /= 3 -> 1+1,2+2 -> 2,4
2 /= 3 -> 2+1,4+4 -> 3,8
3 /= 3

I: x <= N ∧ y = 2^x ∧ x < y
v: N-x

-- Inicialización: {P}S{I}
-- Postcondición: (I ∧ -B0 ∧..∧ -Bn) -> Q
-- Invariante: {I ∧ Bn} Sn {I}
-- Variante(a): (I ∧ Bn) -> v >= 0
-- Variante(b): {I ∧ Bn ∧ v = A} Sn {v < A}

-- Inicialización
{N >= 0} x, y := 0,1 {x <= N ∧ y = 2^x ∧ x < y}
    [DEF WP]
N >= 0 -> wp.(x, y := 0,1).(x <= N ∧ y = 2^x ∧ x < y)
    [DEF SUSTITUCIÓN WP]
N >= 0 -> 0 <= N ∧ 1 = 2^0 ∧ 0 < 1
    [LEIBNITZ, ARITMETICA]
N >= 0 -> True ∧ True ∧ True
    [LÓGICA]
True

-- Postcondición
x <= N ∧ y = 2^x ∧ x < y ∧ x = N -> y = 2*N
    [LEIBNITZ]
x <= N ∧ y = 2^x ∧ x < y ∧ x = N -> 2^x = 2^x
    [LÓGICA]
x <= N ∧ y = 2^x ∧ x < y ∧ x = N -> True
    [LÓGICA]
True

-- Invariante
{x <= N ∧ y = 2^x ∧ x < y ∧ x <> N} x, y := x+1, y+y {x <= N ∧ y = 2^x ∧ x < y}
    [DEF WP]
x <= N ∧ y = 2^x ∧ x < y ∧ x <> N -> wp.(x, y := x+1, y+y).(x <= N ∧ y = 2^x ∧ x < y)
    [DEF ASIGNACIÓN WP]
x <= N ∧ y = 2^x ∧ x < y ∧ x <> N -> x+1 <= N ∧ y+y = 2^x+1 ∧ x+1 < y+y
    [LEIBNITZ, LÓGICA]
x <= N ∧ y = 2^x ∧ x < y ∧ x <> N -> True ∧ True ∧ True
    [LÓGICA]
True

-- Variante(a)
(x <= N ∧ y = 2^x ∧ x < y ∧ x <> N) -> N-x >= 0
    [ARITMETICA]
(x <= N ∧ y = 2^x ∧ x < y ∧ x <> N) -> N >= x
    [LEIBNITZ]
(x <= N ∧ y = 2^x ∧ x < y ∧ x <> N) -> True
    [LÓGICA]
True

-- Variante(b)
{x <= N ∧ y = 2^x ∧ x < y ∧ x <> N ∧ N-x = A} x, y := x+1, y+y {N-x < A}
    [DEF WP]
x <= N ∧ y = 2^x ∧ x < y ∧ x <> N ∧ N-x = A -> wp.(x, y := x+1, y+y).(N-x < A)
    [DEF ASIGNACIÓN WP]
x <= N ∧ y = 2^x ∧ x < y ∧ x <> N ∧ N-x = A -> N-(x+1) < A
    [ARITMETICA]
x <= N ∧ y = 2^x ∧ x < y ∧ x <> N ∧ N-x = A -> N-x-1 < A
    [LEIBNITZ]
x <= N ∧ y = 2^x ∧ x < y ∧ x <> N ∧ N-x = A -> A-1 < A
    [LÓGICA]
x <= N ∧ y = 2^x ∧ x < y ∧ x <> N ∧ N-x = A -> True
    [LÓGICA]
True

------------------------------------------------------------------------------
--EJERCICIO 6: Hacer un programa imperativo que dadas dos variables enteras,
-- calcule en una de ellas el mínimo. Especificar y demostrar.
{True}
if x >= y -> x := y; 
[] x < y -> skip;
fi
{x <= y}

-- P -> B0 v...v Bn
-- {P ∧ Bn} Sn {Q}
True -> x >= y v x < y
    [LÓGICA]
True -> True
    [LÓGICA]
True

{True ∧ x >= y} x := y {x <= y}
    [DEF WP]
True ∧ x >= y -> wp.(x := y).(x <= y)
    [NEUTRO ∧, DEF ASIGNACIÓN WP]
x >= y -> y <= y
    [LÓGICA]
x >= y -> True
    [LÓGICA]
True

{True ∧ x < y} skip {x <= y}
    [DEF WP]
True ∧ x < y -> wp.skip.(x <= y)
    [NEUTRO ∧, DEF SKIP WP]
x < y -> x <= y
    [LEIBNITZ]
x < y -> True
    [LÓGICA]
True

------------------------------------------------------------------------------
--EJERCICIO 7: Programa en funcional que diga si un numero es potencia de dos
f.n = <∃i : 0 <= i < n : n = 2^i>

--CB n = 0
f.0
    [ESPECIFICACIÓN]
<∃i : 0 <= i < 0 : n = 2^i>
    [RANGO VACIO]
False

--CI n = n+1
--HI f.n = <∃i : 0 <= i < n : n = 2^i>
f.n+1
    [ESPECIFICACIÓN]
<∃i : 0 <= i < n+1 : n+1 = 2^i>
    [SEPARACIÓN DE TERMINOS]
<∃i : 0 <= i < n : n+1 = 2^i> v <∃i : n <= i < 1 : n+1 = 2^i>
    [RANGO UNITARIO]
<∃i : 0 <= i < n : n+1 = 2^i> v n+1 = 2^n
    
    GENERALIZAMOS g.n.x = <∃i : 0 <= i < n : n+x = 2^i>
    --CB n = 0
    n.0
        [ESPECIFICACIÓN]
    <∃i : 0 <= i < 0 : 0+x = 2^i>
        [RANGO VACIO]
    False

    --CI n = n+1
    n.n+1.x
        [ESPECIFICACIÓN]
    <∃i : 0 <= i < n+1 : n+1+x = 2^i>
        [PARTICIÓN DE RANGO]
    <∃i : 0 <= i < n : n+1+x = 2^i> v <∃i : n <= i < 1 : n+1+x = 2^i>
        [RANGO UNITARIO]
    <∃i : 0 <= i < n : n+1+x = 2^i> v n+1+x = 2^n
        [HI]
    g.n.(1+x) v n+1+x = 2^n

-- PARA CERRAR
f.0 = False
f.(n+1) = g.n.0

------------------------------------------------------------------------------
--EJERCICIO 8: Encontrar E
-- {True} i, s := 0, E {∑j : 0 <= j < i : a[i]}
{True} i, s := 0, E {s = Sum j : 0 <= j < i : a[i]}
    [DEF WP]
wp.(i, s := 0, E).(s = Sum j : 0 <= j < i : a[i])
    [DEF ASIGNACIÓN WP]
E = <Sum j : 0 <= j < 0 : a[0]>
    [RANGO VACIO]
E = 0

{True} i, s := 0, E {s = Sum j : 0 <= j <= i : a[i]}
    [DEF WP]
wp.(i, s := 0, E).(s = Sum j : 0 <= j <= i : a[i])
    [DEF ASIGNACIÓN WP]
E = Sum j : 0 <= j <= 0 : a[0]
    [RANGO UNITARIO]
E = a[0]

------------------------------------------------------------------------------
--REPASO LÓGICA PROPOSICIONAL
------------------------------------------------------------------------------
--EJERCICIO 1: Demostrar
-- P -> Q ≡ -P v Q
P -> Q
    [DEF ->]
P v Q ≡ Q
    [NEUTRO v]
P v Q ≡ Q v False
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
Q v (P ≡ False)
    [CONTRAPOSITIVA]
Q v -P
    [CONMUTATIVA]
-P v Q

--(P -> Q) v (Q -> P)
(P -> Q) v (Q -> P)
    [P -> Q ≡ -P v Q]
(-P v Q) v (-Q v P)
    [CONMUTATIVA, ASOCIATIVA v]
(-P v P) v (-Q v Q)
    [TERCERO EXCLUIDO]
True v True
    [ABSORCIÓN]
True

-- P v (P ∧ Q) ≡ P
P v (P ∧ Q) ≡ P
    [REGLA DORADA]
(P ∧ Q) ∧ P ≡ P ∧ Q
    [CONMUTATIVA, ASOCIATIVA ∧]
(P ∧ P) ∧ Q ≡ P ∧ Q
    [IDEMPOTENCIA]
P ∧ Q ≡ P ∧ Q
    [NEUTRO ≡]
True

------------------------------------------------------------------------------
--EJERCICIO 2: Averiguar quienes son caballeros y quienes mentirosos
-- A dice: yo soy un caballero y B es un mentiroso
A ≡ A ∧ -B
    [REGLA DORADA]
-B ≡ -B v A
    [NEUTRO v]
-B v False ≡ -B v A
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
-B v (False ≡ A)
    [CONTRAPOSITIVA]
-B v -A

-- A dice: yo soy un mentiroso y B es un caballero
A ≡ -A ∧ B
    [REGLA DORADA]
A ≡ -A ≡ B ≡ B v -A
    [NEUTRO v]
A ≡ -A ≡ B v False ≡ B v -A
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
A ≡ -A ≡ B v (False ≡ -A)
    [CONTRAPOSITIVA]
A ≡ -A ≡ B v A
    [CONTRAPOSITIVA]
False ≡ B v A
    [CONTRAPOSITIVA]
-B v -A

-- A dice: yo soy un caballero y B es un caballero
A ≡ A ∧ B
    [REGLA DORADA]
B ≡ B v A
    [NEUTRO v]
B v False ≡ B v A
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
B v (False ≡ A)
    [CONTRAPOSITIVA]
B v -A

-- Nos encontramos con A y B, A dice: al menos uno de nosotros es un mentiroso
A ≡ -A v -B
    [REGLA DORADA]
A ≡ -A ≡ -B ≡ -B ∧ -A
    [CONTRAPOSITIVA]
False ≡ -B ≡ -B ∧ -A
    [REGLA DORADA]
False ≡ -A ≡ -A v -B
    [NEUTRO v]
False ≡ -A v False ≡ -A v -B
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
False ≡ -A v (False ≡ -B)
    [CONTRAPOSITIVA]
False ≡ -A v B
    [CONTRAPOSITIVA]
A v -B

-- A dice: yo soy un mentiroso o B es un caballero
A ≡ -A v B
    [REGLA DORADA]
A ≡ -A ≡ B ≡ B ∧ -A
    [CONTRAPOSITIVA]
False ≡ B ≡ B ∧ -A
    [REGLA DORADA]
False ≡ -A ≡ -A v B
    [NEUTRO v]
False ≡ -A v False ≡ -A v B
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
False ≡ -A v (False ≡ B)
    [CONTRAPOSITIVA]
False ≡ -A v -B
    [CONTRAPOSITIVA]
A v B

-- Le preguntan a A si es un caballero, A dice: Si soy un caballero, entonces me
-- comere el sombrero. Demostrar que A se tiene que comer el sombrero
A ≡ A -> S
    [P -> Q ≡ -P v Q]
A ≡ -A v S
    [REGLA DORADA]
A ≡ -A ≡ S ≡ S ∧ -A
    [CONTRAPOSITIVA]
False ≡ S ≡ S ∧ -A
    [REGLA DORADA]
False ≡ -A ≡ -A v S
    [NEUTRO v]
False ≡ -A v False ≡ -A v S
    [(A v B) ≡ (A v C) ≡ A v (B ≡ C)]
False ≡ -A v (False ≡ S)
    [CONTRAPOSITIVA]
False ≡ -A v -S
    [CONTRAPOSITIVA]
A v S

------------------------------------------------------------------------------
--EJERCICIO 3: Dada la definición de N
-- <Ni : Ri : Ti> = <∑i : Ri ∧ Ti : 1>

--Enunciar y demostrar la regla de partición de rango de la contatoria
<Ni : Ri v Si : Ti>
    [DEF N]
<∑i : (Ri v Si) ∧ Ti : 1>
    [DISTRIBUTIVA]
<∑i : (Ri ∧ Ti) v (Si ∧ Ti) : 1>
    [PARTICIÓN DE RANGO]
<∑i : Ri ∧ Ti : 1> + <∑i : Si ∧ Ti : 1>
    [DEF N]
<Ni : Ri : Ti> + <Ni : Si : Ti>

--Idem con la regla del rango vacio
<Ni : false : Ti>
    [DEF N]
<∑i : False ∧ Ti : 1>
    [LÓGICA]
<∑i : False : 1>
    [RANGO VACIO]
0

--Probar <∑i : Ri ∧ Ti : K> = K*<Ni : Ri : Ti>
K*<Ni : Ri : Ti>
    [DEF N]
K*<∑i : Ri ∧ Ti : 1>
    [DISTRIBUTIVA DE K]
<∑i : Ri ∧ Ti : K*1>
    [ARITMETICA]
<∑i : Ri ∧ Ti : K>

------------------------------------------------------------------------------
--EJERCICIOS DE REPASO
------------------------------------------------------------------------------
--EJERCICIO 1: Dada la siguiente especificación y sea xs una lista no vacía, 
-- expresar la especificación en lenguaje natural, dando su enunciado.
-- f.xs = <∃ as, bs, cs : xs = as++bs++cs ∧ #bs>1 : capicua.bs>

DADA UNA LISTA NO VACIA, ENCONTRAR UN SUBSEGMENTO DE LA MISMA QUE SEA CAPICUA

--Especifica capicua.xs
capicua.xs = <∀i : 0 <= i < #xs : xs.i = xs.(#xs-i-1)>

--Dadas las funciones split3 : [a]− > [([a], [a], [a])] y split2 : [a]− > [([a], [a])]
--,escribir la especificación de f usando listas por comprensión.
split2.xs = [(take n xs, drop n xs) | n <- [0..#xs]]
split3.xs = [(as, bs, cs) | (as, ys) <- split2 xs, (bs, cs) <- split2 ys]

f.xs
    | length xs > 1 && foldl (||) False (split3 xs) = capicua.xs
    | otherwise = False

------------------------------------------------------------------------------
--EJERCICIO 2: Expresar en lenguaje natural y derivar
f.xs.ys = #xs = #ys ∧ <∀i : 0<= i <#xs : xs.i = ys.i>

LO QUE TENEMOS ES UNA FUNCIÓN QUE COMPRUEBA QUE AMBAS LISTAS SEAN IGUALES

--CB xs = []
f.[].ys 
    [ESPECIFICACIÓN]
#[] = #ys ∧ <∀i : 0<= i <#[] : [].i = ys.i>
    [DEF CARDINAL]
0 = #ys ∧ <∀i : 0<= i <0 : [].i = ys.i>
    [RANGO VACIO]
0 = #ys ∧ True
    [NEUTRO ∧]
#ys = 0

--CB ys = []
f.xs.[] 
    [ESPECIFICACIÓN]
#xs = #[] ∧ <∀i : 0<= i <#xs : xs.i = [].i>
    [DEF CARDINAL, DEF POSICIÓN]
#xs = 0 ∧ <∀i : 0<= i <#xs : xs.i = 0>
    [LÓGICA]
#xs = 0

--CB xs, ys = []
f.[].[] 
    [ESPECIFICACIÓN]
#[] = #[] ∧ <∀i : 0<= i <#[] : [].i = [].i>
    [DEF CARDINAL, RANGO VACIO]
True ∧ True
    [LÓGICA]
True

--CI xs, ys = x:xs, y:ys
--HI f.xs.ys = #xs = #ys ∧ <∀i : 0 <= i < #xs : xs.i = ys.i>
f.(x:xs).(y:ys)
    [ESPECIFICACIÓN]
#(x:xs) = #(y:ys) ∧ <∀i : 0 <= i < #(x:xs) : (x:xs).i = (y:ys).i>
    [DEF CARDINAL]
1+#xs = 1+#ys ∧ <∀i : 0 <= i < 1+#xs : (x:xs).i = (y:ys).i>
    [LÓGICA, PARTICIÓN DE RANGO]
1+#xs = 1+#ys ∧ <∀i : 0 <= i < 1 : (x:xs).i = (y:ys).i> 
 ∧ <∀i : 1 <= i < 1+#xs : (x:xs).i = (y:ys).i>
    [RANGO UNITARIO]
1+#xs = 1+#ys ∧ (x:xs).0 = (y:ys).0 ∧ <∀i : 1 <= i < 1+#xs : (x:xs).i = (y:ys).i>
    [DEF POSICIÓN, i <- i+1]
1+#xs = 1+#ys ∧ x = y ∧ <∀i : 1 <= i+1 < 1+#xs : (x:xs).(i+1) = (y:ys).(i+1)>
    [ARITMETICA, DEF POSICIÓN, CONMUTATIVA ∧]
x = y ∧ #xs = #ys ∧ <∀i : 0 <= i < #xs : xs.i = ys.i>
    [HI]
x = y ∧ f.xs.ys

------------------------------------------------------------------------------
--EJERCICIO 3: Dada la siguiente especificación, ¿Puede expresarla en lenguaje
-- natural? Determina el invariante, sugerir el programa que la satisface.
-- {P: N > 0}
-- {Q: r = <Min i : 0 <= i < N : a.i>}

cons N: Int;
var r, min, x: Int;
array a [x, N) of Int;

x, min := 0, 0;
{P: N > 0}
do x <> N ∧ a.x <= min -> x, min := x+1, a.x;
[] x <> N ∧ a.x > min -> x ;= x+1;
fi
{Q: r = <Min i : 0 <= i < N : a.i>}
{I: x <= N}

-- Inicialización
-- {P}S{I}
{N > 0} x, min := 0, 0 {x <= N}
    [DEF WP HOARE]
N > 0 -> wp.(x,min := 0, 0).(x <= N)
    [DEF ASIGNACIÓN WP]
N > 0 -> 0 <= N
    [LEIBNITZ]
True
