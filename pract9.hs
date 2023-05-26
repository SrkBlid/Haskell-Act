--EJERCICIO 1
--F es una función que determina si xs es una lista donde todos los
-- elementos son iguales
f :: [a] -> Bool
f.xs = <∀i : 0 < i < #xs : xs.0 = xs.i>

--F es una función que determina si xs es una lista donde todos los 
-- elementos son diferentes
f :: [a] -> Bool
f.xs = <∀i, j : 0 <= i < j < #xs : xs.i /= xs.j>

g :: [a] -> Bool
g.xs = <∀i : 0 <= i < #xs-1 : xs.i /= xs.(i+1)>

--F es una función que determina si xs es una lista de elementos ordenados
f :: [a] -> Bool
f.xs = <∀i, j : 0 <= i < j < #xs : xs.i <= xs.j>

--P es un predicado que es true cuando aparece 1 en xs 
-- entonces debe aparecer 0 en xs
P = <∃i : 0 <= i < #xs : xs.i = 1> ∧ <∃j : 0 <= j < #xs : xs.j = 0>
P' = <∃i, j : (0 <= i < #xs) ∧ (0 <= j < #xs) : xs.i = 1 && xs.j = 0>

--p es el producto de todos los elementos primos de xs
p = <∏i : 0 <= i < #xs ∧ esPrimo(i) : xs.i>
    where 
        esPrimo n = not <∃j : 1 < j < (n-1) : mod n j = 0>

------------------------------------------------------------------------------
--EJERCICIO 2: Sea xs una lista no vacia con elementos booleanos, tal que
-- true aparezca al menos una vez en la lista. Especificar:

--n es el menor entero tal que xs.n = true
n = <min i : 0 <= i < #xs ∧ xs.i = True : i>

--n es el último elementos de la lista tal que xs.n = true
n = <max i : 0 <= i < #xs ∧ xs.i : i>

--f es una función que devuelve true si todos los elementos de xs son iguales
f :: [a] -> Bool
f.xs = <∀i : 0 <= i < #xs : xs.0 = xs.i>

f' :: [a] -> Bool
f'.xs = <and i : 0 <= i < #xs : xs.i>

------------------------------------------------------------------------------
--EJERCICIO 3
--f.xs determina si xs tiene la misma cantidad de pares que impares
f :: [a] -> Bool
f.xs = <∑i : (0 <= i < #xs) : mod xs.i 2 = 0> == <∑j : (0 <= j < #xs) : mod xs.j 2 /= 0>

--f.n determina si n es primo
f :: Int -> Bool
f.n = not <∃j : 1 < j < (n-1) : mod n j = 0>

--f.xs.ys determina si ys es una subsecuencia de xs
f :: [a] -> Bool
f.xs.ys = <∃as, cs : xs = as++ys++cs> 

--f.xs.ys determinar si ys es una subsecuencia final de xs
f :: [a] -> Bool
f.xs.ys = <∃as : xs = as++ys>

------------------------------------------------------------------------------
--EJERCICIO 4
--Dada una lista de enteros, especifique la suma del subsegmento de suma minima
f :: [Int] -> [Int]
f.xs = <min as, bs, cs : xs = as++bs++cs : sum.bs>

--Especifique maxIgual que determina la longitud del máximo subsegmento en
-- donde todos los elementos son iguales.
maxIgual :: [a] -> Int
maxIgual.xs = <max as, bs, cs : xs = as++bs++cs ∧ 
                <∀i : (0 <= i < #bs) : bs.0 = bs.i >: #bs>

--Especifique maxDistinto que determina la longitud del subsegmento más largo
-- en donde todos los elementos son distintos.
maxDistintos :: [Int] -> Int
maxDistintos.xs = <max as, bs, cs : xs = as++bs++cs ∧
                <∀i, j : (0 <= i < j < #bs) : bs.i /= bs.j> : #bs>

------------------------------------------------------------------------------
--EJERCICIO 5
split2 :: [a] -> [([a], [a])]
split2 xs = [(take n xs, drop n xs) | n <- [0..length xs]]

split3 :: [a] -> [([a], [a], [a])]
split3 xs = [(as, bs, cs) | (as, ys) <- split2 xs, (bs, cs) <- split2 ys]

--La especificación del ejercicio 1(e) por listas por comprensión
--1(e) = p es el producto de todos los elementos primos de xs
<∏i : 0 <= i <= #xs ∧ esPrimo(i) : xs.i>
p xs = product [ xs!!n | n <- [0..length xs-1], esPrimo(xs!!n)]

--La especificación del ejercicio 3(c) por listas por comprensión
--3(c) = f.xs.ys determina si ys es una subsecuencia de xs
<∃as, cs : xs = as++ys++cs> 
esSubsecuencia xs ys = any (\(as, cs) -> xs == as++ys++cs) (split2 xs)

--La especificación del ejercicio 3(d) por listas por comprensión
--3(d) = f.xs.ys determinar si ys es una subsecuencia final de xs
f.xs.ys = <∃as : xs = as++ys>
esSubFin xs ys = any (\as -> xs == as++ys) (split2 xs)

--Dada una lista de números, calcular el valor del subsegmento
-- de suma maximo
f.xs = <max bs : xs = as++bs++cs : sum.bs>