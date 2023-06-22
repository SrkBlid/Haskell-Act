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

--------------------------------------------------------------------------------------
-- Especificar y derivar una función f : [Nat] -> Nat -> Bool, tal que f.xs.k devuelve true cuando todos los elementos en posiciones mayores que k son mayores a xs.k

--------------------------------------------------------------------------------------
-- Dadas las siguientes definiciones funcionales:
--	    f^0 = id
--	    f^(n+1) = f • f^n
-- Donde • es la composición funcional, demostrar:
--	    f^n • f^m • f^h = f^(n+m+h)

--------------------------------------------------------------------------------------
-- Especificar y derivar la siguiente función: Dada una lista de números naturales, la función P dice si la suma de elementos pares es igual a la suma de los elementos impares de la lista.

--------------------------------------------------------------------------------------
-- Especificar y derivar un algoritmo imperativo que calcule el máximo común divisor de dos números positivos, recordar que el máximo común divisor posee las siguientes propiedades:
--	    mcd.x.x = x
--	    mcd.x.y = mcd.y.x
--	    Si x > y, entonces mcd.x.y = mcd.(x-y).y
--	    Si x < y, entonces mcd.x.y = mcd.x.(y-x)

--------------------------------------------------------------------------------------
----------------------------------------2016B-----------------------------------------
--------------------------------------------------------------------------------------
-- En la isla de mentirosos y caballeros se encuentran en el siguiente escenario:
--	    •A dice: B y yo somos del mismo tipo
--	    •B dice: A y yo somos de diferente tipo
--  ¿Qué puede deducir utilizando el cálculo proposicional dado en la materia?

--------------------------------------------------------------------------------------
-- Demostrar la siguiente propiedad:
--	    <Min i : R.i : -E.i> = - <Max i : R.i : F.i>

--------------------------------------------------------------------------------------
-- Dada la siguiente especificación de la función f : [Nat] -> [Nat] -> Bool:
--	    f.xs.ys = <∀i, j : 0 <= i < #xs ∧ 0 <= j < #ys : xs.i - ys.j = 0>
-- derive la función f.

--------------------------------------------------------------------------------------
-- Especificar y derivar un programa imperativo que dado dos números x e y, calcule su mínimo común múltiplo.

--------------------------------------------------------------------------------------
-- Demostrar que durante cualquier ciclo lo siguiente se cumple: 
--	    P ∧ t ≤ 0 ⇒ ¬B ≡ P ∧ B ⇒ t > 0
--  Teniendo en cuenta que P es el invariante del ciclo, B es la guarda y t es el variante.

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
