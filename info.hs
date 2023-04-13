--let X sirve para definir un nombre en GHCI, lo podemos realizar
--con variables simples y listas.
--ej: let a = 1 == a = 1

---------------------------------------------------------------

--CONCATENAR 2 LISTAS: ++
--CONCATENAR 1 ELEMENTO Y 1 LISTA: : // Inserta el elemento al
--                                      concatenar al comienzo
--OBTENER 1 ELEMENTO DE LA LISTA: !! X //X = Posición

--Funciones para operar en listas:
--  head: devuelve el primer elemento
--  tail: devuelve toda la lista menos el primer elemento
--  last: devuelve el último elemento
--  init: devuelve toda la lista menos el último elemento
--  lenght: devuelve el tamaño de la lista
--  null: comprueba si la lista esta vacia(true) o no(false)
--  reverse: pone del revés a la lista
--  take x: toma los x primeros elementos de la lista
--  drop x: elimina los x primeros elementos de la lista
--  maximum: devuelve el elemento de mayor valor
--  minimum: devuelve el elemento de menor valor
--  sum: suma todos los elementos de la lista entre si
--  product: multiplica todos los elementos entre si
--  elem x: nos dice si x esta en la lista(true) o no(false)

---------------------------------------------------------------

--TEXAS RANGOS: Es escribir las expresiones por rangos
--ej: [1..10] == [1,2,3,4,5,6,7,8,9,10]
--ej: ['a'..'z'] == "abcdefghijklmnopqrstuvwxyz"

-- ¿QUE PASA SI QUEREMOS ALGO MÁS ESPECIFICO? Solo separamos
-- los primeros dos números con una coma y especificando el
-- limite superior
-- ej: [2,4..20] == [2,4,6,8,10,12,14,16,18,20]
-- ej: [3,6..20] == [3,6,9,12,15,18]

--Más funciones para listas:
--  cycle
--  repeat
--  replicate

---------------------------------------------------------------

--LISTAS INTENSIONALES: Dado una función, un rango y un
--predicado (condición) devuelve una lista
--ej: [x*2 | x <- [1..10]] == [2,4,6,8,10,12,14,16,18,20]
--este ejemplo contiene función (x*2) y rango (x <- [1..10])

--ej: [x*2 | x <- [1..10], x*2 >= 12] == [12,14,16,18,20]
--este es el mismo ejemplo que el anterior pero con una condición
--nueva (x*2 >= 12)

--ej: boomBangs xs = [if x < 10 then "BOOM" else "BANG" | x <- xs, ood x]
--este ejemplo es para mostrar que se pueden utilizar en funciones

--ej: [x | x <- [10..20], x /= 13, x /= 15, x /= 19]
--ejemplo con varios predicados

--ej: [x*y | x <- [2,5,10], y <- [8,10,11], x*y > 50] == [55,80,100,110]
--ejemplo con 2 listas

--ej: removeNonUppercase st = [c | c <- st, elem c ['A'..'Z']]
--    removeNonUppercase "noMEGUSTANLASRANAS" = "MEGUSTANLASRANAS"
--ejemplo eliminando las minusculas de la lista

---------------------------------------------------------------

--TUPLAS: Son como las listas pero heterogeneas y son utilizadas cuando
--sabemos exactamente cuantos valores tienen que ser combinados
--ej: [(1,2), (3,4), (5,6)]

--Funciones en tuplas:
--  fst: toma una tupla y devuelve su primer componente
--       ej: fst (8,11) = 8
--  snd: toma una tupla y devuelve su segundo componente
--       ej: snd (8,11) = 11
--  zip: toma 2 listas y une sus elementos en tuplas
--       ej: zip [1,2,3] ["uno", "dos", "tres"] == [(1,"uno"),(2,"dos"),(3,"tres")]
--       SI EL TAMAÑO DE LAS LISTAS NO CONCUERDAN SE ACORTAN A LA CANTIDAD MENOR

---------------------------------------------------------------

-- :t X //nos da el tipo de una expresión
--	Int     -> Representa enteros
--	Integer -> Representa enteros pero sin acotar asi que representan numeros muchos
--             mas grandes, pero Int es mas eficiente
--	Float   -> Representa reales, numeros con coma
--	Double  -> Representa reales pero con el doble de precisión
--	Bool    -> Representa tipos booleanos
--	Char    -> Representa un caracter

-- a -> Es una variable de tipo, puede ser cualquier tipo
-- Funciones polimórficas: Aquellas que su tipo es a

--Restricciones de clase: Son representadas con => al comienzo de la definición de la función.
--	Eq       -> Permite que el tipo contenga las funciones == y /=
--	Ord      -> Permite que contenga funciones de comparación cómo >, <, >=, <= para ser 
--              de este tipo tiene que ser Eq
--	Show     -> Permite representar sus elementos como cadenas
--	Read     -> Lo opuesto a Show, toma una cadena y devuelve su valor. Read solo funciona
--              con expresiones/operaciones y no con elementos debido a que tomar el 
--              resultado de la misma para interpretar su tipo:
--		EJ BIEN: read "8.2"+3.5 = 11.7
--		EJ MAL: read "4" = ERROR
--		EJ MAL CORREGIDO: read "4" :: Int = 4
--	Enum     -> Son tipos que pueden ser ordenados, podemos usar los miembros de las listas
--              aritméticas, tambien esta definido el succ y pred
--	Bounded  -> Poseen limites inferior y superiores con minBound y maxBound
--	Num      -> Clase de tipos númericos, sus miembros se comportan como todos los numeros
--              (Int, Integer, Float, Double), debe ser de tipo Show y Eq
--	Integral -> Es Num pero solo son Int e Integer
--	Floating -> Es Num pero solo son Float y Double

---------------------------------------------------------------

--Pattern Matching: Consta de construir los casos de tu código por
-- patrones de tal manera que cada vez que ejecutemos el código este 
-- vaya a parar solo al caso donde le corresponde.
-- error: Esta función toma una cadena y genera un error en tiempo de ejecución con la misma.

--As Patterns: Los patrones como son útiles para descomponer algo usando un patrón, 
-- de forma que se ligue con las variables que queramos y además podamos mantener 
-- una referencia a ese algo como un todo.
-- EJ: xs@(x:y:ys), esto es lo mismo que x:y:ys pero nos permite acceder facilmente a 
--     la lista completa usando xs en lugar de tener que escribir x:y:ys

--Guardas: A diferencia de los patrones, que aseguran que un valor tenga determinada forma,
-- las guardas son una forma de comprobar si alguna propiedad de un valor es cierta o falsa,
-- son como las sentencias if.
--where: liga variables a valores al final de una función de modo que toda la función y sus 
-- guardas puedan acceder a ellas.
-- EJ: En lugar de..
--	bmi weight height
--		| weight/height ^ 2 <= 18.5 = "Infrapeso"
--		| weight/height ^ 2 <= 25.0 = "Normal"
--		| weight/height ^ 2 <= 30.0 = "Sobrepeso"
--		| otherwise = "Gordo"

--	Podemos definirlo cómo
--	bmi weight height
--		| bmi <= skinny = "Infrapeso"
--		| bmi <= normal = "Normal"
--		| bmi <= over = "Sobrepeso"
--		| otherwise = "Gordo"
--		where bmi = weight/height ^ 2
--		      skinny = 18.5
--		      normal = 25.0
--		      over = 30.0
--	ó cómo:
--		where bmi = weight/height ^ 2
--		      (skinny, normal, over) = (18.5, 25.0, 30.0)

--let: Son como las where pero dejan ligar valores en cualquier lugar y son expresiones en si
-- mismas pero de uso muy local asi que no pueden extenderse entre las guardas.
-- Su forma es: let <definición> in <expresión>
-- Las variables que definamos en let son accesibles en la parte in.
-- Ej: [let square x = x*x in (square 5, square 3, square 2)]
--		= [(25,9,4)]
-- let puede ser utilizado en listas intensionadas sin tener que usar su parte in
--	Ej: calcBmis :: (RealFloat a) => [(a,a)] -> [a]
--	    calcBmis xs = [bmi | (w,h) <- xs, let bmi = w/h ^ 2]

--case: Son expresiones donde se toman casos especificos de código, son como los switch en C. 
-- Su sintaxis es: case <expresion> of <patron> -> resultado
--				    <patron> -> resultado
--				    <patron> -> resultado
--				    ...
-- Pueden ser utilizadas en cualquier lugar.
-- EJ: 
--   descList :: [a] -> String
--   descList xs = "The list is" ++ case xs of [] -> "empty"
--						                       [x] -> "unitary"
--						                       xs -> "complex"

---------------------------------------------------------------

--ALGUNAS FUNCIONES RECURSIVAS

--maximum: toma una lista de elementos ordenados y devuelve la más grande
-- DEF. 1:
-- maximum' :: (Ord a) => [a] -> a
-- maximum' [] = error "maximo de una lista vacia"
-- maximum' [x] = x
-- maximum' (x:xs)
--      | x > maxTail = x
--      | otherwise = maxTail
--      where maxTail = maximum' xs
-- DEF. 2:
-- maximum'' :: (Ord a) => [a] -> a
-- maximum'' [] = error "maximo de una lista vacia"
-- maximum'' [x] = x
-- maximum'' (x:xs) = max x (maximum'' xs)

--zip: toma dos listas y las combina en una
-- zip': [a] -> [b] -> [(a,b)]
-- zip' _ [] = []
-- zip' [] _ = []
-- zip' (x:xs) (y:ys) = (x,y): zip' xs ys

--quicksort: metodo de ordenamiento
-- quicksort :: (Ord a) => [a] -> [a]
-- quicksort [] = []
-- quicksort (x:xs) =
--    let bigSorted = quicksort [a | a <- xs, a > x]
--        smallSorted = quicksort [a | a <- xs, a <= x]
--        in smallSorted ++ [x] ++ bigSorted

---------------------------------------------------------------

--Funciones de orden superior: Son aquellas funciones que toman funciones cómo parámetros o
-- devuelven funciones cómo resultado
-- EJ:
-- zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
-- zipWith' _ [] _ = []
-- zipWith' _ _ [] = []
-- zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys
--
-- zipWith' (+) [4,2,5,6] [2,6,2,3] = [6,8,7,9]
-- zipWith' max [6,3,2,1] [7,3,1,5] = [7,3,2,5]
-- zipWith' (zipWith' (*)) [[1,2,3], [3,5,6], [2,3,4]] [[3,2,2], [3,4,5], [5,4,3]]
--          = [[3,4,6], [9,20,30], [10,12,12]]
-- zipWith' (++) ["foo ", "bar ", "baz "] ["fighters", "hoppers", "aldrin"]
--          = ["foo fighters", "bar hoopers", "baz aldrin"]
-- zipWith' (*) (replicate 5 2) [1..] = [2,4,6,8,10]
--
-- flip: Dada una función y 2 argumentos, devuelve una función parecida pero los dos
--  primeros paramétros estan intercambiados
--  flip' :: (a -> b -> c) -> (b -> a -> c)
--  flip' f = g
--      where g x y = f y x
--
--  EJ:
--    flip' zip [1,2,3,4,5] [6,7,8,9,0] = [(6,1),(7,2),(8,3),(9,4),(0,5)]

--Funciones currificadas: Currificar consiste en transformar una función que utiliza
-- multiples argumentos en una secuencia de funciones que utilizan un único argumento
-- Ej:
-- max 4 5 == (max 4) 5

--Funciones al vuelo: Son aquellas funciones que se llaman con menos argumentos de los nec.
-- EJ: En lugar de..
-- compareWithHundred :: (Num a, Ord a) => a -> Ordening
-- compareWithHundred x = compare 100 x
--
-- Usamos..
-- compareWithHundred :: (Num a, Ord a) => a -> Ordening
-- compareWithHundred x = compare 100 x

--ASOCIACIONES Y FILTROS
--
-- map: Toma una función y una lista, le aplica esa función a la lista
-- map :: (a -> b) -> [a] -> [b]
-- map _ [] = []
-- map f (x:xs) = f x: map f xs
--
--  EJ:
--  map (+3) [1,2,3,4,5] = [4,5,6,7,8]
--  map (++ "!") ["BIFF", "BANG", "PUFF"] = ["BIFF!", "BANG!", "PUFF!"]
--  map (replicate 3) [3..6] = [[3,3,3], [4,4,4], [5,5,5], [6,6,6]]
--  map (map (^2)) [[1,2], [3,4,5,6], [7,8]] = [[1,4], [9,16,25,36], [49,64]]
--  map fst [(1,2), (3,5), (6,3), (2,6), (2,5)] = [1,3,6,2,2]

-- filter: Toma un predicado(Booleano) y una lista, devuelve la lista que lo satisface
-- filter :: (a -> Bool) -> [a] -> [a]
-- filter _ [] = []
-- filter p (x:xs)
--      | p x = x : filter p xs
--      | otherwise = filter p xs
--
--  EJ:
--  filter (>3) [1,5,3,2,1,6,4,3,2,1] = [5,6,4]
--  filter even [1..10] = [2,4,6,8,10]
--  let notNull x = not (null x) in filter notNull [[1,2,3], [], [3,4,5], [2,2], [], []]]
--          = [[1,2,3], [3,4,5], [2,2]]
--  filter ('elem' ['A'..'Z']) "i lauGh At You BecAuse u r aLL the Same" = "GAYBALLS"

--takeWhile: Toma un predicado y una lista, la recorre y devuelve estos elementos
-- mientras el predicado se mantenga cierto
--  EJ:
--  takeWhile (/= 9) [1..] = [1,2,3,4,5,6,7,8]
--  takeWhile (/= 'a') "Los elefantes" = "Los elef"
--  sum (takeWhile (<10000) (filter odd (map (^2) [1..]))) = 166650

--LAMBDAS: Son funciones anonimas que suelen ser usadas cuando necesitas una función una
-- sola vez, se usan para no tener que usar un where, estas son expresiones.
-- Se utiliza el \<expresión> para definirlas
--  EJ:
--  map (\(a,b) -> a+b) [(1,2), (3,5), (6,3)] = [3, 8, 9]

--Pliegues(folds): Son funciones que toman una función binaria (sumas, restas, etc), 
-- un valor inicial (acumulador) y una lista que plegar.
--Hay 2 tipos de pliegues:
--	•foldl: Pliega la lista empezando desde la izquierda, la función binaria es aplicada
--   junto a el valor inicial y la cabeza de la lista.
--	 EJ: 
--	 sum' :: (Num a) => [a] -> a
--	 sum' xs = foldl (\acc x -> acc + x) 0 xs
--		La función lambda (\acc) es lo mismo que (+)
--
--	MISMA FUNCIÓN PERO SIN LAMBDA
--	 sum' :: (Num a) => [a] -> a
--	 sum' xs = foldl (+) 0 xs
--
--	MISMA FUNCIÓN PERO CURRIFICADA
--	 sum' :: (Num a) => [a] -> a
--	 sum' = foldl (+) 0
--
--	sum' [3,5,2,1]
--	0+3
--	 [3,5,2,1]
--	3+5
--	 [5,2,1]
--	8+2
--	 [2,1]
--	10+1
--	 [1]
--	11
--
-- Cuando estamos hablando de pliegues, tanto el tipo del acumulador como del resultado final son el mismo.
--
--	•foldr: Pliega por la derecha, la función binaria es aplicada al ultimo elemento de la lista.
--	EJ:
--	 map' :: (a -> b) -> [a] -> [b]
--	 map' f xs = foldr (\x acc -> f x : acc) [] xs
--	 Lo que hace es evaluar el elemento del final y lo concatena en la cabeza del acumulador, 
--   en este caso, la lista vacia.
--
--	map' (+3) [1,2,3]
--	3+3 -> 6:[]
--	 [1,2,3]
--	2+3 -> 5:[6]
--	 [1,2]
--	1+3 -> 4:[5,6]
--	 [1]
--	[4,5,6]
--
--	REFLEXIÓN DE ESTE EJEMPLO: Podriamos haber aplicado esto mismo con un 
--  foldl (map' f xs = foldl(\acc x -> acc + [f x]) [] xs) pero el problema es que la función ++ es bastante
--  menos eficiente que :, asi que normalmente usaremos foldr cuando construimos a partir de una lista.

-- foldl y foldr: Funcionan de la misma manera solo que el foldl consume elementos por la izquierda 
-- (desde el primero) y el foldr consume elementos por la derecha (desde el ultimo).
-- La función binaria de foldl tienen el acumulador cómo primer parametro y el valor actual cómo segundo
-- parametro (\acc x -> ...) mientras que la función binaria de foldr es al revez, tiene como primer 
-- parametro al valor actual y como acumulador al segundo parametro (\x acc -> ...).

-- Si ponemos al revez una lista podemos hacer foldl como si fuera un foldr y viceversa.

-- Los foldlr funcionan con listas infinitas mientras que los foldl no ya que si a una lista infinita 
-- le aplicas foldr, en algun momento va a llegar al inicio de esa lista, mientras que si le aplicamos foldl,
-- nunca llegariamos al final de la misma.

-- Las funciones foldl1 foldr1 son muy parecidas a foldl y foldr, solo que no hay necesidad de indicar 
-- un valor inicial ya que asumen que el primer(último) elemento de la lista es el valor inicial. 
-- Tienen errores de compilación con listas vacias, lo que no sucede con foldl o foldr.
--	Ej: sum = foldl1 (+)
--
-- scanl y scanr: Son como foldl y foldr pero tambien devuelve cómo resultado los acumuladores intermedios,
-- es decir, los valores que vamos acumulando durante el proceso.
-- MISMO EJ DE SUMA:
--  scanl (+) 0 [3,5,2,1] = [0,3,8,10,11]
--  scanr (+) 0 [3,5,2,1] = [11,8,3,1,0]
--  Como vemos, ademas del res. final, da los res. parciales. Además, al usar scanl, el resultado final 
--  sera el último elemento de la lista resultante mientras que son scanr sera el primero.

--Funciones con $
-- ($) :: (a -> b) -> a -> b
-- f $ x = f x
--
-- Mientras que el espacio entre funciones tiene un alto orden de precedencia (asocia de izquierdas), 
-- la función $ tiene un bajo orden de precedencia (asocia a la derecha).
-- Basicamente sirve para no tener que escribir tanto, la expresión a la derecha del $ sera aplicada cómo 
-- parámetro a la función de la izquierda.
-- EJ:
--  sqrt 3 + 4 + 9 = suma 9 más 4 más raiz de 3
--	si queremos la raiz de 3 + 4 + 9 es...
--  sqrt (3 + 4 + 9)
--	o lo que es igual a...
--  sqrt $ 3 + 4 + 9

--Composición de funciones
-- En matematicas esta definido cómo: (f • g)x = f(g(x)) que significa que al componer 2 funciones 
-- obtenemos 1 nueva, tambien se puede ver que llamamos a g con x y luego llamamos a f con su resultado.
-- En Haskell la composición de funciones es practicamente lo mismo, esta definida cómo:
--  (.) :: (b -> c) -> (a -> b) -> a -> c
--  f . g = \x -> f(g x)
--
-- La composición de funciones se usa para crear funciones al vuelo pasa ser pasadas a otras funciones, 
-- se pueden usar lambdas en lugar de composición pero estas últimas son más claras y concisas.
--
-- EJ: CONVERTIR TODOS LOS NUMEROS A NEGATIVO, USANDO SU ABSOLUTO Y NEGANDOLO
--  CON LAMBDA...
--   map (\x -> negate(abs x)) [5,-3,-6,7,-3,2,-19,24]
--   = [-5,-3,-6,-7,-3,-2,-19,-24]
--
--  CON COMPOSICION...
--   map (negate . abs) [5,-3,-6,7,-3,2,-19,24]
--   = [-5,-3,-6,-7,-3,-2,-19,-24]
--
-- La composición de funciones es asociativa a derecha, es decir, que podemos componer varias 
-- funciones al mismo tiempo.
-- EJ:
--  map (\xs -> negate (sum (tail xs))) [[1..5], [3..6], [1..7]]
--  ==
--  map (negate . sum . tail) [[1..5], [3..6], [1..7]]
--
-- Con las funciones que toman varios parametros, si queremos usarlas en la composición de funciones, 
-- tenemos que aplicarlas parcialmente de forma que cada función tome solo un parámetro.
--
-- Otro uso común de la composición de funciones es la definición de funciones en el llamado estilo
-- libre de puntos.
--
-- Estilo libre de puntos: Es una función que no menciona explicitamente los puntos (valores) del 
-- espacio sobre los que actua.
-- EJ1:
--  sum' xs = foldl (+) 0 xs
--  ==
--  sum' = foldl (+) 0
--  EXPLICACIÓN: Gracias a la currificación, podemos eliminar xs de ambos lados ya que 'foldl (+) 0'
--  es una función que toma una lista.
-- EJ2:
--  fn = ceiling (negate (tan (cos (max 50 x))))
--  (No podemos eliminar simplemente x de ambos lados ya que 'max 50' solo no tiene mucho sentido 
--  por lo que usamos composición de funciones)
--  fn = ceiling . negate . tan . cos . max 50