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