--1- Leer capitulos 1 y 2 del libro

--2- 
--head, retorna el primer elemento de una lista
hd2 :: [a] -> a
hd2 (x:xs) = x

--tail, retorna toda la lista menos el primer elemento
tl2 :: [a] -> [a]
tl2 (x:xs) = xs

--last, retorna el último elemento de la lista
last2 :: [a] -> a
last2 [x] = x 
last2 (x:xs) = last2 xs

--init, retorna toda la lista menos el último elemento
init2 :: [a] -> [a]
init2 [x] = []
init2 (x:xs) = x : init2 xs

