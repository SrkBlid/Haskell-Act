--EJERCICIO 3
--tres = <∀i : 0 <= i <= #xs : xs.0 == xs.i>
tres :: Eq a => [a] -> Bool
tres [] = True
tres [x] = True
tres (x:xs)
    | x /= head xs = False
    | otherwise = tres xs

tres2 :: Eq a => [a] -> Bool
tres2 xs = and [n == head xs | n <- xs]

--EJERCICIO 4
--f.xs = <∏i : o <= i < #xs : xs.i>
cuatro :: [Int] -> Int
cuatro xs = product xs

--EJERCICIO 5
--f.xs = <∀i : 0 <= i < #xs-1 : xs.i <= xs.(i+1)>
cinco :: Ord a => [a] -> Bool
cinco (x:xs) = False

cinco2 :: Ord a => [a] -> Bool
cinco2 [] = True
cinco2 [x] = True
cinco2 (x:xs)
    | x > head xs = False
    | otherwise = cinco2 xs

--EJERCICIO 6
--m.xs = <min i : 0 <= i < #xs : xs.i>
seis :: [Int] -> Int
seis [] = error "No hay elementos"
seis [x] = x
seis (x:xs) = min x (seis xs)

seis2 xs = foldr (min) 99999999999999 xs