--1
--no (a y b)
nand :: Bool -> Bool -> Bool
nand True True = False
nand False True = True
nand True False = True
nand False False = True

--2
maj :: Bool -> Bool -> Bool -> Bool
maj True _ True = True
maj True True _ = True
maj _ True True = True
maj True _ _ = False
maj _ True _ = False
maj _ _ True = False

maj2 :: Bool -> Bool -> Bool -> Bool
maj2 n m l
    | n && m = True
    | n && l = True
    | m && l = True
    | otherwise = False

--3
--paraTodo [0,1,2,3] [4,1,2,6] even = False
--paraTodo :: Rango -> Elementos -> Termino -> Resultado
paraTodo :: [Int] -> [a] -> (Int -> [a] -> Bool) -> Bool
paraTodo [] ys f = False
paraTodo xs ys f = and [f x ys | x <- xs]

even2 :: (Integral a) => Int -> [a] -> Bool
even2 _ [] = False
even2 n xs
    | n > length xs-1 = error "La posición es más grande que la lista"
    | n < 0 = error "La posición es negativa"
    | otherwise = mod (elemento n xs 0) 2 == 0
    where 
        elemento n (x:xs) i
            | n /= i = elemento n xs (i+1)
            | otherwise = x 

existe :: [Int] -> [a] -> (Int -> [a] -> Bool) -> Bool
existe [] ys f = False
existe xs ys f = or [f x ys | x <- xs]

odd2 :: (Integral a) => Int -> [a] -> Bool
odd2 _ [] = False
odd2 n xs
    | n > length xs-1 = error "La posición es más grande que la lista"
    | n < 0 = error "La posición es negativa"
    | otherwise = mod (elemento n xs 0) 2 /= 0
    where 
        elemento n (x:xs) i
            | n /= i = elemento n xs (i+1)
            | otherwise = x 

--4
