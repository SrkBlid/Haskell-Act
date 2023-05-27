--EJERCICIO 1: Demostrar que la concatenación de listas es asociativa
(xs ++ ys) ++ zs == xs ++ (ys ++ zs)

--CB xs = []
xs.[]
    [ESPECIFICACIÓN]
([] ++ ys) ++ zs == [] ++ (ys ++ zs)
    [DEF []]
ys ++ zs == ys ++ zs
    [LÓGICA]
True

--CI xs = (x:xs)
--HI = (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
xs.(x:xs)
    [ESPEFICICACIÓN]
(x:xs ++ ys) ++ zs == x:xs ++ (ys ++ zs)
    [DEF CONCATENACIÓN]
x : (xs ++ ys) ++ zs == x : (xs ++ (ys ++ zs))
    [HI]
x : (xs ++ (ys++zs)) == x : (xs ++ (ys ++ zs))
    [LÓGICA]
True

------------------------------------------------------------------------------
--EJERCICIO 2: Demostrar las siguientes propiedades
--map (f o g) xs = (map f) o (map g) xs
--CB xs = []
xs.[]
    [ESPECIFICACIÓN]
map (f o g) [] = (map f) o (map g) []
    [DEF MAP [], DEF COMPOSICIÓN]
[] = map f []
    [DEF MAP []]
[] = []

--CI xs = (x:xs)
--HI = map (f o g) xs = (map f) o (map g) xs
xs.(x:xs)
    [ESPECIFICACIÓN]
map (f o g) (x:xs) = (map f) o (map g) (x:xs)
    [DEF COMPOSICIÓN]
(f o g) x : map (f o g) xs = (map f) ((map g) (x:xs))
    [DEF MAP]
(f o g) x : map (f o g) xs = (map f) (g x : (map g xs))
    [DEF MAP]
(f o g) x : map (f o g) xs = f (g x) : (map f) (map g) xs
    [HI]
f (g x) : map (f o g) xs = f (g x) : map (f o g) xs
    [LÓGICA]
True

--reversa (xs++ys) = reversa ys ++ reversa xs
--CB xs = []
xs.[]
    [ESPECIFICACIÓN]
reversa ([]++ys) = reversa ys ++ reversa []
    [DEF ++ []]
reversa ys = reversa ys ++ reversa []
    [DEF REVERSA []]
reversa ys = reversa ys
    [LÓGICA]

--CI xs = (x:xs)
--HI = reversa (xs++ys) = reversa ys ++ reversa xs
xs.(x:xs)
    [ESPECIFICACIÓN]
reversa (x:xs++ys) = reversa ys ++ reversa (x:xs)
    [DEF CONCATENACIÓN]
reversa x:(xs++ys) = reversa ys ++ reversa (x:xs)
    [DEF REVERSA]
reversa (xs++ys)++[x] = reversa ys ++ reversa xs ++ [x]
    [HI]
reversa ys ++ reversa xs ++ [x] = reversa ys ++ reversa xs ++ [x]
    [LÓGICA]
True

--reversa (reversa xs) = xs
--CB xs = []
xs.[]
    [ESPECIFICACIÓN]
reversa (reversa []) = []
    [DEF REVERSA]
reversa [] = []
    [DEF REVERSA]
[] = []
    [LÓGICA]
True

--CI xs = (x:xs)
--HI = reversa (reversa xs) = xs
xs.(x:xs)
    [ESPECIFICACIÓN]
reversa (reversa (x:xs)) = x:xs
    [DEF REVERSA]
reversa (reversa xs)++[x] = x:xs
    [HI]
xs++[x] = x:xs
    [DEF CONCATENACIÓN]
x:xs = x:xs
    [LÓGICA]
True

------------------------------------------------------------------------------
--EJERCICIO 3
f :: [a] -> Bool
f = <∀i : 0 <= i <= #xs : xs.0 == xs.i>

--CB xs = []
xs.[]
    [ESPECIFICACIÒN]
<∀i : 0 <= i <= #[] : [].0 == [].i>
    [DEF CARDINAL]
<∀i : 0 <= i <= 0 : [].0 == [].i>
    [RANGO VACIO]
True

--CI xs = x:xs
--HI: <∀i : 0 <= i <= #xs : xs.0 = xs.i>
xs.(x:xs)
    [ESPECIFICACIÒN]
<∀i : 0 <= i <= #(x:xs) : (x:xs).0 = (x:xs).i>
    [DEF CARDINAL, DEF POSICIÒN(Index o !!)]
<∀i : 0 <= i <= 1+#xs : x = (x:xs).i>
    [LÒGICA]
<∀i : (0 <= i < 1) v (1 <= i <= 1+#xs) : x = (x:xs).i>
    [PARTICIÒN DE RANGO]
<∀i : 0 <= i < 1 : x = (x:xs).i> ∧ <∀j : 1 <= j < 1+#xs : x = (x:xs).j>
    [RANGO UNITARIO, i <- i+1]
x = (x:xs).0 ∧ <∀i : 1 <= i+1 < 1+#xs : x = (x:xs).i+1>
    [ARTIMETICA, DEF POSICIÒN]
x = (x:xs).0 ∧ <∀i : 0 <= i < #xs : x = xs.i>
    [DEF POSICIÒN]
x = x ∧ <∀i : 0 <= i < #xs : x = xs.i>
    [LÒGICA]
<∀i : 0 <= i < #xs : x = xs.i>


    [MODULARIZACIÒN: g.x.xs]
    
    g.z.xs = <∀i : 0 <= i < #xs : z = xs.i>
    --CB xs = []
    g.z.[]
        [ESPECIFICACIÒN]
    <∀i : 0 <= i <= #[] : z == [].i>
        [DEF CARDINAL]
    <∀i : 0 <= i <= 0 : z == [].i>
        [RANGO VACIO]
    True

    --CI xs = (x:xs)
    --HI : <∀i : 0 <= i < #xs : z = xs.i>
    g.z.(x:xs)
        [ESPECIFICACIÒN]
    <∀i : 0 <= i < #(x:xs) : z = (x:xs).i>
        [PARTICIÒN DE RANGO, DEF CARDINAL]
    <∀i : 0 <= i < 1 : z = (x:xs).i> ∧ <∀j : 1 <= j < #1+xs : z = (x:xs).j>
        [RANGO VACIO, i <- i+1, ARITMETICA, DEF POSICIÒN]
    z = x ∧ <∀i : 0 <= i < #xs : z = xs.i>
        [HI]
    z = x ∧ g.z.xs

    [AHORA DEFINIMOS F CON G]

f.[] = True
f.(x:xs) = x ∧ g.z.xs

------------------------------------------------------------------------------
--EJERCICIO 4
f.xs = <∏i : o <= i < #xs : xs.i>
--CB xs = []
xs.[]
    [ESPECIFICACIÓN]
<∏i : o <= i < #[] : [].i>
    [DEF CARDINAL]
<∏i : o <= i < 0 : [].i>
    [RANGO VACIO]
True

--CI xs = (x:xs)
--HI = <∏i : o <= i < #xs : xs.i> = f.xs
xs.(x:xs)
    [ESPECIFICACIÓN]
<∏i : o <= i < #(x:xs) : (x:xs).i>
    [DEF CARDINAL]
<∏i : o <= i < 1+#xs : (x:xs).i>
    [LÓGICA]
<∏i : (o <= i < 1) v (1 <= i < 1+#xs) : (x:xs).i>
    [PARTICIÓN DE RANGO]
<∏i : (o <= i < 1) : (x:xs).i> ∧ <∏i : (1 <= i < 1+#xs) : (x:xs).i>
    [RANGO UNITARIO]
(x:xs).0 ∧ <∏i : (1 <= i < 1+#xs) : (x:xs).i>
    [i <- i+1]
(x:xs).0 ∧ <∏i : (1 <= i+1 < 1+#xs) : (x:xs).i+1>
    [DEF POSICIÓN]
x ∧ <∏i : (1 <= i+1 < 1+#xs) : xs.i>
    [ARITMETICA (-1 al rango)]
x ∧ <∏i : (0 <= i < #xs) : xs.i>
    [HI]
x ∧ f.xs

--Para cerrar
f.[] = True
f.(x:xs) = x ∧ f.xs

------------------------------------------------------------------------------
--EJERCICIO 5
f.xs = <∀i : 0 <= i < #xs-1 : xs.i <= xs.(i+1)>

--CB xs = []
xs.[]
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #[]-1 : xs.i <= xs.(i+1)>
    [DEF CARDINAL]
<∀i : 0 <= i < -1 : [].i <= [].(i+1)>
    [RANGO VACIO]
True

--CI xs = (x:xs)
--HI = <∀i : 0 <= i < #xs-1 : xs.i <= xs.(i+1)> = f.xs
xs.(x:xs)
    [ESPECIFICACIÓN]
<∀i : 0 <= i < #(x:xs)-1 : (x:xs).i <= (x:xs).(i+1)>
    [DEF CARDINAL]
<∀i : 0 <= i < 1+#xs-1 : (x:xs).i <= (x:xs).(i+1)>
    [LÓGICA]
<∀i : (0 <= i < 1) v (1 <= i < 1+#xs-1) : (x:xs).i <= (x:xs).(i+1)>
    [PARTICIÓN DE RANGO]
<∀i : 0 <= i < 1 : (x:xs).i <= (x:xs).(i+1)> ∧ <∀i : 1 <= i < 1+#xs-1 : (x:xs).i <= (x:xs).(i+1)>
    [RANGO UNITARIO]
(x:xs).0 <= (x:xs).(0+1) ∧ <∀i : 1 <= i < 1+#xs-1 : (x:xs).i <= (x:xs).(i+1)>
    [ARITMETICA (x:xs.1), DEF POSICIÓN]
x <= (x:xs).1 ∧ <∀i : 1 <= i < #xs : (x:xs).i <= (x:xs).(i+1)>
    [DEF POSICIÓN]
x <= xs.0 ∧ <∀i : 1 <= i < #xs : (x:xs).i <= xs.i>
    [i <- i+1]
x <= xs.0 ∧ <∀i : 1 <= i+1 < #xs : (x:xs).(i+1) <= xs.(i+1)>
    [DEF POSICIÓN]
x <= xs.0 ∧ <∀i : 1 <= i+1 < #xs : xs.i <= xs.(i+1)>
    [ARITMETICA (-1 al rango)]
x <= xs.0 ∧ <∀i : 0 <= i < #xs-1 : xs.i <= xs.(i+1)>
    [HI]
x <= xs.0 ∧ f.xs

--PARA CERRAR
f.[] = True
f.(x:xs) = x <= xs.0 ∧ f.xs

------------------------------------------------------------------------------
--EJERCICIO 6: sea m una función que devuelva el minimo de una lista dada.
m :: [Num] -> Num
m.xs = <min i : 0 <= i < #xs : xs.i>

--CB xs = []
xs.[]
    [ESPECIFICACIÓN]
<min i : 0 <= i < #[] : [].i>
    [DEF CARDINAL]
<min i : 0 <= i < 0 : [].i>
    [RANGO VACIO]
0

--CI xs = (x:xs)
--HI = <min i : 0 <= i < #xs : xs.i>
xs.(x:xs)
    [ESPECIFICACIÓN]
<min i : 0 <= i < #(x:xs) : (x:xs).i>
    [DEF CARDINAL]
<min i : 0 <= i < 1+#xs : (x:xs).i>
    [LÓGICA]
<min i : (0 <= i < 1) v (1 <= i < 1+#xs) : (x:xs).i>
    [PARTICIÓN DE RANGO]
<min i : 0 <= i < 1 : (x:xs).i> ∧ <min i : 1 <= i <= 1+#xs : (x:xs).i>
    [RANGO UNITARIO]
(x:xs).0 ∧ <min i : 1 <= i <= 1+#xs : (x:xs).i>
    [DEF POSICIÓN]
x ∧ <min i : 1 <= i <= 1+#xs : (x:xs).i>
    [i <- i+1]
x ∧ <min i : 1 <= i+1 <= 1+#xs : (x:xs).(i+1)>
    [DEF POSICIÓN, ARITMETICA]
x ∧ <min i : 0 <= i <= #xs : xs.i>
    [HI]
x ∧ f.xs

--PARA CERRAR
f.[] = 0
f.(x:xs) = x ∧ f.xs

------------------------------------------------------------------------------
--EJERCICIO 7
f :: [Num] -> Bool
<∃i : 0 <= i < #xs : xs.i = sum xs-(xs.i)>

--CB xs = []
<∃i : 0 <= i < #[] : [].i = sum []-([].i)>
    [DEF CARDINAL]
<∃i : 0 <= i < 0 : [].i = sum []-([].i)>
    [RANGO VACIO]
False

--CI xs = (x:xs)
--HI: <∃i : 0 <= i < #xs : xs.i = sum.xs-(xs.i)>
<∃i : 0 <= i < #(x:xs) : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [DEF CARDINAL]
<∃i : 0 <= i < 1+#xs : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [LÒGICA]
<∃i : (0 <= i < 1) v (1 <= i < 1+#xs) : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [PARTICIÒN DE RANGO]
<∃i : (0 <= i < 1) : (x:xs).i = sum.(x:xs)-(x:xs).i> v <∃i : (1 <= i < 1+#xs) : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [RANGO UNITARIO]
((x:xs).0 = sum.(x:xs)-(x:xs).0) v <∃i : (1 <= i < 1+#xs) : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [DEF POSICIÒN]
x = sum.(x:xs)-x v <∃i : (1 <= i < 1+#xs) : (x:xs).i = sum.(x:xs)-(x:xs).i>
    [i <- j+1]
x = sum.(x:xs)-x v <∃j : (1 <= j+1 < 1+#xs) : (x:xs).j+1 = sum.(x:xs)-(x:xs).j+1>
    [ARITMETICA]
x = sum.(x:xs)-x v <∃j : (0 <= j < #xs) : (x:xs).j+1 = sum.(x:xs)-(x:xs).j+1>
    [DEF POSICIÒN]
x = sum.(x:xs)-x v <∃j : (0 <= j < #xs) : xs.j = sum.(x:xs)-xs.j>

         --LLEGAMOS A UN OBSTACULO IMPASABLE, PASAMOS A GENERALIZAR
        
    g :: Num -> [Num] -> Bool
    <∃i : 0 <= i < #xs : xs.i = z+sum xs-(xs.i)>

    --CB xs = []
    <∃i : 0 <= i < #[] : [].i = z+sum []-([].i)>
        [DEF CARDINAL]
    <∃i : 0 <= i < 0 : [].i = z+sum []-([].i)>
        [RANGO VACIO]
    False
    
    --CI xs = (x:xs)
    --HI: <∃i : 0 <= i < #xs : xs.i = z+sum.xs-(xs.i)>
    <∃i : 0 <= i < #(x:xs) : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
        [DEF CARDINAL]
    <∃i : 0 <= i < 1+#xs : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
        [LÒGICA]
    <∃i : (0 <= i < 1) v (1 <= i < 1+#xs) : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
        [PARTICIÒN DE RANGO]
    <∃i : (0 <= i < 1) : (x:xs).i = z+sum.(x:xs)-(x:xs).i> v <∃i : (1 <= i < 1+#xs) : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
        [RANGO UNITARIO]
    ((x:xs).0 = z+sum.(x:xs)-(x:xs).0) v <∃i : (1 <= i < 1+#xs) : z+(x:xs).i = sum.(x:xs)-(x:xs).i>
        [DEF POSICIÒN]
    x = z+sum.xs-x+x v <∃i : (1 <= i < 1+#xs) : (x:xs).i = z+sum.(x:xs)-(x:xs).i>
        [ARIMETICA, i <- j+1]
    x = z+sum.xs v <∃j : (1 <= j+1 < 1+#xs) : (x:xs).j+1 = z+sum.(x:xs)-(x:xs).j+1>
        [ARITMETICA]
    x = z+sum.xs v <∃j : (0 <= j < #xs) : (x:xs).j+1 = z+sum.(x:xs)-(x:xs).j+1>
        [DEF POSICIÒN]
    x = z+sum.xs v <∃j : (0 <= j < #xs) : xs.j = z+x+sum.xs-(xs.j)>
        [ARITMETICA]
    x = z+sum.xs v <∃j : (0 <= j < #xs) : xs.j = (z+x)+sum.xs-(xs.j)>
        [HI]
    x = z+sum.xs v g.z.xs
    

            [AHORA DEFINIMOS F CON G]
    
    f.[] = False
    f.(x:xs) = (x = 0+sum.xs) v g.0.xs

------------------------------------------------------------------------------
--EJERCICIO 8


------------------------------------------------------------------------------
--EJERCICIO 9

------------------------------------------------------------------------------
--EJERCICIO 10

------------------------------------------------------------------------------
--EJERCICIO 11