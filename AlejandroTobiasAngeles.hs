
-- Alejandro Tobias Angeles

-- Parte 1

-- ////////////////////////////////////////////////////////////////

-- Tipo de datos Prop con los simbolos de Σ
data Prop = P | Q | R | S deriving (Eq, Show, Read)

-- Tipo de datos Formula con sus valores admitidos
data Formula = At Prop | Neg Formula | Con Formula Formula | Dis Formula Formula  deriving(Read, Eq)

-- Instanciacion como Show
instance Show Formula where 
    show (At p) = show p
    show (Neg p) = "¬" ++ show p
    show (Con for1 for2) = "(" ++ show for1 ++ " ^ " ++ show for2 ++ ")"
    show (Dis for1 for2) = "(" ++ show for1 ++ " v " ++ show for2 ++ ")"

-- Funcion que evalua una formula para saber si es una clausula. Lo sera cuando:
esClausula :: Formula -> Bool
esClausula (At p) = True -- sea un atomo 
esClausula (Neg (At p)) = True -- sea la negacion de un atomo
esClausula (Dis p1 p2) = esClausula p1 && esClausula p2 -- sea la disyuncion sin conjunciones
esClausula _ = False

-- Ejemplos clausulas :
-- P v Q -> (Dis (At P) (At Q))
-- ¬P v Q -> (Dis (Neg (At P)) (At Q))
-- ¬P v ¬Q -> (Dis (Neg (At P)) (Neg (At Q)))


-- Los literales son atomos o negaciones de atomos
esLiteral :: Formula -> Bool
esLiteral (At p) = True 
esLiteral (Neg (At p)) = True
esLiteral _ = False
-- Hice esta funcion al principio porque la usaba para el esClausula, pero al final no la he utilizado.

-- Funcion que dada una formula en FNC devuelve una lista con las clausulas que la componen
fncAlista :: Formula -> [Formula]
fncAlista (At p) = [At p]
fncAlista (Neg (At p)) = [Neg (At p)]
fncAlista (Dis p1 p2) = [Dis p1 p2]
fncAlista (Con p1 p2) = fncAlista p1 ++ fncAlista p2
fncAlista _ = []

-- Ejemplos de formulas en FNC pasadas a lista
-- (P v Q) ^ (¬P v R) -> Con (Dis (At P) (At Q), Dis (Neg (At P)) (At R)) -> [(P v Q),(¬P v R)]
-- (P v Q) ^ (¬P v R) ^ (¬Q v S) -> ( Con (Con (Dis (At P) (At Q)) (Dis (Neg (At P)) (At R))) (Dis (Neg(At Q)) (At S))) -> [(P v Q),(¬P v R),(¬Q v S)]


-- Funcion que dada una clausula devuelve una lista con los literales que la componen
clausulaLista:: Formula -> [Formula]
clausulaLista (At p) = [At p]
clausulaLista (Neg (At p)) = [Neg (At p)]
clausulaLista (Dis f1 f2) = clausulaLista f1 ++ clausulaLista f2
clausulaLista _ = []

-- Ejemplos de clausulas pasadas a lista
-- P v Q -> (Dis (At P) (At Q)) -> [P,Q]
-- ¬P v Q -> (Dis (Neg (At P)) (At Q)) -> [¬P,Q]
-- ¬P v ¬Q -> (Dis (Neg (At P)) (Neg (At Q))) -> [¬P,¬Q]


-- Funcion que dada una clausula comprueba si es clausula de Horn o no
-- En este caso se cuenta el numero de literales positivos, si es mayor que 1 no es clausula de Horn
esClausulaHorn :: Formula -> Bool
esClausulaHorn (At p) = True
esClausulaHorn (Neg (At p)) = True
esClausulaHorn (Dis p1 p2) 
    | contarPositivos2 (Dis p1 p2) >= 2 = False
    | otherwise = True

-- Ejemplos de clausulas de Horn
-- P v (¬Q) -> (Dis (At P) (Neg(At Q))) -> True
-- (¬P) v (¬Q) -> (Dis (Neg (At P)) (Neg (At Q))) -> True

-- Una posibilidad de contar los literales positivos de la clausula es esta
contarPositivos1 :: Formula -> Int
contarPositivos1 (At p) = 1
contarPositivos1 (Neg (At p)) = 0
contarPositivos1 (Dis p1 p2) = contarPositivos1 p1 + contarPositivos1 p2
contarPositivos1 _ = 0

-- Otra posibilidad para usar funciones de orden superior es un fold, pero hara falta una
-- funcion auxiliar que reciba un literal y devuelva 1 en caso de ser un atomo
-- o 0 en caso de ser una negacion

contarPositivos2 :: Formula -> Int
contarPositivos2 f = foldl(\x y -> x + pos y) 0 (clausulaLista f)

-- Esta funcion "traduce a valores" si el literal esta negado o no
pos :: Formula -> Int
pos (At p) = 1
pos (Neg (At p)) = 0


resolvente :: [Formula] -> [Formula] -> [Formula]
resolvente [] [] = []
resolvente [] ys = ys
resolvente xs [] = xs
resolvente xs ys =    -- Lo primero que hacemos es eliminar los posibles literales repetidos
    let x = eliminarRepetidos xs in
    let y = eliminarRepetidos ys in  -- Despues llamamos a la funcion resolventeAux, definida mas abajo
    eliminarRepetidos (resolventeAux x y ++ resolventeAux y x)

-- Ejemplo de clausulas con sus resolventes

-- (P v Q) , (¬P v R) -> [(At P) ,(At Q)] [(Neg (At P)), (At R)] -> [Q,R]

    
-- Funcion que elimina los elementos repetidos de una lista con funcion de primer orden
eliminarRepetidos :: [Formula] -> [Formula]
eliminarRepetidos [] = []
eliminarRepetidos xs = foldl (\x y -> if y `elem` x then x else x ++ [y]) [] xs
    
-- Funcion que dadas dos listas de literales devuelve los literales de la primera lista que no 
-- tienen su opuesto en la segunda
resolventeAux :: [Formula] -> [Formula] -> [Formula]
resolventeAux xs ys = foldl (\x y -> if negacion y `elem` ys then x else x ++ [y]) [] xs
 
-- Funcion que devuelve el opuesto del literal proporcionado
negacion :: Formula -> Formula
negacion (At p) = Neg (At p)
negacion (Neg (At p)) = At p
negacion _ = error "No es un literal"

-- ////////////////////////////////////////////////////////////////////

-- Parte 2

-- ////////////////////////////////////////////////////////////////////

resolucion :: [[Formula]] -> [Formula] -> [Formula]
-- Primero para buscar la primera clausula que resuelva G, podemos
-- usar un dropWhile que vaya eliminando las que no lo resuelven,
-- despues calculamos la resolvente y volvemos a llamar a la funcion con 
-- la nueva G
resolucion xs x = resolucionAux xs x []

-- Lo que hacemos es comprobar si alguna clausula puede resolverse con el G dado
-- esto lo hacemos con un dropWhile que va descartando los que no resuelven
-- despues calculamos la resolvente y volvemos a llamar a la funcion con la nueva G
-- Un punto importante es que debemos tener una lista con las G que vamos obteniendo
-- si no la tuvieramos podriamos entrar en bucles infinitos al volver a obtener G que ya
-- habiamos obtenido
resolucionAux :: [[Formula]] -> [Formula] -> [[Formula]] -> [Formula]
resolucionAux xs x listaG = 
    let clauSol = dropWhile (\y -> not (resuelve y x)) xs in 
        if clauSol == [] then x
        else let resol = resolvente (head clauSol) x in
            if resol == [] then resol
            else if resol `elem` listaG then x
            else resolucionAux xs resol (resol:listaG)


-- Esta funcion nos ayuda a saber si una clausula resuelve antes de hacerlo
resuelve :: [Formula] -> [Formula] -> Bool
resuelve c g = any (\x -> negacion x `elem` g) c

-- Ejemplos resolucion

-- [[(At P), (Neg(At Q))], [(At R)]] [(Neg(At P))] -> [¬Q]
-- [[(At P), (Neg(At Q))], [(At R)]] [(Neg(At P)), (At Q)] -> []

-- ////////////////////////////////////////////////////////////////////

-- Parte 3

-- ////////////////////////////////////////////////////////////////////


-- Menu que permite al usuario ejecutar las funciones anteriormente definidas
menu :: IO()
menu = do 
    putStrLn "1 - Comprobar si la formula introducida es una clausula"
    putStrLn "2 - Pasar una formula en FNC a lista con las clausulas que la forman"
    putStrLn "3 - Pasar una clausula a lista con los literales que la forman"
    putStrLn "4 - Comprobar si una clausula es de Horn"
    putStrLn "5 - Calcular el resolvente de 2 clausulas"
    putStrLn "6 - Calcular la resolucion de una clausula de Horn con una lista de clausulas"
    putStrLn "0 - Salir"

    putStr "Introduzca la accion que deseas probar: "
    accion <- getLine
    case accion of
        "1" -> do
            putStr "Introduzca la formula: "
            formula <- getLine
            putStr "Resultado: "
            print(esClausula (read formula))
            menu
        "2" -> do
            putStr "Introduzca la formula: "
            formula <- getLine
            putStr "Resultado: "
            print(fncAlista (read formula))
            menu
        "3" -> do
            putStr "Introduzca la clausula: "
            clausula <- getLine
            putStr "Resultado: "
            print(clausulaLista (read clausula))
            menu
        "4" -> do
            putStr "Introduzca la clausula: "
            clausula <- getLine
            putStr "Resultado: "
            print(esClausulaHorn (read clausula))
            menu
        "5" -> do
            putStr "Introduzca la primera clausula: "
            clausula1 <- getLine
            putStr "Introduzca la segunda clausula: "
            clausula2 <- getLine
            putStr "Resultado: "
            print(resolvente (read clausula1) (read clausula2))
            menu
        "6" -> do
            putStr "Introduzca la lista de clausulas de Horn: "
            clausulas <- getLine
            putStr "Introduzca la clausula de Horn a resolver: "
            clausula <- getLine
            putStr "Resultado: "
            print(resolucion (read clausulas) (read clausula))
            menu
        "0" -> putStrLn "Programa terminado"
        _ -> do
            putStrLn "Opcion no valida"
            menu            
            
    
-- ////////////////////////////////////////////////////////////////////
