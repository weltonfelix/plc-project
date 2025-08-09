type Id = String
type Number = Double
data Term = Var Id
           | Lit Number
           | Sum Term Term
           | Mult Term Term
           | Lam Id Term
           | Apl Term Term
           | Atr Term Term
           | Seq Term Term
           | While Term Term
           | MethodCall Term Id Term
           | If Term Term Term
           | New Id
           | InstanceOf Term Id
           | For Id Term Term Term
           | This
           | AField Term Id


data Definition = Def Id Term
data Method  = Method Id Term -- Term --> Lambda
data Decl = ClassDecl Id [Id] [Method]
           | FunDecl  Id Term

data Value = Num Double
            | Ref Int  -- referencia pra um obj
            | Fun (Value -> State -> Heap -> (Value, State, Heap))
            | Error

type Program = [Definition]
type Environment = [(Id, Value)]
type State = [(Id, Value)]
type Object = (Id, State) -- classe, estado
type Heap = [(Value, Object)] -- endereço, objeto


------------- interpretador -------------------------

int :: Environment -> State -> Heap -> Term -> (Value, State, Heap)  --tem que alterar a heap tb
int e s h (Var id)     = (search id s, s, h)
int e s h (Lit num)    = (Num num,     s, h)

int e s h (Sum  t1 t2) = (somaVal n1 n2, s2, h2)
                        where (n1, s1, h1) = int e s h t1
                              (n2, s2, h2) = int e s1 h1 t2

int e s h (Mult t1 t2) = (multVal n1 n2, s2, h2)
                        where (n1, s1, h1) = int e s h t1
                              (n2, s2, h2) = int e s1 h1 t2

int e s h (AField t1 id)    = (search id os, s1, h1)  --retorno o valor do campo do objeto na heap
                            where (_, os)     = getObj rf h1
                                  (rf, s1, h1) = int e s h t1

int e s h (Atr (Var id) t2) = (v, wr (id, v) s1, h1)
                            where (v, s1, h1) = int e s h t2
int e s h (Atr (AField t1 id) t2) = (v, s2, wrh  rf (id, v) h2)
                            where (rf, s2, h2) = int e s1 h1 t1
                                  (v, s1, h1) = int e s  h  t2

int e s h (Lam x t) = (Fun (\v s h -> int ((x,v):e) s h t), s, h)

int e s h (Apl t u) = app v1 v2 e2 h2
                    where (v1,e1, h1) = int e s h t
                          (v2,e2, h2) = int e1 s h1 u


int e s h (If t_cond t_then t_else) =
    case v_cond of
        Num n -> if n /= 0
             then int e s1 h1 t_then
             else int e s1 h1 t_else
        _     -> (Error, s1, h1)
    where
        (v_cond, s1, h1) = int e s h t_cond


int e s h (InstanceOf t_expr class_id) =
    let
        (val, s1, h1) = int e s h t_expr
    in
        case val of
        Ref ref_addr ->
            let
            (obj_class, _) = getObj (Ref ref_addr) h1
            in
            if obj_class == class_id && obj_class /= ""
            then (Num 1, s1, h1)
            else (Num 0, s1, h1)
        _ -> (Num 0, s1, h1)

--        | Lam Id Term
    --    | Apl Term Term
    --    | Seq Term Term
    --    | While Term Term
    --    | MethodCall Term Id Term
    --    | If Term Term Term
    --    | New Id
    --    | InstanceOf Term Id
    --    | For Id Term Term Term
    --    | This


--------- funções auxiliares ---------------

search :: Id -> State -> Value
search i [] = Error
search i ((j,v):l) = if i == j then v else search i l

getObj :: Value -> Heap -> Object
getObj (Ref i) [] = ("", [])  --error
getObj (Ref i) ((Ref j, v):l) = if i == j then v else getObj (Ref i) l
getObj (Ref i) ((_,v):l) = getObj (Ref i) l  -- caso o Value não seja Ref
getObj _ _ = ("", [])


somaVal :: Value -> Value -> Value
somaVal (Num x) (Num y) = Num (x+y)
somaVal _ _ = Error

multVal :: Value -> Value -> Value
multVal (Num x) (Num y) = Num (x*y)
multVal _ _ = Error

app :: Value -> Value -> State -> Heap -> (Value, State, Heap)
app (Fun f) v e h = f v e h
app _ _ e h = (Error, e, h)

wr :: (Id, Value) -> State -> State
wr (i,v) [] = [(i,v)]
wr (i,v) ((j,u):l) = if (i == j) then (j,v):l else [(j,u)] ++ (wr (i,v) l)

wrh :: Value -> (Id, Value) -> Heap -> Heap --write heap -> procura o objeto com a ref e dá wr no estado dele
wrh (Ref i) v [] = [] -- se não achar a ref, não faz nada?
wrh (Ref i) v ((Ref j, (c, s)):l) | i == j     = (Ref j, (c, wr v s)) : l 
                                  | otherwise  = (Ref j, (c, s)) : (wrh (Ref i) v l)
wrh ref v (h:hs) = h : (wrh ref v hs)  -- caso o Value não seja Ref

---------- instancias de show ---------------
instance Show Value where
    show (Num x) = show x
    show (Ref i) = "Ref(" ++ show i ++ ")"
    show (Fun _) = "<function>"
    show Error = "Error"

instance Show Term where
    show (Var id) = id
    show (Lit num) = show num
    show (Sum x y) = "(" ++ (show x) ++ " + " ++ (show y) ++ ")"
    show (Mult x y) = "(" ++ (show x) ++ " * " ++ (show y) ++ ")"
    show (Lam x y) = "( Lambda " ++ x ++ ": " ++ (show y) ++ ")"
    show (Apl t1 t2)  = (show t1) ++ "(" ++ (show t2) ++ ")"
    show (Atr t1 t2)  = (show t1) ++ " = " ++ (show t2)
    show (Seq t1 t2)  = (show t1) ++ ";\n" ++ (show t2)
    show (While t1 t2) = "while( " ++ (show t1) ++ "){\n" ++ (show t2) ++ "}\n";
    show (MethodCall t1 id t2) = "call(" ++ (show t1) ++ ", " ++ id ++ ", " ++ (show t2) ++ ")"
    show (If t1 t2 t3) = "if( " ++ (show t1) ++ " ){\n" ++ (show t2) ++ "\n} else {\n" ++ (show t3) ++ "\n}\n";
    show (New id) = "new " ++ id
    show (InstanceOf t id) = "InstanceOf(" ++ (show t) ++ ", " ++ id ++ ")"
    show (For id t1 t2 t3) = "for " ++ id ++ " in range(" ++ (show t1) ++ ", " ++ (show t2) ++ "){\n" ++ (show t3) ++ "}\n"
    show (This) = "this"
    show (AField t id) = (show t) ++ "." ++ id

instance Show Definition where
    show (Def id termo)  = "def " ++ (id) ++ " = " ++ (show termo)

ifexemplo = If (Sum (Var "x") (Lit 2)) (Atr (Var "y") (Lit 5)) (Atr (Var "y") (Lit 3))
forexemplo = For "i" (Lit 0) (Sum (Var "X") (Lit 5)) ifexemplo

------------------------ --------------------------
-- Tests

testSearch = do
    print $ "expected 5, got: " ++ show (search "x" [("x", Num 5)])
    print $ "expected Ref(10), got: " ++ show (search "x" [("x", Ref 10)])
    print $ "expected <function>, got: " ++ show (search "x" [("x", Fun (\v s h -> (Num 42, s, h)))])
    print $ "expected Error, got: " ++ show (search "y" [("x", Num 5)])

testGetObj = do
    print $ "expected ('A', [('x', Num 5)]), got: " ++ show (getObj (Ref 10) [(Ref 10, ("A", [("x", Num 5)]))])
    print $ "expected ('B', [('y', Num 7)]), got: " ++ show (getObj (Ref 20) [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))])
    print $ "expected ('', []), got: " ++ show (getObj (Ref 30) [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))])
    print $ "expected ('', []), got: " ++ show (getObj (Num 5) [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))])

testSomaVal = do
    print $ "expected Num 8, got: " ++ show (somaVal (Num 5) (Num 3))
    print $ "expected Error, got: " ++ show (somaVal (Num 5) (Ref 10))
    print $ "expected Error, got: " ++ show (somaVal (Ref 10) (Num 3))
    print $ "expected Error, got: " ++ show (somaVal (Ref 10) (Ref 20))

testMultVal = do
    print $ "expected Num 15, got: " ++ show (multVal (Num 5) (Num 3))
    print $ "expected Error, got: " ++ show (multVal (Num 5) (Ref 10))
    print $ "expected Error, got: " ++ show (multVal (Ref 10) (Num 3))
    print $ "expected Error, got: " ++ show (multVal (Ref 10) (Ref 20))

testApp = do
    print $ "expected (Num 42, ..., ...), got: " ++ show (app (Fun (\v s h -> (Num 42, s, h))) (Num 5) [] [])
    print $ "expected (Error, ..., ...), got: " ++ show (app (Fun (\v s h -> (Num 42, s, h))) (Ref 10) [] [])
    print $ "expected (Error, ..., ...), got: " ++ show (app (Ref 10) (Num 5) [] [])
    print $ "expected (Num 12, [('x', Num 5)], [(Ref 1, ('A', [('a', Num 12)])])), got: " ++ show (
            app (
                    Fun (\v s h -> (
                            Num 12,
                            ("x", Num 5) : s,
                            (Ref 1, ("A", [("a", Num 12)])) : h
                            )
                        )
                ) (Num 5) [] []
        )

testWr = do
    print $ "expected [('x', Num 5)], got: " ++ show (wr ("x", Num 5) [])
    print $ "expected [('x', Num 5), ('y', Num 10)], got: " ++ show (wr ("y", Num 10) [("x", Num 5)])
    print $ "expected [('x', Num 5), ('y', Num 10)], got: " ++ show (wr ("x", Num 5) [("x", Num 3), ("y", Num 10)])
    print $ "expected [('x', Fun _)], got: " ++ show (wr ("x", Fun (\v s h -> (Num 42, s, h))) [])

testWrh = do
    let h = [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))]
    print $ "expected [(Ref 10, ('A', [('x', Num 5)]))], got: " ++ show (wrh (Ref 10) ("x", Num 5) h)
    print $ "expected [(Ref 20, ('B', [('y', Num 10)]))], got: " ++ show (wrh (Ref 20) ("y", Num 10) h)
    print $ "expected [(Ref 10, ('A', [('x', Num 5)])), (Ref 20, ('B', [('y', Num 7)]))], got: " ++ show (wrh (Ref 30) ("z", Num 8) h)