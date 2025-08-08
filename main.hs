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

int e s h (Sum  t1 t2) = (somaVal n1 n2, s, h)
                        where (n1, _, _) = int e s h t1
                              (n2, _, _) = int e s h t2

int e s h (Mult t1 t2) = (multVal n1 n2, s, h)
                        where (n1, _, _) = int e s h t1
                              (n2, _, _) = int e s h t2

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