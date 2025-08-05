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


data Method = Method Id Term -- Term --> Lambda

data Decl= ClassDecl Id [Id] [Method]
           | FunDecl Id Term

data Definition = Def Id Term

type Program = [Definition]


data Value = Num Double
            | Ref Int  -- referencia pra um obj
            | Fun (Value -> State -> (Value, State))
            | Error

type State = [(Id, Value)]
type Environment = [(Id, Value)]
type Object = (Id, State) -- classe, estado
type Heap = [(Ref, Object)] -- endereço, objeto

-- heap -> conjunto de pares endereco objeto -> tem que ter um id classe e estado


------------- interpretador -------------------------

search :: Id -> State -> Value
search i [] = Error
search i ((j,v):l) = if i == j then v else search i l

somaVal :: x -> y -> State -> Num
somaVal (Number x) (Number y) _ = Number (x+y)
somaVal (Var x) (Var y) s = somaVal (search x s) (search y s)
somaVal _ _ _ = Error

multVal :: x -> y -> State -> Num
multVal (Number x) (Number y) _ = Number (x*y)
multVal (Var x) (Var y) s = multVal (search x s) (search y s)
multVal _ _ _ = Error

app :: Value -> Value -> State -> (Value, State)
app (Fun f) v e = f v e
app _ _ e = (Error, e)

wr :: Eq a => (a, t) -> [(a, t)] -> [(a, t)]
wr (i,v) [] = [(i,v)]
wr (Var i,v) ((j,u):l) = if (i == j) then (j,v):l else [(j,u)] ++ (wr (i,v) l)
(This,v) ((j,u):l) = if (This == j) then (j,v):l else [(j,u)] ++ (wr (This,v) l)


int :: Environment -> State -> Heap -> Term -> (Value, State)
int e s h (Var id)     = (search id s, s)
int e s h (Lit num)    = (Num num, s)

int e s h (Sum  t1 t2) = (somaVal n1 (int t2), s) where (n1, s) = int t1
int e s h (Mult t1 t2) = (multVal (int t1) (int t2), s)

int e s h (Atr (Var id) t2) = wr id v ns h
                            where (v, ns) = int e ns h t2 -- valor e novo estado
int e s h (Atr (Afield This id) t2) = wr This v ns h
                            where (v, ns) = int e ns h t2 -- valor e novo estado
int e s h (Atr (Afield (Var idobj) id) t2) = wr (avaliar o id dentro do idobj) v ns h
                            where (v, ns) = int e ns h t2 -- valor e novo estado
int e s h (Atr t1 t2) =  -- atribui valor de t2 a t1

-- int e s h (If cond ifTrue ifFalse) = 

-- Term = Var Id
--            | Lam Id Term
--            | Apl Term Term
--            | Seq Term Term
--            | While Term Term
--            | MethodCall Term Id Term
--            | If Term Term Term
--            | New Id
--            | InstanceOf Term Id
--            | For Id Term Term Term
--            | This
--            | AField Term Id



---------- instancias de show ---------------
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

instance Show Definition where
    show (Def id termo)  = "def " ++ (id) ++ " = " ++ (show termo)

ifexemplo = If (Sum (Var "x") (Lit 2)) (Atr (Var "y") (Lit 5)) (Atr (Var "y") (Lit 3))
forexemplo = For "i" (Lit 0) (Sum (Var "X") (Lit 5)) ifexemplo

------------------------ --------------------------