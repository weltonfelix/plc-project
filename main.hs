{-|
PLC Interpreter (OO-flavored) — overview and organization

This file implements a small interpreter with:
    - AST (Term): variables, numeric literals, sum/multiplication, lambda/application,
        assignment, sequencing, while, if, field read/write, object creation (new), and instanceof.
    - Runtime model: immutable Environment, mutable State, and a Heap of objects.
    - Closures (Fun) that capture the Environment and operate over (Value, State, Heap).

Conventions:
    - Truthiness: any (Num n) with n ≠ 0 is true; (Num 0) is false.
    - Type/operator errors yield Error.
    - Evaluation is strict and left-to-right, threading State and Heap.

Tip: use the 'main' function at the bottom to run quick smoke tests in GHCi.

Call 'runExample' to execute a sample program.
or 'runInBaseEnv programWhile' to run the while example
or 'runInBaseEnv _term_' to run a term in the base environment.
-}

import Data.List (sortBy)
import Data.Ord (comparing)

----------------------------
-- Basic types and AST   --
----------------------------
type Id = String -- Identifiers are Haskell strings
type Number = Double -- Numeric literals are represented as Doubles

-- | Term represents the language constructs (AST)
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
           | TermVal Value -- for method calls parameters
           | EmptyTerm -- do nothing 


data Definition = Def Id Term
data Method  = Method Id Term -- Term --> Lambda
data Decl = ClassDecl Id [Id] [Method]
           | FunDecl  Id Term

-- | Runtime values
data Value = Num Double
            | Ref Int  -- referencia pra um obj
            | Fun (Value -> State -> Heap -> (Value, State, Heap))
            | Error String 
            | ClassDef [Id] [Method]
            | Void

type Program = [Definition]

-- | Environment: immutable variables (closures, global refs, etc.)
type Environment = [(Id, Value)]
-- | State: mutable variables
type State = [(Id, Value)]

-- | Object: pair (class name, fields state)
type Object = (Id, State)
-- | Heap: maps reference (Ref n) to object
type Heap = [(Value, Object)]

--------------- Declarations -------------------
intDecl :: [Decl] -> Environment
intDecl [] = []
intDecl ((ClassDecl id fields methods):ls) = (id, ClassDef fields methods) : intDecl ls
intDecl ((FunDecl id term):ls) = (id, Fun (\v s h -> int [] s h (Apl term (TermVal v)))) : intDecl ls


-------------- Interpreter --------------------------
-- | int: interpret a Term under (Environment, State, Heap).
--   Returns (Value, State, Heap) after evaluation.
int :: Environment -> State -> Heap -> Term -> (Value, State, Heap)  -- may update heap too

-- Variable and Literal evaluation
int e s h (Var id)     = (search id (s ++ e), s, h) -- Returns the variable value, searching in State and Environment
int e s h (Lit num)    = (Num num,     s, h) -- Returns the literal value

-- Numeric binary operations
int e s h (Sum  t1 t2) = (sumVal n1 n2, s2, h2)
                        where (n1, s1, h1) = int e s h t1
                              (n2, s2, h2) = int e s1 h1 t2

int e s h (Mult t1 t2) = (multVal n1 n2, s2, h2)
                        where (n1, s1, h1) = int e s h t1
                              (n2, s2, h2) = int e s1 h1 t2

-- Field read: returns the field value from the heap object
int e s h (AField t1 id)    = (search id os, s1, h1)
                            where (_, os)     = getObj rf h1
                                  (rf, s1, h1) = int e s h t1

-- Assignment (variable and field)
-- | Updates the state and heap with the new value
int e s h (Atr (Var id) rhs) = (v, wr (id, v) s1, h1)
                            where (v, s1, h1) = int e s h rhs
int e s h (Atr (AField t1 id) rhs) = (v, s2, wrh  rf (id, v) h2)
                            where
                                (v, s1, h1) = int e s  h  rhs
                                (rf, s2, h2) = int e s1 h1 t1

-- Lambda Function
-- | Creates a closure with the current environment
int e s h (Lam x t) = (Fun (\v s h -> int ((x,v):e) s h t), s, h)

-- Sequencing (t; u)
-- | Evaluates t, then u, threading the updated state and heap
int e s h (Seq t u) = int e s1 h1 u
                    where (_, s1, h1) = int e s h t

-- Function application
-- | Applies a function to an argument, threading the state and heap
-- | First, evaluates the function and argument
int e s h (Apl f v) = app f1 v1 s2 h2
                    where (f1,s1, h1) = int e s h f
                          (v1,s2, h2) = int e s1 h1 v


-- If/Else
-- | Evaluates the condition and branches accordingly
int e s h (If t_cond t_then t_else) =
    case v_cond of
        Num n -> if n /= 0
             then int e s1 h1 t_then
             else int e s1 h1 t_else
        _     -> (Error "Condition must be numeric", s1, h1)
    where
        (v_cond, s1, h1) = int e s h t_cond

-- While (re-evaluates the condition on each iteration)
int e s h (While cond body) = let (cond_res, s1, h1) = int e s h cond in
    case cond_res of
        Num n | n /= 0 -> 
                let (_, s2, h2) = int e s1 h1 body in
                    int e s2 h2 (While cond body) 
        Num _ -> (Num 0, s1, h1)
        _ -> (Error "While condition must be numeric", s1, h1)

-- Instanceof and new
-- | Checks if the expression is an instance of a class
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

-- For loop: for id in range(start, end) { body }
int e s h (For id start end body) = 
    let (start_val, s1, h1) = int e s h start
        (end_val, s2, h2) = int e s1 h1 end
    in case (start_val, end_val) of
        (Num start_n, Num end_n) -> 
            forLoop id (round start_n) (round end_n) body e s2 h2
        _ -> (Error "For loop bounds must be numeric", s2, h2)
  where
    forLoop :: Id -> Int -> Int -> Term -> Environment -> State -> Heap -> (Value, State, Heap)
    forLoop id start end body e s h
        | start >= end = (Num 0, s, h)
        | otherwise = 
            let (_, s1, h1) = int ((id, Num (fromIntegral start)):e) s h body
            in forLoop id (start + 1) end body e s1 h1

-- | Creates a new object in the heap
int e s h (New class_id) =
    let
        new_ref = length h + 1
        (ClassDef atributes  _)  = search class_id e
        new_obj = (class_id, idToEmptyState atributes) -- create new object with empty state
    in
    (Ref new_ref, s, h ++ [(Ref new_ref, new_obj)])

--  MethodCall Term Id Term
int e s h (MethodCall t1 id t2) = (retVal, s2, h3)
                                where   (obj, s1, h1) = int e s h t1  -- get object reference from variable
                                --- get method and object state
                                        (class_obj, state_obj1) = getObj obj h1
                                        (ClassDef _ methods)    = search class_obj e
                                        (method)                = searchMethod id methods  
                                --- get value of t2 (the parameter)
                                        (v, s2, h2) = int e s1 h1 t2
                                --- create environment with 'this' pointing to current object
                                        method_env = ("this", obj) : e
                                --- apply the method to the object state and parameter with 'this' in environment
                                        (retVal, _, h3) = int method_env state_obj1 h2 (Apl method (TermVal v))

-- This: returns the current object reference
int e s h This = (search "this" e, s, h)

int e s h (TermVal v) = (v, s, h) -- unwrap TermVal to Value
int e s h t = (Error ("Unknown term " ++ (show t)) , s, h) -- Fallback for unrecognized terms

---------- Helper Functions ----------------

type SearchContext = [(Id, Value)] -- Context for searching in State/Env

-- | Lookup an identifier in an association list (State/Env)
search :: Id -> SearchContext -> Value
search i [] = Error ("Var not found " ++ i)
search i ((j,v):l) = if i == j then v else search i l

searchMethod :: Id -> [Method] -> Term
searchMethod _ [] = EmptyTerm 
searchMethod i ((Method j t):l) | i == j    = t
                                | otherwise = searchMethod i l

-- | Retrieve object from Heap for a given Value (expects Ref n)
getObj :: Value -> Heap -> Object
getObj (Ref i) [] = ("", [])  --error
getObj (Ref i) ((Ref j, v):l) = if i == j then v else getObj (Ref i) l
getObj (Ref i) ((_,v):l) = getObj (Ref i) l  -- caso o Value não seja Ref
getObj _ _ = ("", [])


-- | Numeric operations
sumVal :: Value -> Value -> Value
sumVal (Error m) _ = Error m
sumVal _ (Error m) = Error m
sumVal (Num x) (Num y) = Num (x+y)
sumVal _ _ = Error "Cannot add non-numeric values"

multVal :: Value -> Value -> Value
multVal (Error m) _ = Error m
multVal _ (Error m) = Error m
multVal (Num x) (Num y) = Num (x*y)
multVal _ _ = Error "Cannot multiply non-numeric values"

-- | Apply a function-value to an argument, threading State/Heap
app :: Value -> Value -> State -> Heap -> (Value, State, Heap)
app (Fun f) (Num v) e h = f (Num v) e h
app (Fun f) _ e h = (Error "Cannot apply non-numeric argument", e, h)
app _ _ e h = (Error "Cannot apply non-function", e, h)

-- | Write/update a pair (Id,Value) in the State
wr :: (Id, Value) -> State -> State
wr (i,v) [] = [(i,v)]
wr (i,v) ((j,u):l) = if (i == j) then (j,v):l else [(j,u)] ++ (wr (i,v) l)

-- | Write a field in an object referenced in the Heap
wrh :: Value -> (Id, Value) -> Heap -> Heap -- find object by ref and write into its field state
wrh (Ref i) v [] = [] -- if ref is not found, do nothing
wrh (Ref i) v ((Ref j, (c, s)):l) | i == j     = (Ref j, (c, wr v s)) : l 
                                  | otherwise  = (Ref j, (c, s)) : (wrh (Ref i) v l)
wrh _ _ h = h  -- caso o Value não seja Ref, do nothing

-- | Write/update a object in the Heap
wrho :: Value -> Object -> Heap -> Heap -- 
wrho (Ref i) obj [] = [(Ref i, obj)] -- if ref is not found, add it
wrho (Ref i) obj ((Ref j, _):l) | i == j     = (Ref j, obj) : l 
                               | otherwise  = (Ref j, obj) : (wrho (Ref i) obj l)
wrho _ _ h = h  -- caso o Value não seja Ref, do nothing

idToEmptyState :: [Id] -> State
idToEmptyState [] = []
idToEmptyState (id:ls) = (id, Num 0) : idToEmptyState ls

---------- Equality ----------
instance Eq Value where
    (Num a) == (Num b) = a == b
    (Ref a) == (Ref b) = a == b
    Fun _   == Fun _   = True   -- functions are not comparable; treat as equal for tests
    (Error m1)   == (Error m2)   = m1 == m2
    _       == _       = False

---------- Show Instances ---------------
instance Show Value where
    show (Num x) = show x
    show (Ref i) = "Ref($" ++ show i ++ ")"
    show (Fun _) = "<function>"
    show (Error message) = "Unhandled error: " ++ message
    show (ClassDef fields methods) = "Class(" ++ show fields ++ ", " ++ show methods ++ ")"
    show (Void) = "Void"

printTab :: Int -> String
printTab 0 = ""
printTab n =  "   " ++ printTab (n-1)

showIdent :: Int -> Term -> String
showIdent n (Var id)      = printTab n ++ id
showIdent n (Lit num)     = printTab n ++ show num
showIdent n (Sum x y)     = printTab n ++ "(" ++ (show x) ++ " + " ++ (show y) ++ ")"
showIdent n (Mult x y)    = printTab n ++ "(" ++ (show x) ++ " * " ++ (show y) ++ ")"
showIdent n (Lam x y)     = printTab n ++ "(Lambda " ++ x ++ ": " ++ (show y) ++ ")"
showIdent n (Apl t1 t2)   = printTab n ++ (show t1) ++ "(" ++ (show t2) ++ ")"
showIdent n (Atr t1 t2)   = printTab n ++ (show t1) ++ " = " ++ (show t2)
showIdent n (Seq t1 t2)   = (showIdent n t1) ++ "\n" ++ (showIdent n t2)
showIdent n (MethodCall t1 id t2) = printTab n ++  (show t1) ++ "." ++ id ++ "(" ++ (show t2) ++ ")"
showIdent n (While t1 t2) = printTab n ++ "while(" ++ (show t1) ++ "){\n" ++ (showIdent (n+1) t2) ++ "\n" ++ printTab n ++ "}"
showIdent n (If t1 t2 t3) = printTab n ++ "if("    ++ (show t1) ++ "){\n" ++ (showIdent (n+1) t2) ++ "\n" ++ printTab n ++ "} else {\n" ++ (showIdent (n+1) t3) ++ "\n" ++ printTab n ++ "}"
showIdent n (New id)      = printTab n ++ "new " ++ id
showIdent n (InstanceOf t id) = printTab n ++ "InstanceOf(" ++ (show t) ++ ", " ++ id ++ ")"
showIdent n (For id t1 t2 t3) = printTab n ++  "for " ++ id ++ " in range(" ++ (show t1) ++ ", " ++ (show t2) ++ "){\n" ++ (showIdent (n+1) t3) ++ "}"
showIdent n (This) = printTab n ++ "this"
showIdent n (AField t id) = printTab n ++ (show t) ++ "." ++ id
showIdent n (TermVal v)   = printTab n ++ "TermVal(" ++ (show v) ++ ")"
showIdent n (EmptyTerm)   = printTab n

instance Show Term where
    show t = showIdent 0 t

instance Show Definition where
    show (Def id term)  = "def " ++ (id) ++ " = " ++ (show term)

instance Show Method where
    show (Method id term)  = "Method " ++ (id) ++ (show term)

instance Show Decl where
    show (ClassDecl id fields methods) = "ClassDecl " ++ id ++ " " ++ show fields ++ " " ++ show methods
    show (FunDecl id term) = "FunDecl " ++ id ++ " " ++ show term

-------- Tests ---------
-- Simple assertion helpers
assertEq :: (Eq a, Show a) => String -> a -> a -> IO ()
assertEq label expected actual =
    if expected == actual
        then putStrLn ("PASS " ++ label)
        else do
            putStrLn ("FAIL " ++ label)
            putStrLn ("  expected: " ++ show expected)
            putStrLn ("  got:      " ++ show actual)

-- | Normalize the heap by sorting its entries.
normalizeHeap :: Heap -> Heap
normalizeHeap = sortBy (comparing key)
    where
        key :: (Value, Object) -> Int
        key (Ref i, _) = i
        key _          = maxBound :: Int

-- | Normalize the state by sorting its entries.
normalizeState :: State -> State
normalizeState = sortBy (comparing fst)

-- | Normalize the entire triple (Value, State, Heap) for consistent comparison.
normalizeTriple :: (Value, State, Heap) -> (Value, State, Heap)
normalizeTriple (v, s, h) = (v, normalizeState s, normalizeHeap h)

-- | Assert the entire triple (Value, State, Heap) in one go.
-- Prints a single PASS/FAIL line; on failure, shows expected vs. actual.
expectAll :: String -> (Value, State, Heap) -> (Value, State, Heap) -> IO ()
expectAll label expected actual =
    let
        expected' = normalizeTriple expected
        actual'   = normalizeTriple actual
    in
    if expected' == actual'
        then putStrLn ("PASS " ++ label)
        else do
            putStrLn ("FAIL " ++ label)
            putStrLn ("  expected: " ++ show expected')
            putStrLn ("  got:      " ++ show actual')

-- | Convenience: run int and assert the whole triple against an expected one.
expectInt :: String -> (Value, State, Heap) -> Environment -> State -> Heap -> Term -> IO ()
expectInt label expected e s h t = expectAll label expected (int e s h t)

-- | Assert the value against the expected one.
expectValue :: String -> Value -> Value -> IO ()
expectValue label expected actual = assertEq label expected actual

-- | Assert the state against the expected one.
expectState :: String -> State -> State -> IO ()
expectState label expected actual = assertEq label (normalizeState expected) (normalizeState actual)

-- | Assert the heap against the expected one.
expectHeap :: String -> Heap -> Heap -> IO ()
expectHeap label expected actual = assertEq label (normalizeHeap expected) (normalizeHeap actual)

-- | Assert an object against the expected one.
expectObject :: String -> (String, [(String, Value)]) -> (String, [(String, Value)]) -> IO ()
expectObject label expected actual = assertEq label expected actual

-- Tests Basic Functions

testSearch :: IO ()
testSearch = do
    print $ "Test search:"
    -- Should return numbers
    expectValue "Should be able to find number variables" 
        (Num 5) (search "x" [("x", Num 5)])
    -- Should return Refs
    expectValue "Should be able to find ref variables" 
        (Ref 10) (search "x" [("x", Ref 10)])
    -- Should return functions
    expectValue "Should be able to find function variables" 
        (Fun (\v s h -> (Num 42, s, h))) (search "x" [("x", Fun (\v s h -> (Num 42, s, h)))])
    expectValue "Should return Error for unknown variable" 
        (Error "Var not found") (search "y" [("x", Num 5)])

testGetObj :: IO ()
testGetObj = do
    print $ "Test getObj:"
    expectObject "Should be able to return an object from heap (1)" 
        ("A", [("x", Num 5)]) (getObj (Ref 10) [(Ref 10, ("A", [("x", Num 5)]))])
    expectObject "Should be able to return an object from heap (2)" 
        ("B", [("y", Num 7)]) (getObj (Ref 20) [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))])
    expectObject "Should return empty object if Ref not found" 
        (("", [])) (getObj (Ref 30) [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))])
    expectObject "Should return empty object if Value is not Ref" 
        (("", [])) (getObj (Num 5) [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))])

testsumVal :: IO ()
testsumVal = do
    print $ "Test sumVal:"
    -- Should return Num with sum
    expectValue "Should be able to sum two Num" (Num 8) (sumVal (Num 5) (Num 3))
    -- Should return Error for Ref
    expectValue "Should return Error for Ref (1)" (Error "Cannot add non-numeric values") (sumVal (Num 5) (Ref 10))
    expectValue "Should return Error for Ref (2)" (Error "Cannot add non-numeric values") (sumVal (Ref 10) (Num 3))
    expectValue "Should return Error for Ref (3)"  (Error "Cannot add non-numeric values") (sumVal (Ref 10) (Ref 20))

testMultVal :: IO ()
testMultVal = do
    print $ "Test multVal:"
    -- Should return Num with multiplication
    expectValue "Should be able to multiply two Num" (Num 15) (multVal (Num 5) (Num 3))
    -- Should return Error for Ref
    expectValue "Should return Error for Ref (1)" (Error "Cannot multiply non-numeric values") (multVal (Num 5) (Ref 10))
    expectValue "Should return Error for Ref (2)" (Error "Cannot multiply non-numeric values") (multVal (Ref 10) (Num 3))
    expectValue "Should return Error for Ref (3)" (Error "Cannot multiply non-numeric values") (multVal (Ref 10) (Ref 20))

testApp :: IO ()
testApp = do
    print $ "Test app:"
    -- Should apply a function to a numeric value
    expectAll "Should be able to apply a function to a numeric value" (Num 42, [], []) (app (Fun (\v s h -> (Num 42, s, h))) (Num 5) [] [])
    -- Should return Error for Ref
    expectAll "Should return Error for Ref" (Error "Cannot apply non-numeric argument", [], []) (app (Fun (\v s h -> (Num 42, s, h))) (Ref 10) [] [])
    -- Should return Error for non-function
    expectAll "Should return Error for non-function" (Error "Cannot apply non-function", [], []) (app (Ref 10) (Num 5) [] [])
    -- Should apply a function for a closure with state and heap
    expectAll "Should be able to apply a function for a closure with state and heap" (Num 12, [("x", Num 5)], [(Ref 1, ("A", [("a", Num 12)]))]) (app (
            Fun (\v s h -> (
                    Num 12,
                    ("x", Num 5) : s,
                            (Ref 1, ("A", [("a", Num 12)])) : h
                            )
                        )
                ) (Num 5) [] []
        )

testWr :: IO ()
testWr = do
    print $ "Test wr:"
    -- Should return the written variable
    expectState "Should be able to create a new variable with a value" [("x", Num 5)] (wr ("x", Num 5) [])
    -- Should update existing variable
    expectState "Should be able to update an existing variable (1)" [("x", Num 5), ("y", Num 10)] (wr ("y", Num 10) [("x", Num 5)])
    expectState "Should be able to update an existing variable (2)" [("x", Num 5), ("y", Num 10)] (wr ("x", Num 5) [("x", Num 3), ("y", Num 10)])
    -- Should update existing variable with a function
    expectState "Should be able to update an existing variable with a function"
        [("x", Fun (\_ s' h' -> (Num 0, s', h'))), ("y", Num 10)]
        (wr ("x", Fun (\v s h -> (Num 42, s, h))) [("x", Num 3), ("y", Num 10)])

testWrh :: IO ()
testWrh = do
    print $ "Test wrh:"
    let h = [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))]
    -- Should write a field in an object
    expectHeap "Should be able to write a field in an object (1)" [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))] (wrh (Ref 10) ("x", Num 5) h)
    expectHeap "Should be able to write a field in an object (2)" [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 10)]))] (wrh (Ref 20) ("y", Num 10) h)
    expectHeap "Should be able to write a field in an object (3)" [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))] (wrh (Ref 30) ("z", Num 8) h)
    -- Should return empty object if Ref not found
    expectHeap "Should return empty object if Ref not found" [] (wrh (Ref 30) ("z", Num 8) h)


-- Test Interpreter Functions

testVar :: IO ()
testVar = do
    print $ "TEST Var:"
    expectInt "Should be able to find Var in state" (Num 5, [("x", Num 5)], []) [] [("x", Num 5)] [] (Var "x")
    expectInt "Should be able to find Var in environment" (Ref 10, [], []) [("x", Ref 10)] [] [] (Var "x")
    expectInt "Should return Error if Var not found" (Error "Var not found", [("y", Num 5)], []) [] [("y", Num 5)] [] (Var "x")

testLit :: IO ()
testLit = do
    print $ "TEST Lit:"
    expectInt "Should be able to return Lit 5 value" (Num 5, [], []) [] [] [] (Lit 5)
    expectInt "Should be able to return Lit -3 value" (Num (-3), [], []) [] [] [] (Lit (-3))

testSum :: IO ()
testSum = do
    print $ "TEST Sum:"
    expectInt "Should be able to return Sum (Lit 5) (Lit 3) value" (Num 8, [], []) [] [] [] (Sum (Lit 5) (Lit 3))
    expectInt "Should return Error if Var not found" (Error "Var not found", [], []) [] [] [] (Sum (Lit 5) (Var "x"))

testMult :: IO ()
testMult = do
    print $ "TEST Mult:"
    expectInt "Should be able to return Mult (Lit 5) (Lit 3) value" (Num 15, [], []) [] [] [] (Mult (Lit 5) (Lit 3))
    expectInt "Should return Error if Var not found" (Error "Var not found", [], []) [] [] [] (Mult (Lit 5) (Var "x"))

testAField :: IO ()
testAField = do
    print $ "TEST AField:"
    let h = [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))]
        s = [("o1", Ref 10)]
        e = [("o2", Ref 20)]
    expectInt "Should be able to return a number from a state variable object" (Num 5, s, h) e s h (AField (Var "o1") "x")
    expectInt "Should be able to return a number from an environment variable object" (Num 7, s, h) e s h (AField (Var "o2") "y")
    expectInt "Should return Error if object not found" (Error "Var not found", s, h) e s h (AField (Var "y") "x")
    expectInt "Should return Error if property not exists" (Error "Var not found", s, h) e s h (AField (Var "o1") "y")

testAtr :: IO ()
testAtr = do
    print $ "TEST Atr:"
    let h = [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))]
        s = [("o1", Ref 10)]
        e = [("o2", Ref 20)]
    expectInt "Should be able to create a new var in state" (Num 10, ("newVar", Num 10) : s, h) e s h (Atr (Var "newVar") (Lit 10))
    expectInt "Should be able to update existing var in state" (Num 5, [("o1", Num 5)], h) e s h (Atr (Var "o1") (Lit 5))
    expectInt "Should be able to update existing var in heap object" (Num 8, [("o1", Ref 10)], [(Ref 10, ("A", [("x", Num 8)])), (Ref 20, ("B", [("y", Num 7)]))]) e s h (Atr (AField (Var "o1") "x") (Lit 8))

testLam :: IO ()
testLam = do
    print $ "TEST Lam:"
    let h = [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))]
        s = [("o1", Ref 10)]
        e = [("o2", Ref 20)]
    expectInt "Should be able to create a lambda function" (Fun (\_ s' h' -> (Num 0, s', h')), s, h) e s h (Lam "x" (Sum (Var "x") (Lit 3)))
    let (Fun f, _, _) = int e s h (Lam "x" (Sum (Var "x") (Lit 3))) 
    expectAll "Should be able to apply a created lambda function" (Num 8, s, h) (f (Num 5) s h)


testSeq :: IO ()
testSeq = do
    print $ "TEST Seq:"
    let h = [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))]
        s = [("o1", Ref 10)]
        e = [("o2", Ref 20)]
    -- Should execute first term and then second
    expectInt "Should execute first term and then second" (Num 8, [("o1", Num 8)], h) e s h (Seq (Atr (Var "o1") (Lit 8)) (Var "o1"))

testApl :: IO ()
testApl = do
    print $ "TEST Apl:"
    let h = [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))]
        s = [("o1", Ref 10)]
        e = [("o2", Ref 20)]
    -- Should apply the function
    expectInt "Should apply the function" (Num 8, s, h) e s h (Apl (Lam "x" (Sum (Var "x") (Lit 3))) (Lit 5))

testIf :: IO ()
testIf = do
    print $ "TEST If:"
    let h = [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))]
        s = [("o1", Ref 10)]
        e = [("o2", Ref 20)]
    -- Should execute then branch
    expectInt "Should execute then branch" (Num 5, ("y", Num 5) : s, h) e s h (If (Lit 1) (Atr (Var "y") (Lit 5)) (Atr (Var "y") (Lit 3)))
    -- Should execute else branch
    expectInt "Should execute else branch" (Num 3, ("y", Num 3) : s, h) e s h (If (Lit 0) (Atr (Var "y") (Lit 5)) (Atr (Var "y") (Lit 3)))

testWhile :: IO ()
testWhile = do
    print $ "TEST While:"
    let h = [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))]
        s = [("x", Num 5), ("y", Num 0)]
        e = [("o2", Ref 20)]
    expectInt "Should execute body while condition is true" (Num 0, [("x", Num 0), ("y", Num 5)], h) e s h (While (Var "x") (Seq (Atr (Var "x") (Sum (Var "x") (Lit (-1)))) (Atr (Var "y") (Sum (Var "y") (Lit 1)))))
    expectInt "Should return Num 0 when condition is false" (Num 0, [("x", Num 5), ("y", Num 0)], h) e s h (While (Lit 0) (Atr (Var "x") (Lit 5)))

testInstanceOf :: IO ()
testInstanceOf = do
    print $ "TEST InstanceOf:"
    let h = [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))]
        s = [("o1", Ref 10)]
        e = [("o2", Ref 20)]
    -- Should return 1 if instance of class
    expectInt "Should return 1 if instance of class" (Num 1, s, h) e s h (InstanceOf (Var "o1") "A")
    -- Should return 0 if not instance of class
    expectInt "Should return 0 if not instance of class" (Num 0, s, h) e s h (InstanceOf (Var "o1") "B")

testNew :: IO ()
testNew = do
    print $ "TEST New:"
    let h = [(Ref 10, ("A", [("x", Num 5)])), (Ref 20, ("B", [("y", Num 7)]))]
        s = [("o1", Ref 10)]
        e = [("o2", Ref 20)]
    -- Should create a new object in heap
    expectInt "Should create a new object in heap" (Ref 3, s, (Ref 3, ("C", [])) : h) e s h (New "C")
    -- Should create a new object in heap and attribute to a new variable
    expectInt "Should create a new object in heap and attribute to a new variable" (Ref 3, ("o3", Ref 3) : s, (Ref 3, ("C", [])) : h) e s h (Atr (Var "o3") (New "C"))

-- | Execute all tests
main :: IO ()
main = do
    putStrLn "\n== TEST RESULTS =="
    putStrLn "== Basic helpers =="
    testSearch
    testGetObj
    testsumVal
    testMultVal
    putStrLn "\n== App =="
    testApp
    putStrLn "\n== Interpreter cases =="
    testVar
    testLit
    testSum
    testMult
    testAField
    testAtr
    testLam
    testSeq
    testApl
    testIf
    testWhile
    testInstanceOf
    testNew

--------------- Exemplos ------------------

contaMethod = Method "Depositar" (Lam "valor" (Atr (AField This "Saldo") (Sum (AField This "Saldo") (Var "valor"))))
contaMtSegu = Method "DepositarSeguro" (Lam "valor" ( 
    If (Apl (Apl (Var ">") (Var "valor")) (Lit 0))              ---if valor > 0
        (Atr (AField This "Saldo") (Sum (AField This "Saldo") (Var "valor")))   -- this.saldo += valor
        EmptyTerm  --empty else
            ))

contaClass = ClassDecl "Conta" ["Saldo"] [contaMethod, contaMtSegu]

-- Exemplos de definições de funções globais
squareFunc = FunDecl "square" (Lam "x" (Mult (Var "x") (Var "x")))
addTenFunc = FunDecl "addTen" (Lam "n" (Sum (Var "n") (Lit 10)))
doubleFunc = FunDecl "double" (Lam "x" (Mult (Var "x") (Lit 2)))

exampleAmbienteContaFromDecl = intDecl [contaClass]
exampleAmbienteFuncsFromDecl = intDecl [squareFunc, addTenFunc, doubleFunc]
baseEnv = [ ("<", ltFunction) ] ++ exampleAmbienteContaFromDecl ++ exampleAmbienteFuncsFromDecl -- inclui a função <, a classe Conta e as funções globais

contaAtrCt = Atr (Var "ct") (New "Conta")
contaSeeSaldo = AField (Var "ct") "Saldo"
ifTerm = If (Apl (Apl (Var "<") (Var "i")) (Lit 2))        -- if(i < 2)
            (MethodCall (Var "ct") "DepositarSeguro" (Lit (-55)))  --   ct.DepositarSeguro(-55)
            (MethodCall (Var "ct") "Depositar" (Lit 100))  -- else ct.Depositar(100)
whileTerm = Seq (Atr (Var "i") (Lit 1))                    -- i = 1
        ( While (Apl (Apl (Var "<") (Var "i")) (Lit 6))    -- while(i < 6)
            (Seq ifTerm                                    --   ifTerm
            (Atr (Var "i") (Sum (Var "i") (Lit 1))))       --   i = i + 1
        )
contaSeqPrograma = Seq contaAtrCt ( Seq whileTerm contaSeeSaldo )
contaDebugPrograma = Seq contaAtrCt (MethodCall (Var "ct") "Depositar" (Lit 100))

--------------------------------------------------------------------
runExample :: IO ()
runExample = do
    -- Executa o programa de exemplo
    let (ret, stateFinal, heapFinal) = runInBaseEnv contaSeqPrograma

    putStrLn $ "\n===================="
    putStrLn $ "Programa: \n--------------\n" ++ show contaSeqPrograma ++ "\n--------------"
    putStrLn $ "Resultado da execução: " ++ show ret
    putStrLn $ "Estado final: " ++ show stateFinal
    putStrLn $ "Heap final: " ++ show heapFinal

    case lookup "ct" stateFinal of
        Just ref@(Ref _) -> do
            let (_, campos) = getObj ref heapFinal
            putStrLn $ "Saldo final: " ++ show (lookup "Saldo" campos)
        _ -> putStrLn "Objeto 'ct' não encontrado no estado."

    putStrLn $ "====================\n"
--------------------------------------------------------------------

lessThan :: Value -> State -> Heap -> (Value, State, Heap)
lessThan v1 s h = (Fun lessThanSecond, s, h)
  where
    lessThanSecond :: Value -> State -> Heap -> (Value, State, Heap)
    lessThanSecond v2 s' h' = 
      case (v1, v2) of
        (Num n1, Num n2) -> (Num (if n1 < n2 then 1 else 0), s', h')
        _                -> (Error "Invalid operands to <", s', h')
ltFunction = Fun lessThan

-- Programas de exemplo para testar funções definidas
testSquareProgram = Apl (Var "square") (Lit 5)  -- deve retornar 25
testAddTenProgram = Apl (Var "addTen") (Lit 7)  -- deve retornar 17
testDoubleProgram = Apl (Var "double") (Lit 3)  -- deve retornar 6

-- Programa composto usando várias funções
testComposedProgram = Apl (Var "square") (Apl (Var "addTen") (Lit 2))  -- square(addTen(2)) = square(12) = 144

programWhile = Seq (Atr (Var "sum") (Lit 0))                -- sum = 0
    (Seq (Atr (Var "i") (Lit 1))                            -- i = 1
      (While (Apl (Apl (Var "<") (Var "i")) (Lit 101))      -- while(i < 101)
        ( Seq (Atr (Var "sum") (Sum (Var "sum") (Var "i"))) --    sum = sum + i
          (Atr (Var "i") (Sum (Var "i") (Lit 1))) )         --    i = i + 1
      )
    )

-- run in the base environment with empty state and heap
runInBaseEnv :: Term -> (Value, State, Heap)
runInBaseEnv t = int baseEnv [] [] t

-- Função para testar as definições de funções
testDefFunctions :: IO ()
testDefFunctions = do
    putStrLn "\n== TEST DEF FUNCTIONS =="
    
    let (result1, _, _) = runInBaseEnv testSquareProgram
    putStrLn $ "square(5) = " ++ show result1 ++ " (expected: 25.0)"

    let (result2, _, _) = runInBaseEnv testAddTenProgram  
    putStrLn $ "addTen(7) = " ++ show result2 ++ " (expected: 17.0)"

    let (result3, _, _) = runInBaseEnv testDoubleProgram
    putStrLn $ "double(3) = " ++ show result3 ++ " (expected: 6.0)"

    let (result4, _, _) = runInBaseEnv testComposedProgram
    putStrLn $ "square(addTen(2)) = " ++ show result4 ++ " (expected: 144.0)"
