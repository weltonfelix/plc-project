module Main where

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

data Decl= Method Id Term -- Term --> Lambda
           | Class Id [Id] [Method]
           | Fun Id Term

data Definition = Def Id Term

type Program = [Definition]





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
