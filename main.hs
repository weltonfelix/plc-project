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
