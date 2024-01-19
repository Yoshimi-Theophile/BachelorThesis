
data Term 
    = Var String
    | Lambda String Term
    | App Term Term

printTerm :: Term -> String
printTerm (Var x) = x 
printTerm (Lambda x t) = "\\" ++ x ++ "." ++ printTerm t
printTerm (App t1 t2) = "(" ++ printTerm t1 ++ " " ++ printTerm t2 ++ ")"

type Env = [(String, Term)]

find :: String -> Env -> Term
find s [] = Var s
find s ((v, t) : tail) = if s == v then t else find s tail

reduce :: Term -> Env -> Term
reduce (Var x) e = find x e
reduce (Lambda x t) e = Lambda x (reduce t e)
reduce (App t1 t2) e = case reduce t1 e of 
    Lambda y t3 -> reduce t3 ((y, reduce t2 e) : e)
    any -> App any (reduce t2 e) 

data LType
    = TVar String
    | TApp LType LType

type TEnv = [(Term, LType)]

printType :: LType -> String
printType (TVar v) = v
printType (TApp v1 v2) = "( " ++ v1 ++ " -> " ++ v2 ++ " )"

-- genSym :: Int -> String


-- getLinType :: Term -> Type
-- getLinType (Var x)

churchTrue :: Term = Lambda "x" (Lambda "y" (Var "x"))
churchFalse :: Term = Lambda "x" (Lambda "y" (Var "y"))