{-

To Do
- Fix reduce (why is it wrong?)
- Add More Examples
- make sure getLinType works without reduced terms
- make isLinear, isPlanar, isBridgeless

-}

data Term 
    = Var String
    | Lambda String Term
    | App Term Term

type Env = [(String, Term)]

printTerm :: Term -> String
printTerm (Var x) = x 
printTerm (Lambda x t) = "\\" ++ x ++ "." ++ printTerm t
printTerm (App t1 t2) = "(" ++ printTerm t1 ++ " " ++ printTerm t2 ++ ")"

findEnv :: String -> Env -> Term
findEnv s [] = Var s
findEnv s ((v, t) : tail) = if s == v then t else findEnv s tail

reduceHelper :: Term -> Env -> Term
reduceHelper (Var x) e = findEnv x e
reduceHelper (Lambda x t) e = Lambda x (reduceHelper t e)
reduceHelper (App t1 t2) e = case reduceHelper t1 e of 
    Lambda y t3 -> reduceHelper t3 ((y, reduceHelper t2 e) : e)
    any -> App any (reduceHelper t2 e) 

reduce :: Term -> Term
reduce t = reduceHelper t []

data LType
    = TVar String
    | TApp LType LType

type TEnv = [(Term, LType)]

printType :: LType -> String
printType (TVar v) = v
printType (TApp v1 v2) = "( " ++ printType v1 ++ " -> " ++ printType v2 ++ " )"

-- comparison

eqTerm :: Term -> Term -> Bool
eqTerm (Var x) (Var y) = x == y
eqTerm (Lambda x t1) (Lambda y t2) = (x == y) && (eqTerm t1 t2)
eqTerm (App t1 t2) (App t3 t4) = (eqTerm t1 t3) && (eqTerm t2 t4)
eqTerm other1 other2 = False

eqType :: LType -> LType -> Bool
eqType (TVar x) (TVar y) = x == y
eqType (TApp ty1 ty2) (TApp ty3 ty4) = (eqType ty1 ty3) && (eqType ty2 ty4)
eqType other1 other2 = False

findTEnv :: Term -> TEnv -> Int -> LType
findTEnv (Var s) [] n = TVar (s ++ show n)
findTEnv s [] n = TVar ("c" ++ show n)
findTEnv s ((v, ty) : tail) n = if eqTerm s v then ty else findTEnv s tail n

-- update x in y with z

-- assumed first argument is a TVar (change necessary?)
updateType :: LType -> LType -> LType -> LType
updateType t (TVar y) target = if eqType t (TVar y) then target else TVar y
updateType t (TApp ty1 ty2) target = TApp (updateType t ty1 target) (updateType t ty2 target)

updateTEnv :: LType -> TEnv -> LType -> TEnv
updateTEnv t [] ty = []
updateTEnv t ((t1, ty1) : tail) ty = (t1, updateType t ty1 ty) : (updateTEnv t tail ty)

-- currently only works if beta-normal (which is annoying)
getLinTypeHelper :: Term -> TEnv -> Int -> (LType, TEnv, Int)
getLinTypeHelper (Var x) e n = (findTEnv (Var x) e n, e, n+1)
getLinTypeHelper (Lambda x t) e n = let varty = TVar (x ++ show n) in 
                                    let (ty, ey, ny) = (getLinTypeHelper t ((Var x, varty) : e) (n+1)) in 
                                    (TApp (findTEnv (Var x) ey n) ty, ey, ny)
getLinTypeHelper (App t1 t2) e n = let (ty2, e2, n2) = (getLinTypeHelper t2 e n) in 
    case t1 of
    Lambda y t3 ->  let (ty3, e3, n3) = (getLinTypeHelper t3 ((Var y, ty2) : e2) n2) in
                        (ty3, e3, n3)
    Var x ->        let gentype = (TVar ("a" ++ show n2)) in
                    let enew = updateTEnv (findTEnv (Var x) e n2) e2 (TApp ty2 gentype) in
                        (gentype, enew, n2+1)
    app ->          let (tyapp, eapp, napp) = (getLinTypeHelper app e2 n2) in
                    let gentype = (TVar ("b" ++ show napp)) in
                    let enew = updateTEnv tyapp eapp (TApp ty2 gentype) in
                        (gentype, enew, napp+1)
    -- any -> (TVar ("a" ++ show n), n+1)

getLinType :: Term -> LType
getLinType t = let (ty, e, n) = (getLinTypeHelper t [] 0) in ty

-- QoL functions

multiApp :: Term -> [Term] -> Term
multiApp t [] = t
multiApp t (arg : tail) = multiApp (App t arg) tail

multiLambda :: [String] -> Term -> Term
multiLambda [] t = t
multiLambda (s : tail) t = (Lambda s (multiLambda tail t))

{- 
Simple church boolean functions
These aren't linear, but getLinType/reduce only require each argument to be used at MOST once.
Therefore I use them for testing anyway.
-}

churchTrue :: Term = Lambda "x" (Lambda "y" (Var "x"))
churchFalse :: Term = Lambda "x" (Lambda "y" (Var "y"))

smalltest :: Term = App (App churchTrue churchTrue) churchFalse

churchNot :: Term = Lambda "p" (App (App (Var "p") churchFalse) churchTrue)
churchAnd :: Term = Lambda "p" (Lambda "q" (App (App (Var "p") (Var "q")) churchFalse))
churchOr :: Term = Lambda "p" (Lambda "q" (App (App (Var "p") churchTrue) (Var "q")))

-- printTerm (reduce (App churchAnd churchTrue))
-- printType (getLinType (App churchAnd churchTrue))

{-
Linear
-}

linTrue :: Term = multiLambda ["x", "y"] (App (Var "x") (Var "y"))
linFalse :: Term = multiLambda ["x", "y"] (App (Var "y") (Var "x"))

linNot :: Term = multiLambda ["P", "x", "y"] (multiApp (Var "P") [Var "y", Var "x"])

-- printTerm (reduce (App linNot linTrue))
-- printTerm (reduce (App linNot linFalse))