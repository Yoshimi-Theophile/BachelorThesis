{-

To Do
- Fix Type Unification
- Add More Examples
- make isLinear, isPlanar, isBridgeless

note:

    reduce (multiApp linOr [linTrue, linFalse])

outputs

    Lambda "x0000000" (Lambda "y00000000000000" (Lambda "k0000000000000000000000000000" (App (App (Var "k0000000000000000000000000000") (Var "x0000000")) (Var "y00000000000000"))))

(i.e. make genSymFromList increment an existing number instead of adding one each time)

-}

-- ===== Types =====

data Term 
    = Var String
    | Lambda String Term
    | App Term Term
    deriving (Show, Eq)

type Env = [(String, Term)]

data LType
    = TVar String
    | TApp LType LType
    deriving (Show, Eq)

type TEnv = [(Term, LType)]

-- ===== Printing =====

printTerm :: Term -> String
printTerm (Var x) = x 
printTerm (Lambda x t) = "\\" ++ x ++ "." ++ printTerm t
printTerm (App t1 t2) = "(" ++ printTerm t1 ++ " " ++ printTerm t2 ++ ")"

printType :: LType -> String
printType (TVar v) = v
printType (TApp v1 v2) = "( " ++ printType v1 ++ " -> " ++ printType v2 ++ " )"

-- ===== List Search =====

findEnv :: String -> Env -> Term
findEnv s [] = Var s
findEnv s ((v, t) : tail) = if s == v then t else findEnv s tail

findTEnv :: Term -> TEnv -> Int -> LType
findTEnv (Var s) [] n = TVar (s ++ show n)
findTEnv s [] n = TVar ("c" ++ show n)
findTEnv s ((v, ty) : tail) n = if s == v then ty else findTEnv s tail n

findVList :: String -> [String] -> Bool
findVList s [] = False
findVList s (v : tail) = if s == v then True else findVList s tail

-- ===== reduction =====

{-
-- assume all bound variables are used (true for LLC)
-- gets free and bound variables from a term
getFBV :: Term -> [String] 
getFBV (Var x) = [x]
getFBV (Lambda x t) = getFBV t
getFBV (App t1 t2) = (getFBV t1) ++ (getFBV t2)
-}

deleteAll :: (Eq t) => t -> [t] -> [t]
deleteAll a [] = []
deleteAll a (hd : tail) = if a==hd then deleteAll a tail else hd : (deleteAll a tail)

getFV :: Term -> [String]
getFV (Var x) = [x]
getFV (Lambda x t) = deleteAll x (getFV t)
getFV (App t1 t2) = getFV t1 ++ getFV t2

getBV :: Term -> [String]
getBV (Var x) = []
getBV (Lambda x t) = x : (getBV t)
getBV (App t1 t2) = getBV t1 ++ getBV t2

-- creates a new variable name that doesn't exist in a list of names
genSymFromList :: String -> Int -> [String] -> String
genSymFromList x n li = 
    if findVList x li 
    then let newvar = x ++ show n in
        if findVList newvar li
        then genSymFromList x (n+1) li
        else newvar
    else x

-- update variable x in term y with z
subst :: String -> Term -> Term -> Term
subst a (Var x) b = 
    if a == x
    then b
    else Var x
subst a (Lambda x t) b = 
    if a == x
    then (Lambda x t)
    else let xnew = genSymFromList x 0 ([a] ++ getFV b ++ getFV t) in
        Lambda xnew (subst a (subst x t (Var xnew)) b)
subst a (App t1 t2) b =
    App (subst a t1 b) (subst a t2 b)

-- Lambda x (substVar a t b)

reduceHelper :: Term -> Env -> Term
reduceHelper (Var x) e = findEnv x e
reduceHelper (Lambda x t) e = Lambda x (reduceHelper t e)
reduceHelper (App t1 t2) e = case reduceHelper t1 e of 
    Lambda y t3 -> 
        let t3new = subst y t3 t2 in
        reduceHelper t3new ((y, reduceHelper t2 e) : e)
    any -> App any (reduceHelper t2 e)

reduce :: Term -> Term
reduce t = reduceHelper t []

-- ===== Type Inference =====

-- unify is very probably wrong
unify :: LType -> LType -> LType -- first type priority
unify (TApp l1 l2) (TApp r1 r2) = TApp (unify l1 r1) (unify l2 r2)
unify (TVar l) (TVar r) = TVar l
unify (TApp l1 l2) (TVar r) = TApp l1 l2
unify (TVar l) (TApp r1 r2) = TApp r1 r2


red :: Term -> TEnv -> Int -> (LType, TEnv, Int)
red (Var x) e n = 
    let new = (x ++ show n) in
        (TVar new, (Var x, TVar new) : e, n+1)
red (Lambda x t) e n =
    let (tyt, et, nt) = red t e n in
    let tyx = findTEnv (Var x) et nt in
        (TApp tyx tyt, et, nt+1)
red (App t1 t2) e n =
    let (tyt2, et2, nt2) = red t2 e n in
    let gentype = ("a" ++ show nt2) in
    let (tyt1, et1, nt1) = blue t1 et2 (TApp tyt2 (TVar gentype)) (nt2+1) in
        (TVar gentype, et1, nt1)

blue :: Term -> TEnv -> LType -> Int -> (LType, TEnv, Int)
blue (Var x) e ty n = 
    (ty, (Var x, ty) : e, n)
blue (Lambda x t) e ty n = case ty of
    TApp ty1 ty2 -> let (tyt, et, nt) = red t ((Var x, ty1) : e) n in
                    (TApp ty1 (unify ty2 tyt), et, nt)
    v -> (v, ((Lambda x t), v) : e, n)
blue (App t1 t2) e ty n =
    let (tyt2, et2, nt2) = red t2 e n in
    let (tyt1, et1, nt1) = blue t1 et2 (TApp tyt2 ty) nt2 in
        (ty, et1, nt1)

getLinType :: Term -> LType
getLinType (Var x) = TVar x
getLinType (Lambda x t) = let (tyr, er, nr) = red (Lambda x t) [] 0 in tyr
getLinType (App t1 t2) = let (tyr, er, nr) = blue (App t1 t2) [] (TVar "a") 0 in tyr

-- QoL functions

multiApp :: Term -> [Term] -> Term
multiApp t [] = t
multiApp t (arg : tail) = multiApp (App t arg) tail

multiLambda :: [String] -> Term -> Term
multiLambda [] t = t
multiLambda (s : tail) t = (Lambda s (multiLambda tail t))

-- ===== Testing =====

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

linTrue :: Term = multiLambda ["x", "y", "k"] (multiApp (Var "k") [Var "x", Var "y"])
linFalse :: Term = multiLambda ["x", "y", "k"] (multiApp (Var "k") [Var "y", Var "x"])

linNot :: Term = multiLambda ["P", "x", "y"] (multiApp (Var "P") [Var "y", Var "x"])

test1 :: Term = multiLambda ["x", "y"] (App (Var "x") (Var "y"))
test2 :: Term = multiLambda ["x", "y"] (App (Var "y") (Var "x"))
test :: Term = multiApp (multiLambda ["x", "y"] (App (Var "x") (Var "y"))) [Var "y"]

-- printTerm (reduce (App linNot test1))
-- reduce (App (Lambda "x" (Var "x")) (Var "x"))

identity :: Term = Lambda "x" (Var "x")
id :: Term = Lambda "B" (multiApp (Var "B") [identity, identity, identity])

linOr :: Term = multiLambda ["P", "Q"] (multiApp (Var "P") [linTrue, Var "Q", multiLambda ["u", "v"] (multiApp id [Var "v", Var "u"])])
linAnd :: Term = multiLambda ["P", "Q"] (multiApp (Var "P") [Var "Q", linFalse, multiLambda ["u", "v"] (multiApp id [Var "v", Var "u"])])

linPair :: Term = multiLambda ["x", "y", "z"] (multiApp (Var "z") [Var "x", Var "y"])

linCopy :: Term = multiApp (Var "P") [
    (multiApp linPair [linTrue, linTrue]),
    (multiApp linPair [linFalse, linFalse]),
    multiLambda ["U", "V"] (App (Var "U") (multiLambda ["u1", "u2"] (App (Var "V") (multiLambda ["v1", "v2"] (multiApp linPair [
            multiApp id [Var "v1", Var "u1"],
            multiApp id [Var "v2", Var "u2"]
        ])))))
    ]

cp1 :: Term = multiLambda ["fnc", "p", "k"] (App (Var "k") (App (Var "fnc") (Var "p")))
cp2 :: Term = multiLambda ["fnc", "p", "q", "k"] (App (Var "k") (multiApp (Var "fnc") [Var "p", Var "q"]))

linNotGate :: Term = App cp1 linNot
linOrGate :: Term = App cp2 linOr
linAndGate :: Term = App cp2 linAnd

-- reduce test