import Data.Char
-- import Debug.Trace

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

type TEnv = [(String, LType)]

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

findTEnv :: String -> TEnv -> Int -> LType
findTEnv s [] n = TVar (s ++ show n)
findTEnv s ((v, ty) : tail) n = if s == v then ty else findTEnv s tail n

findVList :: String -> [String] -> Bool
findVList s [] = False
findVList s (v : tail) = if s == v then True else findVList s tail

-- ===== reduction =====

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

incrementStringAux :: String -> (String, Bool)
incrementStringAux num =
    case num of
        "9" -> ("0", True)
        c:[] -> ((chr ((ord c) + 1)):[], False)
        '9':tail -> let (n, r) = incrementStringAux tail in
            if r then ('0':n, True) else ('9':n, False)
        c:tail -> let (n, r) = incrementStringAux tail in
            if r then ((chr ((ord c) + 1)):n, True) else (c:n, False)

incrementString :: String -> String
incrementString x = let (ret, _) = incrementStringAux x in ret

genSymIncrement :: String -> String -> [String] -> String
genSymIncrement origin number li =
    let newnum = incrementString number in
        if findVList (origin ++ newnum) li
        then genSymIncrement origin newnum li
        else origin ++ newnum

genSymAux :: String -> String -> [String] -> String
genSymAux x acc li =
    case x of
        [] -> (genSymIncrement (acc ++ "_") "0" li)
        c:tail -> if c == '_' then (genSymIncrement (acc ++ [c]) tail li)
                  else genSymAux tail (acc ++ [c]) li 

genSymFromList :: String -> [String] -> String
genSymFromList x li = 
    if findVList x li 
    then genSymAux x "" li
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
    else let xnew = genSymFromList x ([a] ++ getFV b ++ getFV t) in
        Lambda xnew (subst a (subst x t (Var xnew)) b)
subst a (App t1 t2) b =
    App (subst a t1 b) (subst a t2 b)

substalpha :: String -> Term -> Term -> Term
substalpha a (Var x) b = Var x
substalpha a (Lambda x t) b = 
    if a == x
    then (Lambda x t)
    else let xnew = genSymFromList x ([a] ++ getFV b ++ getFV t) in
        Lambda xnew (substalpha a (subst x t (Var xnew)) b)
substalpha a (App t1 t2) b =
    App (subst a t1 b) (subst a t2 b)

-- Lambda x (substVar a t b)

substreduce :: Term -> Term
substreduce (Var x) = Var x
substreduce (Lambda x t) = Lambda x (substreduce t)
substreduce (App t1 t2) = case substreduce t1 of 
    Lambda y t3 -> 
        let t3new = subst y t3 t2 in
        substreduce t3new
    any -> App any (substreduce t2)

reduceHelper :: Term -> Env -> Term
reduceHelper (Var x) e = findEnv x e
reduceHelper (Lambda x t) e = Lambda x (reduceHelper t e)
reduceHelper (App t1 t2) e = case reduceHelper t1 e of 
    Lambda y t3 -> 
        let t3new = substalpha y t3 t2 in
        reduceHelper t3new ((y, reduceHelper t2 e) : e)
    any -> App any (reduceHelper t2 e)

reduce :: Term -> Term
reduce t = reduceHelper t []

-- ===== Type Inference =====

-- update x in y with z
typesubst :: String -> LType -> LType -> LType
typesubst a ty ty2 = case ty of
    TVar b -> if a == b then ty2 else TVar b
    TApp tyl tyr -> TApp (typesubst a tyl ty2) (typesubst a tyr ty2)

tenvsubst :: String -> TEnv -> LType -> TEnv
tenvsubst a [] ty2 = []
tenvsubst a ((s, ty):tail) ty2 = (s, typesubst a ty ty2) : (tenvsubst a tail ty2)

teqsubst :: String -> [(LType, LType)] -> LType -> [(LType, LType)]
teqsubst a [] ty3 = []
teqsubst a ((ty1, ty2):tail) ty3 = (typesubst a ty1 ty3, typesubst a ty2 ty3) : (teqsubst a tail ty3)

unify :: [(LType, LType)] -> LType -> TEnv -> (LType, TEnv)
unify [] ty e = (ty, e)
unify ((lhs,rhs):tail) ty e = case (lhs, rhs) of
    (TVar a, TVar b) -> unify (teqsubst a tail (TVar b)) (typesubst a ty (TVar b)) (tenvsubst a e (TVar b))
    (TVar a, TApp r1 r2) -> unify (teqsubst a tail (TApp r1 r2)) (typesubst a ty (TApp r1 r2)) (tenvsubst a e (TApp r1 r2))
    (TApp l1 l2, TVar b) -> unify (teqsubst b tail (TApp l1 l2)) (typesubst b ty (TApp l1 l2)) (tenvsubst b e (TApp l1 l2))
    (TApp l1 l2, TApp r1 r2) -> unify ((r1, l1):(l2, r2):tail) ty e

getbasename :: Term -> String
getbasename (Var x) = x ++ "_"
getbasename t = "a_"

synth :: Term -> Int -> (LType, TEnv, Int)
synth (Lambda x t) n =
    let (tyt, et, nt) = synth t n in
    let tyx = findTEnv x et nt in
        (TApp tyx tyt, et, nt+1)
synth t n =
    let gentype = ((getbasename t) ++ show n) in
    check t (TVar gentype) [] (n+1)

check :: Term -> LType -> TEnv -> Int -> (LType, TEnv, Int)
check (Var x) ty e n = 
    (ty, (x, ty):e, n)
check (App t1 t2) ty e n =
    let (tyt2, et2, nt2) = synth t2 n in
    let (tyt1, et1, nt1) = check t1 (TApp tyt2 ty) (et2 ++ e) nt2 in
        case tyt1 of
            TApp start end -> (end, et1 ++ et2, nt1)
            def -> (ty, et1 ++ et2, nt1) -- fallback; should not happen
check t ty e n =
    let (tyL, eL, nL) = synth t n in
    let (tyEq, eEq) = unify [(tyL, ty)] ty (eL ++ e) in
    (tyEq, eEq, nL)

getLinType :: Term -> LType
getLinType (Var x) = TVar x
getLinType (Lambda x t) = let (tyr, er, nr) = synth (Lambda x t) 0 in tyr
getLinType (App t1 t2) = let (tyr, er, nr) = synth (App t1 t2) 0 in tyr

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

-- "((\\P.\\Q.(((P \\x.\\y.\\k.((k x) y)) Q) \\u.\\v.((\\B.(((B \\x.x) \\x.x) \\x.x) v) u)) \\x.\\y.\\k.((k x) y)) \\x.\\y.\\k.((k y) x))"
-- reduce (multiApp linOr [linTrue, linFalse])
-- Lambda "x_7" (Lambda "y_4" (Lambda "k_0" (App (App (Var "k_0") (Var "x_7")) (Var "y_4"))))

-- reduce (App (Lambda "x" (Var "x")) (Var "x"))
-- Var "x"

-- "(\\P.\\x.\\y.((P y) x) \\x.\\y.(x y))"
-- reduce (App linNot test1)
-- Lambda "x_1" (Lambda "y_2" (App (Var "y_2") (Var "x_1")))

allRules :: Term = Lambda "x" (multiApp (Lambda "y" (App (Var "x") (Var "y"))) [Lambda "a" (Var "a"), Lambda "b" (Var "b")])

mini :: Term = Lambda "x" (multiApp (Lambda "y" (App (Var "x") (Var "y"))) [Lambda "a" (Var "a")])