import Std.Data.HashMap

inductive Typ
  | var : String → Typ
  | fn : Typ → Typ → Typ
  | prod : Typ → Typ → Typ
  | sum : Typ → Typ → Typ
deriving BEq

inductive Term
  | var : Typ → String → Term
  | fn : Typ → String → Term → Term
  | app : Typ → Term → Term → Term
  | prod : Typ → Term → Term → Term
  | sum : Typ → Term → Term → Term

def Term.getTyp : Term → Typ
  | .var τ _ => τ
  | .fn τ _ _ => τ
  | .app τ _ _ => τ
  | .prod τ _ _ => τ
  | .sum τ _ _ => τ

def check (env : Std.HashMap String Typ) : Term → Bool
  | .var τ x =>
    (· == τ) <$> env[x]? |>.getD false
  | .fn τ x b =>
    match τ with
    | .fn α β => b.getTyp == β && check (env.insert x α) b
    | _ => false
  | .app τ f x =>
    match f.getTyp with
    | .fn α β => x.getTyp == α && β == τ && check env f && check env x
    | _ => false
  | .prod τ x y =>
    match τ with
    | .prod α β =>
      x.getTyp == α && y.getTyp == β && check env x && check env y
    | _ => false
  | .sum τ x y =>
    match τ with
    | .sum α β =>
      x.getTyp == α && y.getTyp == β && check env x && check env y
    | _ => false

def ab_imp_ba := Term.fn (.fn (.var "A") (.fn (.var "B") (.prod (.var "B") (.var "A")))) "a" (.fn (.fn (.var "B") (.prod (.var "B") (.var "A"))) "b" (.prod (.prod (.var "B") (.var "A")) (.var (.var "B") "b") (.var (.var "A") "a")))

#eval check (.ofList []) ab_imp_ba
