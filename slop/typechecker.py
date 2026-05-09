import sys

from dataclasses import dataclass
from typing import Any

@dataclass(frozen=True)
class Term:
    pass

@dataclass(frozen=True)
class Var(Term):
    x: int

@dataclass(frozen=True)
class Lam(Term):
    b: Term
    beta: Term

@dataclass(frozen=True)
class App(Term):
    f: Term
    phi: Term
    a: Term
    alpha: Term

@dataclass(frozen=True)
class Typ(Term):
    u: int

@dataclass(frozen=True)
class Fn(Term):
    alpha: Term
    beta: Term

@dataclass(frozen=True)
class Prod(Term):
    alpha: Term
    beta: Term

@dataclass(frozen=True)
class Pmk(Term):
    pass

@dataclass(frozen=True)
class ProdRec(Term):
    pass

@dataclass(frozen=True)
class Sum(Term):
    alpha: Term
    beta: Term

@dataclass(frozen=True)
class Inl(Term):
    pass

@dataclass(frozen=True)
class Inr(Term):
    pass

@dataclass(frozen=True)
class SumRec(Term):
    pass

@dataclass(frozen=True)
class Eq(Term):
    a: Term
    a_prime: Term
    alpha: Term

@dataclass(frozen=True)
class Refl(Term):
    pass

@dataclass(frozen=True)
class EqRec(Term):
    pass

@dataclass(frozen=True)
class Nat(Term):
    pass

@dataclass(frozen=True)
class Zero(Term):
    pass

@dataclass(frozen=True)
class Succ(Term):
    pass

@dataclass(frozen=True)
class NatRec(Term):
    pass

@dataclass(frozen=True)
class Unit(Term):
    pass

@dataclass(frozen=True)
class Intro(Term):
    pass

@dataclass(frozen=True)
class Fls(Term):
    pass

@dataclass(frozen=True)
class FlsRec(Term):
    pass

def parse_sexp(s: str) -> Term:
    s = s.replace("(", " ( ").replace(")", " ) ")
    tokens = s.split()
    
    def parse_tokens(tokens, idx):
        token = tokens[idx]
        if token == "(":
            idx += 1
            args = []
            while tokens[idx] != ")":
                arg, idx = parse_tokens(tokens, idx)
                args.append(arg)
            idx += 1
            return args, idx
        else:
            return token, idx + 1
            
    ast, _ = parse_tokens(tokens, 0)
    
    def build_term(ast) -> Term:
        if not isinstance(ast, list):
            return ast
        op = ast[0]
        if op == "0n": return Var(int(ast[1]))
        elif op == "1n": return Lam(build_term(ast[1]), build_term(ast[2]))
        elif op == "2n": return App(build_term(ast[1]), build_term(ast[2]), build_term(ast[3]), build_term(ast[4]))
        elif op == "3n": return Typ(int(ast[1]))
        elif op == "4n": return Fn(build_term(ast[1]), build_term(ast[2]))
        elif op == "5n": return Prod(build_term(ast[1]), build_term(ast[2]))
        elif op == "6n": return Pmk()
        elif op == "7n": return ProdRec()
        elif op == "8n": return Sum(build_term(ast[1]), build_term(ast[2]))
        elif op == "9n": return Inl()
        elif op == "10n": return Inr()
        elif op == "11n": return SumRec()
        elif op == "12n": return Eq(build_term(ast[1]), build_term(ast[2]), build_term(ast[3]))
        elif op == "13n": return Refl()
        elif op == "14n": return EqRec()
        elif op == "15n": return Nat()
        elif op == "16n": return Zero()
        elif op == "17n": return Succ()
        elif op == "18n": return NatRec()
        elif op == "19n": return Unit()
        elif op == "20n": return Intro()
        elif op == "21n": return Fls()
        elif op == "22n": return FlsRec()
        else:
            raise ValueError(f"Unknown op: {op}")
            
    return build_term(ast)

dbtypes_strs = [
    "(3n 1)",
    "(4n (3n 0) (4n (4n (0n 0) (3n 0)) (4n (0n 1) (4n (2n (0n 1) (4n (0n 2) (3n 0)) (0n 0) (0n 2)) (5n (0n 3) (0n 2))))))",
    "(4n (3n 0) (4n (4n (0n 0) (3n 0)) (4n (4n (5n (0n 1) (0n 0)) (3n 0)) (4n (4n (0n 2) (4n (2n (0n 2) (4n (0n 3) (3n 0)) (0n 0) (0n 3)) (2n (0n 2) (4n (5n (0n 4) (0n 3)) (3n 0)) (2n (2n (2n (2n (6n) (4n (3n 0) (4n (4n (0n 0) (3n 0)) (4n (0n 1) (4n (2n (0n 1) (4n (0n 2) (3n 0)) (0n 0) (0n 2)) (5n (0n 3) (0n 2)))))) (0n 4) (3n 0)) (4n (4n (0n 4) (3n 0)) (4n (0n 5) (4n (2n (0n 1) (4n (0n 6) (3n 0)) (0n 0) (0n 6)) (5n (0n 7) (0n 2))))) (0n 3) (4n (0n 4) (3n 0))) (4n (0n 4) (4n (2n (0n 4) (4n (0n 5) (3n 0)) (0n 0) (0n 5)) (5n (0n 6) (0n 5)))) (0n 1) (0n 4)) (4n (2n (0n 3) (4n (0n 4) (3n 0)) (0n 1) (0n 4)) (5n (0n 5) (0n 4))) (0n 0) (2n (0n 3) (4n (0n 4) (3n 0)) (0n 1) (0n 4))) (5n (0n 4) (0n 3))))) (4n (5n (0n 3) (0n 2)) (2n (0n 2) (4n (5n (0n 4) (0n 3)) (3n 0)) (0n 0) (5n (0n 4) (0n 3))))))))",
    "(4n (3n 0) (4n (3n 0) (4n (0n 1) (8n (0n 2) (0n 1)))))",
    "(4n (3n 0) (4n (3n 0) (4n (0n 0) (8n (0n 2) (0n 1)))))",
    "(4n (3n 0) (4n (3n 0) (4n (4n (8n (0n 1) (0n 0)) (3n 0)) (4n (4n (0n 2) (2n (0n 1) (4n (8n (0n 3) (0n 2)) (3n 0)) (2n (2n (2n (9n) (4n (3n 0) (4n (3n 0) (4n (0n 1) (8n (0n 2) (0n 1))))) (0n 3) (3n 0)) (4n (3n 0) (4n (0n 4) (8n (0n 5) (0n 1)))) (0n 2) (3n 0)) (4n (0n 3) (8n (0n 4) (0n 3))) (0n 0) (0n 3)) (8n (0n 3) (0n 2)))) (4n (4n (0n 2) (2n (0n 2) (4n (8n (0n 4) (0n 3)) (3n 0)) (2n (2n (2n (10n) (4n (3n 0) (4n (3n 0) (4n (0n 0) (8n (0n 2) (0n 1))))) (0n 4) (3n 0)) (4n (3n 0) (4n (0n 0) (8n (0n 6) (0n 1)))) (0n 3) (3n 0)) (4n (0n 3) (8n (0n 5) (0n 4))) (0n 0) (0n 3)) (8n (0n 4) (0n 3)))) (4n (8n (0n 4) (0n 3)) (2n (0n 3) (4n (8n (0n 5) (0n 4)) (3n 0)) (0n 0) (8n (0n 5) (0n 4)))))))))",
    "(4n (3n 0) (4n (0n 0) (12n (0n 0) (0n 0) (0n 1))))",
    "(4n (3n 0) (4n (0n 0) (4n (4n (0n 1) (4n (12n (0n 1) (0n 0) (0n 2)) (3n 0))) (4n (2n (2n (0n 0) (4n (0n 2) (4n (12n (0n 2) (0n 0) (0n 3)) (3n 0))) (0n 1) (0n 2)) (4n (12n (0n 1) (0n 1) (0n 2)) (3n 0)) (2n (2n (13n) (4n (3n 0) (4n (0n 0) (12n (0n 0) (0n 0) (0n 1)))) (0n 2) (3n 0)) (4n (0n 2) (12n (0n 0) (0n 0) (0n 3))) (0n 1) (0n 2)) (12n (0n 1) (0n 1) (0n 2))) (4n (0n 3) (4n (12n (0n 3) (0n 0) (0n 4)) (2n (2n (0n 3) (4n (0n 5) (4n (12n (0n 5) (0n 0) (0n 6)) (3n 0))) (0n 1) (0n 5)) (4n (12n (0n 4) (0n 1) (0n 5)) (3n 0)) (0n 0) (12n (0n 4) (0n 1) (0n 5)))))))))",
    "(3n 0)",
    "(15n)",
    "(4n (15n) (15n))",
    "(4n (4n (15n) (3n 0)) (4n (2n (0n 0) (4n (15n) (3n 0)) (16n) (15n)) (4n (4n (15n) (4n (2n (0n 2) (4n (15n) (3n 0)) (0n 0) (15n)) (2n (0n 3) (4n (15n) (3n 0)) (2n (17n) (4n (15n) (15n)) (0n 1) (15n)) (15n)))) (4n (15n) (2n (0n 3) (4n (15n) (3n 0)) (0n 0) (15n))))))",
    "(3n 0)",
    "(19n)",
    "(3n 0)",
    "(4n (4n (21n) (3n 0)) (4n (21n) (2n (0n 1) (4n (21n) (3n 0)) (0n 0) (21n))))"
]

dbtypes = [parse_sexp(s) for s in dbtypes_strs]

def get_dbtype(t: Term) -> Term:
    match t:
        case Typ(0): return dbtypes[0]
        case Pmk(): return dbtypes[1]
        case ProdRec(): return dbtypes[2]
        case Inl(): return dbtypes[3]
        case Inr(): return dbtypes[4]
        case SumRec(): return dbtypes[5]
        case Refl(): return dbtypes[6]
        case EqRec(): return dbtypes[7]
        case Nat(): return dbtypes[8]
        case Zero(): return dbtypes[9]
        case Succ(): return dbtypes[10]
        case NatRec(): return dbtypes[11]
        case Unit(): return dbtypes[12]
        case Intro(): return dbtypes[13]
        case Fls(): return dbtypes[14]
        case FlsRec(): return dbtypes[15]
        case _: return 0

def term_rec(t: Term, s: Any, fdep, fvar) -> Term:
    def g(s, term):
        match term:
            case Var(x): return fvar(s, x)
            case Lam(b, beta): return Lam(g(fdep(s), b), g(fdep(s), beta))
            case App(f, phi, a, alpha): return App(g(s, f), g(s, phi), g(s, a), g(s, alpha))
            case Fn(alpha, beta): return Fn(g(s, alpha), g(fdep(s), beta))
            case Prod(alpha, beta): return Prod(g(s, alpha), g(s, beta))
            case Sum(alpha, beta): return Sum(g(s, alpha), g(s, beta))
            case Eq(a, a_prime, alpha): return Eq(g(s, a), g(s, a_prime), g(s, alpha))
            case _: return term
    return g(s, t)

def incr(t: Term) -> Term:
    return term_rec(t, 0, lambda d: d + 1, lambda d, x: Var(x + 1 if d <= x else x))

def sub(t: Term, t_prime: Term) -> Term:
    def fdep(s):
        d, tp = s
        return (d + 1, incr(tp))
    def fvar(s, x):
        d, tp = s
        if x == d:
            return tp
        else:
            return Var(x - 1 if d < x else x)
    return term_rec(t, (0, t_prime), fdep, fvar)

def evaluate(t: Term) -> Term:
    match t:
        case Lam(b, beta):
            return Lam(evaluate(b), evaluate(beta))
        case App(f, phi, a, alpha):
            f_prime = evaluate(f)
            a_prime = evaluate(a)
            match f_prime, a_prime:
                case Lam(b, _), ap:
                    return evaluate(sub(b, ap))
                case App(App(App(App(ProdRec(), _, _, _), _, _, _), _, _, _), _, g, Fn(alpha_val, gamma)), \
                     App(App(App(App(Pmk(), _, _, _), _, _, _), _, a_val, _), _, b, beta):
                    return evaluate(App(App(g, Fn(alpha_val, gamma), a_val, alpha_val), sub(gamma, a_val), b, beta))
                case App(App(App(App(App(SumRec(), _, _, _), _, _, _), _, _, _), _, g, gamma), _, _, _), \
                     App(App(App(Inl(), _, _, _), _, _, _), _, a_val, alpha_val):
                    return evaluate(App(g, gamma, a_val, alpha_val))
                case App(App(App(App(App(SumRec(), _, _, _), _, _, _), _, _, _), _, _, _), _, g, gamma), \
                     App(App(App(Inr(), _, _, _), _, _, _), _, b_val, beta_val):
                    return evaluate(App(g, gamma, b_val, beta_val))
                case App(App(App(App(App(EqRec(), _, _, _), _, _, _), _, _, _), _, ha, _), _, _, _), \
                     App(App(Refl(), _, _, _), _, _, _):
                    return evaluate(ha)
                case App(App(App(NatRec(), _, _, _), _, z, _), _, _, _), Zero():
                    return evaluate(z)
                case App(App(App(NatRec(), _, m, _), _, _, _), _, g, Fn(Nat(), gamma)), \
                     App(Succ(), Fn(Nat(), Nat()), n, Nat()):
                    return evaluate(App(App(g, Fn(Nat(), gamma), n, Nat()), sub(gamma, n), App(f_prime, phi, n, Nat()), App(m, Fn(Nat(), Typ(0)), n, Nat())))
                case x, ap:
                    return App(x, evaluate(phi), ap, evaluate(alpha))
        case Fn(alpha, beta):
            return Fn(evaluate(alpha), evaluate(beta))
        case Prod(alpha, beta):
            return Prod(evaluate(alpha), evaluate(beta))
        case Sum(alpha, beta):
            return Sum(evaluate(alpha), evaluate(beta))
        case Eq(a, a_prime, alpha):
            return Eq(evaluate(a), evaluate(a_prime), evaluate(alpha))
        case _:
            return t
    return t # needed? No, the match is exhaustive theoretically but Python needs it

def cumeq(a: Term, a_prime: Term) -> bool:
    return (a == Typ(0) and a_prime == Typ(1)) or a == evaluate(a_prime)

def check(env: list[Term], t: Term, tau: Term) -> bool:
    match t, tau:
        case Var(x), alpha:
            if x < len(env):
                return cumeq(evaluate(env[x]), alpha)
            return False
        case Lam(b, beta), Fn(alpha, beta_prime):
            new_env = [incr(e) for e in [alpha] + env]
            return check(new_env, b, beta) and evaluate(beta) == evaluate(beta_prime)
        case App(f, Fn(alpha, beta), a, alpha_prime), beta_prime:
            return (check(env, f, Fn(alpha, beta)) and check(env, a, alpha) and 
                    evaluate(alpha) == evaluate(alpha_prime) and cumeq(evaluate(sub(beta, a)), beta_prime))
        case Fn(alpha, beta), Typ(u):
            new_env = [incr(e) for e in [alpha] + env]
            return check(env, alpha, Typ(u)) and check(new_env, beta, Typ(u))
        case Prod(alpha, beta), Typ(u):
            return check(env, alpha, Typ(u)) and check(env, beta, Fn(alpha, Typ(0)))
        case Sum(alpha, beta), Typ(u):
            return check(env, alpha, Typ(u)) and check(env, beta, Typ(u))
        case Eq(a, a_prime, alpha), Typ(u):
            return check(env, a, alpha) and check(env, a_prime, alpha) and check(env, alpha, Typ(u))
        case Typ(1), _:
            return False
        case t_val, tau_val:
            return cumeq(get_dbtype(t_val), tau_val)
    return False

def check_pair(t: Term, tau: Term) -> bool:
    return check([], tau, Typ(1)) and check([], t, tau)

if __name__ == "__main__":
    # Test basic checks
    assert check([], get_dbtype(Pmk()), Typ(1)), "Pmk btype mismatch"
    assert check([], get_dbtype(ProdRec()), Typ(1)), "ProdRec btype mismatch"
    assert check([], get_dbtype(Inl()), Typ(1)), "Inl btype mismatch"
    assert check([], get_dbtype(Inr()), Typ(1)), "Inr btype mismatch"
    assert check([], get_dbtype(SumRec()), Typ(1)), "SumRec btype mismatch"
    assert check([], get_dbtype(Refl()), Typ(1)), "Refl btype mismatch"
    assert check([], get_dbtype(EqRec()), Typ(1)), "EqRec btype mismatch"
    assert check([], get_dbtype(NatRec()), Typ(1)), "NatRec btype mismatch"
    assert check([], get_dbtype(FlsRec()), Typ(1)), "FlsRec btype mismatch"
    assert not check([], Typ(1), Typ(1)), "Typ(1) Typ(1) shouldn't pass"
    print("Self test passed!")

    import os
    proofs_dir = "proofs"
    if os.path.isdir(proofs_dir):
        passed = 0
        failed = 0
        for filename in sorted(os.listdir(proofs_dir)):
            filepath = os.path.join(proofs_dir, filename)
            with open(filepath, 'r') as f:
                content = f.read().strip()
            
            if content.startswith("'("):
                content = content[2:-1]
                
            depth = 0
            split_idx = -1
            for i, c in enumerate(content):
                if c == '(': depth += 1
                elif c == ')': depth -= 1
                elif c == '.' and depth == 0:
                    # found the root dot
                    split_idx = i
                    break
                    
            if split_idx == -1:
                print(f"Failed to parse {filename}")
                failed += 1
                continue
                
            t_str = content[:split_idx].strip()
            tau_str = content[split_idx+1:].strip()
            
            try:
                t = parse_sexp(t_str)
                tau = parse_sexp(tau_str)
                
                if check_pair(t, tau):
                    print(f"Proof {filename} PASSED")
                    passed += 1
                else:
                    print(f"Proof {filename} FAILED")
                    failed += 1
            except Exception as e:
                print(f"Exception on {filename}: {e}")
                failed += 1
                
        print(f"Results: {passed} passed, {failed} failed.")
        assert failed == 0, "Some proofs failed to typecheck"
