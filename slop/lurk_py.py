#!/usr/bin/env python3
"""Minimal Lurk interpreter.

Goal: just enough features to run cert_helpers.lurk + cert_verifier.lurk +
the per-test asserts in a generated cert_*.lurk dump.  Used to debug
verifier failures (where lurk-rs prints a useless `<Err InvalidArg>`).

Reports the failing form + a short call-stack snippet on errors.

Usage: lurk_py.py <file.lurk>
"""

from __future__ import annotations

import os
import re
import sys
import time
from dataclasses import dataclass

sys.setrecursionlimit(200_000)

# Counters bumped on every interpreter step we care about, for benchmarking
# the verifier under different micro-optimizations.
EVAL_CALLS = [0]      # one count per `evaluate(expr, env)` entry
CONS_ALLOCS = [0]     # one count per Cons() construction
ENV_ALLOCS = [0]      # one count per Env() construction (closure frame, let, etc.)
CALLS_PER_FN: dict[str, int] = {}  # closure name -> # invocations

# ---------------------------------------------------------------- tokenizer

TOKEN = re.compile(r"\(|\)|'|;[^\n]*|\s+|\"[^\"]*\"|[^()\s'`,]+")


def tokenize(s):
    out = []
    for m in TOKEN.finditer(s):
        tok = m.group()
        if tok.startswith(";") or tok.isspace():
            continue
        out.append(tok)
    return out


# ---------------------------------------------------------------- AST atoms

class Symbol(str):
    __slots__ = ()


def parse_atom(tok):
    if tok.startswith('"'):
        return tok[1:-1]
    if re.fullmatch(r"-?\d+n?", tok):
        return int(tok.rstrip("n"))
    return Symbol(tok)


# ---------------------------------------------------------------- parser
#
# Returns Python lists (parsed forms).  `!` is treated as a single token: a
# directive call appears as `! (def x ...)` in the token stream; we surface it
# at the top level only.

def parse(tokens, pos):
    tok = tokens[pos]
    pos += 1
    if tok == "'":
        v, pos = parse(tokens, pos)
        return [Symbol("quote"), v], pos
    if tok == "(":
        items = []
        while tokens[pos] != ")":
            v, pos = parse(tokens, pos)
            items.append(v)
        return items, pos + 1
    if tok == ")":
        raise SyntaxError("unexpected )")
    if tok == "!":
        raise SyntaxError("stray ! inside expression")
    return parse_atom(tok), pos


# ---------------------------------------------------------------- runtime

class Nil:
    __slots__ = ()
    def __repr__(self): return "nil"


class T:
    __slots__ = ()
    def __repr__(self): return "t"


NIL = Nil()
TRUE = T()


class Cons:
    __slots__ = ("car", "cdr")
    def __init__(self, car, cdr):
        CONS_ALLOCS[0] += 1
        self.car = car
        self.cdr = cdr
    def __repr__(self):
        return list_to_str(self)


def list_to_str(v, depth=0):
    if depth > 30:
        return "…"
    if v is NIL: return "nil"
    if v is TRUE: return "t"
    if isinstance(v, int): return str(v)
    if isinstance(v, str): return v
    if isinstance(v, Cons):
        parts = []
        cur = v
        n = 0
        while isinstance(cur, Cons):
            parts.append(list_to_str(cur.car, depth + 1))
            cur = cur.cdr
            n += 1
            if n > 50:
                parts.append("…")
                return "(" + " ".join(parts) + ")"
        if cur is NIL:
            return "(" + " ".join(parts) + ")"
        return "(" + " ".join(parts) + " . " + list_to_str(cur, depth + 1) + ")"
    return str(v)


@dataclass
class Closure:
    params: tuple
    body: list
    env: "Env"
    name: str = "lambda"


class Env:
    __slots__ = ("bindings", "parent")
    def __init__(self, parent=None):
        ENV_ALLOCS[0] += 1
        self.bindings = {}
        self.parent = parent
    def lookup(self, name):
        e = self
        while e is not None:
            if name in e.bindings:
                return e.bindings[name]
            e = e.parent
        raise NameError(f"unbound symbol: {name}")


# ------------------------------------------------------ truthy / quote

def truthy(v):
    return v is not NIL


def datafy(expr):
    """Convert a parsed AST form into Lurk data (cons-list / number / symbol)."""
    if isinstance(expr, list):
        # Build a nil-terminated cons-list from the elements.
        cur = NIL
        for x in reversed(expr):
            cur = Cons(datafy(x), cur)
        return cur
    if isinstance(expr, Symbol):
        if expr == "nil": return NIL
        if expr == "t": return TRUE
        return expr  # bare symbol stays as a symbol value
    return expr


# ------------------------------------------------------ builtins

class LurkError(Exception):
    pass


def _check_num(*xs):
    for x in xs:
        if not isinstance(x, int):
            raise LurkError(f"InvalidArg: expected number, got {list_to_str(x)}")


def b_tree_lookup(tree, i, size):
    """Native impl of cert_helpers.lurk's tree-lookup.  Same semantics, but
    avoids the eval dispatch overhead — this is THE hot path."""
    while size != 1:
        half = size >> 1
        if i < half:
            tree = tree.car
            size = half
        else:
            tree = tree.cdr
            i -= half
            size -= half
    return tree


def b_cons(a, b): return Cons(a, b)
def b_car(x):
    if not isinstance(x, Cons): raise LurkError(f"car of non-cons: {list_to_str(x)}")
    return x.car
def b_cdr(x):
    if not isinstance(x, Cons): raise LurkError(f"cdr of non-cons: {list_to_str(x)}")
    return x.cdr
def b_eq(a, b):
    # Structural equality (matches Lurk semantics closely enough for our use).
    if a is b: return TRUE
    if isinstance(a, int) and isinstance(b, int):
        return TRUE if a == b else NIL
    if isinstance(a, Cons) and isinstance(b, Cons):
        # iterative to avoid deep recursion
        stack = [(a, b)]
        while stack:
            x, y = stack.pop()
            if x is y: continue
            if isinstance(x, Cons) and isinstance(y, Cons):
                stack.append((x.car, y.car))
                stack.append((x.cdr, y.cdr))
            elif isinstance(x, int) and isinstance(y, int):
                if x != y: return NIL
            elif (x is NIL and y is NIL) or (x is TRUE and y is TRUE):
                continue
            else:
                return NIL
        return TRUE
    if (a is NIL and b is NIL) or (a is TRUE and b is TRUE):
        return TRUE
    return NIL
def b_eq_num(a, b):
    _check_num(a, b)
    return TRUE if a == b else NIL
def b_lt(a, b): _check_num(a, b); return TRUE if a < b else NIL
def b_le(a, b): _check_num(a, b); return TRUE if a <= b else NIL
def b_gt(a, b): _check_num(a, b); return TRUE if a > b else NIL
def b_ge(a, b): _check_num(a, b); return TRUE if a >= b else NIL
def b_add(a, b): _check_num(a, b); return a + b
def b_sub(a, b): _check_num(a, b); return a - b
def b_mul(a, b): _check_num(a, b); return a * b
def b_div(a, b): _check_num(a, b); return a // b


# ------------------------------------------------------ evaluator (with TCO)

# Maintain a small call stack snapshot for error reporting.
CALL_DEPTH_LIMIT = 200_000
DEBUG_FRAMES: list[str] = []

def push_frame(label):
    if len(DEBUG_FRAMES) < 30:
        DEBUG_FRAMES.append(label)

def pop_frame():
    if DEBUG_FRAMES:
        DEBUG_FRAMES.pop()


def repr_short(v, limit=80):
    s = list_to_str(v)
    if len(s) > limit:
        s = s[:limit] + "…"
    return s


def evaluate(expr, env):
    """TCO loop."""
    EVAL_CALLS[0] += 1
    while True:
        # atoms
        if isinstance(expr, int):
            return expr
        if isinstance(expr, Symbol):
            # special atoms
            if expr == "nil": return NIL
            if expr == "t": return TRUE
            return env.lookup(expr)
        if not isinstance(expr, list):
            return expr  # already a runtime value (e.g., a datafied cons)
        if not expr:
            return NIL
        head = expr[0]
        if isinstance(head, Symbol):
            if head == "quote":
                return datafy(expr[1])
            if head == "lambda":
                params = tuple(str(p) for p in expr[1])
                body = expr[2:]
                return Closure(params, body, env)
            if head == "if":
                cond = evaluate(expr[1], env)
                if truthy(cond):
                    expr = expr[2]
                else:
                    expr = expr[3] if len(expr) >= 4 else "nil"
                continue
            if head == "let":
                bindings = expr[1]
                body = expr[2:]
                new_env = Env(env)
                # Sequential evaluation (Lurk's `let`).
                for binding in bindings:
                    name = str(binding[0])
                    val = evaluate(binding[1], new_env)
                    new_env.bindings[name] = val
                for b in body[:-1]:
                    evaluate(b, new_env)
                expr = body[-1]
                env = new_env
                continue
            if head == "letrec":
                bindings = expr[1]
                body = expr[2:]
                new_env = Env(env)
                # Two-pass: install placeholders first so closures can reference each other.
                for binding in bindings:
                    new_env.bindings[str(binding[0])] = NIL
                for binding in bindings:
                    new_env.bindings[str(binding[0])] = evaluate(binding[1], new_env)
                for b in body[:-1]:
                    evaluate(b, new_env)
                expr = body[-1]
                env = new_env
                continue
            if head == "cons":
                a = evaluate(expr[1], env)
                b = evaluate(expr[2], env)
                return Cons(a, b)
            # else: function call
        # function application
        fn = evaluate(head, env)
        args = [evaluate(a, env) for a in expr[1:]]
        if isinstance(fn, Closure):
            if len(args) != len(fn.params):
                raise LurkError(f"arity mismatch for {fn.name}: want {len(fn.params)}, got {len(args)}")
            new_env = Env(fn.env)
            for n, v in zip(fn.params, args):
                new_env.bindings[n] = v
            CALLS_PER_FN[fn.name] = CALLS_PER_FN.get(fn.name, 0) + 1
            arg_str = ", ".join(repr_short(a) for a in args)
            label = f"{fn.name}({arg_str})"
            DEBUG_FRAMES.append(label)
            try:
                for b in fn.body[:-1]:
                    evaluate(b, new_env)
                result = evaluate(fn.body[-1], new_env)
                DEBUG_FRAMES.pop()
                return result
            except LurkError:
                # Leave frame in DEBUG_FRAMES so the outermost handler can see it.
                raise
        if callable(fn):
            try:
                return fn(*args)
            except LurkError as e:
                raise
        raise LurkError(f"not callable: {fn} (form was {expr})")


# ------------------------------------------------------ top-level

def build_global_env():
    env = Env()
    env.bindings.update({
        "cons": b_cons,
        "car": b_car, "cdr": b_cdr,
        "eq": b_eq,
        "=": b_eq_num,
        "<": b_lt, "<=": b_le, ">": b_gt, ">=": b_ge,
        "+": b_add, "-": b_sub, "*": b_mul, "/": b_div,
    })
    return env


def run_file(path, env, verbose=True):
    src = open(path).read()
    toks = tokenize(src)
    pos = 0
    assertion_idx = 0
    while pos < len(toks):
        if toks[pos] == "!":
            pos += 1
            form, pos = parse(toks, pos)
            handle_directive(form, env, os.path.dirname(os.path.abspath(path)), assertion_idx, verbose)
            if form[0] == "assert":
                assertion_idx += 1
        else:
            form, pos = parse(toks, pos)
            v = evaluate(form, env)
            if verbose:
                print(list_to_str(v))


def handle_directive(form, env, base_dir, assertion_idx, verbose):
    head = form[0]
    if head == "def":
        name = str(form[1])
        val = evaluate(form[2], env)
        if isinstance(val, Closure):
            val.name = name
        env.bindings[name] = val
        if verbose: print(name)
    elif head == "defrec":
        name = str(form[1])
        # Bypass slow recursive Lurk impls for the hot-path helpers.
        if name == "tree-lookup":
            env.bindings[name] = b_tree_lookup
            if verbose: print(name + " [native]")
            return
        env.bindings[name] = NIL  # placeholder
        c = evaluate(form[2], env)
        if isinstance(c, Closure):
            c.name = name
            # If TRACE_NIL is set and this is check-cert, wrap to log nil returns.
            if os.environ.get("TRACE_NIL") and name in ("check-cert", "cumeq", "eq-incr-by", "eq-sub-by", "lookup-theorem", "lookup-dbtype"):
                orig = c
                def make_wrapper(orig_fn, fname):
                    def wrapper(*args):
                        # Implement as a manual call into evaluate
                        if len(args) != len(orig_fn.params):
                            raise LurkError(f"arity")
                        new_env = Env(orig_fn.env)
                        for n, v in zip(orig_fn.params, args):
                            new_env.bindings[n] = v
                        DEBUG_FRAMES.append(f"{fname}({', '.join(repr_short(a) for a in args)})")
                        try:
                            for b in orig_fn.body[:-1]:
                                evaluate(b, new_env)
                            r = evaluate(orig_fn.body[-1], new_env)
                            if r is NIL:
                                print(f"NIL <- {fname}({', '.join(repr_short(a) for a in args)})", file=sys.stderr)
                            DEBUG_FRAMES.pop()
                            return r
                        except LurkError:
                            raise
                    return wrapper
                env.bindings[name] = make_wrapper(c, name)
                if verbose: print(name + " [traced]")
                return
        env.bindings[name] = c
        if verbose: print(name)
    elif head == "load":
        fname = form[1]
        path = os.path.join(base_dir, fname)
        if verbose: print(f"; loading {fname}", file=sys.stderr)
        run_file(path, env, verbose=verbose)
    elif head == "assert":
        DEBUG_FRAMES.clear()
        t0 = time.time()
        try:
            v = evaluate(form[1], env)
        except LurkError as e:
            print(f"\n*** assert #{assertion_idx} ({form[1][:120]}…) ERRORED")
            print(f"*** {e}")
            print(f"*** call stack (top {len(DEBUG_FRAMES)} frames):")
            for f in DEBUG_FRAMES[-25:]:
                print(f"    {f}")
            sys.exit(1)
        dt = time.time() - t0
        if not truthy(v):
            print(f"\n*** assert #{assertion_idx} FAILED (evaluates to nil) in {dt:.2f}s")
            print(f"*** form: {form[1]}")
            sys.exit(1)
        else:
            if verbose: print(f"t  ; assert #{assertion_idx} ok in {dt:.2f}s")
    else:
        raise LurkError(f"unknown directive: {head}")


def main():
    if len(sys.argv) != 2:
        print("usage: lurk_py.py <file.lurk>", file=sys.stderr)
        sys.exit(1)
    env = build_global_env()
    try:
        run_file(sys.argv[1], env)
    except LurkError as e:
        print(f"\n*** FATAL: {e}")
        print(f"*** call stack (top {len(DEBUG_FRAMES)} frames):")
        for f in DEBUG_FRAMES[-25:]:
            print(f"    {f}")
        sys.exit(1)
    print(f";; counters: eval={EVAL_CALLS[0]:,}  cons={CONS_ALLOCS[0]:,}  envs={ENV_ALLOCS[0]:,}", file=sys.stderr)
    top = sorted(CALLS_PER_FN.items(), key=lambda x: -x[1])[:15]
    for n, c in top:
        print(f";;   {c:>12,}  {n}", file=sys.stderr)


if __name__ == "__main__":
    main()
